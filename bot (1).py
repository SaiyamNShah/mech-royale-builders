"""Apex-FINAL — V11-derived placement-focused combat bot.

Core:
- Persistent world memory and spatial-hashed 3D collision map.
- Fast 16-ray local steering, multi-ring cover and remembered flanker avoidance.
- Proactive but conditional rooftop control with climb hysteresis and edge-lock.
- Simultaneous Laser + Gun combat, barrel LOS, precise charge release.
- Projectile and laser evasion, supply drops, predictive zone positioning.

Standard library only. Requires the supplied mechfight.py wrapper.
"""

from __future__ import annotations

import json
import math
import os
import random
from typing import Dict, List, Optional, Tuple

import mechfight as mf


PI = math.pi
TAU = 2.0 * PI


def clamp(v, lo, hi):
    return lo if v < lo else hi if v > hi else v


def wrap_angle(a):
    return (a + PI) % TAU - PI


def angle_diff(a, b):
    return wrap_angle(a - b)


def dist2d(a, b):
    return math.hypot(a[0] - b[0], a[1] - b[1])


def dist3d(a, b):
    return math.sqrt(
        (a[0] - b[0]) ** 2
        + (a[1] - b[1]) ** 2
        + (a[2] - b[2]) ** 2
    )


def point_in_ring(x, y, ring):
    n = len(ring) // 2
    if n < 3:
        return False

    inside = False
    x1 = ring[2 * (n - 1)]
    y1 = ring[2 * (n - 1) + 1]

    for i in range(n):
        x2 = ring[2 * i]
        y2 = ring[2 * i + 1]

        if (y1 > y) != (y2 > y):
            xi = x1 + (y - y1) * (x2 - x1) / (y2 - y1)
            if x < xi:
                inside = not inside

        x1, y1 = x2, y2

    return inside


class Prism:
    __slots__ = (
        "kind", "base", "top", "ring", "holes",
        "minx", "maxx", "miny", "maxy", "cx", "cy"
    )

    def __init__(self, raw):
        self.kind = raw["kind"]
        self.base = float(raw["base"])
        self.top = float(raw["top"])
        self.ring = raw["ring"]
        self.holes = raw.get("holes", [])

        xs = self.ring[0::2]
        ys = self.ring[1::2]

        self.minx = min(xs)
        self.maxx = max(xs)
        self.miny = min(ys)
        self.maxy = max(ys)

        self.cx = (self.minx + self.maxx) * 0.5
        self.cy = (self.miny + self.maxy) * 0.5

    def contains_xy(self, x, y):
        if (
            x < self.minx or x > self.maxx
            or y < self.miny or y > self.maxy
        ):
            return False

        if not point_in_ring(x, y, self.ring):
            return False

        for h in self.holes:
            if point_in_ring(x, y, h):
                return False

        return True


class ArenaMap:
    """V11 spatial hash, terrain physics, roof index, and canopy metadata."""

    def __init__(self, map_dir, max_slope_deg=50.0):
        self.cell = 25.0
        self.grid = {}
        self.roofs = []

        self.nx = 0
        self.ny = 0
        self.min_x = 0.0
        self.min_y = 0.0
        self.step = 1.0
        self.scale = 0.01
        self.terrain = None

        self.bounds = (-508.0, 550.0, -328.0, 384.0)

        self.max_slope_tan = math.tan(
            math.radians(max(10.0, max_slope_deg - 3.0))
        )

        # Trees affect vision, not bullet or beam collision.
        self.tree_grid = {}
        self.tree_cell = 25.0

        self._load(map_dir)

    def _load(self, map_dir):
        wpath = os.path.join(map_dir, "v2", "world.json")
        tpath = os.path.join(map_dir, "v2", "terrain.i16")

        if not os.path.exists(wpath):
            wpath = os.path.join(map_dir, "world.json")
            tpath = os.path.join(map_dir, "terrain.i16")

        if not os.path.exists(wpath):
            return

        with open(wpath, "r", encoding="utf-8") as f:
            w = json.load(f)

        b = w.get("bounds", {})
        if b:
            self.bounds = (
                float(b["minX"]) + 4.0,
                float(b["maxX"]) - 4.0,
                float(b["minY"]) + 4.0,
                float(b["maxY"]) - 4.0,
            )

        tm = w.get("terrain", {})

        self.nx = int(tm.get("nx", 0))
        self.ny = int(tm.get("ny", 0))
        self.min_x = float(tm.get("minX", 0.0))
        self.min_y = float(tm.get("minY", 0.0))
        self.step = max(0.01, float(tm.get("step", 1.0)))
        self.scale = float(tm.get("scale", 0.01))

        if os.path.exists(tpath) and self.nx > 1 and self.ny > 1:
            with open(tpath, "rb") as f:
                raw = f.read()

            if len(raw) >= self.nx * self.ny * 2:
                self.terrain = memoryview(raw).cast("h")

        for rp in w.get("prisms", []):
            if not rp.get("ring"):
                continue

            p = Prism(rp)

            ix0 = int(math.floor(p.minx / self.cell))
            ix1 = int(math.floor(p.maxx / self.cell))
            iy0 = int(math.floor(p.miny / self.cell))
            iy1 = int(math.floor(p.maxy / self.cell))

            for ix in range(ix0, ix1 + 1):
                for iy in range(iy0, iy1 + 1):
                    self.grid.setdefault((ix, iy), []).append(p)

            if (
                p.kind == "building"
                and p.maxx - p.minx > 16.0
                and p.maxy - p.miny > 16.0
                and p.contains_xy(p.cx, p.cy)
            ):
                rh = p.top - self.terrain_z(p.cx, p.cy)

                if 8.5 <= rh <= 28.0:
                    self.roofs.append((p.cx, p.cy, p.top))

        # Load actual world tree data. No trees are added to the solid grid.
        trees = w.get("trees", {})
        if isinstance(trees, dict):
            fields = trees.get("fields", [])
            data = trees.get("data", [])

            if isinstance(fields, list) and fields:
                stride = len(fields)

                if all(k in fields for k in ("x", "y", "crownR")):
                    ix = fields.index("x")
                    iy = fields.index("y")
                    ir = fields.index("crownR")
                    iz = fields.index("z") if "z" in fields else None
                    ib = (
                        fields.index("crownBase")
                        if "crownBase" in fields else None
                    )
                    ih = (
                        fields.index("height")
                        if "height" in fields else None
                    )

                    for i in range(0, len(data) - stride + 1, stride):
                        try:
                            tx = float(data[i + ix])
                            ty = float(data[i + iy])
                            rr = float(data[i + ir])
                            tz = float(data[i + iz]) if iz is not None else 0.0
                            cb = (
                                float(data[i + ib])
                                if ib is not None else 0.0
                            )
                            th = (
                                float(data[i + ih])
                                if ih is not None else 15.0
                            )
                        except (ValueError, TypeError, IndexError):
                            continue

                        if rr <= 0.0:
                            continue

                        tree = (tx, ty, tz + cb, tz + th, rr)

                        gx0 = int(math.floor((tx - rr) / self.tree_cell))
                        gx1 = int(math.floor((tx + rr) / self.tree_cell))
                        gy0 = int(math.floor((ty - rr) / self.tree_cell))
                        gy1 = int(math.floor((ty + rr) / self.tree_cell))

                        for gx in range(gx0, gx1 + 1):
                            for gy in range(gy0, gy1 + 1):
                                self.tree_grid.setdefault(
                                    (gx, gy), []
                                ).append(tree)

    def terrain_z(self, x, y):
        if self.terrain is None:
            return 0.0

        gx = clamp(
            (x - self.min_x) / self.step, 0.0, self.nx - 1.001
        )
        gy = clamp(
            (y - self.min_y) / self.step, 0.0, self.ny - 1.001
        )

        i = int(gx)
        j = int(gy)

        fx = gx - i
        fy = gy - j

        idx = j * self.nx + i
        a = self.terrain

        z00 = a[idx]
        z10 = a[idx + 1]
        z01 = a[idx + self.nx]
        z11 = a[idx + self.nx + 1]

        z0 = z00 + (z10 - z00) * fx
        z1 = z01 + (z11 - z01) * fx

        return (z0 + (z1 - z0) * fy) * self.scale

    def _cell_prisms(self, x, y):
        return self.grid.get(
            (
                int(math.floor(x / self.cell)),
                int(math.floor(y / self.cell)),
            ),
            (),
        )

    def support_z(self, x, y, feet_z):
        best = self.terrain_z(x, y)

        for p in self._cell_prisms(x, y):
            if (
                best < p.top <= feet_z + 1.5
                and p.contains_xy(x, y)
            ):
                best = p.top

        return best

    def roof_prism_under(self, x, y, feet_z):
        best = None
        best_top = -1e9

        for p in self._cell_prisms(x, y):
            if (
                abs(p.top - feet_z) <= 2.2
                and p.top > best_top
                and p.contains_xy(x, y)
            ):
                best = p
                best_top = p.top

        return best

    def is_solid(self, x, y, z):
        if z < self.terrain_z(x, y) - 0.15:
            return True

        for p in self._cell_prisms(x, y):
            if p.base <= z <= p.top and p.contains_xy(x, y):
                return True

        return False

    def _prism_wall_height(
        self, x, y, feet_z, step_up, height
    ):
        head = feet_z + height - 0.2
        step_z = feet_z + step_up
        max_h = 0.0

        for p in self._cell_prisms(x, y):
            if (
                p.top > step_z
                and p.base < head
                and p.contains_xy(x, y)
            ):
                max_h = max(max_h, p.top - feet_z)

        return max_h

    def wall_height_along(
        self, x0, y0, z0, dx, dy,
        dist, radius, height, step_up
    ):
        nx = x0 + dx * dist
        ny = y0 + dy * dist

        if (
            nx < self.bounds[0] + radius
            or nx > self.bounds[1] - radius
            or ny < self.bounds[2] + radius
            or ny > self.bounds[3] - radius
        ):
            return 99.0

        mx = x0 + dx * dist * 0.5
        my = y0 + dy * dist * 0.5

        tz0 = self.terrain_z(x0, y0)
        tzm = self.terrain_z(mx, my)
        tz1 = self.terrain_z(nx, ny)

        half = max(1.0, dist * 0.5)

        if z0 <= tz0 + 2.0:
            if (
                (tzm - tz0) / half > self.max_slope_tan
                or (tz1 - tzm) / half > self.max_slope_tan
            ):
                return 99.0

        feet = max(z0, tz1) if z0 <= tz0 + 1.5 else z0

        px = -dy * radius * 0.85
        py = dx * radius * 0.85

        return max(
            self._prism_wall_height(
                nx, ny, feet, step_up, height
            ),
            self._prism_wall_height(
                nx + px, ny + py, feet, step_up, height
            ),
            self._prism_wall_height(
                nx - px, ny - py, feet, step_up, height
            ),
        )

    def has_los(self, a, b, step_m=4.0):
        dx = b[0] - a[0]
        dy = b[1] - a[1]
        dz = b[2] - a[2]

        d = math.sqrt(dx * dx + dy * dy + dz * dz)

        if d < 3.5:
            return True

        steps = max(2, min(46, int(d / step_m)))
        inv = 1.0 / steps

        for k in range(1, steps):
            f = k * inv

            if self.is_solid(
                a[0] + dx * f,
                a[1] + dy * f,
                a[2] + dz * f,
            ):
                return False

        return True

    def barrel_los(
        self, pos, muzzle_h, radius,
        yaw, pitch, target
    ):
        """Approximate shot origin using actual forward barrel emergence."""
        off = radius + 0.5
        cp = math.cos(pitch)

        origin = [
            pos[0] + math.cos(yaw) * cp * off,
            pos[1] + math.sin(yaw) * cp * off,
            pos[2] + muzzle_h + math.sin(pitch) * off,
        ]

        # An embedded barrel cannot shoot through a solid.
        if self.is_solid(origin[0], origin[1], origin[2]):
            return False

        return self.has_los(origin, target, 3.5)

    def arc_clear(
        self, muzzle, yaw, pitch, speed, g, flight_t
    ):
        vx = speed * math.cos(pitch) * math.cos(yaw)
        vy = speed * math.cos(pitch) * math.sin(yaw)
        vz = speed * math.sin(pitch)

        for frac in (0.08, 0.18, 0.34, 0.52, 0.72, 0.88):
            tt = flight_t * frac

            px = muzzle[0] + vx * tt
            py = muzzle[1] + vy * tt
            pz = muzzle[2] + vz * tt - 0.5 * g * tt * tt

            if self.is_solid(px, py, pz):
                return False

        return True

    def canopy_at(self, x, y, eye_z):
        """Small, soft positioning preference; never ballistic cover."""
        cell = (
            int(math.floor(x / self.tree_cell)),
            int(math.floor(y / self.tree_cell)),
        )

        score = 0.0

        for tx, ty, bottom, top, rr in self.tree_grid.get(cell, ()):
            if eye_z < bottom - 2.0 or eye_z > top + 2.0:
                continue

            d = math.hypot(x - tx, y - ty)

            if d < rr:
                score += (rr - d) / max(1.0, rr)

        return min(2.0, score)


UPGRADE_TIER = {
    "plating": 99.0,
    "armor": 98.0,
    "nanites": 97.0,
    "gun_mag": 96.0,
    "laser_damage": 95.0,
    "gun_damage": 93.0,
    "laser_charge": 91.0,
    "servos": 90.0,
    "gun_rate": 89.0,
    "lightning_efficiency": 88.0,
    "lightning_range": 85.0,
    "jets": 83.0,
    "reactor": 81.0,
    "gun_velocity": 78.0,
    "capacitor": 75.0,
    "gyros": 73.0,
    "lightning_chain": 70.0,
    "sensors": 65.0,
    "mortar_reload": 59.0,
    "mortar_splash": 57.0,
    "mortar_velocity": 55.0,
    "laser_pierce": 53.0,
}


class Bot:
    name = "Apex-FINAL"

    def __init__(self, hello: mf.Hello):
        self.slot = int(hello["slot"])
        self.rng = random.Random(int(hello["seed"]))
        self.cfg = hello["config"]

        mc = self.cfg.get("mech", {})
        cc = self.cfg.get("cubes", {})
        wc = self.cfg.get("weapons", {})
        lc = self.cfg.get("loot", {})

        self.base_radius = float(mc.get("radius", 2.5))
        self.base_height = float(mc.get("height", 9.0))
        self.step_up = float(mc.get("step_up", 1.2))
        self.gravity = float(mc.get("gravity", 22.0))

        self.size_per_cube = float(cc.get("size_per_cube", 0.05))
        self.stat_cap = int(cc.get("stat_cap", 10))
        self.reach = float(lc.get("pickup_radius", 4.0))

        self.mortar_g = float(
            wc.get("mortar", {}).get("gravity", 22.0)
        )
        self.mortar_splash = float(
            wc.get("mortar", {}).get("splash_radius", 7.0)
        )

        self.map = ArenaMap(
            hello["map"]["dir"],
            float(mc.get("max_slope_deg", 50.0)),
        )

        self.last_damage_t = -10.0
        self.last_combat_t = -10.0
        self.last_damage_bearing = None

        self.beam_threats = {}
        self.enemy_charge_start = {}

        self.last_pos = None
        self.stuck_ticks = 0

        self.strafe_dir = 1.0 if self.slot % 2 == 0 else -1.0
        self.strafe_flip_tick = 0
        self.strafe_interval = 15

        self.scan_yaw = 0.0
        self.climbing_roof = None

        # V11 persistent memory.
        self.mem_pickups = {}
        self.mem_cubes = {}
        self.mem_crates = {}
        self.mem_enemies = {}

    def _pick_upgrade(self, offer, weapons, hp_frac):
        held = {
            w["kind"] for w in weapons if w is not None
        }

        best_i = 0
        best_s = -1e9

        for i, choice in enumerate(offer["choices"]):
            cid = choice["id"]
            score = UPGRADE_TIER.get(cid, 50.0)

            if cid == "gun_mag" and "gun" in held:
                score += 6.0

            if cid == "nanites":
                score += 5.0 if hp_frac < 0.82 else 1.0

            if cid == "plating" and hp_frac < 0.5:
                score += 3.0

            if cid == "laser_damage" and "laser" in held:
                score += 5.0

            if cid == "lightning_efficiency" and "lightning" in held:
                score += 4.0

            if cid.startswith("mortar_") and "mortar" not in held:
                score -= 20.0

            if score > best_s:
                best_s = score
                best_i = i

        return best_i

    def _update_world_memory(self, obs, pos, aim_yaw, zone):
        t = float(obs["t"])
        x, y = pos[0], pos[1]

        zcx, zcy = zone["center"]
        zr = max(0.0, float(zone["radius"]))

        vis_p = set()
        vis_c = set()
        vis_cr = set()
        vis_e = set()

        for p in obs["pickups"]:
            pid = int(p["id"])
            vis_p.add(pid)
            self.mem_pickups[pid] = (p["kind"], p["pos"], t)

        for c in obs["cubes"]:
            cid = int(c["id"])
            vis_c.add(cid)
            self.mem_cubes[cid] = (c["pos"], t)

        for cr in obs["crates"]:
            cid = int(cr["id"])
            vis_cr.add(cid)
            self.mem_crates[cid] = (cr["pos"], t)

        def should_evict(p, seen_t, max_age):
            if t - seen_t > max_age:
                return True

            if dist2d(p, (zcx, zcy)) > zr + 5.0:
                return True

            d = dist2d((x, y), p)

            if d > 100.0:
                return False

            yaw = math.atan2(p[1] - y, p[0] - x)

            if d > 35.0 and abs(angle_diff(yaw, aim_yaw)) > 0.8:
                return False

            # Do not forget loot hidden by a building.
            eye = [x, y, pos[2] + 8.0]
            target = [p[0], p[1], p[2] + 1.0]

            return self.map.has_los(eye, target, 6.0)

        for pid in list(self.mem_pickups):
            if pid not in vis_p:
                kind, p, st = self.mem_pickups[pid]
                if should_evict(p, st, 65.0):
                    del self.mem_pickups[pid]

        for cid in list(self.mem_cubes):
            if cid not in vis_c:
                p, st = self.mem_cubes[cid]
                if should_evict(p, st, 45.0):
                    del self.mem_cubes[cid]

        for cid in list(self.mem_crates):
            if cid not in vis_cr:
                p, st = self.mem_crates[cid]
                if should_evict(p, st, 65.0):
                    del self.mem_crates[cid]

        for e in obs["mechs"]:
            if e["kind"] != "mech":
                continue

            eid = int(e["id"])
            vis_e.add(eid)

            self.mem_enemies[eid] = (e["pos"], t)

            if e.get("charging"):
                if eid not in self.enemy_charge_start:
                    self.enemy_charge_start[eid] = t
            else:
                self.enemy_charge_start.pop(eid, None)

        for eid in list(self.enemy_charge_start):
            if eid not in vis_e:
                del self.enemy_charge_start[eid]

        for eid in list(self.mem_enemies):
            if t - self.mem_enemies[eid][1] > 8.0:
                del self.mem_enemies[eid]

    def _predict_slewed_aim(
        self, cur, yaw, pitch,
        turn_rate, pitch_rate, dt=0.05
    ):
        nyaw = wrap_angle(
            cur[0] + clamp(
                angle_diff(yaw, cur[0]),
                -turn_rate * dt,
                turn_rate * dt,
            )
        )

        npitch = cur[1] + clamp(
            pitch - cur[1],
            -pitch_rate * dt,
            pitch_rate * dt,
        )

        return nyaw, npitch

    def _lead_aim(
        self, muzzle, target, vel,
        speed, z_off, shot_offset
    ):
        tx = target[0]
        ty = target[1]
        tz = target[2] + z_off

        vx, vy, vz = vel

        px, py, pz = tx, ty, tz

        for _ in range(3):
            d = math.sqrt(
                (px - muzzle[0]) ** 2
                + (py - muzzle[1]) ** 2
                + (pz - muzzle[2]) ** 2
            )

            tt = (
                max(0.0, d - shot_offset)
                / max(1.0, speed)
                + 0.04
            )

            px = tx + vx * tt
            py = ty + vy * tt

            if abs(vz) > 0.5:
                ground = self.map.terrain_z(px, py) + z_off
                pz = max(
                    ground,
                    tz + vz * tt
                    - 0.5 * self.gravity * tt * tt,
                )
            else:
                pz = tz + vz * tt

        dx = px - muzzle[0]
        dy = py - muzzle[1]
        dz = pz - muzzle[2]

        return (
            math.atan2(dy, dx),
            math.atan2(dz, max(0.1, math.hypot(dx, dy))),
        )

    def _mortar_aim(
        self, muzzle, target, vel,
        speed, g, high_arc
    ):
        r0 = dist2d(muzzle, target)

        t_est = clamp(
            r0 / max(10.0, speed * 0.72),
            0.1, 4.5,
        )

        px = target[0] + vel[0] * t_est * 0.65
        py = target[1] + vel[1] * t_est * 0.65
        pz = target[2] + 1.0

        dx = px - muzzle[0]
        dy = py - muzzle[1]
        dz = pz - muzzle[2]

        r = math.hypot(dx, dy)

        if r < 17.0 or g <= 0.0:
            return None

        v2 = speed * speed

        disc = v2 * v2 - g * (
            g * r * r + 2.0 * dz * v2
        )

        if disc < 0.0:
            return None

        root = math.sqrt(disc)

        pitch = math.atan2(
            v2 + root if high_arc else v2 - root,
            g * r,
        )

        vh = max(1.0, speed * math.cos(pitch))

        return math.atan2(dy, dx), pitch, r / vh

    def _dodge_vector(
        self, t, pos, radius, projs, enemies
    ):
        ex = 0.0
        ey = 0.0
        urgent = False
        lethal = []

        mx = pos[0]
        my = pos[1]
        mz = pos[2] + 4.5

        for p in projs:
            px, py, pz = p["pos"]
            vx, vy, vz = p["vel"]

            if p["kind"] == "mortar":
                g = max(0.1, self.mortar_g)

                a = 0.5 * g
                b = -vz
                c = pos[2] - pz

                disc = b * b - 4.0 * a * c

                if disc < 0.0:
                    continue

                tt = (-b + math.sqrt(disc)) / (2.0 * a)

                if tt < 0.0 or tt > 2.0:
                    continue

                ix = px + vx * tt
                iy = py + vy * tt

                d = math.hypot(mx - ix, my - iy)
                danger = self.mortar_splash + radius + 2.0

                if d < danger:
                    yaw = math.atan2(my - iy, mx - ix)
                    weight = (danger - d) / danger

                    ex += math.cos(yaw) * weight * 5.2
                    ey += math.sin(yaw) * weight * 5.2

                    if tt < 0.9:
                        urgent = True

            else:
                v2 = vx * vx + vy * vy + vz * vz

                if v2 < 1.0:
                    continue

                rx = mx - px
                ry = my - py
                rz = mz - pz

                tt = (
                    rx * vx + ry * vy + rz * vz
                ) / v2

                if tt < 0.0 or tt > 0.65:
                    continue

                cx = px + vx * tt - mx
                cy = py + vy * tt - my
                cz = pz + vz * tt - mz

                if abs(cz) > 6.5:
                    continue

                d = math.hypot(cx, cy)
                threshold = radius + 2.5

                if d < threshold:
                    hv = math.hypot(vx, vy)

                    if hv <= 0.1:
                        continue

                    nx = -vy / hv
                    ny = vx / hv

                    if nx * cx + ny * cy > 0.0:
                        nx = -nx
                        ny = -ny

                    weight = (threshold - d) / threshold

                    ex += nx * weight * 2.5
                    ey += ny * weight * 2.5

                    if d < radius + 0.8:
                        urgent = True

        # Anticipate enemy beam release without abandoning our own DPS.
        for e in enemies:
            if not e.get("charging"):
                continue

            ep = e["pos"]
            eyaw = e["aim"][0]

            ldx = math.cos(eyaw)
            ldy = math.sin(eyaw)

            rx = mx - ep[0]
            ry = my - ep[1]

            along = rx * ldx + ry * ldy

            if not 0.0 < along < 275.0:
                continue

            cx = rx - along * ldx
            cy = ry - along * ldy

            d = math.hypot(cx, cy)

            if d >= radius + 7.0:
                continue

            eid = int(e["id"])
            elapsed = t - self.enemy_charge_start.get(eid, t)

            if elapsed < 0.28:
                continue

            lethal.append(e)

            nx = -ldy
            ny = ldx

            if nx * cx + ny * cy < 0.0:
                nx = -nx
                ny = -ny

            ex += nx * 4.8
            ey += ny * 4.8
            urgent = True

        return ex, ey, urgent, lethal

    def _best_roof(self, x, y, zone):
        zcx, zcy = zone["next_center"]
        zr = max(
            12.0,
            zone["next_radius"]
            - min(15.0, zone["next_radius"] * 0.2),
        )

        best = None
        best_d = 100.0

        for rx, ry, rz in self.map.roofs:
            if dist2d((rx, ry), (zcx, zcy)) > zr:
                continue

            d = math.hypot(rx - x, ry - y)

            if d < best_d:
                best_d = d
                best = (rx, ry, rz)

        return best

    def _steer_v11(
        self, pos, desired_yaw, zone, dodge,
        radius, height, threats, flankers,
        want_zero_los, want_slice, allow_climb,
        keep_on_roof, energy
    ):
        x, y, z = pos

        zcx, zcy = zone["center"]
        zr = max(
            2.0,
            zone["radius"]
            - min(6.0, zone["radius"] * 0.2),
        )

        best_score = -1e9
        best_dir = [
            math.cos(desired_yaw),
            math.sin(desired_yaw),
        ]

        need_jump = False
        need_jet = False

        for k in range(16):
            off = k * (PI / 8.0)

            if off > PI:
                off -= TAU

            ang = desired_yaw + off
            dx = math.cos(ang)
            dy = math.sin(ang)

            h_near = self.map.wall_height_along(
                x, y, z, dx, dy,
                4.5, radius, height, self.step_up,
            )

            h_mid = (
                99.0 if h_near > 0.0
                else self.map.wall_height_along(
                    x, y, z, dx, dy,
                    10.5, radius, height, self.step_up,
                )
            )

            min_energy = (
                10.0 if self.climbing_roof is not None
                else 45.0
            )

            climbable = (
                allow_climb
                and energy > min_energy
                and 1.2 < h_near < 28.0
            )

            score = math.cos(off) * 3.4
            score += (
                dx * dodge[0] + dy * dodge[1]
            ) * 3.2

            if h_near > 0.0:
                score -= 0.8 if climbable else 12.0
            elif h_mid > 0.0:
                score -= 3.2

            nx1 = x + dx * 5.0
            ny1 = y + dy * 5.0
            nx2 = x + dx * 11.0
            ny2 = y + dy * 11.0

            # V11 roof edge-lock.
            if keep_on_roof and h_near == 0.0:
                sup = self.map.support_z(nx1, ny1, z)

                if sup < z - 4.0:
                    score -= 10.0

            dz = math.hypot(nx2 - zcx, ny2 - zcy)

            if dz > zr:
                score -= (dz - zr) * 0.5

            # Never deliberately flee toward a recently observed flanker.
            if flankers and h_near == 0.0:
                for fp in flankers[:3]:
                    d0 = math.hypot(x - fp[0], y - fp[1])
                    d1 = math.hypot(nx2 - fp[0], ny2 - fp[1])

                    if d0 < 70.0 and d1 < d0:
                        score -= 2.8

            # Canopy is a soft sight benefit, not physical cover.
            if (
                threats
                and h_near == 0.0
                and k % 2 == 0
                and not keep_on_roof
            ):
                score += 0.65 * self.map.canopy_at(
                    nx2, ny2, z + height * 0.85
                )

            # Preserve V11's 13m/25m cover evaluation.
            if (
                threats
                and h_near == 0.0
                and k % 2 == 0
                and (want_zero_los or want_slice)
            ):
                best_bonus = -1e9

                for rr in (13.0, 25.0):
                    sx = x + dx * rr
                    sy = y + dy * rr

                    if math.hypot(sx - zcx, sy - zcy) > zr:
                        continue

                    if rr > 15.0:
                        if h_mid > 0.0:
                            continue

                        if self.map.wall_height_along(
                            x, y, z, dx, dy, rr,
                            radius, height, self.step_up
                        ) > 0.0:
                            continue

                    sz = self.map.support_z(sx, sy, z) + 5.5
                    count = 0

                    for th in threats[:3]:
                        tp = th["pos"]

                        if self.map.has_los(
                            [sx, sy, sz],
                            [tp[0], tp[1], tp[2] + 7.5],
                            7.5,
                        ):
                            count += 1

                    weight = 1.0 if rr < 15.0 else 0.72

                    if want_zero_los:
                        bonus = (
                            9.0 if count == 0
                            else 1.5 if count == 1
                            else -4.5 * count
                        )
                    else:
                        bonus = (
                            7.0 if count == 1
                            else 2.2 if count == 0
                            else -4.5 * (count - 1)
                        )

                    best_bonus = max(best_bonus, bonus * weight)

                    if (
                        (want_zero_los and count == 0)
                        or (want_slice and count == 1)
                    ):
                        break

                if best_bonus > -1e8:
                    score += best_bonus

            if score > best_score:
                best_score = score
                best_dir = [dx, dy]
                need_jump = h_near > 0.0
                need_jet = climbable

        return best_dir, need_jump, need_jet

    def act(self, obs: mf.Observation) -> mf.Action:
        me = obs["self"]
        t = float(obs["t"])
        tick = int(obs["tick"])

        pos = me["pos"]
        x, y, z = pos

        hp = float(me["hp"])
        max_hp = max(1.0, float(me["max_hp"]))
        hp_frac = hp / max_hp

        energy = float(me["energy"])
        cubes = float(me["cubes"])
        weapons = me["weapons"]
        stats = me["stats"]
        zone = obs["zone"]

        scale = 1.0 + self.size_per_cube * cubes

        radius = float(
            stats.get("radius", self.base_radius * scale)
        )
        height = float(
            stats.get("height", self.base_height * scale)
        )
        muzzle_h = float(
            stats.get("muzzle_height", 7.0 * scale)
        )

        turn_rate = float(stats.get("turn_rate", 4.0))
        pitch_rate = float(stats.get("pitch_rate", 3.0))
        min_pitch = float(stats.get("min_pitch", -0.7))
        max_pitch = float(stats.get("max_pitch", 1.3))
        regen_delay = float(stats.get("regen_delay", 5.0))
        walk_speed = float(stats.get("walk_speed", 11.7))
        boost_speed = float(stats.get("boost_speed", 19.5))

        muzzle = [x, y, z + muzzle_h]
        shot_offset = radius + 0.5

        terrain_here = self.map.terrain_z(x, y)
        on_roof = z > terrain_here + 5.5

        cur_roof = (
            self.map.roof_prism_under(x, y, z)
            if on_roof else None
        )

        act: mf.Action = {"tick": tick}

        self._update_world_memory(
            obs, pos, me["aim"][0], zone
        )

        for ev in obs["events"]:
            et = ev["type"]

            if et == "damaged":
                self.last_damage_t = t
                self.last_combat_t = t

                if ev.get("bearing") is not None:
                    self.last_damage_bearing = float(
                        ev["bearing"]
                    )

            elif et == "hit":
                self.last_combat_t = t

        for bm in obs["beams"]:
            if bm.get("path"):
                self.beam_threats[int(bm["by"])] = (
                    bm["path"][0], t
                )

        self.beam_threats = {
            k: v for k, v in self.beam_threats.items()
            if t - v[1] < 2.5
        }

        if (
            self.last_pos is not None
            and dist2d((x, y), self.last_pos) < 0.14
        ):
            self.stuck_ticks += 1
        else:
            self.stuck_ticks = 0

        self.last_pos = (x, y)

        if tick - self.strafe_flip_tick >= self.strafe_interval:
            self.strafe_dir = -self.strafe_dir
            self.strafe_flip_tick = tick
            self.strafe_interval = self.rng.randint(13, 17)

        if obs["offer"]:
            act["pick"] = self._pick_upgrade(
                obs["offer"], weapons, hp_frac
            )

        # ----------------------------------------------------------
        # Weapon acquisition: preserve Laser + Gun as the default.
        # ----------------------------------------------------------

        w_rank = {
            "laser": 5.3,
            "gun": 4.8,
            "lightning": 4.6,
            "mortar": 1.0,
        }

        held = {
            w["kind"] for w in weapons if w is not None
        }

        charging_slot = None

        for i, w in enumerate(weapons):
            if (
                w is not None
                and w["kind"] == "laser"
                and float(w.get("charge", 0.0)) > 0.0
            ):
                charging_slot = i
                break

        for p in obs["pickups"]:
            if p["kind"] in held:
                continue

            if (
                dist2d((x, y), p["pos"]) >= self.reach - 0.15
                or abs(p["pos"][2] - z) >= 3.8
            ):
                continue

            if weapons[0] is None or weapons[1] is None:
                act["take"] = p["id"]
                break

            if charging_slot is not None:
                continue

            worst = (
                0 if w_rank.get(weapons[0]["kind"], 0.0)
                <= w_rank.get(weapons[1]["kind"], 0.0)
                else 1
            )

            if (
                w_rank.get(p["kind"], 0.0)
                > w_rank.get(weapons[worst]["kind"], 0.0)
            ):
                act["take"] = p["id"]
                act["drop"] = worst
                break

        # ----------------------------------------------------------
        # Threat detection and target scoring.
        # ----------------------------------------------------------

        enemies = [
            e for e in obs["mechs"]
            if e["kind"] == "mech"
        ]
        npcs = [
            e for e in obs["mechs"]
            if e["kind"] == "npc"
        ]

        has_laser = "laser" in held
        has_lightning = "lightning" in held

        enemies_with_los = []
        best_los_enemy = None
        best_any_enemy = None

        best_los_z = 4.5
        best_los_score = -1e9
        best_any_score = -1e9
        closest_los_dist = 999.0

        for e in enemies:
            ep = e["pos"]
            ec = float(e.get("cubes", 0.0))
            escale = 1.0 + self.size_per_cube * ec

            mid_z = 4.5 * escale
            high_z = 7.2 * escale

            d = dist3d(pos, ep)

            los_mid = self.map.has_los(
                muzzle,
                [ep[0], ep[1], ep[2] + mid_z],
            )

            los_high = (
                False if los_mid
                else self.map.has_los(
                    muzzle,
                    [ep[0], ep[1], ep[2] + high_z],
                )
            )

            los = los_mid or los_high

            ehp = float(e.get("hp", 1000.0))

            yaw_to_me = math.atan2(
                y - ep[1], x - ep[0]
            )

            rear_exposed = (
                abs(angle_diff(e["aim"][0], yaw_to_me))
                > PI * 0.52
            )

            score = (
                -d * 1.10
                + (1400.0 - ehp) * 0.20
            )

            if ehp < 450.0:
                score += 205.0

            if rear_exposed:
                score += 55.0

            enemy_weapons = e.get("weapons", [])

            if has_laser and "mortar" in enemy_weapons:
                score += 80.0

            if (
                has_lightning
                and d < 44.0
                and "laser" in enemy_weapons
            ):
                score += 75.0

            if e.get("charging"):
                score += 45.0

            if los:
                enemies_with_los.append(e)
                closest_los_dist = min(
                    closest_los_dist, d
                )

                if score > best_los_score:
                    best_los_score = score
                    best_los_enemy = e
                    best_los_z = (
                        mid_z if los_mid else high_z
                    )

            if score > best_any_score:
                best_any_score = score
                best_any_enemy = e

        los_ids = {
            int(e["id"]) for e in enemies_with_los
        }

        flankers = [
            ep for eid, (ep, st) in self.mem_enemies.items()
            if eid not in los_ids and t - st < 8.0
        ]

        dodge_x, dodge_y, dodge_urgent, lethal_lasers = (
            self._dodge_vector(
                t, pos, radius,
                obs["projectiles"], enemies
            )
        )

        protect_regen = (
            not enemies_with_los
            and hp_frac < 0.90
            and t - self.last_combat_t
            >= max(0.5, regen_delay - 1.5)
        )

        # ----------------------------------------------------------
        # Zone and positioning.
        # ----------------------------------------------------------

        zcx, zcy = zone["next_center"]

        current_center = zone["center"]
        current_radius = max(0.0, float(zone["radius"]))
        next_radius = max(0.0, float(zone["next_radius"]))

        dist_cur = dist2d((x, y), current_center)
        dist_next = math.hypot(x - zcx, y - zcy)

        cur_margin = min(22.0, current_radius * 0.25)
        next_margin = min(12.0, next_radius * 0.25)

        next_safe_radius = max(
            0.0, next_radius - next_margin
        )

        travel_needed = max(
            0.0, dist_next - next_safe_radius
        )

        travel_eta = travel_needed / max(
            8.0, walk_speed
        )

        time_to_shrink = float(zone["shrink_start"]) - t

        shrink_soon = (
            travel_needed > 3.0
            and time_to_shrink
            < max(12.0, travel_eta + 8.0)
        )

        zone_urgent = (
            not me["in_zone"]
            or dist_cur > max(
                1.0, current_radius - cur_margin
            )
            or shrink_soon
            or (
                next_radius < 26.0
                and time_to_shrink < 18.0
                and dist_next > max(
                    2.0, next_radius * 0.45
                )
            )
        )

        if self.climbing_roof is not None:
            if (
                z >= self.climbing_roof[2] - 0.8
                or energy < 10.0
                or zone_urgent
            ):
                self.climbing_roof = None

        from_center = math.atan2(
            y - zcy, x - zcx
        )

        edge_r = max(
            0.0, next_radius * 0.66
        )

        edge_anchor = (
            zcx + math.cos(from_center) * edge_r,
            zcy + math.sin(from_center) * edge_r,
        )

        goal_xy = edge_anchor
        want_boost = False
        want_zero_los = False
        want_slice = False
        allow_climb = False

        keep_on_roof = (
            on_roof
            and not zone_urgent
            and (
                not enemies_with_los
                or all(
                    e["pos"][2] < z - 4.0
                    for e in enemies_with_los
                )
            )
        )

        cover_targets = enemies_with_los
        state_label = "edge"

        # Supply drops: full HP + energy can be worth more than cubes.
        best_drop = None
        best_drop_score = -1e9

        for dr in obs["drops"]:
            dp = dr["pos"]
            dd = dist2d((x, y), dp)

            if (
                dd > 145.0
                or dr["lands_in"] > 15.0
                or (
                    hp_frac > 0.95
                    and cubes >= self.stat_cap
                )
            ):
                continue

            score = (
                (1.0 - hp_frac) * 100.0
                + max(0.0, self.stat_cap - cubes) * 4.0
                - dd * 0.35
                - max(0.0, dr["lands_in"]) * 1.2
            )

            if score > best_drop_score:
                best_drop_score = score
                best_drop = dr

        capturing_drop = False

        if best_drop is not None:
            dp = best_drop["pos"]
            dd = dist2d((x, y), dp)

            capturing_drop = (
                best_drop["lands_in"] <= 0.1
                and dd < max(
                    1.0, best_drop["radius"] - 1.5
                )
                and len(enemies_with_los) < 2
                and hp_frac > 0.25
            )

        # Persistent weapon memory.
        want_weapon_pos = None

        if weapons[1] is None or "mortar" in held:
            candidates = [
                (kind, p)
                for kind, p, st in self.mem_pickups.values()
                if (
                    kind in ("laser", "lightning")
                    and kind not in held
                )
            ]

            if candidates:
                candidate = min(
                    candidates,
                    key=lambda item: dist3d(pos, item[1]),
                )

                if dist3d(pos, candidate[1]) < 195.0:
                    want_weapon_pos = candidate

        best_cube = None

        if self.mem_cubes:
            best_cube = min(
                (
                    p for p, st
                    in self.mem_cubes.values()
                ),
                key=lambda p: dist3d(pos, p),
            )

        cube_range = (
            65.0 if cubes < self.stat_cap else 24.0
        )

        best_crate = None

        if self.mem_crates:
            best_crate = min(
                (
                    p for p, st
                    in self.mem_crates.values()
                ),
                key=lambda p: dist3d(pos, p),
            )

        roof = self._best_roof(x, y, zone)

        roof_safe_to_claim = (
            roof is not None
            and not on_roof
            and has_laser
            and energy > 60.0
            and next_radius > 80.0
            and closest_los_dist > 65.0
            and not zone_urgent
            and (
                cubes >= 2.0
                or hp_frac < 0.90
                or dist2d((x, y), roof) < 42.0
            )
        )

        # ----------------------------------------------------------
        # Movement priorities.
        # ----------------------------------------------------------

        if zone_urgent:
            goal_xy = (zcx, zcy)

            want_boost = (
                not me["in_zone"]
                or (
                    energy > 42.0
                    and travel_needed > 15.0
                )
            )

            keep_on_roof = False
            state_label = "zone-rush"

        elif lethal_lasers:
            if cur_roof is not None:
                goal_xy = (
                    cur_roof.cx, cur_roof.cy
                )
                state_label = "roof-duck"
            else:
                ax = sum(
                    e["pos"][0] for e in lethal_lasers
                ) / len(lethal_lasers)

                ay = sum(
                    e["pos"][1] for e in lethal_lasers
                ) / len(lethal_lasers)

                yaw = (
                    math.atan2(y - ay, x - ax)
                    + self.strafe_dir * PI * 0.45
                )

                goal_xy = (
                    x + math.cos(yaw) * 30.0,
                    y + math.sin(yaw) * 30.0,
                )

                want_zero_los = True
                cover_targets = lethal_lasers
                state_label = "anti-laser"

            want_boost = (
                energy > 22.0
                and charging_slot is None
            )

        elif capturing_drop and best_drop is not None:
            goal_xy = (
                best_drop["pos"][0],
                best_drop["pos"][1],
            )
            keep_on_roof = False
            state_label = "drop-cap"

        elif hp_frac < 0.46 and enemies_with_los:
            if (
                cur_roof is not None
                and all(
                    e["pos"][2] < z - 4.0
                    for e in enemies_with_los
                )
            ):
                goal_xy = (
                    cur_roof.cx, cur_roof.cy
                )
                state_label = "roof-regen"

            else:
                ax = sum(
                    e["pos"][0]
                    for e in enemies_with_los
                ) / len(enemies_with_los)

                ay = sum(
                    e["pos"][1]
                    for e in enemies_with_los
                ) / len(enemies_with_los)

                away = math.atan2(
                    y - ay, x - ax
                )
                inward = math.atan2(
                    zcy - y, zcx - x
                )

                goal_xy = (
                    x + (
                        math.cos(away) * 0.68
                        + math.cos(inward) * 0.32
                    ) * 40.0,
                    y + (
                        math.sin(away) * 0.68
                        + math.sin(inward) * 0.32
                    ) * 40.0,
                )

                want_zero_los = True
                state_label = "escape-cover"

            want_boost = (
                energy > 26.0
                and charging_slot is None
            )

        elif (
            want_weapon_pos is not None
            and closest_los_dist > 34.0
            and hp_frac > 0.42
        ):
            wp = want_weapon_pos[1]

            goal_xy = (wp[0], wp[1])

            want_boost = (
                energy > 35.0
                and charging_slot is None
            )

            allow_climb = wp[2] > z + 4.0
            keep_on_roof = False
            state_label = "weapon-rush"

        elif (
            self.climbing_roof is not None
            and closest_los_dist > 40.0
        ):
            goal_xy = (
                self.climbing_roof[0],
                self.climbing_roof[1],
            )

            allow_climb = True
            state_label = "climb-roof"

        elif roof_safe_to_claim:
            self.climbing_roof = roof

            goal_xy = (roof[0], roof[1])
            allow_climb = True
            state_label = "take-roof"

        elif (
            best_cube is not None
            and dist3d(pos, best_cube) < cube_range
            and len(enemies_with_los) <= 1
            and (
                not on_roof
                or best_cube[2] >= z - 4.0
                or dist3d(pos, best_cube) < 10.0
            )
        ):
            goal_xy = (
                best_cube[0], best_cube[1]
            )

            if best_cube[2] < z - 4.0:
                keep_on_roof = False

            state_label = "cube"

        elif (
            best_drop is not None
            and not enemies_with_los
        ):
            goal_xy = (
                best_drop["pos"][0],
                best_drop["pos"][1],
            )

            want_boost = (
                energy > 42.0
                and dist2d((x, y), goal_xy) > 18.0
            )

            keep_on_roof = False
            state_label = "drop"

        elif best_los_enemy is not None:
            ep = best_los_enemy["pos"]
            d = dist3d(pos, ep)

            if len(enemies_with_los) >= 2:
                ax = sum(
                    e["pos"][0]
                    for e in enemies_with_los
                ) / len(enemies_with_los)

                ay = sum(
                    e["pos"][1]
                    for e in enemies_with_los
                ) / len(enemies_with_los)

                away = math.atan2(
                    y - ay, x - ax
                )

                strafe = (
                    away + self.strafe_dir * 0.50
                )

                goal_xy = (
                    x + math.cos(strafe) * 35.0,
                    y + math.sin(strafe) * 35.0,
                )

                want_slice = True

                want_boost = (
                    energy > 34.0
                    and charging_slot is None
                )

                state_label = "slice-1v1"

            else:
                eyaw = math.atan2(
                    ep[1] - y, ep[0] - x
                )

                if has_laser and has_lightning:
                    opt_range = (
                        35.0 if d < 45.0 else 86.0
                    )
                elif has_laser:
                    opt_range = 92.0
                elif has_lightning:
                    opt_range = 34.0
                else:
                    opt_range = 78.0

                radial = (
                    0.50 if d > opt_range + 16.0
                    else -0.75 if d < opt_range - 14.0
                    else 0.0
                )

                strafe = (
                    eyaw + self.strafe_dir * PI * 0.5
                )

                mx = (
                    math.cos(eyaw) * radial
                    + math.cos(strafe) * 0.92
                )
                my = (
                    math.sin(eyaw) * radial
                    + math.sin(strafe) * 0.92
                )

                goal_xy = (
                    x + mx * 30.0,
                    y + my * 30.0,
                )

                want_boost = (
                    energy > 48.0
                    and d < 52.0
                    and charging_slot is None
                )

                state_label = "kite"

        elif (
            on_roof
            and cur_roof is not None
            and protect_regen
        ):
            goal_xy = (
                cur_roof.cx, cur_roof.cy
            )
            state_label = "roof-recover"

        elif (
            npcs
            and cubes < self.stat_cap
            and hp_frac > 0.52
            and not protect_regen
        ):
            npc = min(
                npcs,
                key=lambda n: dist3d(pos, n["pos"]),
            )

            nd = dist3d(pos, npc["pos"])

            if nd < 105.0:
                nyaw = math.atan2(
                    npc["pos"][1] - y,
                    npc["pos"][0] - x,
                )

                radial = (
                    0.55 if nd > 46.0
                    else -0.55 if nd < 28.0
                    else 0.0
                )

                sang = (
                    nyaw + self.strafe_dir * PI * 0.5
                )

                goal_xy = (
                    x + (
                        math.cos(nyaw) * radial
                        + math.cos(sang) * 0.85
                    ) * 25.0,
                    y + (
                        math.sin(nyaw) * radial
                        + math.sin(sang) * 0.85
                    ) * 25.0,
                )

                keep_on_roof = False
                state_label = "farm-npc"

        elif (
            best_crate is not None
            and cubes < self.stat_cap
            and not protect_regen
            and dist3d(pos, best_crate) < 105.0
        ):
            goal_xy = (
                best_crate[0], best_crate[1]
            )

            allow_climb = best_crate[2] > z + 4.0
            keep_on_roof = False
            state_label = "farm-crate"

        if capturing_drop:
            self.stuck_ticks = 0

        desired_yaw = math.atan2(
            goal_xy[1] - y,
            goal_xy[0] - x,
        )

        if self.stuck_ticks > 4:
            desired_yaw = wrap_angle(
                desired_yaw
                + self.strafe_dir * PI * 0.55
            )

        if (
            capturing_drop
            and best_drop is not None
            and dist2d(
                (x, y), best_drop["pos"]
            ) > max(1.0, best_drop["radius"] - 2.0)
        ):
            move_vec = [
                math.cos(desired_yaw),
                math.sin(desired_yaw),
            ]
            need_jump = False
            need_jet = False

        else:
            move_vec, need_jump, need_jet = (
                self._steer_v11(
                    pos,
                    desired_yaw,
                    zone,
                    (dodge_x, dodge_y),
                    radius,
                    height,
                    cover_targets
                    if (want_zero_los or want_slice)
                    else [],
                    flankers,
                    want_zero_los,
                    want_slice,
                    allow_climb,
                    keep_on_roof,
                    energy,
                )
            )

        jump_cmd = False

        if (
            need_jet
            or (
                self.climbing_roof is not None
                and not me["grounded"]
                and z < self.climbing_roof[2] + 0.5
            )
        ):
            if me["grounded"]:
                jump_cmd = True
            elif energy > 8.0:
                want_boost = True

        elif (
            self.stuck_ticks > 5
            or (
                need_jump
                and self.stuck_ticks > 2
            )
        ):
            if me["grounded"]:
                jump_cmd = True
            elif energy > 22.0:
                want_boost = True

        if (
            dodge_urgent
            and energy > 15.0
            and charging_slot is None
        ):
            want_boost = True

        act["move"] = move_vec
        act["boost"] = bool(want_boost)
        act["jump"] = bool(jump_cmd)

        # ----------------------------------------------------------
        # Precision combat. Fire BOTH slots when advantageous.
        # ----------------------------------------------------------

        fire = [False, False]

        aim_yaw = float(me["aim"][0])
        aim_pitch = float(me["aim"][1])

        target_pos = None
        target_vel = [0.0, 0.0, 0.0]
        target_z_off = 4.5
        target_radius = 2.5
        target_los = False
        target_hp = 1000.0

        if best_los_enemy is not None:
            e = best_los_enemy

            escale = (
                1.0
                + self.size_per_cube * float(e.get("cubes", 0.0))
            )

            target_pos = e["pos"]
            target_vel = e["vel"]
            target_z_off = best_los_z
            target_radius = self.base_radius * escale
            target_los = True
            target_hp = float(e.get("hp", 1000.0))

        elif best_any_enemy is not None:
            e = best_any_enemy

            escale = (
                1.0
                + self.size_per_cube * float(e.get("cubes", 0.0))
            )

            target_pos = e["pos"]
            target_vel = e["vel"]
            target_z_off = 4.5 * escale
            target_radius = self.base_radius * escale
            target_los = False
            target_hp = float(e.get("hp", 1000.0))

        elif (
            npcs
            and hp_frac > 0.45
            and cubes < self.stat_cap
            and not protect_regen
        ):
            npc = min(
                npcs,
                key=lambda n: dist3d(pos, n["pos"]),
            )

            if dist3d(pos, npc["pos"]) < 100.0:
                target_pos = npc["pos"]
                target_vel = npc["vel"]
                target_z_off = 1.8
                target_radius = 1.8
                target_hp = float(npc.get("hp", 350.0))

                target_los = self.map.has_los(
                    muzzle,
                    [
                        target_pos[0],
                        target_pos[1],
                        target_pos[2] + target_z_off,
                    ],
                )

        elif (
            obs["crates"]
            and hp_frac > 0.45
            and cubes < self.stat_cap
            and not protect_regen
        ):
            cr = min(
                obs["crates"],
                key=lambda c: dist3d(pos, c["pos"]),
            )

            if dist3d(pos, cr["pos"]) < 95.0:
                target_pos = cr["pos"]
                target_vel = [0.0, 0.0, 0.0]
                target_z_off = 1.5
                target_radius = 1.6
                target_hp = float(cr.get("hp", 300.0))

                target_los = self.map.has_los(
                    muzzle,
                    [
                        target_pos[0],
                        target_pos[1],
                        target_pos[2] + target_z_off,
                    ],
                )

        if target_pos is not None:
            d_tgt = dist3d(pos, target_pos)

            dx = target_pos[0] - x
            dy = target_pos[1] - y

            direct_yaw = math.atan2(dy, dx)
            direct_pitch = math.atan2(
                target_pos[2] + target_z_off - muzzle[2],
                max(0.1, math.hypot(dx, dy)),
            )

            aim_yaw = direct_yaw
            aim_pitch = direct_pitch

            primary_slot = None
            primary_score = -1e9

            # An already charging laser should be completed,
            # not accidentally interrupted by weapon switching.
            if charging_slot is not None and target_los:
                primary_slot = charging_slot

            else:
                for i, w in enumerate(weapons):
                    if w is None:
                        continue

                    kind = w["kind"]
                    ws = w["stats"]
                    score = -1e9

                    if (
                        kind == "lightning"
                        and target_los
                        and d_tgt
                        <= float(ws.get("range", 45.0)) - 1.0
                        and energy
                        > float(ws.get("energy", 3.0)) + 5.0
                    ):
                        score = 115.0

                    elif (
                        kind == "laser"
                        and target_los
                        and d_tgt
                        <= float(ws.get("range", 280.0)) - 5.0
                    ):
                        if (
                            d_tgt > 38.0
                            or float(w.get("charge", 0.0)) > 0.0
                        ) and (
                            float(w.get("cooldown", 0.0)) <= 0.1
                            or float(w.get("charge", 0.0)) > 0.0
                        ):
                            score = 105.0

                    elif (
                        kind == "gun"
                        and target_los
                        and d_tgt
                        <= float(ws.get("range", 230.0)) - 5.0
                        and float(w.get("reload", 0.0)) <= 0.0
                    ):
                        score = 96.0

                    elif (
                        kind == "mortar"
                        and 18.0 < d_tgt < 225.0
                        and float(w.get("cooldown", 0.0)) <= 0.1
                    ):
                        score = 74.0 if not target_los else 45.0

                    if score > primary_score:
                        primary_score = score
                        primary_slot = i

                if primary_score < 0.0:
                    primary_slot = None

            if primary_slot is not None:
                w = weapons[primary_slot]
                kind = w["kind"]
                ws = w["stats"]

                other = 1 - primary_slot
                ow = weapons[other]

                target_point = [
                    target_pos[0],
                    target_pos[1],
                    target_pos[2] + target_z_off,
                ]

                if kind == "lightning":
                    aim_yaw = direct_yaw
                    aim_pitch = direct_pitch

                    pyaw, ppitch = self._predict_slewed_aim(
                        me["aim"], aim_yaw, aim_pitch,
                        turn_rate, pitch_rate,
                    )

                    half_cone = math.radians(
                        float(ws.get("cone_deg", 30.0)) * 0.46
                    )

                    if (
                        abs(angle_diff(pyaw, direct_yaw))
                        <= half_cone
                        and target_los
                    ):
                        fire[primary_slot] = True

                elif kind == "gun":
                    aim_yaw, aim_pitch = self._lead_aim(
                        muzzle,
                        target_pos,
                        target_vel,
                        float(ws.get("speed", 252.0)),
                        target_z_off,
                        shot_offset,
                    )

                    pyaw, ppitch = self._predict_slewed_aim(
                        me["aim"], aim_yaw, aim_pitch,
                        turn_rate, pitch_rate,
                    )

                    if (
                        abs(angle_diff(pyaw, aim_yaw)) < 0.15
                        and target_los
                        and self.map.barrel_los(
                            pos, muzzle_h, radius,
                            pyaw, ppitch, target_point,
                        )
                    ):
                        fire[primary_slot] = True

                elif kind == "laser":
                    charge = float(w.get("charge", 0.0))
                    max_c = max(
                        0.05, float(ws.get("charge", 0.75))
                    )
                    min_c = float(ws.get("min_charge", 0.15))
                    hold_s = float(ws.get("hold_s", 2.0))

                    # Fire Gun throughout the early charge window.
                    use_gun_aim = (
                        charge < max_c * 0.84
                        and ow is not None
                        and ow["kind"] == "gun"
                        and float(ow.get("reload", 0.0)) <= 0.0
                        and d_tgt
                        <= float(
                            ow["stats"].get("range", 230.0)
                        ) - 5.0
                    )

                    if use_gun_aim:
                        aim_yaw, aim_pitch = self._lead_aim(
                            muzzle,
                            target_pos,
                            target_vel,
                            float(
                                ow["stats"].get("speed", 252.0)
                            ),
                            target_z_off,
                            shot_offset,
                        )

                        fire[primary_slot] = True

                    else:
                        aim_yaw = direct_yaw
                        aim_pitch = direct_pitch

                        pyaw, ppitch = self._predict_slewed_aim(
                            me["aim"], aim_yaw, aim_pitch,
                            turn_rate, pitch_rate,
                        )

                        tolerance = clamp(
                            math.atan2(
                                target_radius * 0.85,
                                max(1.0, d_tgt),
                            ),
                            0.014, 0.14,
                        )

                        aligned = (
                            abs(angle_diff(pyaw, aim_yaw))
                            <= tolerance
                            and abs(ppitch - aim_pitch)
                            <= tolerance * 1.4
                        )

                        barrel_clear = (
                            target_los
                            and self.map.barrel_los(
                                pos, muzzle_h, radius,
                                pyaw, ppitch, target_point,
                            )
                        )

                        # Favor nearly full charge for damage,
                        # but finish critically weakened targets early.
                        ready = (
                            charge >= max_c * 0.90
                            or (
                                target_hp < 155.0
                                and charge >= min_c
                            )
                        )

                        auto = (
                            charge >= max_c + hold_s - 0.20
                        )

                        if (
                            (ready or auto)
                            and aligned
                            and barrel_clear
                        ):
                            # Releasing the trigger fires the beam.
                            fire[primary_slot] = False

                        elif (
                            float(w.get("cooldown", 0.0)) <= 0.05
                            or charge > 0.0
                        ):
                            fire[primary_slot] = True

                elif kind == "mortar":
                    tube = [
                        x, y, z + height + 0.5
                    ]

                    speed = float(ws.get("speed", 72.0))
                    gravity = float(
                        ws.get("gravity", self.mortar_g)
                    )

                    result = self._mortar_aim(
                        tube, target_pos, target_vel,
                        speed, gravity,
                        high_arc=not target_los,
                    )

                    if result is not None:
                        myaw, mpitch, flight_t = result

                        if self.map.arc_clear(
                            tube, myaw, mpitch,
                            speed, gravity, flight_t,
                        ):
                            aim_yaw = myaw
                            aim_pitch = mpitch

                            pyaw, ppitch = (
                                self._predict_slewed_aim(
                                    me["aim"],
                                    aim_yaw, aim_pitch,
                                    turn_rate, pitch_rate,
                                )
                            )

                            if (
                                abs(angle_diff(pyaw, aim_yaw)) < 0.10
                                and abs(ppitch - aim_pitch) < 0.10
                            ):
                                fire[primary_slot] = True

                # Independent secondary trigger.
                # This is the V10/V11 dual-fire breakthrough.
                if ow is not None and target_los:
                    ok = ow["kind"]
                    ows = ow["stats"]

                    pyaw, ppitch = self._predict_slewed_aim(
                        me["aim"],
                        aim_yaw, aim_pitch,
                        turn_rate, pitch_rate,
                    )

                    if (
                        ok == "gun"
                        and float(ow.get("reload", 0.0)) <= 0.0
                        and d_tgt
                        <= float(ows.get("range", 230.0)) - 5.0
                    ):
                        if (
                            abs(angle_diff(pyaw, aim_yaw)) < 0.15
                            and self.map.barrel_los(
                                pos, muzzle_h, radius,
                                pyaw, ppitch, target_point,
                            )
                        ):
                            fire[other] = True

                    elif (
                        ok == "lightning"
                        and energy
                        > float(ows.get("energy", 3.0)) + 6.0
                        and d_tgt
                        <= float(ows.get("range", 45.0)) - 1.0
                    ):
                        half_cone = math.radians(
                            float(
                                ows.get("cone_deg", 30.0)
                            ) * 0.46
                        )

                        if (
                            abs(angle_diff(pyaw, direct_yaw))
                            <= half_cone
                        ):
                            fire[other] = True

            # If no usable primary, maintain target tracking.
            elif len(enemies_with_los) >= 2:
                sx = 0.0
                sy = 0.0

                for e in enemies_with_los:
                    yaw = math.atan2(
                        e["pos"][1] - y,
                        e["pos"][0] - x,
                    )
                    sx += math.cos(yaw)
                    sy += math.sin(yaw)

                if math.hypot(sx, sy) > 0.01:
                    aim_yaw = math.atan2(sy, sx)

        else:
            # Defend the front arc against remembered attacks.
            if self.beam_threats:
                bp = min(
                    self.beam_threats.values(),
                    key=lambda item: dist2d(
                        (x, y), item[0]
                    ),
                )[0]

                aim_yaw = math.atan2(
                    bp[1] - y, bp[0] - x
                )

            elif (
                t - self.last_damage_t < 2.5
                and self.last_damage_bearing is not None
            ):
                aim_yaw = self.last_damage_bearing

            else:
                near = [
                    s for s in obs["sounds"]
                    if (
                        s["dist"] == "near"
                        and s["kind"] in (
                            "gun", "lightning", "laser_charge",
                            "laser", "step", "boost", "jet",
                        )
                    )
                ]

                if near:
                    s = min(
                        near,
                        key=lambda item: item["age"],
                    )
                    aim_yaw = float(s["bearing"])

                elif obs["sounds"]:
                    s = min(
                        obs["sounds"],
                        key=lambda item: (
                            0 if item["dist"] == "near"
                            else 1 if item["dist"] == "mid"
                            else 2,
                            item["age"],
                        ),
                    )
                    aim_yaw = float(s["bearing"])

                else:
                    self.scan_yaw = wrap_angle(
                        self.scan_yaw + 0.45
                    )
                    aim_yaw = self.scan_yaw

        # Do not carry an obsolete laser charge indefinitely
        # after every target disappears.
        if target_pos is None:
            for i, w in enumerate(weapons):
                if (
                    w is not None
                    and w["kind"] == "laser"
                    and float(w.get("charge", 0.0)) > 0.0
                ):
                    fire[i] = False

        # Reload opportunistically, never by stopping a live fight.
        if not enemies_with_los:
            for i, w in enumerate(weapons):
                if (
                    w is not None
                    and w["kind"] == "gun"
                    and not fire[i]
                    and float(w.get("reload", 0.0)) <= 0.0
                ):
                    ammo = float(w.get("ammo", 12))
                    mag = float(
                        w["stats"].get("mag", 12)
                    )

                    if ammo < mag * 0.75:
                        act["reload"] = True

        act["aim"] = [
            wrap_angle(aim_yaw),
            clamp(aim_pitch, min_pitch, max_pitch),
        ]

        act["fire"] = [
            bool(fire[0]),
            bool(fire[1]),
        ]

        mf.draw.label(f"{state_label} | hp {hp:.0f} | c {cubes:.0f}")
        return act


mf.run(Bot)
