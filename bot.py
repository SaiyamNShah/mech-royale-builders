"""Apex-V9 — Fixed Slope/Cylinder Physics, Corner-Slicing 1v1 Isolation, Zero-Whiff Aim & Anti-Squad AI."""
from __future__ import annotations

import json
import math
import os
import random
from typing import Dict, List, Optional, Tuple

import mechfight as mf


def clamp(v: float, lo: float, hi: float) -> float:
    return lo if v < lo else hi if v > hi else v


def wrap_angle(a: float) -> float:
    return (a + math.pi) % (2.0 * math.pi) - math.pi


def angle_diff(a: float, b: float) -> float:
    return wrap_angle(a - b)


def dist2d(a: Tuple[float, float], b: Tuple[float, float]) -> float:
    return math.hypot(a[0] - b[0], a[1] - b[1])


def dist3d(a: List[float], b: List[float]) -> float:
    return math.sqrt((a[0] - b[0]) ** 2 + (a[1] - b[1]) ** 2 + (a[2] - b[2]) ** 2)


def point_in_ring(x: float, y: float, ring: List[float]) -> bool:
    inside = False
    n = len(ring) // 2
    if n < 3:
        return False
    x1, y1 = ring[2 * (n - 1)], ring[2 * (n - 1) + 1]
    for i in range(n):
        x2, y2 = ring[2 * i], ring[2 * i + 1]
        if (y1 > y) != (y2 > y):
            x_int = x1 + (y - y1) * (x2 - x1) / (y2 - y1)
            if x < x_int:
                inside = not inside
        x1, y1 = x2, y2
    return inside


class Prism:
    __slots__ = ("kind", "base", "top", "ring", "holes", "minx", "maxx", "miny", "maxy")

    def __init__(self, raw: dict):
        self.kind: str = raw["kind"]
        self.base: float = float(raw["base"])
        self.top: float = float(raw["top"])
        self.ring: List[float] = raw["ring"]
        self.holes: List[List[float]] = raw.get("holes", [])
        xs = self.ring[0::2]
        ys = self.ring[1::2]
        self.minx, self.maxx = min(xs), max(xs)
        self.miny, self.maxy = min(ys), max(ys)

    def contains_xy(self, x: float, y: float) -> bool:
        if x < self.minx or x > self.maxx or y < self.miny or y > self.maxy:
            return False
        if not point_in_ring(x, y, self.ring):
            return False
        for h in self.holes:
            if point_in_ring(x, y, h):
                return False
        return True


class ArenaMap:
    """Spatial-hashed 3D map with true slope checks, cylinder collision, and fast LOS."""

    def __init__(self, map_dir: str, max_slope_deg: float = 50.0):
        self.cell = 25.0
        self.grid: Dict[Tuple[int, int], List[Prism]] = {}
        self.nx = 0
        self.ny = 0
        self.min_x = 0.0
        self.min_y = 0.0
        self.step = 1.0
        self.scale = 0.01
        self.terrain: Optional[memoryview] = None
        self.bounds = (-508.0, 550.0, -328.0, 384.0)
        self.max_slope_tan = math.tan(math.radians(max(10.0, max_slope_deg - 3.0)))
        self._load(map_dir)

    def _load(self, map_dir: str) -> None:
        wpath = os.path.join(map_dir, "v2", "world.json")
        tpath = os.path.join(map_dir, "v2", "terrain.i16")
        if not os.path.exists(wpath):
            return
        with open(wpath, "r", encoding="utf-8") as f:
            w = json.load(f)
        b = w.get("bounds", {})
        if b:
            self.bounds = (b["minX"] + 4.0, b["maxX"] - 4.0, b["minY"] + 4.0, b["maxY"] - 4.0)
        tmeta = w.get("terrain", {})
        self.nx = int(tmeta.get("nx", 0))
        self.ny = int(tmeta.get("ny", 0))
        self.min_x = float(tmeta.get("minX", 0.0))
        self.min_y = float(tmeta.get("minY", 0.0))
        self.step = float(tmeta.get("step", 1.0))
        self.scale = float(tmeta.get("scale", 0.01))
        if os.path.exists(tpath) and self.nx > 0 and self.ny > 0:
            with open(tpath, "rb") as f:
                raw = f.read()
            self.terrain = memoryview(raw).cast("h")
        for rp in w.get("prisms", []):
            p = Prism(rp)
            ix0 = int(math.floor(p.minx / self.cell))
            ix1 = int(math.floor(p.maxx / self.cell))
            iy0 = int(math.floor(p.miny / self.cell))
            iy1 = int(math.floor(p.maxy / self.cell))
            for ix in range(ix0, ix1 + 1):
                for iy in range(iy0, iy1 + 1):
                    self.grid.setdefault((ix, iy), []).append(p)

    def terrain_z(self, x: float, y: float) -> float:
        if self.terrain is None:
            return 0.0
        gx = clamp((x - self.min_x) / self.step, 0.0, self.nx - 1.001)
        gy = clamp((y - self.min_y) / self.step, 0.0, self.ny - 1.001)
        i, j = int(gx), int(gy)
        fx, fy = gx - i, gy - j
        idx = j * self.nx + i
        z00 = self.terrain[idx]
        z10 = self.terrain[idx + 1]
        z01 = self.terrain[idx + self.nx]
        z11 = self.terrain[idx + self.nx + 1]
        z0 = z00 + (z10 - z00) * fx
        z1 = z01 + (z11 - z01) * fx
        return (z0 + (z1 - z0) * fy) * self.scale

    def is_solid(self, x: float, y: float, z: float) -> bool:
        if z < self.terrain_z(x, y) - 0.15:
            return True
        cell_prisms = self.grid.get((int(math.floor(x / self.cell)), int(math.floor(y / self.cell))))
        if not cell_prisms:
            return False
        for p in cell_prisms:
            if p.base <= z <= p.top and p.contains_xy(x, y):
                return True
        return False

    def _prism_blocks_point(self, x: float, y: float, feet_z: float, step_up: float, height: float) -> bool:
        cell_prisms = self.grid.get((int(math.floor(x / self.cell)), int(math.floor(y / self.cell))))
        if not cell_prisms:
            return False
        head_z = feet_z + height - 0.2
        step_z = feet_z + step_up
        for p in cell_prisms:
            if p.top > step_z and p.base < head_z and p.contains_xy(x, y):
                return True
        return False

    def path_blocked(
        self,
        x0: float,
        y0: float,
        z0: float,
        dx: float,
        dy: float,
        dist: float,
        radius: float,
        height: float,
        step_up: float,
    ) -> bool:
        """True slope + cylinder-aware walkability check along ray (x0, y0) -> (x0+dx*dist, y0+dy*dist)."""
        nx, ny = x0 + dx * dist, y0 + dy * dist
        if nx < self.bounds[0] + radius or nx > self.bounds[1] - radius or ny < self.bounds[2] + radius or ny > self.bounds[3] - radius:
            return True

        # Check steep terrain slope across 2 sub-steps (never blocks gentle campus hills!)
        mid_x, mid_y = x0 + dx * (dist * 0.5), y0 + dy * (dist * 0.5)
        tz0 = self.terrain_z(x0, y0)
        tz_mid = self.terrain_z(mid_x, mid_y)
        tz1 = self.terrain_z(nx, ny)
        half_d = max(1.0, dist * 0.5)
        if (tz_mid - tz0) / half_d > self.max_slope_tan or (tz1 - tz_mid) / half_d > self.max_slope_tan:
            return True

        # Check cylinder center + left/right shoulders at destination
        feet_z = max(z0, tz1) if z0 <= tz0 + 1.5 else z0
        px, py = -dy * (radius * 0.85), dx * (radius * 0.85)
        if self._prism_blocks_point(nx, ny, feet_z, step_up, height):
            return True
        if self._prism_blocks_point(nx + px, ny + py, feet_z, step_up, height):
            return True
        if self._prism_blocks_point(nx - px, ny - py, feet_z, step_up, height):
            return True
        return False

    def has_los(self, a: List[float], b: List[float], step_m: float = 4.0) -> bool:
        dx, dy, dz = b[0] - a[0], b[1] - a[1], b[2] - a[2]
        d = math.sqrt(dx * dx + dy * dy + dz * dz)
        if d < 4.0:
            return True
        steps = max(2, min(46, int(d / step_m)))
        inv = 1.0 / steps
        for k in range(1, steps):
            t = k * inv
            if self.is_solid(a[0] + dx * t, a[1] + dy * t, a[2] + dz * t):
                return False
        return True

    def arc_clear(self, muzzle: List[float], yaw: float, pitch: float, speed: float, g: float, flight_t: float) -> bool:
        """Checks 6 points along mortar arc so we never blast a wall in front of our face."""
        vx = speed * math.cos(pitch) * math.cos(yaw)
        vy = speed * math.cos(pitch) * math.sin(yaw)
        vz = speed * math.sin(pitch)
        for frac in (0.08, 0.18, 0.32, 0.50, 0.70, 0.86):
            tt = flight_t * frac
            px = muzzle[0] + vx * tt
            py = muzzle[1] + vy * tt
            pz = muzzle[2] + vz * tt - 0.5 * g * tt * tt
            if self.is_solid(px, py, pz):
                return False
        return True


# Upgrade priority tuned for 1v15 survival + high burst DPS
UPGRADE_TIER: Dict[str, float] = {
    "armor": 100.0,
    "plating": 97.0,
    "nanites": 95.0,
    "servos": 92.0,
    "lightning_efficiency": 90.0,
    "laser_damage": 89.0,
    "laser_charge": 88.0,
    "gun_damage": 87.0,
    "gun_rate": 86.0,
    "lightning_range": 84.0,
    "gun_mag": 82.0,
    "jets": 79.0,
    "reactor": 77.0,
    "lightning_chain": 76.0,
    "gun_velocity": 73.0,
    "capacitor": 70.0,
    "gyros": 66.0,
    "sensors": 62.0,
    "mortar_reload": 56.0,
    "mortar_splash": 54.0,
    "mortar_velocity": 52.0,
    "laser_pierce": 50.0,
}


class Bot:
    name = "Apex-V9"

    def __init__(self, hello: mf.Hello):
        self.slot = int(hello["slot"])
        self.rng = random.Random(int(hello["seed"]))
        self.cfg = hello["config"]
        mech_cfg = self.cfg.get("mech", {})
        self.base_radius = float(mech_cfg.get("radius", 2.5))
        self.base_height = float(mech_cfg.get("height", 9.0))
        self.step_up = float(mech_cfg.get("step_up", 1.2))
        self.max_slope_deg = float(mech_cfg.get("max_slope_deg", 50.0))
        self.gravity = float(mech_cfg.get("gravity", 22.0))
        self.size_per_cube = float(self.cfg.get("cubes", {}).get("size_per_cube", 0.05))
        self.stat_cap = int(self.cfg.get("cubes", {}).get("stat_cap", 10))
        self.reach = float(self.cfg.get("loot", {}).get("pickup_radius", 4.0))
        self.mortar_g = float(self.cfg.get("weapons", {}).get("mortar", {}).get("gravity", 22.0))
        self.mortar_splash = float(self.cfg.get("weapons", {}).get("mortar", {}).get("splash_radius", 7.0))

        self.map = ArenaMap(hello["map"]["dir"], self.max_slope_deg)
        self.last_damage_t = -10.0
        self.last_damage_bearing: Optional[float] = None
        self.beam_threats: Dict[int, Tuple[List[float], float]] = {}
        self.last_pos: Optional[Tuple[float, float]] = None
        self.stuck_ticks = 0
        self.strafe_dir = 1.0 if (self.slot % 2 == 0) else -1.0
        self.strafe_flip_tick = 0
        self.strafe_interval = 6
        self.scan_yaw = 0.0

    def _pick_upgrade(self, offer: mf.Offer, weapons: List[Optional[mf.WeaponObs]]) -> int:
        held = {w["kind"] for w in weapons if w is not None}
        best_i, best_s = 0, -1e9
        for i, c in enumerate(offer["choices"]):
            cid = c["id"]
            s = UPGRADE_TIER.get(cid, 50.0)
            if any(cid.startswith(k + "_") for k in held):
                s += 5.0
            if s > best_s:
                best_s = s
                best_i = i
        return best_i

    def _lead_aim(
        self,
        muzzle: List[float],
        target_pos: List[float],
        target_vel: List[float],
        proj_speed: float,
        target_z_off: float,
        shot_offset: float,
    ) -> Tuple[float, float]:
        tx, ty, tz = target_pos[0], target_pos[1], target_pos[2] + target_z_off
        vx, vy, vz = target_vel[0], target_vel[1], target_vel[2]
        px, py, pz = tx, ty, tz
        for _ in range(3):
            d = math.sqrt((px - muzzle[0]) ** 2 + (py - muzzle[1]) ** 2 + (pz - muzzle[2]) ** 2)
            t = max(0.0, d - shot_offset) / max(1.0, proj_speed) + 0.04
            px = tx + vx * t
            py = ty + vy * t
            if abs(vz) > 0.5:
                pz = max(self.map.terrain_z(px, py) + target_z_off, tz + vz * t - 0.5 * self.gravity * t * t)
            else:
                pz = tz + vz * t
        dx, dy, dz = px - muzzle[0], py - muzzle[1], pz - muzzle[2]
        return math.atan2(dy, dx), math.atan2(dz, max(0.1, math.hypot(dx, dy)))

    def _mortar_aim(
        self, muzzle: List[float], target_pos: List[float], target_vel: List[float], speed: float, g: float, high_arc: bool
    ) -> Optional[Tuple[float, float, float]]:
        r0 = math.hypot(target_pos[0] - muzzle[0], target_pos[1] - muzzle[1])
        t_est = clamp(r0 / max(10.0, speed * 0.72), 0.1, 4.5)
        px = target_pos[0] + target_vel[0] * t_est * 0.65
        py = target_pos[1] + target_vel[1] * t_est * 0.65
        pz = target_pos[2] + 1.0
        dx, dy, dz = px - muzzle[0], py - muzzle[1], pz - muzzle[2]
        r = math.hypot(dx, dy)
        if r < 17.0:
            return None
        v2 = speed * speed
        disc = v2 * v2 - g * (g * r * r + 2.0 * dz * v2)
        if disc < 0.0:
            return None
        sq = math.sqrt(disc)
        pitch = math.atan2(v2 + sq if high_arc else v2 - sq, g * r)
        vz = speed * math.sin(pitch)
        vh = max(1.0, speed * math.cos(pitch))
        flight_t = r / vh
        return math.atan2(dy, dx), pitch, flight_t

    def _dodge_vector(
        self, pos: List[float], radius: float, projs: List[mf.ProjectileObs], enemies: List[mf.ActorObs]
    ) -> Tuple[float, float, bool]:
        ex, ey = 0.0, 0.0
        urgent = False
        mx, my, mz = pos[0], pos[1], pos[2] + 4.5

        for p in projs:
            px, py, pz = p["pos"]
            vx, vy, vz = p["vel"]
            if p["kind"] == "mortar":
                # Exact parabolic impact-time calculation with gravity
                g = self.mortar_g
                a_q = 0.5 * g
                b_q = -vz
                c_q = pos[2] - pz
                disc = b_q * b_q - 4.0 * a_q * c_q
                if disc < 0.0:
                    continue
                t_imp = (-b_q + math.sqrt(disc)) / (2.0 * a_q)
                if t_imp < 0.0 or t_imp > 2.0:
                    continue
                ix, iy = px + vx * t_imp, py + vy * t_imp
                d_imp = dist2d((mx, my), (ix, iy))
                danger_r = self.mortar_splash + radius + 2.0
                if d_imp < danger_r:
                    away_yaw = math.atan2(my - iy, mx - ix)
                    w = (danger_r - d_imp) / danger_r
                    ex += math.cos(away_yaw) * w * 5.0
                    ey += math.sin(away_yaw) * w * 5.0
                    if t_imp < 0.9:
                        urgent = True
            else:
                v2 = vx * vx + vy * vy + vz * vz
                if v2 < 1.0:
                    continue
                rx, ry, rz = mx - px, my - py, mz - pz
                t = (rx * vx + ry * vy + rz * vz) / v2
                if t < 0.0 or t > 0.65:
                    continue
                cx = px + vx * t - mx
                cy = py + vy * t - my
                cz = pz + vz * t - mz
                if abs(cz) > 6.5:
                    continue
                d_perp = math.hypot(cx, cy)
                thresh = radius + 2.4
                if d_perp < thresh:
                    hv = math.hypot(vx, vy)
                    if hv > 0.1:
                        nx, ny = -vy / hv, vx / hv
                        if nx * cx + ny * cy > 0:
                            nx, ny = -nx, -ny
                        w = (thresh - d_perp) / thresh
                        ex += nx * w * 2.2
                        ey += ny * w * 2.2
                        if d_perp < radius + 0.8:
                            urgent = True

        # Exact ray-distance dodge for charging enemy lasers
        for e in enemies:
            if e.get("charging"):
                ep = e["pos"]
                eyaw = e["aim"][0]
                ldx, ldy = math.cos(eyaw), math.sin(eyaw)
                rx, ry = mx - ep[0], my - ep[1]
                proj = rx * ldx + ry * ldy
                if 0.0 < proj < 260.0:
                    cx, cy = rx - proj * ldx, ry - proj * ldy
                    d_ray = math.hypot(cx, cy)
                    if d_ray < radius + 3.2:
                        nx, ny = -ldy, ldx
                        if nx * cx + ny * cy < 0:
                            nx, ny = -nx, -ny
                        ex += nx * 4.5
                        ey += ny * 4.5
                        urgent = True

        return ex, ey, urgent

    def _steer_with_isolation(
        self,
        pos: List[float],
        desired_yaw: float,
        zone: mf.ZoneObs,
        dodge: Tuple[float, float],
        radius: float,
        height: float,
        threats: List[mf.ActorObs],
        want_zero_los: bool,
        want_1v1_slice: bool,
    ) -> Tuple[List[float], bool]:
        x, y, z = pos[0], pos[1], pos[2]
        zr = max(4.0, zone["radius"] - min(6.0, zone["radius"] * 0.2))
        zcx, zcy = zone["center"]
        best_score = -1e9
        best_dir = [math.cos(desired_yaw), math.sin(desired_yaw)]
        need_jump = False

        # 16 candidate directions around desired_yaw
        for k in range(16):
            off = k * (math.pi / 8.0)
            if off > math.pi:
                off -= 2.0 * math.pi
            ang = desired_yaw + off
            dx, dy = math.cos(ang), math.sin(ang)

            b_near = self.map.path_blocked(x, y, z, dx, dy, 4.5, radius, height, self.step_up)
            b_mid = True if b_near else self.map.path_blocked(x, y, z, dx, dy, 10.5, radius, height, self.step_up)

            score = math.cos(off) * 3.4
            score += (dx * dodge[0] + dy * dodge[1]) * 3.2
            if b_near:
                score -= 12.0
            elif b_mid:
                score -= 3.5

            nx2, ny2 = x + dx * 11.0, y + dy * 11.0
            d_zone = dist2d((nx2, ny2), (zcx, zcy))
            if d_zone > zr:
                score -= (d_zone - zr) * 0.5

            # Geometric Corner-Slicing (sample every 45° = max 8*3 = 24 fast raycasts)
            if threats and not b_near and (k % 2 == 0) and (want_zero_los or want_1v1_slice):
                sx, sy = x + dx * 13.0, y + dy * 13.0
                sz = self.map.terrain_z(sx, sy) + 5.5
                los_cnt = 0
                for th in threats[:3]:
                    tp = th["pos"]
                    if self.map.has_los([sx, sy, sz], [tp[0], tp[1], tp[2] + 7.5], step_m=6.5):
                        los_cnt += 1
                if want_zero_los:
                    if los_cnt == 0:
                        score += 6.5
                    elif los_cnt == 1:
                        score += 1.5
                    else:
                        score -= 4.0 * los_cnt
                elif want_1v1_slice:
                    if los_cnt == 1:
                        score += 6.0  # Clean 1v1 isolation!
                    elif los_cnt == 0:
                        score += 2.0
                    else:
                        score -= 4.5 * (los_cnt - 1)

            if score > best_score:
                best_score = score
                best_dir = [dx, dy]
                need_jump = b_near

        return best_dir, need_jump

    def act(self, obs: mf.Observation) -> mf.Action:
        me = obs["self"]
        t = float(obs["t"])
        tick = int(obs["tick"])
        pos = me["pos"]
        x, y, z = pos[0], pos[1], pos[2]
        hp_frac = me["hp"] / max(1.0, me["max_hp"])
        energy = float(me["energy"])
        cubes = float(me["cubes"])
        weapons = me["weapons"]
        zone = obs["zone"]
        stats = me["stats"]

        scale = 1.0 + self.size_per_cube * cubes
        my_radius = float(stats.get("radius", self.base_radius * scale))
        my_height = float(stats.get("height", self.base_height * scale))
        muzzle_h = float(stats.get("muzzle_height", 7.0 * scale))
        min_pitch = float(stats.get("min_pitch", -1.2))
        max_pitch = float(stats.get("max_pitch", 1.2))
        shot_offset = my_radius + 0.5
        muzzle = [x, y, z + muzzle_h]

        act: mf.Action = {"tick": tick}

        # 1. Track damage events & beams from unseen attackers
        for ev in obs["events"]:
            if ev["type"] == "damaged":
                self.last_damage_t = t
                if ev.get("bearing") is not None:
                    self.last_damage_bearing = float(ev["bearing"])
        for bm in obs["beams"]:
            if bm["path"]:
                self.beam_threats[int(bm["by"])] = (bm["path"][0], t)
        # Prune stale beam threats (>2.5s)
        self.beam_threats = {k: v for k, v in self.beam_threats.items() if t - v[1] < 2.5}

        if self.last_pos is not None and dist2d((x, y), self.last_pos) < 0.14:
            self.stuck_ticks += 1
        else:
            self.stuck_ticks = 0
        self.last_pos = (x, y)

        # Unpredictable juke-strafing (5-8 ticks)
        if tick - self.strafe_flip_tick >= self.strafe_interval:
            self.strafe_dir = -self.strafe_dir
            self.strafe_flip_tick = tick
            self.strafe_interval = self.rng.randint(5, 8)

        # 2. Pick upgrades using exact tier list
        if obs["offer"]:
            act["pick"] = self._pick_upgrade(obs["offer"], weapons)

        # 3. Weapon pickup: Dream combos = Laser+Lightning, Gun+Laser, Gun+Lightning (swap out Mortar ASAP)
        w_rank = {"laser": 5.0, "lightning": 4.6, "gun": 4.2, "mortar": 1.0}
        held_kinds = {w["kind"] for w in weapons if w is not None}
        charging_laser_slot: Optional[int] = None
        for idx_w, w in enumerate(weapons):
            if w is not None and w["kind"] == "laser" and float(w.get("charge", 0.0)) > 0.0:
                charging_laser_slot = idx_w
                break

        for p in obs["pickups"]:
            if p["kind"] in held_kinds:
                continue
            if dist2d((x, y), (p["pos"][0], p["pos"][1])) < self.reach - 0.15 and abs(p["pos"][2] - z) < 3.8:
                if weapons[1] is None or weapons[0] is None:
                    act["take"] = p["id"]
                    break
                elif charging_laser_slot is None:
                    worst_slot = 0 if w_rank[weapons[0]["kind"]] <= w_rank[weapons[1]["kind"]] else 1
                    if w_rank[p["kind"]] > w_rank[weapons[worst_slot]["kind"]]:
                        act["take"] = p["id"]
                        act["drop"] = worst_slot
                        break

        # 4. Analyze visible enemies (exact scaled center height, muzzle LOS, rear-armor exposure)
        enemies = [m for m in obs["mechs"] if m["kind"] == "mech"]
        npcs = [m for m in obs["mechs"] if m["kind"] == "npc"]

        has_laser = "laser" in held_kinds
        has_lightning = "lightning" in held_kinds
        enemies_with_los: List[mf.ActorObs] = []
        best_los_enemy: Optional[mf.ActorObs] = None
        best_los_score = -1e9
        best_any_enemy: Optional[mf.ActorObs] = None
        best_any_score = -1e9

        for e in enemies:
            ep = e["pos"]
            ec = float(e.get("cubes", 0.0))
            ez_mid = ep[2] + 4.5 * (1.0 + self.size_per_cube * ec)
            d = dist3d(pos, ep)
            los = self.map.has_los(muzzle, [ep[0], ep[1], ez_mid])
            ehp = float(e.get("hp", 1000.0))

            # Check if enemy back is exposed to us (1.5x rear-armor bonus!)
            yaw_e_to_me = math.atan2(y - ep[1], x - ep[0])
            rear_exposed = abs(angle_diff(e["aim"][0], yaw_e_to_me)) > (math.pi * 0.52)

            s = -d * 1.15 + (1400.0 - ehp) * 0.18
            if ehp < 420.0:
                s += 180.0
            if rear_exposed:
                s += 55.0
            if has_laser and "mortar" in e.get("weapons", []):
                s += 70.0
            if los:
                enemies_with_los.append(e)
                if s > best_los_score:
                    best_los_score = s
                    best_los_enemy = e
            if s > best_any_score:
                best_any_score = s
                best_any_enemy = e

        # 5. Movement Decision + Geometric Corner-Slicing
        zcx, zcy = zone["next_center"]
        dist_to_cur = dist2d((x, y), (zone["center"][0], zone["center"][1]))
        dist_to_next = dist2d((x, y), (zcx, zcy))
        cur_margin = min(22.0, zone["radius"] * 0.25)
        next_margin = min(12.0, zone["next_radius"] * 0.25)
        shrink_soon = t > zone["shrink_start"] - 14.0 and dist_to_next > max(4.0, zone["next_radius"] - next_margin)
        zone_urgent = (not me["in_zone"]) or (dist_to_cur > max(4.0, zone["radius"] - cur_margin)) or shrink_soon

        ang_from_c = math.atan2(y - zcy, x - zcx)
        edge_r = max(4.0, zone["next_radius"] * 0.58)
        edge_anchor = (zcx + math.cos(ang_from_c) * edge_r, zcy + math.sin(ang_from_c) * edge_r)

        goal_xy = edge_anchor
        want_boost = False
        want_zero_los = False
        want_1v1_slice = False
        state_label = "edge"

        best_drop: Optional[mf.DropObs] = None
        for dr in obs["drops"]:
            if dist2d((x, y), (dr["pos"][0], dr["pos"][1])) < 115.0 and dr["lands_in"] < 8.0 and (hp_frac < 0.85 or cubes < self.stat_cap):
                best_drop = dr
                break

        capturing_drop = (
            best_drop is not None
            and best_drop["lands_in"] <= 0.1
            and dist2d((x, y), (best_drop["pos"][0], best_drop["pos"][1])) < best_drop["radius"] + 4.0
            and len(enemies_with_los) < 2
            and hp_frac >= 0.35
        )
        nearest_cube = min(obs["cubes"], key=lambda item: dist3d(pos, item["pos"])) if obs["cubes"] else None

        if zone_urgent:
            goal_xy = (zcx, zcy)
            want_boost = (not me["in_zone"]) or (energy > 45.0)
            state_label = "zone-rush"
        elif capturing_drop and best_drop is not None:
            goal_xy = (best_drop["pos"][0], best_drop["pos"][1])
            state_label = "drop-cap"
        elif hp_frac < 0.45 and enemies_with_los:
            ax = sum(e["pos"][0] for e in enemies_with_los) / len(enemies_with_los)
            ay = sum(e["pos"][1] for e in enemies_with_los) / len(enemies_with_los)
            away_yaw = math.atan2(y - ay, x - ax)
            z_yaw = math.atan2(zcy - y, zcx - x)
            goal_xy = (
                x + (math.cos(away_yaw) * 0.72 + math.cos(z_yaw) * 0.28) * 40.0,
                y + (math.sin(away_yaw) * 0.72 + math.sin(z_yaw) * 0.28) * 40.0,
            )
            want_zero_los = True
            want_boost = energy > 25.0 and charging_laser_slot is None
            state_label = "escape-cover"
        elif nearest_cube is not None and dist3d(pos, nearest_cube["pos"]) < 52.0 and len(enemies_with_los) <= 1:
            goal_xy = (nearest_cube["pos"][0], nearest_cube["pos"][1])
            state_label = "cube"
        elif best_drop is not None and len(enemies_with_los) == 0:
            goal_xy = (best_drop["pos"][0], best_drop["pos"][1])
            want_boost = energy > 45.0 and dist2d((x, y), goal_xy) > 12.0
            state_label = "drop"
        elif best_los_enemy is not None:
            d_en = dist3d(pos, best_los_enemy["pos"])
            if len(enemies_with_los) >= 2:
                # Corner-slice to isolate 1v1 while kiting away from squad centroid
                ax = sum(e["pos"][0] for e in enemies_with_los) / len(enemies_with_los)
                ay = sum(e["pos"][1] for e in enemies_with_los) / len(enemies_with_los)
                away_yaw = math.atan2(y - ay, x - ax)
                strafe_ang = away_yaw + self.strafe_dir * 0.55
                goal_xy = (x + math.cos(strafe_ang) * 35.0, y + math.sin(strafe_ang) * 35.0)
                want_1v1_slice = True
                want_boost = energy > 35.0 and charging_laser_slot is None
                state_label = "slice-1v1"
            else:
                en_yaw = math.atan2(best_los_enemy["pos"][1] - y, best_los_enemy["pos"][0] - x)
                # Optimal engagement distance based on loadout
                if has_lightning and not has_laser:
                    opt_range = 34.0
                elif has_laser and not has_lightning:
                    opt_range = 88.0
                else:
                    opt_range = 36.0 if d_en < 48.0 else 74.0
                radial = 0.55 if d_en > opt_range + 14.0 else (-0.70 if d_en < opt_range - 12.0 else 0.0)
                strafe_ang = en_yaw + self.strafe_dir * (math.pi * 0.5)
                mx = math.cos(en_yaw) * radial + math.cos(strafe_ang) * 0.90
                my = math.sin(en_yaw) * radial + math.sin(strafe_ang) * 0.90
                goal_xy = (x + mx * 30.0, y + my * 30.0)
                want_boost = energy > 55.0 and d_en < 45.0 and charging_laser_slot is None
                state_label = f"duel-{best_los_enemy['id']:.0f}"
        elif weapons[1] is None and obs["pickups"]:
            cand = [p for p in obs["pickups"] if p["kind"] in ("laser", "lightning")]
            if cand:
                p = min(cand, key=lambda item: dist3d(pos, item["pos"]))
                if dist3d(pos, p["pos"]) < 110.0:
                    goal_xy = (p["pos"][0], p["pos"][1])
                    want_boost = energy > 50.0
                    state_label = f"loot-{p['kind']}"
        elif npcs and cubes < self.stat_cap and hp_frac > 0.52:
            npc = min(npcs, key=lambda n: dist3d(pos, n["pos"]))
            if dist3d(pos, npc["pos"]) < 100.0:
                goal_xy = (npc["pos"][0], npc["pos"][1])
                state_label = "farm-npc"
        elif obs["crates"] and cubes < self.stat_cap:
            cr = min(obs["crates"], key=lambda item: dist3d(pos, item["pos"]))
            if dist3d(pos, cr["pos"]) < 95.0:
                goal_xy = (cr["pos"][0], cr["pos"][1])
                state_label = "farm-crate"

        desired_yaw = math.atan2(goal_xy[1] - y, goal_xy[0] - x)
        if self.stuck_ticks > 4:
            desired_yaw = wrap_angle(desired_yaw + self.strafe_dir * (math.pi * 0.55))

        dodge_x, dodge_y, dodge_urgent = self._dodge_vector(pos, my_radius, obs["projectiles"], enemies)
        if capturing_drop and best_drop is not None and dist2d((x, y), (best_drop["pos"][0], best_drop["pos"][1])) > best_drop["radius"] - 2.0:
            move_vec = [math.cos(desired_yaw), math.sin(desired_yaw)]
            need_jump = False
        else:
            move_vec, need_jump = self._steer_with_isolation(
                pos,
                desired_yaw,
                zone,
                (dodge_x, dodge_y),
                my_radius,
                my_height,
                enemies_with_los if (want_zero_los or want_1v1_slice) else [],
                want_zero_los,
                want_1v1_slice,
            )

        # Only jump when genuinely stuck on a ledge (keep feet planted for 58.5 m/s^2 agility!)
        jump_cmd = False
        if self.stuck_ticks > 5 or (need_jump and self.stuck_ticks > 2):
            if me["grounded"]:
                jump_cmd = True
            elif energy > 25.0:
                want_boost = True
        if dodge_urgent and energy > 12.0 and charging_laser_slot is None:
            want_boost = True

        act["move"] = move_vec
        act["boost"] = want_boost
        act["jump"] = jump_cmd

        # 6. Zero-Whiff Precision Aim & Dual-Fire Controller
        fire = [False, False]
        aim_yaw, aim_pitch = me["aim"][0], 0.0
        target_pos: Optional[List[float]] = None
        target_vel = [0.0, 0.0, 0.0]
        target_z_off = 4.5
        target_radius = 2.5
        target_los = False
        target_hp = 1000.0

        if best_los_enemy is not None:
            ec = float(best_los_enemy.get("cubes", 0.0))
            escale = 1.0 + self.size_per_cube * ec
            target_pos = best_los_enemy["pos"]
            target_vel = best_los_enemy["vel"]
            target_z_off = 4.5 * escale
            target_radius = self.base_radius * escale
            target_los = True
            target_hp = float(best_los_enemy.get("hp", 1000.0))
        elif best_any_enemy is not None:
            ec = float(best_any_enemy.get("cubes", 0.0))
            escale = 1.0 + self.size_per_cube * ec
            target_pos = best_any_enemy["pos"]
            target_vel = best_any_enemy["vel"]
            target_z_off = 4.5 * escale
            target_radius = self.base_radius * escale
            target_los = False
            target_hp = float(best_any_enemy.get("hp", 1000.0))
        elif npcs and hp_frac > 0.45 and cubes < self.stat_cap:
            npc = min(npcs, key=lambda n: dist3d(pos, n["pos"]))
            if dist3d(pos, npc["pos"]) < 95.0:
                target_pos = npc["pos"]
                target_vel = npc["vel"]
                target_z_off = 1.8
                target_radius = 1.8
                target_los = self.map.has_los(muzzle, [target_pos[0], target_pos[1], target_pos[2] + 1.8])
                target_hp = float(npc.get("hp", 350.0))
        elif obs["crates"] and hp_frac > 0.45 and cubes < self.stat_cap:
            cr = min(obs["crates"], key=lambda c: dist3d(pos, c["pos"]))
            if dist3d(pos, cr["pos"]) < 85.0:
                target_pos = cr["pos"]
                target_z_off = 1.5
                target_radius = 1.6
                target_los = self.map.has_los(muzzle, [target_pos[0], target_pos[1], target_pos[2] + 1.5])
                target_hp = float(cr.get("hp", 300.0))

        # Preserve an already-charging laser so it NEVER misfires into air/walls!
        if charging_laser_slot is not None:
            lw = weapons[charging_laser_slot]
            assert lw is not None
            fire[charging_laser_slot] = True  # Default: keep holding trigger!

        if target_pos is not None:
            d_tgt = dist3d(pos, target_pos)
            direct_yaw = math.atan2(target_pos[1] - y, target_pos[0] - x)
            direct_pitch = math.atan2(target_pos[2] + target_z_off - muzzle[2], max(0.1, dist2d((x, y), (target_pos[0], target_pos[1]))))
            aim_yaw, aim_pitch = direct_yaw, direct_pitch

            # Choose primary weapon (if laser is already charging with LOS, finish the beam first!)
            primary_slot: Optional[int] = None
            if charging_laser_slot is not None and target_los:
                primary_slot = charging_laser_slot
            else:
                primary_score = -1.0
                for i, w in enumerate(weapons):
                    if w is None:
                        continue
                    k = w["kind"]
                    ws = w["stats"]
                    s = -1.0
                    if k == "lightning" and target_los and d_tgt <= float(ws.get("range", 45.0)) - 1.0 and energy > 8.0:
                        s = 115.0
                    elif k == "laser" and target_los and d_tgt <= float(ws.get("range", 280.0)) - 5.0:
                        if (d_tgt > 44.0 or float(w.get("charge", 0.0)) > 0.0) and (w["cooldown"] <= 0.1 or float(w.get("charge", 0.0)) > 0.0) and not dodge_urgent:
                            s = 102.0
                    elif k == "gun" and target_los and d_tgt <= float(ws.get("range", 230.0)) - 5.0 and float(w.get("reload", 0.0)) == 0.0:
                        s = 96.0
                    elif k == "mortar" and 18.0 < d_tgt < 225.0 and w["cooldown"] <= 0.1:
                        s = 72.0 if not target_los else 45.0
                    if s > primary_score:
                        primary_score = s
                        primary_slot = i

            if primary_slot is not None:
                w = weapons[primary_slot]
                assert w is not None
                k = w["kind"]
                ws = w["stats"]
                if k == "lightning":
                    # Lead aim for dual-fire gun while staying inside exact lightning cone!
                    aim_yaw, aim_pitch = self._lead_aim(muzzle, target_pos, target_vel, 252.0, target_z_off, shot_offset)
                    cone_half = math.radians(float(ws.get("cone_deg", 30.0)) * 0.46)
                    if abs(angle_diff(me["aim"][0], direct_yaw)) <= cone_half:
                        fire[primary_slot] = True
                elif k == "gun":
                    aim_yaw, aim_pitch = self._lead_aim(muzzle, target_pos, target_vel, float(ws.get("speed", 252.0)), target_z_off, shot_offset)
                    if abs(angle_diff(me["aim"][0], aim_yaw)) < 0.15:
                        fire[primary_slot] = True
                elif k == "laser":
                    aim_yaw, aim_pitch = direct_yaw, direct_pitch
                    charge = float(w.get("charge", 0.0))
                    max_c = float(ws.get("charge", 0.75))
                    min_c = float(ws.get("min_charge", 0.15))
                    hold_s = float(ws.get("hold_s", 2.0))
                    hit_tol = clamp(math.atan2(target_radius * 0.82, max(1.0, d_tgt)), 0.012, 0.14)
                    yaw_err = abs(angle_diff(me["aim"][0], aim_yaw))
                    pitch_err = abs(me["aim"][1] - aim_pitch)
                    about_to_autofire = charge >= (max_c + hold_s - 0.20)
                    ready_to_release = (charge >= max_c * 0.88) or (target_hp < 155.0 and charge >= min_c)
                    if (ready_to_release or about_to_autofire) and yaw_err <= hit_tol and pitch_err <= hit_tol * 1.35:
                        fire[primary_slot] = False  # Release hitscan beam on target!
                    elif w["cooldown"] <= 0.05 or charge > 0.0:
                        fire[primary_slot] = True
                elif k == "mortar":
                    m_res = self._mortar_aim(
                        [x, y, z + my_height + 0.5],
                        target_pos,
                        target_vel,
                        float(ws.get("speed", 72.0)),
                        float(ws.get("gravity", self.mortar_g)),
                        high_arc=not target_los,
                    )
                    if m_res is not None:
                        myaw, mpitch, ft = m_res
                        if self.map.arc_clear([x, y, z + my_height + 0.5], myaw, mpitch, float(ws.get("speed", 72.0)), float(ws.get("gravity", self.mortar_g)), ft):
                            aim_yaw, aim_pitch = myaw, mpitch
                            if abs(angle_diff(me["aim"][0], aim_yaw)) < 0.10 and abs(me["aim"][1] - aim_pitch) < 0.10:
                                fire[primary_slot] = True

                # Opportunistic dual-fire secondary slot when aligned
                other = 1 - primary_slot
                ow = weapons[other]
                if ow is not None and target_los:
                    ok = ow["kind"]
                    ows = ow["stats"]
                    if ok == "gun" and float(ow.get("reload", 0.0)) == 0.0 and d_tgt <= float(ows.get("range", 230.0)) - 5.0:
                        if abs(angle_diff(me["aim"][0], aim_yaw)) < 0.14:
                            fire[other] = True
                    elif ok == "lightning" and energy > 10.0 and d_tgt <= float(ows.get("range", 45.0)) - 1.0:
                        cone_half = math.radians(float(ows.get("cone_deg", 30.0)) * 0.46)
                        if abs(angle_diff(me["aim"][0], direct_yaw)) <= cone_half:
                            fire[other] = True
        else:
            # No visible target: snap torso toward unseen beam shooter, recent damage, or near sound
            if self.beam_threats:
                bp = min(self.beam_threats.values(), key=lambda item: dist2d((x, y), (item[0][0], item[0][1])))[0]
                aim_yaw = math.atan2(bp[1] - y, bp[0] - x)
            elif t - self.last_damage_t < 2.5 and self.last_damage_bearing is not None:
                aim_yaw = self.last_damage_bearing
            else:
                near_sounds = [s for s in obs["sounds"] if s["dist"] == "near" and s["kind"] in ("gun", "lightning", "laser_charge", "laser", "step", "boost", "jet")]
                if near_sounds:
                    s = min(near_sounds, key=lambda item: item["age"])
                    aim_yaw = float(s["bearing"])
                elif obs["sounds"]:
                    s = min(obs["sounds"], key=lambda item: (0 if item["dist"] == "near" else 1 if item["dist"] == "mid" else 2, item["age"]))
                    aim_yaw = float(s["bearing"])
                else:
                    self.scan_yaw = wrap_angle(self.scan_yaw + 0.45)
                    aim_yaw = self.scan_yaw

        # Opportunistic reload whenever gun is not firing and mag < 50%
        for idx_w, w in enumerate(weapons):
            if w is not None and w["kind"] == "gun" and not fire[idx_w] and float(w.get("reload", 0.0)) == 0.0:
                if float(w.get("ammo", 12)) < float(w["stats"].get("mag", 12)) * 0.5:
                    act["reload"] = True

        act["aim"] = [aim_yaw, clamp(aim_pitch, min_pitch, max_pitch)]
        act["fire"] = fire

        mf.draw.label(f"{state_label} | hp {me['hp']:.0f} | c {cubes:.0f}")
        return act


mf.run(Bot)