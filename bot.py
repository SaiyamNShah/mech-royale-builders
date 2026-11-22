"""Apex-V12 — V11 + Observed-Laser Cooldown Ledger (unseen = UNSAFE), 0.28 s Charge Threshold, Barrel-Origin Laser Jiggle-Peek & Barrel-Gated Dual-Fire."""
from __future__ import annotations

import json
import math
import os
import random
import time
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
    __slots__ = ("kind", "base", "top", "ring", "holes", "minx", "maxx", "miny", "maxy", "cx", "cy")

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
        self.cx = 0.5 * (self.minx + self.maxx)
        self.cy = 0.5 * (self.miny + self.maxy)

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
    """Spatial-hashed 3D map with true slope/cylinder physics, rooftop index, and support-height queries."""

    def __init__(self, map_dir: str, max_slope_deg: float = 50.0):
        self.cell = 25.0
        self.grid: Dict[Tuple[int, int], List[Prism]] = {}
        self.roofs: List[Tuple[float, float, float]] = []
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
            wpath = os.path.join(map_dir, "world.json")
            tpath = os.path.join(map_dir, "terrain.i16")
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
            if p.kind == "building" and (p.maxx - p.minx) > 16.0 and (p.maxy - p.miny) > 16.0:
                if p.contains_xy(p.cx, p.cy):
                    rel_h = p.top - self.terrain_z(p.cx, p.cy)
                    if 8.5 <= rel_h <= 28.0:
                        self.roofs.append((p.cx, p.cy, p.top))

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

    def support_z(self, x: float, y: float, feet_z: float) -> float:
        """Returns highest walkable surface at (x, y) at or below feet_z + 1.5."""
        best = self.terrain_z(x, y)
        cell_prisms = self.grid.get((int(math.floor(x / self.cell)), int(math.floor(y / self.cell))))
        if cell_prisms:
            for p in cell_prisms:
                if p.top <= feet_z + 1.5 and p.top > best and p.contains_xy(x, y):
                    best = p.top
        return best

    def roof_prism_under(self, x: float, y: float, feet_z: float) -> Optional[Prism]:
        cell_prisms = self.grid.get((int(math.floor(x / self.cell)), int(math.floor(y / self.cell))))
        if not cell_prisms:
            return None
        best_p: Optional[Prism] = None
        best_top = -1e9
        for p in cell_prisms:
            if abs(p.top - feet_z) <= 2.2 and p.top > best_top and p.contains_xy(x, y):
                best_top = p.top
                best_p = p
        return best_p

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

    def _prism_wall_height(self, x: float, y: float, feet_z: float, step_up: float, height: float) -> float:
        cell_prisms = self.grid.get((int(math.floor(x / self.cell)), int(math.floor(y / self.cell))))
        if not cell_prisms:
            return 0.0
        head_z = feet_z + height - 0.2
        step_z = feet_z + step_up
        max_h = 0.0
        for p in cell_prisms:
            if p.top > step_z and p.base < head_z and p.contains_xy(x, y):
                h = p.top - feet_z
                if h > max_h:
                    max_h = h
        return max_h

    def wall_height_along(
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
    ) -> float:
        nx, ny = x0 + dx * dist, y0 + dy * dist
        if nx < self.bounds[0] + radius or nx > self.bounds[1] - radius or ny < self.bounds[2] + radius or ny > self.bounds[3] - radius:
            return 99.0

        mid_x, mid_y = x0 + dx * (dist * 0.5), y0 + dy * (dist * 0.5)
        tz0 = self.terrain_z(x0, y0)
        tz_mid = self.terrain_z(mid_x, mid_y)
        tz1 = self.terrain_z(nx, ny)
        half_d = max(1.0, dist * 0.5)
        if z0 <= tz0 + 2.0:
            if (tz_mid - tz0) / half_d > self.max_slope_tan or (tz1 - tz_mid) / half_d > self.max_slope_tan:
                return 99.0

        feet_z = max(z0, tz1) if z0 <= tz0 + 1.5 else z0
        px, py = -dy * (radius * 0.85), dx * (radius * 0.85)
        h = self._prism_wall_height(nx, ny, feet_z, step_up, height)
        h_l = self._prism_wall_height(nx + px, ny + py, feet_z, step_up, height)
        h_r = self._prism_wall_height(nx - px, ny - py, feet_z, step_up, height)
        return max(h, h_l, h_r)

    def has_los(self, a: List[float], b: List[float], step_m: float = 4.0) -> bool:
        dx, dy, dz = b[0] - a[0], b[1] - a[1], b[2] - a[2]
        d = math.sqrt(dx * dx + dy * dy + dz * dz)
        if d < 3.5:
            return True
        steps = max(2, min(46, int(d / step_m)))
        inv = 1.0 / steps
        for k in range(1, steps):
            t = k * inv
            if self.is_solid(a[0] + dx * t, a[1] + dy * t, a[2] + dz * t):
                return False
        return True

    def barrel_clear(
        self, muzzle: List[float], yaw: float, pitch: float, shot_offset: float, target: List[float], step_m: float = 2.0
    ) -> bool:
        """Server firing geometry: shot emerges shot_offset (= radius + 0.5) ahead of the muzzle along the REAL aim.
        True only if that short barrel segment is open AND the ray from the emergence point reaches target."""
        cp = math.cos(pitch)
        ux = cp * math.cos(yaw)
        uy = cp * math.sin(yaw)
        uz = math.sin(pitch)
        n = max(2, int(math.ceil(shot_offset / 0.5)))
        for i in range(1, n + 1):
            s = shot_offset * i / n
            if self.is_solid(muzzle[0] + ux * s, muzzle[1] + uy * s, muzzle[2] + uz * s):
                return False
        origin = [muzzle[0] + ux * shot_offset, muzzle[1] + uy * shot_offset, muzzle[2] + uz * shot_offset]
        return self.has_los(origin, target, step_m=step_m)

    def arc_clear(self, muzzle: List[float], yaw: float, pitch: float, speed: float, g: float, flight_t: float) -> bool:
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


# Round-2 Phase-5 Winning Upgrade Priority
UPGRADE_TIER: Dict[str, float] = {
    "nanites": 100.0,
    "armor": 97.0,
    "plating": 94.0,
    "laser_damage": 92.0,
    "laser_charge": 91.0,
    "gun_damage": 90.0,
    "gun_rate": 89.0,
    "servos": 87.0,
    "lightning_efficiency": 86.0,
    "gun_mag": 84.0,
    "lightning_range": 82.0,
    "jets": 79.0,
    "reactor": 77.0,
    "gun_velocity": 75.0,
    "lightning_chain": 73.0,
    "capacitor": 69.0,
    "gyros": 65.0,
    "sensors": 61.0,
    "mortar_reload": 56.0,
    "mortar_splash": 54.0,
    "mortar_velocity": 52.0,
    "laser_pierce": 50.0,
}


class Bot:
    name = "Apex-V12"

    # A/B switches and tunables
    ENABLE_PEEK = True
    ENABLE_LEDGER_ROOF = True
    PEEK_MARGIN = 0.35        # 0.10 release latency + 0.25 safety on top of the exposure window
    LASER_DANGER_T = 0.28     # enemy laser charge elapsed (s) at which we treat it as lethal (2x laser_charge => 0.42 s total)

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
        self.last_combat_t = -10.0
        self.last_damage_bearing: Optional[float] = None
        self.beam_threats: Dict[int, Tuple[List[float], float]] = {}
        self.last_pos: Optional[Tuple[float, float]] = None
        self.stuck_ticks = 0
        self.strafe_dir = 1.0 if (self.slot % 2 == 0) else -1.0
        self.strafe_flip_tick = 0
        self.strafe_interval = 14
        self.scan_yaw = 0.0

        # Round-2 Persistent World Memory (eliminates FOV amnesia!)
        self.mem_pickups: Dict[int, Tuple[str, List[float], float]] = {}  # id -> (kind, pos, seen_t)
        self.mem_cubes: Dict[int, Tuple[List[float], float]] = {}        # id -> (pos, seen_t)
        self.mem_crates: Dict[int, Tuple[List[float], float]] = {}       # id -> (pos, seen_t)
        self.mem_enemies: Dict[int, Tuple[List[float], float]] = {}      # id -> (pos, seen_t)
        self.enemy_charge_start: Dict[int, float] = {}                   # id -> t when laser charging began
        self.climbing_roof: Optional[Tuple[float, float, float]] = None  # Hysteresis roof climb target

        # V12 Upgrade C: observed-laser cooldown ledger (beams carry shooter id => exact; absent id => UNSAFE)
        self.enemy_laser_ready: Dict[int, float] = {}                    # id -> t when that enemy's laser is ready again
        self.laser_cd = float(self.cfg.get("weapons", {}).get("laser", {}).get("cooldown", 1.65))

        # V12 Upgrade A: barrel-origin jiggle-peek state
        self.peek_owned_charge = False
        self.peek_prev_mode = False
        self.peek_home: Optional[Tuple[float, float]] = None
        self.peek_axis: Tuple[float, float] = (0.0, 0.0)
        self.peek_return_until = -10.0
        self.peek_block_until = -10.0
        self.peek_started_t = -10.0
        self.peek_side = 0.0
        self.peek_lock_until = -10.0
        self.peek_plan: Optional[Tuple[int, float, float, float, float]] = None  # (target id, cx, cy, s, planned_t)

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

    def _update_world_memory(self, obs: mf.Observation, pos: List[float], aim_yaw: float, zone: mf.ZoneObs) -> None:
        t = float(obs["t"])
        x, y = pos[0], pos[1]
        zcx, zcy = zone["center"]
        zr = zone["radius"]

        # Track visible IDs this tick
        vis_p = set()
        for p in obs["pickups"]:
            pid = int(p["id"])
            vis_p.add(pid)
            self.mem_pickups[pid] = (p["kind"], p["pos"], t)

        vis_c = set()
        for c in obs["cubes"]:
            cid = int(c["id"])
            vis_c.add(cid)
            self.mem_cubes[cid] = (c["pos"], t)

        vis_cr = set()
        for cr in obs["crates"]:
            crid = int(cr["id"])
            vis_cr.add(crid)
            self.mem_crates[crid] = (cr["pos"], t)

        # Evict taken/destroyed/out-of-zone items when we are looking right at them or within proximity sensor (38m)
        def should_evict(item_pos: List[float], seen_t: float, max_age: float) -> bool:
            if t - seen_t > max_age:
                return True
            if dist2d((item_pos[0], item_pos[1]), (zcx, zcy)) > zr + 5.0:
                return True
            d = dist2d((x, y), (item_pos[0], item_pos[1]))
            if d < 32.0:
                return True
            if d < 90.0 and abs(angle_diff(math.atan2(item_pos[1] - y, item_pos[0] - x), aim_yaw)) < 0.65:
                return True
            return False

        for pid in list(self.mem_pickups.keys()):
            if pid not in vis_p and should_evict(self.mem_pickups[pid][1], self.mem_pickups[pid][2], 65.0):
                del self.mem_pickups[pid]
        for cid in list(self.mem_cubes.keys()):
            if cid not in vis_c and should_evict(self.mem_cubes[cid][0], self.mem_cubes[cid][1], 45.0):
                del self.mem_cubes[cid]
        for crid in list(self.mem_crates.keys()):
            if crid not in vis_cr and should_evict(self.mem_crates[crid][0], self.mem_crates[crid][1], 65.0):
                del self.mem_crates[crid]

        # Track enemy positions & exact laser charge start timestamps
        vis_e = set()
        for m in obs["mechs"]:
            if m["kind"] == "mech":
                eid = int(m["id"])
                vis_e.add(eid)
                self.mem_enemies[eid] = (m["pos"], t)
                if m.get("charging"):
                    if eid not in self.enemy_charge_start:
                        self.enemy_charge_start[eid] = t
                else:
                    self.enemy_charge_start.pop(eid, None)
        for eid in list(self.enemy_charge_start.keys()):
            if eid not in vis_e:
                del self.enemy_charge_start[eid]
        for eid in list(self.mem_enemies.keys()):
            if t - self.mem_enemies[eid][1] > 8.0:
                del self.mem_enemies[eid]

    def laser_safe_for(self, eid: int, now: float, window: float) -> bool:
        """True only if enemy eid was OBSERVED firing its laser and the cooldown outlasts `window`.
        Missing entry defaults to -1e9 => UNSAFE."""
        return self.enemy_laser_ready.get(eid, -1e9) - now > window

    def _rear_or_close_threat(self, t: float, x: float, y: float, yaw0: float, pid: int) -> bool:
        """Veto peeking while another (remembered <=4 s) enemy is close, or behind our torso aim (rear armor is 1.5x)."""
        for eid2, (ep2, seen) in self.mem_enemies.items():
            if eid2 == pid or t - seen > 4.0:
                continue
            d2 = dist2d((x, y), (ep2[0], ep2[1]))
            if d2 < 55.0:
                return True
            if d2 < 110.0 and abs(angle_diff(math.atan2(ep2[1] - y, ep2[0] - x), yaw0)) > math.pi * 0.52:
                return True
        return False

    def _goal_clear(
        self, goal: Tuple[float, float], muzzle_h: float, z: float, shot_offset: float, tp: List[float], tgt: List[float]
    ) -> bool:
        gx, gy = goal
        gm = [gx, gy, self.map.support_z(gx, gy, z) + muzzle_h]
        gyaw = math.atan2(tp[1] - gy, tp[0] - gx)
        gpit = math.atan2(tgt[2] - gm[2], max(0.1, math.hypot(tp[0] - gx, tp[1] - gy)))
        return self.map.barrel_clear(gm, gyaw, gpit, shot_offset, tgt)

    def _find_peek(
        self,
        t: float,
        pos: List[float],
        muzzle_h: float,
        radius: float,
        height: float,
        shot_offset: float,
        tp: List[float],
        z_off: float,
        zone: mf.ZoneObs,
        others: List[mf.ActorObs],
        strict_edge: bool,
        pid: int,
        needs_ledger: bool,
        aim: List[float],
        turn_rate: float,
        pitch_rate: float,
        walk_v: float,
        rem_pre: float,
    ) -> Optional[Tuple[float, float, float]]:
        """Smallest lateral side-step (|s| <= 4.5 m) whose REAL barrel ray (muzzle + radius+0.5 ahead) reaches the target,
        with wall/slope/ledge checks along the walk and a LOS veto against other enemies. Soft-capped at ~1.4 ms."""
        t0 = time.perf_counter()
        x, y, z = pos[0], pos[1], pos[2]
        theta = math.atan2(tp[1] - y, tp[0] - x)
        nx, ny = -math.sin(theta), math.cos(theta)
        zr = max(4.0, zone["radius"] - min(6.0, zone["radius"] * 0.2))
        zcx, zcy = zone["center"]
        locked = t < self.peek_lock_until and self.peek_side != 0.0
        pref = self.peek_side if locked else self.strafe_dir
        if locked:
            offs = sorted((-1.5, 1.5, -3.0, 3.0, -4.5, 4.5), key=lambda s: (0 if s * pref > 0 else 1, abs(s)))
        else:
            offs = sorted((-1.5, 1.5, -3.0, 3.0, -4.5, 4.5), key=lambda s: (abs(s), 0 if s * pref > 0 else 1))
        tgt = [tp[0], tp[1], tp[2] + z_off]
        for s in offs:
            if time.perf_counter() - t0 > 0.0014:
                break
            ux, uy = (nx, ny) if s > 0.0 else (-nx, -ny)
            dist = abs(s)
            cx, cy = x + nx * s, y + ny * s
            if dist2d((cx, cy), (zcx, zcy)) > zr:
                continue
            ok = True
            for q in (1.5, 3.0, 4.5):
                if q > dist + 1e-6:
                    break
                if self.map.wall_height_along(x, y, z, ux, uy, q, radius, height, self.step_up) > 0.0:
                    ok = False
                    break
                sup = self.map.support_z(x + ux * q, y + uy * q, z)
                if abs(sup - z) > 1.5 or (strict_edge and sup < z - 0.6):
                    ok = False
                    break
            if not ok:
                continue
            if strict_edge:
                # never step so far that the body overhangs a ledge
                if self.map.support_z(cx + ux * (radius + 0.8), cy + uy * (radius + 0.8), z) < z - 0.6:
                    continue
            cz = self.map.support_z(cx, cy, z)
            cm = [cx, cy, cz + muzzle_h]
            tyaw = math.atan2(tp[1] - cy, tp[0] - cx)
            tpit = math.atan2(tgt[2] - cm[2], max(0.1, math.hypot(tp[0] - cx, tp[1] - cy)))
            if needs_ledger:
                tpeek = dist / max(1.0, 0.5 * walk_v)  # laser charge halves movement speed
                taim = max(
                    abs(angle_diff(tyaw, aim[0])) / max(0.5, turn_rate),
                    abs(tpit - aim[1]) / max(0.5, pitch_rate),
                )
                # Fast <=1.6m peek (tpeek+taim < 0.36s) beats an uncharged enemy's >=0.42s laser charge;
                # deeper peeks require observed cooldown + 0.42s enemy charge to outlast our exposure.
                if tpeek + taim > 0.36:
                    req_cd = max(0.0, rem_pre + tpeek + taim + 0.15 - 0.42)
                    if not self.laser_safe_for(pid, t, req_cd):
                        continue
            if not self.map.barrel_clear(cm, tyaw, tpit, shot_offset, tgt):
                continue
            exposed = False
            for ot in others[:2]:
                op = ot["pos"]
                if self.map.has_los(cm, [op[0], op[1], op[2] + 4.5], step_m=4.0):
                    exposed = True
                    break
            if exposed:
                continue
            return (cx, cy, s)
        return None

    def _predict_slewed_aim(
        self, cur_aim: List[float], cmd_yaw: float, cmd_pitch: float, turn_rate: float, pitch_rate: float, dt: float = 0.05
    ) -> Tuple[float, float]:
        dyaw = angle_diff(cmd_yaw, cur_aim[0])
        max_dy = turn_rate * dt
        nyaw = wrap_angle(cur_aim[0] + clamp(dyaw, -max_dy, max_dy))
        dp = cmd_pitch - cur_aim[1]
        max_dp = pitch_rate * dt
        npitch = cur_aim[1] + clamp(dp, -max_dp, max_dp)
        return nyaw, npitch

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
        vh = max(1.0, speed * math.cos(pitch))
        return math.atan2(dy, dx), pitch, r / vh

    def _dodge_vector(
        self, t: float, pos: List[float], radius: float, projs: List[mf.ProjectileObs], enemies: List[mf.ActorObs]
    ) -> Tuple[float, float, bool, List[mf.ActorObs]]:
        ex, ey = 0.0, 0.0
        urgent = False
        lethal_laser_threats: List[mf.ActorObs] = []
        mx, my, mz = pos[0], pos[1], pos[2] + 4.5

        for p in projs:
            px, py, pz = p["pos"]
            vx, vy, vz = p["vel"]
            if p["kind"] == "mortar":
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
                    ex += math.cos(away_yaw) * w * 5.2
                    ey += math.sin(away_yaw) * w * 5.2
                    if t_imp < 0.9:
                        urgent = True
            else:
                v2 = vx * vx + vy * vy + vz * vz
                if v2 < 1.0:
                    continue
                rx, ry, rz = mx - px, my - py, mz - pz
                t_hit = (rx * vx + ry * vy + rz * vz) / v2
                if t_hit < 0.0 or t_hit > 0.65:
                    continue
                cx = px + vx * t_hit - mx
                cy = py + vy * t_hit - my
                cz = pz + vz * t_hit - mz
                if abs(cz) > 6.5:
                    continue
                d_perp = math.hypot(cx, cy)
                thresh = radius + 2.5
                if d_perp < thresh:
                    hv = math.hypot(vx, vy)
                    if hv > 0.1:
                        nx, ny = -vy / hv, vx / hv
                        if nx * cx + ny * cy > 0:
                            nx, ny = -nx, -ny
                        w = (thresh - d_perp) / thresh
                        ex += nx * w * 2.5
                        ey += ny * w * 2.5
                        if d_perp < radius + 0.8:
                            urgent = True

        # Round-2 Phase-2 Winner: Enemy Laser Charge-Window Timing (V12: threshold 0.28 s, since 2x laser_charge => 0.42 s charge).
        # Keep punishing during the first 0.28s of an observed charge, then snap to cover!
        for e in enemies:
            if e.get("charging"):
                ep = e["pos"]
                eyaw = e["aim"][0]
                ldx, ldy = math.cos(eyaw), math.sin(eyaw)
                rx, ry = mx - ep[0], my - ep[1]
                proj = rx * ldx + ry * ldy
                if 0.0 < proj < 275.0:
                    cx, cy = rx - proj * ldx, ry - proj * ldy
                    d_ray = math.hypot(cx, cy)
                    if d_ray < radius + 5.5:
                        eid = int(e["id"])
                        elapsed = t - self.enemy_charge_start.get(eid, t)
                        if elapsed >= self.LASER_DANGER_T:
                            lethal_laser_threats.append(e)
                            nx, ny = -ldy, ldx
                            if nx * cx + ny * cy < 0:
                                nx, ny = -nx, -ny
                            ex += nx * 4.2
                            ey += ny * 4.2
                            urgent = True

        return ex, ey, urgent, lethal_laser_threats

    def _best_roof(self, x: float, y: float, zone: mf.ZoneObs) -> Optional[Tuple[float, float, float]]:
        zcx, zcy = zone["next_center"]
        zr = max(12.0, zone["next_radius"] - min(15.0, zone["next_radius"] * 0.2))
        best = None
        best_d = 115.0
        for rx, ry, rz in self.map.roofs:
            if dist2d((rx, ry), (zcx, zcy)) > zr:
                continue
            d = dist2d((x, y), (rx, ry))
            if d < best_d:
                best_d = d
                best = (rx, ry, rz)
        return best

    def _steer_v11(
        self,
        pos: List[float],
        desired_yaw: float,
        zone: mf.ZoneObs,
        dodge: Tuple[float, float],
        radius: float,
        height: float,
        threats: List[mf.ActorObs],
        flankers: List[List[float]],
        want_zero_los: bool,
        want_1v1_slice: bool,
        allow_climb: bool,
        keep_on_roof: bool,
        energy: float,
    ) -> Tuple[List[float], bool, bool]:
        x, y, z = pos[0], pos[1], pos[2]
        zr = max(4.0, zone["radius"] - min(6.0, zone["radius"] * 0.2))
        zcx, zcy = zone["center"]
        best_score = -1e9
        best_dir = [math.cos(desired_yaw), math.sin(desired_yaw)]
        need_jump = False
        need_jet = False

        for k in range(16):
            off = k * (math.pi / 8.0)
            if off > math.pi:
                off -= 2.0 * math.pi
            ang = desired_yaw + off
            dx, dy = math.cos(ang), math.sin(ang)

            h_near = self.map.wall_height_along(x, y, z, dx, dy, 4.5, radius, height, self.step_up)
            h_mid = 99.0 if h_near > 0.0 else self.map.wall_height_along(x, y, z, dx, dy, 10.5, radius, height, self.step_up)

            # Hysteresis climb: when climbing_roof is active, allow climbing down to energy > 10!
            e_min = 10.0 if self.climbing_roof is not None else 45.0
            climbable = allow_climb and energy > e_min and 1.2 < h_near < 28.0

            score = math.cos(off) * 3.4
            score += (dx * dodge[0] + dy * dodge[1]) * 3.2
            if h_near > 0.0:
                score -= 0.8 if climbable else 12.0
            elif h_mid > 0.0:
                score -= 3.2

            nx1, ny1 = x + dx * 5.0, y + dy * 5.0
            nx2, ny2 = x + dx * 11.0, y + dy * 11.0

            # Phase-3 Winner: Roof Edge-Lock! Don't accidentally strafe off a rooftop into ground swarm!
            if keep_on_roof and h_near == 0.0:
                sup = self.map.support_z(nx1, ny1, z)
                if sup < z - 4.0:
                    score -= 10.0

            d_zone = dist2d((nx2, ny2), (zcx, zcy))
            if d_zone > zr:
                score -= (d_zone - zr) * 0.5

            # Phase-4 Winner: Anti-Flank Memory — penalize walking toward unseen remembered flankers
            if flankers and h_near == 0.0:
                for fp in flankers[:3]:
                    d_now = dist2d((x, y), (fp[0], fp[1]))
                    d_next = dist2d((nx2, ny2), (fp[0], fp[1]))
                    if d_now < 70.0 and d_next < d_now:
                        score -= 2.2

            # Phase-4 Winner: Fast Multi-Ring Cover Lookahead (13m + early-exit 25m!) for real cover & 1v1 slicing
            if threats and h_near == 0.0 and (k % 2 == 0) and (want_zero_los or want_1v1_slice):
                best_ring_bonus = -1e9
                for r_check in (13.0, 25.0):
                    sx, sy = x + dx * r_check, y + dy * r_check
                    if dist2d((sx, sy), (zcx, zcy)) > zr:
                        continue
                    if r_check > 15.0 and (h_mid > 0.0 or self.map.wall_height_along(x, y, z, dx, dy, r_check, radius, height, self.step_up) > 0.0):
                        continue
                    sz = self.map.support_z(sx, sy, z) + 5.5
                    los_cnt = 0
                    for th in threats[:3]:
                        tp = th["pos"]
                        if self.map.has_los([sx, sy, sz], [tp[0], tp[1], tp[2] + 7.5], step_m=7.5):
                            los_cnt += 1
                    w_dist = 1.0 if r_check < 15.0 else 0.72
                    if want_zero_los:
                        b_val = (9.0 if los_cnt == 0 else (1.5 if los_cnt == 1 else -4.5 * los_cnt)) * w_dist
                    else:
                        b_val = (7.0 if los_cnt == 1 else (2.2 if los_cnt == 0 else -4.5 * (los_cnt - 1))) * w_dist
                    if b_val > best_ring_bonus:
                        best_ring_bonus = b_val
                    # Early exit: if 13m already gives optimal cover (0 LOS) or 1v1 slice (1 LOS), skip 25m!
                    if (want_zero_los and los_cnt == 0) or (want_1v1_slice and los_cnt == 1):
                        break
                if best_ring_bonus > -1e8:
                    score += best_ring_bonus

            if score > best_score:
                best_score = score
                best_dir = [dx, dy]
                need_jump = h_near > 0.0
                need_jet = climbable

        return best_dir, need_jump, need_jet

    def act(self, obs: mf.Observation) -> mf.Action:
        t_start = time.perf_counter()
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
        turn_rate = float(stats.get("turn_rate", 4.0))
        pitch_rate = float(stats.get("pitch_rate", 3.0))
        min_pitch = float(stats.get("min_pitch", -0.7))
        max_pitch = float(stats.get("max_pitch", 1.3))
        regen_delay = float(stats.get("regen_delay", 5.0))
        shot_offset = my_radius + 0.5
        muzzle = [x, y, z + muzzle_h]
        tz_here = self.map.terrain_z(x, y)
        on_roof = z > tz_here + 5.5
        cur_roof = self.map.roof_prism_under(x, y, z) if on_roof else None

        act: mf.Action = {"tick": tick}

        # 1. Update Persistent World Memory & combat events
        self._update_world_memory(obs, pos, me["aim"][0], zone)

        for ev in obs["events"]:
            et = ev["type"]
            if et == "damaged":
                self.last_damage_t = t
                self.last_combat_t = t
                if ev.get("bearing") is not None:
                    self.last_damage_bearing = float(ev["bearing"])
            elif et == "hit":
                self.last_combat_t = t
        for bm in obs["beams"]:
            if bm["path"]:
                bid = int(bm["by"])
                self.beam_threats[bid] = (bm["path"][0], t)
                if bm.get("kind") == "laser":
                    # Observed laser release => exact cooldown ledger for that shooter id
                    shot_t = t - float(bm.get("age", 0.0) or 0.0)
                    self.enemy_laser_ready[bid] = shot_t + self.laser_cd
                    self.enemy_charge_start.pop(bid, None)
        self.beam_threats = {k: v for k, v in self.beam_threats.items() if t - v[1] < 2.5}
        if self.enemy_laser_ready:
            for k in [k for k, v in self.enemy_laser_ready.items() if v < t - 6.0]:
                del self.enemy_laser_ready[k]

        if self.last_pos is not None and dist2d((x, y), self.last_pos) < 0.14:
            self.stuck_ticks += 1
        else:
            self.stuck_ticks = 0
        self.last_pos = (x, y)

        if tick - self.strafe_flip_tick >= self.strafe_interval:
            self.strafe_dir = -self.strafe_dir
            self.strafe_flip_tick = tick
            self.strafe_interval = self.rng.randint(13, 17)

        # 2. Pick upgrades using Round-2 Phase-5 Winning Tier List
        if obs["offer"]:
            act["pick"] = self._pick_upgrade(obs["offer"], weapons)

        # 3. Weapon Pickup: Dream = Laser + Gun or Laser + Lightning (swap out Mortar ASAP)
        w_rank = {"laser": 5.3, "gun": 4.8, "lightning": 4.6, "mortar": 1.0}
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

        # 4. Analyze visible enemies with multi-point muzzle LOS + remembered flankers
        enemies = [m for m in obs["mechs"] if m["kind"] == "mech"]
        npcs = [m for m in obs["mechs"] if m["kind"] == "npc"]

        has_laser = "laser" in held_kinds
        has_lightning = "lightning" in held_kinds
        enemies_with_los: List[mf.ActorObs] = []
        vis_enemy_ids = set()
        best_los_enemy: Optional[mf.ActorObs] = None
        best_los_z_off = 4.5
        best_los_score = -1e9
        best_any_enemy: Optional[mf.ActorObs] = None
        best_any_score = -1e9
        closest_los_dist = 999.0

        for e in enemies:
            vis_enemy_ids.add(int(e["id"]))
            ep = e["pos"]
            ec = float(e.get("cubes", 0.0))
            escale = 1.0 + self.size_per_cube * ec
            z_mid = 4.5 * escale
            z_hi = 7.2 * escale
            d = dist3d(pos, ep)
            los_mid = self.map.has_los(muzzle, [ep[0], ep[1], ep[2] + z_mid])
            los_hi = False if los_mid else self.map.has_los(muzzle, [ep[0], ep[1], ep[2] + z_hi])
            los = los_mid or los_hi
            ehp = float(e.get("hp", 1000.0))

            yaw_e_to_me = math.atan2(y - ep[1], x - ep[0])
            rear_exposed = abs(angle_diff(e["aim"][0], yaw_e_to_me)) > (math.pi * 0.52)

            s = -d * 1.10 + (1400.0 - ehp) * 0.20
            if ehp < 420.0:
                s += 195.0
            if rear_exposed:
                s += 55.0
            if has_laser and "mortar" in e.get("weapons", []):
                s += 80.0
            if has_lightning and d < 44.0 and "laser" in e.get("weapons", []):
                s += 75.0  # Short enemy laser!
            if e.get("charging"):
                s += 40.0
            if los:
                enemies_with_los.append(e)
                if d < closest_los_dist:
                    closest_los_dist = d
                if s > best_los_score:
                    best_los_score = s
                    best_los_enemy = e
                    best_los_z_off = z_mid if los_mid else z_hi
            if s > best_any_score:
                best_any_score = s
                best_any_enemy = e

        # Unseen remembered flankers (in mem_enemies but not in enemies_with_los)
        los_ids = {int(e["id"]) for e in enemies_with_los}
        flanker_positions = [ep for eid, (ep, _) in self.mem_enemies.items() if eid not in los_ids]

        # Incoming projectiles & exact laser charge-window detector
        dodge_x, dodge_y, dodge_urgent, lethal_lasers = self._dodge_vector(t, pos, my_radius, obs["projectiles"], enemies)
        protect_regen = (len(enemies_with_los) == 0) and (hp_frac < 0.85) and (t - self.last_combat_t >= max(0.5, regen_delay - 1.5))

        # 5. Movement Decision Engine (Persistent Memory + Roof Hysteresis + Roof-Center Regen + Multi-Ring Cover)
        zcx, zcy = zone["next_center"]
        dist_to_cur = dist2d((x, y), (zone["center"][0], zone["center"][1]))
        dist_to_next = dist2d((x, y), (zcx, zcy))
        cur_margin = min(22.0, zone["radius"] * 0.25)
        next_margin = min(12.0, zone["next_radius"] * 0.25)
        shrink_soon = t > zone["shrink_start"] - 14.0 and dist_to_next > max(4.0, zone["next_radius"] - next_margin)
        zone_urgent = (not me["in_zone"]) or (dist_to_cur > max(4.0, zone["radius"] - cur_margin)) or shrink_soon

        # Cancel roof climb if we arrived, ran out of energy, or zone became urgent
        if self.climbing_roof is not None:
            if z >= self.climbing_roof[2] - 0.8 or energy < 10.0 or zone_urgent:
                self.climbing_roof = None

        ang_from_c = math.atan2(y - zcy, x - zcx)
        edge_r = max(4.0, zone["next_radius"] * 0.66)
        edge_anchor = (zcx + math.cos(ang_from_c) * edge_r, zcy + math.sin(ang_from_c) * edge_r)

        goal_xy = edge_anchor
        want_boost = False
        want_zero_los = False
        want_1v1_slice = False
        allow_climb = False
        keep_on_roof = on_roof and (not zone_urgent) and (len(enemies_with_los) == 0 or all(e["pos"][2] < z - 4.0 for e in enemies_with_los))
        cover_targets = enemies_with_los
        state_label = "edge"

        best_drop: Optional[mf.DropObs] = None
        for dr in obs["drops"]:
            if dist2d((x, y), (dr["pos"][0], dr["pos"][1])) < 145.0 and dr["lands_in"] < 9.5 and (hp_frac < 0.85 or cubes < self.stat_cap):
                best_drop = dr
                break

        capturing_drop = (
            best_drop is not None
            and best_drop["lands_in"] <= 0.1
            and dist2d((x, y), (best_drop["pos"][0], best_drop["pos"][1])) < best_drop["radius"] + 4.0
            and len(enemies_with_los) < 2
            and hp_frac >= 0.38
        )

        # 5b. V12 Upgrade A: true barrel-origin laser jiggle-peek.
        # Precharge while covered -> side-step (half speed) until the REAL barrel ray is clear -> release -> return home.
        peek_mode = False
        peek_go = False
        peek_goal: Optional[Tuple[float, float]] = None
        peek_slot: Optional[int] = None
        laser_slot: Optional[int] = None
        for idx_w, w in enumerate(weapons):
            if w is not None and w["kind"] == "laser":
                laser_slot = idx_w
                break
        walk_v = float(stats.get("walk_speed", stats.get("speed", 11.7)))
        if (
            self.ENABLE_PEEK
            and laser_slot is not None
            and me["grounded"]
            and not zone_urgent
            and not lethal_lasers
            and not dodge_urgent
            and not capturing_drop
            and self.climbing_roof is None
            and hp_frac >= 0.40
            and t >= self.peek_block_until
            and t - self.last_damage_t > 0.8
            and len(enemies_with_los) <= 1
            and (time.perf_counter() - t_start) < 0.0025
        ):
            pw = weapons[laser_slot]
            assert pw is not None
            p_charge = float(pw.get("charge", 0.0))
            pe = best_los_enemy if best_los_enemy is not None else best_any_enemy
            if pe is not None and (float(pw["cooldown"]) <= 0.05 or p_charge > 0.0) and not pe.get("charging"):
                pws = pw["stats"]
                max_c = float(pws.get("charge", 0.75))
                hold_s = float(pws.get("hold_s", 2.0))
                pep = pe["pos"]
                pid = int(pe["id"])
                z_off_p = 4.5 * (1.0 + self.size_per_cube * float(pe.get("cubes", 0.0)))
                d_pe = dist3d(pos, pep)
                if 38.0 <= d_pe <= min(float(pws.get("range", 280.0)) - 5.0, 150.0):
                    tgt_pt = [pep[0], pep[1], pep[2] + z_off_p]
                    yaw0 = math.atan2(pep[1] - y, pep[0] - x)
                    pit0 = math.atan2(tgt_pt[2] - muzzle[2], max(0.1, dist2d((x, y), (pep[0], pep[1]))))
                    has_l = "laser" in pe.get("weapons", ["laser"])
                    rem_pre = max(0.0, 0.88 * max_c - p_charge)
                    if not self._rear_or_close_threat(t, x, y, yaw0, pid):
                        if self.map.barrel_clear(muzzle, yaw0, pit0, shot_offset, tgt_pt):
                            # Real barrel ray already clear: fire phase if we own a charge, or if muzzle-center LOS missed a clear barrel.
                            if (p_charge > 0.0 and self.peek_owned_charge) or best_los_enemy is None:
                                taim0 = max(
                                    abs(angle_diff(yaw0, me["aim"][0])) / max(0.5, turn_rate),
                                    abs(pit0 - me["aim"][1]) / max(0.5, pitch_rate),
                                )
                                req_cd0 = max(0.0, rem_pre + taim0 + 0.15 - 0.42)
                                if (not has_l) or (rem_pre + taim0 <= 0.36) or self.laser_safe_for(pid, t, req_cd0):
                                    peek_mode = True
                                    peek_slot = laser_slot
                                    if self.peek_plan is None or self.peek_plan[0] != pid:
                                        self.peek_axis = (-math.sin(yaw0) * self.strafe_dir, math.cos(yaw0) * self.strafe_dir)
                        else:
                            found: Optional[Tuple[float, float, float]] = None
                            pl = self.peek_plan
                            if (
                                pl is not None
                                and pl[0] == pid
                                and self.peek_prev_mode
                                and t - pl[4] < 1.5
                                and self._goal_clear((pl[1], pl[2]), muzzle_h, z, shot_offset, pep, tgt_pt)
                            ):
                                # Keep the SAME goal for the whole attempt (re-planning from a dithered position inflates |s|)
                                found = (pl[1], pl[2], pl[3])
                            else:
                                others = sorted(
                                    (o for o in enemies if int(o["id"]) != pid and dist2d((x, y), (o["pos"][0], o["pos"][1])) < 140.0),
                                    key=lambda o: dist2d((x, y), (o["pos"][0], o["pos"][1])),
                                )
                                found = self._find_peek(
                                    t, pos, muzzle_h, my_radius, my_height, shot_offset, pep, z_off_p, zone, others,
                                    on_roof or keep_on_roof, pid, has_l, me["aim"], turn_rate, pitch_rate, walk_v, rem_pre,
                                )
                                if found is not None:
                                    self.peek_plan = (pid, found[0], found[1], found[2], t)
                                    self.peek_side = 1.0 if found[2] > 0.0 else -1.0
                                    self.peek_lock_until = t + 0.6  # side hysteresis
                                    self.peek_axis = (-math.sin(yaw0) * self.peek_side, math.cos(yaw0) * self.peek_side)
                                else:
                                    self.peek_plan = None
                            if found is not None:
                                peek_mode = True
                                peek_slot = laser_slot
                                peek_goal = (found[0], found[1])
                                gd = dist2d((x, y), peek_goal)
                                peek_go = (p_charge >= 0.88 * max_c) and ((max_c + hold_s - p_charge) > gd / max(1.0, 0.5 * walk_v) + 0.35)
        if peek_mode:
            if not self.peek_prev_mode:
                self.peek_started_t = t
                self.peek_home = (x, y)
            elif t - self.peek_started_t > 2.4:
                peek_mode, peek_go, peek_goal, peek_slot = False, False, None, None
                self.peek_block_until = t + 2.5

        # Persistent Memory Weapon Rush (up to 195m when Slot 1 empty or holding Mortar!)
        want_weapon_pos: Optional[Tuple[str, List[float]]] = None
        if weapons[1] is None or "mortar" in held_kinds:
            cand_w = [(k, ppos) for k, ppos, _ in self.mem_pickups.values() if k in ("laser", "lightning") and k not in held_kinds]
            if cand_w:
                cand_best = min(cand_w, key=lambda item: dist3d(pos, item[1]))
                if dist3d(pos, cand_best[1]) < 195.0:
                    want_weapon_pos = cand_best

        # Persistent Memory Cubes & Crates
        best_cube_pos: Optional[List[float]] = None
        if self.mem_cubes:
            best_cube_pos = min((cpos for cpos, _ in self.mem_cubes.values()), key=lambda cpos: dist3d(pos, cpos))
        cube_pick_r = 65.0 if cubes < self.stat_cap else 24.0

        best_crate_pos: Optional[List[float]] = None
        if self.mem_crates:
            best_crate_pos = min((cpos for cpos, _ in self.mem_crates.values()), key=lambda cpos: dist3d(pos, cpos))

        roof = self._best_roof(x, y, zone)

        # V12 Upgrade C: ledge-punish. Only when every LOS enemy is >=4 m below and its OBSERVED laser cooldown outlasts our retreat.
        roof_punish_ok = False
        if (
            self.ENABLE_LEDGER_ROOF
            and cur_roof is not None
            and best_los_enemy is not None
            and not zone_urgent
            and not lethal_lasers
            and 0.40 <= hp_frac < 0.50
            and len(enemies_with_los) <= 2
            and all(e["pos"][2] < z - 4.0 and not e.get("charging") for e in enemies_with_los)
        ):
            dc_roof = dist2d((x, y), (cur_roof.cx, cur_roof.cy))
            win_roof = min(0.8, dc_roof / max(1.0, walk_v)) + 0.20
            roof_punish_ok = self.laser_safe_for(int(best_los_enemy["id"]), t, win_roof) and all(
                ("laser" not in e.get("weapons", ["laser"])) or self.laser_safe_for(int(e["id"]), t, win_roof)
                for e in enemies_with_los
            )

        if zone_urgent:
            goal_xy = (zcx, zcy)
            want_boost = (not me["in_zone"]) or (energy > 40.0)
            keep_on_roof = False
            state_label = "zone-rush"
        elif lethal_lasers:
            # Round-2 Phase-2/3 Winner: At t>=0.35s of enemy laser charge, break LOS!
            if cur_roof is not None:
                # On roof -> step straight toward roof center to instantly drop ground LOS!
                goal_xy = (cur_roof.cx, cur_roof.cy)
                state_label = "roof-duck"
            else:
                ax = sum(e["pos"][0] for e in lethal_lasers) / len(lethal_lasers)
                ay = sum(e["pos"][1] for e in lethal_lasers) / len(lethal_lasers)
                perp_yaw = math.atan2(y - ay, x - ax) + self.strafe_dir * (math.pi * 0.45)
                goal_xy = (x + math.cos(perp_yaw) * 30.0, y + math.sin(perp_yaw) * 30.0)
                want_zero_los = True
                cover_targets = lethal_lasers
                state_label = "anti-laser"
            want_boost = energy > 20.0 and charging_laser_slot is None
        elif capturing_drop and best_drop is not None:
            goal_xy = (best_drop["pos"][0], best_drop["pos"][1])
            keep_on_roof = False
            state_label = "drop-cap"
        elif hp_frac < 0.50 and enemies_with_los and not roof_punish_ok:
            if cur_roof is not None and all(e["pos"][2] < z - 4.0 for e in enemies_with_los):
                # Round-2 Phase-3 Winner: Roof-Center Regen! Step inward to break ground LOS & heal!
                goal_xy = (cur_roof.cx, cur_roof.cy)
                want_boost = energy > 28.0 and charging_laser_slot is None
                state_label = "roof-regen"
            else:
                ax = sum(e["pos"][0] for e in enemies_with_los) / len(enemies_with_los)
                ay = sum(e["pos"][1] for e in enemies_with_los) / len(enemies_with_los)
                away_yaw = math.atan2(y - ay, x - ax)
                z_yaw = math.atan2(zcy - y, zcx - x)
                goal_xy = (
                    x + (math.cos(away_yaw) * 0.72 + math.cos(z_yaw) * 0.28) * 40.0,
                    y + (math.sin(away_yaw) * 0.72 + math.sin(z_yaw) * 0.28) * 40.0,
                )
                want_zero_los = True
                want_boost = energy > 24.0 and charging_laser_slot is None
                state_label = "escape-cover"
        elif roof_punish_ok:
            # Enemy laser verified on cooldown: hold the ledge (edge-lock stays active) and keep gun/laser pressure instead of center-ducking.
            pe_yaw = math.atan2(best_los_enemy["pos"][1] - y, best_los_enemy["pos"][0] - x)
            sa = pe_yaw + self.strafe_dir * (math.pi * 0.5)
            goal_xy = (x + math.cos(sa) * 8.0, y + math.sin(sa) * 8.0)
            keep_on_roof = True
            state_label = "roof-punish"
        elif want_weapon_pos is not None and closest_los_dist > 34.0 and hp_frac > 0.42:
            goal_xy = (want_weapon_pos[1][0], want_weapon_pos[1][1])
            want_boost = energy > 32.0 and charging_laser_slot is None
            if want_weapon_pos[1][2] > z + 4.0:
                allow_climb = True
            keep_on_roof = False
            state_label = f"rush-{want_weapon_pos[0]}"
        elif self.climbing_roof is not None and closest_los_dist > 40.0:
            goal_xy = (self.climbing_roof[0], self.climbing_roof[1])
            allow_climb = True
            state_label = "climb-roof"
        elif best_cube_pos is not None and dist3d(pos, best_cube_pos) < cube_pick_r and len(enemies_with_los) <= 1:
            goal_xy = (best_cube_pos[0], best_cube_pos[1])
            if best_cube_pos[2] < z - 4.0:
                keep_on_roof = False
            state_label = "cube"
        elif best_drop is not None and len(enemies_with_los) == 0:
            goal_xy = (best_drop["pos"][0], best_drop["pos"][1])
            want_boost = energy > 38.0 and dist2d((x, y), goal_xy) > 12.0
            keep_on_roof = False
            state_label = "drop"
        elif best_los_enemy is not None:
            d_en = dist3d(pos, best_los_enemy["pos"])
            if len(enemies_with_los) >= 2:
                ax = sum(e["pos"][0] for e in enemies_with_los) / len(enemies_with_los)
                ay = sum(e["pos"][1] for e in enemies_with_los) / len(enemies_with_los)
                away_yaw = math.atan2(y - ay, x - ax)
                strafe_ang = away_yaw + self.strafe_dir * 0.50
                goal_xy = (x + math.cos(strafe_ang) * 35.0, y + math.sin(strafe_ang) * 35.0)
                want_1v1_slice = True
                want_boost = energy > 32.0 and charging_laser_slot is None
                state_label = "slice-1v1"
            else:
                en_yaw = math.atan2(best_los_enemy["pos"][1] - y, best_los_enemy["pos"][0] - x)
                if has_laser and has_lightning:
                    opt_range = 35.0 if d_en < 45.0 else 86.0
                elif has_laser:
                    opt_range = 92.0
                elif has_lightning:
                    opt_range = 34.0
                else:
                    opt_range = 78.0
                radial = 0.50 if d_en > opt_range + 16.0 else (-0.75 if d_en < opt_range - 14.0 else 0.0)
                strafe_ang = en_yaw + self.strafe_dir * (math.pi * 0.5)
                mx = math.cos(en_yaw) * radial + math.cos(strafe_ang) * 0.92
                my = math.sin(en_yaw) * radial + math.sin(strafe_ang) * 0.92
                goal_xy = (x + mx * 30.0, y + my * 30.0)
                want_boost = energy > 48.0 and d_en < 52.0 and charging_laser_slot is None
                state_label = f"kite-{best_los_enemy['id']:.0f}"
        elif (not peek_mode) and roof is not None and not on_roof and has_laser and energy > 55.0 and zone["radius"] > 75.0:
            self.climbing_roof = roof
            goal_xy = (roof[0], roof[1])
            allow_climb = True
            state_label = "take-roof"
        elif npcs and cubes < self.stat_cap and hp_frac > 0.52 and not protect_regen:
            npc = min(npcs, key=lambda n: dist3d(pos, n["pos"]))
            if dist3d(pos, npc["pos"]) < 105.0:
                nyaw = math.atan2(npc["pos"][1] - y, npc["pos"][0] - x)
                nd = dist3d(pos, npc["pos"])
                rad = 0.55 if nd > 46.0 else (-0.55 if nd < 28.0 else 0.0)
                sang = nyaw + self.strafe_dir * (math.pi * 0.5)
                goal_xy = (
                    x + (math.cos(nyaw) * rad + math.cos(sang) * 0.85) * 25.0,
                    y + (math.sin(nyaw) * rad + math.sin(sang) * 0.85) * 25.0,
                )
                keep_on_roof = False
                state_label = "farm-npc"
        elif best_crate_pos is not None and cubes < self.stat_cap and not protect_regen:
            if dist3d(pos, best_crate_pos) < 105.0:
                goal_xy = (best_crate_pos[0], best_crate_pos[1])
                if best_crate_pos[2] > z + 4.0:
                    allow_climb = True
                keep_on_roof = False
                state_label = "farm-crate"

        if capturing_drop:
            self.stuck_ticks = 0
        desired_yaw = math.atan2(goal_xy[1] - y, goal_xy[0] - x)
        if self.stuck_ticks > 4:
            desired_yaw = wrap_angle(desired_yaw + self.strafe_dir * (math.pi * 0.55))

        if capturing_drop and best_drop is not None and dist2d((x, y), (best_drop["pos"][0], best_drop["pos"][1])) > best_drop["radius"] - 2.0:
            move_vec = [math.cos(desired_yaw), math.sin(desired_yaw)]
            need_jump, need_jet = False, False
        else:
            move_vec, need_jump, need_jet = self._steer_v11(
                pos,
                desired_yaw,
                zone,
                (dodge_x, dodge_y),
                my_radius,
                my_height,
                cover_targets if (want_zero_los or want_1v1_slice) else [],
                flanker_positions,
                want_zero_los,
                want_1v1_slice,
                allow_climb,
                keep_on_roof,
                energy,
            )

        if peek_mode and peek_slot is not None:
            want_boost = False
            need_jump = False
            need_jet = False
            self.stuck_ticks = 0
            pgoal = peek_goal
            if pgoal is None and self.peek_plan is not None and t - self.peek_plan[4] < 1.6:
                pgoal = (self.peek_plan[1], self.peek_plan[2])
            gd2 = dist2d((x, y), pgoal) if pgoal is not None else 0.0
            if peek_go and pgoal is not None and gd2 > 0.3:
                move_vec = [(pgoal[0] - x) / gd2, (pgoal[1] - y) / gd2]
                state_label = "peek-go"
            else:
                # Hold exact covered spot while precharging, or hold exact clear spot while releasing hitscan beam
                move_vec = [0.0, 0.0]
                state_label = "peek-fire" if (peek_goal is None) else "peek-chg"
        elif (
            t < self.peek_return_until
            and self.peek_home is not None
            and not zone_urgent
            and not dodge_urgent
            and not lethal_lasers
            and me["grounded"]
        ):
            hx, hy = self.peek_home
            hd = dist2d((x, y), (hx, hy))
            if 0.5 < hd < 9.0:
                hux, huy = (hx - x) / hd, (hy - y) / hd
                if (
                    self.map.wall_height_along(x, y, z, hux, huy, min(hd, 3.0), my_radius, my_height, self.step_up) <= 0.0
                    and abs(self.map.support_z(hx, hy, z) - z) <= 1.5
                ):
                    move_vec = [hux, huy]
                    need_jump = False
                    need_jet = False

        jump_cmd = False
        if need_jet or (self.climbing_roof is not None and not me["grounded"] and z < self.climbing_roof[2] + 0.5):
            if me["grounded"]:
                jump_cmd = True
            elif energy > 8.0:
                want_boost = True
        elif self.stuck_ticks > 5 or (need_jump and self.stuck_ticks > 2):
            if me["grounded"]:
                jump_cmd = True
            elif energy > 22.0:
                want_boost = True
        if dodge_urgent and energy > 15.0 and charging_laser_slot is None:
            want_boost = True

        act["move"] = move_vec
        act["boost"] = want_boost
        act["jump"] = jump_cmd

        # 6. Simultaneous Laser+Gun Dual-Fire (84% Gun Cut) & Precision Aim
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
            target_z_off = best_los_z_off
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
        elif npcs and hp_frac > 0.45 and cubes < self.stat_cap and not protect_regen:
            npc = min(npcs, key=lambda n: dist3d(pos, n["pos"]))
            if dist3d(pos, npc["pos"]) < 100.0:
                target_pos = npc["pos"]
                target_vel = npc["vel"]
                target_z_off = 1.8
                target_radius = 1.8
                target_los = self.map.has_los(muzzle, [target_pos[0], target_pos[1], target_pos[2] + 1.8])
                target_hp = float(npc.get("hp", 350.0))
        elif obs["crates"] and hp_frac > 0.45 and cubes < self.stat_cap and not protect_regen:
            cr = min(obs["crates"], key=lambda c: dist3d(pos, c["pos"]))
            if dist3d(pos, cr["pos"]) < 95.0:
                target_pos = cr["pos"]
                target_z_off = 1.5
                target_radius = 1.6
                target_los = self.map.has_los(muzzle, [target_pos[0], target_pos[1], target_pos[2] + 1.5])
                target_hp = float(cr.get("hp", 300.0))

        # Preserve active laser charge only while a target exists
        if charging_laser_slot is not None and target_pos is not None:
            fire[charging_laser_slot] = True

        if target_pos is not None:
            d_tgt = dist3d(pos, target_pos)
            direct_yaw = math.atan2(target_pos[1] - y, target_pos[0] - x)
            direct_pitch = math.atan2(target_pos[2] + target_z_off - muzzle[2], max(0.1, dist2d((x, y), (target_pos[0], target_pos[1]))))
            aim_yaw, aim_pitch = direct_yaw, direct_pitch

            primary_slot: Optional[int] = None
            if peek_mode and peek_slot is not None:
                primary_slot = peek_slot
            elif charging_laser_slot is not None and target_los:
                primary_slot = charging_laser_slot
            else:
                primary_score = -1.0
                for i, w in enumerate(weapons):
                    if w is None:
                        continue
                    k = w["kind"]
                    ws = w["stats"]
                    s = -1.0
                    if k == "lightning" and target_los and d_tgt <= float(ws.get("range", 45.0)) - 1.0 and energy > 9.0:
                        s = 115.0
                    elif k == "laser" and target_los and d_tgt <= float(ws.get("range", 280.0)) - 5.0:
                        if (d_tgt > 38.0 or float(w.get("charge", 0.0)) > 0.0) and (w["cooldown"] <= 0.1 or float(w.get("charge", 0.0)) > 0.0):
                            s = 105.0
                    elif k == "gun" and target_los and d_tgt <= float(ws.get("range", 230.0)) - 5.0 and float(w.get("reload", 0.0)) == 0.0:
                        s = 96.0
                    elif k == "mortar" and 18.0 < d_tgt < 225.0 and w["cooldown"] <= 0.1:
                        s = 74.0 if not target_los else 45.0
                    if s > primary_score:
                        primary_score = s
                        primary_slot = i

            if primary_slot is not None:
                w = weapons[primary_slot]
                assert w is not None
                k = w["kind"]
                ws = w["stats"]
                other = 1 - primary_slot
                ow = weapons[other]

                if k == "lightning":
                    aim_yaw, aim_pitch = self._lead_aim(muzzle, target_pos, target_vel, 252.0, target_z_off, shot_offset)
                    pyaw, _ = self._predict_slewed_aim(me["aim"], aim_yaw, aim_pitch, turn_rate, pitch_rate)
                    cone_half = math.radians(float(ws.get("cone_deg", 30.0)) * 0.46)
                    if abs(angle_diff(pyaw, direct_yaw)) <= cone_half:
                        fire[primary_slot] = True
                elif k == "gun":
                    aim_yaw, aim_pitch = self._lead_aim(muzzle, target_pos, target_vel, float(ws.get("speed", 252.0)), target_z_off, shot_offset)
                    pyaw, _ = self._predict_slewed_aim(me["aim"], aim_yaw, aim_pitch, turn_rate, pitch_rate)
                    if abs(angle_diff(pyaw, aim_yaw)) < 0.15:
                        fire[primary_slot] = True
                elif k == "laser":
                    charge = float(w.get("charge", 0.0))
                    max_c = float(ws.get("charge", 0.75))
                    min_c = float(ws.get("min_charge", 0.15))
                    hold_s = float(ws.get("hold_s", 2.0))
                    # Round-2 Phase-2 Winner: Lead-aim & fire Gun up to 84% of Laser charge, then snap to hitscan!
                    if (not peek_mode) and charge < max_c * 0.84 and ow is not None and ow["kind"] == "gun" and float(ow.get("reload", 0.0)) == 0.0 and d_tgt <= float(ow["stats"].get("range", 230.0)) - 5.0:
                        aim_yaw, aim_pitch = self._lead_aim(muzzle, target_pos, target_vel, float(ow["stats"].get("speed", 252.0)), target_z_off, shot_offset)
                        fire[primary_slot] = True
                    else:
                        aim_yaw, aim_pitch = direct_yaw, direct_pitch
                        pyaw, ppitch = self._predict_slewed_aim(me["aim"], aim_yaw, aim_pitch, turn_rate, pitch_rate)
                        hit_tol = clamp(math.atan2(target_radius * 0.85, max(1.0, d_tgt)), 0.014, 0.14)
                        yaw_err = abs(angle_diff(pyaw, aim_yaw))
                        pitch_err = abs(ppitch - aim_pitch)
                        about_to_autofire = charge >= (max_c + hold_s - 0.20)
                        ready_to_release = (charge >= max_c * 0.88) or (target_hp < 155.0 and charge >= min_c)
                        if (ready_to_release or about_to_autofire) and yaw_err <= hit_tol and pitch_err <= hit_tol * 1.4:
                            # V12: release only through a geometrically valid barrel ray (hitscan leaves from radius+0.5 ahead of the muzzle)
                            if about_to_autofire or self.map.barrel_clear(
                                muzzle, pyaw, ppitch, shot_offset, [target_pos[0], target_pos[1], target_pos[2] + target_z_off]
                            ):
                                fire[primary_slot] = False
                                if peek_mode:
                                    self.peek_return_until = t + 1.0
                            else:
                                fire[primary_slot] = True
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
                            pyaw, ppitch = self._predict_slewed_aim(me["aim"], aim_yaw, aim_pitch, turn_rate, pitch_rate)
                            if abs(angle_diff(pyaw, aim_yaw)) < 0.10 and abs(ppitch - aim_pitch) < 0.10:
                                fire[primary_slot] = True

                if ow is not None and target_los:
                    ok = ow["kind"]
                    ows = ow["stats"]
                    pyaw, _ = self._predict_slewed_aim(me["aim"], aim_yaw, aim_pitch, turn_rate, pitch_rate)
                    if ok == "gun" and float(ow.get("reload", 0.0)) == 0.0 and d_tgt <= float(ows.get("range", 230.0)) - 5.0:
                        if abs(angle_diff(pyaw, aim_yaw)) < 0.15:
                            # V12: while the laser is charging, the gun must also leave through a clear barrel (no rounds into geometry)
                            if (charging_laser_slot is None and k != "laser") or self.map.barrel_clear(
                                muzzle, pyaw, aim_pitch, shot_offset, [target_pos[0], target_pos[1], target_pos[2] + target_z_off]
                            ):
                                fire[other] = True
                    elif ok == "lightning" and energy > 10.0 and d_tgt <= float(ows.get("range", 45.0)) - 1.0:
                        cone_half = math.radians(float(ows.get("cone_deg", 30.0)) * 0.46)
                        if abs(angle_diff(pyaw, direct_yaw)) <= cone_half:
                            fire[other] = True
            elif len(enemies_with_los) >= 2:
                sx = sum(math.cos(math.atan2(e["pos"][1] - y, e["pos"][0] - x)) for e in enemies_with_los)
                sy = sum(math.sin(math.atan2(e["pos"][1] - y, e["pos"][0] - x)) for e in enemies_with_los)
                if math.hypot(sx, sy) > 0.01:
                    aim_yaw = math.atan2(sy, sx)
        else:
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

        if len(enemies_with_los) == 0:
            for idx_w, w in enumerate(weapons):
                if w is not None and w["kind"] == "gun" and not fire[idx_w] and float(w.get("reload", 0.0)) == 0.0:
                    if float(w.get("ammo", 12)) < float(w["stats"].get("mag", 12)) * 0.75:
                        act["reload"] = True

        # V12: a charge started by the peek planner must not sit at half speed into a wall once the peek is no longer valid
        if self.peek_owned_charge and not peek_mode and charging_laser_slot is not None and not target_los:
            fire[charging_laser_slot] = False
        self.peek_prev_mode = peek_mode
        if peek_mode:
            self.peek_owned_charge = True
        elif charging_laser_slot is None:
            self.peek_owned_charge = False

        act["aim"] = [aim_yaw, clamp(aim_pitch, min_pitch, max_pitch)]
        act["fire"] = fire

        mf.draw.label(f"{state_label} | hp {me['hp']:.0f} | c {cubes:.0f}")
        return act


mf.run(Bot)