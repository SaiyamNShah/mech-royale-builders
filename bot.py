"""Apex-V13 — Unified 3-Layer Architecture: True Nanite Regen Continuity, Global Anti-Encirclement Threat Field, 6m Nav-Grid A*, RoofRecord Control & Contextual Upgrades."""
from __future__ import annotations

import heapq
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
    __slots__ = ("kind", "base", "top", "ring", "holes", "minx", "maxx", "miny", "maxy", "cx", "cy", "area")

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
        self.area = (self.maxx - self.minx) * (self.maxy - self.miny)

    def contains_xy(self, x: float, y: float) -> bool:
        if x < self.minx or x > self.maxx or y < self.miny or y > self.maxy:
            return False
        if not point_in_ring(x, y, self.ring):
            return False
        for h in self.holes:
            if point_in_ring(x, y, h):
                return False
        return True


class RoofRecord:
    __slots__ = ("cx", "cy", "top_z", "rel_h", "area", "prism", "edge_nodes")

    def __init__(self, prism: Prism, rel_h: float, edge_nodes: List[Tuple[float, float]]):
        self.cx = prism.cx
        self.cy = prism.cy
        self.top_z = prism.top
        self.rel_h = rel_h
        self.area = prism.area
        self.prism = prism
        self.edge_nodes = edge_nodes


class EnemyBelief:
    __slots__ = ("eid", "pos", "vel", "t_seen", "hp", "max_hp", "cubes", "weapons", "charging", "aim")

    def __init__(self, eid: int, pos: List[float], vel: List[float], t_seen: float,
                 hp: float, max_hp: float, cubes: float, weapons: List[str], charging: bool, aim: List[float]):
        self.eid = eid
        self.pos = list(pos)
        self.vel = list(vel)
        self.t_seen = t_seen
        self.hp = hp
        self.max_hp = max_hp
        self.cubes = cubes
        self.weapons = list(weapons)
        self.charging = charging
        self.aim = list(aim)

    def predicted_pos(self, now: float) -> Tuple[float, float, float]:
        dt = clamp(now - self.t_seen, 0.0, 1.5)
        return (self.pos[0] + self.vel[0] * dt, self.pos[1] + self.vel[1] * dt, self.pos[2])

    def certainty(self, now: float) -> float:
        return math.exp(-max(0.0, now - self.t_seen) / 5.0)


class SoundBelief:
    __slots__ = ("ox", "oy", "bearing", "r_lo", "r_hi", "kind", "t_event", "weight")

    def __init__(self, ox: float, oy: float, bearing: float, r_lo: float, r_hi: float, kind: str, t_event: float, weight: float):
        self.ox = ox
        self.oy = oy
        self.bearing = bearing
        self.r_lo = r_lo
        self.r_hi = r_hi
        self.kind = kind
        self.t_event = t_event
        self.weight = weight


class ArenaMap:
    """Spatial-hashed 3D map + fast 6m nav grid (resolves campus alleys) + RoofRecord index."""

    def __init__(self, map_dir: str, max_slope_deg: float = 50.0, base_radius: float = 2.5, step_up: float = 1.2):
        self.cell = 25.0
        self.grid: Dict[Tuple[int, int], List[Prism]] = {}
        self.roofs: List[RoofRecord] = []
        self.nx = 0
        self.ny = 0
        self.min_x = 0.0
        self.min_y = 0.0
        self.step = 1.0
        self.scale = 0.01
        self.terrain: Optional[memoryview] = None
        self.bounds = (-508.0, 550.0, -328.0, 384.0)
        self.max_slope_tan = math.tan(math.radians(max(10.0, max_slope_deg - 3.0)))

        # Fine 6m walkability & cover-pocket grid (precomputed once in hello < 0.4s!)
        self.nav_step = 6.0
        self.nav_nx = 0
        self.nav_ny = 0
        self.walkable = bytearray()
        self.escape_deg = bytearray()   # 0..8 walkable neighbors
        self.cover_adj = bytearray()    # 1 if adjacent to a solid building (instant cover pocket!)
        self._load(map_dir, base_radius, step_up)

    def _load(self, map_dir: str, base_radius: float, step_up: float) -> None:
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
            # Build RoofRecord with inset edge firing nodes
            if p.kind == "building" and (p.maxx - p.minx) > 16.0 and (p.maxy - p.miny) > 16.0:
                if p.contains_xy(p.cx, p.cy):
                    rel_h = p.top - self.terrain_z(p.cx, p.cy)
                    if 8.5 <= rel_h <= 28.0:
                        edges: List[Tuple[float, float]] = []
                        inset = base_radius + 1.8
                        for ang_i in range(8):
                            ang = ang_i * (math.pi * 0.25)
                            dx, dy = math.cos(ang), math.sin(ang)
                            # Walk out from center until near edge, then inset
                            last_ok = (p.cx, p.cy)
                            for r_probe in (4.0, 8.0, 12.0, 16.0, 20.0, 26.0, 32.0):
                                px, py = p.cx + dx * r_probe, p.cy + dy * r_probe
                                if p.contains_xy(px, py):
                                    last_ok = (px, py)
                                else:
                                    break
                            ex = last_ok[0] - dx * inset
                            ey = last_ok[1] - dy * inset
                            if p.contains_xy(ex, ey) and dist2d((ex, ey), (p.cx, p.cy)) > 3.0:
                                edges.append((ex, ey))
                        self.roofs.append(RoofRecord(p, rel_h, edges))

        # Precompute 6m ground walkability grid (fast: ~20k cells, resolves narrow alleys!)
        self.nav_nx = int((self.bounds[1] - self.bounds[0]) / self.nav_step) + 1
        self.nav_ny = int((self.bounds[3] - self.bounds[2]) / self.nav_step) + 1
        n_tot = self.nav_nx * self.nav_ny
        self.walkable = bytearray(n_tot)
        self.escape_deg = bytearray(n_tot)
        self.cover_adj = bytearray(n_tot)

        nx, ny, ns = self.nav_nx, self.nav_ny, self.nav_step
        bx0, by0 = self.bounds[0], self.bounds[2]
        r_chk = base_radius * 0.72
        for j in range(ny):
            wy = by0 + j * ns
            row = j * nx
            for i in range(nx):
                wx = bx0 + i * ns
                tz = self.terrain_z(wx, wy)
                # Center + 4 cardinal body-clearance probes
                if (
                    self._prism_wall_height(wx, wy, tz, step_up, 9.0) <= 0.0
                    and self._prism_wall_height(wx + r_chk, wy, tz, step_up, 9.0) <= 0.0
                    and self._prism_wall_height(wx - r_chk, wy, tz, step_up, 9.0) <= 0.0
                    and self._prism_wall_height(wx, wy + r_chk, tz, step_up, 9.0) <= 0.0
                    and self._prism_wall_height(wx, wy - r_chk, tz, step_up, 9.0) <= 0.0
                ):
                    self.walkable[row + i] = 1

        # Compute escape degree (open neighbors) & adjacent-building cover flag
        walk = self.walkable
        for j in range(1, ny - 1):
            row = j * nx
            for i in range(1, nx - 1):
                idx = row + i
                if not walk[idx]:
                    continue
                deg = 0
                has_wall = 0
                for dj in (-1, 0, 1):
                    nrow = (j + dj) * nx
                    for di in (-1, 0, 1):
                        if di == 0 and dj == 0:
                            continue
                        if walk[nrow + i + di]:
                            deg += 1
                        else:
                            has_wall = 1
                self.escape_deg[idx] = deg
                self.cover_adj[idx] = has_wall

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

    def to_nav(self, x: float, y: float) -> Tuple[int, int]:
        i = int(clamp(round((x - self.bounds[0]) / self.nav_step), 0, self.nav_nx - 1))
        j = int(clamp(round((y - self.bounds[2]) / self.nav_step), 0, self.nav_ny - 1))
        return i, j

    def from_nav(self, i: int, j: int) -> Tuple[float, float]:
        return self.bounds[0] + i * self.nav_step, self.bounds[2] + j * self.nav_step

    def nearest_walkable(self, x: float, y: float) -> Tuple[float, float, int, int]:
        if self.nav_nx == 0:
            return x, y, 0, 0
        i0, j0 = self.to_nav(x, y)
        nx, ny, walk = self.nav_nx, self.nav_ny, self.walkable
        if walk[j0 * nx + i0]:
            wx, wy = self.from_nav(i0, j0)
            return wx, wy, i0, j0
        for r in range(1, 5):
            for dj in range(-r, r + 1):
                nj = j0 + dj
                if nj < 0 or nj >= ny:
                    continue
                for di in range(-r, r + 1):
                    if abs(di) != r and abs(dj) != r:
                        continue
                    ni = i0 + di
                    if 0 <= ni < nx and walk[nj * nx + ni]:
                        wx, wy = self.from_nav(ni, nj)
                        return wx, wy, ni, nj
        wx, wy = self.from_nav(i0, j0)
        return wx, wy, i0, j0

    def astar_waypoint(
        self, start: Tuple[float, float], goal: Tuple[float, float], threats_xy: List[Tuple[float, float, float]], max_exp: int = 160
    ) -> Tuple[float, float]:
        """Fast bounded 6m A* with dynamic enemy repulsion along edges (< 1.2ms worst-case)."""
        if self.nav_nx == 0:
            return goal
        si, sj = self.to_nav(start[0], start[1])
        _, _, gi, gj = self.nearest_walkable(goal[0], goal[1])
        if abs(si - gi) <= 2 and abs(sj - gj) <= 2:
            return goal

        nx, ny, walk = self.nav_nx, self.nav_ny, self.walkable
        start_id = sj * nx + si
        goal_id = gj * nx + gi
        pq: List[Tuple[float, int]] = [(math.hypot(si - gi, sj - gj), start_id)]
        came: Dict[int, int] = {}
        g_score: Dict[int, float] = {start_id: 0.0}
        best_id = start_id
        best_h = math.hypot(si - gi, sj - gj)

        dirs = (
            (1, 0, 1.0), (-1, 0, 1.0), (0, 1, 1.0), (0, -1, 1.0),
            (1, 1, 1.414), (1, -1, 1.414), (-1, 1, 1.414), (-1, -1, 1.414),
        )
        # Pre-convert threat positions into grid coords for ultra-fast repulsion
        t_grid = [((tx - self.bounds[0]) / self.nav_step, (ty - self.bounds[2]) / self.nav_step, tw) for tx, ty, tw in threats_xy[:5]]

        exp = 0
        while pq and exp < max_exp:
            _, cur = heapq.heappop(pq)
            if cur == goal_id:
                best_id = cur
                break
            exp += 1
            ci, cj = cur % nx, cur // nx
            cg = g_score[cur]
            for di, dj, step_c in dirs:
                ni, nj = ci + di, cj + dj
                if 0 <= ni < nx and 0 <= nj < ny:
                    nid = nj * nx + ni
                    if nid != goal_id and not walk[nid]:
                        continue
                    dyn_pen = 0.0
                    for tgi, tgj, tw in t_grid:
                        d2 = (ni - tgi) * (ni - tgi) + (nj - tgj) * (nj - tgj)
                        if d2 < 81.0:  # within 54m (9 cells)
                            dyn_pen += tw * 3.0 / (1.0 + d2 * 0.12)
                    ng = cg + step_c + dyn_pen
                    if ng < g_score.get(nid, 1e9):
                        g_score[nid] = ng
                        came[nid] = cur
                        h = math.hypot(ni - gi, nj - gj)
                        if h < best_h:
                            best_h = h
                            best_id = nid
                        heapq.heappush(pq, (ng + h * 1.15, nid))

        if best_id == start_id:
            return goal
        node = best_id
        path = [node]
        while node in came and came[node] != start_id:
            node = came[node]
            path.append(node)
        # Pick 3rd cell ahead (~18m) for smooth fluid tangent steering
        pick = path[-3] if len(path) >= 3 else path[-1]
        return self.from_nav(pick % nx, pick // nx)


class Bot:
    name = "Apex-V13"

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
        self.jump_speed = float(mech_cfg.get("jump_speed", 11.0))
        self.jet_accel = float(mech_cfg.get("jet_accel", 34.0))
        self.max_rise_speed = float(mech_cfg.get("max_rise_speed", 10.0))
        self.base_jet_drain = float(mech_cfg.get("jet_drain", 15.0))
        self.size_per_cube = float(self.cfg.get("cubes", {}).get("size_per_cube", 0.05))
        self.stat_cap = int(self.cfg.get("cubes", {}).get("stat_cap", 10))
        self.reach = float(self.cfg.get("loot", {}).get("pickup_radius", 4.0))
        self.mortar_g = float(self.cfg.get("weapons", {}).get("mortar", {}).get("gravity", 22.0))
        self.mortar_splash = float(self.cfg.get("weapons", {}).get("mortar", {}).get("splash_radius", 7.0))

        self.map = ArenaMap(hello["map"]["dir"], self.max_slope_deg, self.base_radius, self.step_up)

        # Confirmed combat / regen timestamps
        self.last_damage_taken_t = -20.0
        self.last_damage_dealt_t = -20.0
        self.last_damage_bearing: Optional[float] = None

        # True Regen Continuity State Machine: NORMAL / DISENGAGE / SEAL / REGEN
        self.regen_state = "NORMAL"
        self.seal_since = -20.0

        # World Beliefs
        self.enemy_beliefs: Dict[int, EnemyBelief] = {}
        self.sound_beliefs: List[SoundBelief] = []
        self.beam_threats: Dict[int, Tuple[List[float], float]] = {}
        self.enemy_charge_start: Dict[int, float] = {}
        self.mem_pickups: Dict[int, Tuple[str, List[float], float]] = {}
        self.mem_cubes: Dict[int, Tuple[List[float], float]] = {}
        self.mem_crates: Dict[int, Tuple[List[float], float]] = {}

        # Navigation & Macro Cache (2-3 Hz replanning)
        self.macro_goal: Optional[Tuple[float, float]] = None
        self.macro_tick = -99
        self.cached_wp: Optional[Tuple[float, float]] = None
        self.cached_wp_goal: Optional[Tuple[float, float]] = None
        self.wp_tick = -99
        self.climbing_roof: Optional[RoofRecord] = None

        # Kinematics / anti-stuck
        self.last_pos: Optional[Tuple[float, float]] = None
        self.stuck_ticks = 0
        self.strafe_dir = 1.0 if (self.slot % 2 == 0) else -1.0
        self.strafe_flip_tick = 0
        self.strafe_interval = 14
        self.scan_yaw = 0.0

    # --- 1. Contextual Upgrade Selector (verified math: nanites > plating/armor > gun_mag (+29.6% DPS!) > laser_damage) ---
    def _pick_upgrade(self, offer: mf.Offer, me: dict, weapons: List[Optional[mf.WeaponObs]], zone: mf.ZoneObs) -> int:
        held = {w["kind"] for w in weapons if w is not None}
        upgs = me.get("upgrades", [])
        nanite_stacks = upgs.count("nanites")
        armor_stacks = upgs.count("armor")
        hp_frac = me["hp"] / max(1.0, me["max_hp"])
        late_circle = zone["radius"] < 150.0

        best_i, best_s = 0, -1e9
        for i, c in enumerate(offer["choices"]):
            cid = c["id"]
            if cid == "nanites":
                s = 110.0 if nanite_stacks < 2 else 40.0
            elif cid == "plating":
                # +15% max HP (+15% EHP immediately)
                s = 102.0 if hp_frac < 0.70 else 98.0
            elif cid == "armor":
                # +8.7..10.5% EHP AND amplifies nanite regen value!
                s = 99.0 + (3.5 if nanite_stacks >= 1 else 0.0) + (1.0 * armor_stacks)
            elif cid == "servos":
                s = 93.0
            elif cid == "gun_mag":
                # Verified +29.6% sustained Gun DPS (+8 rounds & -20% reload)!
                s = 94.0 if "gun" in held else 50.0
            elif cid == "laser_damage":
                s = 95.0 if "laser" in held else 50.0
            elif cid == "laser_charge":
                # Cuts half-speed charge vulnerability by 25%!
                s = 92.0 if "laser" in held else 50.0
            elif cid == "gun_damage":
                s = 91.0 if "gun" in held else 50.0
            elif cid == "lightning_efficiency":
                s = (95.0 if late_circle else 88.0) if "lightning" in held else 48.0
            elif cid == "lightning_range":
                s = (92.0 if late_circle else 85.0) if "lightning" in held else 48.0
            elif cid == "gun_rate":
                s = 86.0 if "gun" in held else 48.0
            elif cid == "jets":
                s = 83.0
            elif cid == "reactor":
                s = 81.0
            elif cid == "lightning_chain":
                s = 80.0 if "lightning" in held else 46.0
            elif cid == "gyros":
                s = 76.0
            elif cid == "gun_velocity":
                s = 74.0 if "gun" in held else 45.0
            elif cid == "capacitor":
                s = 73.0
            elif cid == "sensors":
                s = 68.0
            elif cid in ("mortar_reload", "mortar_splash", "mortar_velocity"):
                s = 62.0 if "mortar" in held else 40.0
            else:
                s = 55.0
            if s > best_s:
                best_s = s
                best_i = i
        return best_i

    # --- 2. 1-D Vertical Climb Energy Estimator ---
    def _climb_energy_needed(self, dz: float, jet_drain: float) -> float:
        if dz <= 1.2:
            return 0.0
        z_sim = 0.0
        vz = self.jump_speed
        e_used = 0.0
        dt = 0.05
        steps = 0
        while z_sim < dz + 1.0 and steps < 120:
            vz = min(self.max_rise_speed, vz + (self.jet_accel - self.gravity) * dt)
            e_used += jet_drain * dt
            z_sim += vz * dt
            steps += 1
        return e_used * 1.25

    # --- 3. World Model & Threat Belief Updates ---
    def _update_beliefs(self, obs: mf.Observation, pos: List[float], aim_yaw: float, zone: mf.ZoneObs) -> None:
        t = float(obs["t"])
        x, y = pos[0], pos[1]
        zcx, zcy = zone["center"]
        zr = zone["radius"]

        # Persistent Loot/Crate/Cube Memory
        vis_p, vis_c, vis_cr = set(), set(), set()
        for p in obs["pickups"]:
            pid = int(p["id"])
            vis_p.add(pid)
            self.mem_pickups[pid] = (p["kind"], p["pos"], t)
        for c in obs["cubes"]:
            cid = int(c["id"])
            vis_c.add(cid)
            self.mem_cubes[cid] = (c["pos"], t)
        for cr in obs["crates"]:
            crid = int(cr["id"])
            vis_cr.add(crid)
            self.mem_crates[crid] = (cr["pos"], t)

        def should_evict(ipos: List[float], seen_t: float, max_age: float) -> bool:
            if t - seen_t > max_age:
                return True
            if dist2d((ipos[0], ipos[1]), (zcx, zcy)) > zr + 5.0:
                return True
            d = dist2d((x, y), (ipos[0], ipos[1]))
            if d < 30.0:
                return True
            if d < 85.0 and abs(angle_diff(math.atan2(ipos[1] - y, ipos[0] - x), aim_yaw)) < 0.62:
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

        # Enemy Beliefs (direct + 11s decaying belief)
        vis_e = set()
        for m in obs["mechs"]:
            if m["kind"] == "mech":
                eid = int(m["id"])
                vis_e.add(eid)
                self.enemy_beliefs[eid] = EnemyBelief(
                    eid, m["pos"], m["vel"], t,
                    float(m.get("hp", 1000.0)), float(m.get("max_hp", 1400.0)),
                    float(m.get("cubes", 0.0)), m.get("weapons", []),
                    bool(m.get("charging", False)), m.get("aim", [0.0, 0.0])
                )
                if m.get("charging"):
                    if eid not in self.enemy_charge_start:
                        self.enemy_charge_start[eid] = t
                else:
                    self.enemy_charge_start.pop(eid, None)
        for eid in list(self.enemy_charge_start.keys()):
            if eid not in vis_e:
                del self.enemy_charge_start[eid]
        for eid in list(self.enemy_beliefs.keys()):
            if t - self.enemy_beliefs[eid].t_seen > 11.0:
                del self.enemy_beliefs[eid]

        # Beam Origins
        for bm in obs["beams"]:
            if bm["path"]:
                bid = int(bm["by"])
                self.beam_threats[bid] = (bm["path"][0], t - float(bm.get("age", 0.0) or 0.0))
        self.beam_threats = {k: v for k, v in self.beam_threats.items() if t - v[1] < 3.0}

        # Sound Beliefs (ring-sector likelihoods from near/mid/far)
        self.sound_beliefs = [sb for sb in self.sound_beliefs if t - sb.t_event < 3.5]
        for s in obs["sounds"]:
            kind = s.get("kind", "")
            if kind in ("death", "drop", "crate"):
                continue
            age = float(s.get("age", 0.0))
            if age > 1.5:
                continue
            d_cls = s.get("dist", "far")
            if d_cls == "near":
                r_lo, r_hi, base_w = 0.0, 62.0, 2.2
            elif d_cls == "mid":
                r_lo, r_hi, base_w = 55.0, 165.0, 1.1
            else:
                r_lo, r_hi, base_w = 155.0, 300.0, 0.4
            if kind in ("laser_charge", "laser", "lightning"):
                base_w *= 1.5
            self.sound_beliefs.append(SoundBelief(x, y, float(s["bearing"]), r_lo, r_hi, kind, t - age, base_w))
        if len(self.sound_beliefs) > 18:
            self.sound_beliefs = self.sound_beliefs[-18:]

    # --- 4. Global Danger & Encirclement Field D(p), C(p) ---
    def _danger_and_encirclement(self, px: float, py: float, now: float, zone: mf.ZoneObs) -> Tuple[float, float, int]:
        """Computes unified threat danger D(p), encirclement C(p) = (1 - rho)*sum(w), and probable enemies within 90m."""
        danger = 0.0
        sum_w = 0.0
        vx, vy = 0.0, 0.0
        near90 = 0

        for eb in self.enemy_beliefs.values():
            q = eb.certainty(now)
            if q < 0.08:
                continue
            ex, ey, _ = eb.predicted_pos(now)
            dx, dy = ex - px, ey - py
            d = math.hypot(dx, dy)
            if d < 90.0:
                near90 += 1
            w_base = 2.0
            if "lightning" in eb.weapons and d < 55.0:
                w_base += 4.5
            if eb.charging:
                w_base += 5.0
            if "laser" in eb.weapons:
                w_base += 1.5
            w = q * w_base * math.exp(-d / 65.0)
            danger += w
            if d > 1.0:
                sum_w += w
                vx += w * (dx / d)
                vy += w * (dy / d)

        for bp, bt in self.beam_threats.values():
            q = math.exp(-max(0.0, now - bt) / 1.5)
            d = dist2d((px, py), (bp[0], bp[1]))
            w = q * 3.0 * math.exp(-d / 90.0)
            danger += w
            if d > 1.0:
                sum_w += w
                vx += w * ((bp[0] - px) / d)
                vy += w * ((bp[1] - py) / d)

        # Ring-sector sound likelihoods (fast scalar evaluation)
        for sb in self.sound_beliefs:
            decay = math.exp(-max(0.0, now - sb.t_event) / 2.5)
            d_o = dist2d((px, py), (sb.ox, sb.oy))
            # Check approximate expected sound source point along bearing at mid-ring radius
            r_mid = 0.5 * (sb.r_lo + sb.r_hi)
            sx = sb.ox + math.cos(sb.bearing) * r_mid
            sy = sb.oy + math.sin(sb.bearing) * r_mid
            d_s = dist2d((px, py), (sx, sy))
            w = sb.weight * decay * math.exp(-d_s / 70.0) * 0.65
            danger += w
            if d_s > 1.0:
                sum_w += w
                vx += w * ((sx - px) / d_s)
                vy += w * ((sy - py) / d_s)

        encirclement = 0.0
        if sum_w > 0.25:
            rho = math.hypot(vx, vy) / sum_w
            encirclement = (1.0 - clamp(rho, 0.0, 1.0)) * sum_w

        # Future zone penalty
        d_next = dist2d((px, py), (zone["next_center"][0], zone["next_center"][1]))
        zr_next = max(6.0, zone["next_radius"] - min(12.0, zone["next_radius"] * 0.2))
        if d_next > zr_next:
            danger += (d_next - zr_next) * 0.08

        return danger, encirclement, near90

    # --- 5. Global Macro Safe-Region Selector (Replaces V11's Static edge_anchor!) ---
    def _choose_cold_sector(self, x: float, y: float, now: float, zone: mf.ZoneObs, regen_bias: bool) -> Tuple[float, float]:
        zcx, zcy = zone["next_center"]
        zr = max(8.0, zone["next_radius"])
        best_pt = (zcx, zcy)
        best_cost = 1e9

        # Sample 16 safe-zone ring anchors (62% of next_radius) + current macro_goal (hysteresis!)
        cands: List[Tuple[float, float]] = []
        r_ring = max(6.0, zr * 0.62)
        for k in range(16):
            ang = k * (math.pi / 8.0)
            cx = zcx + math.cos(ang) * r_ring
            cy = zcy + math.sin(ang) * r_ring
            wx, wy, _, _ = self.map.nearest_walkable(cx, cy)
            cands.append((wx, wy))
        # Also include 4 inner points for shrinking circles / cover pockets
        if zr > 35.0:
            r_in = zr * 0.30
            for k in range(4):
                ang = k * (math.pi * 0.5) + 0.4
                wx, wy, _, _ = self.map.nearest_walkable(zcx + math.cos(ang) * r_in, zcy + math.sin(ang) * r_in)
                cands.append((wx, wy))
        if self.macro_goal is not None:
            cands.append(self.macro_goal)

        nx = self.map.nav_nx
        for cx, cy in cands:
            d_me = dist2d((x, y), (cx, cy))
            danger, encirc, _ = self._danger_and_encirclement(cx, cy, now, zone)
            cov_bonus = 0.0
            esc_bonus = 0.0
            if nx > 0:
                ci, cj = self.map.to_nav(cx, cy)
                idx = cj * nx + ci
                cov_bonus = 1.0 if self.map.cover_adj[idx] else 0.0
                esc_bonus = self.map.escape_deg[idx] / 8.0
            # Lower cost is better
            cost = (
                d_me * 0.035
                + danger * (22.0 if regen_bias else 16.0)
                + encirc * 12.0
                - cov_bonus * (5.5 if regen_bias else 3.2)
                - esc_bonus * 3.5
            )
            if self.macro_goal is not None and dist2d((cx, cy), self.macro_goal) < 8.0:
                cost -= 2.8  # Hysteresis against oscillation
            if cost < best_cost:
                best_cost = cost
                best_pt = (cx, cy)

        return best_pt

    # --- 6. Rooftop Selector using RoofRecord + 1-D Climb Energy + Threat Comparison ---
    def _best_roof_record(
        self, x: float, y: float, z: float, energy: float, jet_drain: float, now: float, zone: mf.ZoneObs, cur_danger: float
    ) -> Optional[RoofRecord]:
        zcx, zcy = zone["next_center"]
        zr = max(12.0, zone["next_radius"] - min(15.0, zone["next_radius"] * 0.2))
        best_r: Optional[RoofRecord] = None
        best_score = -1e9
        for rr in self.map.roofs:
            if dist2d((rr.cx, rr.cy), (zcx, zcy)) > zr:
                continue
            d = dist2d((x, y), (rr.cx, rr.cy))
            if d > 110.0:
                continue
            dz = rr.top_z - z
            req_e = self._climb_energy_needed(dz, jet_drain)
            if energy < req_e + 16.0:
                continue
            rdanger, rencirc, _ = self._danger_and_encirclement(rr.cx, rr.cy, now, zone)
            if rdanger > cur_danger + 1.5:
                continue
            s = 3.0 + min(4.0, rr.area / 350.0) - rdanger * 4.5 - rencirc * 3.0 - d * 0.05 - (req_e / 100.0) * 3.5
            if s > best_score:
                best_score = s
                best_r = rr
        return best_r

    # --- 7. Rear-Armor Guard Yaw ---
    def _guard_yaw(self, x: float, y: float, now: float, fallback: float) -> float:
        vx, vy = 0.0, 0.0
        for eb in self.enemy_beliefs.values():
            q = eb.certainty(now)
            if q < 0.15:
                continue
            ex, ey, _ = eb.predicted_pos(now)
            d = dist2d((x, y), (ex, ey))
            if d > 1.0 and d < 180.0:
                w = q * (3.0 if eb.charging else 1.5) * math.exp(-d / 75.0)
                vx += w * ((ex - x) / d)
                vy += w * ((ey - y) / d)
        for bp, bt in self.beam_threats.values():
            d = dist2d((x, y), (bp[0], bp[1]))
            if d > 1.0:
                w = math.exp(-max(0.0, now - bt) / 1.5) * 2.5
                vx += w * ((bp[0] - x) / d)
                vy += w * ((bp[1] - y) / d)
        if math.hypot(vx, vy) > 0.05:
            return math.atan2(vy, vx)
        return fallback

    # --- 8. Aiming, Ballistics & Dodge Helpers ---
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
        self, muzzle: List[float], target_pos: List[float], target_vel: List[float],
        proj_speed: float, target_z_off: float, shot_offset: float
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

        # Enemy laser charge threshold = 0.28s (handles upgraded 2x laser_charge = 0.42s)
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
                        if elapsed >= 0.28:
                            lethal_laser_threats.append(e)
                            nx, ny = -ldy, ldx
                            if nx * cx + ny * cy < 0:
                                nx, ny = -nx, -ny
                            ex += nx * 4.2
                            ey += ny * 4.2
                            urgent = True

        return ex, ey, urgent, lethal_laser_threats

    # --- 9. Micro Local Collision, Cover & Roof-Edge Steerer ---
    def _local_steer(
        self,
        pos: List[float],
        desired_yaw: float,
        zone: mf.ZoneObs,
        dodge: Tuple[float, float],
        radius: float,
        height: float,
        threats: List[mf.ActorObs],
        flankers: List[Tuple[float, float]],
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

            e_min = 10.0 if self.climbing_roof is not None else 40.0
            climbable = allow_climb and energy > e_min and 1.2 < h_near < 28.0

            score = math.cos(off) * 3.4
            score += (dx * dodge[0] + dy * dodge[1]) * 3.2
            if h_near > 0.0:
                score -= 0.8 if climbable else 12.0
            elif h_mid > 0.0:
                score -= 3.2

            nx1, ny1 = x + dx * 5.0, y + dy * 5.0
            nx2, ny2 = x + dx * 11.0, y + dy * 11.0

            if keep_on_roof and h_near == 0.0:
                sup = self.map.support_z(nx1, ny1, z)
                if sup < z - 4.0:
                    score -= 11.0

            d_zone = dist2d((nx2, ny2), (zcx, zcy))
            if d_zone > zr:
                score -= (d_zone - zr) * 0.55

            if flankers and h_near == 0.0:
                for fx, fy in flankers[:4]:
                    d_now = dist2d((x, y), (fx, fy))
                    d_next = dist2d((nx2, ny2), (fx, fy))
                    if d_now < 75.0 and d_next < d_now:
                        score -= 2.4

            # Dual-ring cover lookahead (12m + early-exit 24m)
            if threats and h_near == 0.0 and (k % 2 == 0) and (want_zero_los or want_1v1_slice):
                best_ring_bonus = -1e9
                for r_check in (12.0, 24.0):
                    sx, sy = x + dx * r_check, y + dy * r_check
                    if dist2d((sx, sy), (zcx, zcy)) > zr:
                        continue
                    if r_check > 14.0 and (h_mid > 0.0 or self.map.wall_height_along(x, y, z, dx, dy, r_check, radius, height, self.step_up) > 0.0):
                        continue
                    sz = self.map.support_z(sx, sy, z) + 5.5
                    los_cnt = 0
                    for th in threats[:3]:
                        tp = th["pos"]
                        if self.map.has_los([sx, sy, sz], [tp[0], tp[1], tp[2] + 7.5], step_m=7.0):
                            los_cnt += 1
                    w_dist = 1.0 if r_check < 14.0 else 0.72
                    if want_zero_los:
                        b_val = (9.5 if los_cnt == 0 else (1.5 if los_cnt == 1 else -4.5 * los_cnt)) * w_dist
                    else:
                        b_val = (7.2 if los_cnt == 1 else (2.2 if los_cnt == 0 else -4.5 * (los_cnt - 1))) * w_dist
                    if b_val > best_ring_bonus:
                        best_ring_bonus = b_val
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

    # --- 10. Main 3-Layer act() Controller ---
    def act(self, obs: mf.Observation) -> mf.Action:
        me = obs["self"]
        t = float(obs["t"])
        tick = int(obs["tick"])
        alive = int(obs.get("alive", 16))
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
        jet_drain = float(stats.get("jet_drain", self.base_jet_drain))
        shot_offset = my_radius + 0.5
        muzzle = [x, y, z + muzzle_h]
        tz_here = self.map.terrain_z(x, y)
        on_roof = z > tz_here + 5.5
        cur_roof = self.map.roof_prism_under(x, y, z) if on_roof else None

        act: mf.Action = {"tick": tick}

        # Layer 1: Ingest Events & Update World Model / Beliefs
        for ev in obs["events"]:
            et = ev["type"]
            if et == "damaged":
                self.last_damage_taken_t = t
                if ev.get("bearing") is not None:
                    self.last_damage_bearing = float(ev["bearing"])
            elif et == "hit":
                self.last_damage_dealt_t = t

        self._update_beliefs(obs, pos, me["aim"][0], zone)

        if self.last_pos is not None and dist2d((x, y), self.last_pos) < 0.14:
            self.stuck_ticks += 1
        else:
            self.stuck_ticks = 0
        self.last_pos = (x, y)

        if tick - self.strafe_flip_tick >= self.strafe_interval:
            self.strafe_dir = -self.strafe_dir
            self.strafe_flip_tick = tick
            self.strafe_interval = self.rng.randint(13, 17)

        # Contextual Upgrade Selection
        if obs["offer"]:
            act["pick"] = self._pick_upgrade(obs["offer"], me, weapons, zone)

        # Loadout Policy: Default Laser + Gun; allow Laser + Lightning in late circle (< 140m radius)
        late_circle = zone["radius"] < 140.0
        w_rank = {"laser": 5.4, "gun": 4.8, "lightning": 5.0 if late_circle else 4.5, "mortar": 1.0}
        held_kinds = {w["kind"] for w in weapons if w is not None}
        charging_laser_slot: Optional[int] = None
        laser_cd_rem = 0.0
        for idx_w, w in enumerate(weapons):
            if w is not None and w["kind"] == "laser":
                laser_cd_rem = float(w.get("cooldown", 0.0))
                if float(w.get("charge", 0.0)) > 0.0:
                    charging_laser_slot = idx_w

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

        # Analyze Visible Enemies (LOS, Airborne, Rear Exposure, Crossfire Reduction)
        enemies = [m for m in obs["mechs"] if m["kind"] == "mech"]
        npcs = [m for m in obs["mechs"] if m["kind"] == "npc"]

        has_laser = "laser" in held_kinds
        has_lightning = "lightning" in held_kinds
        enemies_with_los: List[mf.ActorObs] = []
        best_los_enemy: Optional[mf.ActorObs] = None
        best_los_z_off = 4.5
        best_los_score = -1e9
        best_any_enemy: Optional[mf.ActorObs] = None
        best_any_score = -1e9
        closest_los_dist = 999.0

        for e in enemies:
            ep = e["pos"]
            ev_vel = e["vel"]
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
            # Airborne enemy detection: air_accel = 12 vs 58.5 on ground!
            airborne = (ep[2] - self.map.terrain_z(ep[0], ep[1]) > 2.5) and (abs(ev_vel[2]) > 1.0)

            s = -d * 1.05 + (1400.0 - ehp) * 0.22
            # Sub-1-cycle kill removes an attack bearing!
            if ehp < 420.0:
                s += 240.0
            elif ehp < 650.0:
                s += 95.0
            if airborne:
                s += 115.0
            if "lightning" in e.get("weapons", []) and d < 55.0:
                s += 100.0
            if e.get("charging"):
                s += 65.0
            if rear_exposed:
                s += 60.0
            if has_laser and "mortar" in e.get("weapons", []):
                s += 85.0
            if has_lightning and d < 44.0 and "laser" in e.get("weapons", []):
                s += 80.0

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

        # Threat Field Evaluation at Current Location
        danger_here, encirc_here, near90_count = self._danger_and_encirclement(x, y, t, zone)
        los_ids = {int(e["id"]) for e in enemies_with_los}
        flanker_xy = [eb.predicted_pos(t)[:2] for eid, eb in self.enemy_beliefs.items() if eid not in los_ids]
        threats_for_astar = [(eb.predicted_pos(t)[0], eb.predicted_pos(t)[1], eb.certainty(t)) for eb in self.enemy_beliefs.values()]

        dodge_x, dodge_y, dodge_urgent, lethal_lasers = self._dodge_vector(t, pos, my_radius, obs["projectiles"], enemies)

        # Layer 2: Authoritative True Regen Continuity State Machine
        last_dmg_event = max(self.last_damage_taken_t, self.last_damage_dealt_t)
        regen_start_t = last_dmg_event + regen_delay
        has_nanites = "nanites" in me.get("upgrades", [])
        hp_break = 0.68 if near90_count >= 2 else (0.46 if alive <= 5 else (0.62 if has_nanites else 0.56))
        regen_exit_hp = 0.88 if alive > 8 else (0.82 if alive >= 5 else 0.74)

        zcx, zcy = zone["next_center"]
        dist_to_cur = dist2d((x, y), (zone["center"][0], zone["center"][1]))
        dist_to_next = dist2d((x, y), (zcx, zcy))
        cur_margin = min(22.0, zone["radius"] * 0.25)
        next_margin = min(12.0, zone["next_radius"] * 0.25)
        shrink_soon = t > zone["shrink_start"] - 15.0 and dist_to_next > max(4.0, zone["next_radius"] - next_margin)
        zone_urgent = (not me["in_zone"]) or (dist_to_cur > max(4.0, zone["radius"] - cur_margin)) or shrink_soon

        # State transitions (strict invariant: SEAL/REGEN NEVER suppresses firing when hostile_LOS > 0!)
        finishable = (best_los_enemy is not None and float(best_los_enemy.get("hp", 1000.0)) < 320.0 and hp_frac > 0.25)
        if zone_urgent or hp_frac >= regen_exit_hp:
            self.regen_state = "NORMAL"
        elif hp_frac < hp_break and len(enemies_with_los) > 0 and not finishable:
            self.regen_state = "DISENGAGE"
        elif self.regen_state == "DISENGAGE" and len(enemies_with_los) == 0 and not dodge_urgent:
            self.regen_state = "SEAL"
            self.seal_since = t
        elif self.regen_state in ("SEAL", "REGEN") and len(enemies_with_los) > 0:
            self.regen_state = "DISENGAGE"
        elif self.regen_state == "SEAL" and t >= regen_start_t:
            self.regen_state = "REGEN"
        elif self.regen_state == "NORMAL" and hp_frac < hp_break and len(enemies_with_los) == 0 and (t - last_dmg_event < regen_delay + 4.0):
            self.regen_state = "REGEN" if t >= regen_start_t else "SEAL"

        in_regen_cover = self.regen_state in ("SEAL", "REGEN")
        # Protect imminent regen (no unnecessary NPC/crate aggro when 0 enemies have LOS!)
        protect_regen = in_regen_cover or ((len(enemies_with_los) == 0) and (hp_frac < 0.84) and (t - last_dmg_event >= max(0.5, regen_delay - 1.5)))

        # Cancel roof climb if arrived, low energy, or zone urgent
        if self.climbing_roof is not None:
            if z >= self.climbing_roof.top_z - 0.8 or energy < 10.0 or zone_urgent:
                self.climbing_roof = None

        # Replan Global Macro Safe Region at 2.5 Hz (every 4 decision ticks)
        if tick - self.macro_tick >= 4 or self.macro_goal is None:
            self.macro_goal = self._choose_cold_sector(x, y, t, zone, regen_bias=in_regen_cover or self.regen_state == "DISENGAGE")
            self.macro_tick = tick

        # Supply Drop Economics (check holder, arrival, contest safety)
        best_drop: Optional[mf.DropObs] = None
        for dr in obs["drops"]:
            d_dr = dist2d((x, y), (dr["pos"][0], dr["pos"][1]))
            holder = dr.get("holder")
            if holder is not None and holder != self.slot:
                continue
            if d_dr < 145.0 and dr["lands_in"] < 9.5 and (hp_frac < 0.85 or cubes < self.stat_cap):
                # Abort if any remembered enemy is already right on top of the ring
                contested = any(dist2d((eb.predicted_pos(t)[0], eb.predicted_pos(t)[1]), (dr["pos"][0], dr["pos"][1])) < 18.0 for eb in self.enemy_beliefs.values())
                if not contested:
                    best_drop = dr
                    break

        capturing_drop = (
            best_drop is not None
            and best_drop["lands_in"] <= 0.1
            and dist2d((x, y), (best_drop["pos"][0], best_drop["pos"][1])) < best_drop["radius"] + 4.0
            and len(enemies_with_los) < 2
            and hp_frac >= 0.36
        )

        # Risk-Gated Weapon Rush (prefer Laser; check route danger instead of blind 195m sprint!)
        want_weapon_pos: Optional[Tuple[str, List[float]]] = None
        if (weapons[1] is None or "mortar" in held_kinds) and not in_regen_cover:
            cand_w = [(k, ppos) for k, ppos, _ in self.mem_pickups.values() if k in ("laser", "lightning") and k not in held_kinds]
            if cand_w:
                cand_best = min(cand_w, key=lambda item: dist3d(pos, item[1]) - (25.0 if item[0] == "laser" else 0.0))
                d_wp = dist3d(pos, cand_best[1])
                if d_wp < 185.0:
                    wdanger, _, _ = self._danger_and_encirclement(cand_best[1][0], cand_best[1][1], t, zone)
                    if wdanger < 3.5 or d_wp < 50.0:
                        want_weapon_pos = cand_best

        # Strict 10-Cube Discipline (avoid hitbox bloat on cubes 11-14!)
        best_cube_pos: Optional[List[float]] = None
        if self.mem_cubes:
            best_cube_pos = min((cpos for cpos, _ in self.mem_cubes.values()), key=lambda cpos: dist3d(pos, cpos))
        cube_pick_r = 65.0 if cubes < self.stat_cap else 13.0

        best_crate_pos: Optional[List[float]] = None
        if self.mem_crates:
            best_crate_pos = min((cpos for cpos, _ in self.mem_crates.values()), key=lambda cpos: dist3d(pos, cpos))

        # Authoritative Macro Mode Priority Tree
        goal_xy = self.macro_goal
        use_astar = True
        want_boost = False
        want_zero_los = False
        want_1v1_slice = False
        allow_climb = False
        keep_on_roof = on_roof and (not zone_urgent) and (len(enemies_with_los) == 0 or all(e["pos"][2] < z - 4.0 for e in enemies_with_los))
        cover_targets = enemies_with_los
        state_label = "cold-rot"

        # 1. Zone Urgent
        if zone_urgent:
            goal_xy = (zcx, zcy)
            want_boost = (not me["in_zone"]) or (energy > 38.0)
            keep_on_roof = False
            state_label = "zone-rush"
        # 2. Imminent Charged Laser Lethality
        elif lethal_lasers:
            use_astar = False
            if cur_roof is not None:
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
        # 3. Active Supply Drop Capture (3 cubes + FULL HP/Energy!)
        elif capturing_drop and best_drop is not None:
            goal_xy = (best_drop["pos"][0], best_drop["pos"][1])
            use_astar = False
            keep_on_roof = False
            state_label = "drop-cap"
        # 4. Low-HP Disengage (still fires back at any LOS enemy while breaking LOS!)
        elif self.regen_state == "DISENGAGE" and enemies_with_los:
            use_astar = False
            if cur_roof is not None and all(e["pos"][2] < z - 4.0 for e in enemies_with_los):
                goal_xy = (cur_roof.cx, cur_roof.cy)
                want_boost = energy > 26.0 and charging_laser_slot is None
                state_label = "roof-regen"
            else:
                ax = sum(e["pos"][0] for e in enemies_with_los) / len(enemies_with_los)
                ay = sum(e["pos"][1] for e in enemies_with_los) / len(enemies_with_los)
                away_yaw = math.atan2(y - ay, x - ax)
                cold_yaw = math.atan2(self.macro_goal[1] - y, self.macro_goal[0] - x)
                goal_xy = (
                    x + (math.cos(away_yaw) * 0.65 + math.cos(cold_yaw) * 0.35) * 40.0,
                    y + (math.sin(away_yaw) * 0.65 + math.sin(cold_yaw) * 0.35) * 40.0,
                )
                want_zero_los = True
                want_boost = energy > 22.0 and charging_laser_slot is None
                state_label = "disengage"
        # 5. Preserve Active Regen Continuity (SEAL / REGEN with 0 LOS enemies -> stay safe, NEVER wander out!)
        elif in_regen_cover:
            if cur_roof is not None:
                goal_xy = (cur_roof.cx, cur_roof.cy)
                use_astar = False
                state_label = "roof-heal"
            elif best_drop is not None and dist2d((x, y), (best_drop["pos"][0], best_drop["pos"][1])) < 45.0 and best_drop["lands_in"] <= 1.5:
                goal_xy = (best_drop["pos"][0], best_drop["pos"][1])
                state_label = "heal-drop"
            else:
                # Rotate smoothly toward cold cover pocket away from remembered enemies
                goal_xy = self.macro_goal
                want_zero_los = True
                state_label = "seal-heal" if self.regen_state == "SEAL" else "nanite-heal"
        # 6. Anti-Encirclement Pinch Escape (even before 2+ enemies have LOS!)
        elif encirc_here > 2.2 and danger_here > 3.2 and not finishable:
            goal_xy = self.macro_goal
            want_boost = energy > 32.0 and charging_laser_slot is None
            want_1v1_slice = len(enemies_with_los) >= 2
            state_label = "anti-pinch"
        # 7. Risk-Gated Weapon Acquisition
        elif want_weapon_pos is not None and closest_los_dist > 34.0 and hp_frac > 0.45:
            goal_xy = (want_weapon_pos[1][0], want_weapon_pos[1][1])
            want_boost = energy > 34.0 and charging_laser_slot is None
            if want_weapon_pos[1][2] > z + 4.0:
                allow_climb = True
            keep_on_roof = False
            state_label = f"rush-{want_weapon_pos[0]}"
        # 8. Active Roof Climb Hysteresis
        elif self.climbing_roof is not None and closest_los_dist > 40.0:
            goal_xy = (self.climbing_roof.cx, self.climbing_roof.cy)
            allow_climb = True
            use_astar = False
            state_label = "climb-roof"
        # 9. Nearby Cube (strictly <= 10 cap unless right beside us)
        elif best_cube_pos is not None and dist3d(pos, best_cube_pos) < cube_pick_r and len(enemies_with_los) <= 1:
            goal_xy = (best_cube_pos[0], best_cube_pos[1])
            use_astar = False
            if best_cube_pos[2] < z - 4.0:
                keep_on_roof = False
            state_label = "cube"
        # 10. Uncontested Supply Drop Approach
        elif best_drop is not None and len(enemies_with_los) == 0:
            goal_xy = (best_drop["pos"][0], best_drop["pos"][1])
            want_boost = energy > 38.0 and dist2d((x, y), goal_xy) > 12.0
            keep_on_roof = False
            state_label = "drop"
        # 11. Active Combat (1v1 Slicing / Weapon-Cycle Cover / Roof Ledge Discipline)
        elif best_los_enemy is not None:
            d_en = dist3d(pos, best_los_enemy["pos"])
            use_astar = False
            if len(enemies_with_los) >= 2:
                # On roof with Laser on cooldown vs 2+ ground threats -> dip inward during cooldown!
                if cur_roof is not None and has_laser and laser_cd_rem > 0.35 and all(e["pos"][2] < z - 4.0 for e in enemies_with_los):
                    goal_xy = (cur_roof.cx, cur_roof.cy)
                    state_label = "roof-cd"
                else:
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
                    opt_range = 35.0 if d_en < 45.0 else 88.0
                elif has_laser:
                    opt_range = 94.0
                elif has_lightning:
                    opt_range = 34.0
                else:
                    opt_range = 78.0
                radial = 0.50 if d_en > opt_range + 16.0 else (-0.75 if d_en < opt_range - 14.0 else 0.0)
                strafe_ang = en_yaw + self.strafe_dir * (math.pi * 0.5)
                mx = math.cos(en_yaw) * radial + math.cos(strafe_ang) * 0.92
                my = math.sin(en_yaw) * radial + math.sin(strafe_ang) * 0.92
                goal_xy = (x + mx * 30.0, y + my * 30.0)
                # Laser cooldown cover bias during 1v1 duels (unless target is finishable!)
                if has_laser and laser_cd_rem > 0.45 and float(best_los_enemy.get("hp", 1000.0)) > 450.0 and d_en > 45.0:
                    want_zero_los = True
                want_boost = energy > 48.0 and d_en < 52.0 and charging_laser_slot is None
                state_label = f"kite-{best_los_enemy['id']:.0f}"
        # 12. Claim Strong Rooftop Fortress (using exact 1-D climb energy & threat check)
        elif not on_roof and has_laser and zone["radius"] > 70.0:
            rr = self._best_roof_record(x, y, z, energy, jet_drain, t, zone, danger_here)
            if rr is not None:
                self.climbing_roof = rr
                goal_xy = (rr.cx, rr.cy)
                allow_climb = True
                state_label = "take-roof"
        # 13. Safe Early Cube Farming (NPCs & Crates up to stat_cap=10 when 0 LOS threats)
        elif npcs and cubes < self.stat_cap and hp_frac > 0.55 and not protect_regen:
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
                use_astar = False
                keep_on_roof = False
                state_label = "farm-npc"
        elif best_crate_pos is not None and cubes < self.stat_cap and not protect_regen:
            if dist3d(pos, best_crate_pos) < 105.0:
                goal_xy = (best_crate_pos[0], best_crate_pos[1])
                if best_crate_pos[2] > z + 4.0:
                    allow_climb = True
                keep_on_roof = False
                state_label = "farm-crate"

        # Layer 3: Fine 6m A* Waypoint Planning (cached at 2 Hz, instant invalidation if goal shifts > 18m)
        nav_target = goal_xy
        if use_astar and (not on_roof) and dist2d((x, y), goal_xy) > 24.0:
            goal_shifted = self.cached_wp_goal is None or dist2d(goal_xy, self.cached_wp_goal) > 18.0
            if tick - self.wp_tick >= 5 or self.cached_wp is None or goal_shifted:
                self.cached_wp = self.map.astar_waypoint((x, y), goal_xy, threats_for_astar)
                self.cached_wp_goal = goal_xy
                self.wp_tick = tick
            nav_target = self.cached_wp

        if capturing_drop:
            self.stuck_ticks = 0
        desired_yaw = math.atan2(nav_target[1] - y, nav_target[0] - x)
        if self.stuck_ticks > 4:
            desired_yaw = wrap_angle(desired_yaw + self.strafe_dir * (math.pi * 0.55))

        if capturing_drop and best_drop is not None and dist2d((x, y), (best_drop["pos"][0], best_drop["pos"][1])) > best_drop["radius"] - 2.0:
            move_vec = [math.cos(desired_yaw), math.sin(desired_yaw)]
            need_jump, need_jet = False, False
        else:
            move_vec, need_jump, need_jet = self._local_steer(
                pos,
                desired_yaw,
                zone,
                (dodge_x, dodge_y),
                my_radius,
                my_height,
                cover_targets if (want_zero_los or want_1v1_slice) else [],
                flanker_xy,
                want_zero_los,
                want_1v1_slice,
                allow_climb,
                keep_on_roof,
                energy,
            )

        jump_cmd = False
        if need_jet or (self.climbing_roof is not None and not me["grounded"] and z < self.climbing_roof.top_z + 0.5):
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

        # Combat Aim, Simultaneous Laser+Gun Dual-Fire & Rear-Armor Guard Yaw
        fire = [False, False]
        aim_yaw, aim_pitch = me["aim"][0], 0.0
        target_pos: Optional[List[float]] = None
        target_vel = [0.0, 0.0, 0.0]
        target_z_off = 4.5
        target_radius = 2.5
        target_los = False
        target_hp = 1000.0

        # Invariant: NEVER suppress fire on an enemy with LOS! Only suppress NPC/crate/blind-mortar during SEAL/REGEN!
        if best_los_enemy is not None:
            ec = float(best_los_enemy.get("cubes", 0.0))
            escale = 1.0 + self.size_per_cube * ec
            target_pos = best_los_enemy["pos"]
            target_vel = best_los_enemy["vel"]
            target_z_off = best_los_z_off
            target_radius = self.base_radius * escale
            target_los = True
            target_hp = float(best_los_enemy.get("hp", 1000.0))
        elif (not in_regen_cover) and best_any_enemy is not None:
            ec = float(best_any_enemy.get("cubes", 0.0))
            escale = 1.0 + self.size_per_cube * ec
            target_pos = best_any_enemy["pos"]
            target_vel = best_any_enemy["vel"]
            target_z_off = 4.5 * escale
            target_radius = self.base_radius * escale
            target_los = False
            target_hp = float(best_any_enemy.get("hp", 1000.0))
        elif npcs and hp_frac > 0.48 and cubes < self.stat_cap and not protect_regen:
            npc = min(npcs, key=lambda n: dist3d(pos, n["pos"]))
            if dist3d(pos, npc["pos"]) < 100.0:
                target_pos = npc["pos"]
                target_vel = npc["vel"]
                target_z_off = 1.8
                target_radius = 1.8
                target_los = self.map.has_los(muzzle, [target_pos[0], target_pos[1], target_pos[2] + 1.8])
                target_hp = float(npc.get("hp", 350.0))
        elif obs["crates"] and hp_frac > 0.48 and cubes < self.stat_cap and not protect_regen:
            cr = min(obs["crates"], key=lambda c: dist3d(pos, c["pos"]))
            if dist3d(pos, cr["pos"]) < 95.0:
                target_pos = cr["pos"]
                target_z_off = 1.5
                target_radius = 1.6
                target_los = self.map.has_los(muzzle, [target_pos[0], target_pos[1], target_pos[2] + 1.5])
                target_hp = float(cr.get("hp", 300.0))

        # Preserve active laser charge only while a LOS target exists
        if charging_laser_slot is not None and target_pos is not None and target_los:
            fire[charging_laser_slot] = True

        if target_pos is not None:
            d_tgt = dist3d(pos, target_pos)
            direct_yaw = math.atan2(target_pos[1] - y, target_pos[0] - x)
            direct_pitch = math.atan2(target_pos[2] + target_z_off - muzzle[2], max(0.1, dist2d((x, y), (target_pos[0], target_pos[1]))))
            aim_yaw, aim_pitch = direct_yaw, direct_pitch

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
                    if k == "lightning" and target_los and d_tgt <= float(ws.get("range", 45.0)) - 1.0 and energy > 9.0:
                        s = 115.0
                    elif k == "laser" and target_los and d_tgt <= float(ws.get("range", 280.0)) - 5.0:
                        if (d_tgt > 38.0 or float(w.get("charge", 0.0)) > 0.0) and (w["cooldown"] <= 0.1 or float(w.get("charge", 0.0)) > 0.0):
                            s = 105.0
                    elif k == "gun" and target_los and d_tgt <= float(ws.get("range", 230.0)) - 5.0 and float(w.get("reload", 0.0)) == 0.0:
                        s = 96.0
                    elif k == "mortar" and (not in_regen_cover) and 18.0 < d_tgt < 225.0 and w["cooldown"] <= 0.1:
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
                    if charge < max_c * 0.84 and ow is not None and ow["kind"] == "gun" and float(ow.get("reload", 0.0)) == 0.0 and d_tgt <= float(ow["stats"].get("range", 230.0)) - 5.0:
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
                            fire[primary_slot] = False
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

                # Simultaneous Dual-Fire Secondary Slot
                if ow is not None and target_los:
                    ok = ow["kind"]
                    ows = ow["stats"]
                    pyaw, _ = self._predict_slewed_aim(me["aim"], aim_yaw, aim_pitch, turn_rate, pitch_rate)
                    if ok == "gun" and float(ow.get("reload", 0.0)) == 0.0 and d_tgt <= float(ows.get("range", 230.0)) - 5.0:
                        if abs(angle_diff(pyaw, aim_yaw)) < 0.15:
                            fire[other] = True
                    elif ok == "lightning" and energy > 10.0 and d_tgt <= float(ows.get("range", 45.0)) - 1.0:
                        cone_half = math.radians(float(ows.get("cone_deg", 30.0)) * 0.46)
                        if abs(angle_diff(pyaw, direct_yaw)) <= cone_half:
                            fire[other] = True
            else:
                # Not firing -> protect 1.5x rear armor using weighted threat guard yaw!
                aim_yaw = self._guard_yaw(x, y, t, direct_yaw)
        else:
            # Rear-Armor Guard Yaw when out of sight / healing / rotating!
            guard = self._guard_yaw(x, y, t, 999.0)
            if guard < 100.0:
                aim_yaw = guard
            elif t - self.last_damage_taken_t < 2.5 and self.last_damage_bearing is not None:
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

        act["aim"] = [aim_yaw, clamp(aim_pitch, min_pitch, max_pitch)]
        act["fire"] = fire

        mf.draw.label(f"{state_label} | hp {me['hp']:.0f} | c {cubes:.0f}")
        return act


mf.run(Bot)