"""Apex Mech Royale AI — 3D map-aware, ballistic-aiming, survival-first combat bot."""
from __future__ import annotations

import json
import math
import os
import random
import struct
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
    """Fast spatial-hashed 3D map loader for world.json + terrain.i16."""

    def __init__(self, map_dir: str):
        self.cell = 25.0
        self.grid: Dict[Tuple[int, int], List[Prism]] = {}
        self.prisms: List[Prism] = []
        self.nx = 0
        self.ny = 0
        self.min_x = 0.0
        self.min_y = 0.0
        self.step = 1.0
        self.scale = 0.01
        self.terrain: Optional[memoryview] = None
        self.bounds = (-500.0, 540.0, -320.0, 375.0)
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
            self.prisms.append(p)
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
        if z < self.terrain_z(x, y) - 0.1:
            return True
        cell_prisms = self.grid.get((int(math.floor(x / self.cell)), int(math.floor(y / self.cell))))
        if not cell_prisms:
            return False
        for p in cell_prisms:
            if p.base <= z <= p.top and p.contains_xy(x, y):
                return True
        return False

    def blocked_at_feet(self, x: float, y: float, feet_z: float, step_up: float = 1.2) -> bool:
        if x < self.bounds[0] or x > self.bounds[1] or y < self.bounds[2] or y > self.bounds[3]:
            return True
        tz = self.terrain_z(x, y)
        if tz > feet_z + step_up + 0.5:
            return True
        cell_prisms = self.grid.get((int(math.floor(x / self.cell)), int(math.floor(y / self.cell))))
        if not cell_prisms:
            return False
        for p in cell_prisms:
            # Solid wall if prism overlaps mech body (feet_z + step_up to feet_z + 8.5)
            if p.top > feet_z + step_up and p.base < feet_z + 8.5:
                if p.contains_xy(x, y):
                    return True
        return False

    def has_los(self, a: List[float], b: List[float], step_m: float = 3.5) -> bool:
        dx, dy, dz = b[0] - a[0], b[1] - a[1], b[2] - a[2]
        d = math.sqrt(dx * dx + dy * dy + dz * dz)
        if d < 3.5:
            return True
        steps = max(2, min(60, int(d / step_m)))
        inv = 1.0 / steps
        for k in range(1, steps):
            t = k * inv
            if self.is_solid(a[0] + dx * t, a[1] + dy * t, a[2] + dz * t):
                return False
        return True


class Bot:
    name = "Apex-V1"

    def __init__(self, hello: mf.Hello):
        self.slot = int(hello["slot"])
        self.rng = random.Random(int(hello["seed"]))
        self.cfg = hello["config"]
        self.reach = float(self.cfg["loot"]["pickup_radius"])
        self.map = ArenaMap(hello["map"]["dir"])
        self.last_damage_t = -10.0
        self.last_damage_bearing: Optional[float] = None
        self.last_pos: Optional[Tuple[float, float]] = None
        self.stuck_ticks = 0
        self.strafe_dir = 1.0
        self.strafe_flip_tick = 0
        self.scan_yaw = 0.0

        # Build upgrade preference scores from hello.config.upgrades
        self.upgrade_scores: Dict[str, float] = {}
        for u in self.cfg.get("upgrades", []):
            uid = u["id"]
            score = 1.0
            for eff in u.get("effects", []):
                path = eff.get("path", "")
                if "armor" in path or "damage_mult" in path or "max_hp" in path:
                    score += 4.0
                elif "damage" in path or "cooldown" in path:
                    score += 3.5
                elif "regen" in path or "speed" in path or "energy" in path:
                    score += 2.5
                elif "range" in path or "near_range" in path:
                    score += 2.0
            if "armor" in uid or "hp" in uid or "regen" in uid:
                score += 2.0
            self.upgrade_scores[uid] = score

    def _pick_upgrade(self, offer: mf.Offer, weapons: List[Optional[mf.WeaponObs]]) -> int:
        held = {w["kind"] for w in weapons if w is not None}
        best_i, best_s = 0, -1e9
        for i, c in enumerate(offer["choices"]):
            cid = c["id"]
            s = self.upgrade_scores.get(cid, 1.0)
            if any(k in cid for k in held):
                s += 1.5
            if s > best_s:
                best_s = s
                best_i = i
        return best_i

    def _lead_aim(
        self, muzzle: List[float], target_pos: List[float], target_vel: List[float], proj_speed: float, target_z_off: float
    ) -> Tuple[float, float]:
        tx, ty, tz = target_pos[0], target_pos[1], target_pos[2] + target_z_off
        vx, vy, vz = target_vel[0], target_vel[1], target_vel[2]
        px, py, pz = tx, ty, tz
        for _ in range(2):
            d = math.sqrt((px - muzzle[0]) ** 2 + (py - muzzle[1]) ** 2 + (pz - muzzle[2]) ** 2)
            t = d / max(1.0, proj_speed)
            px = tx + vx * t
            py = ty + vy * t
            pz = tz + vz * t * 0.5
        dx, dy, dz = px - muzzle[0], py - muzzle[1], pz - muzzle[2]
        return math.atan2(dy, dx), math.atan2(dz, max(0.1, math.hypot(dx, dy)))

    def _mortar_aim(
        self, muzzle: List[float], target_pos: List[float], target_vel: List[float], speed: float, g: float, high_arc: bool
    ) -> Optional[Tuple[float, float]]:
        # Lead by approximate flight time
        dx0 = target_pos[0] - muzzle[0]
        dy0 = target_pos[1] - muzzle[1]
        r0 = math.hypot(dx0, dy0)
        t_est = clamp(r0 / max(10.0, speed * 0.75), 0.1, 4.5)
        px = target_pos[0] + target_vel[0] * t_est * 0.7
        py = target_pos[1] + target_vel[1] * t_est * 0.7
        pz = target_pos[2] + 1.0
        dx, dy, dz = px - muzzle[0], py - muzzle[1], pz - muzzle[2]
        r = math.hypot(dx, dy)
        if r < 10.0:
            return None
        v2 = speed * speed
        disc = v2 * v2 - g * (g * r * r + 2.0 * dz * v2)
        if disc < 0.0:
            return None
        sq = math.sqrt(disc)
        pitch = math.atan2(v2 + sq if high_arc else v2 - sq, g * r)
        return math.atan2(dy, dx), pitch

    def _dodge_vector(self, pos: List[float], projs: List[mf.ProjectileObs]) -> Tuple[float, float, bool]:
        ex, ey = 0.0, 0.0
        urgent = False
        mx, my, mz = pos[0], pos[1], pos[2] + 4.5
        for p in projs:
            px, py, pz = p["pos"]
            vx, vy, vz = p["vel"]
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
            thresh = 8.5 if p["kind"] == "mortar" else 4.2
            if d_perp < thresh:
                # Move perpendicular to projectile velocity
                hv = math.hypot(vx, vy)
                if hv > 0.1:
                    nx, ny = -vy / hv, vx / hv
                    # Choose side away from closest point
                    if nx * cx + ny * cy > 0:
                        nx, ny = -nx, -ny
                    w = (thresh - d_perp) / thresh
                    ex += nx * w * (2.5 if p["kind"] == "mortar" else 1.4)
                    ey += ny * w * (2.5 if p["kind"] == "mortar" else 1.4)
                    if p["kind"] == "mortar" or d_perp < 3.0:
                        urgent = True
        return ex, ey, urgent

    def _steer(
        self, pos: List[float], desired_yaw: float, zone: mf.ZoneObs, dodge: Tuple[float, float]
    ) -> Tuple[List[float], bool]:
        x, y, z = pos[0], pos[1], pos[2]
        zcx, zcy = zone["next_center"]
        zr = max(15.0, zone["radius"] - 6.0)
        best_score = -1e9
        best_dir = [math.cos(desired_yaw), math.sin(desired_yaw)]
        need_jump = False

        # Sample 12 directions around desired_yaw
        offsets = (0.0, 0.35, -0.35, 0.75, -0.75, 1.2, -1.2, 1.7, -1.7, 2.3, -2.3, math.pi)
        for off in offsets:
            ang = desired_yaw + off
            dx, dy = math.cos(ang), math.sin(ang)
            nx1, ny1 = x + dx * 5.0, y + dy * 5.0
            nx2, ny2 = x + dx * 11.0, y + dy * 11.0
            blocked1 = self.map.blocked_at_feet(nx1, ny1, z)
            blocked2 = self.map.blocked_at_feet(nx2, ny2, z)

            score = math.cos(off) * 3.0
            score += (dx * dodge[0] + dy * dodge[1]) * 2.5
            if blocked1:
                score -= 8.0
            elif blocked2:
                score -= 2.5

            # Penalize stepping outside zone
            d_zone = dist2d((nx2, ny2), (zone["center"][0], zone["center"][1]))
            if d_zone > zr:
                score -= (d_zone - zr) * 0.4

            if score > best_score:
                best_score = score
                best_dir = [dx, dy]
                need_jump = blocked1

        return best_dir, need_jump

    def act(self, obs: mf.Observation) -> mf.Action:
        me = obs["self"]
        t = float(obs["t"])
        tick = int(obs["tick"])
        pos = me["pos"]
        x, y, z = pos[0], pos[1], pos[2]
        hp_frac = me["hp"] / max(1.0, me["max_hp"])
        energy = float(me["energy"])
        weapons = me["weapons"]
        zone = obs["zone"]
        stats = me["stats"]
        muzzle_h = float(stats.get("muzzle_height", 7.0))
        eye_h = float(stats.get("eye_height", 8.0))
        muzzle = [x, y, z + muzzle_h]
        eye = [x, y, z + eye_h]

        act: mf.Action = {"tick": tick}

        # 1. Track damage events & stuck detection
        for ev in obs["events"]:
            if ev["type"] == "damaged":
                self.last_damage_t = t
                if ev.get("bearing") is not None:
                    self.last_damage_bearing = float(ev["bearing"])
        if self.last_pos is not None and dist2d((x, y), self.last_pos) < 0.15:
            self.stuck_ticks += 1
        else:
            self.stuck_ticks = 0
        self.last_pos = (x, y)

        if tick - self.strafe_flip_tick > 22:
            self.strafe_dir = -self.strafe_dir
            self.strafe_flip_tick = tick

        # 2. Pick upgrades immediately
        if obs["offer"]:
            act["pick"] = self._pick_upgrade(obs["offer"], weapons)

        # 3. Weapon pickup / swap logic (prefer laser > lightning > mortar > gun)
        w_rank = {"laser": 4, "lightning": 3, "mortar": 2, "gun": 1}
        held_kinds = {w["kind"] for w in weapons if w is not None}
        laser_charging = any(w is not None and w["kind"] == "laser" and w.get("charge", 0.0) > 0.0 for w in weapons)
        for p in obs["pickups"]:
            if p["kind"] in held_kinds:
                continue
            if dist2d((x, y), (p["pos"][0], p["pos"][1])) < self.reach - 0.15 and abs(p["pos"][2] - z) < 3.8:
                if weapons[1] is None:
                    act["take"] = p["id"]
                    break
                elif weapons[0] is None:
                    act["take"] = p["id"]
                    break
                elif not laser_charging:
                    # Swap out weakest weapon if pickup is strictly better
                    worst_slot = 0 if w_rank[weapons[0]["kind"]] <= w_rank[weapons[1]["kind"]] else 1
                    if w_rank[p["kind"]] > w_rank[weapons[worst_slot]["kind"]]:
                        act["take"] = p["id"]
                        act["drop"] = worst_slot
                        break

        # 4. Categorize visible actors
        enemies = [m for m in obs["mechs"] if m["kind"] == "mech"]
        npcs = [m for m in obs["mechs"] if m["kind"] == "npc"]

        # Score enemies: closer + lower HP + clear LOS + cook-off bonus
        has_laser = "laser" in held_kinds
        best_enemy: Optional[mf.ActorObs] = None
        best_enemy_los = False
        best_enemy_score = -1e9
        for e in enemies:
            d = dist3d(pos, e["pos"])
            los = self.map.has_los(eye, [e["pos"][0], e["pos"][1], e["pos"][2] + 4.5])
            ehp = float(e.get("hp", 1000.0))
            s = -d * 1.2 + (1400.0 - ehp) * 0.08 + (80.0 if los else -40.0)
            if has_laser and "mortar" in e.get("weapons", []):
                s += 35.0
            if s > best_enemy_score:
                best_enemy_score = s
                best_enemy = e
                best_enemy_los = los

        # 5. Movement goal selection
        zcx, zcy = zone["next_center"]
        dist_to_cur_center = dist2d((x, y), (zone["center"][0], zone["center"][1]))
        zone_urgent = (not me["in_zone"]) or (dist_to_cur_center > zone["radius"] - 22.0)

        goal_xy = (zcx, zcy)
        want_boost = False
        state_label = "zone"

        # Check supply drops
        best_drop: Optional[mf.DropObs] = None
        for dr in obs["drops"]:
            d_drop = dist2d((x, y), (dr["pos"][0], dr["pos"][1]))
            if d_drop < 140.0 and (hp_frac < 0.75 or me["cubes"] < 8):
                best_drop = dr
                break

        if zone_urgent:
            goal_xy = (zcx, zcy)
            want_boost = energy > 20.0
            state_label = "zone-rush"
        elif hp_frac < 0.42 and best_enemy is not None and dist3d(pos, best_enemy["pos"]) < 110.0:
            # Disengage away from enemy toward zone center to trigger 5s HP regen
            away_yaw = math.atan2(y - best_enemy["pos"][1], x - best_enemy["pos"][0])
            z_yaw = math.atan2(zcy - y, zcx - x)
            mix_x = math.cos(away_yaw) * 0.7 + math.cos(z_yaw) * 0.3
            mix_y = math.sin(away_yaw) * 0.7 + math.sin(z_yaw) * 0.3
            goal_xy = (x + mix_x * 40.0, y + mix_y * 40.0)
            want_boost = energy > 25.0
            state_label = "disengage"
        elif best_drop is not None and (best_enemy is None or dist3d(pos, best_enemy["pos"]) > 40.0):
            goal_xy = (best_drop["pos"][0], best_drop["pos"][1])
            want_boost = energy > 35.0 and dist2d((x, y), goal_xy) > 15.0
            state_label = "supply-drop"
        elif obs["cubes"]:
            c = min(obs["cubes"], key=lambda item: dist3d(pos, item["pos"]))
            if dist3d(pos, c["pos"]) < 65.0:
                goal_xy = (c["pos"][0], c["pos"][1])
                state_label = "cube"
        elif weapons[1] is None and obs["pickups"]:
            cand = [p for p in obs["pickups"] if p["kind"] != "gun"]
            if cand:
                p = min(cand, key=lambda item: dist3d(pos, item["pos"]))
                if dist3d(pos, p["pos"]) < 90.0:
                    goal_xy = (p["pos"][0], p["pos"][1])
                    want_boost = energy > 45.0
                    state_label = f"loot-{p['kind']}"
        elif best_enemy is not None:
            # Combat kiting: maintain optimal range based on our weapons
            d_en = dist3d(pos, best_enemy["pos"])
            en_yaw = math.atan2(best_enemy["pos"][1] - y, best_enemy["pos"][0] - x)
            opt_range = 32.0 if "lightning" in held_kinds else (95.0 if has_laser else 65.0)
            radial = 0.0
            if d_en > opt_range + 15.0:
                radial = 0.55
            elif d_en < opt_range - 12.0:
                radial = -0.65
            strafe_ang = en_yaw + self.strafe_dir * (math.pi * 0.5)
            mx = math.cos(en_yaw) * radial + math.cos(strafe_ang) * 0.85
            my = math.sin(en_yaw) * radial + math.sin(strafe_ang) * 0.85
            goal_xy = (x + mx * 30.0, y + my * 30.0)
            want_boost = energy > 55.0 and d_en < 55.0
            state_label = f"fight-{best_enemy['id']:.0f}"
        elif obs["crates"] and me["cubes"] < 10:
            cr = min(obs["crates"], key=lambda item: dist3d(pos, item["pos"]))
            if dist3d(pos, cr["pos"]) < 75.0:
                goal_xy = (cr["pos"][0], cr["pos"][1])
                state_label = "farm-crate"

        desired_yaw = math.atan2(goal_xy[1] - y, goal_xy[0] - x)
        dodge_x, dodge_y, dodge_urgent = self._dodge_vector(pos, obs["projectiles"])
        move_vec, need_jump = self._steer(pos, desired_yaw, zone, (dodge_x, dodge_y))

        jump_cmd = False
        if need_jump or self.stuck_ticks > 4:
            if me["grounded"]:
                jump_cmd = True
            elif energy > 25.0:
                want_boost = True  # Jet over ledge
        if dodge_urgent and energy > 15.0:
            want_boost = True

        act["move"] = move_vec
        act["boost"] = want_boost
        act["jump"] = jump_cmd

        # 6. Aiming & Firing
        fire = [False, False]
        aim_yaw, aim_pitch = me["aim"][0], 0.0
        target_pos: Optional[List[float]] = None
        target_vel = [0.0, 0.0, 0.0]
        target_z_off = 4.5
        target_los = False
        target_is_mech = False

        if best_enemy is not None:
            target_pos = best_enemy["pos"]
            target_vel = best_enemy["vel"]
            target_z_off = 4.5
            target_los = best_enemy_los
            target_is_mech = True
        elif npcs and hp_frac > 0.55 and me["cubes"] < 10:
            npc = min(npcs, key=lambda n: dist3d(pos, n["pos"]))
            if dist3d(pos, npc["pos"]) < 85.0:
                target_pos = npc["pos"]
                target_vel = npc["vel"]
                target_z_off = 1.8
                target_los = self.map.has_los(eye, [target_pos[0], target_pos[1], target_pos[2] + 1.8])
        elif obs["crates"] and hp_frac > 0.55 and me["cubes"] < 10:
            cr = min(obs["crates"], key=lambda c: dist3d(pos, c["pos"]))
            if dist3d(pos, cr["pos"]) < 70.0:
                target_pos = cr["pos"]
                target_z_off = 1.5
                target_los = self.map.has_los(eye, [target_pos[0], target_pos[1], target_pos[2] + 1.5])

        if target_pos is not None:
            d_tgt = dist3d(pos, target_pos)
            # Choose best weapon for this target
            for slot_i, w in enumerate(weapons):
                if w is None:
                    continue
                kind = w["kind"]
                ws = w["stats"]
                if kind == "lightning":
                    if d_tgt <= float(ws.get("range", 45.0)) - 1.5 and target_los and energy > 12.0:
                        aim_yaw = math.atan2(target_pos[1] - y, target_pos[0] - x)
                        aim_pitch = math.atan2(target_pos[2] + target_z_off - muzzle[2], max(0.1, dist2d((x, y), (target_pos[0], target_pos[1]))))
                        if abs(angle_diff(me["aim"][0], aim_yaw)) < 0.45:
                            fire[slot_i] = True
                elif kind == "laser":
                    if target_los and d_tgt <= float(ws.get("range", 280.0)) - 5.0:
                        aim_yaw = math.atan2(target_pos[1] - y, target_pos[0] - x)
                        aim_pitch = math.atan2(target_pos[2] + target_z_off - muzzle[2], max(0.1, dist2d((x, y), (target_pos[0], target_pos[1]))))
                        charge = float(w.get("charge", 0.0))
                        max_c = float(ws.get("charge", 0.75))
                        min_c = float(ws.get("min_charge", 0.15))
                        yaw_err = abs(angle_diff(me["aim"][0], aim_yaw))
                        pitch_err = abs(me["aim"][1] - aim_pitch)
                        # Hold to charge, release when charged and aligned
                        if charge >= max_c * 0.90 and yaw_err < 0.07 and pitch_err < 0.07:
                            fire[slot_i] = False  # Release beam!
                        elif not target_is_mech and charge >= min_c and yaw_err < 0.07:
                            fire[slot_i] = False
                        elif w["cooldown"] <= 0.05:
                            fire[slot_i] = True
                elif kind == "mortar":
                    if d_tgt > 18.0 and d_tgt < 225.0 and w["cooldown"] <= 0.05:
                        m_aim = self._mortar_aim(
                            [x, y, z + 9.5],
                            target_pos,
                            target_vel,
                            float(ws.get("speed", 72.0)),
                            float(ws.get("gravity", 22.0)),
                            high_arc=not target_los,
                        )
                        if m_aim is not None:
                            aim_yaw, aim_pitch = m_aim
                            if abs(angle_diff(me["aim"][0], aim_yaw)) < 0.12 and abs(me["aim"][1] - aim_pitch) < 0.12:
                                fire[slot_i] = True
                elif kind == "gun":
                    if target_los and d_tgt <= float(ws.get("range", 230.0)) - 5.0:
                        g_yaw, g_pitch = self._lead_aim(
                            muzzle, target_pos, target_vel, float(ws.get("speed", 252.0)), target_z_off
                        )
                        if not any(fire):
                            aim_yaw, aim_pitch = g_yaw, g_pitch
                        if abs(angle_diff(me["aim"][0], g_yaw)) < 0.15:
                            fire[slot_i] = True
        else:
            # No visible target: face recent damage bearing (rear-armor protection), or scan 360°
            if t - self.last_damage_t < 2.5 and self.last_damage_bearing is not None:
                aim_yaw = self.last_damage_bearing
            elif obs["sounds"]:
                s = min(obs["sounds"], key=lambda item: (0 if item["dist"] == "near" else 1 if item["dist"] == "mid" else 2, item["age"]))
                aim_yaw = float(s["bearing"])
            else:
                self.scan_yaw = wrap_angle(self.scan_yaw + 0.35)
                aim_yaw = self.scan_yaw
            # Early gun reload when safe
            for w in weapons:
                if w is not None and w["kind"] == "gun" and w.get("reload", 0.0) == 0.0:
                    if w.get("ammo", 12) < w["stats"].get("mag", 12) * 0.5:
                        act["reload"] = True

        act["aim"] = [aim_yaw, clamp(aim_pitch, -1.2, 1.2)]
        act["fire"] = fire

        mf.draw.label(f"{state_label} | hp {me['hp']:.0f} | c {me['cubes']:.0f}")
        return act


mf.run(Bot)