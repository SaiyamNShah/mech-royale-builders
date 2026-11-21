"""Apex-V5 — Distance-scaled hitscan, 600-DPS dual-fire, cube snowball & anti-squad kiting."""
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
    """Fast spatial-hashed 3D map for muzzle LOS and obstacle avoidance."""

    def __init__(self, map_dir: str):
        self.cell = 25.0
        self.grid: Dict[Tuple[int, int], List[Prism]] = {}
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
        if self.terrain_z(x, y) > feet_z + step_up + 0.5:
            return True
        cell_prisms = self.grid.get((int(math.floor(x / self.cell)), int(math.floor(y / self.cell))))
        if not cell_prisms:
            return False
        for p in cell_prisms:
            if p.top > feet_z + step_up and p.base < feet_z + 8.5 and p.contains_xy(x, y):
                return True
        return False

    def has_los(self, a: List[float], b: List[float], step_m: float = 3.5) -> bool:
        dx, dy, dz = b[0] - a[0], b[1] - a[1], b[2] - a[2]
        d = math.sqrt(dx * dx + dy * dy + dz * dz)
        if d < 3.5:
            return True
        steps = max(2, min(48, int(d / step_m)))
        inv = 1.0 / steps
        for k in range(1, steps):
            t = k * inv
            if self.is_solid(a[0] + dx * t, a[1] + dy * t, a[2] + dz * t):
                return False
        return True


class Bot:
    name = "Apex-V5"

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
        self.strafe_dir = 1.0 if (self.slot % 2 == 0) else -1.0
        self.strafe_flip_tick = 0
        self.scan_yaw = 0.0

        # Score upgrades: Survival (Armor/HP/Regen) + DPS (Damage/Cooldown)
        self.upgrade_scores: Dict[str, float] = {}
        for u in self.cfg.get("upgrades", []):
            uid = u["id"]
            score = 1.0
            for eff in u.get("effects", []):
                path = eff.get("path", "")
                if "armor" in path or "damage_mult" in path:
                    score += 8.0
                elif "max_hp" in path or "regen" in path:
                    score += 7.0
                elif "damage" in path or "cooldown" in path or "charge" in path:
                    score += 6.0
                elif "speed" in path or "energy" in path:
                    score += 3.5
                elif "range" in path or "near_range" in path:
                    score += 2.0
            if any(k in uid for k in ("armor", "regen", "hp", "shield")):
                score += 3.0
            self.upgrade_scores[uid] = score

    def _pick_upgrade(self, offer: mf.Offer, weapons: List[Optional[mf.WeaponObs]]) -> int:
        held = {w["kind"] for w in weapons if w is not None}
        best_i, best_s = 0, -1e9
        for i, c in enumerate(offer["choices"]):
            cid = c["id"]
            s = self.upgrade_scores.get(cid, 1.0)
            if any(k in cid for k in held):
                s += 3.0
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
        for _ in range(3):
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
        r0 = math.hypot(target_pos[0] - muzzle[0], target_pos[1] - muzzle[1])
        t_est = clamp(r0 / max(10.0, speed * 0.75), 0.1, 4.5)
        px = target_pos[0] + target_vel[0] * t_est * 0.65
        py = target_pos[1] + target_vel[1] * t_est * 0.65
        pz = target_pos[2] + 1.0
        dx, dy, dz = px - muzzle[0], py - muzzle[1], pz - muzzle[2]
        r = math.hypot(dx, dy)
        if r < 14.0:
            return None
        v2 = speed * speed
        disc = v2 * v2 - g * (g * r * r + 2.0 * dz * v2)
        if disc < 0.0:
            return None
        sq = math.sqrt(disc)
        pitch = math.atan2(v2 + sq if high_arc else v2 - sq, g * r)
        return math.atan2(dy, dx), pitch

    def _dodge_vector(
        self, pos: List[float], projs: List[mf.ProjectileObs], enemies: List[mf.ActorObs]
    ) -> Tuple[float, float, bool]:
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
            thresh = 9.5 if p["kind"] == "mortar" else 4.6
            if d_perp < thresh:
                hv = math.hypot(vx, vy)
                if hv > 0.1:
                    nx, ny = -vy / hv, vx / hv
                    if nx * cx + ny * cy > 0:
                        nx, ny = -nx, -ny
                    w = (thresh - d_perp) / thresh
                    mult = 3.5 if p["kind"] == "mortar" else 1.8
                    ex += nx * w * mult
                    ey += ny * w * mult
                    if p["kind"] == "mortar" or d_perp < 3.0:
                        urgent = True

        for e in enemies:
            if e.get("charging"):
                ep = e["pos"]
                to_me_yaw = math.atan2(my - ep[1], mx - ep[0])
                if abs(angle_diff(e["aim"][0], to_me_yaw)) < 0.25:
                    perp = to_me_yaw + self.strafe_dir * (math.pi * 0.5)
                    ex += math.cos(perp) * 3.8
                    ey += math.sin(perp) * 3.8
                    urgent = True

        return ex, ey, urgent

    def _steer(
        self, pos: List[float], desired_yaw: float, zone: mf.ZoneObs, dodge: Tuple[float, float]
    ) -> Tuple[List[float], bool]:
        x, y, z = pos[0], pos[1], pos[2]
        zr = max(14.0, zone["radius"] - 6.0)
        best_score = -1e9
        best_dir = [math.cos(desired_yaw), math.sin(desired_yaw)]
        need_jump = False

        offsets = (0.0, 0.38, -0.38, 0.82, -0.82, 1.3, -1.3, 1.85, -1.85, 2.45, -2.45, math.pi)
        for off in offsets:
            ang = desired_yaw + off
            dx, dy = math.cos(ang), math.sin(ang)
            nx1, ny1 = x + dx * 5.0, y + dy * 5.0
            nx2, ny2 = x + dx * 12.0, y + dy * 12.0
            b1 = self.map.blocked_at_feet(nx1, ny1, z)
            b2 = self.map.blocked_at_feet(nx2, ny2, z)

            score = math.cos(off) * 3.2
            score += (dx * dodge[0] + dy * dodge[1]) * 3.0
            if b1:
                score -= 9.5
            elif b2:
                score -= 3.0

            d_zone = dist2d((nx2, ny2), (zone["center"][0], zone["center"][1]))
            if d_zone > zr:
                score -= (d_zone - zr) * 0.45

            if score > best_score:
                best_score = score
                best_dir = [dx, dy]
                need_jump = b1

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
        muzzle = [x, y, z + muzzle_h]

        act: mf.Action = {"tick": tick}

        # 1. Track damage & stuck state
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

        if tick - self.strafe_flip_tick > 16:
            self.strafe_dir = -self.strafe_dir
            self.strafe_flip_tick = tick

        # 2. Pick upgrades immediately
        if obs["offer"]:
            act["pick"] = self._pick_upgrade(obs["offer"], weapons)

        # 3. Weapon pickup: Dream loadout = Lightning + Gun (or Lightning + Laser)
        w_rank = {"lightning": 5, "gun": 4, "laser": 3, "mortar": 1}
        held_kinds = {w["kind"] for w in weapons if w is not None}
        laser_charging = any(w is not None and w["kind"] == "laser" and w.get("charge", 0.0) > 0.0 for w in weapons)
        for p in obs["pickups"]:
            if p["kind"] in held_kinds:
                continue
            if dist2d((x, y), (p["pos"][0], p["pos"][1])) < self.reach - 0.15 and abs(p["pos"][2] - z) < 3.8:
                if weapons[1] is None or weapons[0] is None:
                    act["take"] = p["id"]
                    break
                elif not laser_charging:
                    worst_slot = 0 if w_rank[weapons[0]["kind"]] <= w_rank[weapons[1]["kind"]] else 1
                    if w_rank[p["kind"]] > w_rank[weapons[worst_slot]["kind"]]:
                        act["take"] = p["id"]
                        act["drop"] = worst_slot
                        break

        # 4. Analyze visible enemies using MUZZLE LOS (exact shot clearance)
        enemies = [m for m in obs["mechs"] if m["kind"] == "mech"]
        npcs = [m for m in obs["mechs"] if m["kind"] == "npc"]

        has_laser = "laser" in held_kinds
        has_lightning = "lightning" in held_kinds
        enemies_with_los: List[mf.ActorObs] = []
        best_enemy: Optional[mf.ActorObs] = None
        best_enemy_los = False
        best_enemy_score = -1e9

        for e in enemies:
            d = dist3d(pos, e["pos"])
            los = self.map.has_los(muzzle, [e["pos"][0], e["pos"][1], e["pos"][2] + 4.5])
            if los:
                enemies_with_los.append(e)
            ehp = float(e.get("hp", 1000.0))
            s = -d * 1.25 + (1400.0 - ehp) * 0.16 + (110.0 if los else -60.0)
            if ehp < 400.0 and los:
                s += 160.0  # Secure kill for placement + cubes
            if has_laser and "mortar" in e.get("weapons", []):
                s += 50.0
            if s > best_enemy_score:
                best_enemy_score = s
                best_enemy = e
                best_enemy_los = los

        # 5. Movement: Zone > Supply Drop > Cubes > Anti-Squad Kite > Duel > Farm
        zcx, zcy = zone["next_center"]
        dist_to_cur = dist2d((x, y), (zone["center"][0], zone["center"][1]))
        zone_urgent = (not me["in_zone"]) or (dist_to_cur > zone["radius"] - 22.0)

        # Safe perimeter anchor (55% of next_radius) to avoid 360° encirclement
        ang_from_c = math.atan2(y - zcy, x - zcx)
        edge_r = max(10.0, zone["next_radius"] * 0.55)
        edge_anchor = (zcx + math.cos(ang_from_c) * edge_r, zcy + math.sin(ang_from_c) * edge_r)

        goal_xy = edge_anchor
        want_boost = False
        state_label = "edge"

        best_drop: Optional[mf.DropObs] = None
        for dr in obs["drops"]:
            if dist2d((x, y), (dr["pos"][0], dr["pos"][1])) < 105.0 and dr["lands_in"] < 8.0 and (hp_frac < 0.80 or me["cubes"] < 10):
                best_drop = dr
                break

        if zone_urgent:
            goal_xy = (zcx, zcy)
            want_boost = energy > 18.0
            state_label = "zone-rush"
        elif obs["cubes"] and dist3d(pos, min(obs["cubes"], key=lambda item: dist3d(pos, item["pos"]))["pos"]) < 45.0:
            c = min(obs["cubes"], key=lambda item: dist3d(pos, item["pos"]))
            goal_xy = (c["pos"][0], c["pos"][1])
            want_boost = energy > 35.0 and len(enemies_with_los) > 0
            state_label = "cube"
        elif best_drop is not None and len(enemies_with_los) <= 1:
            goal_xy = (best_drop["pos"][0], best_drop["pos"][1])
            want_boost = energy > 30.0 and dist2d((x, y), goal_xy) > 10.0
            state_label = "drop"
        elif hp_frac < 0.45 and enemies_with_los:
            ax = sum(e["pos"][0] for e in enemies_with_los) / len(enemies_with_los)
            ay = sum(e["pos"][1] for e in enemies_with_los) / len(enemies_with_los)
            away_yaw = math.atan2(y - ay, x - ax)
            z_yaw = math.atan2(zcy - y, zcx - x)
            mx = math.cos(away_yaw) * 0.72 + math.cos(z_yaw) * 0.28
            my = math.sin(away_yaw) * 0.72 + math.sin(z_yaw) * 0.28
            goal_xy = (x + mx * 40.0, y + my * 40.0)
            want_boost = energy > 22.0 and not laser_charging
            state_label = "kite-low"
        elif best_enemy is not None:
            d_en = dist3d(pos, best_enemy["pos"])
            if len(enemies_with_los) >= 2:
                ax = sum(e["pos"][0] for e in enemies_with_los) / len(enemies_with_los)
                ay = sum(e["pos"][1] for e in enemies_with_los) / len(enemies_with_los)
                away_yaw = math.atan2(y - ay, x - ax)
                strafe_ang = away_yaw + self.strafe_dir * 0.55
                goal_xy = (x + math.cos(strafe_ang) * 35.0, y + math.sin(strafe_ang) * 35.0)
                want_boost = energy > 35.0 and not laser_charging
                state_label = "kite-multi"
            else:
                en_yaw = math.atan2(best_enemy["pos"][1] - y, best_enemy["pos"][0] - x)
                opt_range = 30.0 if has_lightning else 55.0
                radial = 0.60 if d_en > opt_range + 12.0 else (-0.65 if d_en < opt_range - 10.0 else 0.0)
                strafe_ang = en_yaw + self.strafe_dir * (math.pi * 0.5)
                mx = math.cos(en_yaw) * radial + math.cos(strafe_ang) * 0.85
                my = math.sin(en_yaw) * radial + math.sin(strafe_ang) * 0.85
                goal_xy = (x + mx * 30.0, y + my * 30.0)
                want_boost = energy > 55.0 and d_en < 45.0 and not laser_charging
                state_label = f"duel-{best_enemy['id']:.0f}"
        elif weapons[1] is None and obs["pickups"]:
            cand = [p for p in obs["pickups"] if p["kind"] in ("lightning", "laser")]
            if cand:
                p = min(cand, key=lambda item: dist3d(pos, item["pos"]))
                if dist3d(pos, p["pos"]) < 100.0:
                    goal_xy = (p["pos"][0], p["pos"][1])
                    want_boost = energy > 45.0
                    state_label = f"loot-{p['kind']}"
        elif npcs and me["cubes"] < 10 and hp_frac > 0.55:
            npc = min(npcs, key=lambda n: dist3d(pos, n["pos"]))
            if dist3d(pos, npc["pos"]) < 95.0:
                goal_xy = (npc["pos"][0], npc["pos"][1])
                state_label = "farm-npc"
        elif obs["crates"] and me["cubes"] < 10:
            cr = min(obs["crates"], key=lambda item: dist3d(pos, item["pos"]))
            if dist3d(pos, cr["pos"]) < 90.0:
                goal_xy = (cr["pos"][0], cr["pos"][1])
                state_label = "farm-crate"

        desired_yaw = math.atan2(goal_xy[1] - y, goal_xy[0] - x)
        dodge_x, dodge_y, dodge_urgent = self._dodge_vector(pos, obs["projectiles"], enemies)
        move_vec, need_jump = self._steer(pos, desired_yaw, zone, (dodge_x, dodge_y))

        jump_cmd = False
        if need_jump or self.stuck_ticks > 4:
            if me["grounded"]:
                jump_cmd = True
            elif energy > 22.0:
                want_boost = True
        if dodge_urgent and energy > 15.0:
            want_boost = True

        act["move"] = move_vec
        act["boost"] = want_boost
        act["jump"] = jump_cmd

        # 6. Precision Aim & 600-DPS Dual-Fire Controller
        fire = [False, False]
        aim_yaw, aim_pitch = me["aim"][0], 0.0
        target_pos: Optional[List[float]] = None
        target_vel = [0.0, 0.0, 0.0]
        target_z_off = 4.5
        target_los = False
        target_hp = 1000.0

        if best_enemy is not None:
            target_pos = best_enemy["pos"]
            target_vel = best_enemy["vel"]
            target_z_off = 4.5
            target_los = best_enemy_los
            target_hp = float(best_enemy.get("hp", 1000.0))
        elif npcs and hp_frac > 0.50 and me["cubes"] < 10:
            npc = min(npcs, key=lambda n: dist3d(pos, n["pos"]))
            if dist3d(pos, npc["pos"]) < 90.0:
                target_pos = npc["pos"]
                target_vel = npc["vel"]
                target_z_off = 1.8
                target_los = self.map.has_los(muzzle, [target_pos[0], target_pos[1], target_pos[2] + 1.8])
                target_hp = float(npc.get("hp", 350.0))
        elif obs["crates"] and hp_frac > 0.50 and me["cubes"] < 10:
            cr = min(obs["crates"], key=lambda c: dist3d(pos, c["pos"]))
            if dist3d(pos, cr["pos"]) < 80.0:
                target_pos = cr["pos"]
                target_z_off = 1.5
                target_los = self.map.has_los(muzzle, [target_pos[0], target_pos[1], target_pos[2] + 1.5])
                target_hp = float(cr.get("hp", 300.0))

        if target_pos is not None:
            d_tgt = dist3d(pos, target_pos)
            primary_slot: Optional[int] = None
            primary_score = -1.0
            for i, w in enumerate(weapons):
                if w is None:
                    continue
                k = w["kind"]
                ws = w["stats"]
                s = -1.0
                if k == "lightning" and target_los and d_tgt <= float(ws.get("range", 45.0)) - 1.0 and energy > 8.0:
                    s = 110.0
                elif k == "gun" and target_los and d_tgt <= float(ws.get("range", 230.0)) - 5.0 and w.get("reload", 0.0) == 0.0:
                    s = 95.0
                elif k == "laser" and target_los and d_tgt <= float(ws.get("range", 280.0)) - 5.0:
                    if (d_tgt > 45.0 or w.get("charge", 0.0) > 0.0) and (w["cooldown"] <= 0.1 or w.get("charge", 0.0) > 0.0) and not dodge_urgent:
                        s = 90.0
                elif k == "mortar" and 18.0 < d_tgt < 225.0 and w["cooldown"] <= 0.1:
                    s = 65.0 if not target_los else 45.0
                if s > primary_score:
                    primary_score = s
                    primary_slot = i

            if primary_slot is not None:
                w = weapons[primary_slot]
                assert w is not None
                k = w["kind"]
                ws = w["stats"]
                if k == "lightning":
                    aim_yaw, aim_pitch = self._lead_aim(muzzle, target_pos, target_vel, 252.0, target_z_off)
                    raw_yaw = math.atan2(target_pos[1] - y, target_pos[0] - x)
                    if abs(angle_diff(me["aim"][0], raw_yaw)) < 0.48:
                        fire[primary_slot] = True
                elif k == "gun":
                    aim_yaw, aim_pitch = self._lead_aim(muzzle, target_pos, target_vel, float(ws.get("speed", 252.0)), target_z_off)
                    if abs(angle_diff(me["aim"][0], aim_yaw)) < clamp(3.0 / max(1.0, d_tgt), 0.03, 0.22):
                        fire[primary_slot] = True
                elif k == "laser":
                    aim_yaw = math.atan2(target_pos[1] - y, target_pos[0] - x)
                    aim_pitch = math.atan2(target_pos[2] + target_z_off - muzzle[2], max(0.1, dist2d((x, y), (target_pos[0], target_pos[1]))))
                    charge = float(w.get("charge", 0.0))
                    max_c = float(ws.get("charge", 0.75))
                    min_c = float(ws.get("min_charge", 0.15))
                    # Distance-scaled hitscan tolerance so we never miss a charged beam
                    hit_tol = clamp(1.9 / max(1.0, d_tgt), 0.015, 0.12)
                    yaw_err = abs(angle_diff(me["aim"][0], aim_yaw))
                    pitch_err = abs(me["aim"][1] - aim_pitch)
                    ready_to_release = (charge >= max_c * 0.85) or (target_hp < 155.0 and charge >= min_c)
                    if ready_to_release and yaw_err < hit_tol and pitch_err < hit_tol * 1.3:
                        fire[primary_slot] = False
                    elif w["cooldown"] <= 0.05 or charge > 0.0:
                        fire[primary_slot] = True
                elif k == "mortar":
                    m_aim = self._mortar_aim(
                        [x, y, z + 9.5], target_pos, target_vel, float(ws.get("speed", 72.0)), float(ws.get("gravity", 22.0)), high_arc=not target_los
                    )
                    if m_aim is not None:
                        aim_yaw, aim_pitch = m_aim
                        if abs(angle_diff(me["aim"][0], aim_yaw)) < 0.10 and abs(me["aim"][1] - aim_pitch) < 0.10:
                            fire[primary_slot] = True

                # Dual-fire secondary slot simultaneously!
                other = 1 - primary_slot
                ow = weapons[other]
                if ow is not None and target_los:
                    ok = ow["kind"]
                    if ok == "gun" and ow.get("reload", 0.0) == 0.0 and d_tgt <= float(ow["stats"].get("range", 230.0)) - 5.0:
                        if abs(angle_diff(me["aim"][0], aim_yaw)) < clamp(3.2 / max(1.0, d_tgt), 0.03, 0.22):
                            fire[other] = True
                    elif ok == "lightning" and energy > 8.0 and d_tgt <= float(ow["stats"].get("range", 45.0)) - 1.0:
                        raw_yaw = math.atan2(target_pos[1] - y, target_pos[0] - x)
                        if abs(angle_diff(me["aim"][0], raw_yaw)) < 0.48:
                            fire[other] = True
            else:
                aim_yaw = math.atan2(target_pos[1] - y, target_pos[0] - x)
        else:
            # Rear-armor protection: face recent attacker or nearest sound
            if t - self.last_damage_t < 2.5 and self.last_damage_bearing is not None:
                aim_yaw = self.last_damage_bearing
            elif obs["sounds"]:
                s = min(obs["sounds"], key=lambda item: (0 if item["dist"] == "near" else 1 if item["dist"] == "mid" else 2, item["age"]))
                aim_yaw = float(s["bearing"])
            else:
                self.scan_yaw = wrap_angle(self.scan_yaw + 0.42)
                aim_yaw = self.scan_yaw
            for w in weapons:
                if w is not None and w["kind"] == "gun" and w.get("reload", 0.0) == 0.0:
                    if w.get("ammo", 12) < w["stats"].get("mag", 12) * 0.65:
                        act["reload"] = True

        act["aim"] = [aim_yaw, clamp(aim_pitch, -1.2, 1.2)]
        act["fire"] = fire

        mf.draw.label(f"{state_label} | hp {me['hp']:.0f} | c {me['cubes']:.0f}")
        return act


mf.run(Bot)