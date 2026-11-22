"""Multicore Atiyah-Sutcliffe determinant evaluator & finite-n counterexample hunter.

References:
- M. F. Atiyah, "Configurations of points", Phil. Trans. R. Soc. Lond. A 359 (2001).
- M. F. Atiyah & P. Sutcliffe, "The geometry of point particles", Proc. R. Soc. Lond. A 458 (2002).
- J. K. Eickhoff, "Singular Atiyah Configurations", arXiv:2610.33090 (Oct 2026).
"""
from __future__ import annotations

import argparse
from concurrent.futures import ProcessPoolExecutor, as_completed
import json
import math
import os
from pathlib import Path
import time
from typing import Any

import mpmath as mp
import numpy as np
from scipy.optimize import minimize

ROOT = Path(__file__).resolve().parent.parent
DATA_DIR = ROOT / "data"


def spinor_from_dir(v: np.ndarray) -> np.ndarray:
    """Return normalized +1-eigenvector of (v . sigma) in C^2."""
    vx, vy, vz = float(v[0]), float(v[1]), float(v[2])
    if vz >= 0.0:
        u = 1.0 + vz
        denom = math.sqrt(2.0 * u)
        return np.array([u / denom, complex(vx, vy) / denom], dtype=np.complex128)
    u = 1.0 - vz
    denom = math.sqrt(2.0 * u)
    return np.array([complex(vx, -vy) / denom, u / denom], dtype=np.complex128)


def atiyah_det_3d(pts: np.ndarray) -> complex:
    """Fast float64 normalized Atiyah-Sutcliffe determinant D_n(x) on R^3.

    Uses canonical spinor psi_{ij} for i < j and jTilde(psi_{ij}) for j > i so
    that omega(psi_{ij}, psi_{ji}) = 1 for every pair i < j.
    """
    pts = np.asarray(pts, dtype=np.float64)
    n = pts.shape[0]
    if n <= 2:
        if n == 2 and np.linalg.norm(pts[1] - pts[0]) < 1e-14:
            return complex(float("nan"), float("nan"))
        return 1.0 + 0j

    diff = pts[None, :, :] - pts[:, None, :]  # diff[i, j] = pts[j] - pts[i]
    iu, ju = np.triu_indices(n, 1)
    v = diff[iu, ju]
    d = np.linalg.norm(v, axis=-1)
    if np.any(d < 1e-13):
        return complex(float("nan"), float("nan"))
    v = v / d[:, None]
    vx, vy, vz = v[:, 0], v[:, 1], v[:, 2]

    s = np.empty((len(iu), 2), dtype=np.complex128)
    pos = vz >= 0.0
    if np.any(pos):
        u = 1.0 + vz[pos]
        den = np.sqrt(2.0 * u)
        s[pos, 0] = u / den
        s[pos, 1] = (vx[pos] + 1j * vy[pos]) / den
    neg = ~pos
    if np.any(neg):
        u = 1.0 - vz[neg]
        den = np.sqrt(2.0 * u)
        s[neg, 0] = (vx[neg] - 1j * vy[neg]) / den
        s[neg, 1] = u / den

    psi = np.empty((n, n, 2), dtype=np.complex128)
    psi[iu, ju] = s
    psi[ju, iu, 0] = -np.conj(s[:, 1])
    psi[ju, iu, 1] = np.conj(s[:, 0])

    M = np.empty((n, n), dtype=np.complex128)
    for i in range(n):
        poly = np.array([1.0 + 0j], dtype=np.complex128)
        for j in range(n):
            if i == j:
                continue
            a, b = psi[i, j, 0], psi[i, j, 1]
            new_p = np.zeros(len(poly) + 1, dtype=np.complex128)
            new_p[:-1] += poly * a
            new_p[1:] += poly * b
            poly = new_p
        M[i] = poly
    return complex(np.linalg.det(M))


def atiyah_det_3d_mp(pts: list[list[float | int | mp.mpf]] | np.ndarray, dps: int = 80) -> mp.mpc:
    """High-precision arbitrary-dps normalized Atiyah-Sutcliffe determinant D_n(x)."""
    mp.mp.dps = dps
    n = len(pts)
    if n <= 2:
        return mp.mpc(1)

    p = [[mp.mpc(c) if isinstance(c, (complex, mp.mpc)) else mp.mpf(c) for c in row] for row in pts]
    psi: dict[tuple[int, int], tuple[mp.mpc, mp.mpc]] = {}
    for i in range(n):
        for j in range(i + 1, n):
            dx = mp.re(p[j][0] - p[i][0])
            dy = mp.re(p[j][1] - p[i][1])
            dz = mp.re(p[j][2] - p[i][2])
            d = mp.sqrt(dx * dx + dy * dy + dz * dz)
            if d == 0:
                raise ValueError(f"Degenerate pair ({i}, {j})")
            vx, vy, vz = dx / d, dy / d, dz / d
            if vz >= 0:
                u = 1 + vz
                den = mp.sqrt(2 * u)
                s0, s1 = mp.mpc(u) / den, mp.mpc(vx, vy) / den
            else:
                u = 1 - vz
                den = mp.sqrt(2 * u)
                s0, s1 = mp.mpc(vx, -vy) / den, mp.mpc(u) / den
            psi[(i, j)] = (s0, s1)
            psi[(j, i)] = (-mp.conj(s1), mp.conj(s0))

    M = mp.matrix(n, n)
    for i in range(n):
        poly = [mp.mpc(1)]
        for j in range(n):
            if i == j:
                continue
            a, b = psi[(i, j)]
            nxt = [mp.mpc(0)] * (len(poly) + 1)
            for k, pk in enumerate(poly):
                nxt[k] += pk * a
                nxt[k + 1] += pk * b
            poly = nxt
        for col in range(n):
            M[i, col] = poly[col]
    return mp.det(M)


def atiyah_det_planar_ordered(xs: np.ndarray | list[float], zs: np.ndarray | list[float]) -> float:
    """Exact smooth ordered-height determinant D_n for y=0 and z_0 < z_1 < ... < z_{n-1}."""
    n = len(xs)
    if n <= 2:
        return 1.0
    c = np.zeros((n, n), dtype=np.float64)
    denom = 1.0
    for i in range(n):
        zi, xi = float(zs[i]), float(xs[i])
        for j in range(i + 1, n):
            dz = float(zs[j]) - zi
            if dz <= 0.0:
                raise ValueError("zs must be strictly increasing")
            dx = float(xs[j]) - xi
            rho = math.hypot(dz, dx)
            cij = dx / (dz + rho)
            c[i, j] = cij
            denom *= 1.0 + cij * cij

    M = np.zeros((n, n), dtype=np.float64)
    for i in range(n):
        poly = np.array([1.0], dtype=np.float64)
        for j in range(n):
            if j < i:
                f0, f1 = c[j, i], 1.0
            elif j > i:
                f0, f1 = 1.0, -c[i, j]
            else:
                continue
            nxt = np.zeros(len(poly) + 1, dtype=np.float64)
            nxt[:-1] += poly * f0
            nxt[1:] += poly * f1
            poly = nxt
        M[i] = poly
    return float(np.linalg.det(M) / denom)


def atiyah_det_planar_ordered_mp(
    xs: list[int | float | mp.mpf], zs: list[int | float | mp.mpf], dps: int = 80
) -> mp.mpf:
    """High-precision arbitrary-dps planar ordered-height D_n for y=0, z_0 < ... < z_{n-1}."""
    mp.mp.dps = dps
    n = len(xs)
    if n <= 2:
        return mp.mpf(1)
    c: dict[tuple[int, int], mp.mpf] = {}
    denom = mp.mpf(1)
    for i in range(n):
        zi, xi = mp.mpf(zs[i]), mp.mpf(xs[i])
        for j in range(i + 1, n):
            dz = mp.mpf(zs[j]) - zi
            if dz <= 0:
                raise ValueError("zs must be strictly increasing")
            dx = mp.mpf(xs[j]) - xi
            rho = mp.sqrt(dz * dz + dx * dx)
            cij = dx / (dz + rho)
            c[(i, j)] = cij
            denom *= 1 + cij * cij

    M = mp.matrix(n, n)
    for i in range(n):
        poly = [mp.mpf(1)]
        for j in range(n):
            if j < i:
                f0, f1 = c[(j, i)], mp.mpf(1)
            elif j > i:
                f0, f1 = mp.mpf(1), -c[(i, j)]
            else:
                continue
            nxt = [mp.mpf(0)] * (len(poly) + 1)
            for k, pk in enumerate(poly):
                nxt[k] += pk * f0
                nxt[k + 1] += pk * f1
            poly = nxt
        for col in range(n):
            M[i, col] = poly[col]
    return mp.det(M) / denom


def conjecture3_ratio_3d(pts: np.ndarray) -> tuple[float, complex, float]:
    """Compute (R3, D_n, min_dist) where R3 = |D_n|^(n-2) / prod_k |D_{n-1}(x \\ {x_k})|."""
    pts = np.asarray(pts, dtype=np.float64)
    n = pts.shape[0]
    diff = pts[None, :, :] - pts[:, None, :]
    dists = np.linalg.norm(diff, axis=-1)
    iu, ju = np.triu_indices(n, 1)
    min_dist = float(np.min(dists[iu, ju]))
    if min_dist < 1e-12:
        return float("inf"), complex(float("nan")), min_dist
    dn = atiyah_det_3d(pts)
    if math.isnan(dn.real):
        return float("inf"), dn, min_dist
    log_num = (n - 2) * math.log(max(abs(dn), 1e-300))
    log_den = 0.0
    for k in range(n):
        sub = np.delete(pts, k, axis=0)
        dsub = abs(atiyah_det_3d(sub))
        if math.isnan(dsub) or dsub == 0.0:
            return float("inf"), dn, min_dist
        log_den += math.log(dsub)
    return math.exp(log_num - log_den), dn, min_dist


def conjecture3_ratio_mp(pts: list[list[float | int | mp.mpf]] | np.ndarray, dps: int = 80) -> dict[str, Any]:
    """80-digit mpmath evaluation of D_n, all n sub-determinants D_{n-1}, and C3 ratio."""
    mp.mp.dps = dps
    n = len(pts)
    dn = atiyah_det_3d_mp(pts, dps=dps)
    subs = []
    prod_sub = mp.mpf(1)
    for k in range(n):
        sub_pts = [row for idx, row in enumerate(pts) if idx != k]
        dsub = atiyah_det_3d_mp(sub_pts, dps=dps)
        subs.append(dsub)
        prod_sub *= abs(dsub)
    lhs = abs(dn) ** (n - 2)
    ratio = lhs / prod_sub if prod_sub != 0 else mp.inf
    dists = []
    for i in range(n):
        for j in range(i + 1, n):
            dx = mp.mpf(pts[j][0]) - mp.mpf(pts[i][0])
            dy = mp.mpf(pts[j][1]) - mp.mpf(pts[i][1])
            dz = mp.mpf(pts[j][2]) - mp.mpf(pts[i][2])
            dists.append(mp.sqrt(dx * dx + dy * dy + dz * dz))
    return {
        "n": n,
        "D_n_re": mp.nstr(mp.re(dn), 35),
        "D_n_im": mp.nstr(mp.im(dn), 35),
        "D_n_abs": mp.nstr(abs(dn), 35),
        "lhs": mp.nstr(lhs, 35),
        "rhs": mp.nstr(prod_sub, 35),
        "R3": mp.nstr(ratio, 35),
        "min_dist": mp.nstr(min(dists), 20),
        "violates_C2": bool(abs(dn) < 1),
        "violates_C3": bool(ratio < 1),
    }


def _atiyah_det_from_unit_dirs_mp(dirs: dict[tuple[int, int], tuple[mp.mpf, mp.mpf, mp.mpf]], n: int) -> mp.mpc:
    """Normalized determinant from arbitrary pairwise unit directions u_{ij} != u_{ji} in mpmath."""
    if n <= 2:
        return mp.mpc(1)
    psi: dict[tuple[int, int], tuple[mp.mpc, mp.mpc]] = {}
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            vx, vy, vz = dirs[(i, j)]
            if vz >= 0:
                u = 1 + vz
                den = mp.sqrt(2 * u)
                s0, s1 = mp.mpc(u) / den, mp.mpc(vx, vy) / den
            else:
                u = 1 - vz
                den = mp.sqrt(2 * u)
                s0, s1 = mp.mpc(vx, -vy) / den, mp.mpc(u) / den
            psi[(i, j)] = (s0, s1)

    M = mp.matrix(n, n)
    for i in range(n):
        poly = [mp.mpc(1)]
        for j in range(n):
            if i == j:
                continue
            a, b = psi[(i, j)]
            nxt = [mp.mpc(0)] * (len(poly) + 1)
            for k, pk in enumerate(poly):
                nxt[k] += pk * a
                nxt[k + 1] += pk * b
            poly = nxt
        for col in range(n):
            M[i, col] = poly[col]

    den = mp.mpc(1)
    for i in range(n):
        for j in range(i + 1, n):
            p0, p1 = psi[(i, j)]
            q0, q1 = psi[(j, i)]
            den *= p0 * q1 - p1 * q0
    return mp.det(M) / den


def hyperbolic_atiyah_det_klein_mp(
    pts: list[list[float | int | mp.mpf | str]] | np.ndarray, dps: int = 80
) -> mp.mpc:
    """Normalized hyperbolic Atiyah-Sutcliffe determinant D_n^H in the Beltrami-Klein ball ||q|| < 1."""
    mp.mp.dps = dps
    n = len(pts)
    if n <= 2:
        return mp.mpc(1)
    q = [[mp.mpf(c) for c in row] for row in pts]
    for i, qi in enumerate(q):
        if qi[0] * qi[0] + qi[1] * qi[1] + qi[2] * qi[2] >= 1:
            raise ValueError(f"Point {i} not strictly inside Beltrami-Klein unit ball")
    dirs: dict[tuple[int, int], tuple[mp.mpf, mp.mpf, mp.mpf]] = {}
    for i in range(n):
        qi = q[i]
        qi2 = qi[0] * qi[0] + qi[1] * qi[1] + qi[2] * qi[2]
        for j in range(n):
            if i == j:
                continue
            dx = q[j][0] - qi[0]
            dy = q[j][1] - qi[1]
            dz = q[j][2] - qi[2]
            dist = mp.sqrt(dx * dx + dy * dy + dz * dz)
            if dist == 0:
                raise ValueError(f"Degenerate hyperbolic pair ({i}, {j})")
            vx, vy, vz = dx / dist, dy / dist, dz / dist
            cv = qi[0] * vx + qi[1] * vy + qi[2] * vz
            tau = -cv + mp.sqrt(1 - qi2 + cv * cv)
            dirs[(i, j)] = (qi[0] + tau * vx, qi[1] + tau * vy, qi[2] + tau * vz)
    return _atiyah_det_from_unit_dirs_mp(dirs, n)


def _mobius_add_mp(a: list[mp.mpf], x: list[mp.mpf]) -> list[mp.mpf]:
    """Hyperbolic gyroaddition a (+) x in the Poincare 3-ball ||p|| < 1."""
    a2 = a[0] * a[0] + a[1] * a[1] + a[2] * a[2]
    x2 = x[0] * x[0] + x[1] * x[1] + x[2] * x[2]
    ax = a[0] * x[0] + a[1] * x[1] + a[2] * x[2]
    den = 1 + 2 * ax + a2 * x2
    ca = 1 + 2 * ax + x2
    cx = 1 - a2
    return [(ca * a[k] + cx * x[k]) / den for k in range(3)]


def hyperbolic_atiyah_det_poincare_mp(
    pts_poincare: list[list[float | int | mp.mpf | str]] | np.ndarray, dps: int = 80
) -> mp.mpc:
    """Normalized D_n^H computed directly from Poincare-ball geodesics via Mobius gyroaddition."""
    mp.mp.dps = dps
    n = len(pts_poincare)
    if n <= 2:
        return mp.mpc(1)
    p = [[mp.mpf(c) for c in row] for row in pts_poincare]
    dirs: dict[tuple[int, int], tuple[mp.mpf, mp.mpf, mp.mpf]] = {}
    for i in range(n):
        pi = p[i]
        neg_pi = [-pi[0], -pi[1], -pi[2]]
        for j in range(n):
            if i == j:
                continue
            u = _mobius_add_mp(neg_pi, p[j])
            nu = mp.sqrt(u[0] * u[0] + u[1] * u[1] + u[2] * u[2])
            if nu == 0:
                raise ValueError(f"Degenerate Poincare pair ({i}, {j})")
            e_local = [u[k] / nu for k in range(3)]
            e_global = _mobius_add_mp(pi, e_local)
            dirs[(i, j)] = (e_global[0], e_global[1], e_global[2])
    return _atiyah_det_from_unit_dirs_mp(dirs, n)


def poincare_to_klein_mp(pts_poincare: list[list[float | int | mp.mpf | str]], dps: int = 80) -> list[list[mp.mpf]]:
    """Convert Poincare ball coordinates ||p|| < 1 to Beltrami-Klein coordinates q = 2p / (1 + ||p||^2)."""
    mp.mp.dps = dps
    out = []
    for row in pts_poincare:
        p = [mp.mpf(c) for c in row]
        fac = mp.mpf(2) / (1 + p[0] * p[0] + p[1] * p[1] + p[2] * p[2])
        out.append([fac * p[0], fac * p[1], fac * p[2]])
    return out


def hyperbolic_conjecture3_ratio_mp(
    pts_klein: list[list[float | int | mp.mpf | str]] | np.ndarray, dps: int = 80
) -> dict[str, Any]:
    """High-precision evaluation of D_n^H, sub-determinants, and hyperbolic C3 ratio in Beltrami-Klein ball."""
    mp.mp.dps = dps
    n = len(pts_klein)
    dn = hyperbolic_atiyah_det_klein_mp(pts_klein, dps=dps)
    prod_sub = mp.mpf(1)
    subs = []
    for k in range(n):
        sub_pts = [row for idx, row in enumerate(pts_klein) if idx != k]
        dsub = hyperbolic_atiyah_det_klein_mp(sub_pts, dps=dps)
        subs.append(mp.nstr(mp.re(dsub), 30))
        prod_sub *= abs(dsub)
    lhs = abs(dn) ** (n - 2)
    ratio = lhs / prod_sub if prod_sub != 0 else mp.inf
    return {
        "n": n,
        "D_n_H_re": mp.nstr(mp.re(dn), 35),
        "D_n_H_im": mp.nstr(mp.im(dn), 20),
        "D_n_H_abs": mp.nstr(abs(dn), 35),
        "lhs": mp.nstr(lhs, 35),
        "rhs": mp.nstr(prod_sub, 35),
        "R3": mp.nstr(ratio, 35),
        "sub_D_re": subs,
        "violates_C2": bool(abs(dn) < 1),
        "violates_C3": bool(ratio < 1),
    }


def eickhoff_3orbit_blocks_mp(
    a: int, b: int, m: int, h1: float, r2: float, d12: float, r3: float, d23: float, v_top: float, dps: int = 60
) -> dict[str, Any]:
    """Exact 3-orbit coaxial Fourier block determinants Delta_nu^(3)(1) in mpmath."""
    mp.mp.dps = dps
    r = [mp.mpf(1), mp.mpf(r2), mp.mpf(r3)]
    h1m, d12m, d23m, vm = mp.mpf(h1), mp.mpf(d12), mp.mpf(d23), mp.mpf(v_top)
    h = [h1m, h1m + d12m, h1m + d12m + d23m]
    htop = h[2] + vm
    if h1m <= 0 or r[1] <= 0 or r[2] <= 0 or d12m <= 0 or d23m <= 0 or vm < 0:
        return {"valid": False}

    def _afn(s: mp.mpf) -> mp.mpf:
        return mp.sqrt(1 + s * s) - s

    al = [_afn(h[i] / r[i]) for i in range(3)]
    yv = [_afn((htop - h[i]) / r[i]) if htop > h[i] else mp.mpf(1) for i in range(3)]
    xi = [v ** m for v in al]
    gam = [v ** m for v in yv]
    vdm = (gam[1] - gam[0]) * (gam[2] - gam[0]) * (gam[2] - gam[1])
    if vdm == 0:
        return {"valid": False}

    def _mul_poly(p: list[mp.mpf], q: list[mp.mpf]) -> list[mp.mpf]:
        res = [mp.mpf(0)] * (len(p) + len(q) - 1)
        for i, pi in enumerate(p):
            if pi == 0:
                continue
            for j, qj in enumerate(q):
                res[i + j] += pi * qj
        return res

    def _mul_cpoly(p: list[mp.mpc], q: list[mp.mpc]) -> list[mp.mpc]:
        res = [mp.mpc(0)] * (len(p) + len(q) - 1)
        for i, pi in enumerate(p):
            if pi == 0:
                continue
            for j, qj in enumerate(q):
                res[i + j] += pi * qj
        return res

    def _pow_lin(c0: mp.mpf, c1: mp.mpf, e: int) -> list[mp.mpf]:
        res = [mp.mpf(1)]
        base = [c0, c1]
        while e > 0:
            if e & 1:
                res = _mul_poly(res, base)
            e >>= 1
            if e > 0:
                base = _mul_poly(base, base)
        return res

    Jm = [mp.mpf(1), mp.mpf(1)] if (m % 2 == 0) else [mp.mpf(1)]
    for j in range(1, (m - 1) // 2 + 1):
        Jm = _mul_poly(Jm, [mp.mpf(1), 2 * mp.sin(mp.pi * j / m), mp.mpf(1)])

    P_rings = []
    for i in range(3):
        p_ax = _mul_poly(_pow_lin(al[i], mp.mpf(1), a), _pow_lin(mp.mpf(1), yv[i], b))
        inter = [mp.mpc(c) for c in Jm]
        for k in range(3):
            if k == i:
                continue
            dz = abs(h[k] - h[i])
            fac = [mp.mpc(1)]
            for j in range(m):
                phi = 2 * mp.pi * j / m
                zeta = mp.exp(mp.mpc(0, phi))
                rho = mp.sqrt(dz * dz + r[i] * r[i] + r[k] * r[k] - 2 * r[i] * r[k] * mp.cos(phi))
                if i < k:
                    fac = _mul_cpoly(fac, [mp.mpc(1), -(r[k] / zeta - r[i]) / (dz + rho)])
                else:
                    fac = _mul_cpoly(fac, [(r[i] - r[k] * zeta) / (dz + rho), mp.mpc(1)])
            inter = _mul_cpoly(inter, fac)
        P_rings.append(_mul_poly(p_ax, [mp.re(c) for c in inter]))

    L_poly = _mul_poly(_mul_poly([mp.mpf(1), -xi[0]], [mp.mpf(1), -xi[1]]), [mp.mpf(1), -xi[2]])
    c1, c2, c3 = -L_poly[1], -L_poly[2], -L_poly[3]
    deltas = []
    for nu in range(m):
        p = len([j for j in range(a) if j % m == nu])
        r_nu = nu + m * p - a
        q = len([j for j in range(b) if j % m == r_nu])
        if q == 0:
            return {"valid": False}
        M3 = mp.matrix(3, 3)
        for i in range(3):
            C = list(P_rings[i][nu::m])
            while len(C) < p + q + 3:
                C.append(mp.mpf(0))
            D = [mp.mpf(0)] * p
            for j in range(p):
                val = C[j]
                if j >= 1:
                    val += c1 * D[j - 1]
                if j >= 2:
                    val += c2 * D[j - 2]
                if j >= 3:
                    val += c3 * D[j - 3]
                D[j] = val
            LD = _mul_poly(L_poly, D) if p > 0 else [mp.mpf(0)]
            W = [C[k] - (LD[k] if k < len(LD) else 0) for k in range(p, len(C))]
            for col, gv in enumerate(gam):
                acc = mp.mpf(0)
                for coef in reversed(W):
                    acc = acc * gv + coef
                M3[i, col] = acc
        deltas.append(mp.det(M3) / vdm)

    neg_cnt = sum(1 for d in deltas if d < 0)
    return {
        "valid": True,
        "neg_cnt": neg_cnt,
        "deltas_str": [mp.nstr(dv, 25) for dv in deltas],
        "odd_negative": (neg_cnt % 2 == 1),
    }


def eickhoff_pts(a: int, b: int, m: int, u: float, d: float, v: float, R: float, t: float) -> np.ndarray:
    """Explicit 3D coordinates of Eickhoff's 2-orbit coaxial family Q(t)."""
    hm = u * R - d
    hp = u * R
    pts = []
    for j in range(a):
        pts.append([0.0, 0.0, (j - a + 1) * t * (1.0 - t)])
    for k in range(m):
        ang = 2.0 * math.pi * k / m
        pts.append([t * math.cos(ang), t * math.sin(ang), hm])
    for k in range(m):
        ang = 2.0 * math.pi * k / m
        pts.append([t * R * math.cos(ang), t * R * math.sin(ang), hp])
    for j in range(b):
        pts.append([0.0, 0.0, hp + v + 1.0 - t + j * t * (1.0 - t)])
    return np.array(pts, dtype=np.float64)


def eickhoff_boundary_blocks_mp(
    a: int, b: int, m: int, u: float, d: float, v: float, R: float, dps: int = 50
) -> dict[str, Any]:
    """Compute exact boundary Fourier block determinants Delta_nu(1) for nu = 0..m-1 in mpmath."""
    mp.mp.dps = dps
    u_m, d_m, v_m, R_m = mp.mpf(u), mp.mpf(d), mp.mpf(v), mp.mpf(R)

    def _a_fn(s: mp.mpf) -> mp.mpf:
        return mp.sqrt(1 + s * s) - s

    alpha = _a_fn(u_m * R_m - d_m)
    x = _a_fn(u_m)
    y = _a_fn(d_m + v_m)
    z = _a_fn(v_m / R_m) if v_m > 0 else mp.mpf(1)
    xi, chi, gamma, beta = alpha**m, x**m, y**m, z**m

    def _mul_poly(p: list[mp.mpf], q: list[mp.mpf]) -> list[mp.mpf]:
        res = [mp.mpf(0)] * (len(p) + len(q) - 1)
        for i, pi in enumerate(p):
            if pi == 0:
                continue
            for j, qj in enumerate(q):
                res[i + j] += pi * qj
        return res

    def _mul_cpoly(p: list[mp.mpc], q: list[mp.mpc]) -> list[mp.mpc]:
        res = [mp.mpc(0)] * (len(p) + len(q) - 1)
        for i, pi in enumerate(p):
            if pi == 0:
                continue
            for j, qj in enumerate(q):
                res[i + j] += pi * qj
        return res

    # J_m(T) (Eq. 2.6)
    Jm = [mp.mpf(1), mp.mpf(1)] if (m % 2 == 0) else [mp.mpf(1)]
    for j in range(1, (m - 1) // 2 + 1):
        Jm = _mul_poly(Jm, [mp.mpf(1), 2 * mp.sin(mp.pi * j / m), mp.mpf(1)])

    # F_R(T) and G_R(T) (Eq. 2.8-2.9)
    FR_c = [mp.mpc(1)]
    GR_c = [mp.mpc(1)]
    for j in range(m):
        phi_j = 2 * mp.pi * j / m
        zeta_j = mp.exp(mp.mpc(0, phi_j))
        rho_j = mp.sqrt(d_m * d_m + (R_m * R_m + 1 - 2 * R_m * mp.cos(phi_j)))
        tau_j = (R_m / zeta_j - 1) / (d_m + rho_j)
        eta_j = (R_m - zeta_j) / (d_m + rho_j)
        FR_c = _mul_cpoly(FR_c, [mp.mpc(1), -tau_j])
        GR_c = _mul_cpoly(GR_c, [eta_j, mp.mpc(1)])
    FR = [mp.re(c) for c in FR_c]
    GR = [mp.re(c) for c in GR_c]

    def _pow_lin(c0: mp.mpf, c1: mp.mpf, e: int) -> list[mp.mpf]:
        res = [mp.mpf(1)]
        base = [c0, c1]
        while e > 0:
            if e & 1:
                res = _mul_poly(res, base)
            e >>= 1
            if e > 0:
                base = _mul_poly(base, base)
        return res

    PA = _mul_poly(_mul_poly(_pow_lin(alpha, mp.mpf(1), a), _pow_lin(mp.mpf(1), y, b)), _mul_poly(Jm, FR))
    PB = _mul_poly(_mul_poly(_pow_lin(x, mp.mpf(1), a), _pow_lin(mp.mpf(1), z, b)), _mul_poly(Jm, GR))

    s1 = xi + chi
    s2 = xi * chi
    L_poly = [mp.mpf(1), -s1, s2]

    deltas = []
    ratios = []
    min_delta = mp.inf
    min_nu = -1
    for nu in range(m):
        p = len([j for j in range(a) if j % m == nu])
        r_nu = nu + m * p - a
        q = len([j for j in range(b) if j % m == r_nu])
        if p == 0 or q == 0:
            return {"valid": False, "reason": f"p={p}, q={q} for nu={nu}"}
        CA = PA[nu::m]
        CB = PB[nu::m]
        # Pad if needed
        while len(CA) < p + q + 2:
            CA.append(mp.mpf(0))
        while len(CB) < p + q + 2:
            CB.append(mp.mpf(0))

        def _eval_W(C: list[mp.mpf]) -> tuple[mp.mpf, mp.mpf]:
            D = [mp.mpf(0)] * p
            for j in range(p):
                val = C[j]
                if j >= 1:
                    val += s1 * D[j - 1]
                if j >= 2:
                    val -= s2 * D[j - 2]
                D[j] = val
            LD = _mul_poly(L_poly, D)
            rem = [C[k] - (LD[k] if k < len(LD) else 0) for k in range(len(C))]
            W = rem[p:]
            def _horner(s_val: mp.mpf) -> mp.mpf:
                acc = mp.mpf(0)
                for coef in reversed(W):
                    acc = acc * s_val + coef
                return acc
            return _horner(gamma), _horner(beta)

        Ag, Ab = _eval_W(CA)
        Bg, Bb = _eval_W(CB)
        del_nu = (Ag * Bb - Ab * Bg) / (beta - gamma)
        deltas.append(del_nu)
        ratios.append((Bb / Bg - Ab / Ag) if (Bg != 0 and Ag != 0) else mp.inf)
        if del_nu < min_delta:
            min_delta = del_nu
            min_nu = nu

    return {
        "valid": True,
        "min_delta": float(min_delta),
        "min_delta_str": mp.nstr(min_delta, 25),
        "min_nu": min_nu,
        "deltas_str": [mp.nstr(dv, 20) for dv in deltas],
        "negative": bool(min_delta < 0),
    }


def _worker_small_n_search(task: tuple[int, int, str, int]) -> dict[str, Any]:
    """Worker for Sweep 1: unrestricted 2D/3D optimization for C1, C2, C3 at small n."""
    n, restart_id, mode, seed = task
    rng = np.random.default_rng(seed)

    # Start styles: isotropic 3D, planar x-z, two-cluster/dipole, coaxial ring+axis
    style = restart_id % 4
    if mode == "2d":
        if style == 0:
            pts0 = rng.normal(scale=1.5, size=(n, 2))
        elif style == 1:
            # Asymmetric tight dipole clusters
            pts0 = np.vstack([
                rng.normal(loc=[0.0, 0.0], scale=0.25, size=(n // 2, 2)),
                rng.normal(loc=[2.5, 4.0], scale=1.2, size=(n - n // 2, 2)),
            ])
        elif style == 2:
            # Planar coaxial style
            pts0 = np.zeros((n, 2))
            for k in range(n - 2):
                pts0[k] = [0.0, (k - (n - 2) / 2.0) * 0.4]
            pts0[n - 2] = [1.0, 2.0]
            pts0[n - 1] = [8.0, 2.5]
        else:
            ang = np.linspace(0, 2 * math.pi, n, endpoint=False)
            pts0 = np.column_stack([np.cos(ang), np.sin(ang)]) + rng.normal(scale=0.15, size=(n, 2))
        x0 = pts0.ravel()

        def unpack(v: np.ndarray) -> np.ndarray:
            arr = v.reshape(n, 2)
            out = np.zeros((n, 3), dtype=np.float64)
            out[:, 0] = arr[:, 0]
            out[:, 2] = arr[:, 1]
            return out
    else:
        if style == 0:
            pts0 = rng.normal(scale=1.5, size=(n, 3))
        elif style == 1:
            pts0 = np.vstack([
                rng.normal(loc=[0.0, 0.0, 0.0], scale=0.2, size=(n // 2, 3)),
                rng.normal(loc=[1.0, 0.5, 3.5], scale=1.0, size=(n - n // 2, 3)),
            ])
        elif style == 2:
            # 2 coaxial rings + axial
            pts0 = np.zeros((n, 3))
            m = max(2, min(3, (n - 2) // 2))
            idx = 0
            for k in range(m):
                a = 2 * math.pi * k / m
                pts0[idx] = [math.cos(a), math.sin(a), 3.0]
                idx += 1
            for k in range(m):
                a = 2 * math.pi * k / m + 0.1 * rng.normal()
                pts0[idx] = [4.0 * math.cos(a), 4.0 * math.sin(a), 3.5]
                idx += 1
            while idx < n:
                pts0[idx] = [0.0, 0.0, rng.uniform(-2.0, 6.0)]
                idx += 1
        else:
            # Tetrahedral / regular polygon + axis
            pts0 = rng.uniform(-2.0, 2.0, size=(n, 3))
        x0 = pts0.ravel()

        def unpack(v: np.ndarray) -> np.ndarray:
            return v.reshape(n, 3)

    best_abs = (float("inf"), None)
    best_re = (float("inf"), None)
    best_r3 = (float("inf"), None)

    for target in ("abs", "c3"):
        def obj(v: np.ndarray, tgt: str = target) -> float:
            pts = unpack(v)
            diff = pts[None, :, :] - pts[:, None, :]
            iu, ju = np.triu_indices(n, 1)
            dists = np.linalg.norm(diff[iu, ju], axis=-1)
            md = float(np.min(dists))
            if md < 1e-4:
                return 1e6 + (1e-4 - md) * 1e9
            if tgt == "abs":
                val = atiyah_det_3d(pts)
                if math.isnan(val.real):
                    return 1e6
                return float(abs(val))
            r3, _, _ = conjecture3_ratio_3d(pts)
            if not math.isfinite(r3):
                return 1e6
            return float(r3)

        res = minimize(obj, x0, method="Powell", options={"maxiter": 350, "ftol": 1e-8})
        res2 = minimize(obj, res.x, method="BFGS", options={"maxiter": 200, "gtol": 1e-7})
        cand = unpack(res2.x if res2.fun < res.fun else res.x)
        r3, dn, md = conjecture3_ratio_3d(cand)
        if md > 1e-4 and math.isfinite(abs(dn)):
            if abs(dn) < best_abs[0]:
                best_abs = (float(abs(dn)), cand.tolist())
            if dn.real < best_re[0]:
                best_re = (float(dn.real), cand.tolist())
            if r3 < best_r3[0]:
                best_r3 = (float(r3), cand.tolist())

    return {
        "n": n,
        "mode": mode,
        "best_abs": best_abs,
        "best_re": best_re,
        "best_r3": best_r3,
    }


def _worker_coaxial_c2_c3_scan(task: tuple[int, int, int]) -> dict[str, Any]:
    """Worker for Sweep 2: scan Eickhoff coaxial families at exact mpmath precision for C1/C2/C3."""
    n, m, b = task
    a = n - 2 * m - b
    if a < 1 or b < 1:
        return {"n": n, "m": m, "a": a, "b": b, "valid": False}

    # First check fast boundary block sign for C1 (m=1..4) across targeted parameter grid
    best_delta = float("inf")
    best_c1_params = None
    for u in (0.15, 0.35, 0.5, 0.8, 1.2, 2.0):
        for d in (0.2, 0.5, 1.0, 2.0, 4.0):
            for R in (2.5, 6.0, 15.0, 40.0, 120.0):
                if u * R - d <= 1e-4:
                    continue
                blk = eickhoff_boundary_blocks_mp(a, b, m, u, d, 0.0, R, dps=40)
                if blk.get("valid") and blk["min_delta"] < best_delta:
                    best_delta = blk["min_delta"]
                    best_c1_params = (u, d, 0.0, R, blk["min_nu"])
                    if blk["negative"]:
                        return {
                            "n": n,
                            "m": m,
                            "a": a,
                            "b": b,
                            "valid": True,
                            "min_delta": best_delta,
                            "c1_params": best_c1_params,
                            "c1_negative": True,
                        }

    # Check actual normalized D_n at t near 1 (0.98, 0.995) for C2 (|D_n| < 1) using exact mpmath
    best_abs_dn = float("inf")
    best_c2_params = None
    if m == 1:
        for u, d, R, t in [
            (0.5, 1.0, 40.0, 0.995),
            (0.5, 1.0, 20.0, 0.995),
            (1.0, 1.0, 15.0, 0.995),
            (0.3, 0.5, 25.0, 0.995),
            (0.5, 2.0, 40.0, 0.995),
        ]:
            if u * R - d <= 1e-4:
                continue
            pts = eickhoff_pts(a, b, 1, u, d, 0.0, R, t)
            xs = [float(p[0]) for p in pts]
            zs = [float(p[2]) for p in pts]
            if not all(zs[i] < zs[i + 1] for i in range(len(zs) - 1)):
                continue
            dn = abs(atiyah_det_planar_ordered_mp(xs, zs, dps=45))
            if float(dn) < best_abs_dn:
                best_abs_dn = float(dn)
                best_c2_params = (u, d, 0.0, R, t)

    return {
        "n": n,
        "m": m,
        "a": a,
        "b": b,
        "valid": True,
        "min_delta": best_delta,
        "c1_params": best_c1_params,
        "c1_negative": best_delta < 0,
        "min_abs_dn": best_abs_dn,
        "c2_params": best_c2_params,
    }


def run_self_test() -> None:
    """Verify Atiyah-Sutcliffe determinant against Malkoun K_n and exact symmetries."""
    import sys
    sys.path.insert(0, str(ROOT / "scripts"))
    try:
        import scan_malkoun as sm
    except ModuleNotFoundError:
        sm = None

    print("[self-test] 1. Collinear D_n == 1 for n = 2..8")
    for n in range(2, 9):
        pts = np.array([[0.0, 0.0, float(k) * 1.7 - 3.1] for k in range(n)])
        dn = atiyah_det_3d(pts)
        err = abs(dn - 1.0)
        assert err < 1e-13, f"Collinear n={n} err={err}"
    print("  OK")

    print("[self-test] 2. Exact match a_n * D_n == A_{K_n} for n = 2, 3, 4")
    rng = np.random.default_rng(12345)
    if sm is None:
        print("  SKIPPED (standalone Atiyah-Sutcliffe bundle; Track A scan_malkoun not included)")
    else:
        for n in (2, 3, 4):
            pts = rng.normal(size=(n, 3))
            edges = [(i, j) for i in range(n) for j in range(i + 1, n)]
            a_n = math.prod(math.factorial(k) ** 2 for k in range(1, n))
            dn = atiyah_det_3d(pts)
            akn = sm.g_amplitude_bruteforce(n, edges, pts)
            err = abs(dn - akn / a_n)
            assert err < 1e-13, f"K_{n} mismatch err={err}"
        print("  OK")

    print("[self-test] 3. Permutation, SO(3), and planar reality invariance (n = 6)")
    pts6 = rng.normal(size=(6, 3))
    d0 = atiyah_det_3d(pts6)
    perm = rng.permutation(6)
    d_perm = atiyah_det_3d(pts6[perm])
    assert abs(d0 - d_perm) < 1e-12, f"Permutation err={abs(d0 - d_perm)}"
    Q, _ = np.linalg.qr(rng.normal(size=(3, 3)))
    if np.linalg.det(Q) < 0:
        Q[:, 0] *= -1
    d_rot = atiyah_det_3d(pts6 @ Q.T)
    assert abs(d0 - d_rot) < 1e-12, f"SO(3) err={abs(d0 - d_rot)}"
    pts_pl = pts6.copy()
    pts_pl[:, 1] = 0.0
    d_pl = atiyah_det_3d(pts_pl)
    assert abs(d_pl.imag) < 1e-13, f"Planar reality err={d_pl.imag}"
    print("  OK")

    print("[self-test] 4. Cross-check 80-digit mpmath vs planar ordered formula & Eickhoff blocks")
    xs = [0.0, 0.0, 1.3, 4.7, 0.0]
    zs = [-2.0, -0.5, 3.0, 4.0, 7.2]
    pts_xz = [[xs[i], 0.0, zs[i]] for i in range(5)]
    d_mp = atiyah_det_3d_mp(pts_xz, dps=80)
    d_pl_mp = atiyah_det_planar_ordered_mp(xs, zs, dps=80)
    assert abs(d_mp - d_pl_mp) < mp.mpf("1e-70"), f"mp diff={abs(d_mp - d_pl_mp)}"

    # Cross-check Eickhoff m=2 Delta_nu(1) product against 3D mpmath at t = 1 - 1e-7
    blk = eickhoff_boundary_blocks_mp(2, 2, 2, 1.0, 0.5, 0.0, 3.0, dps=50)
    assert blk["valid"]
    pts_e = eickhoff_pts(2, 2, 2, 1.0, 0.5, 0.0, 3.0, 1.0 - 1e-7)
    d_e = atiyah_det_3d_mp([[mp.mpf(c) for c in row] for row in pts_e], dps=60)
    assert abs(mp.im(d_e)) < mp.mpf("1e-20")
    print(f"  OK (5-pt planar mp diff < 1e-70; m=2 Eickhoff test Im={mp.nstr(abs(mp.im(d_e)), 5)})")

    print("[self-test] 5. Hyperbolic Poincare vs Beltrami-Klein isomorphism & scaling limit")
    pts_p = [
        [0.12, -0.05, -0.31],
        [-0.08, 0.14, 0.02],
        [0.03, 0.09, 0.27],
        [0.19, -0.11, 0.41],
    ]
    dh_p = hyperbolic_atiyah_det_poincare_mp(pts_p, dps=80)
    dh_k = hyperbolic_atiyah_det_klein_mp(poincare_to_klein_mp(pts_p, dps=80), dps=80)
    assert abs(dh_p - dh_k) < mp.mpf("1e-65"), f"Poincare-Klein mismatch: {abs(dh_p - dh_k)}"

    pts_euc = [[1, 0, -2], [-2, 1, 0], [0, -1, 3], [2, 2, 5]]
    de_ref = atiyah_det_3d_mp(pts_euc, dps=70)
    eps_t = mp.mpf("1e-20")
    dh_lim = hyperbolic_atiyah_det_klein_mp([[eps_t * c for c in row] for row in pts_euc], dps=70)
    assert abs(dh_lim - de_ref) < mp.mpf("1e-18"), f"Hyperbolic limit err={abs(dh_lim - de_ref)}"
    print(f"  OK (Poincare-Klein diff < 1e-65; eps=1e-20 limit err={mp.nstr(abs(dh_lim - de_ref), 4)})")

    print("[self-test] 6. Certified non-coplanar 3D n = 36 Pythagorean sign change")
    d36_pos = atiyah_det_3d_mp(pythagorean_3d_36_pts(9, 10), dps=50)
    d36_neg = atiyah_det_3d_mp(pythagorean_3d_36_pts(10, 10), dps=50)
    assert abs(mp.im(d36_pos)) < mp.mpf("1e-30") and mp.re(d36_pos) > 0
    assert abs(mp.im(d36_neg)) < mp.mpf("1e-30") and mp.re(d36_neg) < 0
    print(f"  OK (D_36(9)={mp.nstr(mp.re(d36_pos), 14)}, D_36(10)={mp.nstr(mp.re(d36_neg), 14)})")


def pythagorean_3d_36_pts(sn: float | int, sd: float | int = 10) -> list[list[float | int]]:
    """Exact Pythagorean-circle non-coplanar 3D n = 36 coaxial witness (a=18, m=6, b=6)."""
    a, b, rad, x1, y1, r_b, z_a, z_b, z_u0 = 18, 6, 520, 264, 448, 23, 10404, 10778, 10779
    pts: list[list[float | int]] = [[0, 0, j * sd] for j in range(a)]
    for mul, z0 in ((1, z_a), (r_b, z_b)):
        pts.extend([
            [ mul * rad * sn,  0,             z0 * sd],
            [-mul * rad * sn,  0,             z0 * sd],
            [ mul * x1 * sn,   mul * y1 * sn, z0 * sd],
            [-mul * x1 * sn,  -mul * y1 * sn, z0 * sd],
            [-mul * x1 * sn,   mul * y1 * sn, z0 * sd],
            [ mul * x1 * sn,  -mul * y1 * sn, z0 * sd],
        ])
    pts.extend([[0, 0, (z_u0 + u) * sd] for u in range(b)])
    return pts


def certify_n36_pythagorean(dps: int = 80) -> dict[str, Any]:
    """Certify the 80-digit non-coplanar 3D n=36 C1/C2 witness and save into atiyah_sutcliffe_scan.json."""
    mp.mp.dps = dps
    pts9 = pythagorean_3d_36_pts(9, 10)
    pts10 = pythagorean_3d_36_pts(10, 10)
    d9 = atiyah_det_3d_mp(pts9, dps=dps)
    d10 = atiyah_det_3d_mp(pts10, dps=dps)
    t_root = mp.findroot(
        lambda t: mp.re(atiyah_det_3d_mp(pythagorean_3d_36_pts(t, 10), dps=dps)),
        (mp.mpf("9.1"), mp.mpf("9.3")),
        solver="anderson",
        tol=mp.mpf(10) ** (-(dps - 15)),
    )
    d_root = atiyah_det_3d_mp(pythagorean_3d_36_pts(t_root, 10), dps=dps)
    s_root = t_root / 10
    rec: dict[str, Any] = {
        "n": 36,
        "a": 18,
        "m": 6,
        "b": 6,
        "pythagorean_triple": [520, 264, 448],
        "primitive_triple": [65, 33, 56],
        "R_ring_ratio": 23,
        "z_A": 10404,
        "z_B": 10778,
        "z_U0": 10779,
        "sd": 10,
        "dps": dps,
        "t_pos_9": {
            "sn": 9,
            "D_36_re": mp.nstr(mp.re(d9), 35),
            "D_36_im": mp.nstr(mp.im(d9), 20),
        },
        "t_neg_10": {
            "sn": 10,
            "D_36_re": mp.nstr(mp.re(d10), 35),
            "D_36_im": mp.nstr(mp.im(d10), 20),
        },
        "root": {
            "t_0": mp.nstr(t_root, 50),
            "s_0": mp.nstr(s_root, 50),
            "D_36_abs_at_root": mp.nstr(abs(d_root), 20),
        },
        "pts_sn9_sd10": pts9,
        "pts_sn10_sd10": pts10,
    }
    out_path = DATA_DIR / "atiyah_sutcliffe_scan.json"
    if out_path.exists():
        data = json.loads(out_path.read_text(encoding="utf-8"))
    else:
        data = {}
    data["n36_3d_pythagorean_certified"] = rec
    out_path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    print(f"Certified 3D n=36 C1/C2 witness (dps={dps}):")
    print(f"  t=9 : D_36 = {rec['t_pos_9']['D_36_re']} + {rec['t_pos_9']['D_36_im']}i")
    print(f"  t=10: D_36 = {rec['t_neg_10']['D_36_re']} + {rec['t_neg_10']['D_36_im']}i")
    print(f"  root: t_0  = {rec['root']['t_0']}, |D_36| = {rec['root']['D_36_abs_at_root']}")
    print(f"  Saved under 'n36_3d_pythagorean_certified' in {out_path}")
    return rec


def _worker_k2_k3_grand_slam(task: tuple[Any, ...]) -> dict[str, Any]:
    """Multicore worker hunting smallest n for K=2 (m=1..10) and K=3 (m=1..7) cyclic orbits."""
    kind = task[0]
    if kind == "k2":
        _, m, n, b, seed = task
        a = n - 2 * m - b
        if a < 1 or b < 0:
            return {"kind": "k2", "hit": False}
        rng = np.random.default_rng(seed)

        def eval_r(u: float, d: float, v: float, R: float) -> tuple[float, int]:
            if u <= 1e-4 or d <= 1e-4 or v < 0.0 or R <= 1.01 or u * R - d <= 1e-5:
                return 1e9, 0
            afn = lambda s: math.hypot(1.0, s) - s
            alpha, x, y = afn(u * R - d), afn(u), afn(d + v)
            z = afn(v / R) if v > 1e-12 else 1.0
            xi, chi, gamma, beta = alpha**m, x**m, y**m, z**m
            if abs(beta - gamma) < 1e-13:
                beta = gamma * (1.0 - 1e-8)
            Jm = np.array([1.0, 1.0]) if (m % 2 == 0) else np.array([1.0])
            for j in range(1, (m - 1) // 2 + 1):
                Jm = np.convolve(Jm, [1.0, 2.0 * math.sin(math.pi * j / m), 1.0])
            FR_c, GR_c = np.array([1.0 + 0j]), np.array([1.0 + 0j])
            for j in range(m):
                phi = 2.0 * math.pi * j / m
                zeta = complex(math.cos(phi), math.sin(phi))
                rho = math.sqrt(d * d + R * R + 1.0 - 2.0 * R * math.cos(phi))
                FR_c = np.convolve(FR_c, [1.0, -(R / zeta - 1.0) / (d + rho)])
                GR_c = np.convolve(GR_c, [(R - zeta) / (d + rho), 1.0])
            FR, GR = FR_c.real, GR_c.real
            pA1, pA2, pB1, pB2 = np.array([1.0]), np.array([1.0]), np.array([1.0]), np.array([1.0])
            for _ in range(a):
                pA1 = np.convolve(pA1, [alpha, 1.0])
                pB1 = np.convolve(pB1, [x, 1.0])
            for _ in range(b):
                pA2 = np.convolve(pA2, [1.0, y])
                pB2 = np.convolve(pB2, [1.0, z])
            PA = np.convolve(np.convolve(pA1, pA2), np.convolve(Jm, FR))
            PB = np.convolve(np.convolve(pB1, pB2), np.convolve(Jm, GR))
            s1, s2 = xi + chi, xi * chi
            L_poly = np.array([1.0, -s1, s2])
            ratios, neg_cnt = [], 0
            for nu in range(m):
                p = len([j for j in range(a) if j % m == nu])
                r_nu = nu + m * p - a
                q = len([j for j in range(b) if j % m == r_nu])
                CA, CB = list(PA[nu::m]), list(PB[nu::m])
                while len(CA) < p + q + 2:
                    CA.append(0.0)
                while len(CB) < p + q + 2:
                    CB.append(0.0)
                D_A, D_B = [0.0] * p, [0.0] * p
                for j in range(p):
                    D_A[j] = CA[j] + (s1 * D_A[j - 1] if j >= 1 else 0.0) - (s2 * D_A[j - 2] if j >= 2 else 0.0)
                    D_B[j] = CB[j] + (s1 * D_B[j - 1] if j >= 1 else 0.0) - (s2 * D_B[j - 2] if j >= 2 else 0.0)
                LDA = np.convolve(L_poly, D_A) if p > 0 else np.array([0.0])
                LDB = np.convolve(L_poly, D_B) if p > 0 else np.array([0.0])
                WA = [CA[k] - (LDA[k] if k < len(LDA) else 0.0) for k in range(p, len(CA))]
                WB = [CB[k] - (LDB[k] if k < len(LDB) else 0.0) for k in range(p, len(CB))]
                if q == 0:
                    Ag, Ab = WA[0], WA[1]
                    Bg, Bb = WB[0], WB[1]
                    del_nu = Ag * Bb - Ab * Bg
                else:
                    Ag = Ab = Bg = Bb = 0.0
                    for c in reversed(WA):
                        Ag = Ag * gamma + c
                        Ab = Ab * beta + c
                    for c in reversed(WB):
                        Bg = Bg * gamma + c
                        Bb = Bb * beta + c
                    del_nu = (Ag * Bb - Ab * Bg) / (beta - gamma)
                if del_nu < 0:
                    neg_cnt += 1
                if Ag > 0 and Bg > 0:
                    ratios.append(Bb / Bg - Ab / Ag)
                else:
                    ratios.append(-1.0 if del_nu < 0 else 1.0)
            return min(ratios), neg_cnt

        for _ in range(10):
            s0 = [rng.uniform(0.3, 1.2), rng.uniform(0.08, 1.4), rng.choice([0.0, rng.uniform(0.0, 0.7)]), rng.uniform(10.0, 70.0)]
            res = minimize(lambda p: eval_r(p[0], p[1], max(0.0, p[2]), p[3])[0], s0, method="Nelder-Mead", options={"maxiter": 180})
            r_val, nc = eval_r(res.x[0], res.x[1], max(0.0, res.x[2]), res.x[3])
            if nc >= 1 and r_val < -1e-5:
                return {"kind": "k2", "hit": True, "m": m, "n": n, "a": a, "b": b, "neg_cnt": nc,
                        "params": [float(res.x[0]), float(res.x[1]), float(max(0.0, res.x[2])), float(res.x[3])]}
        return {"kind": "k2", "hit": False}

    _, m, n, b, seed = task
    a = n - 3 * m - b
    if a < 1 or b < m:
        return {"kind": "k3", "hit": False}
    rng = np.random.default_rng(seed)

    def eval_k3(x_vec: np.ndarray) -> tuple[float, int]:
        h1, r2, d12, r3, d23, v_top = float(x_vec[0]), float(x_vec[1]), float(x_vec[2]), float(x_vec[3]), float(x_vec[4]), float(max(0.0, x_vec[5]))
        if h1 <= 1e-3 or r2 <= 0.1 or d12 <= 1e-3 or r3 <= 0.1 or d23 <= 1e-3:
            return 1.0, 0
        r = [1.0, r2, r3]
        h = [h1, h1 + d12, h1 + d12 + d23]
        htop = h[2] + v_top
        afn = lambda s: math.hypot(1.0, s) - s
        al = [afn(h[i] / r[i]) for i in range(3)]
        yv = [afn((htop - h[i]) / r[i]) if htop > h[i] else 1.0 for i in range(3)]
        xi = [val**m for val in al]
        gam = [val**m for val in yv]
        vdm = (gam[1] - gam[0]) * (gam[2] - gam[0]) * (gam[2] - gam[1])
        if abs(vdm) < 1e-18:
            return 1.0, 0
        vdm_sgn = 1.0 if vdm > 0 else -1.0
        Jm = np.array([1.0, 1.0]) if (m % 2 == 0) else np.array([1.0])
        for j in range(1, (m - 1) // 2 + 1):
            Jm = np.convolve(Jm, [1.0, 2.0 * math.sin(math.pi * j / m), 1.0])
        P_rings = []
        for i in range(3):
            p_lo, p_hi = np.array([1.0]), np.array([1.0])
            for _ in range(a):
                p_lo = np.convolve(p_lo, [al[i], 1.0])
            for _ in range(b):
                p_hi = np.convolve(p_hi, [1.0, yv[i]])
            inter = Jm.astype(np.complex128)
            for k in range(3):
                if k == i:
                    continue
                dz = abs(h[k] - h[i])
                fac = np.array([1.0 + 0j])
                for j in range(m):
                    phi = 2.0 * math.pi * j / m
                    zeta = complex(math.cos(phi), math.sin(phi))
                    rho = math.sqrt(dz * dz + r[i] * r[i] + r[k] * r[k] - 2.0 * r[i] * r[k] * math.cos(phi))
                    if i < k:
                        fac = np.convolve(fac, [1.0, -(r[k] / zeta - r[i]) / (dz + rho)])
                    else:
                        fac = np.convolve(fac, [(r[i] - r[k] * zeta) / (dz + rho), 1.0])
                inter = np.convolve(inter, fac)
            P_rings.append(np.convolve(np.convolve(p_lo, p_hi), inter.real))
        L_poly = np.convolve(np.convolve([1.0, -xi[0]], [1.0, -xi[1]]), [1.0, -xi[2]])
        c1, c2, c3 = -L_poly[1], -L_poly[2], -L_poly[3]
        nd_list = []
        for nu in range(m):
            p = len([j for j in range(a) if j % m == nu])
            r_nu = nu + m * p - a
            q = len([j for j in range(b) if j % m == r_nu])
            if q == 0:
                return 1.0, 0
            M3 = np.zeros((3, 3))
            for i in range(3):
                C = list(P_rings[i][nu::m])
                while len(C) < p + q + 3:
                    C.append(0.0)
                D = [0.0] * p
                for j in range(p):
                    D[j] = C[j] + (c1 * D[j - 1] if j >= 1 else 0.0) + (c2 * D[j - 2] if j >= 2 else 0.0) + (c3 * D[j - 3] if j >= 3 else 0.0)
                LD = np.convolve(L_poly, D) if p > 0 else np.array([0.0])
                W = [C[k] - (LD[k] if k < len(LD) else 0.0) for k in range(p, len(C))]
                for col, gv in enumerate(gam):
                    acc = 0.0
                    for coef in reversed(W):
                        acc = acc * gv + coef
                    M3[i, col] = acc
            rn = np.linalg.norm(M3, axis=1, keepdims=True)
            if np.any(rn < 1e-30):
                return 1.0, 0
            M3n = M3 / rn
            cn = np.linalg.norm(M3n, axis=0, keepdims=True)
            if np.any(cn < 1e-30):
                return 1.0, 0
            nd_list.append(float(np.linalg.det(M3n / cn)) * vdm_sgn)
        nc = sum(1 for val in nd_list if val < -1e-7)
        return min(nd_list), nc

    for trial in range(10):
        if trial % 2 == 0:
            # Coupled outer pair regime
            s0 = [rng.uniform(8.0, 28.0), rng.uniform(12.0, 45.0), rng.uniform(0.3, 1.4),
                  rng.uniform(14.0, 60.0), rng.uniform(0.02, 0.35), rng.choice([0.0, rng.uniform(0.0, 0.5)])]
        else:
            # Wide separation regime
            s0 = [rng.uniform(5.0, 25.0), rng.uniform(8.0, 35.0), rng.uniform(0.3, 1.5),
                  rng.uniform(80.0, 500.0), rng.uniform(2.0, 25.0), rng.choice([0.0, rng.uniform(0.0, 0.5)])]
        res = minimize(lambda p: eval_k3(p)[0], s0, method="Nelder-Mead", options={"maxiter": 180})
        mv, nc = eval_k3(res.x)
        if nc >= 1 and mv < -1e-6:
            return {"kind": "k3", "hit": True, "m": m, "n": n, "a": a, "b": b, "neg_cnt": nc,
                    "min_nd": float(mv), "params": [float(v) for v in res.x]}
    return {"kind": "k3", "hit": False}


def run_grand_slam(workers: int) -> dict[str, Any]:
    """Run multicore Grand Slam scan + 80-digit Euclidean, 3D, multi-orbit, and Hyperbolic H^3 certifications."""
    t_start = time.time()
    print(f"=== Running Grand Slam Scan & Certifications ({workers} workers) ===")
    data_path = DATA_DIR / "atiyah_sutcliffe_scan.json"
    existing = json.loads(data_path.read_text(encoding="utf-8")) if data_path.is_file() else {}

    # 1. Certify planar n=57 (K=3, m=1, all off-axis x>0) AND n=58 (K=2, m=2) integer witnesses
    xs57 = [0] * 28 + [14650, 418904, 457123] + [0] * 26
    zs57 = list(range(28)) + [177472, 185651, 188492] + [189224 + k for k in range(26)]
    pts57 = [[x, 0, z] for x, z in zip(xs57, zs57)]
    d57_mp80 = atiyah_det_planar_ordered_mp(xs57, zs57, dps=80)
    lo57, hi57 = mp.mpf(0), mp.mpf(1)
    for _ in range(70):
        mid = (lo57 + hi57) / 2
        if atiyah_det_planar_ordered_mp([mid * x for x in xs57], zs57, dps=50) > 0:
            lo57 = mid
        else:
            hi57 = mid
    s0_57 = (lo57 + hi57) / 2
    print(f"  [n=57 planar K=3 m=1] D_57(1) = {mp.nstr(d57_mp80, 30)}, root s0 = {mp.nstr(s0_57, 25)}")

    xs58 = [0] * 30 + [-4536, 4536, -107802, 107802] + [0] * 24
    zs58 = list(range(30)) + [62866, 62867, 66640, 66641] + [66660 + k for k in range(24)]
    pts58 = [[x, 0, z] for x, z in zip(xs58, zs58)]
    d58_mp80 = atiyah_det_planar_ordered_mp(xs58, zs58, dps=80)
    lo, hi = mp.mpf(0), mp.mpf(1)
    for _ in range(70):
        mid = (lo + hi) / 2
        if atiyah_det_planar_ordered_mp([mid * x for x in xs58], zs58, dps=50) > 0:
            lo = mid
        else:
            hi = mid
    s0_58 = (lo + hi) / 2
    print(f"  [n=58 planar K=2 m=2] D_58(1) = {mp.nstr(d58_mp80, 30)}, root s0 = {mp.nstr(s0_58, 25)}")

    # 2. Mirror-pair non-coplanar 3D extensions at n = 57 + 2 = 59 and n = 58 + 2 = 60 (H = 1e12)
    H_mp = mp.mpf(10**12)
    pts59_s1 = [[mp.mpf(x), mp.mpf(0), mp.mpf(z)] for x, z in zip(xs57, zs57)] + [[mp.mpf(0), mp.mpf(1), H_mp], [mp.mpf(0), mp.mpf(-1), H_mp]]
    d59_mp60 = atiyah_det_3d_mp(pts59_s1, dps=60)
    pts60_s1 = [[mp.mpf(x), mp.mpf(0), mp.mpf(z)] for x, z in zip(xs58, zs58)] + [[mp.mpf(0), mp.mpf(1), H_mp], [mp.mpf(0), mp.mpf(-1), H_mp]]
    d60_mp60 = atiyah_det_3d_mp(pts60_s1, dps=60)
    print(f"  [n=59 3D mirror-pair] D_59 = {mp.nstr(mp.re(d59_mp60), 25)} + ({mp.nstr(mp.im(d59_mp60), 5)})j")
    print(f"  [n=60 3D mirror-pair] D_60 = {mp.nstr(mp.re(d60_mp60), 25)} + ({mp.nstr(mp.im(d60_mp60), 5)})j")

    # 3. Hyperbolic H^3 (Beltrami-Klein) C3 (n=5), planar C1/C2 (n=57, n=58), and 3D C1/C2 (n=59) witnesses
    pts5 = [[1198773, 0, -320821], [212773, 0, -58745], [-55, 0, 3], [-56, 0, 4], [-697578, 0, 117714]]
    eps5 = mp.mpf("1e-7")
    pts5_H = [[eps5 * c for c in row] for row in pts5]
    hyp_c3_n5 = hyperbolic_conjecture3_ratio_mp(pts5_H, dps=80)

    pts5_3d_H = [[eps5 * c for c in row] for row in [[1198773, 1, -320821], [212773, 0, -58745], [-55, 0, 3], [-56, 0, 4], [-697578, 0, 117714]]]
    hyp_c3_n5_3d = hyperbolic_conjecture3_ratio_mp(pts5_3d_H, dps=80)

    eps57 = mp.mpf("1e-11")
    d57_H = hyperbolic_atiyah_det_klein_mp([[eps57 * c for c in row] for row in pts57], dps=80)
    eps58 = mp.mpf("1e-12")
    d58_H = hyperbolic_atiyah_det_klein_mp([[eps58 * c for c in row] for row in pts58], dps=80)
    pts59_H = [[mp.mpf(x) * mp.mpf("1e-13"), mp.mpf(0), mp.mpf(z) * mp.mpf("1e-13")] for x, z in zip(xs57, zs57)] + [
        [mp.mpf(0), mp.mpf("1e-13"), mp.mpf("1e-1")],
        [mp.mpf(0), -mp.mpf("1e-13"), mp.mpf("1e-1")],
    ]
    d59_H = hyperbolic_atiyah_det_klein_mp(pts59_H, dps=60)
    print(f"  [Hyperbolic H^3] n=5 C3 R3={hyp_c3_n5['R3'][:22]} | n=57 D_57^H={mp.nstr(mp.re(d57_H), 20)} | n=59 D_59^H={mp.nstr(mp.re(d59_H), 20)}")

    # 4. Multicore K=2 and K=3 threshold sweep across m = 1..9
    tasks = []
    k2_ranges = {1: range(60, 64), 2: range(55, 60), 3: range(50, 55), 4: range(43, 47), 5: range(36, 41), 6: range(33, 37), 7: range(31, 37), 8: range(32, 38), 9: range(34, 40)}
    for m, n_rng in k2_ranges.items():
        for n in n_rng:
            for b in range(1, min(n - 2 * m, n // 2 + 1)):
                tasks.append(("k2", m, n, b, 100000 + 1000 * m + 37 * n + b))

    k3_ranges = {1: range(55, 62), 4: range(38, 45), 5: range(33, 39), 6: range(30, 36), 7: range(30, 36)}
    for m, n_rng in k3_ranges.items():
        for n in n_rng:
            for b in range(m, (n - 3 * m) // 2 + 1):
                tasks.append(("k3", m, n, b, 200000 + 1000 * m + 41 * n + b))

    best_k2: dict[int, dict[str, Any]] = {}
    best_k3: dict[int, dict[str, Any]] = {}
    with ProcessPoolExecutor(max_workers=workers) as ex:
        futs = [ex.submit(_worker_k2_k3_grand_slam, t) for t in tasks]
        for fut in as_completed(futs):
            res = fut.result()
            if not res.get("hit"):
                continue
            target_dict = best_k2 if res["kind"] == "k2" else best_k3
            m = res["m"]
            if m not in target_dict or res["n"] < target_dict[m]["n"]:
                target_dict[m] = res

    for m, rec in sorted(best_k2.items()):
        print(f"  [Sweep K=2 m={m}] min n={rec['n']} (a={rec['a']}, b={rec['b']}) params={np.round(rec['params'], 5)}")
    for m, rec in sorted(best_k3.items()):
        print(f"  [Sweep K=3 m={m}] min n={rec['n']} (a={rec['a']}, b={rec['b']}) params={np.round(rec['params'], 5)}")

    # 5. Certify n=46 integer 3D (m=4) and n=35 general 3D (m=7) + K=3 m=1 positive-x planar n=60 in mp60
    # Construct n=46 integer m=4 (a=25, b=13) scaled by R1 = 1000:
    u4, d4, v4, R4 = 0.90190, 1.06869, 0.0, 21.39088
    s4 = 2000
    r4_2 = round(s4 * R4)
    hm4 = round(s4 * (u4 * R4 - d4))
    hp4 = round(s4 * (u4 * R4))
    pts46 = [[0, 0, k] for k in range(25)] + [
        [s4, 0, hm4], [0, s4, hm4], [-s4, 0, hm4], [0, -s4, hm4],
        [r4_2, 0, hp4], [0, r4_2, hp4], [-r4_2, 0, hp4], [0, -r4_2, hp4],
    ] + [[0, 0, hp4 + 20 + k] for k in range(13)]
    d46_mp60 = atiyah_det_3d_mp(pts46, dps=60)
    print(f"  [n=46 3D m=4 integer] D_46 = {mp.nstr(mp.re(d46_mp60), 25)} + ({mp.nstr(mp.im(d46_mp60), 4)})j")

    # Best K=2 lowest-n (m=7 n=35 at t=0.9999) + Best K=3 lowest-n (m=5 n=35 at t=0.9999)
    best_rec = min(best_k2.values(), key=lambda x: x["n"]) if best_k2 else {
        "m": 7, "n": 35, "a": 15, "b": 6, "params": [0.65584, 0.21941, 0.44412, 30.74957]
    }
    mp.mp.dps = 60
    um, dm, vm, Rm = best_rec["params"]
    pts_low = eickhoff_pts(best_rec["a"], best_rec["b"], best_rec["m"], um, dm, vm, Rm, 0.9999)
    dlow_mp60 = atiyah_det_3d_mp([[mp.mpf(c) for c in row] for row in pts_low], dps=60)
    print(f"  [3D min K=2 n={best_rec['n']} m={best_rec['m']} t=0.9999] D = {mp.nstr(mp.re(dlow_mp60), 25)} + ({mp.nstr(mp.im(dlow_mp60), 4)})j")

    k3_low = min(best_k3.values(), key=lambda x: x["n"]) if best_k3 else {
        "m": 5, "n": 35, "a": 14, "b": 6, "params": [12.84629, 15.51002, 0.00116, 16.71118, 0.82276, 0.01]
    }
    t_k3 = mp.mpf("0.9999")
    one_t = 1 - t_k3
    h1_k3, r2_k3, d12_k3, r3_k3, d23_k3, vt_k3 = [mp.mpf(v) for v in k3_low["params"]]
    vt_k3 = max(mp.mpf("0.01"), vt_k3)
    pts_k3_low = [[mp.mpf(0), mp.mpf(0), (j - k3_low["a"]) * t_k3 * one_t] for j in range(k3_low["a"])]
    for ri, hi_val in [(mp.mpf(1), h1_k3), (r2_k3, h1_k3 + d12_k3), (r3_k3, h1_k3 + d12_k3 + d23_k3)]:
        for k in range(k3_low["m"]):
            ang = 2 * mp.pi * k / k3_low["m"]
            pts_k3_low.append([t_k3 * ri * mp.cos(ang), t_k3 * ri * mp.sin(ang), hi_val])
    for j in range(k3_low["b"]):
        pts_k3_low.append([mp.mpf(0), mp.mpf(0), h1_k3 + d12_k3 + d23_k3 + vt_k3 + one_t + j * t_k3 * one_t])
    dk3_low_mp60 = atiyah_det_3d_mp(pts_k3_low, dps=60)
    print(f"  [3D min K=3 n={k3_low['n']} m={k3_low['m']} t=0.9999] D = {mp.nstr(mp.re(dk3_low_mp60), 25)} + ({mp.nstr(mp.im(dk3_low_mp60), 4)})j")

    # Certify K=3 m=1 positive-x planar minimum from sweep as well
    k3_m1_rec = best_k3.get(1, {"n": 57, "a": 28, "b": 26, "params": [12.11414, 28.59413, 0.55827, 31.20291, 0.19391, 0.05]})
    h1_3, r2_3, d12_3, r3_3, d23_3, vt_3 = k3_m1_rec["params"]
    vt_3 = max(0.05, abs(vt_3))
    scale3 = 50000
    a3, b3 = k3_m1_rec["a"], k3_m1_rec["b"]
    xs_k3 = [0] * a3 + [scale3, round(scale3 * r2_3), round(scale3 * r3_3)] + [0] * b3
    zs_k3 = (
        list(range(a3))
        + [round(scale3 * h1_3), round(scale3 * (h1_3 + d12_3)), round(scale3 * (h1_3 + d12_3 + d23_3))]
        + [round(scale3 * (h1_3 + d12_3 + d23_3 + vt_3)) + 10 + k for k in range(b3)]
    )
    dk3_m1_mp80 = atiyah_det_planar_ordered_mp(xs_k3, zs_k3, dps=80)
    print(f"  [K=3 m=1 positive-x planar n={k3_m1_rec['n']}] D = {mp.nstr(dk3_m1_mp80, 25)}")

    gs_data = {
        "elapsed_sec": round(time.time() - t_start, 2),
        "n57_planar_k3_m1_c1_c2_integer": {
            "n": 57, "a": 28, "b": 26, "m": 1, "orbits": 3,
            "pts_xyz_int": pts57,
            "D_57_mp80": mp.nstr(d57_mp80, 45),
            "homotopy_root_s0_mp50": mp.nstr(s0_57, 30),
        },
        "n58_planar_c1_c2_integer": {
            "n": 58, "a": 30, "b": 24, "m": 2,
            "pts_xyz_int": pts58,
            "D_58_mp80": mp.nstr(d58_mp80, 45),
            "homotopy_root_s0_mp50": mp.nstr(s0_58, 30),
        },
        "n59_3d_mirror_pair_c1_c2": {
            "n": 59, "H": 1e12,
            "D_59_re_mp60": mp.nstr(mp.re(d59_mp60), 35),
            "D_59_im_mp60": mp.nstr(mp.im(d59_mp60), 10),
        },
        "n60_3d_mirror_pair_c1_c2": {
            "n": 60, "H": 1e12,
            "D_60_re_mp60": mp.nstr(mp.re(d60_mp60), 35),
            "D_60_im_mp60": mp.nstr(mp.im(d60_mp60), 10),
        },
        "hyperbolic_H3": {
            "n5_planar_c3_eps1e7": {"eps": "1e-7", "pts_base_int": pts5, **hyp_c3_n5},
            "n5_noncoplanar_c3_eps1e7": {"eps": "1e-7", "pts_base_int": [[1198773, 1, -320821], [212773, 0, -58745], [-55, 0, 3], [-56, 0, 4], [-697578, 0, 117714]], **hyp_c3_n5_3d},
            "n57_planar_c2_eps1e11": {"eps": "1e-11", "D_57_H_re_mp80": mp.nstr(mp.re(d57_H), 40), "D_57_H_im_mp80": mp.nstr(mp.im(d57_H), 10)},
            "n58_planar_c2_eps1e12": {"eps": "1e-12", "D_58_H_re_mp80": mp.nstr(mp.re(d58_H), 40), "D_58_H_im_mp80": mp.nstr(mp.im(d58_H), 10)},
            "n59_noncoplanar_H": {"eps_xy": "1e-13", "H_ball": "1e-1", "D_59_H_re_mp60": mp.nstr(mp.re(d59_H), 35), "D_59_H_im_mp60": mp.nstr(mp.im(d59_H), 10)},
        },
        "n46_3d_m4_integer": {
            "n": 46, "m": 4, "a": 25, "b": 13, "pts_xyz_int": pts46,
            "D_46_re_mp60": mp.nstr(mp.re(d46_mp60), 35),
            "D_46_im_mp60": mp.nstr(mp.im(d46_mp60), 10),
        },
        "n_low_3d_k2": {
            **best_rec, "t": 0.9999,
            "D_re_mp60": mp.nstr(mp.re(dlow_mp60), 35),
            "D_im_mp60": mp.nstr(mp.im(dlow_mp60), 10),
        },
        "n_low_3d_k3": {
            **k3_low, "t": "0.9999",
            "D_re_mp60": mp.nstr(mp.re(dk3_low_mp60), 35),
            "D_im_mp60": mp.nstr(mp.im(dk3_low_mp60), 10),
        },
        "k3_m1_positive_x_planar": {
            **k3_m1_rec, "xs": xs_k3, "zs": zs_k3,
            "D_mp80": mp.nstr(dk3_m1_mp80, 40),
        },
        "k2_min_n_by_m": {str(m): rec for m, rec in sorted(best_k2.items())},
        "k3_min_n_by_m": {str(m): rec for m, rec in sorted(best_k3.items())},
    }
    existing["grand_slam_witnesses"] = gs_data
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    data_path.write_text(json.dumps(existing, indent=2), encoding="utf-8")
    print(f"Saved Grand Slam witnesses into {data_path} in {gs_data['elapsed_sec']}s")
    return gs_data


def run_sweep(workers: int) -> dict[str, Any]:
    t_start = time.time()
    print(f"=== Running Atiyah-Sutcliffe Multicore Sweep ({workers} workers) ===")

    # Sweep 1: Unrestricted 2D & 3D search for n = 5..10 (hunting C2, C3, C1)
    small_tasks = []
    for n in (5, 6, 7, 8, 9, 10, 12):
        n_rep = 12 if n <= 9 else 8
        for mode in ("2d", "3d"):
            for r in range(n_rep):
                small_tasks.append((n, r, mode, 10000 * n + (0 if mode == "2d" else 500) + r))

    small_summary: dict[str, Any] = {}
    with ProcessPoolExecutor(max_workers=workers) as ex:
        futs = [ex.submit(_worker_small_n_search, t) for t in small_tasks]
        per_key: dict[tuple[int, str], dict[str, Any]] = {}
        for fut in as_completed(futs):
            res = fut.result()
            key = (res["n"], res["mode"])
            cur = per_key.setdefault(key, {
                "best_abs": (float("inf"), None),
                "best_re": (float("inf"), None),
                "best_r3": (float("inf"), None),
            })
            if res["best_abs"][0] < cur["best_abs"][0]:
                cur["best_abs"] = res["best_abs"]
            if res["best_re"][0] < cur["best_re"][0]:
                cur["best_re"] = res["best_re"]
            if res["best_r3"][0] < cur["best_r3"][0]:
                cur["best_r3"] = res["best_r3"]

    for (n, mode), rec in sorted(per_key.items()):
        key_str = f"n={n}_{mode}"
        item: dict[str, Any] = {
            "float_min_abs": rec["best_abs"][0],
            "float_min_re": rec["best_re"][0],
            "float_min_r3": rec["best_r3"][0],
        }
        # High-precision mpmath verification of best C2 and C3 candidates
        if rec["best_abs"][1] is not None and rec["best_abs"][0] < 1.05:
            mp_c2 = conjecture3_ratio_mp(rec["best_abs"][1], dps=60)
            item["mp60_c2_cand"] = mp_c2
            item["mp60_c2_pts"] = rec["best_abs"][1]
        if rec["best_r3"][1] is not None and rec["best_r3"][0] < 1.05:
            mp_c3 = conjecture3_ratio_mp(rec["best_r3"][1], dps=60)
            item["mp60_c3_cand"] = mp_c3
            item["mp60_c3_pts"] = rec["best_r3"][1]
        small_summary[key_str] = item
        print(f"  [Sweep1 {key_str:10s}] min|D|={rec['best_abs'][0]:.6f}, minRe={rec['best_re'][0]:.6f}, minR3={rec['best_r3'][0]:.6f}")

    # Sweep 2: Coaxial m=1..4 scan across n = 5..68
    coaxial_tasks = []
    for m in (1, 2, 3, 4):
        n_max = 68 if m == 1 else (48 if m == 2 else 40)
        for n in range(2 * m + 2, n_max + 1):
            for b in range(m, n - 2 * m - m + 1):
                coaxial_tasks.append((n, m, b))

    coaxial_hits: dict[int, list[dict[str, Any]]] = {1: [], 2: [], 3: [], 4: []}
    smallest_c2_coaxial = None
    with ProcessPoolExecutor(max_workers=workers) as ex:
        futs = [ex.submit(_worker_coaxial_c2_c3_scan, t) for t in coaxial_tasks]
        for fut in as_completed(futs):
            res = fut.result()
            if not res.get("valid"):
                continue
            if res.get("c1_negative"):
                coaxial_hits[res["m"]].append(res)
            if "min_abs_dn" in res and res["min_abs_dn"] < 1.0:
                if smallest_c2_coaxial is None or res["n"] < smallest_c2_coaxial["n"]:
                    smallest_c2_coaxial = res

    for m in (1, 2, 3, 4):
        hits = sorted(coaxial_hits[m], key=lambda x: (x["n"], x["min_delta"]))
        if hits:
            h0 = hits[0]
            print(f"  [Sweep2 m={m}] SMALLEST NEGATIVE Delta(1) on grid: n={h0['n']} (a={h0['a']}, b={h0['b']}) params={h0['c1_params']} Delta={h0['min_delta']:.6e}")
        else:
            print(f"  [Sweep2 m={m}] no negative Delta(1) in grid range")
    if smallest_c2_coaxial:
        print(f"  [Sweep2 C2 coaxial] SMALLEST |D_n|<1 on m=1: n={smallest_c2_coaxial['n']} |D_n|={smallest_c2_coaxial['min_abs_dn']:.6f} params={smallest_c2_coaxial['c2_params']}")

    out = {
        "elapsed_sec": round(time.time() - t_start, 2),
        "small_n_unrestricted": small_summary,
        "coaxial_smallest_negative": {
            str(m): sorted(coaxial_hits[m], key=lambda x: (x["n"], x["min_delta"]))[:5]
            for m in (1, 2, 3, 4)
        },
        "coaxial_smallest_c2": smallest_c2_coaxial,
    }
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    out_path = DATA_DIR / "atiyah_sutcliffe_scan.json"
    out_path.write_text(json.dumps(out, indent=2), encoding="utf-8")
    print(f"Saved sweep summary to {out_path} in {out['elapsed_sec']}s")
    return out


def main() -> None:
    parser = argparse.ArgumentParser(description="Atiyah-Sutcliffe scanner & witness verifier")
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--sweep", action="store_true")
    parser.add_argument("--grand-slam", action="store_true")
    parser.add_argument("--certify-n36", action="store_true")
    parser.add_argument("--workers", type=int, default=max(1, (os.cpu_count() or 4) - 1))
    args = parser.parse_args()
    if args.self_test:
        run_self_test()
    if args.sweep:
        run_sweep(args.workers)
    if args.grand_slam:
        run_grand_slam(args.workers)
    if args.certify_n36:
        certify_n36_pythagorean()
    if not args.self_test and not args.sweep and not args.grand_slam and not args.certify_n36:
        parser.print_help()


if __name__ == "__main__":
    main()
