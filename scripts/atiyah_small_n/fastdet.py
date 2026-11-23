"""Fast vectorised normalized Atiyah determinant (same conventions as
scripts/scan_atiyah_sutcliffe.py::atiyah_det_3d) plus a scale-free variant."""
from __future__ import annotations

import math

import numpy as np

_VCACHE: dict[int, tuple[np.ndarray, complex]] = {}


def _roots(n: int) -> tuple[np.ndarray, complex]:
    if n not in _VCACHE:
        w = np.exp(2j * np.pi * np.arange(n) / n)
        V = w[:, None] ** np.arange(n)[None, :]  # V[k, l] = w_k^l
        _VCACHE[n] = (w, complex(np.linalg.det(V)))
    return _VCACHE[n]


def spinors(pts: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    """Return (A, B) with psi_ij = (A[i,j], B[i,j]); diagonal set to (1, 0)."""
    n = pts.shape[0]
    diff = pts[None, :, :] - pts[:, None, :]
    iu, ju = np.triu_indices(n, 1)
    v = diff[iu, ju]
    d = np.linalg.norm(v, axis=-1)
    v = v / d[:, None]
    vx, vy, vz = v[:, 0], v[:, 1], v[:, 2]
    s0 = np.empty(len(iu), dtype=np.complex128)
    s1 = np.empty(len(iu), dtype=np.complex128)
    pos = vz >= 0.0
    u = 1.0 + vz[pos]
    den = np.sqrt(2.0 * u)
    s0[pos] = u / den
    s1[pos] = (vx[pos] + 1j * vy[pos]) / den
    neg = ~pos
    u = 1.0 - vz[neg]
    den = np.sqrt(2.0 * u)
    s0[neg] = (vx[neg] - 1j * vy[neg]) / den
    s1[neg] = u / den
    A = np.ones((n, n), dtype=np.complex128)
    B = np.zeros((n, n), dtype=np.complex128)
    A[iu, ju] = s0
    B[iu, ju] = s1
    A[ju, iu] = -np.conj(s1)
    B[ju, iu] = np.conj(s0)
    return A, B


def det_and_scale(pts: np.ndarray) -> tuple[complex, float]:
    """Return (D_n, log of Hadamard bound of the evaluation matrix / |det V|).

    D_n = det(P) / det(V) where P[i, k] = p_i(w_k) = prod_{j != i} (a_ij + b_ij w_k).
    The second value is log(prod_i ||P_i||_2 / |det V|) >= log |D_n|.
    """
    n = pts.shape[0]
    w, detV = _roots(n)
    A, B = spinors(pts)
    F = A[:, :, None] + B[:, :, None] * w[None, None, :]  # (i, j, k)
    idx = np.arange(n)
    F[idx, idx, :] = 1.0
    P = np.prod(F, axis=1)
    sign, logabs = np.linalg.slogdet(P)
    D = sign * math.exp(logabs) / detV if logabs < 700 else complex("nan")
    rows = np.linalg.norm(P, axis=1)
    logH = float(np.sum(np.log(rows))) - math.log(abs(detV))
    return complex(D), logH, (sign / (detV / abs(detV))), logabs - math.log(abs(detV))


def atiyah_det(pts: np.ndarray) -> complex:
    return det_and_scale(np.asarray(pts, dtype=np.float64))[0]


def normalized(pts: np.ndarray) -> complex:
    """Scale-free D_n / HadamardBound in the closed unit disc."""
    _, logH, phase, logabs = det_and_scale(np.asarray(pts, dtype=np.float64))
    return phase * math.exp(logabs - logH)


def phase_logabs(pts: np.ndarray) -> tuple[complex, float]:
    _, _, phase, logabs = det_and_scale(np.asarray(pts, dtype=np.float64))
    return phase, logabs
