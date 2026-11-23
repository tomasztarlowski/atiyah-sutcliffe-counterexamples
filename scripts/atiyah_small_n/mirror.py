"""Mirror-symmetric (y -> -y) family with collapsed weighted clusters.

State = (weights, n_single, n_pair) + parameter vector
  clusters: (x, z) centre of a tight z-chain of `w` points (collapsed-cluster limit)
  singles : (x, z) in the mirror plane
  pairs   : (x, log y, z) and its mirror image
D is real on this family.  Beam search drops points while keeping D < 0.
"""
from __future__ import annotations

import json
import math
import sys
import time
from concurrent.futures import ProcessPoolExecutor

import numpy as np
from scipy.optimize import minimize

import fastdet as F

EPS = 2e-6      # chain spacing relative to configuration diameter
SEP = 2e-4      # minimal allowed separation between distinct objects (relative)
DATA = str(__import__("pathlib").Path(__file__).resolve().parents[2] / "data" / "atiyah_sutcliffe_scan.json")


def unpack(p, weights, ns, npair):
    c = len(weights)
    cl = p[: 2 * c].reshape(c, 2)
    sg = p[2 * c : 2 * c + 2 * ns].reshape(ns, 2)
    pr = p[2 * c + 2 * ns :].reshape(npair, 3)
    return cl, sg, pr


def objects(p, weights, ns, npair):
    """Distinct macro objects as 3D points (clusters as centres)."""
    cl, sg, pr = unpack(p, weights, ns, npair)
    out = [[x, 0.0, z] for x, z in cl] + [[x, 0.0, z] for x, z in sg]
    for x, ly, z in pr:
        y = math.exp(ly)
        out.append([x, y, z])
        out.append([x, -y, z])
    return np.array(out)


def build(p, weights, ns, npair, eps=EPS):
    obj = objects(p, weights, ns, npair)
    diam = float(np.max(np.linalg.norm(obj - obj.mean(0), axis=1))) * 2 + 1e-300
    pts = []
    for c, w in enumerate(weights):
        x, _, z = obj[c]
        for j in range(w):
            pts.append([x, 0.0, z + (j - (w - 1) / 2) * eps * diam])
    pts.extend(obj[len(weights):].tolist())
    return np.array(pts), obj, diam


def nd(p, weights, ns, npair):
    if not np.all(np.isfinite(p)) or np.any(np.abs(p) > 300):
        return 1.0
    pts, obj, diam = build(p, weights, ns, npair)
    d = np.linalg.norm(obj[None] - obj[:, None], axis=-1)
    md = float(np.min(d[np.triu_indices(len(obj), 1)])) if len(obj) > 1 else diam
    pen = 0.0
    if md < SEP * diam:
        pen = (SEP - md / diam) / SEP  # in (0, 1]
    with np.errstate(all="ignore"):
        try:
            v = F.normalized(pts)
        except Exception:
            return 1.0
    if not math.isfinite(v.real):
        return 1.0
    return float(v.real) + pen * 1e-3


def polish(p0, weights, ns, npair, rounds=3):
    args = (weights, ns, npair)
    best_p, best = np.array(p0, float), nd(p0, *args)
    for _ in range(rounds):
        r = minimize(nd, best_p, args=args, method="L-BFGS-B", options={"maxiter": 300, "eps": 1e-7})
        if r.fun < best:
            best, best_p = float(r.fun), r.x
        r = minimize(nd, best_p, args=args, method="Nelder-Mead",
                     options={"maxiter": 200 * len(best_p), "xatol": 1e-10, "fatol": 1e-17, "adaptive": True})
        if r.fun < best * (1 + 1e-6) - 1e-20:
            best, best_p = float(r.fun), r.x
        else:
            break
    return best, best_p


def ring_objects(r, h, m, phase=0):
    """Return (singles, pairs) of a regular m-gon symmetric under y -> -y."""
    singles, pairs = [], []
    for k in range(m):
        a = 2 * math.pi * (k + 0.5 * phase) / m
        x, y = r * math.cos(a), r * math.sin(a)
        if abs(y) < 1e-9 * r:
            singles.append([x, h])
        elif y > 0:
            pairs.append([x, math.log(y), h])
    return singles, pairs


def eickhoff_state(a, b, m, u, d, v, R):
    hm, hp = u * R - d, u * R
    clusters = [[0.0, 0.0], [0.0, hp + v + 1e-3]]
    s1, p1 = ring_objects(1.0, hm, m)
    s2, p2 = ring_objects(R, hp, m)
    singles, pairs = s1 + s2, p1 + p2
    p = np.array([c for o in clusters + singles for c in o] + [c for o in pairs for c in o], float)
    return (a, b), len(singles), len(pairs), p


def neighbours(weights, ns, npair, p):
    """All one-step reductions of a state."""
    c = len(weights)
    cl, sg, pr = unpack(np.asarray(p, float), weights, ns, npair)
    out = []
    for i in range(c):
        if weights[i] > 1:
            w = list(weights); w[i] -= 1
            out.append((f"w{i}", tuple(w), ns, npair, np.concatenate([cl.ravel(), sg.ravel(), pr.ravel()])))
        else:  # weight-1 cluster disappears
            w = list(weights); del w[i]
            out.append((f"W{i}", tuple(w), ns, npair, np.concatenate([np.delete(cl, i, 0).ravel(), sg.ravel(), pr.ravel()])))
    for i in range(ns):
        out.append((f"s{i}", weights, ns - 1, npair, np.concatenate([cl.ravel(), np.delete(sg, i, 0).ravel(), pr.ravel()])))
    for i in range(npair):
        rest = np.delete(pr, i, 0)
        out.append((f"p{i}", weights, ns, npair - 1, np.concatenate([cl.ravel(), sg.ravel(), rest.ravel()])))
        merged = np.vstack([sg, [[pr[i, 0], pr[i, 2]]]]) if ns else np.array([[pr[i, 0], pr[i, 2]]])
        out.append((f"m{i}", weights, ns + 1, npair - 1, np.concatenate([cl.ravel(), merged.ravel(), rest.ravel()])))
    return out


def count(weights, ns, npair):
    return sum(weights) + ns + 2 * npair


def _work(task):
    tag, weights, ns, npair, p, seed = task
    p = np.asarray(p, float)
    if seed:
        p = p + np.random.default_rng(seed).normal(scale=0.03, size=p.shape) * (1 + np.abs(p)) * 0.3
    with np.errstate(all="ignore"):
        val, q = polish(p, weights, ns, npair)
    return {"tag": tag, "weights": list(weights), "ns": ns, "npair": npair, "n": count(weights, ns, npair),
            "nd": val, "p": q.tolist()}


def main():
    beam = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    ms = sys.argv[2].split(",") if len(sys.argv) > 2 else ["5", "6", "7", "8", "9"]
    out = sys.argv[3] if len(sys.argv) > 3 else "mirror_results.json"
    g = json.load(open(DATA))["grand_slam_witnesses"]["k2_min_n_by_m"]
    tasks = []
    for m in ms:
        w = g[m]
        weights, ns, npair, p = eickhoff_state(w["a"], w["b"], int(m), *w["params"])
        print(f"seed m={m} n={count(weights, ns, npair)} raw nd={nd(p, weights, ns, npair):.3e}", flush=True)
        tasks.append((f"m{m}", weights, ns, npair, p.tolist(), 0))
    t0 = time.time()
    best_by_n: dict[int, list] = {}
    with ProcessPoolExecutor(max_workers=14) as ex:
        level = list(ex.map(_work, tasks))
        while level:
            neg = [r for r in level if r["nd"] < -1e-12]
            for r in level:
                if r["n"] >= 0 and r in neg:
                    best_by_n.setdefault(r["n"], []).append(r)
            for n in best_by_n:
                best_by_n[n] = sorted(best_by_n[n], key=lambda r: r["nd"])[: 3 * beam]
            json.dump({str(k): v for k, v in best_by_n.items()}, open(out, "w"))
            summary = {n: f"{v[0]['nd']:.2e}" for n, v in sorted(best_by_n.items())}
            print(f"[{time.time()-t0:.0f}s] level size {len(level)}, negatives {len(neg)}; best by n: {summary}", flush=True)
            if not neg:
                break
            # diversify: keep the best `beam` per (n, structure signature)
            groups: dict[tuple, list] = {}
            for r in sorted(neg, key=lambda r: r["nd"]):
                groups.setdefault((r["n"], tuple(r["weights"]), r["ns"], r["npair"]), []).append(r)
            keep = [rs[0] for rs in groups.values()]
            keep = sorted(keep, key=lambda r: (r["n"], r["nd"]))[: 4 * beam]
            tasks = []
            for r in keep:
                for tag, w, ns, npair, p in neighbours(tuple(r["weights"]), r["ns"], r["npair"], r["p"]):
                    for s in (0, 1 + hash((r["tag"], tag)) % 10**6):
                        tasks.append((r["tag"] + "." + tag, w, ns, npair, p.tolist(), s))
            level = list(ex.map(_work, tasks, chunksize=2))
    print("DONE", {n: v[0]["nd"] for n, v in sorted(best_by_n.items())})


if __name__ == "__main__":
    main()
