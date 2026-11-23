"""Structure search in the weighted mirror family: drops + same-n exchange moves."""
import json, sys, time, math
from concurrent.futures import ProcessPoolExecutor
import numpy as np
import mirror as M


def exchanges(weights, ns, npair, p, rng):
    cl, sg, pr = M.unpack(np.asarray(p, float), weights, ns, npair)
    obj = M.objects(np.asarray(p, float), weights, ns, npair)
    diam = float(np.ptp(obj, axis=0).max()) + 1e-12
    out = []

    def near():
        o = obj[rng.integers(len(obj))]
        s = diam * 10 ** rng.uniform(-2.5, -0.3)
        return o[0] + s * rng.normal(), abs(s * rng.normal()) + 1e-6 * diam, o[2] + s * rng.normal()

    def pack(w, c, s, q):
        return tuple(w), len(s), len(q), np.concatenate([np.ravel(c), np.ravel(s), np.ravel(q)])

    c = len(weights)
    for i in range(c):
        if weights[i] >= 2:
            w = list(weights); w[i] -= 1
            x, y, z = near()
            out.append(("x1", *pack(w, cl, np.vstack([sg.reshape(-1, 2), [[x, z]]]), pr)))
            for j in range(c):
                if j != i:
                    w2 = list(weights); w2[i] -= 1; w2[j] += 1
                    out.append(("x5", *pack(w2, cl, sg, pr)))
            for k in (1, 2, 3):
                if weights[i] > k:
                    w3 = list(weights); w3[i] -= k; w3.append(k)
                    x, y, z = near()
                    out.append(("x6", *pack(w3, np.vstack([cl, [[x, z]]]), sg, pr)))
        if weights[i] >= 3:
            w = list(weights); w[i] -= 2
            x, y, z = near()
            out.append(("x2", *pack(w, cl, sg, np.vstack([pr.reshape(-1, 3), [[x, math.log(y), z]]]))))
    for i in range(ns):
        for j in range(c):
            w = list(weights); w[j] += 1
            out.append(("x3", *pack(w, cl, np.delete(sg, i, 0), pr)))
    for i in range(npair):
        for j in range(c):
            w = list(weights); w[j] += 2
            out.append(("x4", *pack(w, cl, sg, np.delete(pr, i, 0))))
    return out


def main():
    src, out, budget = sys.argv[1], sys.argv[2], float(sys.argv[3])
    d = json.load(open(src))
    best = {int(k): v for k, v in d.items()}
    rng = np.random.default_rng(12345)
    t0 = time.time(); rnd = 0
    with ProcessPoolExecutor(max_workers=14) as ex:
        while time.time() - t0 < budget:
            nmin = min(best)
            pool = [r for n in (nmin, nmin + 1) for r in best.get(n, [])]
            groups = {}
            for r in sorted(pool, key=lambda r: r["nd"]):
                groups.setdefault((r["n"], tuple(sorted(r["weights"])), r["ns"], r["npair"]), []).append(r)
            reps = sorted([rs[0] for rs in groups.values()], key=lambda r: (r["n"], r["nd"]))[:10]
            tasks = []
            for r in reps:
                w = tuple(r["weights"])
                if r["n"] == nmin:  # try to go lower
                    for tag, w2, ns, npair, p in M.neighbours(w, r["ns"], r["npair"], r["p"]):
                        for s in range(3):
                            tasks.append((r["tag"] + "." + tag, w2, ns, npair, p.tolist(), 0 if s == 0 else int(rng.integers(1, 2**31))))
                for tag, w2, ns, npair, p in exchanges(w, r["ns"], r["npair"], r["p"], rng):
                    tasks.append((r["tag"] + "." + tag, w2, ns, npair, p.tolist(), 0))
            idx = rng.permutation(len(tasks))[:420]
            tasks = [tasks[i] for i in idx]
            res = list(ex.map(M._work, tasks, chunksize=2))
            neg = [r for r in res if r["nd"] < -1e-12]
            for r in neg:
                best.setdefault(r["n"], []).append(r)
            for n in best:
                seen, lst = set(), []
                for r in sorted(best[n], key=lambda r: r["nd"]):
                    key = (tuple(sorted(r["weights"])), r["ns"], r["npair"], round(r["nd"] * 1e9))
                    if key not in seen:
                        seen.add(key); lst.append(r)
                best[n] = lst[:30]
            json.dump({str(k): v for k, v in best.items()}, open(out, "w"))
            rnd += 1
            lo = min(best)
            print(f"[{time.time()-t0:.0f}s] round {rnd}: {len(tasks)} tries, {len(neg)} neg, n hit {sorted({r['n'] for r in neg})}; min n {lo} "
                  f"structs {[(r['weights'], r['ns'], r['npair'], '%.1e' % r['nd']) for r in best[lo][:3]]}", flush=True)
    print("DONE", {n: (v[0]["nd"], v[0]["weights"], v[0]["ns"], v[0]["npair"]) for n, v in sorted(best.items())})


if __name__ == "__main__":
    main()
