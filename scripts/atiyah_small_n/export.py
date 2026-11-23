"""Export best candidate per n as integer coordinates and re-verify at 60 digits."""
import json, sys, numpy as np
sys.path.insert(0, str(__import__('pathlib').Path(__file__).resolve().parents[1]))
import scan_atiyah_sutcliffe as S, mirror as M
import mpmath as mp
src, out, scale = sys.argv[1], sys.argv[2], 10**9
d = json.load(open(src)); res = {}
for n in sorted(d, key=int):
    if int(n) > 34: continue
    for r in d[n][:6]:
        w = tuple(r['weights']); p = np.array(r['p'])
        pts, obj, diam = M.build(p, w, r['ns'], r['npair'], 1e-4)
        c = pts.mean(0); c[1] = 0.0
        ip = np.rint((pts - c) / diam * scale).astype(np.int64)
        ints = [[int(a) for a in row] for row in ip]
        assert len({tuple(x) for x in ints}) == len(ints)
        sym = {tuple(x) for x in ints} == {(x[0], -x[1], x[2]) for x in ints}
        D = S.atiyah_det_3d_mp(ints, 60)
        if D.real < 0 and sym:
            dd = np.linalg.norm(ip[None] - ip[:, None], axis=-1).astype(float)
            res[n] = {"n": int(n), "cluster_weights": list(w), "in_plane_singles": r['ns'], "mirror_pairs": r['npair'],
                      "coordinate_scale": scale, "points_int": ints, "mirror_symmetric_y": sym,
                      "min_pairwise_distance_int": float(dd[np.triu_indices(len(ints), 1)].min()),
                      "D_re_mp60": mp.nstr(D.real, 30), "D_im_mp60": mp.nstr(D.imag, 5)}
            print(n, w, r['ns'], r['npair'], 'D =', mp.nstr(D.real, 18), 'Im', mp.nstr(D.imag, 3), 'minsep', res[n]["min_pairwise_distance_int"], flush=True)
            break
    else:
        print(n, 'NO integer witness survived rounding')
json.dump({"description": "Mirror-symmetric integer configurations in R^3 with negative real Atiyah determinant D_n (numerical, 60-digit mpmath; not Lean-certified).", "witnesses": res}, open(out, 'w'), indent=1)
