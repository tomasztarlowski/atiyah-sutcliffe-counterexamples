# Small-n search for negative Atiyah determinants

Numerical search (float64, confirmed with 60-digit `mpmath`) for mirror-symmetric
configurations in R^3 with `D_n < 0` below the previously recorded `n = 35`.
Results are numerical observations only; nothing here is Lean-certified.

- `fastdet.py` – vectorised determinant, same conventions as `../scan_atiyah_sutcliffe.py`.
- `mirror.py` – mirror-symmetric family with collapsed weighted clusters; beam descent from known witnesses.
- `explore.py` – structure search (point drops and same-n exchange moves): `python explore.py <states.json> <out.json> <seconds>`.
- `export.py` – rounds the best state per n to integer coordinates and re-verifies: `python export.py <states.json> <out.json>`.

Data: `data/atiyah_small_n_witnesses.json` (integer witnesses, n = 26..34).

## Lean certificate for n = 26

`Matematyka/AtiyahSutcliffe3D26.lean` (generated) proves, with standard axioms only, that the
family `x26Clamp t` (integer base points in `data/atiyah_n26_lean_base.json`, xy-plane scaled by
`max t 1`) has `Re D > 0` at `t = 8`, `Re D < 0` at `t = 10`, `Im D = 0` for all `t`, hence a
non-coplanar 26-point configuration with `D = 0`.

The Lean file was produced by one-off generators that port Part 3 and Part 5 of
`AtiyahSutcliffe3D36.lean` by text substitution and then emit the literal stage tables; they are not
included here.
