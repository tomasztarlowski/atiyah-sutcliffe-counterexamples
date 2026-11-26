# Counterexamples and Holomorphic No-Go Rigidity for the Euclidean, Hyperbolic, and Symplectic Atiyah–Sutcliffe Conjectures

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24443573.svg)](https://doi.org/10.5281/zenodo.24443573)

Machine-checked **Lean 4 (`v4.35.0` + Mathlib `v4.35.0`, rev `56a00585`)** counterexamples, continuous homotopies, representation-theoretic No-Go rigidity theorems, and high-precision (`60`–`80` digit `mpmath`) numerical certificates refuting the Atiyah–Sutcliffe conjectures across Euclidean $C_n(\mathbb{R}^3)$, hyperbolic $C_n(\mathbb{H}^3)$, symplectic $\mathrm{Sp}(m)$, and odd-orthogonal $B_m = \mathrm{SO}(2m+1)$ configuration loci, alongside a universal $\mathrm{SU}(2) \times S_m$ spinor No-Go theorem.

- **Preprint manuscript (`Publication / Preprint`, inline PDF preview):** [`paper/atiyah_sutcliffe_counterexamples.tex`](paper/atiyah_sutcliffe_counterexamples.tex) ([compiled PDF](paper/atiyah_sutcliffe_counterexamples.pdf), 21 pages, 9 sections, 4 tables; archived Zenodo `v2.0.0` PDF was prepared against an earlier `v4.37.0-rc1` build, while this repository is pinned and verified on `leanprover/lean4:v4.35.0`) — Zenodo Preprint DOI: https://doi.org/10.5281/zenodo.24506382 (Concept DOI: https://doi.org/10.5281/zenodo.24506381)
- **Zenodo code & data archive:** https://doi.org/10.5281/zenodo.24443573 (Concept DOI — always resolves to the latest release; `v2.0.0`: https://doi.org/10.5281/zenodo.24505697; `v1.1.0`: https://doi.org/10.5281/zenodo.24476029)
- **Axiom purity & Palomar bridge:** All 8 Lean 4 library modules and `Solution.lean` contain **zero** `sorry`, **zero** `admit`, and **zero** `native_decide` (staged kernel table checks use `decide +kernel`). All **26 compared headline theorems** exported in `Challenge.lean` / `Solution.lean` / `comparator.json` depend strictly on standard Lean axioms `{propext, Classical.choice, Quot.sound}` (additional results noted below reside in the imported `Matematyka.AtiyahSutcliffe*` library modules).

---

## Summary of Main Certified Results

| Space / Group | Conjecture(s) | Particle Count $n$ | Witness / Method | Key Lean 4 Declarations |
|---|---|---|---|---|
| Planar $\mathbb{R}^2$ | **C3** (sharp minimal) | **$n = 5$** | Planar integer witness ($R_3 \approx 0.999996368278 < 1$), denominator cancellation, `FpIv` ($S_5 = 10^{18}$) | `exists_five_planar_points_violating_conjecture_3`, `disproof_atiyah_sutcliffe_conjecture_3` |
| Non-coplanar $\mathbb{R}^3$ | **C3** (sharp minimal) | **$n = 5$** | Out-of-plane perturbation $(1198773, \delta, -320821)$ with chart-independent limit | `exists_five_noncoplanar_points_violating_conjecture_3` |
| Planar $\mathbb{R}^2$ | **C1, C2** (direct nonzero C2) | **$n = 35$** | Staggered two-sided homotopy `x35Path`, staged `decide +kernel` Gaussian elimination ($S_{35} = 10^{34}$): $-1 < D_{35}(1) < 0$ ($\approx -0.499606$) and IVT $D_{35} = 0$ | `x35Path_one_re_neg_and_norm_lt_one`, `exists_planar_35_violating_conjecture_2`, `exists_planar_35_atiyahDet_zero` |
| Planar $\mathbb{R}^2$ ($K=3, 2$) | **C1, C2** | **$n = 57, 63$** | Off-axis orbits with `gaussDetIv`/`elimFront` + `denFoldIv` ($S_{57}=10^{40}$, $S_{63}=10^{35}$): $-1 < D_n(1) < 0$ and IVT $D_n = 0$ | `x57Path_one_re_neg_and_norm_lt_one`, `exists_planar_57_atiyahDet_zero`, `x63Path_one_norm_lt_one` |
| Non-coplanar $\mathbb{R}^3$ | **C1, C2** | **$n = 26$** | Mirror-symmetric ($y \mapsto -y$) integer family `x26Clamp`; certified $26 \times 26$ complex Gaussian elimination (`gaussDetCIv`, $S_{26}=10^{30}$), $D_{26}(8) > 0 > D_{26}(10)$ and IVT $D_{26} = 0$ | `exists_noncoplanar_3d_26_atiyahDet_neg`, `exists_noncoplanar_3d_26_atiyahDet_zero`, `disproof_atiyah_conjecture_1_3d_26`, `disproof_atiyah_sutcliffe_conjecture_2_3d_26` |
| Non-coplanar $\mathbb{R}^3$ | **C1, C2** | **$n = 36$** | Two coaxial Pythagorean $(33,56,65)$ rings (`x36Clamp`), parity split $36 \to 18 \times 18 \to 6 \times 6$ Schur reduction, `CFpIv` sign reversal $D_{36}(9) > 0 > D_{36}(10)$ ($S_{36}=10^{18}$) | `exists_noncoplanar_3d_36_atiyahDet_neg`, `exists_noncoplanar_3d_36_atiyahDet_zero`, `disproof_atiyah_conjecture_1_3d_36`, `disproof_atiyah_sutcliffe_conjecture_2_3d_36` |
| Non-coplanar $\mathbb{R}^3$ | **C1, C2** ($0 < |D| < 1$) | **$n = 37, 59$** | Mirror-pair extension $(0, \pm 1, H)$ of $\mathbf{x}^{(35)}$ and $\mathbf{x}^{(57)}$, exact $\sigma_2$ reality & $H \to +\infty$ decoupling | `exists_noncoplanar_37_violating_conjecture_2`, `exists_noncoplanar_37_atiyahDet_zero`, `exists_noncoplanar_59_violating_conjecture_2` |
| Hyperbolic $\mathbb{H}^2, \mathbb{H}^3$ | **C3** (and $n=3$ 5-gap) | **$n = 5$**, **$n = 3$** | Beltrami–Klein ball $\mathbb{B}^3 \cong \mathbb{H}^3$ limit $\lim_{\varepsilon \to 0^+} D_n^{\mathbb{H}}(\varepsilon \mathbf{x}) = D_n(\mathbf{x})$ (`n=5` coplanar $\mathbb{H}^2$ & non-coplanar $\mathbb{H}^3$); exact 5-gap positivity identity $D_3^{\mathbb{H}} > 1$ at $\{(-3/5,0,0),(3/5,0,0),(0,0,4/5)\}$ | `exists_five_planar_hyperbolic_violating_conjecture_3`, `exists_five_noncoplanar_hyperbolic_violating_conjecture_3`, `disproof_hyperbolic_atiyah_sutcliffe_conjecture_3`, `three_point_uniform_gap_identity`, `hyperbolic_three_point_five_gap_gt_one`, `exists_hyperbolic_three_point_det_gt_one` |
| Hyperbolic $\mathbb{H}^2, \mathbb{H}^3$ | **C1, C2** | **$n = 35$ ($\mathbb{H}^2$), $n = 26, 37, 59$ ($\mathbb{H}^3$)** | General permutation $y$-reflection reality (`atiyahDetOfSpinors_im_eq_zero_of_perm_yRefl`) + Klein scaling of `x26Clamp`, `x35Path`, and mirror-pair lifts | `exists_noncoplanar_26_hyperbolic_atiyahDet_zero`, `exists_noncoplanar_26_hyperbolic_violating_conjecture_2`, `exists_planar_35_hyperbolic_violating_conjecture_2`, `exists_noncoplanar_37_hyperbolic_violating_conjecture_2`, `disproof_hyperbolic_atiyah_conjecture_1`, `disproof_hyperbolic_atiyah_sutcliffe_conjecture_2` |
| Symplectic $\mathrm{Sp}(m)$ | **C1, C2, $D \neq 0$** | **$2m = 40$ ($\mathrm{Sp}(20)$, $\mathbb{R}^2$)** & **$2m = 36$ ($\mathrm{Sp}(18)$, 3D)** | $z$-rotation parity-subblock reduction ($20 \times 20$ / $18 \times 18$ real even subblocks, `S_symp = 10^28`) bypassing quaternionic Study non-negativity $D_{2m} \ge 0$ | `exists_planar_symplectic_20_atiyahDet_zero`, `disproof_symplectic_20_conjecture_1`, `exists_noncoplanar_symplectic_18_atiyahDet_zero`, `disproof_symplectic_18_conjecture_1` |
| Orthogonal $B_{18} = \mathrm{SO}(37)$ | **C1, C2**, non-origin rank | **$n = 37$** ($1 + 36$ points) | Origin-augmented Pythagorean pairs, $18 \times 18$ odd subblock sign flip (`b18SubMat`), nullvector vanishes at origin index | `exists_noncoplanar_orthogonalB_18_atiyahDet_zero_and_nonOrigin_dep`, `disproof_orthogonalB_18_conjecture_1` |
| Universal $\mathrm{SU}(2) \times S_m$ No-Go | Multi-body spinor ansätze | **$n = 26$ ($\mathbb{R}^3$), $35$ ($\mathbb{R}^2$), $36$ ($\mathrm{Sp}(18)$)** | Diagonal $U_\zeta$ ($\zeta = (3+4i)/5$) + Hadamard $U_H$ Schur–Weyl rigidity proving every weighted sum collapses row-wise to $\mu_i(\mathbf{x}) p_i^{\mathrm{Atiyah}}(t)$ | `su2_symmetric_multilinear_eq_atiyahFactor`, `weightedSpinorCandidate_eq_smul_atiyahPoly`, `universal_holomorphic_spinor_nogo_noncoplanar_3d_26`, `universal_holomorphic_spinor_nogo_planar_35`, `universal_holomorphic_spinor_nogo_symplectic_36` |

Additional archived high-precision (`60`–`65` digit `mpmath`) numerical observations in `data/`:
- Bounded coaxial $m$-gon sweeps (`data/atiyah_sutcliffe_scan.json`): $\mathrm{Re}\, D_n < 0$ down to $n = 35$ ($K = 3, m = 5$ and $K = 2, m = 7$) and a $\mathbb{Z}^3$ witness at $n = 46$ ($K = 2, m = 4$).
- Mirror-symmetric small-$n$ witnesses (`data/atiyah_small_n_witnesses.json`): integer witnesses with $D_n < 0$ for every $26 \le n \le 34$.
- Part II witnesses (`data/atiyah_part2_witnesses.json`): compact 9-digit planar $n = 35$ (`planar_35_compact`, $D_{35} \approx -7.225271903803 \times 10^{12}$), direct nonzero symplectic $\mathrm{Sp}(20)$ C2 witness (`planar_sp20_40_c2`, $D_{40} \approx +0.001580470140$), and direct nonzero 3D $\mathrm{Sp}(18)$ C2 witness (`sp18_36_3d_c2`, $D_{36} \approx +0.244578325159$).

---

## Repository Structure

```text
.
├── Matematyka.lean                          # Root library importing all 8 modules below
├── Matematyka/
│   ├── MalkounCounterexample.lean           # Shared Pauli spinor & omega preliminaries on R^3 / C^2
│   ├── AtiyahSutcliffe.lean                 # Normalized D_n, FpIv, n=5 C3, n=63 planar C1/C2
│   ├── AtiyahSutcliffeExtensions.lean       # Chart switching, gaussDetIv/denFoldIv, n=57, n=59, H^3
│   ├── AtiyahSutcliffe3D36.lean             # Non-coplanar 3D n=36 Pythagorean C1/C2 disproof
│   ├── AtiyahSutcliffe3D26.lean             # Mirror-symmetric 3D n=26 C1/C2 disproof (gaussDetCIv)
│   ├── AtiyahSutcliffePlanar35.lean         # Planar n=35 (S35=10^34), 3D n=37, H^3 n=26/35/37
│   ├── AtiyahSutcliffeSymplectic.lean       # Sp(20) (N=40), Sp(18) (N=36), B_18=SO(37) (N=37)
│   └── AtiyahSutcliffeNoGo.lean             # SU(2)xS_m rigidity, weighted No-Go, H^3 n=3 5-gap D_3>1
├── Challenge.lean                           # Lightweight Palomar/Comparator specification (26 theorems)
├── Solution.lean                            # Zero-sorry proof bridge importing Matematyka.AtiyahSutcliffe*
├── comparator.json                          # Axiom and theorem checklist for Challenge vs Solution
├── formalization.yaml                       # Formalization metadata
├── paper/
│   ├── atiyah_sutcliffe_counterexamples.tex # Unified LaTeX manuscript (21 pages, 9 sections)
│   └── atiyah_sutcliffe_counterexamples.pdf # Compiled PDF
├── scripts/
│   ├── scan_atiyah_sutcliffe.py             # High-precision (60-80 digit mpmath) verifier & sweep
│   ├── atiyah_small_n/                      # Mirror-symmetric small-n search (n=26..34)
│   └── part2_gen/                           # Lean table generators & 65/80-digit verifiers (n=35, Sp/B_18)
├── data/
│   ├── atiyah_sutcliffe_scan.json           # Archived coaxial sweep coordinates & C3/H^3 certificates
│   ├── atiyah_small_n_witnesses.json        # Integer witnesses with D_n < 0 for n = 26..34
│   ├── atiyah_n26_lean_base.json            # Base points and endpoints of the n=26 Lean family
│   └── atiyah_part2_witnesses.json          # Planar n=35 & symplectic Sp(20)/Sp(18)/B_18 JSON witnesses
├── lean-toolchain                           # leanprover/lean:v4.35.0
├── lakefile.toml
├── lake-manifest.json
└── LICENSE                                  # Apache-2.0
```

---

## Quick Reproduction

### 1. Verify all Lean 4 proofs

Requires [elan / Lean 4](https://leanprover.github.io/) matching `lean-toolchain` (`leanprover/lean:v4.35.0`, Mathlib `v4.35.0` rev `56a005855ea17e0b0958f73ec801ae140b0a1679`):

```bash
lake exe cache get
lake build
```

*(Note: `AtiyahSutcliffe3D36.lean`, `AtiyahSutcliffe3D26.lean`, `AtiyahSutcliffePlanar35.lean`, and `AtiyahSutcliffeSymplectic.lean` verify staged `decide +kernel` interval tables across matrices up to size $40 \times 40$; building sequentially inside `lake build` compiles all 8 library modules plus `Challenge` and `Solution` cleanly with zero warnings.)*

### 2. Run high-precision numerical verification (`mpmath`)

```bash
python3 -m pip install mpmath numpy scipy
python3 scripts/scan_atiyah_sutcliffe.py --self-test
python3 scripts/scan_atiyah_sutcliffe.py --certify-n36
```

*(Cross-checks Euclidean witnesses and Beltrami–Klein $\mathbb{B}^3$ / Poincaré ball $\mathbb{D}^3$ hyperbolic evaluations at 60–80 decimal digits.)*

---

## Context & Prior Art

1. **M. V. Berry & J. M. Robbins (1997)**, *Indistinguishability for quantum particles: spin, statistics and the geometric phase*, Proc. R. Soc. Lond. A **453**, 1771–1790 — posed the smooth equivariant frame problem.
2. **M. F. Atiyah (2001)**, *Configurations of points*, Phil. Trans. R. Soc. Lond. A **359**, 1375–1387; **M. F. Atiyah & P. Sutcliffe (2002)**, *The geometry of point particles*, Proc. R. Soc. Lond. A **458**, 1089–1115 — posed Conjectures 1–3 in $\mathbb{R}^3$ and $\mathbb{H}^3$.
3. **M. F. Atiyah & R. Bielawski (2002)**, *Nahm's equations, configuration spaces and flag manifolds*, Bull. Braz. Math. Soc. **33**, 157–176 (`arXiv:math/0110112`); **J. Malkoun (2014, 2015)** (`arXiv:1407.8291`, `arXiv:1508.04076`) — generalized to compact Lie groups and formulated the $\mathrm{Sp}(m)$ and $B_m = \mathrm{SO}(2m+1)$ candidates.
4. **M. Eastwood & P. Norbury (2001)**, **D. Ž. Đoković (2002)**, **M. Mazur & B. V. Petrenko (2012, `arXiv:1102.4662`)**, **M. N. Bou Khuzam & M. J. Johnson (2014, `arXiv:1401.2787`)** — proved small-$n$ positive results for $n \le 4$.
5. **J. Eickhoff (Oct 2026, `arXiv:2610.33090`)**, *Singular Atiyah Configurations* — proved asymptotic existence of finite singular configurations ($D_n = 0$) in Euclidean and hyperbolic space via two-orbit dihedral families ($K = 2$).
6. **A. Akhtyamov (Oct 2026)**, [`azakhtyamov/atiyah-sutcliffe-disproof`](https://github.com/azakhtyamov/atiyah-sutcliffe-disproof) (`google-deepmind/formal-conjectures#6966`) — independently formalized a Lean 4 disproof of Euclidean C1 using a 46-point 3D helix via the unnormalized projective formulation of Mazur–Petrenko.
7. **H. Tan & Y. Zhang (4 Oct 2026)**, [*The Atiyah–Sutcliffe determinant at five points: positivity and failure of the deletion inequality*](https://doi.org/10.5281/zenodo.23142909) (Zenodo preprint) — announced $\operatorname{Re} D_5 \ge 5/768$ for all five-point configurations (C1 at $n = 5$) and a planar integer five-point counterexample to C3, certified by rational interval arithmetic. This predates the present repository; no priority is claimed here for the failure of Euclidean C3.

---

## Author & AI Disclosure

- **Author:** Tomasz Tarłowski (`tomasztarlowski`)
- **AI Assistance & Review Disclosure:** Witness discovery, Lean 4 proof engineering, informal script/text checks, and manuscript preparation were carried out in a human–AI collaborative workflow using Gemini, Claude, and OpenAI Codex models. All formal proofs were mechanically verified by the Lean 4 `v4.35.0` kernel (`propext`, `Classical.choice`, `Quot.sound` only) and `lake comparator` across all 26 compared theorems, and numerical values were cross-checked in 60–80 digit `mpmath`; review status is self-assessed by the author (`formalization.yaml`), with no external human mathematical peer review of the formalization conducted prior to registration.

## License

Licensed under the [Apache License 2.0](LICENSE).
