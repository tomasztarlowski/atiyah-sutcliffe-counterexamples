# Formal Disproofs of the Euclidean and Hyperbolic Atiyah–Sutcliffe Conjectures in Lean 4

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24443573.svg)](https://doi.org/10.5281/zenodo.24443573)

Machine-checked **Lean 4 (`v4.37.0-rc1` + Mathlib)** counterexamples, continuous homotopies, and high-precision (`60`–`80` digit `mpmath`) numerical certificates refuting all three classical Atiyah–Sutcliffe conjectures (2001/2002) in Euclidean space $C_n(\mathbb{R}^3)$ and hyperbolic space $C_n(\mathbb{H}^3)$.

- **Preprint manuscript:** [`paper/atiyah_sutcliffe_counterexamples.tex`](paper/atiyah_sutcliffe_counterexamples.tex) ([compiled PDF](paper/atiyah_sutcliffe_counterexamples.pdf), 17 pages)
- **Zenodo archive:** https://doi.org/10.5281/zenodo.24443573 (Concept DOI — always latest version; `v1.1.0`: https://doi.org/10.5281/zenodo.24476029)
- **Axiom purity:** All Lean 4 modules contain **zero** `sorry`, **zero** `admit`, **zero** `native_decide` (the $n = 26$ module uses kernel-only `decide +kernel`), and depend strictly on standard Lean axioms `{propext, Classical.choice, Quot.sound}`.

---

## Summary of Main Certified Results

| Space | Conjecture(s) | Particle Count $n$ | Witness / Method | Key Lean 4 Declarations |
|---|---|---|---|---|
| Planar $\mathbb{R}^2$ | **C3** (sharp minimal) | **$n = 5$** | Planar integer witness ($R_3 \approx 0.999996368278 < 1$), denominator cancellation, `FpIv` ($S_5 = 10^{18}$) | `exists_five_planar_points_violating_conjecture_3`, `disproof_atiyah_sutcliffe_conjecture_3` |
| Non-coplanar $\mathbb{R}^3$ | **C3** (sharp minimal) | **$n = 5$** | Out-of-plane perturbation $(1198773, \delta, -320821)$ with chart-independent limit | `exists_five_noncoplanar_points_violating_conjecture_3` |
| Planar $\mathbb{R}^2$ ($K=3, m=1$) | **C1, C2** | **$n = 57$** | Three positive-$x$ off-axis points ($a=28, b=26$), `gaussDetIv` + `denFoldIv` ($S_{57}=10^{40}$): $-1 < D_{57}(1) < 0$ ($\approx -0.498322$) and IVT $D_{57} = 0$ | `x57Path_one_re_neg_and_norm_lt_one`, `exists_planar_57_violating_conjecture_2`, `exists_planar_57_atiyahDet_zero` |
| Planar $\mathbb{R}^2$ ($K=2, m=1$) | **C1, C2** | **$n = 63$** | Exact $2 \times 2$ axial reduction + `denFoldIv` ($S_{63}=10^{35}$): $-1 < D_{63}(1) < 0$ ($\approx -0.639593$) and IVT $D_{63} = 0$ | `x63Path_one_norm_lt_one`, `exists_planar_63_atiyahDet_zero` |
| Non-coplanar $\mathbb{R}^3$ | **C1, C2** | **$n = 26$** | Mirror-symmetric ($y \mapsto -y$) integer family `x26Clamp` without rotational symmetry; certified complex Gaussian elimination `gaussDetCIv` on the full $26 \times 26$ matrix, staged kernel checks, sign reversal $D_{26}(8) > 0 > D_{26}(10)$ ($S_{26}=10^{30}$) | `exists_noncoplanar_3d_26_atiyahDet_neg`, `exists_noncoplanar_3d_26_atiyahDet_zero`, `disproof_atiyah_conjecture_1_3d_26`, `disproof_atiyah_sutcliffe_conjecture_2_3d_26` |
| Non-coplanar $\mathbb{R}^3$ | **C1, C2** | **$n = 36$** | Two coaxial Pythagorean $(33,56,65)$ rings (`x36Clamp`), parity split $36 \to 18 \times 18 \to 6 \times 6$ Schur complement, complex `CFpIv` sign reversal $D_{36}(9) > 0 > D_{36}(10)$ ($S_{36}=10^{18}$) | `exists_noncoplanar_3d_36_atiyahDet_neg`, `exists_noncoplanar_3d_36_atiyahDet_zero`, `disproof_atiyah_conjecture_1_3d_36`, `disproof_atiyah_sutcliffe_conjecture_2_3d_36` |
| Non-coplanar $\mathbb{R}^3$ | **C1, C2** ($0 < |D| < 1$) | **$n = 59$** | Mirror-pair extension $(0, \pm 1, H)$ of $\mathbf{x}^{(57)}(s)$, exact reality & decoupling as $H \to +\infty$ | `exists_noncoplanar_59_violating_conjecture_2`, `exists_noncoplanar_59_atiyahDet_zero` |
| Hyperbolic $\mathbb{H}^2, \mathbb{H}^3$ | **C3** | **$n = 5$** | Beltrami–Klein ball $\mathbb{B}^3 \cong \mathbb{H}^3$ infinitesimal scaling $\lim_{\varepsilon \to 0^+} D_n^{\mathbb{H}}(\varepsilon \mathbf{x}) = D_n(\mathbf{x})$ | `exists_five_planar_hyperbolic_violating_conjecture_3`, `exists_five_noncoplanar_hyperbolic_violating_conjecture_3`, `disproof_hyperbolic_atiyah_sutcliffe_conjecture_3` |
| Hyperbolic $\mathbb{H}^2, \mathbb{H}^3$ | **C1, C2** | **$n = 57$ ($\mathbb{H}^2$), $n = 59$ ($\mathbb{H}^3$)** | Klein scaling of $\mathbf{x}^{(57)}$ and mirror-pair $\widetilde{\mathbf{x}}_H$ yielding $-1 < D_n^{\mathbb{H}} < 0$ and $D_n^{\mathbb{H}} = 0$ | `exists_planar_57_hyperbolic_atiyahDet_zero`, `exists_noncoplanar_59_hyperbolic_violating_conjecture_2`, `exists_noncoplanar_59_hyperbolic_atiyahDet_zero`, `disproof_hyperbolic_atiyah_conjecture_1`, `disproof_hyperbolic_atiyah_sutcliffe_conjecture_2` |

In addition, bounded numerical sweeps using coaxial $m$-gon ansätze (`scripts/scan_atiyah_sutcliffe.py`, archived in `data/atiyah_sutcliffe_scan.json`) locate sign-reversal witnesses down to **$n = 35$** in $\mathbb{R}^3$ ($K=3, m=5$ and $K=2, m=7$) and a $\mathbb{Z}^3$ integer witness at **$n = 46$** ($K=2, m=4$).

Releasing the rotational symmetry (keeping only the mirror symmetry $y \mapsto -y$) and alternating local optimization with point deletions (`scripts/atiyah_small_n/`) gives integer witnesses with $D_n < 0$ for every $26 \le n \le 34$ (`data/atiyah_small_n_witnesses.json`, 60-digit `mpmath`; numerical observations except for the Lean-certified $n = 26$ family). The same search and an unsymmetric root search found nothing at $n = 25$; the smallest $n$ at which C1 fails is not known.

---

## Repository Structure

```text
.
├── Matematyka.lean                          # Root library importing the 5 modules below
├── Matematyka/
│   ├── MalkounCounterexample.lean           # Shared Pauli spinor & omega preliminaries on R^3 / C^2
│   ├── AtiyahSutcliffe.lean                 # Normalized D_n, FpIv, n=5 C3, n=63 planar C1/C2
│   ├── AtiyahSutcliffeExtensions.lean       # Chart switching, gaussDetIv/denFoldIv, n=57, n=59, H^3
│   ├── AtiyahSutcliffe3D36.lean             # Non-coplanar 3D n=36 Pythagorean C1/C2 disproof
│   └── AtiyahSutcliffe3D26.lean             # Mirror-symmetric 3D n=26 C1/C2 disproof (complex Gaussian elimination)
├── paper/
│   ├── atiyah_sutcliffe_counterexamples.tex # LaTeX manuscript (17 pages)
│   └── atiyah_sutcliffe_counterexamples.pdf # Compiled PDF
├── scripts/
│   ├── scan_atiyah_sutcliffe.py             # High-precision (60-80 digit mpmath) verifier & sweep
│   └── atiyah_small_n/                      # Mirror-symmetric small-n search (n=26 generators not included)
├── data/
│   ├── atiyah_sutcliffe_scan.json           # Archived coordinates and numerical certificates
│   ├── atiyah_small_n_witnesses.json        # Integer witnesses with D_n < 0 for n = 26..34
│   └── atiyah_n26_lean_base.json            # Base points and endpoints of the n=26 Lean family
├── lean-toolchain                           # leanprover/lean:v4.37.0-rc1
├── lakefile.toml
├── lake-manifest.json
└── LICENSE                                  # Apache-2.0
```

---

## Quick Reproduction

### 1. Verify all Lean 4 proofs

Requires [elan / Lean 4](https://leanprover.github.io/) matching `lean-toolchain` (`leanprover/lean:v4.37.0-rc1`):

```bash
lake exe cache get
lake build
```

*(Checking `AtiyahSutcliffe3D36.lean` computes kernel interval certificates across the 36-point matrix and typically takes ~4–5 minutes on modern hardware with `0` errors and `0` warnings; `AtiyahSutcliffe3D26.lean` (2.3 MB, literal stage tables checked with kernel-only `decide +kernel`) takes about 3 minutes.)*

### 2. Run high-precision numerical verification (`mpmath`)

```bash
python3 -m pip install mpmath numpy scipy
python3 scripts/scan_atiyah_sutcliffe.py --self-test
python3 scripts/scan_atiyah_sutcliffe.py --certify-n36
```

*(Cross-checks all Euclidean witnesses and Beltrami–Klein $\mathbb{B}^3$ / Poincaré ball $\mathbb{D}^3$ hyperbolic evaluations at 60–80 decimal digits.)*

---

## Context & Prior Art

1. **M. F. Atiyah (2001)**, *Configurations of points*, Phil. Trans. R. Soc. Lond. A **359**, 1375–1387; **M. F. Atiyah & P. Sutcliffe (2002)**, *The geometry of point particles*, Proc. R. Soc. Lond. A **458**, 1089–1115 — posed Conjectures 1–3 in $\mathbb{R}^3$ and $\mathbb{H}^3$.
2. **M. Eastwood & P. Norbury (2001)**, **D. Ž. Đoković (2002)**, **M. Mazur & B. V. Petrenko (2012, `arXiv:1102.4662`)**, **M. N. Bou Khuzam & M. J. Johnson (2014, `arXiv:1401.2787`)** — proved small-$n$ positive results for $n \le 4$.
3. **J. Eickhoff (Oct 2026, `arXiv:2610.33090`)**, *Singular Atiyah Configurations* — proved asymptotic existence of finite singular configurations ($D_n = 0$) in Euclidean and hyperbolic space via two-orbit dihedral families ($K = 2$).
4. **A. Akhtyamov (Oct 2026)**, [`azakhtyamov/atiyah-sutcliffe-disproof`](https://github.com/azakhtyamov/atiyah-sutcliffe-disproof) (`google-deepmind/formal-conjectures#6966`) — independently formalized a Lean 4 disproof of Euclidean C1 using a 46-point 3D helix via the unnormalized projective formulation of Mazur–Petrenko.
5. **H. Tan & Y. Zhang (4 Oct 2026)**, [*The Atiyah–Sutcliffe determinant at five points: positivity and failure of the deletion inequality*](https://doi.org/10.5281/zenodo.23142909) (Zenodo preprint) — announced $\operatorname{Re} D_5 \ge 5/768$ for all five-point configurations (C1 at $n = 5$) and a planar integer five-point counterexample to C3, certified by rational interval arithmetic. This predates the present repository; no priority is claimed here for the failure of Euclidean C3.

Our work formalizes the full normalized determinant $D_n(\mathbf{x})$ (enabling C2 and C3), lowers the Lean-certified 3D C1/C2 particle threshold from $46$ to $36$ and then to $26$, gives a Lean 4 proof that C3 fails at the minimal $n = 5$ (planar and strictly non-coplanar; the planar failure was first announced by Tan–Zhang), certifies direct nonzero $-1 < D_n < 0$ violations of C2, and establishes the first machine-checked hyperbolic $\mathbb{H}^3$ disproofs of C1–C3.

---

## Author & AI Disclosure

- **Author:** Tomasz Tarłowski (`tomasztarlowski`)
- **AI Assistance Disclosure:** Witness discovery, Lean 4 proof engineering, and manuscript preparation were carried out in a human–AI collaborative workflow using Gemini, Claude, and OpenAI Codex models. All formal proofs were independently verified by the Lean 4 kernel (`propext`, `Classical.choice`, `Quot.sound` only), and all numerical values were independently checked in 60–80 digit `mpmath`.

## License

Licensed under the [Apache License 2.0](LICENSE).
