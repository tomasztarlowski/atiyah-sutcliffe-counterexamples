"""Generate lean/Matematyka/AtiyahSutcliffeSymplectic.lean for Sp(20), Sp(18), and B_18."""
from __future__ import annotations

import json
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
S_SYMP = 10**28


def floor_div(a: int, b: int) -> int:
    return a // b


def ceil_div(a: int, b: int) -> int:
    return -((-a) // b)


def fp_add(a: tuple[int, int], b: tuple[int, int]) -> tuple[int, int]:
    return (a[0] + b[0], a[1] + b[1])


def fp_sub(a: tuple[int, int], b: tuple[int, int]) -> tuple[int, int]:
    return (a[0] - b[1], a[1] - b[0])


def fp_neg(a: tuple[int, int]) -> tuple[int, int]:
    return (-a[1], -a[0])


def fp_mul(a: tuple[int, int], b: tuple[int, int], S: int = S_SYMP) -> tuple[int, int]:
    p = [a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1]]
    return (floor_div(min(p), S), ceil_div(max(p), S))


def slope3d_fp(num: int, dz: int, rho: int, S: int = S_SYMP) -> tuple[int, int]:
    if num == 0:
        return (0, 0)
    dlo = S * dz + rho
    dhi = S * dz + rho + 1
    assert dlo > 0
    if num >= 0:
        return (floor_div(S * S * num, dhi), ceil_div(S * S * num, dlo))
    k = -num
    return (-ceil_div(S * S * k, dlo), -floor_div(S * S * k, dhi))


CFp = tuple[tuple[int, int], tuple[int, int]]
CZERO: CFp = ((0, 0), (0, 0))
CONE: CFp = ((S_SYMP, S_SYMP), (0, 0))


def c_add(a: CFp, b: CFp) -> CFp:
    return (fp_add(a[0], b[0]), fp_add(a[1], b[1]))


def c_neg(a: CFp) -> CFp:
    return (fp_neg(a[0]), fp_neg(a[1]))


def c_conj(a: CFp) -> CFp:
    return (a[0], fp_neg(a[1]))


def c_mul(a: CFp, b: CFp, S: int = S_SYMP) -> CFp:
    return (
        fp_sub(fp_mul(a[0], b[0], S), fp_mul(a[1], b[1], S)),
        fp_add(fp_mul(a[0], b[1], S), fp_mul(a[1], b[0], S)),
    )


def c_normSq(a: CFp, S: int = S_SYMP) -> tuple[int, int]:
    return fp_add(fp_mul(a[0], a[0], S), fp_mul(a[1], a[1], S))


def fp_divPos(a: tuple[int, int], b: tuple[int, int], S: int = S_SYMP) -> tuple[int, int]:
    assert b[0] > 0
    n1, n2 = S * a[0], S * a[1]
    d1, d2 = b[0], b[1]
    lo = min(n1 // d1, n1 // d2, n2 // d1, n2 // d2)
    hi = max((n1 + d1 - 1) // d1, (n1 + d2 - 1) // d2, (n2 + d1 - 1) // d1, (n2 + d2 - 1) // d2)
    return (lo, hi)


def c_div(a: CFp, b: CFp, S: int = S_SYMP) -> CFp:
    ns = c_normSq(b, S)
    assert ns[0] > 0, f"Pivot not separated: {b}"
    num = c_mul(a, c_conj(b), S)
    return (fp_divPos(num[0], ns, S), fp_divPos(num[1], ns, S))


def c_is_zero(a: CFp) -> bool:
    return a[0] == (0, 0) and a[1] == (0, 0)


def mulLinListC_iv(f0: CFp, f1: CFp, ps: list[CFp]) -> list[CFp]:
    s0 = [CZERO if c_is_zero(x) or c_is_zero(f0) else c_mul(f0, x) for x in ps] + [CZERO]
    s1 = [CZERO] + [CZERO if c_is_zero(x) or c_is_zero(f1) else c_mul(f1, x) for x in ps]
    return [c_add(x, y) for x, y in zip(s0, s1)]


def stepPolyCIv(w_table: list[list[CFp]], i: int, ps: list[CFp], j: int) -> list[CFp]:
    if j == i:
        return ps
    if j < i:
        return mulLinListC_iv(c_neg(c_conj(w_table[j][i])), CONE, ps)
    return mulLinListC_iv(CONE, w_table[i][j], ps)


def elimRowsCIvWithMults(
    piv: CFp, ptail: list[CFp], rows: list[list[CFp]]
) -> tuple[list[CFp], list[list[CFp]]]:
    mults: list[CFp] = []
    nxt: list[list[CFp]] = []
    for row in rows:
        rh, rt = row[0], row[1:]
        if c_is_zero(rh):
            mults.append(CZERO)
            nxt.append(rt)
        else:
            mult = c_div(c_neg(rh), piv)
            mults.append(mult)
            nxt.append(
                [r if c_is_zero(p) else c_add(r, c_mul(mult, p)) for r, p in zip(rt, ptail)]
            )
    return mults, nxt


def fmt_cfp(a: CFp) -> str:
    return f"⟨⟨{a[0][0]}, {a[0][1]}⟩, ⟨{a[1][0]}, {a[1][1]}⟩⟩"


def fmt_cfp_list(xs: list[CFp]) -> str:
    return "[" + ", ".join(fmt_cfp(x) for x in xs) + "]"


def fmt_cfp_mat(rows: list[list[CFp]], indent: str = "  ") -> str:
    if not rows:
        return "[]"
    lines = ["["]
    for idx, row in enumerate(rows):
        sep = "," if idx + 1 < len(rows) else ""
        lines.append(f"{indent}[{', '.join(fmt_cfp(x) for x in row)}]{sep}")
    lines.append("]")
    return "\n".join(lines)


def fmt_int_mat(rows: list[list[int]], indent: str = "  ") -> str:
    lines = ["["]
    for idx, row in enumerate(rows):
        sep = "," if idx + 1 < len(rows) else ""
        lines.append(f"{indent}[{', '.join(str(x) for x in row)}]{sep}")
    lines.append("]")
    return "\n".join(lines)


def fmt_coord_triple_list(pts: list[list[int]]) -> tuple[str, str, str]:
    xs = "[" + ", ".join(str(p[0]) for p in pts) + "]"
    ys = "[" + ", ".join(str(p[1]) for p in pts) + "]"
    zs = "[" + ", ".join(str(p[2]) for p in pts) + "]"
    return xs, ys, zs


def compute_cert(
    prefix: str,
    fam: str,
    base_pts: list[list[int]],
    t_val: int,
    src_indices: list[int],
    odd: bool,
    chunks: list[list[int]],
    expect_sign: str,
) -> tuple[str, str]:
    n = len(base_pts)
    m = len(src_indices)
    pts = [[t_val * p[0], t_val * p[1], p[2]] for p in base_pts]
    rho_tbl = [[0] * n for _ in range(n)]
    w_tbl: list[list[CFp]] = [[CZERO] * n for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            dx = pts[j][0] - pts[i][0]
            dy = pts[j][1] - pts[i][1]
            dz = pts[j][2] - pts[i][2]
            assert dz >= 0
            if dx != 0 or dy != 0:
                sq = dx * dx + dy * dy + dz * dz
                rho = math.isqrt(S_SYMP * S_SYMP * sq)
                assert rho > 0
                assert rho * rho <= S_SYMP * S_SYMP * sq <= (rho + 1) * (rho + 1)
                assert S_SYMP * dz + rho > 0
                rho_tbl[i][j] = rho
                w_tbl[i][j] = (slope3d_fp(dx, dz, rho), slope3d_fp(dy, dz, rho))

    p_stages: list[list[list[CFp]]] = []
    cur_p = [[CONE] for _ in range(m)]
    for ch in chunks:
        nxt_p = []
        for r_idx, i in enumerate(src_indices):
            ps = cur_p[r_idx][:]
            for j in ch:
                ps = stepPolyCIv(w_tbl, i, ps, j)
            nxt_p.append(ps)
        cur_p = nxt_p
        p_stages.append(cur_p)

    sub = [[cur_p[r][2 * c + (1 if odd else 0)] for c in range(m)] for r in range(m)]

    g_stages: list[tuple[list[CFp], list[list[CFp]], CFp]] = []
    cur_g = [row[:] for row in sub]
    cur_prod = CONE
    for step in range(m):
        piv = cur_g[0][0]
        assert c_normSq(piv)[0] > 0, f"{prefix}: zero pivot at step {step}"
        cur_prod = c_mul(cur_prod, piv)
        mults, nxt_g = elimRowsCIvWithMults(piv, cur_g[0][1:], cur_g[1:])
        cur_g = nxt_g
        g_stages.append((mults, cur_g, cur_prod))

    if expect_sign == "pos":
        assert cur_prod[0][0] > 0, f"{prefix} expected > 0, got {cur_prod}"
    else:
        assert cur_prod[0][1] < 0, f"{prefix} expected < 0, got {cur_prod}"

    print(f"{prefix}: OK (sign={expect_sign}, lo={cur_prod[0][0]}, hi={cur_prod[0][1]})")

    lines: list[str] = []
    lines.append(f"section Cert_{prefix}\n")
    lines.append("set_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n\n")
    lines.append(f"private def rho_{prefix} : List (List ℤ) := {fmt_int_mat(rho_tbl)}\n\n")
    lines.append(f"private def w_{prefix} : List (List CFpIv) := {fmt_cfp_mat(w_tbl)}\n\n")
    lines.append(
        f"private lemma ok_{prefix} : slopeTableOk {n} S_symp {fam}BaseXList {fam}BaseYList {fam}BaseZList {t_val} rho_{prefix} w_{prefix} = true := by decide +kernel\n\n"
    )
    for k, st in enumerate(p_stages):
        lines.append(f"private def P_{prefix}_{k} : List (List CFpIv) := {fmt_cfp_mat(st)}\n\n")
    for k in range(len(p_stages)):
        lhs = (
            f"stagePRows S_symp (wRead2D w_{prefix}) {fam}SrcList {fam}_ch{k} (List.replicate {m} [CFpIv.ofInt S_symp 1])"
            if k == 0
            else f"stagePRows S_symp (wRead2D w_{prefix}) {fam}SrcList {fam}_ch{k} P_{prefix}_{k-1}"
        )
        lines.append(f"private lemma stP_{prefix}_{k} : {lhs} = P_{prefix}_{k} := by decide +kernel\n")
    lines.append(
        f"\nprivate lemma srcRows_{prefix}_eq : {fam}SrcList.map (polyListCIv S_symp (wRead2D w_{prefix})) = P_{prefix}_{len(p_stages)-1} := by\n"
        f"  rw [{fam}_srcRows_stages, "
        + ", ".join(f"stP_{prefix}_{k}" for k in range(len(p_stages)))
        + "]\n\n"
    )
    ext_fn = "extractSubOdd" if odd else "extractSubEven"
    lines.append(f"private def sub_{prefix} : List (List CFpIv) := {fmt_cfp_mat(sub)}\n\n")
    lines.append(
        f"private lemma sub_{prefix}_eq : {ext_fn} {m} P_{prefix}_{len(p_stages)-1} = sub_{prefix} := by decide +kernel\n\n"
    )
    for step, (mults, rows_st, prod_st) in enumerate(g_stages):
        lines.append(f"private def M_{prefix}_{step} : List CFpIv := {fmt_cfp_list(mults)}\n\n")
        lines.append(f"private def G_{prefix}_{step} : List (List CFpIv) := {fmt_cfp_mat(rows_st)}\n\n")
        lines.append(f"private def Q_{prefix}_{step} : CFpIv := {fmt_cfp(prod_st)}\n\n")
    for step in range(m):
        lhs_r = f"sub_{prefix}" if step == 0 else f"G_{prefix}_{step-1}"
        lhs_p = "(CFpIv.ofInt S_symp 1)" if step == 0 else f"Q_{prefix}_{step-1}"
        lines.append(
            f"private lemma stG_{prefix}_{step} : gaussHeadCIvWithMults S_symp {lhs_r} {lhs_p} M_{prefix}_{step} = (true, G_{prefix}_{step}, Q_{prefix}_{step}) := by decide +kernel\n"
        )
    lines.append(
        f"\nprivate lemma gauss_{prefix}_eq : gaussDetCIv S_symp {m} ({ext_fn} {m} ({fam}SrcList.map (polyListCIv S_symp (wRead2D w_{prefix})))) (CFpIv.ofInt S_symp 1) = (true, Q_{prefix}_{m-1}) := by\n"
        f"  rw [srcRows_{prefix}_eq, sub_{prefix}_eq]\n"
        + "".join(
            f"  rw [gaussDetCIv_step_withMults (m := {m - 1 - step}) stG_{prefix}_{step}]\n"
            for step in range(m)
        )
        + "  rfl\n\n"
    )
    cmp_lemma = (
        f"0 < Q_{prefix}_{m-1}.re.lo"
        if expect_sign == "pos"
        else f"Q_{prefix}_{m-1}.re.hi < 0"
    )
    lines.append(f"private lemma sign_{prefix} : {cmp_lemma} := by decide\n\n")
    lines.append(f"end Cert_{prefix}\n\n")
    return "".join(lines), f"Q_{prefix}_{m-1}"


def perm_def_section(name: str, n: int, mapping: list[int]) -> str:
    list_str = "[" + ", ".join(str(x) for x in mapping) + "]"
    return f"""private def {name}List : List ℕ := {list_str}

private def {name}Fn (i : Fin {n}) : Fin {n} := ⟨{name}List.getD i.1 0, by
  have h : ∀ k : Fin {n}, {name}List.getD k.1 0 < {n} := by decide
  exact h i⟩

private lemma {name}Fn_invol : ∀ i : Fin {n}, {name}Fn ({name}Fn i) = i := by decide

private def {name}Perm : Equiv.Perm (Fin {n}) where
  toFun := {name}Fn
  invFun := {name}Fn
  left_inv := {name}Fn_invol
  right_inv := {name}Fn_invol
"""


def build_lean() -> str:
    out: list[str] = []
    out.append(f"""import Matematyka.AtiyahSutcliffe
import Matematyka.AtiyahSutcliffeExtensions
import Matematyka.AtiyahSutcliffe3D36
import Matematyka.AtiyahSutcliffe3D26
import Matematyka.AtiyahSutcliffePlanar35

/-!
# Part II: Symplectic $\\mathrm{{Sp}}(m)$ ($C_m$) and Orthogonal $B_m$ ($\\mathrm{{SO}}(2m+1)$) Disproofs

This module formalizes exact counterexamples to Atiyah–Sutcliffe Conjectures 1 and 2 restricted to:
1. Centrally symmetric symplectic configurations `SymplecticConfig m` ($N = 2m$):
   - Planar $\\mathrm{{Sp}}(20)$ ($N = 40$, $20 \\times 20$ real even subblock).
   - Strictly non-coplanar 3D $\\mathrm{{Sp}}(18)$ ($N = 36$, $18 \\times 18$ real even subblock).
2. Origin-augmented orthogonal $B_{{18}}$ ($\\mathrm{{SO}}(37)$) configurations `OrthogonalBConfig 18`:
   - Strictly non-coplanar 3D $B_{{18}}$ ($N = 37$, $18 \\times 18$ real odd subblock), proving both
     $D_{{37}} = 0$ and linear dependence of the $36$ non-origin Atiyah polynomials.
-/

namespace Matematyka.AtiyahSutcliffeSymplectic

open scoped ComplexConjugate
open Matematyka.MalkounCounterexample
open Matematyka.AtiyahSutcliffe
open Matematyka.AtiyahSutcliffe3D36
open Matematyka.AtiyahSutcliffe3D26
open Matematyka.AtiyahSutcliffePlanar35

/-! ## Section 1: Symplectic and Orthogonal-$B_m$ Configurations and Conjectures -/

section Configs

/-- A centrally symmetric configuration of $2m$ distinct points in $\\mathbb{{R}}^3$
(Malkoun's symplectic $\\mathrm{{Sp}}(m)$ locus $\\mathbf{{X}} = -\\mathbf{{X}}$). -/
structure SymplecticConfig (m : ℕ) where
  p : Fin (2 * m) → Fin 3 → ℝ
  distinct : ∀ i j, i ≠ j → p i ≠ p j
  antipodal : Equiv.Perm (Fin (2 * m))
  involutive : ∀ i, antipodal (antipodal i) = i
  neg_eq : ∀ i k, p (antipodal i) k = -p i k

/-- Coercion from `SymplecticConfig m` to `DistinctPoints (2 * m)`. -/
def symplecticPoints {{m : ℕ}} (c : SymplecticConfig m) : DistinctPoints (2 * m) :=
  ⟨c.p, c.distinct⟩

/-- Atiyah Determinant Nonzero Conjecture restricted to `SymplecticConfig m`. -/
def SymplecticAtiyahDetNonzeroProp (m : ℕ) : Prop :=
  ∀ c : SymplecticConfig m, atiyahDet (symplecticPoints c) ≠ 0

/-- Atiyah Conjecture 1 (Linear Independence) restricted to `SymplecticConfig m`. -/
def SymplecticAtiyahConjecture1Prop (m : ℕ) : Prop :=
  ∀ c : SymplecticConfig m, LinearIndependent ℂ (fun i : Fin (2 * m) =>
    atiyahPoly (fun u v => canonicalSpinor (unitDir (c.p u) (c.p v))) i)

/-- Atiyah–Sutcliffe Conjecture 2 restricted to `SymplecticConfig m`. -/
def SymplecticAtiyahSutcliffeConjecture2Prop (m : ℕ) : Prop :=
  ∀ c : SymplecticConfig m, 1 ≤ ‖atiyahDet (symplecticPoints c)‖

/-- A centrally symmetric configuration of $2m + 1$ distinct points in $\\mathbb{{R}}^3$ with a
designated fixed origin particle (orthogonal $B_m = \\mathrm{{SO}}(2m+1)$ locus). -/
structure OrthogonalBConfig (m : ℕ) where
  p : Fin (2 * m + 1) → Fin 3 → ℝ
  distinct : ∀ i j, i ≠ j → p i ≠ p j
  originIdx : Fin (2 * m + 1)
  origin_eq : ∀ k, p originIdx k = 0
  antipodal : Equiv.Perm (Fin (2 * m + 1))
  involutive : ∀ i, antipodal (antipodal i) = i
  fix_origin : antipodal originIdx = originIdx
  neg_eq : ∀ i k, p (antipodal i) k = -p i k

/-- Coercion from `OrthogonalBConfig m` to `DistinctPoints (2 * m + 1)`. -/
def orthogonalBPoints {{m : ℕ}} (c : OrthogonalBConfig m) : DistinctPoints (2 * m + 1) :=
  ⟨c.p, c.distinct⟩

/-- Atiyah Determinant Nonzero Conjecture restricted to `OrthogonalBConfig m`. -/
def OrthogonalBAtiyahDetNonzeroProp (m : ℕ) : Prop :=
  ∀ c : OrthogonalBConfig m, atiyahDet (orthogonalBPoints c) ≠ 0

/-- Atiyah Conjecture 1 (Linear Independence) restricted to `OrthogonalBConfig m`. -/
def OrthogonalBAtiyahConjecture1Prop (m : ℕ) : Prop :=
  ∀ c : OrthogonalBConfig m, LinearIndependent ℂ (fun i : Fin (2 * m + 1) =>
    atiyahPoly (fun u v => canonicalSpinor (unitDir (c.p u) (c.p v))) i)

/-- Atiyah–Sutcliffe Conjecture 2 restricted to `OrthogonalBConfig m`. -/
def OrthogonalBAtiyahSutcliffeConjecture2Prop (m : ℕ) : Prop :=
  ∀ c : OrthogonalBConfig m, 1 ≤ ‖atiyahDet (orthogonalBPoints c)‖

end Configs

/-! ## Section 2: Disjoint `rotZ`-Paired Parity Subblock Algebra & Canonical Spinor Bridge -/

section SubblockAlgebra

private lemma det_eq_zero_of_rotZ_evenSubblock_det_zero {{m : ℕ}}
    (M : Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ)
    (src : Fin m → Fin (2 * m)) (hsrc_inj : Function.Injective src)
    (τ : Equiv.Perm (Fin (2 * m)))
    (μ : Fin m → ℂ) (hμ_ne : ∀ r, μ r ≠ 0)
    (hdisj : ∀ r s : Fin m, τ (src r) ≠ src r → τ (src r) ≠ src s)
    (hfixed : ∀ r : Fin m, τ (src r) = src r → ∀ c : Fin m, M (src r) ⟨2 * c.1 + 1, by omega⟩ = 0)
    (hpaired : ∀ r : Fin m, τ (src r) ≠ src r →
      ∀ k : Fin (2 * m), M (τ (src r)) k = μ r * (-1 : ℂ) ^ k.1 * M (src r) k)
    (hsub : (Matrix.of fun r c : Fin m => M (src r) ⟨2 * c.1, by omega⟩).det = 0) :
    M.det = 0 := by
  let subEven : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun r c : Fin m => M (src r) ⟨2 * c.1, by omega⟩
  obtain ⟨v, hv_ne, hv_mul⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hsub
  let rowTerm : Fin m → Fin (2 * m) → ℂ := fun r i =>
    if τ (src r) = src r then (if i = src r then v r else 0)
    else (if i = src r then v r / 2 else if i = τ (src r) then (v r / 2) * (μ r)⁻¹ else 0)
  let w : Fin (2 * m) → ℂ := fun i => ∑ r : Fin m, rowTerm r i
  have hv_ex : ∃ r₀ : Fin m, v r₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hv_ne (funext h)
  obtain ⟨r₀, hr₀⟩ := hv_ex
  have hterm_other : ∀ r : Fin m, r ≠ r₀ → rowTerm r (src r₀) = 0 := by
    intro r hr_ne
    have hsrc_ne : src r₀ ≠ src r := fun h => hr_ne (hsrc_inj h).symm
    by_cases hf : τ (src r) = src r
    · simp [rowTerm, hf, hsrc_ne]
    · have hτ_ne : src r₀ ≠ τ (src r) := (hdisj r r₀ hf).symm
      simp [rowTerm, hf, hsrc_ne, hτ_ne]
  have hw_r0 : w (src r₀) ≠ 0 := by
    have hsum : w (src r₀) = rowTerm r₀ (src r₀) :=
      Finset.sum_eq_single r₀ (fun r _ hr => hterm_other r hr) (fun hr => absurd (Finset.mem_univ r₀) hr)
    rw [hsum]
    by_cases hf : τ (src r₀) = src r₀
    · simpa [rowTerm, hf] using hr₀
    · simp only [rowTerm, hf, ↓reduceIte]
      exact div_ne_zero hr₀ (by norm_num)
  have hw_ne : w ≠ 0 := fun h => hw_r0 (by simp [h])
  refine Matrix.exists_vecMul_eq_zero_iff.mp ⟨w, hw_ne, ?_⟩
  ext k
  have hk2 : k.1 < 2 * m := k.2
  have hk_split : (Matrix.vecMul w M) k = ∑ r : Fin m, ∑ i : Fin (2 * m), rowTerm r i * M i k := by
    simp only [Matrix.vecMul, dotProduct, w, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [hk_split]
  have hr_term : ∀ r : Fin m, ∑ i : Fin (2 * m), rowTerm r i * M i k =
      if k.1 % 2 = 0 then v r * M (src r) k else 0 := by
    intro r
    by_cases hf : τ (src r) = src r
    · have hsum : (∑ i : Fin (2 * m), rowTerm r i * M i k) = v r * M (src r) k := by
        simp [rowTerm, hf]
      rw [hsum]
      rcases Nat.mod_two_eq_zero_or_one k.1 with hk0 | hk1
      · simp [hk0]
      · have hklt : k.1 / 2 < m := by omega
        have hk_eq : k = ⟨2 * (k.1 / 2) + 1, by omega⟩ := Fin.ext (by dsimp; omega)
        have hzero : M (src r) k = 0 := by rw [hk_eq]; exact hfixed r hf ⟨k.1 / 2, hklt⟩
        simp [hk1, hzero]
    · have hsrc_ne_τ : src r ≠ τ (src r) := fun h => hf h.symm
      have hsum : (∑ i : Fin (2 * m), rowTerm r i * M i k) =
          (v r / 2) * M (src r) k + ((v r / 2) * (μ r)⁻¹) * M (τ (src r)) k := by
        have ht1 : ∀ i : Fin (2 * m), rowTerm r i * M i k =
            (if i = src r then (v r / 2) * M (src r) k else 0) +
              (if i = τ (src r) then ((v r / 2) * (μ r)⁻¹) * M (τ (src r)) k else 0) := by
          intro i
          by_cases h1 : i = src r
          · subst h1; simp [rowTerm, hf, hsrc_ne_τ]
          · by_cases h2 : i = τ (src r)
            · subst h2; simp [rowTerm, hf]
            · simp [rowTerm, hf, h1, h2]
        simp_rw [ht1, Finset.sum_add_distrib]
        simp
      rw [hsum, hpaired r hf k]
      have hmul_cancel : (v r / 2) * (μ r)⁻¹ * (μ r * (-1 : ℂ) ^ k.1 * M (src r) k) =
          (v r / 2) * (-1 : ℂ) ^ k.1 * M (src r) k := by
        calc
          (v r / 2) * (μ r)⁻¹ * (μ r * (-1 : ℂ) ^ k.1 * M (src r) k)
            = (v r / 2) * ((μ r)⁻¹ * μ r) * ((-1 : ℂ) ^ k.1 * M (src r) k) := by ring
          _ = (v r / 2) * 1 * ((-1 : ℂ) ^ k.1 * M (src r) k) := by rw [inv_mul_cancel₀ (hμ_ne r)]
          _ = (v r / 2) * (-1 : ℂ) ^ k.1 * M (src r) k := by ring
      rw [hmul_cancel]
      rcases Nat.mod_two_eq_zero_or_one k.1 with hk0 | hk1
      · have hpow : (-1 : ℂ) ^ k.1 = 1 := by
          rw [show k.1 = 2 * (k.1 / 2) by omega, pow_mul]; norm_num
        simp only [hk0, ↓reduceIte, hpow, mul_one]
        ring
      · have hpow : (-1 : ℂ) ^ k.1 = -1 := by
          rw [show k.1 = 2 * (k.1 / 2) + 1 by omega, pow_add, pow_mul]; norm_num
        have hnot : k.1 % 2 ≠ 0 := by omega
        simp only [hnot, ↓reduceIte, hpow]
        ring
  simp_rw [hr_term]
  rcases Nat.mod_two_eq_zero_or_one k.1 with hk0 | hk1
  · simp only [hk0, ↓reduceIte]
    let c : Fin m := ⟨k.1 / 2, by omega⟩
    have hkc : k = ⟨2 * c.1, by omega⟩ := Fin.ext (by dsimp [c]; omega)
    rw [hkc]
    exact congr_fun hv_mul c
  · have hnot : k.1 % 2 ≠ 0 := by omega
    simp [hnot]

private lemma det_eq_zero_and_nonOrigin_vecMul_of_rotZ_oddSubblock_det_zero {{m : ℕ}}
    (M : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℂ)
    (orig : Fin (2 * m + 1))
    (src : Fin m → Fin (2 * m + 1)) (hsrc_inj : Function.Injective src)
    (τ : Equiv.Perm (Fin (2 * m + 1)))
    (μ : Fin m → ℂ) (hμ_ne : ∀ r, μ r ≠ 0)
    (horig : ∀ r : Fin m, src r ≠ orig ∧ τ (src r) ≠ orig)
    (hdisj : ∀ r s : Fin m, τ (src r) ≠ src r → τ (src r) ≠ src s)
    (hfixed : ∀ r : Fin m, τ (src r) = src r → ∀ c : Fin (m + 1), M (src r) ⟨2 * c.1, by omega⟩ = 0)
    (hpaired : ∀ r : Fin m, τ (src r) ≠ src r →
      ∀ k : Fin (2 * m + 1), M (τ (src r)) k = μ r * (-1 : ℂ) ^ k.1 * M (src r) k)
    (hsub : (Matrix.of fun r c : Fin m => M (src r) ⟨2 * c.1 + 1, by omega⟩).det = 0) :
    M.det = 0 ∧ ∃ w : Fin (2 * m + 1) → ℂ, w ≠ 0 ∧ w orig = 0 ∧ Matrix.vecMul w M = 0 := by
  let subOdd : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun r c : Fin m => M (src r) ⟨2 * c.1 + 1, by omega⟩
  obtain ⟨v, hv_ne, hv_mul⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hsub
  let rowTerm : Fin m → Fin (2 * m + 1) → ℂ := fun r i =>
    if τ (src r) = src r then (if i = src r then v r else 0)
    else (if i = src r then v r / 2 else if i = τ (src r) then -(v r / 2) * (μ r)⁻¹ else 0)
  let w : Fin (2 * m + 1) → ℂ := fun i => ∑ r : Fin m, rowTerm r i
  have hv_ex : ∃ r₀ : Fin m, v r₀ ≠ 0 := by
    by_contra h; push Not at h; exact hv_ne (funext h)
  obtain ⟨r₀, hr₀⟩ := hv_ex
  have hterm_other : ∀ r : Fin m, r ≠ r₀ → rowTerm r (src r₀) = 0 := by
    intro r hr_ne
    have hsrc_ne : src r₀ ≠ src r := fun h => hr_ne (hsrc_inj h).symm
    by_cases hf : τ (src r) = src r
    · simp [rowTerm, hf, hsrc_ne]
    · have hτ_ne : src r₀ ≠ τ (src r) := (hdisj r r₀ hf).symm
      simp [rowTerm, hf, hsrc_ne, hτ_ne]
  have hw_r0 : w (src r₀) ≠ 0 := by
    have hsum : w (src r₀) = rowTerm r₀ (src r₀) :=
      Finset.sum_eq_single r₀ (fun r _ hr => hterm_other r hr) (fun hr => absurd (Finset.mem_univ r₀) hr)
    rw [hsum]
    by_cases hf : τ (src r₀) = src r₀
    · simpa [rowTerm, hf] using hr₀
    · simp only [rowTerm, hf, ↓reduceIte]
      exact div_ne_zero hr₀ (by norm_num)
  have hw_ne : w ≠ 0 := fun h => hw_r0 (by simp [h])
  have hw_orig : w orig = 0 := by
    refine Finset.sum_eq_zero fun r _ => ?_
    have h1 := (horig r).1.symm
    have h2 := (horig r).2.symm
    by_cases hf : τ (src r) = src r <;> simp [rowTerm, hf, h1, h2]
  have hwM : Matrix.vecMul w M = 0 := by
    ext k
    have hk2 : k.1 < 2 * m + 1 := k.2
    have hk_split : (Matrix.vecMul w M) k = ∑ r : Fin m, ∑ i : Fin (2 * m + 1), rowTerm r i * M i k := by
      simp only [Matrix.vecMul, dotProduct, w, Finset.sum_mul]
      rw [Finset.sum_comm]
    rw [hk_split]
    have hr_term : ∀ r : Fin m, ∑ i : Fin (2 * m + 1), rowTerm r i * M i k =
        if k.1 % 2 = 1 then v r * M (src r) k else 0 := by
      intro r
      by_cases hf : τ (src r) = src r
      · have hsum : (∑ i : Fin (2 * m + 1), rowTerm r i * M i k) = v r * M (src r) k := by
          simp [rowTerm, hf]
        rw [hsum]
        rcases Nat.mod_two_eq_zero_or_one k.1 with hk0 | hk1
        · have hklt : k.1 / 2 < m + 1 := by omega
          have hk_eq : k = ⟨2 * (k.1 / 2), by omega⟩ := Fin.ext (by dsimp; omega)
          have hzero : M (src r) k = 0 := by rw [hk_eq]; exact hfixed r hf ⟨k.1 / 2, hklt⟩
          simp [hk0, hzero]
        · simp [hk1]
      · have hsrc_ne_τ : src r ≠ τ (src r) := fun h => hf h.symm
        have hsum : (∑ i : Fin (2 * m + 1), rowTerm r i * M i k) =
            (v r / 2) * M (src r) k + (-(v r / 2) * (μ r)⁻¹) * M (τ (src r)) k := by
          have ht1 : ∀ i : Fin (2 * m + 1), rowTerm r i * M i k =
              (if i = src r then (v r / 2) * M (src r) k else 0) +
                (if i = τ (src r) then (-(v r / 2) * (μ r)⁻¹) * M (τ (src r)) k else 0) := by
            intro i
            by_cases h1 : i = src r
            · subst h1; simp [rowTerm, hf, hsrc_ne_τ]
            · by_cases h2 : i = τ (src r)
              · subst h2; simp [rowTerm, hf]
              · simp [rowTerm, hf, h1, h2]
          simp_rw [ht1, Finset.sum_add_distrib]
          simp
        rw [hsum, hpaired r hf k]
        have hmul_cancel : (-(v r / 2) * (μ r)⁻¹) * (μ r * (-1 : ℂ) ^ k.1 * M (src r) k) =
            -(v r / 2) * (-1 : ℂ) ^ k.1 * M (src r) k := by
          calc
            (-(v r / 2) * (μ r)⁻¹) * (μ r * (-1 : ℂ) ^ k.1 * M (src r) k)
              = -(v r / 2) * ((μ r)⁻¹ * μ r) * ((-1 : ℂ) ^ k.1 * M (src r) k) := by ring
            _ = -(v r / 2) * 1 * ((-1 : ℂ) ^ k.1 * M (src r) k) := by rw [inv_mul_cancel₀ (hμ_ne r)]
            _ = -(v r / 2) * (-1 : ℂ) ^ k.1 * M (src r) k := by ring
        rw [hmul_cancel]
        rcases Nat.mod_two_eq_zero_or_one k.1 with hk0 | hk1
        · have hpow : (-1 : ℂ) ^ k.1 = 1 := by
            rw [show k.1 = 2 * (k.1 / 2) by omega, pow_mul]; norm_num
          simp [hk0, hpow]
        · have hpow : (-1 : ℂ) ^ k.1 = -1 := by
            rw [show k.1 = 2 * (k.1 / 2) + 1 by omega, pow_add, pow_mul]; norm_num
          simp only [hk1, ↓reduceIte, hpow]
          ring
    simp_rw [hr_term]
    rcases Nat.mod_two_eq_zero_or_one k.1 with hk0 | hk1
    · simp [hk0]
    · simp only [hk1, ↓reduceIte]
      let c : Fin m := ⟨k.1 / 2, by omega⟩
      have hkc : k = ⟨2 * c.1 + 1, by omega⟩ := Fin.ext (by dsimp [c]; omega)
      rw [hkc]
      exact congr_fun hv_mul c
  exact ⟨Matrix.exists_vecMul_eq_zero_iff.mp ⟨w, hw_ne, hwM⟩, w, hw_ne, hw_orig, hwM⟩

private lemma pauliDot_stereoPair' {{a b : Fin 3 → ℝ}} (hab : a ≠ b) (hz : a 2 ≤ b 2) :
    let w : ℂ := (((b 0 - a 0 : ℝ) : ℂ) + Complex.I * ((b 1 - a 1 : ℝ) : ℂ)) /
      (stereoDenomR a b : ℂ)
    (pauliDot (unitDir a b)).mulVec ![1, w] = ![1, w] ∧
      (pauliDot (unitDir b a)).mulVec ![-star w, 1] = ![-star w, 1] := by
  dsimp only
  set dx : ℝ := b 0 - a 0
  set dy : ℝ := b 1 - a 1
  set dz : ℝ := b 2 - a 2
  set r : ℝ := euclidNorm (fun k => b k - a k)
  have hr_pos : 0 < r := euclidNorm_pos_of_ne hab
  have hden_pos : 0 < dz + r := stereoDenomR_pos hab hz
  have hrsq : dx ^ 2 + dy ^ 2 + dz ^ 2 = r ^ 2 := by
    have hnn : 0 ≤ dx ^ 2 + dy ^ 2 + dz ^ 2 := by positivity
    simpa [r, euclidNorm, dx, dy, dz] using (Real.sq_sqrt hnn).symm
  have hrsqC : (dx : ℂ) ^ 2 + (dy : ℂ) ^ 2 + (dz : ℂ) ^ 2 = (r : ℂ) ^ 2 := by exact_mod_cast hrsq
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr_pos.ne'
  have hdenC : ((dz + r : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hden_pos.ne'
  have hdenC' : (dz : ℂ) + (r : ℂ) ≠ 0 := by simpa [Complex.ofReal_add] using hdenC
  have hden_eq : (stereoDenomR a b : ℂ) = ((dz + r : ℝ) : ℂ) := by simp [stereoDenomR, dz, r]
  have hstar_w :
      star ((((dx : ℂ) + Complex.I * (dy : ℂ)) / ((dz + r : ℝ) : ℂ))) =
        ((dx : ℂ) - Complex.I * (dy : ℂ)) / ((dz + r : ℝ) : ℂ) := by
    simp [Complex.conj_ofReal, Complex.conj_I, sub_eq_add_neg]
  have hI2 : (Complex.I : ℂ) ^ 2 = -1 := Complex.I_sq
  constructor
  · ext k; fin_cases k
    · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero,
        Matrix.cons_val_one, pauliDot, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
        unitDir, hden_eq]
      have hd_dx : (b 0 - a 0) = dx := rfl
      have hd_dy : (b 1 - a 1) = dy := rfl
      have hd_dz : (b 2 - a 2) = dz := rfl
      have heu : euclidNorm (fun j => b j - a j) = r := rfl
      rw [hd_dx, hd_dy, hd_dz, heu]
      push_cast
      field_simp [hrC, hdenC']
      calc
        (dz : ℂ) * ((dz : ℂ) + (r : ℂ)) + ((dx : ℂ) - Complex.I * (dy : ℂ)) * ((dx : ℂ) + Complex.I * (dy : ℂ))
          = (dz : ℂ) ^ 2 + (dz : ℂ) * (r : ℂ) + (dx : ℂ) ^ 2 - (Complex.I : ℂ) ^ 2 * (dy : ℂ) ^ 2 := by ring
        _ = ((dx : ℂ) ^ 2 + (dy : ℂ) ^ 2 + (dz : ℂ) ^ 2) + (dz : ℂ) * (r : ℂ) := by rw [hI2]; ring
        _ = (r : ℂ) ^ 2 + (dz : ℂ) * (r : ℂ) := by rw [hrsqC]
        _ = (r : ℂ) * ((dz : ℂ) + (r : ℂ)) := by ring
    · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero,
        Matrix.cons_val_one, pauliDot, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
        unitDir, hden_eq]
      have hd_dx : (b 0 - a 0) = dx := rfl
      have hd_dy : (b 1 - a 1) = dy := rfl
      have hd_dz : (b 2 - a 2) = dz := rfl
      have heu : euclidNorm (fun j => b j - a j) = r := rfl
      rw [hd_dx, hd_dy, hd_dz, heu]
      push_cast
      field_simp [hrC, hdenC']
      ring
  · have hunit_ba : unitDir b a = fun k => -unitDir a b k := by
      ext k
      have he : euclidNorm (fun j => a j - b j) = r := by
        have : (a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2 + (a 2 - b 2) ^ 2 =
            (b 0 - a 0) ^ 2 + (b 1 - a 1) ^ 2 + (b 2 - a 2) ^ 2 := by ring
        simp [r, euclidNorm, this]
      simp only [unitDir, he]
      change (a k - b k) / r = -((b k - a k) / r)
      ring
    ext k; fin_cases k
    · rw [hunit_ba]
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero,
        Matrix.cons_val_one, pauliDot, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
        unitDir, hden_eq, hstar_w]
      have hd_dx : (b 0 - a 0) = dx := rfl
      have hd_dy : (b 1 - a 1) = dy := rfl
      have hd_dz : (b 2 - a 2) = dz := rfl
      have heu : euclidNorm (fun j => b j - a j) = r := rfl
      rw [hd_dx, hd_dy, hd_dz, heu]
      push_cast
      field_simp [hrC, hdenC']
      ring
    · rw [hunit_ba]
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero,
        Matrix.cons_val_one, pauliDot, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
        unitDir, hden_eq, hstar_w]
      have hd_dx : (b 0 - a 0) = dx := rfl
      have hd_dy : (b 1 - a 1) = dy := rfl
      have hd_dz : (b 2 - a 2) = dz := rfl
      have heu : euclidNorm (fun j => b j - a j) = r := rfl
      rw [hd_dx, hd_dy, hd_dz, heu]
      push_cast
      field_simp [hrC, hdenC']
      have hrew : (r : ℂ) * ((dz : ℂ) + (r : ℂ)) =
          (dx : ℂ) ^ 2 - (Complex.I : ℂ) ^ 2 * (dy : ℂ) ^ 2 + (dz : ℂ) ^ 2 + (dz : ℂ) * (r : ℂ) := by
        calc (r : ℂ) * ((dz : ℂ) + (r : ℂ))
          _ = (r : ℂ) ^ 2 + (dz : ℂ) * (r : ℂ) := by ring
          _ = ((dx : ℂ) ^ 2 + (dy : ℂ) ^ 2 + (dz : ℂ) ^ 2) + (dz : ℂ) * (r : ℂ) := by rw [← hrsqC]
          _ = (dx : ℂ) ^ 2 - (-1 : ℂ) * (dy : ℂ) ^ 2 + (dz : ℂ) ^ 2 + (dz : ℂ) * (r : ℂ) := by ring
          _ = (dx : ℂ) ^ 2 - (Complex.I : ℂ) ^ 2 * (dy : ℂ) ^ 2 + (dz : ℂ) ^ 2 + (dz : ℂ) * (r : ℂ) := by rw [hI2]
      rw [hrew]; ring

private lemma not_linearIndependent_nonOrigin_canonical_of_stereo_vecMul_zero {{n : ℕ}}
    (x : DistinctPoints n) (hz : Monotone (fun i => x.1 i 2))
    (orig : Fin n) (w : Fin n → ℂ)
    (hw_ne : w ≠ 0) (hw_orig : w orig = 0)
    (hwM : Matrix.vecMul w (atiyahMat (stereoSpinor x.1)) = 0) :
    ¬ LinearIndependent ℂ (fun i : {{j : Fin n // j ≠ orig}} =>
      atiyahPoly (fun u v => canonicalSpinor (unitDir (x.1 u) (x.1 v))) i.1) := by
  let ψ0 := stereoSpinor x.1
  let ψ := fun u v => canonicalSpinor (unitDir (x.1 u) (x.1 v))
  have hdeg : ∀ i : Fin n, (atiyahPoly ψ0 i).natDegree ≤ n - 1 := by
    intro i
    have hcard : (Finset.univ.erase i).card = n - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_fin]
    unfold atiyahPoly
    calc
      (∏ j ∈ Finset.univ.erase i, (Polynomial.C (ψ0 i j 0) + Polynomial.C (ψ0 i j 1) * Polynomial.X)).natDegree
        ≤ ∑ j ∈ Finset.univ.erase i, (Polynomial.C (ψ0 i j 0) + Polynomial.C (ψ0 i j 1) * Polynomial.X).natDegree :=
          Polynomial.natDegree_prod_le _ _
      _ ≤ ∑ _j ∈ Finset.univ.erase i, 1 := by
          refine Finset.sum_le_sum fun j _ => ?_
          exact le_trans (Polynomial.natDegree_add_le _ _) (max_le (by simp) (by
            by_cases h1 : ψ0 i j 1 = 0
            · simp [h1]
            · simp [Polynomial.natDegree_C_mul_X _ h1]))
      _ = n - 1 := by simp [hcard]
  have hsum_stereo : ∑ i : {{j : Fin n // j ≠ orig}}, w i.1 • atiyahPoly ψ0 i.1 = 0 := by
    ext k
    change (Polynomial.lcoeff ℂ k) (∑ i : {{j : Fin n // j ≠ orig}}, w i.1 • atiyahPoly ψ0 i.1) = 0
    rw [map_sum]
    simp only [map_smul, Polynomial.lcoeff_apply, smul_eq_mul]
    by_cases hk : k < n
    · let kc : Fin n := ⟨k, hk⟩
      have hsub : (∑ i : {{j : Fin n // j ≠ orig}}, w i.1 * (atiyahPoly ψ0 i.1).coeff k) =
          ∑ i : Fin n, w i * (atiyahMat ψ0) i kc := by
        rw [← Finset.add_sum_erase Finset.univ (fun i => w i * (atiyahMat ψ0) i kc) (Finset.mem_univ orig)]
        have hor0 : w orig * (atiyahMat ψ0) orig kc = 0 := by simp [hw_orig]
        rw [hor0, zero_add]
        refine Finset.sum_bij (fun i _ => i.1) (fun i _ => Finset.mem_erase.mpr ⟨i.2, Finset.mem_univ _⟩)
          (fun _ _ _ _ h => Subtype.ext h) ?_ (fun _ _ => rfl)
        intro b hb
        exact ⟨⟨b, (Finset.mem_erase.mp hb).1⟩, Finset.mem_univ _, rfl⟩
      rw [hsub]
      exact congr_fun hwM kc
    · have hk_gt : ∀ i : {{j : Fin n // j ≠ orig}}, (atiyahPoly ψ0 i.1).coeff k = 0 := by
        intro i
        have hi2 : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le i.1.1) i.1.2
        exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hdeg i.1) (by omega))
      simp [hk_gt]
  have hcol : ∀ i j : Fin n, i ≠ j → ∃ c : ℂ, c ≠ 0 ∧ ∀ k, ψ i j k = c * ψ0 i j k := by
    intro i j hij
    have hψ_pos := isPosSpinor_canonicalSpinor (unitDir_norm_sq (x.2 i j hij))
    have h0_ne : ψ0 i j 0 ≠ 0 ∨ ψ0 i j 1 ≠ 0 := by
      rcases lt_trichotomy i j with hlt | rfl | hgt
      · left; simp [ψ0, stereoSpinor, hij, hlt]
      · exact absurd rfl hij
      · right; simp [ψ0, stereoSpinor, hij, not_lt_of_gt hgt]
    have h0_mul : (pauliDot (unitDir (x.1 i) (x.1 j))).mulVec (ψ0 i j) = ψ0 i j := by
      rcases lt_trichotomy i j with hlt | rfl | hgt
      · simp only [ψ0, stereoSpinor, hij, ↓reduceIte, hlt]
        exact (pauliDot_stereoPair' (x.2 i j hij) (hz hlt.le)).1
      · exact absurd rfl hij
      · have hnot : ¬ i < j := not_lt_of_gt hgt
        simp only [ψ0, stereoSpinor, hij, ↓reduceIte, hnot]
        exact (pauliDot_stereoPair' (x.2 j i hij.symm) (hz hgt.le)).2
    have hom : omega (ψ0 i j) (ψ i j) = 0 := omega_eq_zero_of_mulVec h0_mul hψ_pos.2
    have heq : ψ0 i j 0 * ψ i j 1 = ψ0 i j 1 * ψ i j 0 := sub_eq_zero.mp hom
    have hψ_nz : ψ i j 0 ≠ 0 ∨ ψ i j 1 ≠ 0 := by
      by_contra h; push Not at h
      have h1 := hψ_pos.1
      change ‖ψ i j 0‖ ^ 2 + ‖ψ i j 1‖ ^ 2 = 1 at h1
      rw [h.1, h.2] at h1; norm_num at h1
    rcases h0_ne with h0 | h1
    · refine ⟨ψ i j 0 / ψ0 i j 0, ?_, fun k => ?_⟩
      · intro hc
        have hc0 : ψ i j 0 = 0 := (div_eq_zero_iff.mp hc).resolve_right h0
        rw [hc0, mul_zero] at heq
        have hc1 : ψ i j 1 = 0 := (mul_eq_zero.mp heq).resolve_left h0
        rcases hψ_nz with h | h <;> exact h (by first | exact hc0 | exact hc1)
      · fin_cases k <;> dsimp
        · field_simp [h0]
        · field_simp [h0]; linear_combination heq
    · refine ⟨ψ i j 1 / ψ0 i j 1, ?_, fun k => ?_⟩
      · intro hc
        have hc1 : ψ i j 1 = 0 := (div_eq_zero_iff.mp hc).resolve_right h1
        rw [hc1, mul_zero] at heq
        have hc0 : ψ i j 0 = 0 := (mul_eq_zero.mp heq.symm).resolve_left h1
        rcases hψ_nz with h | h <;> exact h (by first | exact hc0 | exact hc1)
      · fin_cases k <;> dsimp
        · field_simp [h1]; linear_combination -heq
        · field_simp [h1]
  let cFull : Fin n → Fin n → ℂ := fun i j =>
    if hij : i = j then 1 else Classical.choose (hcol i j hij)
  have hcFull_ne : ∀ i j, cFull i j ≠ 0 := by
    intro i j; by_cases hij : i = j <;> simp only [cFull, hij, ↓reduceDIte]
    · exact one_ne_zero
    · exact (Classical.choose_spec (hcol i j hij)).1
  have hcFull_eq : ∀ i j, i ≠ j → ∀ k, ψ i j k = cFull i j * ψ0 i j k := by
    intro i j hij k; simp only [cFull, hij, ↓reduceDIte]
    exact (Classical.choose_spec (hcol i j hij)).2 k
  let α : Fin n → ℂ := fun i => ∏ j ∈ Finset.univ.erase i, cFull i j
  have hα_ne : ∀ i, α i ≠ 0 := fun i => Finset.prod_ne_zero_iff.mpr fun j _ => hcFull_ne i j
  have hpoly_scale : ∀ i, atiyahPoly ψ i = Polynomial.C (α i) * atiyahPoly ψ0 i := by
    intro i
    simp only [atiyahPoly]
    calc
      ∏ j ∈ Finset.univ.erase i, (Polynomial.C (ψ i j 0) + Polynomial.C (ψ i j 1) * Polynomial.X)
        = ∏ j ∈ Finset.univ.erase i,
            (Polynomial.C (cFull i j) * (Polynomial.C (ψ0 i j 0) + Polynomial.C (ψ0 i j 1) * Polynomial.X)) := by
          refine Finset.prod_congr rfl fun j hj => ?_
          have hij : i ≠ j := (Finset.mem_erase.mp hj).1.symm
          rw [hcFull_eq i j hij 0, hcFull_eq i j hij 1, map_mul, map_mul]
          ring
      _ = (∏ j ∈ Finset.univ.erase i, Polynomial.C (cFull i j)) * atiyahPoly ψ0 i := by
          rw [Finset.prod_mul_distrib]; rfl
      _ = Polynomial.C (α i) * atiyahPoly ψ0 i := by rw [← map_prod Polynomial.C]
  intro hli
  rw [Fintype.linearIndependent_iff] at hli
  have hzero : ∑ i : {{j : Fin n // j ≠ orig}}, (w i.1 * (α i.1)⁻¹) • atiyahPoly ψ i.1 = 0 := by
    calc
      ∑ i : {{j : Fin n // j ≠ orig}}, (w i.1 * (α i.1)⁻¹) • atiyahPoly ψ i.1
        = ∑ i : {{j : Fin n // j ≠ orig}}, w i.1 • atiyahPoly ψ0 i.1 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hpoly_scale i.1, Polynomial.smul_eq_C_mul, Polynomial.smul_eq_C_mul, ← mul_assoc,
            ← map_mul Polynomial.C, mul_assoc (w i.1) (α i.1)⁻¹ (α i.1), inv_mul_cancel₀ (hα_ne i.1), mul_one]
      _ = 0 := hsum_stereo
  have hw_ex : ∃ i₀ : Fin n, w i₀ ≠ 0 := by
    by_contra h; push Not at h; exact hw_ne (funext h)
  obtain ⟨i₀, hi₀⟩ := hw_ex
  have hi₀_ne : i₀ ≠ orig := fun h => hi₀ (by simp [h, hw_orig])
  have hc := hli (fun i => w i.1 * (α i.1)⁻¹) hzero ⟨i₀, hi₀_ne⟩
  exact (mul_ne_zero hi₀ (inv_ne_zero (hα_ne i₀))) hc

private lemma subDet_im_eq_zero_of_perm_conj {{m : ℕ}}
    (sub : Matrix (Fin m) (Fin m) ℂ)
    (σ : Equiv.Perm (Fin m)) (f : Fin m → ℂ)
    (hprod : (∏ r : Fin m, f r) * (Equiv.Perm.sign σ : ℂ) = 1)
    (hconj : ∀ r c : Fin m, starRingEnd ℂ (sub (σ r) c) = f r * sub r c) :
    sub.det.im = 0 := by
  have hmat : (starRingEnd ℂ).mapMatrix (sub.submatrix σ id) = Matrix.of (fun r c => f r * sub r c) := by
    ext r c; exact hconj r c
  have hdet_lhs : ((starRingEnd ℂ).mapMatrix (sub.submatrix σ id)).det =
      (Equiv.Perm.sign σ : ℂ) * starRingEnd ℂ sub.det := by
    rw [← RingHom.map_det, Matrix.det_permute σ sub]
    simp
  have hdet_rhs : (Matrix.of (fun r c => f r * sub r c)).det = (∏ r : Fin m, f r) * sub.det := by
    have hmul : Matrix.of (fun r c => f r * sub r c) = Matrix.diagonal f * sub := by
      ext r c; simp [Matrix.mul_apply, Matrix.diagonal]
    rw [hmul, Matrix.det_mul, Matrix.det_diagonal]
  have heq : (Equiv.Perm.sign σ : ℂ) * starRingEnd ℂ sub.det = (∏ r : Fin m, f r) * sub.det := by
    rw [← hdet_lhs, hmat, hdet_rhs]
  have hself : starRingEnd ℂ sub.det = sub.det := by
    have hsgn_inv : (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign σ : ℂ) = 1 := by
      have : (Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign σ : ℤ) = 1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
      exact_mod_cast this
    calc
      starRingEnd ℂ sub.det = (Equiv.Perm.sign σ : ℂ) * ((Equiv.Perm.sign σ : ℂ) * starRingEnd ℂ sub.det) := by
        rw [← mul_assoc, hsgn_inv, one_mul]
      _ = (Equiv.Perm.sign σ : ℂ) * ((∏ r : Fin m, f r) * sub.det) := by rw [heq]
      _ = ((∏ r : Fin m, f r) * (Equiv.Perm.sign σ : ℂ)) * sub.det := by ring
      _ = sub.det := by rw [hprod, one_mul]
  exact Complex.conj_eq_iff_im.mp hself

end SubblockAlgebra

/-! ## Section 3: Unified `rotZ` Parity, `yRefl` Conjugation, Continuity, and Certified `CFpIv` Helpers -/

section GeometricSymmetries

private lemma vec3_val0 {{α : Type*}} (x y z : α) : (![x, y, z] : Fin 3 → α) 0 = x := rfl
private lemma vec3_val1 {{α : Type*}} (x y z : α) : (![x, y, z] : Fin 3 → α) 1 = y := rfl
private lemma vec3_val2 {{α : Type*}} (x y z : α) : (![x, y, z] : Fin 3 → α) 2 = z := rfl

private lemma coeff_comp_neg_X' (P : Polynomial ℂ) (k : ℕ) :
    (P.comp (-Polynomial.X)).coeff k = (-1 : ℂ) ^ k * P.coeff k := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.add_comp, Polynomial.coeff_add, hp, hq]
    ring
  | monomial n a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.mul_comp, Polynomial.C_comp,
      Polynomial.pow_comp, Polynomial.X_comp, neg_eq_neg_one_mul, mul_pow]
    have hneg1 : (-1 : Polynomial ℂ) ^ n = Polynomial.C ((-1 : ℂ) ^ n) := by
      rw [← map_one Polynomial.C, ← map_neg Polynomial.C, ← map_pow Polynomial.C]
    rw [hneg1]
    have hmul : Polynomial.C a * (Polynomial.C ((-1 : ℂ) ^ n) * Polynomial.X ^ n) =
        Polynomial.C (a * (-1 : ℂ) ^ n) * Polynomial.X ^ n := by
      rw [← mul_assoc, map_mul]
    rw [hmul, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X_pow]
    by_cases hnk : n = k
    · subst hnk; simp [mul_comm]
    · simp [Ne.symm hnk]

private lemma stereoDenomR_symm_negXY {{a b : Fin 3 → ℝ}} :
    stereoDenomR ![-a 0, -a 1, a 2] ![-b 0, -b 1, b 2] = stereoDenomR a b := by
  unfold stereoDenomR euclidNorm
  simp only [vec3_val0, vec3_val1, vec3_val2]
  congr 1; congr 1; ring

private lemma stereoDenomR_symm_yRefl {{a b : Fin 3 → ℝ}} :
    stereoDenomR ![a 0, -a 1, a 2] ![b 0, -b 1, b 2] = stereoDenomR a b := by
  unfold stereoDenomR euclidNorm
  simp only [vec3_val0, vec3_val1, vec3_val2]
  congr 1; congr 1; ring

private lemma stereoSlope_rotZ {{N : ℕ}} (p : Fin N → Fin 3 → ℝ) (τ : Equiv.Perm (Fin N))
    (hrot : ∀ i, p (τ i) = ![-p i 0, -p i 1, p i 2]) (i j : Fin N) :
    stereoSlope p (τ i) (τ j) = -stereoSlope p i j := by
  unfold stereoSlope
  have hd : stereoDenomR (p (τ i)) (p (τ j)) = stereoDenomR (p i) (p j) := by
    rw [hrot i, hrot j]; exact stereoDenomR_symm_negXY
  rw [hd, hrot i, hrot j]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  push_cast
  ring

private lemma stereoSlope_yRefl {{N : ℕ}} (p : Fin N → Fin 3 → ℝ) (σ : Equiv.Perm (Fin N))
    (hy : ∀ i, p (σ i) = ![p i 0, -p i 1, p i 2]) (i j : Fin N) :
    stereoSlope p (σ i) (σ j) = star (stereoSlope p i j) := by
  unfold stereoSlope
  have hd : stereoDenomR (p (σ i)) (p (σ j)) = stereoDenomR (p i) (p j) := by
    rw [hy i, hy j]; exact stereoDenomR_symm_yRefl
  rw [hd, hy i, hy j]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, star_div₀, Complex.star_def,
    Complex.conj_ofReal, star_add, star_mul, Complex.conj_I]
  push_cast
  ring

private lemma atiyahPoly_rotZ_fixed {{N : ℕ}} (p : Fin N → Fin 3 → ℝ) (τ : Equiv.Perm (Fin N))
    (hτ : ∀ i, τ (τ i) = i) (hrot : ∀ i, p (τ i) = ![-p i 0, -p i 1, p i 2])
    (i : Fin N) (hfix : τ i = i) (hside : ∀ j, j ≠ i → (τ j < i ↔ j < i)) :
    atiyahPoly (stereoSpinor p) i =
      Polynomial.C ((-1 : ℂ) ^ i.1) * (atiyahPoly (stereoSpinor p) i).comp (-Polynomial.X) := by
  have hcomp : (atiyahPoly (stereoSpinor p) i).comp (-Polynomial.X) =
      ∏ j ∈ Finset.univ.erase i,
        ((Polynomial.C (stereoSpinor p i j 0) + Polynomial.C (stereoSpinor p i j 1) * (-Polynomial.X))) := by
    simp [atiyahPoly, Polynomial.prod_comp]
  rw [hcomp]
  have hbij : atiyahPoly (stereoSpinor p) i =
      ∏ j ∈ Finset.univ.erase i,
        ((if j < i then (-1 : Polynomial ℂ) else 1) *
          (Polynomial.C (stereoSpinor p i j 0) + Polynomial.C (stereoSpinor p i j 1) * (-Polynomial.X))) := by
    unfold atiyahPoly
    refine Finset.prod_bij (fun j _ => τ j) ?_ ?_ ?_ ?_
    · intro j hj
      exact Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hj).1 (by
        have := congr_arg τ h; rwa [hτ, hfix] at this), Finset.mem_univ _⟩
    · intro j₁ _ j₂ _ heq; exact τ.injective heq
    · intro b hb
      refine ⟨τ b, Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hb).1 (by
        have := congr_arg τ h; rwa [hτ, hfix] at this), Finset.mem_univ _⟩, hτ b⟩
    · intro j hj
      have hj_ne : j ≠ i := (Finset.mem_erase.mp hj).1
      have hτj_ne : τ j ≠ i := fun h => hj_ne (by have := congr_arg τ h; rwa [hτ, hfix] at this)
      have hside_j := hside j hj_ne
      by_cases hlt : j < i
      · have hτlt : τ j < i := hside_j.mpr hlt
        simp only [stereoSpinor, hj_ne.symm, hτj_ne.symm, ↓reduceIte, not_lt_of_gt hlt,
          not_lt_of_gt hτlt, hτlt, Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [← hfix, stereoSlope_rotZ p τ hrot j i, hfix]
        simp only [star_neg, map_neg]
        ring
      · have hij : i < j := lt_of_le_of_ne (not_lt.mp hlt) hj_ne.symm
        have hτnlt : ¬ τ j < i := fun h => hlt (hside_j.mp h)
        have hiτj : i < τ j := lt_of_le_of_ne (not_lt.mp hτnlt) hτj_ne.symm
        simp only [stereoSpinor, hj_ne.symm, hτj_ne.symm, ↓reduceIte, hij, hiτj, hτnlt,
          Matrix.cons_val_zero, Matrix.cons_val_one]
        have heq_w := stereoSlope_rotZ p τ hrot i j
        rw [hfix] at heq_w
        rw [heq_w]
        simp only [map_neg]
        ring
  rw [hbij, Finset.prod_mul_distrib]
  congr 1
  rw [← Finset.prod_filter_mul_prod_filter_not (Finset.univ.erase i) (fun j => j < i)]
  have h1 : (Finset.univ.filter (fun j : Fin N => j < i)) = (Finset.univ.erase i).filter (fun j => j < i) := by
    ext j; constructor <;> intro hj
    · exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨ne_of_lt (Finset.mem_filter.mp hj).2, Finset.mem_univ _⟩, (Finset.mem_filter.mp hj).2⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
  have hcard : (Finset.univ.filter (fun j : Fin N => j < i)).card = i.1 := by
    have hb : (Finset.univ.filter (fun j : Fin N => j < i)).card = (Finset.range i.1).card := by
      refine Finset.card_bij (fun j _ => j.1) (fun j hj => Finset.mem_range.mpr (Finset.mem_filter.mp hj).2)
        (fun _ _ _ _ h => Fin.ext h) (fun a ha => ⟨⟨a, lt_trans (Finset.mem_range.mp ha) i.2⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_range.mp ha⟩, rfl⟩)
    rw [hb, Finset.card_range]
  have hpos : (∏ j ∈ (Finset.univ.erase i).filter (fun j => j < i),
      if j < i then (-1 : Polynomial ℂ) else 1) = (-1 : Polynomial ℂ) ^ i.1 := by
    rw [← h1]
    calc
      (∏ j ∈ Finset.univ.filter (fun j : Fin N => j < i), if j < i then (-1 : Polynomial ℂ) else 1)
        = ∏ _j ∈ Finset.univ.filter (fun j : Fin N => j < i), (-1 : Polynomial ℂ) :=
          Finset.prod_congr rfl fun j hj => by simp [(Finset.mem_filter.mp hj).2]
      _ = (-1 : Polynomial ℂ) ^ (Finset.univ.filter (fun j : Fin N => j < i)).card := Finset.prod_const _
      _ = (-1 : Polynomial ℂ) ^ i.1 := by rw [hcard]
  have hneg : (∏ j ∈ (Finset.univ.erase i).filter (fun j => ¬ j < i),
      if j < i then (-1 : Polynomial ℂ) else 1) = 1 :=
    Finset.prod_eq_one fun j hj => by simp [(Finset.mem_filter.mp hj).2]
  rw [hpos, hneg, mul_one]
  simp [map_pow]

private lemma stereoSlope_normSq_eq_one_of_dz_zero {{N : ℕ}} (p : Fin N → Fin 3 → ℝ)
    {{a b : Fin N}} (hp : p a ≠ p b) (hz : p b 2 = p a 2) :
    stereoSlope p a b * star (stereoSlope p a b) = 1 := by
  unfold stereoSlope stereoDenomR
  set dx : ℝ := p b 0 - p a 0
  set dy : ℝ := p b 1 - p a 1
  have hdz : p b 2 - p a 2 = 0 := sub_eq_zero.mpr hz
  have hr_pos : 0 < euclidNorm (fun k => p b k - p a k) := euclidNorm_pos_of_ne hp
  have hrsq : dx ^ 2 + dy ^ 2 = euclidNorm (fun k => p b k - p a k) ^ 2 := by
    have hnn : 0 ≤ (p b 0 - p a 0) ^ 2 + (p b 1 - p a 1) ^ 2 + (p b 2 - p a 2) ^ 2 := by positivity
    have h0 := (Real.sq_sqrt hnn).symm
    change dx ^ 2 + dy ^ 2 + (p b 2 - p a 2) ^ 2 = euclidNorm (fun k => p b k - p a k) ^ 2 at h0
    rw [hdz] at h0; linarith
  have hrsqC : (dx : ℂ) ^ 2 + (dy : ℂ) ^ 2 = (euclidNorm (fun k => p b k - p a k) : ℂ) ^ 2 := by
    exact_mod_cast hrsq
  have hrC : (euclidNorm (fun k => p b k - p a k) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hr_pos.ne'
  rw [hdz, zero_add]
  have hconj : star (((dx : ℂ) + Complex.I * (dy : ℂ)) / (euclidNorm (fun k => p b k - p a k) : ℂ)) =
      ((dx : ℂ) - Complex.I * (dy : ℂ)) / (euclidNorm (fun k => p b k - p a k) : ℂ) := by
    simp [Complex.conj_ofReal, Complex.conj_I, sub_eq_add_neg]
  have heu_dy : (((dx : ℂ) + Complex.I * (dy : ℂ)) / (euclidNorm (fun k => p b k - p a k) : ℂ)) *
      star (((dx : ℂ) + Complex.I * (dy : ℂ)) / (euclidNorm (fun k => p b k - p a k) : ℂ)) = 1 := by
    rw [hconj]
    field_simp [hrC]
    calc
      ((dx : ℂ) + Complex.I * (dy : ℂ)) * ((dx : ℂ) - Complex.I * (dy : ℂ))
        = (dx : ℂ) ^ 2 - (Complex.I : ℂ) ^ 2 * (dy : ℂ) ^ 2 := by ring
      _ = (dx : ℂ) ^ 2 + (dy : ℂ) ^ 2 := by rw [Complex.I_sq]; ring
      _ = (euclidNorm (fun k => p b k - p a k) : ℂ) ^ 2 := hrsqC
  simpa [dx, dy] using heu_dy

private lemma atiyahPoly_rotZ_pair {{N : ℕ}} (p : Fin N → Fin 3 → ℝ)
    (hp : ∀ u v, u ≠ v → p u ≠ p v)
    (τ : Equiv.Perm (Fin N)) (hτ : ∀ u, τ (τ u) = u)
    (hrot : ∀ u, p (τ u) = ![-p u 0, -p u 1, p u 2])
    (i : Fin N) (hlt : i < τ i) (hz : p (τ i) 2 = p i 2)
    (hside : ∀ j, j ≠ i → j ≠ τ i → (τ j < τ i ↔ j < i)) :
    atiyahPoly (stereoSpinor p) (τ i) =
      Polynomial.C ((-1 : ℂ) ^ i.1 * (-star (stereoSlope p i (τ i)))) *
        (atiyahPoly (stereoSpinor p) i).comp (-Polynomial.X) := by
  have hi_ne : i ≠ τ i := ne_of_lt hlt
  have hcomp : (atiyahPoly (stereoSpinor p) i).comp (-Polynomial.X) =
      ∏ j ∈ Finset.univ.erase i,
        ((Polynomial.C (stereoSpinor p i j 0) + Polynomial.C (stereoSpinor p i j 1) * (-Polynomial.X))) := by
    simp [atiyahPoly, Polynomial.prod_comp]
  rw [hcomp]
  let fBij : Fin N → Fin N := fun j => if j = τ i then i else τ j
  let fac : Fin N → Polynomial ℂ := fun j =>
    if j = τ i then Polynomial.C (-star (stereoSlope p i (τ i)))
    else if j < i then (-1 : Polynomial ℂ)
    else 1
  have hmul_eq : atiyahPoly (stereoSpinor p) (τ i) =
      ∏ j ∈ Finset.univ.erase i,
        (fac j * (Polynomial.C (stereoSpinor p i j 0) + Polynomial.C (stereoSpinor p i j 1) * (-Polynomial.X))) := by
    unfold atiyahPoly
    refine (Finset.prod_bij (fun j _ => fBij j) ?_ ?_ ?_ ?_).symm
    · intro j hj
      have hj_ne : j ≠ i := (Finset.mem_erase.mp hj).1
      by_cases hjτ : j = τ i
      · simp [fBij, hjτ, hi_ne]
      · simp only [fBij, hjτ, ↓reduceIte]
        exact Finset.mem_erase.mpr ⟨fun h => hj_ne (τ.injective h), Finset.mem_univ _⟩
    · intro j₁ _ j₂ _ heq
      by_cases c1 : j₁ = τ i <;> by_cases c2 : j₂ = τ i <;> simp only [fBij, c1, c2, ↓reduceIte] at heq
      · rw [c1, c2]
      · exact absurd (by have := congr_arg τ heq; rw [hτ] at this; exact this.symm) c2
      · exact absurd (by have := congr_arg τ heq; rw [hτ] at this; exact this) c1
      · exact τ.injective heq
    · intro b hb
      have hb_ne : b ≠ τ i := (Finset.mem_erase.mp hb).1
      by_cases hbi : b = i
      · exact ⟨τ i, Finset.mem_erase.mpr ⟨hi_ne.symm, Finset.mem_univ _⟩, by simp [fBij, hbi]⟩
      · refine ⟨τ b, Finset.mem_erase.mpr ⟨fun h => hb_ne (by
          have := congr_arg τ h; rwa [hτ] at this), Finset.mem_univ _⟩, ?_⟩
        have hτb_ne : τ b ≠ τ i := fun h => hbi (τ.injective h)
        simp [fBij, hτb_ne, hτ b]
    · intro j hj
      have hj_ne : j ≠ i := (Finset.mem_erase.mp hj).1
      by_cases hjτ : j = τ i
      · subst hjτ
        simp only [fBij, ↓reduceIte, fac, stereoSpinor, hi_ne, hi_ne.symm, hlt,
          not_lt_of_gt hlt, Matrix.cons_val_zero, Matrix.cons_val_one, map_one]
        have hns := stereoSlope_normSq_eq_one_of_dz_zero p (hp i (τ i) hi_ne) hz
        have hpol : Polynomial.C (-star (stereoSlope p i (τ i))) * (1 + Polynomial.C (stereoSlope p i (τ i)) * (-Polynomial.X)) =
            Polynomial.C (-star (stereoSlope p i (τ i))) + 1 * Polynomial.X := by
          calc
            Polynomial.C (-star (stereoSlope p i (τ i))) * (1 + Polynomial.C (stereoSlope p i (τ i)) * (-Polynomial.X))
              = Polynomial.C (-star (stereoSlope p i (τ i))) +
                  Polynomial.C (stereoSlope p i (τ i) * star (stereoSlope p i (τ i))) * Polynomial.X := by
                simp only [map_mul, map_neg]; ring
            _ = Polynomial.C (-star (stereoSlope p i (τ i))) + 1 * Polynomial.X := by
                rw [hns, map_one, one_mul]
        exact hpol
      · have hτj_ne : τ j ≠ τ i := fun h => hj_ne (τ.injective h)
        have hside_j := hside j hj_ne hjτ
        by_cases hjlt : j < i
        · have hτlt : τ j < τ i := hside_j.mpr hjlt
          simp only [fBij, hjτ, ↓reduceIte, fac, hjlt, stereoSpinor, hj_ne.symm, hτj_ne.symm,
            not_lt_of_gt hjlt, not_lt_of_gt hτlt, Matrix.cons_val_zero, Matrix.cons_val_one]
          have heq_w := stereoSlope_rotZ p τ hrot j i
          rw [heq_w]
          simp only [star_neg, neg_neg, map_neg]
          ring
        · have hij : i < j := lt_of_le_of_ne (not_lt.mp hjlt) hj_ne.symm
          have hτnlt : ¬ τ j < τ i := fun h => hjlt (hside_j.mp h)
          have hτlt_ij : τ i < τ j := lt_of_le_of_ne (not_lt.mp hτnlt) hτj_ne.symm
          simp only [fBij, hjτ, ↓reduceIte, fac, hjlt, stereoSpinor, hj_ne.symm, hτj_ne.symm,
            hij, hτlt_ij, Matrix.cons_val_zero, Matrix.cons_val_one]
          have heq_w := stereoSlope_rotZ p τ hrot i j
          rw [heq_w]
          simp only [map_neg]
          ring
  rw [hmul_eq, Finset.prod_mul_distrib]
  congr 1
  rw [← Finset.prod_erase_mul (Finset.univ.erase i) fac (Finset.mem_erase.mpr ⟨hi_ne.symm, Finset.mem_univ _⟩)]
  have hτ_fac : fac (τ i) = Polynomial.C (-star (stereoSlope p i (τ i))) := by simp [fac]
  have hrest_fac : (∏ j ∈ (Finset.univ.erase i).erase (τ i), fac j) = Polynomial.C ((-1 : ℂ) ^ i.1) := by
    have hcongr : (∏ j ∈ (Finset.univ.erase i).erase (τ i), fac j) =
        ∏ j ∈ (Finset.univ.erase i).erase (τ i), if j < i then (-1 : Polynomial ℂ) else 1 := by
      refine Finset.prod_congr rfl fun j hj => ?_
      simp [fac, (Finset.mem_erase.mp hj).1]
    rw [hcongr, ← Finset.prod_filter_mul_prod_filter_not ((Finset.univ.erase i).erase (τ i)) (fun j => j < i)]
    have hflt : ((Finset.univ.erase i).erase (τ i)).filter (fun j => j < i) =
        Finset.univ.filter (fun j : Fin N => j < i) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
      constructor
      · intro h; exact h.2
      · intro hltj; refine ⟨⟨fun he => (he ▸ lt_trans hltj hlt).false, ne_of_lt hltj⟩, hltj⟩
    have hcard : (Finset.univ.filter (fun j : Fin N => j < i)).card = i.1 := by
      have hb : (Finset.univ.filter (fun j : Fin N => j < i)).card = (Finset.range i.1).card := by
        refine Finset.card_bij (fun j _ => j.1) (fun j hj => Finset.mem_range.mpr (Finset.mem_filter.mp hj).2)
          (fun _ _ _ _ h => Fin.ext h) (fun a ha => ⟨⟨a, lt_trans (Finset.mem_range.mp ha) i.2⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_range.mp ha⟩, rfl⟩)
      rw [hb, Finset.card_range]
    have hp1 : (∏ j ∈ ((Finset.univ.erase i).erase (τ i)).filter (fun j => j < i),
        if j < i then (-1 : Polynomial ℂ) else 1) = (-1 : Polynomial ℂ) ^ i.1 := by
      rw [hflt]
      calc
        (∏ j ∈ Finset.univ.filter (fun j : Fin N => j < i), if j < i then (-1 : Polynomial ℂ) else 1)
          = ∏ _j ∈ Finset.univ.filter (fun j : Fin N => j < i), (-1 : Polynomial ℂ) :=
            Finset.prod_congr rfl fun j hj => by simp [(Finset.mem_filter.mp hj).2]
        _ = (-1 : Polynomial ℂ) ^ (Finset.univ.filter (fun j : Fin N => j < i)).card := Finset.prod_const _
        _ = (-1 : Polynomial ℂ) ^ i.1 := by rw [hcard]
    have hp2 : (∏ j ∈ ((Finset.univ.erase i).erase (τ i)).filter (fun j => ¬ j < i),
        if j < i then (-1 : Polynomial ℂ) else 1) = 1 :=
      Finset.prod_eq_one fun j hj => by simp [(Finset.mem_filter.mp hj).2]
    rw [hp1, hp2, mul_one]
    simp [map_pow]
  rw [hrest_fac, hτ_fac, map_mul]

private lemma atiyahPoly_yRefl_fixed {{N : ℕ}} (p : Fin N → Fin 3 → ℝ) (σ : Equiv.Perm (Fin N))
    (hσ : ∀ u, σ (σ u) = u) (hy : ∀ u, p (σ u) = ![p u 0, -p u 1, p u 2])
    (i : Fin N) (hfix : σ i = i) (hside : ∀ j, j ≠ i → (σ j < i ↔ j < i)) :
    (atiyahPoly (stereoSpinor p) i).map (starRingEnd ℂ) = atiyahPoly (stereoSpinor p) i := by
  unfold atiyahPoly
  rw [Polynomial.map_prod]
  refine Finset.prod_bij (fun j _ => σ j) ?_ ?_ ?_ ?_
  · intro j hj
    exact Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hj).1 (by
      have := congr_arg σ h; rwa [hσ, hfix] at this), Finset.mem_univ _⟩
  · intro j₁ _ j₂ _ heq; exact σ.injective heq
  · intro b hb
    refine ⟨σ b, Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hb).1 (by
      have := congr_arg σ h; rwa [hσ, hfix] at this), Finset.mem_univ _⟩, hσ b⟩
  · intro j hj
    have hj_ne : j ≠ i := (Finset.mem_erase.mp hj).1
    have hσj_ne : σ j ≠ i := fun h => hj_ne (by have := congr_arg σ h; rwa [hσ, hfix] at this)
    have hside_j := hside j hj_ne
    by_cases hjlt : j < i
    · have hσlt : σ j < i := hside_j.mpr hjlt
      simp only [stereoSpinor, hj_ne.symm, hσj_ne.symm, ↓reduceIte, not_lt_of_gt hjlt,
        not_lt_of_gt hσlt, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [← hfix, stereoSlope_yRefl p σ hy j i, hfix]
      simp
    · have hij : i < j := lt_of_le_of_ne (not_lt.mp hjlt) hj_ne.symm
      have hσnlt : ¬ σ j < i := fun h => hjlt (hside_j.mp h)
      have hiσj : i < σ j := lt_of_le_of_ne (not_lt.mp hσnlt) hσj_ne.symm
      simp only [stereoSpinor, hj_ne.symm, hσj_ne.symm, ↓reduceIte, hij, hiσj,
        Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      have hw := stereoSlope_yRefl p σ hy i j
      rw [hfix] at hw
      rw [hw]
      simp

private lemma atiyahPoly_yRefl_block {{N : ℕ}} (p : Fin N → Fin 3 → ℝ) (σ : Equiv.Perm (Fin N))
    (hσ : ∀ u, σ (σ u) = u) (hy : ∀ u, p (σ u) = ![p u 0, -p u 1, p u 2])
    (a : Fin N) (ha3 : a.1 + 3 < N)
    (hσa' : σ a = ⟨a.1 + 2, by omega⟩) (hσa1' : σ ⟨a.1 + 1, by omega⟩ = ⟨a.1 + 3, by omega⟩)
    (hx : ∃ x y z : ℝ, 0 < x ∧ 0 < y ∧
      p a = ![x, y, z] ∧ p ⟨a.1 + 1, by omega⟩ = ![-x, -y, z] ∧
      p ⟨a.1 + 2, by omega⟩ = ![x, -y, z] ∧ p ⟨a.1 + 3, by omega⟩ = ![-x, y, z])
    (hside : ∀ j : Fin N, j.1 ≠ a.1 → j.1 ≠ a.1 + 1 → j.1 ≠ a.1 + 2 → j.1 ≠ a.1 + 3 →
      (σ j < ⟨a.1 + 2, by omega⟩ ↔ j < a)) :
    (atiyahPoly (stereoSpinor p) ⟨a.1 + 2, by omega⟩).map (starRingEnd ℂ) =
      Polynomial.C (-Complex.I) * atiyahPoly (stereoSpinor p) a := by
  let a1 : Fin N := ⟨a.1 + 1, by omega⟩
  let a2 : Fin N := ⟨a.1 + 2, by omega⟩
  let a3 : Fin N := ⟨a.1 + 3, by omega⟩
  obtain ⟨x, y, z, hxpos, hypos, hpa, hpa1', hpa2', hpa3'⟩ := hx
  have hpa1 : p a1 = ![-x, -y, z] := hpa1'
  have hpa2 : p a2 = ![x, -y, z] := hpa2'
  have hpa3 : p a3 = ![-x, y, z] := hpa3'
  have hσa : σ a = a2 := hσa'
  have hσa1 : σ a1 = a3 := hσa1'
  have hσa2 : σ a2 = a := by have := hσ a; rwa [hσa] at this
  have hσa3 : σ a3 = a1 := by have := hσ a1; rwa [hσa1] at this
  have hw02 : stereoSlope p a a2 = -Complex.I := by
    have heu : euclidNorm (fun k => p a2 k - p a k) = 2 * y := by
      unfold euclidNorm
      rw [hpa, hpa2]
      simp only [vec3_val0, vec3_val1, vec3_val2]
      rw [show (x - x) ^ 2 + (-y - y) ^ 2 + (z - z) ^ 2 = (2 * y) ^ 2 by ring, Real.sqrt_sq (by linarith)]
    have hyC : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hypos.ne'
    unfold stereoSlope stereoDenomR
    rw [heu, hpa, hpa2]
    simp only [vec3_val0, vec3_val1, vec3_val2]
    push_cast
    field_simp [hyC]
    ring
  have hw12 : stereoSlope p a1 a2 = 1 := by
    have heu : euclidNorm (fun k => p a2 k - p a1 k) = 2 * x := by
      unfold euclidNorm
      rw [hpa1, hpa2]
      simp only [vec3_val0, vec3_val1, vec3_val2]
      rw [show (x - -x) ^ 2 + (-y - -y) ^ 2 + (z - z) ^ 2 = (2 * x) ^ 2 by ring, Real.sqrt_sq (by linarith)]
    have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hxpos.ne'
    unfold stereoSlope stereoDenomR
    rw [heu, hpa1, hpa2]
    simp only [vec3_val0, vec3_val1, vec3_val2]
    push_cast
    field_simp [hxC]
    ring
  have hw03 : stereoSlope p a a3 = -1 := by
    have heu : euclidNorm (fun k => p a3 k - p a k) = 2 * x := by
      unfold euclidNorm
      rw [hpa, hpa3]
      simp only [vec3_val0, vec3_val1, vec3_val2]
      rw [show (-x - x) ^ 2 + (y - y) ^ 2 + (z - z) ^ 2 = (2 * x) ^ 2 by ring, Real.sqrt_sq (by linarith)]
    have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hxpos.ne'
    unfold stereoSlope stereoDenomR
    rw [heu, hpa, hpa3]
    simp only [vec3_val0, vec3_val1, vec3_val2]
    push_cast
    field_simp [hxC]
    ring
  let g : Fin N → Fin N := fun j =>
    if j = a2 then a else if j = a3 then a1 else if j = a1 then a3 else σ j
  let gInv : Fin N → Fin N := fun b =>
    if b = a then a2 else if b = a1 then a3 else if b = a3 then a1 else σ b
  let fac : Fin N → Polynomial ℂ := fun j =>
    if j = a2 then Polynomial.C Complex.I else if j = a3 then (-1 : Polynomial ℂ) else 1
  have ha_a1 : a ≠ a1 := by simp [a1, Fin.ext_iff]
  have ha_a2 : a ≠ a2 := by simp [a2, Fin.ext_iff]
  have ha_a3 : a ≠ a3 := by simp [a3, Fin.ext_iff]
  have ha1_a2 : a1 ≠ a2 := by simp [a1, a2, Fin.ext_iff]
  have ha1_a3 : a1 ≠ a3 := by simp [a1, a3, Fin.ext_iff]
  have ha2_a3 : a2 ≠ a3 := by simp [a2, a3, Fin.ext_iff]
  have hg_leftInv : ∀ j, gInv (g j) = j := by
    intro j
    by_cases h2 : j = a2
    · rw [h2]; simp only [g, gInv, ↓reduceIte]
    · by_cases h3 : j = a3
      · rw [h3]; simp only [g, gInv, ha2_a3.symm, ha_a1.symm, ↓reduceIte]
      · by_cases h1 : j = a1
        · rw [h1]; simp only [g, gInv, ha1_a2, ha1_a3, ha_a3.symm, ha1_a3.symm, ↓reduceIte]
        · by_cases h0 : j = a
          · rw [h0]; simp only [g, gInv, ha_a2, ha_a3, ha_a1, hσa, ha_a2.symm, ha1_a2.symm, ha2_a3, ↓reduceIte, hσa2]
          · have hσ0 : σ j ≠ a := fun hs => h2 (by have := congr_arg σ hs; rwa [hσ, hσa] at this)
            have hσ1 : σ j ≠ a1 := fun hs => h3 (by have := congr_arg σ hs; rwa [hσ, hσa1] at this)
            have hσ3 : σ j ≠ a3 := fun hs => h1 (by have := congr_arg σ hs; rwa [hσ, hσa3] at this)
            simp only [g, gInv, h2, h3, h1, ↓reduceIte, hσ0, hσ1, hσ3, hσ j]
  have hg_mem : ∀ j ∈ Finset.univ.erase a, g j ∈ Finset.univ.erase a2 := by
    intro j hj
    have hja : j ≠ a := (Finset.mem_erase.mp hj).1
    by_cases h2 : j = a2
    · subst h2; simp [g, ha_a2]
    · by_cases h3 : j = a3
      · subst h3; simp [g, ha1_a2, ha2_a3.symm]
      · by_cases h1 : j = a1
        · subst h1; simp [g, ha1_a2, ha1_a3, ha2_a3.symm]
        · simp only [g, h2, h3, h1, ↓reduceIte]
          exact Finset.mem_erase.mpr ⟨fun hs => hja (by have := congr_arg σ hs; rwa [hσ, hσa2] at this), Finset.mem_univ _⟩
  have hg_inj : ∀ j₁ ∈ Finset.univ.erase a, ∀ j₂ ∈ Finset.univ.erase a, g j₁ = g j₂ → j₁ = j₂ := by
    intro j₁ _ j₂ _ heq
    rw [← hg_leftInv j₁, ← hg_leftInv j₂, heq]
  have hg_surj : ∀ b ∈ Finset.univ.erase a2, ∃ j, ∃ (_ : j ∈ Finset.univ.erase a), g j = b := by
    intro b hb
    have hb2 : b ≠ a2 := (Finset.mem_erase.mp hb).1
    by_cases hba : b = a
    · exact ⟨a2, Finset.mem_erase.mpr ⟨ha_a2.symm, Finset.mem_univ _⟩, by simp [g, hba]⟩
    · by_cases hb1 : b = a1
      · exact ⟨a3, Finset.mem_erase.mpr ⟨ha_a3.symm, Finset.mem_univ _⟩, by simp [g, hb1, ha2_a3.symm]⟩
      · by_cases hb3 : b = a3
        · exact ⟨a1, Finset.mem_erase.mpr ⟨ha_a1.symm, Finset.mem_univ _⟩, by simp [g, hb3, ha1_a2, ha1_a3]⟩
        · refine ⟨σ b, Finset.mem_erase.mpr ⟨fun he => hb2 (by have := congr_arg σ he; rwa [hσ, hσa] at this), Finset.mem_univ _⟩, ?_⟩
          have hc2 : σ b ≠ a2 := fun he => hba (by have := congr_arg σ he; rwa [hσ, hσa2] at this)
          have hc3 : σ b ≠ a3 := fun he => hb1 (by have := congr_arg σ he; rwa [hσ, hσa3] at this)
          have hc1 : σ b ≠ a1 := fun he => hb3 (by have := congr_arg σ he; rwa [hσ, hσa1] at this)
          simp [g, hc2, hc3, hc1, hσ b]
  have hprod_eq : (atiyahPoly (stereoSpinor p) a2).map (starRingEnd ℂ) =
      ∏ j ∈ Finset.univ.erase a,
        (fac j * (Polynomial.C (stereoSpinor p a j 0) + Polynomial.C (stereoSpinor p a j 1) * Polynomial.X)) := by
    unfold atiyahPoly
    rw [Polynomial.map_prod]
    refine (Finset.prod_bij (fun j _ => g j) hg_mem hg_inj hg_surj ?_).symm
    intro j hj
    have hja : j ≠ a := (Finset.mem_erase.mp hj).1
    by_cases h2 : j = a2
    · subst h2
      have ha_lt_a2 : a < a2 := by simp [Fin.lt_def, a2]
      simp only [g, ↓reduceIte, fac, stereoSpinor, ha_a2, ha_a2.symm, ha_lt_a2, not_lt_of_gt ha_lt_a2,
        Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
        Matrix.cons_val_zero, Matrix.cons_val_one, hw02]
      simp [map_neg]
      rw [mul_add, mul_one, mul_neg, ← mul_assoc, ← map_mul, Complex.I_mul_I, map_neg, map_one]
      ring
    · by_cases h3 : j = a3
      · subst h3
        have ha1_lt_a2 : a1 < a2 := by simp [Fin.lt_def, a1, a2]
        have ha_lt_a3 : a < a3 := by simp [Fin.lt_def, a3]
        simp only [g, h2, ↓reduceIte, fac, stereoSpinor, ha1_a2.symm, not_lt_of_gt ha1_lt_a2,
          ha_a3, ha_lt_a3, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
          Matrix.cons_val_zero, Matrix.cons_val_one, hw12, hw03]
        simp
        ring
      · by_cases h1 : j = a1
        · subst h1
          have ha2_lt_a3 : a2 < a3 := by simp [Fin.lt_def, a2, a3]
          have ha_lt_a1 : a < a1 := by simp [Fin.lt_def, a1]
          simp only [g, h2, h3, ↓reduceIte, fac, stereoSpinor, ha2_a3, ha2_lt_a3,
            ha_a1, ha_lt_a1, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
            Matrix.cons_val_zero, Matrix.cons_val_one, one_mul]
          have hw23 : stereoSlope p a2 a3 = star (stereoSlope p a a1) := by
            rw [← hσa, ← hσa1]
            exact stereoSlope_yRefl p σ hy a a1
          rw [hw23]
          simp
        · have hja0 : j.1 ≠ a.1 := fun h => hja (Fin.ext h)
          have hja1 : j.1 ≠ a.1 + 1 := fun h => h1 (Fin.ext h)
          have hja2 : j.1 ≠ a.1 + 2 := fun h => h2 (Fin.ext h)
          have hja3 : j.1 ≠ a.1 + 3 := fun h => h3 (Fin.ext h)
          have hside_j := hside j hja0 hja1 hja2 hja3
          have hσj_ne : σ j ≠ a2 := fun h => hja (by have := congr_arg σ h; rwa [hσ, hσa2] at this)
          by_cases hjlt : j < a
          · have hσlt : σ j < a2 := hside_j.mpr hjlt
            simp only [g, h2, h3, h1, ↓reduceIte, fac, stereoSpinor, hja.symm, hσj_ne.symm,
              not_lt_of_gt hjlt, not_lt_of_gt hσlt, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
              Polynomial.map_X, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul]
            rw [← hσa, stereoSlope_yRefl p σ hy j a]
            simp
          · have haj : a < j := lt_of_le_of_ne (not_lt.mp hjlt) hja.symm
            have hσnlt : ¬ σ j < a2 := fun h => hjlt (hside_j.mp h)
            have ha2σj : a2 < σ j := lt_of_le_of_ne (not_lt.mp hσnlt) hσj_ne.symm
            simp only [g, h2, h3, h1, ↓reduceIte, fac, stereoSpinor, hja.symm, hσj_ne.symm,
              haj, ha2σj, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
              Matrix.cons_val_zero, Matrix.cons_val_one, one_mul]
            have hw := stereoSlope_yRefl p σ hy a j
            rw [hσa] at hw
            rw [hw]
            simp
  rw [hprod_eq, Finset.prod_mul_distrib]
  congr 1
  have h2m : a2 ∈ Finset.univ.erase a := Finset.mem_erase.mpr ⟨ha_a2.symm, Finset.mem_univ _⟩
  have h3m : a3 ∈ (Finset.univ.erase a).erase a2 := Finset.mem_erase.mpr
    ⟨ha2_a3.symm, Finset.mem_erase.mpr ⟨ha_a3.symm, Finset.mem_univ _⟩⟩
  rw [← Finset.prod_erase_mul (Finset.univ.erase a) fac h2m,
      ← Finset.prod_erase_mul ((Finset.univ.erase a).erase a2) fac h3m]
  have hrest : (∏ j ∈ ((Finset.univ.erase a).erase a2).erase a3, fac j) = 1 :=
    Finset.prod_eq_one fun j hj => by
      have h3n := (Finset.mem_erase.mp hj).1
      have h2n := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
      simp [fac, h2n, h3n]
  have hf2 : fac a2 = Polynomial.C Complex.I := by simp [fac]
  have hf3 : fac a3 = -1 := by simp [fac, ha2_a3.symm]
  rw [hrest, hf2, hf3, one_mul, map_neg]
  ring

private lemma atiyahPoly_yRefl_block_rev {{N : ℕ}} (p : Fin N → Fin 3 → ℝ) (σ : Equiv.Perm (Fin N))
    (hσ : ∀ u, σ (σ u) = u) (hy : ∀ u, p (σ u) = ![p u 0, -p u 1, p u 2])
    (a : Fin N) (ha3 : a.1 + 3 < N)
    (hσa : σ a = ⟨a.1 + 2, by omega⟩) (hσa1 : σ ⟨a.1 + 1, by omega⟩ = ⟨a.1 + 3, by omega⟩)
    (hx : ∃ x y z : ℝ, 0 < x ∧ 0 < y ∧
      p a = ![x, y, z] ∧ p ⟨a.1 + 1, by omega⟩ = ![-x, -y, z] ∧
      p ⟨a.1 + 2, by omega⟩ = ![x, -y, z] ∧ p ⟨a.1 + 3, by omega⟩ = ![-x, y, z])
    (hside : ∀ j : Fin N, j.1 ≠ a.1 → j.1 ≠ a.1 + 1 → j.1 ≠ a.1 + 2 → j.1 ≠ a.1 + 3 →
      (σ j < ⟨a.1 + 2, by omega⟩ ↔ j < a)) :
    (atiyahPoly (stereoSpinor p) a).map (starRingEnd ℂ) =
      Polynomial.C (-Complex.I) * atiyahPoly (stereoSpinor p) ⟨a.1 + 2, by omega⟩ := by
  have hb := atiyahPoly_yRefl_block p σ hσ hy a ha3 hσa hσa1 hx hside
  have hb2 := congr_arg (Polynomial.map (starRingEnd ℂ)) hb
  have hcid : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := by ext z; simp
  rw [Polynomial.map_map, hcid, Polynomial.map_id, Polynomial.map_mul, Polynomial.map_C] at hb2
  have hmul : Polynomial.C (-Complex.I) * atiyahPoly (stereoSpinor p) ⟨a.1 + 2, by omega⟩ =
      (Polynomial.C (-Complex.I) * Polynomial.C (starRingEnd ℂ (-Complex.I))) *
        (atiyahPoly (stereoSpinor p) a).map (starRingEnd ℂ) := by
    rw [hb2]; ring
  rw [hmul, ← map_mul Polynomial.C]
  have hII : -Complex.I * starRingEnd ℂ (-Complex.I) = 1 := by
    simp [map_neg, Complex.conj_I]
  rw [hII, map_one, one_mul]

private lemma continuous_stereoSlope {{N : ℕ}} (x : ℝ → DistinctPoints N)
    (hcont : ∀ i c, Continuous (fun t => (x t).1 i c))
    (hz : ∀ t, Monotone (fun i => (x t).1 i 2))
    {{i j : Fin N}} (hij : i < j) :
    Continuous (fun t => stereoSlope (x t).1 i j) := by
  unfold stereoSlope stereoDenomR
  have hnum : Continuous (fun t => (((x t).1 j 0 - (x t).1 i 0 : ℝ) : ℂ) +
      Complex.I * (((x t).1 j 1 - (x t).1 i 1 : ℝ) : ℂ)) := by
    refine Continuous.add (Complex.continuous_ofReal.comp ((hcont j 0).sub (hcont i 0)))
      (continuous_const.mul (Complex.continuous_ofReal.comp ((hcont j 1).sub (hcont i 1))))
  have hdz : Continuous (fun t => (x t).1 j 2 - (x t).1 i 2) := (hcont j 2).sub (hcont i 2)
  have hnorm : Continuous (fun t => euclidNorm (fun k => (x t).1 j k - (x t).1 i k)) := by
    unfold euclidNorm
    exact ((((hcont j 0).sub (hcont i 0)).pow 2).add (((hcont j 1).sub (hcont i 1)).pow 2) |>.add
      (((hcont j 2).sub (hcont i 2)).pow 2)).sqrt
  have hden : Continuous (fun t => (((x t).1 j 2 - (x t).1 i 2 +
      euclidNorm (fun k => (x t).1 j k - (x t).1 i k) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hdz.add hnorm)
  refine hnum.div hden fun t => Complex.ofReal_ne_zero.mpr ?_
  exact (stereoDenomR_pos ((x t).2 i j hij.ne) (hz t hij.le)).ne'

private lemma continuous_finset_sum_aux {{α β ι : Type*}} [TopologicalSpace α]
    [AddCommMonoid β] [TopologicalSpace β] [ContinuousAdd β]
    (s : Finset ι) {{f : ι → α → β}} (hf : ∀ i ∈ s, Continuous (f i)) :
    Continuous (fun a => ∑ i ∈ s, f i a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using continuous_const
  | insert i s hi ih =>
    have h1 : Continuous (f i) := hf i (Finset.mem_insert_self i s)
    have h2 : Continuous (fun a => ∑ j ∈ s, f j a) :=
      ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    have heq : (fun a => ∑ j ∈ insert i s, f j a) = fun a => f i a + ∑ j ∈ s, f j a :=
      funext fun a => Finset.sum_insert hi
    rw [heq]
    exact h1.add h2

private lemma continuous_atiyahMat_entry {{N : ℕ}} (x : ℝ → DistinctPoints N)
    (hcont : ∀ i c, Continuous (fun t => (x t).1 i c))
    (hz : ∀ t, Monotone (fun i => (x t).1 i 2))
    (i k : Fin N) :
    Continuous (fun t => (atiyahMat (stereoSpinor (x t).1)) i k) := by
  have hfactor : ∀ j ∈ Finset.univ.erase i, ∀ c : ℕ,
      Continuous (fun t => (Polynomial.C (stereoSpinor (x t).1 i j 0) +
        Polynomial.C (stereoSpinor (x t).1 i j 1) * Polynomial.X).coeff c) := by
    intro j hj c
    have hij : i ≠ j := (Finset.mem_erase.mp hj).1.symm
    have hcoeff0 : ∀ t, (Polynomial.C (stereoSpinor (x t).1 i j 0) +
        Polynomial.C (stereoSpinor (x t).1 i j 1) * Polynomial.X).coeff 0 = stereoSpinor (x t).1 i j 0 := by
      intro t; simp
    have hcoeff1 : ∀ t, (Polynomial.C (stereoSpinor (x t).1 i j 0) +
        Polynomial.C (stereoSpinor (x t).1 i j 1) * Polynomial.X).coeff 1 = stereoSpinor (x t).1 i j 1 := by
      intro t; simp
    have hcoeff_gt : ∀ t (d : ℕ), 2 ≤ d → (Polynomial.C (stereoSpinor (x t).1 i j 0) +
        Polynomial.C (stereoSpinor (x t).1 i j 1) * Polynomial.X).coeff d = 0 := by
      intro t d hc
      rw [Polynomial.coeff_add, Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
      have h0 : d ≠ 0 := by omega
      have h1 : d ≠ 1 := by omega
      simp [h0, h1]
    match c with
    | 0 =>
      simp_rw [hcoeff0]
      rcases lt_trichotomy i j with hlt | rfl | hgt
      · simp [stereoSpinor, hij, hlt, continuous_const]
      · exact absurd rfl hij
      · simp only [stereoSpinor, hij, ↓reduceIte, not_lt_of_gt hgt, Matrix.cons_val_zero]
        exact (Complex.continuous_conj.comp (continuous_stereoSlope x hcont hz hgt)).neg
    | 1 =>
      simp_rw [hcoeff1]
      rcases lt_trichotomy i j with hlt | rfl | hgt
      · simp only [stereoSpinor, hij, ↓reduceIte, hlt, Matrix.cons_val_one]
        exact continuous_stereoSlope x hcont hz hlt
      · exact absurd rfl hij
      · simp [stereoSpinor, hij, not_lt_of_gt hgt, continuous_const]
    | c' + 2 =>
      have heq : (fun t => (Polynomial.C (stereoSpinor (x t).1 i j 0) +
          Polynomial.C (stereoSpinor (x t).1 i j 1) * Polynomial.X).coeff (c' + 2)) = fun _ => 0 :=
        funext fun t => hcoeff_gt t (c' + 2) (by omega)
      rw [heq]; exact continuous_const
  have hprod : ∀ (s : Finset (Fin N)), s ⊆ Finset.univ.erase i → ∀ c : ℕ,
      Continuous (fun t => (∏ j ∈ s, (Polynomial.C (stereoSpinor (x t).1 i j 0) +
        Polynomial.C (stereoSpinor (x t).1 i j 1) * Polynomial.X)).coeff c) := by
    intro s
    classical
    refine Finset.induction_on s ?_ ?_
    · intro _ c
      simp only [Finset.prod_empty, Polynomial.coeff_one]
      exact continuous_const
    · intro a s' ha ih hs_sub c
      simp_rw [Finset.prod_insert ha, Polynomial.coeff_mul]
      refine continuous_finset_sum_aux _ fun p _ => Continuous.mul ?_ ?_
      · exact hfactor a (hs_sub (Finset.mem_insert_self a s')) p.1
      · exact ih (fun z hz' => hs_sub (Finset.mem_insert_of_mem hz')) p.2
  exact hprod (Finset.univ.erase i) Finset.Subset.rfl k.1

/-! ### Staged `CFpIv` verification helpers with per-row cached multipliers -/

private def S_symp : ℤ := {S_SYMP}
private lemma S_symp_pos : 0 < S_symp := by decide

private def wRead2D {{n : ℕ}} (tbl : List (List CFpIv)) (i j : Fin n) : CFpIv :=
  (tbl.getD i.1 []).getD j.1 CFpIv.zero

private def stagePRows {{n : ℕ}} (S : ℤ) (wIv : Fin n → Fin n → CFpIv)
    (src ch : List (Fin n)) (rows : List (List CFpIv)) : List (List CFpIv) :=
  List.zipWith (fun i ps => ch.foldl (stepPolyCIv S wIv i) ps) src rows

private lemma stagePRows_zip {{n : ℕ}} (S : ℤ) (wIv : Fin n → Fin n → CFpIv)
    (src l₀ l₁ : List (Fin n)) :
    stagePRows S wIv src l₁ (src.map fun i => l₀.foldl (stepPolyCIv S wIv i) [CFpIv.ofInt S 1]) =
      src.map fun i => (l₀ ++ l₁).foldl (stepPolyCIv S wIv i) [CFpIv.ofInt S 1] := by
  unfold stagePRows
  induction src with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons, List.zipWith_cons_cons, List.foldl_append, ih]

private lemma stagePRows_init {{n : ℕ}} (S : ℤ) (wIv : Fin n → Fin n → CFpIv)
    (src ch : List (Fin n)) :
    stagePRows S wIv src ch (List.replicate src.length [CFpIv.ofInt S 1]) =
      src.map fun i => ch.foldl (stepPolyCIv S wIv i) [CFpIv.ofInt S 1] := by
  unfold stagePRows
  induction src with
  | nil => rfl
  | cons a as ih => simp only [List.length_cons, List.replicate_succ, List.zipWith_cons_cons, List.map_cons, ih]

private def extractRowEven (m : ℕ) (ps : List CFpIv) : List CFpIv :=
  (List.finRange m).map fun c => ps.getD (2 * c.1) CFpIv.zero

private def extractRowOdd (m : ℕ) (ps : List CFpIv) : List CFpIv :=
  (List.finRange m).map fun c => ps.getD (2 * c.1 + 1) CFpIv.zero

private def extractSubEven (m : ℕ) (rows : List (List CFpIv)) : List (List CFpIv) :=
  rows.map (extractRowEven m)

private def extractSubOdd (m : ℕ) (rows : List (List CFpIv)) : List (List CFpIv) :=
  rows.map (extractRowOdd m)

private lemma getD_map_finRange {{α : Type*}} {{m : ℕ}} (d : α) (f : Fin m → α) (c : Fin m) :
    ((List.finRange m).map f).getD c.1 d = f c := by
  simp [List.getD_eq_getElem?_getD, List.getElem_finRange]

private lemma matCMem_extractSubEven {{n m : ℕ}} {{S : ℤ}} (hS : 0 < S)
    (hn : 0 < n) (hm : 2 * m ≤ n)
    {{wIv : Fin n → Fin n → CFpIv}} {{p : Fin n → Fin 3 → ℝ}}
    (hw : ∀ i j : Fin n, i < j → CFpIv.CFpMem S (wIv i j) (stereoSlope p i j))
    {{srcList : List (Fin n)}} {{src : Fin m → Fin n}}
    (hlen : srcList.length = m) (hsrc : ∀ r : Fin m, srcList.getD r.1 ⟨0, hn⟩ = src r) :
    MatCMem S m (extractSubEven m (srcList.map (polyListCIv S wIv)))
      (Matrix.of fun r c : Fin m => atiyahMat (stereoSpinor p) (src r) ⟨2 * c.1, by have := c.2; omega⟩) := by
  refine ⟨by simp [extractSubEven, hlen], fun r => ?_⟩
  have hmem_i := polyListCIv_mem hS hw (src r)
  have hev := evalListC_polyListC_eq (stereoSlope p) (stereoSpinor p)
    (fun i j hij => by simp [stereoSpinor, hij.ne', not_lt_of_gt hij])
    (fun i j hij => by simp [stereoSpinor, hij.ne, hij]) (src r)
  have hrow_eq : (extractSubEven m (srcList.map (polyListCIv S wIv))).getD r.1 [] =
      extractRowEven m (polyListCIv S wIv (src r)) := by
    simp only [extractSubEven, List.getD_eq_getElem?_getD, List.getElem?_map]
    have hget : srcList[r.1]? = some (src r) := by
      have hrl : r.1 < srcList.length := by have := r.2; omega
      have h0 := hsrc r
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hrl] at h0
      rw [List.getElem?_eq_getElem hrl]
      exact congr_arg some (by simpa using h0)
    rw [hget]
    rfl
  rw [hrow_eq]
  refine ⟨by simp [extractRowEven], fun c => ?_⟩
  unfold extractRowEven
  rw [getD_map_finRange]
  simp only [Matrix.of_apply, atiyahMat]
  have hm_c := hmem_i (2 * c.1)
  rw [← coeff_evalListC _ (2 * c.1), hev] at hm_c
  exact hm_c

private lemma matCMem_extractSubOdd {{n m : ℕ}} {{S : ℤ}} (hS : 0 < S)
    (hn : 0 < n) (hm : 2 * m ≤ n)
    {{wIv : Fin n → Fin n → CFpIv}} {{p : Fin n → Fin 3 → ℝ}}
    (hw : ∀ i j : Fin n, i < j → CFpIv.CFpMem S (wIv i j) (stereoSlope p i j))
    {{srcList : List (Fin n)}} {{src : Fin m → Fin n}}
    (hlen : srcList.length = m) (hsrc : ∀ r : Fin m, srcList.getD r.1 ⟨0, hn⟩ = src r) :
    MatCMem S m (extractSubOdd m (srcList.map (polyListCIv S wIv)))
      (Matrix.of fun r c : Fin m => atiyahMat (stereoSpinor p) (src r) ⟨2 * c.1 + 1, by have := c.2; omega⟩) := by
  refine ⟨by simp [extractSubOdd, hlen], fun r => ?_⟩
  have hmem_i := polyListCIv_mem hS hw (src r)
  have hev := evalListC_polyListC_eq (stereoSlope p) (stereoSpinor p)
    (fun i j hij => by simp [stereoSpinor, hij.ne', not_lt_of_gt hij])
    (fun i j hij => by simp [stereoSpinor, hij.ne, hij]) (src r)
  have hrow_eq : (extractSubOdd m (srcList.map (polyListCIv S wIv))).getD r.1 [] =
      extractRowOdd m (polyListCIv S wIv (src r)) := by
    simp only [extractSubOdd, List.getD_eq_getElem?_getD, List.getElem?_map]
    have hget : srcList[r.1]? = some (src r) := by
      have hrl : r.1 < srcList.length := by have := r.2; omega
      have h0 := hsrc r
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hrl] at h0
      rw [List.getElem?_eq_getElem hrl]
      exact congr_arg some (by simpa using h0)
    rw [hget]
    rfl
  rw [hrow_eq]
  refine ⟨by simp [extractRowOdd], fun c => ?_⟩
  unfold extractRowOdd
  rw [getD_map_finRange]
  simp only [Matrix.of_apply, atiyahMat]
  have hm_c := hmem_i (2 * c.1 + 1)
  rw [← coeff_evalListC _ (2 * c.1 + 1), hev] at hm_c
  exact hm_c

private def cFpIvEq (a b : CFpIv) : Bool :=
  (a.re.lo == b.re.lo) && (a.re.hi == b.re.hi) &&
  (a.im.lo == b.im.lo) && (a.im.hi == b.im.hi)

private lemma eq_of_cFpIvEq {{a b : CFpIv}} (h : cFpIvEq a b = true) : a = b := by
  rcases a with ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩
  rcases b with ⟨⟨b1, b2⟩, ⟨b3, b4⟩⟩
  simp only [cFpIvEq, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩
  rfl

private def elimRowsCIvWithMults (S : ℤ) (piv : CFpIv) (ptail : List CFpIv) :
    List CFpIv → List (List CFpIv) → Bool × List (List CFpIv)
  | _, [] => (true, [])
  | m :: ms, row :: rows =>
    let rhead := row.headD CFpIv.zero
    let rtail := row.tail
    let res := elimRowsCIvWithMults S piv ptail ms rows
    if isZeroCIv rhead then
      (res.1, rtail :: res.2)
    else
      (cFpIvEq (cdivIv S (CFpIv.neg rhead) piv) m && res.1, zipElimCIv S m rtail ptail :: res.2)
  | [], _ :: _ => (false, [])

private lemma elimRowsCIv_eq_of_withMults (S : ℤ) (piv : CFpIv) (ptail : List CFpIv) :
    ∀ (ms : List CFpIv) (rows out : List (List CFpIv)),
      elimRowsCIvWithMults S piv ptail ms rows = (true, out) → elimRowsCIv S piv ptail rows = out
  | _, [], out, h => by
    simp only [elimRowsCIvWithMults, Prod.mk.injEq] at h
    rcases h with ⟨_, rfl⟩
    rfl
  | [], _ :: _, _, h => by simp [elimRowsCIvWithMults] at h
  | m :: ms, row :: rows, out, h => by
    dsimp only [elimRowsCIvWithMults] at h
    by_cases hz : isZeroCIv (row.headD CFpIv.zero) = true
    · simp only [hz, ↓reduceIte, Prod.mk.injEq] at h
      obtain ⟨h1, rfl⟩ := h
      have hres : elimRowsCIvWithMults S piv ptail ms rows =
          ((elimRowsCIvWithMults S piv ptail ms rows).1, (elimRowsCIvWithMults S piv ptail ms rows).2) := rfl
      rw [h1] at hres
      have ih := elimRowsCIv_eq_of_withMults S piv ptail ms rows _ hres
      rw [elimRowsCIv]
      dsimp only
      simp only [hz, ↓reduceIte, ih]
    · simp only [hz, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq, Bool.and_eq_true] at h
      obtain ⟨⟨hm, h1⟩, rfl⟩ := h
      have hres : elimRowsCIvWithMults S piv ptail ms rows =
          ((elimRowsCIvWithMults S piv ptail ms rows).1, (elimRowsCIvWithMults S piv ptail ms rows).2) := rfl
      rw [h1] at hres
      have ih := elimRowsCIv_eq_of_withMults S piv ptail ms rows _ hres
      have hmeq : cdivIv S (CFpIv.neg (row.headD CFpIv.zero)) piv = m := eq_of_cFpIvEq hm
      rw [elimRowsCIv]
      dsimp only
      simp only [hz, Bool.false_eq_true, ↓reduceIte, hmeq, ih]

private def gaussHeadCIvWithMults (S : ℤ) (rows : List (List CFpIv)) (prod : CFpIv) (ms : List CFpIv) :
    Bool × List (List CFpIv) × CFpIv :=
  match rows with
  | pRow :: rest =>
    let piv := pRow.headD CFpIv.zero
    let er := elimRowsCIvWithMults S piv pRow.tail ms rest
    (isSepCIv S piv && er.1, er.2, CFpIv.mul S prod piv)
  | [] => (false, [], prod)

private lemma gaussDetCIv_step_withMults {{S : ℤ}} {{m : ℕ}} {{rows rows' : List (List CFpIv)}}
    {{prod prod' : CFpIv}} {{ms : List CFpIv}}
    (h : gaussHeadCIvWithMults S rows prod ms = (true, rows', prod')) :
    gaussDetCIv S (m + 1) rows prod = gaussDetCIv S m rows' prod' := by
  cases rows with
  | nil => simp [gaussHeadCIvWithMults] at h
  | cons pRow rest =>
    dsimp only [gaussHeadCIvWithMults] at h
    rcases her : elimRowsCIvWithMults S (pRow.headD CFpIv.zero) pRow.tail ms rest with ⟨okE, rowsE⟩
    rw [her] at h
    simp only [Prod.mk.injEq, Bool.and_eq_true] at h
    obtain ⟨⟨hsep, rfl⟩, rfl, hprod'⟩ := h
    have helim := elimRowsCIv_eq_of_withMults S (pRow.headD CFpIv.zero) pRow.tail ms rest rowsE her
    rw [gaussDetCIv]
    simp only [hsep, ↓reduceIte, helim, hprod']

private def slopeEntryOk (S tVal : ℤ) (xBase yBase zBase : List ℤ)
    (rhoTbl : List (List ℤ)) (wTbl : List (List CFpIv)) (i j : ℕ) : Bool :=
  let dx := tVal * (xBase.getD j 0 - xBase.getD i 0)
  let dy := tVal * (yBase.getD j 0 - yBase.getD i 0)
  let dz := zBase.getD j 0 - zBase.getD i 0
  let rho := (rhoTbl.getD i []).getD j 0
  let w := (wTbl.getD i []).getD j CFpIv.zero
  if dx == 0 && dy == 0 then
    cFpIvEq w CFpIv.zero
  else
    decide (0 ≤ dz) && decide (0 < rho) &&
      decide (rho * rho ≤ S * S * (dx * dx + dy * dy + dz * dz)) &&
      decide (S * S * (dx * dx + dy * dy + dz * dz) ≤ (rho + 1) * (rho + 1)) &&
      cFpIvEq w (CFpIv.cslopeIv S dx dy dz rho)

private def slopeTableOk (n : ℕ) (S : ℤ) (xBase yBase zBase : List ℤ) (tVal : ℤ)
    (rhoTbl : List (List ℤ)) (wTbl : List (List CFpIv)) : Bool :=
  (List.range n).all fun i =>
    (List.range n).all fun j =>
      if i < j then slopeEntryOk S tVal xBase yBase zBase rhoTbl wTbl i j else true

private lemma slopeTableOk_mem {{n : ℕ}} {{S : ℤ}} (hS : 0 < S)
    {{xBase yBase zBase : List ℤ}} {{tVal : ℤ}}
    {{rhoTbl : List (List ℤ)}} {{wTbl : List (List CFpIv)}}
    {{p : Fin n → Fin 3 → ℝ}}
    (hp0 : ∀ i : Fin n, p i 0 = (tVal : ℝ) * (xBase.getD i.1 0 : ℝ))
    (hp1 : ∀ i : Fin n, p i 1 = (tVal : ℝ) * (yBase.getD i.1 0 : ℝ))
    (hp2 : ∀ i : Fin n, p i 2 = (zBase.getD i.1 0 : ℝ))
    (hok : slopeTableOk n S xBase yBase zBase tVal rhoTbl wTbl = true)
    (i j : Fin n) (hij : i < j) :
    CFpIv.CFpMem S (wRead2D wTbl i j) (stereoSlope p i j) := by
  have hi_ok := List.all_eq_true.mp hok i.1 (List.mem_range.mpr i.2)
  have hj_ok := List.all_eq_true.mp hi_ok j.1 (List.mem_range.mpr j.2)
  have hijN : i.1 < j.1 := hij
  simp only [hijN, ↓reduceIte, slopeEntryOk] at hj_ok
  set dx : ℤ := tVal * (xBase.getD j.1 0 - xBase.getD i.1 0)
  set dy : ℤ := tVal * (yBase.getD j.1 0 - yBase.getD i.1 0)
  set dz : ℤ := zBase.getD j.1 0 - zBase.getD i.1 0
  set rho : ℤ := (rhoTbl.getD i.1 []).getD j.1 0
  have hdxR : p j 0 - p i 0 = (dx : ℝ) := by rw [hp0 j, hp0 i]; push_cast [dx]; ring
  have hdyR : p j 1 - p i 1 = (dy : ℝ) := by rw [hp1 j, hp1 i]; push_cast [dy]; ring
  have hdzR : p j 2 - p i 2 = (dz : ℝ) := by rw [hp2 j, hp2 i]; push_cast [dz]; ring
  by_cases hzero : (dx == 0 && dy == 0) = true
  · simp only [hzero, ↓reduceIte] at hj_ok
    have hw_eq : wRead2D wTbl i j = CFpIv.zero := eq_of_cFpIvEq hj_ok
    simp only [Bool.and_eq_true, beq_iff_eq] at hzero
    have hslope0 : stereoSlope p i j = 0 := by
      unfold stereoSlope
      rw [hdxR, hdyR, hzero.1, hzero.2]
      simp
    rw [hw_eq, hslope0]
    exact CFpIv.zero_mem S
  · simp only [hzero, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hj_ok
    obtain ⟨⟨⟨⟨hdz_ok, hrho_ok⟩, hlo_ok⟩, hhi_ok⟩, hw_eq_b⟩ := hj_ok
    have hw_eq : wRead2D wTbl i j = CFpIv.cslopeIv S dx dy dz rho := eq_of_cFpIvEq hw_eq_b
    have hdz0 : 0 ≤ dz := of_decide_eq_true hdz_ok
    have hrho0 : 0 < rho := of_decide_eq_true hrho_ok
    have hlo : rho * rho ≤ S * S * (dx * dx + dy * dy + dz * dz) := of_decide_eq_true hlo_ok
    have hhi : S * S * (dx * dx + dy * dy + dz * dz) ≤ (rho + 1) * (rho + 1) := of_decide_eq_true hhi_ok
    have hr_bounds := sqrt_rho_bounds hS hrho0 hlo hhi
    set r : ℝ := euclidNorm (fun k => p j k - p i k)
    have hr_eq : r = Real.sqrt ((dx : ℝ) ^ 2 + (dy : ℝ) ^ 2 + (dz : ℝ) ^ 2) := by
      dsimp only [r, euclidNorm]
      rw [hdxR, hdyR, hdzR]
    have hmem := CFpIv.cslopeIv_mem (dx := dx) (dy := dy) hS hdz0 hrho0 (hr_eq ▸ hr_bounds)
    have hslope_eq : stereoSlope p i j =
        (((dx : ℂ) + Complex.I * (dy : ℂ)) / ((dz : ℂ) + (r : ℂ))) := by
      dsimp only [stereoSlope, stereoDenomR, euclidNorm]
      rw [hdxR, hdyR, hdzR, ← hr_eq]
      push_cast; rfl
    rw [hw_eq, hslope_eq]
    exact hmem

private lemma pos_re_of_CFpMem_symp {{S : ℤ}} (hS : 0 < S) {{iv : CFpIv}} {{z : ℂ}}
    (hmem : CFpIv.CFpMem S iv z) (hlo : 0 < iv.re.lo) : 0 < z.re := by
  have hS_pos : (0 : ℝ) < (S : ℝ) := by exact_mod_cast hS
  have hlo_R : (0 : ℝ) < (iv.re.lo : ℝ) := by exact_mod_cast hlo
  exact pos_of_mul_pos_right (lt_of_lt_of_le hlo_R hmem.1.1) hS_pos.le

private lemma neg_re_of_CFpMem_symp {{S : ℤ}} (hS : 0 < S) {{iv : CFpIv}} {{z : ℂ}}
    (hmem : CFpIv.CFpMem S iv z) (hhi : iv.re.hi < 0) : z.re < 0 := by
  have hS_pos : (0 : ℝ) < (S : ℝ) := by exact_mod_cast hS
  have hhi_R : (iv.re.hi : ℝ) < 0 := by exact_mod_cast hhi
  exact neg_of_mul_neg_right (lt_of_le_of_lt hmem.1.2 hhi_R) hS_pos.le

end GeometricSymmetries

""")
    return "".join(out)


def finish_build_lean(
    sp20_pts: list[list[int]],
    sp18_pts: list[list[int]],
    b18_pts: list[list[int]],
) -> str:
    sp20_src = [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34, 36, 38]
    sp18_src = [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30, 32, 34]
    b18_src = [1, 3, 5, 6, 8, 10, 12, 14, 16, 19, 21, 23, 25, 27, 29, 31, 33, 35]

    ch_40 = [list(range(k, min(k + 5, 40))) for k in range(0, 40, 5)]
    ch_36 = [list(range(k, min(k + 5, 36))) for k in range(0, 36, 5)]
    ch_37 = [list(range(k, min(k + 5, 37))) for k in range(0, 37, 5)]

    c_sp20_1, _ = compute_cert("sp20_1", "sp20", sp20_pts, 1, sp20_src, False, ch_40, "pos")
    c_sp20_2, _ = compute_cert("sp20_2", "sp20", sp20_pts, 2, sp20_src, False, ch_40, "neg")
    c_sp18_7, _ = compute_cert("sp18_7", "sp18", sp18_pts, 7, sp18_src, False, ch_36, "pos")
    c_sp18_8, _ = compute_cert("sp18_8", "sp18", sp18_pts, 8, sp18_src, False, ch_36, "neg")
    c_b18_8, _ = compute_cert("b18_8", "b18", b18_pts, 8, b18_src, True, ch_37, "neg")
    c_b18_9, _ = compute_cert("b18_9", "b18", b18_pts, 9, b18_src, True, ch_37, "pos")

    sp20_anti = [39 - i for i in range(40)]
    sp20_rotz = [next(j for j, q in enumerate(sp20_pts) if q == [-p[0], -p[1], p[2]]) for p in sp20_pts]
    sp18_anti = [35, 34, 33, 32, 31, 30, 25, 24, 27, 26, 29, 28, 19, 18, 21, 20, 23, 22, 13, 12, 15, 14, 17, 16, 7, 6, 9, 8, 11, 10, 5, 4, 3, 2, 1, 0]
    sp18_rotz = [next(j for j, q in enumerate(sp18_pts) if q == [-p[0], -p[1], p[2]]) for p in sp18_pts]
    sp18_yref = [next(j for j, q in enumerate(sp18_pts) if q == [p[0], -p[1], p[2]]) for p in sp18_pts]
    b18_anti = [36, 35, 34, 33, 32, 31, 26, 25, 28, 27, 30, 29, 20, 19, 22, 21, 24, 23, 18, 13, 12, 15, 14, 17, 16, 7, 6, 9, 8, 11, 10, 5, 4, 3, 2, 1, 0]
    b18_rotz = [next(j for j, q in enumerate(b18_pts) if q == [-p[0], -p[1], p[2]]) for p in b18_pts]
    b18_yref = [next(j for j, q in enumerate(b18_pts) if q == [p[0], -p[1], p[2]]) for p in b18_pts]

    out = [build_lean()]

    # Wait: generate clean families WITHOUT sorry in srcRows_stages!
    def emit_family(fam, n, m, pts, src, chunks, anti_map, rotz_map, yref_map):
        xs, ys, zs = fmt_coord_triple_list(pts)
        src_fin = "[" + ", ".join(str(x) for x in src) + "]"
        ch_defs = "\n".join(
            f"private def {fam}_ch{k} : List (Fin {n}) := [" + ", ".join(str(j) for j in ch) + "]"
            for k, ch in enumerate(chunks)
        )
        ch_fold_rhs = " ++ ".join(f"{fam}_ch{k}" for k in range(len(chunks)))
        # Build staged rw proof of {fam}_srcRows_stages!
        # Let expr_0 = (ch0 ++ ch1 ++ ...).foldl
        # Start with LHS: srcList.map (fun i => (List.finRange n).foldl (stepPolyCIv S w i) [1])
        # rw [← {fam}_chunks_eq]
        # Repeat associating ((A ++ B) ++ C): rw [← stagePRows_zip ...]
        stage_expr = f"List.replicate {m} [CFpIv.ofInt S_symp 1]"
        for k in range(len(chunks)):
            stage_expr = f"stagePRows S_symp w {fam}SrcList {fam}_ch{k} ({stage_expr})"
        # Note fold_rhs associates left-to-right: (((ch0 ++ ch1) ++ ch2) ...)
        zip_steps = "\n".join(
            f"  rw [← stagePRows_zip S_symp w {fam}SrcList]" for _ in range(len(chunks) - 1)
        )
        sec: list[str] = []
        sec.append(f"section Family_{fam}\n\n")
        sec.append(f"private def {fam}BaseXList : List ℤ := {xs}\n")
        sec.append(f"private def {fam}BaseYList : List ℤ := {ys}\n")
        sec.append(f"private def {fam}BaseZList : List ℤ := {zs}\n\n")
        sec.append(f"private def {fam}BaseX (i : Fin {n}) : ℤ := {fam}BaseXList.getD i.1 0\n")
        sec.append(f"private def {fam}BaseY (i : Fin {n}) : ℤ := {fam}BaseYList.getD i.1 0\n")
        sec.append(f"private def {fam}BaseZ (i : Fin {n}) : ℤ := {fam}BaseZList.getD i.1 0\n\n")
        sec.append(
            f"private def {fam}Raw (t : ℝ) (i : Fin {n}) : Fin 3 → ℝ :=\n"
            f"  ![max t 1 * ({fam}BaseX i : ℝ), max t 1 * ({fam}BaseY i : ℝ), ({fam}BaseZ i : ℝ)]\n\n"
        )
        sec.append(
            f"private lemma {fam}_base_distinct : ∀ i j : Fin {n}, i ≠ j →\n"
            f"    ({fam}BaseX i ≠ {fam}BaseX j ∨ {fam}BaseY i ≠ {fam}BaseY j ∨ {fam}BaseZ i ≠ {fam}BaseZ j) := by\n"
            f"  decide\n\n"
        )
        sec.append(f"private lemma {fam}_base_z_mono : Monotone {fam}BaseZ := by decide\n\n")
        sec.append(
            f"private lemma {fam}Raw_distinct (t : ℝ) (i j : Fin {n}) (hij : i ≠ j) : {fam}Raw t i ≠ {fam}Raw t j := by\n"
            f"  intro heq\n"
            f"  have hs : (0 : ℝ) < max t 1 := lt_of_lt_of_le zero_lt_one (le_max_right t 1)\n"
            f"  rcases {fam}_base_distinct i j hij with hx | hy | hz\n"
            f"  · have h0 := congr_fun heq 0\n"
            f"    simp only [{fam}Raw, Matrix.cons_val_zero] at h0\n"
            f"    exact hx (Int.cast_injective (mul_left_cancel₀ hs.ne' h0))\n"
            f"  · have h1 := congr_fun heq 1\n"
            f"    simp only [{fam}Raw, Matrix.cons_val_one] at h1\n"
            f"    exact hy (Int.cast_injective (mul_left_cancel₀ hs.ne' h1))\n"
            f"  · have h2 := congr_fun heq 2\n"
            f"    simp only [{fam}Raw, Matrix.cons_val_two] at h2\n"
            f"    exact hz (Int.cast_injective h2)\n\n"
        )
        sec.append(f"private def {fam}Clamp (t : ℝ) : DistinctPoints {n} := ⟨{fam}Raw t, {fam}Raw_distinct t⟩\n\n")
        sec.append(
            f"private lemma {fam}Clamp_z_mono (t : ℝ) : Monotone (fun i => ({fam}Clamp t).1 i 2) :=\n"
            f"  fun _ _ h => Int.cast_le.mpr ({fam}_base_z_mono h)\n\n"
        )
        sec.append(
            f"private lemma continuous_{fam}Clamp_coord (i : Fin {n}) (c : Fin 3) :\n"
            f"    Continuous (fun t => ({fam}Clamp t).1 i c) := by\n"
            f"  fin_cases c <;> simp [{fam}Clamp, {fam}Raw] <;> continuity\n\n"
        )
        sec.append(perm_def_section(f"{fam}Anti", n, anti_map) + "\n")
        sec.append(
            f"private lemma {fam}_anti_coords : ∀ i : Fin {n},\n"
            f"    {fam}BaseX ({fam}AntiFn i) = -{fam}BaseX i ∧\n"
            f"    {fam}BaseY ({fam}AntiFn i) = -{fam}BaseY i ∧\n"
            f"    {fam}BaseZ ({fam}AntiFn i) = -{fam}BaseZ i := by\n"
            f"  decide\n\n"
        )
        sec.append(perm_def_section(f"{fam}RotZ", n, rotz_map) + "\n")
        sec.append(
            f"private lemma {fam}_rotz_coords : ∀ i : Fin {n},\n"
            f"    {fam}BaseX ({fam}RotZFn i) = -{fam}BaseX i ∧\n"
            f"    {fam}BaseY ({fam}RotZFn i) = -{fam}BaseY i ∧\n"
            f"    {fam}BaseZ ({fam}RotZFn i) = {fam}BaseZ i := by\n"
            f"  decide\n\n"
        )
        if yref_map is not None:
            sec.append(perm_def_section(f"{fam}YRef", n, yref_map) + "\n")
            sec.append(
                f"private lemma {fam}_yref_coords : ∀ i : Fin {n},\n"
                f"    {fam}BaseX ({fam}YRefFn i) = {fam}BaseX i ∧\n"
                f"    {fam}BaseY ({fam}YRefFn i) = -{fam}BaseY i ∧\n"
                f"    {fam}BaseZ ({fam}YRefFn i) = {fam}BaseZ i := by\n"
                f"  decide\n\n"
            )
        sec.append(f"private def {fam}SrcRaw : List ℕ := {src_fin}\n\n")
        sec.append(
            f"private def {fam}Src (r : Fin {m}) : Fin {n} := ⟨{fam}SrcRaw.getD r.1 0, by\n"
            f"  have h : ∀ k : Fin {m}, {fam}SrcRaw.getD k.1 0 < {n} := by decide\n"
            f"  exact h r⟩\n\n"
        )
        sec.append(f"private def {fam}SrcList : List (Fin {n}) := (List.finRange {m}).map {fam}Src\n\n")
        sec.append(
            f"private lemma {fam}Src_len : {fam}SrcList.length = {m} := by simp [{fam}SrcList]\n\n"
        )
        sec.append(
            f"private lemma {fam}Src_getD (r : Fin {m}) : {fam}SrcList.getD r.1 ⟨0, by omega⟩ = {fam}Src r := by\n"
            f"  simp [{fam}SrcList, List.getD_eq_getElem?_getD]\n\n"
        )
        sec.append(
            f"private lemma {fam}Src_inj : Function.Injective {fam}Src := by\n"
            f"  intro a b hab\n"
            f"  have h : ∀ x y : Fin {m}, {fam}Src x = {fam}Src y → x = y := by decide\n"
            f"  exact h a b hab\n\n"
        )
        sec.append(ch_defs + "\n\n")
        sec.append(f"private lemma {fam}_chunks_eq : {ch_fold_rhs} = List.finRange {n} := by decide\n\n")
        sec.append(
            f"private lemma {fam}_srcRows_stages (w : Fin {n} → Fin {n} → CFpIv) :\n"
            f"    {fam}SrcList.map (polyListCIv S_symp w) = {stage_expr} := by\n"
            f"  have hmap : {fam}SrcList.map (polyListCIv S_symp w) =\n"
            f"      {fam}SrcList.map (fun i => ({ch_fold_rhs}).foldl (stepPolyCIv S_symp w i) [CFpIv.ofInt S_symp 1]) := by\n"
            f"    refine List.map_congr_left fun i _ => ?_\n"
            f"    unfold polyListCIv\n"
            f"    rw [{fam}_chunks_eq]\n"
            f"  rw [hmap]\n"
            + zip_steps
            + f"\n  simp only [← {fam}Src_len, stagePRows_init]\n\n"
        )
        sec.append(f"end Family_{fam}\n\n")
        return "".join(sec)

    out.append(emit_family("sp20", 40, 20, sp20_pts, sp20_src, ch_40, sp20_anti, sp20_rotz, None))
    out.append(emit_family("sp18", 36, 18, sp18_pts, sp18_src, ch_36, sp18_anti, sp18_rotz, sp18_yref))
    out.append(emit_family("b18", 37, 18, b18_pts, b18_src, ch_37, b18_anti, b18_rotz, b18_yref))

    out.append(c_sp20_1)
    out.append(c_sp20_2)
    out.append(c_sp18_7)
    out.append(c_sp18_8)
    out.append(c_b18_8)
    out.append(c_b18_9)

    # Final proofs linking Configs + Subblocks + Symmetries + Continuity + Certs!
    out.append("""
/-! ## Section 4: Planar $\\mathrm{Sp}(20)$ ($N = 40$) Certified Counterexamples -/

section PlanarSp20

private lemma sp20_y_zero (t : ℝ) (i : Fin 40) : (sp20Clamp t).1 i 1 = 0 := by
  have hy : ∀ k : Fin 40, sp20BaseY k = 0 := by decide
  simp [sp20Clamp, sp20Raw, hy i]

private lemma sp20_rotZ_eq (t : ℝ) (i : Fin 40) :
    (sp20Clamp t).1 (sp20RotZPerm i) = ![-((sp20Clamp t).1 i 0), -((sp20Clamp t).1 i 1), (sp20Clamp t).1 i 2] := by
  have hc := sp20_rotz_coords i
  ext c; fin_cases c
  · simp [sp20Clamp, sp20Raw, sp20RotZPerm, hc.1]
  · simp [sp20Clamp, sp20Raw, sp20RotZPerm, hc.2.1]
  · simp [sp20Clamp, sp20Raw, sp20RotZPerm, hc.2.2]

private lemma sp20_disj : ∀ r s : Fin 20, sp20RotZPerm (sp20Src r) ≠ sp20Src r →
    sp20RotZPerm (sp20Src r) ≠ sp20Src s := by decide

private lemma sp20_fixed_even : ∀ r : Fin 20, sp20RotZPerm (sp20Src r) = sp20Src r →
    (sp20Src r).1 % 2 = 0 ∧ ∀ j : Fin 40, j ≠ sp20Src r → (sp20RotZPerm j < sp20Src r ↔ j < sp20Src r) := by
  decide

private lemma sp20_paired_prop : ∀ r : Fin 20, sp20RotZPerm (sp20Src r) ≠ sp20Src r →
    sp20Src r < sp20RotZPerm (sp20Src r) ∧
    sp20BaseZ (sp20RotZPerm (sp20Src r)) = sp20BaseZ (sp20Src r) ∧
    ∀ j : Fin 40, j ≠ sp20Src r → j ≠ sp20RotZPerm (sp20Src r) →
      (sp20RotZPerm j < sp20RotZPerm (sp20Src r) ↔ j < sp20Src r) := by
  decide

private noncomputable def sp20SubMat (t : ℝ) : Matrix (Fin 20) (Fin 20) ℂ :=
  Matrix.of fun r c : Fin 20 => atiyahMat (stereoSpinor (sp20Clamp t).1) (sp20Src r) ⟨2 * c.1, by omega⟩

private lemma sp20SubMat_im_zero (t : ℝ) : (sp20SubMat t).det.im = 0 := by
  refine subDet_im_eq_zero_of_perm_conj (sp20SubMat t) (Equiv.refl _) (fun _ => 1) (by simp) ?_
  intro r c
  have hpoly_real : ∀ i : Fin 40, (atiyahPoly (stereoSpinor (sp20Clamp t).1) i).map (starRingEnd ℂ) =
      atiyahPoly (stereoSpinor (sp20Clamp t).1) i := by
    intro i
    refine atiyahPoly_yRefl_fixed (sp20Clamp t).1 (Equiv.refl _) (fun _ => rfl) (fun u => by
      ext cc; fin_cases cc <;> simp [sp20_y_zero t u]) i rfl (fun _ _ => Iff.rfl)
  simp only [Equiv.refl_apply, one_mul, sp20SubMat, Matrix.of_apply, atiyahMat]
  have hc := congr_arg (fun P : Polynomial ℂ => P.coeff (2 * c.1)) (hpoly_real (sp20Src r))
  simpa [Polynomial.coeff_map] using hc

private lemma continuous_sp20SubMat_re : Continuous (fun t => (sp20SubMat t).det.re) := by
  refine Complex.continuous_re.comp (Continuous.matrix_det (continuous_pi fun r => continuous_pi fun c => ?_))
  exact continuous_atiyahMat_entry sp20Clamp continuous_sp20Clamp_coord sp20Clamp_z_mono (sp20Src r) ⟨2 * c.1, by omega⟩

private lemma sp20SubMat_det_zero_implies_det_zero {t : ℝ} (hsub : (sp20SubMat t).det = 0) :
    atiyahDet (sp20Clamp t) = 0 := by
  let μ : Fin 20 → ℂ := fun r =>
    if sp20RotZPerm (sp20Src r) = sp20Src r then 1
    else (-1 : ℂ) ^ (sp20Src r).1 * (-star (stereoSlope (sp20Clamp t).1 (sp20Src r) (sp20RotZPerm (sp20Src r))))
  have hμ_ne : ∀ r : Fin 20, μ r ≠ 0 := by
    intro r
    by_cases hf : sp20RotZPerm (sp20Src r) = sp20Src r
    · simp [μ, hf]
    · obtain ⟨hlt, hzB, _⟩ := sp20_paired_prop r hf
      have hz_eq : (sp20Clamp t).1 (sp20RotZPerm (sp20Src r)) 2 = (sp20Clamp t).1 (sp20Src r) 2 := by
        simp [sp20Clamp, sp20Raw, hzB]
      have hns := stereoSlope_normSq_eq_one_of_dz_zero (sp20Clamp t).1
        ((sp20Clamp t).2 _ _ hlt.ne) hz_eq
      have hstar_ne : -star (stereoSlope (sp20Clamp t).1 (sp20Src r) (sp20RotZPerm (sp20Src r))) ≠ 0 := by
        intro hz0
        have hst : star (stereoSlope (sp20Clamp t).1 (sp20Src r) (sp20RotZPerm (sp20Src r))) = 0 := neg_eq_zero.mp hz0
        rw [hst, mul_zero] at hns
        norm_num at hns
      simp only [μ, hf, ↓reduceIte]
      exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hstar_ne
  have hsub' : (Matrix.of fun r c : Fin 20 => (atiyahMat (stereoSpinor (sp20Clamp t).1)) (sp20Src r) ⟨2 * c.1, by omega⟩).det = 0 := by
    unfold sp20SubMat at hsub; exact hsub
  have hMdet : (atiyahMat (stereoSpinor (sp20Clamp t).1)).det = 0 := by
    refine det_eq_zero_of_rotZ_evenSubblock_det_zero (m := 20) (atiyahMat (stereoSpinor (sp20Clamp t).1))
      sp20Src sp20Src_inj sp20RotZPerm μ hμ_ne sp20_disj ?_ ?_ hsub'
    · intro r hfix c
      obtain ⟨heven, hside⟩ := sp20_fixed_even r hfix
      have hp := atiyahPoly_rotZ_fixed (sp20Clamp t).1 sp20RotZPerm sp20RotZFn_invol (sp20_rotZ_eq t) (sp20Src r) hfix hside
      have hc := congr_arg (fun P : Polynomial ℂ => P.coeff (2 * c.1 + 1)) hp
      have hpow_i : (-1 : ℂ) ^ (sp20Src r).1 = 1 := by
        rw [show (sp20Src r).1 = 2 * ((sp20Src r).1 / 2) by omega, pow_mul]; norm_num
      have hpow_k : (-1 : ℂ) ^ (2 * c.1 + 1) = -1 := by
        rw [pow_add, pow_mul]; norm_num
      rw [Polynomial.coeff_C_mul, coeff_comp_neg_X', hpow_i, hpow_k, one_mul] at hc
      have hcoef0 : (atiyahPoly (stereoSpinor (sp20Clamp t).1) (sp20Src r)).coeff (2 * c.1 + 1) = 0 := by
        linear_combination hc / 2
      exact hcoef0
    · intro r hnf k
      obtain ⟨hlt, hzB, hside⟩ := sp20_paired_prop r hnf
      have hz_eq : (sp20Clamp t).1 (sp20RotZPerm (sp20Src r)) 2 = (sp20Clamp t).1 (sp20Src r) 2 := by
        simp [sp20Clamp, sp20Raw, hzB]
      have hp := atiyahPoly_rotZ_pair (sp20Clamp t).1 (sp20Clamp t).2 sp20RotZPerm sp20RotZFn_invol (sp20_rotZ_eq t)
        (sp20Src r) hlt hz_eq hside
      have hc := congr_arg (fun P : Polynomial ℂ => P.coeff k.1) hp
      rw [Polynomial.coeff_C_mul, coeff_comp_neg_X'] at hc
      simp only [atiyahMat, μ, hnf, ↓reduceIte, mul_assoc] at hc ⊢
      exact hc
  rw [atiyahDet_eq_stereoMat_div (sp20Clamp t) (sp20Clamp_z_mono t), hMdet, zero_div]

section SignSp20
attribute [local irreducible] Matrix.det

private lemma sp20Clamp_1_eq_pos : 0 < (sp20SubMat 1).det.re := by
  have hp0 : ∀ i : Fin 40, (sp20Clamp 1).1 i 0 = ((1 : ℤ) : ℝ) * (sp20BaseXList.getD i.1 0 : ℝ) := fun i => by
    simp [sp20Clamp, sp20Raw, sp20BaseX]
  have hp1 : ∀ i : Fin 40, (sp20Clamp 1).1 i 1 = ((1 : ℤ) : ℝ) * (sp20BaseYList.getD i.1 0 : ℝ) := fun i => by
    simp [sp20Clamp, sp20Raw, sp20BaseY]
  have hp2 : ∀ i : Fin 40, (sp20Clamp 1).1 i 2 = (sp20BaseZList.getD i.1 0 : ℝ) := fun i => by
    simp [sp20Clamp, sp20Raw, sp20BaseZ]
  have hw := slopeTableOk_mem S_symp_pos hp0 hp1 hp2 ok_sp20_1
  have hmat := matCMem_extractSubEven S_symp_pos (by decide) (by decide) hw sp20Src_len sp20Src_getD
  have hmat' : MatCMem S_symp 20 (extractSubEven 20 (sp20SrcList.map (polyListCIv S_symp (wRead2D w_sp20_1)))) (sp20SubMat 1) := by
    unfold sp20SubMat; exact hmat
  have hg := gaussDetCIv_mem S_symp_pos gauss_sp20_1_eq (CFpIv.ofInt_mem S_symp 1) hmat'
  rw [Int.cast_one, one_mul] at hg
  exact pos_re_of_CFpMem_symp S_symp_pos hg sign_sp20_1

private lemma sp20Clamp_2_eq_neg : (sp20SubMat 2).det.re < 0 := by
  have hp0 : ∀ i : Fin 40, (sp20Clamp 2).1 i 0 = ((2 : ℤ) : ℝ) * (sp20BaseXList.getD i.1 0 : ℝ) := fun i => by
    simp [sp20Clamp, sp20Raw, sp20BaseX]
  have hp1 : ∀ i : Fin 40, (sp20Clamp 2).1 i 1 = ((2 : ℤ) : ℝ) * (sp20BaseYList.getD i.1 0 : ℝ) := fun i => by
    simp [sp20Clamp, sp20Raw, sp20BaseY]
  have hp2 : ∀ i : Fin 40, (sp20Clamp 2).1 i 2 = (sp20BaseZList.getD i.1 0 : ℝ) := fun i => by
    simp [sp20Clamp, sp20Raw, sp20BaseZ]
  have hw := slopeTableOk_mem S_symp_pos hp0 hp1 hp2 ok_sp20_2
  have hmat := matCMem_extractSubEven S_symp_pos (by decide) (by decide) hw sp20Src_len sp20Src_getD
  have hmat' : MatCMem S_symp 20 (extractSubEven 20 (sp20SrcList.map (polyListCIv S_symp (wRead2D w_sp20_2)))) (sp20SubMat 2) := by
    unfold sp20SubMat; exact hmat
  have hg := gaussDetCIv_mem S_symp_pos gauss_sp20_2_eq (CFpIv.ofInt_mem S_symp 1) hmat'
  rw [Int.cast_one, one_mul] at hg
  exact neg_re_of_CFpMem_symp S_symp_pos hg sign_sp20_2

end SignSp20

section IrredSp20
attribute [local irreducible] atiyahDet sp20SubMat sp20Clamp

private def sp20SymplecticConfig (t : ℝ) : SymplecticConfig 20 where
  p := (sp20Clamp t).1
  distinct := (sp20Clamp t).2
  antipodal := sp20AntiPerm
  involutive := sp20AntiFn_invol
  neg_eq := by
    intro i k
    have hc := sp20_anti_coords i
    fin_cases k
    · simp [sp20Clamp, sp20Raw, sp20AntiPerm, hc.1]
    · simp [sp20Clamp, sp20Raw, sp20AntiPerm, hc.2.1]
    · simp [sp20Clamp, sp20Raw, sp20AntiPerm, hc.2.2]

/-- **Planar Symplectic $\\mathrm{Sp}(20)$ (`n = 40`) C1/C2 Singular Witness:**
There exists a planar centrally symmetric $40$-point configuration with $D_{40} = 0$. -/
theorem exists_planar_symplectic_20_atiyahDet_zero :
    ∃ c : SymplecticConfig 20, IsCoplanar (symplecticPoints c) ∧ atiyahDet (symplecticPoints c) = 0 := by
  let f : ℝ → ℝ := fun t => (sp20SubMat t).det.re
  have hmem : (0 : ℝ) ∈ Set.Icc (f 2) (f 1) := ⟨sp20Clamp_2_eq_neg.le, sp20Clamp_1_eq_pos.le⟩
  obtain ⟨t₀, _, hft₀⟩ := intermediate_value_Icc' (by norm_num : (1 : ℝ) ≤ 2)
    continuous_sp20SubMat_re.continuousOn hmem
  have hsub0 : (sp20SubMat t₀).det = 0 := Complex.ext hft₀ (sp20SubMat_im_zero t₀)
  refine ⟨sp20SymplecticConfig t₀, ?_, sp20SubMat_det_zero_implies_det_zero hsub0⟩
  exact ⟨![0, 1, 0], 0, Or.inr (Or.inl one_ne_zero), fun i => by simp [symplecticPoints, sp20SymplecticConfig, sp20_y_zero t₀ i]⟩

/-- **Disproof of Symplectic Determinant Nonzero Conjecture** at `Sp(20)` (`n = 40`). -/
theorem disproof_symplectic_20_det_nonzero : ¬ SymplecticAtiyahDetNonzeroProp 20 := by
  intro h
  obtain ⟨c, _, hc0⟩ := exists_planar_symplectic_20_atiyahDet_zero
  exact h c hc0

/-- **Disproof of Symplectic Atiyah Conjecture 1** at `Sp(20)` (`n = 40`). -/
theorem disproof_symplectic_20_conjecture_1 : ¬ SymplecticAtiyahConjecture1Prop 20 := by
  intro h
  obtain ⟨c, _, hc0⟩ := exists_planar_symplectic_20_atiyahDet_zero
  exact not_linearIndependent_of_atiyahDet_zero (by omega) (symplecticPoints c) hc0 (h c)

/-- **Disproof of Symplectic Atiyah–Sutcliffe Conjecture 2** at `Sp(20)` (`n = 40`). -/
theorem disproof_symplectic_20_conjecture_2 : ¬ SymplecticAtiyahSutcliffeConjecture2Prop 20 := by
  intro h
  obtain ⟨c, _, hc0⟩ := exists_planar_symplectic_20_atiyahDet_zero
  have hle := h c
  rw [hc0, norm_zero] at hle
  linarith

end IrredSp20

end PlanarSp20

/-! ## Section 5: Strictly Non-Coplanar 3D $\\mathrm{Sp}(18)$ ($N = 36$) Certified Counterexamples -/

section NoncoplanarSp18

private lemma sp18Clamp_noncoplanar (t : ℝ) : Noncoplanar3D (sp18Clamp t).1 := by
  rintro ⟨a, b, c, d, hne, hplane⟩
  have hs : (0 : ℝ) < max t 1 := lt_of_lt_of_le zero_lt_one (le_max_right t 1)
  have h0 := hplane ⟨0, by omega⟩
  have h1 := hplane ⟨1, by omega⟩
  have h6 := hplane ⟨6, by omega⟩
  have h8 := hplane ⟨8, by omega⟩
  have v0 : sp18BaseX ⟨0, by omega⟩ = 0 ∧ sp18BaseY ⟨0, by omega⟩ = 0 ∧ sp18BaseZ ⟨0, by omega⟩ = -4433 := by decide
  have v1 : sp18BaseX ⟨1, by omega⟩ = 0 ∧ sp18BaseY ⟨1, by omega⟩ = 0 ∧ sp18BaseZ ⟨1, by omega⟩ = -4428 := by decide
  have v6 : sp18BaseX ⟨6, by omega⟩ = 1300 ∧ sp18BaseY ⟨6, by omega⟩ = 0 ∧ sp18BaseZ ⟨6, by omega⟩ = -4249 := by decide
  have v8 : sp18BaseX ⟨8, by omega⟩ = 660 ∧ sp18BaseY ⟨8, by omega⟩ = 1120 ∧ sp18BaseZ ⟨8, by omega⟩ = -4249 := by decide
  simp only [sp18Clamp, sp18Raw, v0.1, v0.2.1, v0.2.2, v1.1, v1.2.1, v1.2.2, v6.1, v6.2.1, v6.2.2,
    v8.1, v8.2.1, v8.2.2, vec3_val0, vec3_val1, vec3_val2] at h0 h1 h6 h8
  push_cast at h0 h1 h6 h8
  have hc0 : c = 0 := by linarith
  have hd0 : d = 0 := by linarith
  have ha0 : a = 0 := by
    have hm : a * (max t 1 * 1300) = 0 := by linarith
    exact (mul_eq_zero.mp hm).resolve_right (mul_ne_zero hs.ne' (by norm_num))
  have hb0 : b = 0 := by
    have hm : b * (max t 1 * 1120) = 0 := by linarith
    exact (mul_eq_zero.mp hm).resolve_right (mul_ne_zero hs.ne' (by norm_num))
  rcases hne with h | h | h
  · exact h ha0
  · exact h hb0
  · exact h hc0

private lemma sp18_rotZ_eq (t : ℝ) (i : Fin 36) :
    (sp18Clamp t).1 (sp18RotZPerm i) = ![-((sp18Clamp t).1 i 0), -((sp18Clamp t).1 i 1), (sp18Clamp t).1 i 2] := by
  have hc := sp18_rotz_coords i
  ext c; fin_cases c
  · simp [sp18Clamp, sp18Raw, sp18RotZPerm, hc.1]
  · simp [sp18Clamp, sp18Raw, sp18RotZPerm, hc.2.1]
  · simp [sp18Clamp, sp18Raw, sp18RotZPerm, hc.2.2]

private lemma sp18_yRef_eq (t : ℝ) (i : Fin 36) :
    (sp18Clamp t).1 (sp18YRefPerm i) = ![(sp18Clamp t).1 i 0, -((sp18Clamp t).1 i 1), (sp18Clamp t).1 i 2] := by
  have hc := sp18_yref_coords i
  ext c; fin_cases c
  · simp [sp18Clamp, sp18Raw, sp18YRefPerm, hc.1]
  · simp [sp18Clamp, sp18Raw, sp18YRefPerm, hc.2.1]
  · simp [sp18Clamp, sp18Raw, sp18YRefPerm, hc.2.2]

private lemma sp18_disj : ∀ r s : Fin 18, sp18RotZPerm (sp18Src r) ≠ sp18Src r →
    sp18RotZPerm (sp18Src r) ≠ sp18Src s := by decide

private lemma sp18_fixed_even : ∀ r : Fin 18, sp18RotZPerm (sp18Src r) = sp18Src r →
    (sp18Src r).1 % 2 = 0 ∧ ∀ j : Fin 36, j ≠ sp18Src r → (sp18RotZPerm j < sp18Src r ↔ j < sp18Src r) := by
  decide

private lemma sp18_paired_prop : ∀ r : Fin 18, sp18RotZPerm (sp18Src r) ≠ sp18Src r →
    sp18Src r < sp18RotZPerm (sp18Src r) ∧
    sp18BaseZ (sp18RotZPerm (sp18Src r)) = sp18BaseZ (sp18Src r) ∧
    ∀ j : Fin 36, j ≠ sp18Src r → j ≠ sp18RotZPerm (sp18Src r) →
      (sp18RotZPerm j < sp18RotZPerm (sp18Src r) ↔ j < sp18Src r) := by
  decide

private noncomputable def sp18SubMat (t : ℝ) : Matrix (Fin 18) (Fin 18) ℂ :=
  Matrix.of fun r c : Fin 18 => atiyahMat (stereoSpinor (sp18Clamp t).1) (sp18Src r) ⟨2 * c.1, by omega⟩

private def sp18SubYPermList : List ℕ := [0, 1, 2, 3, 5, 4, 6, 8, 7, 9, 11, 10, 12, 14, 13, 15, 16, 17]
private def sp18SubYFn (r : Fin 18) : Fin 18 := ⟨sp18SubYPermList.getD r.1 0, by
  have h : ∀ k : Fin 18, sp18SubYPermList.getD k.1 0 < 18 := by decide
  exact h r⟩
private def sp18SubYPerm : Equiv.Perm (Fin 18) where
  toFun := sp18SubYFn
  invFun := sp18SubYFn
  left_inv := by decide
  right_inv := by decide

private lemma sp18SubYPerm_sign : Equiv.Perm.sign sp18SubYPerm = 1 := by decide
private lemma sp18_src_yref : ∀ r : Fin 18, sp18YRefPerm (sp18Src r) = sp18Src (sp18SubYPerm r) := by decide

private lemma sp18SubMat_im_zero (t : ℝ) : (sp18SubMat t).det.im = 0 := by
  let f : Fin 18 → ℂ := fun r => if sp18SubYPerm r = r then 1 else -Complex.I
  have hprod : (∏ r : Fin 18, f r) * (Equiv.Perm.sign sp18SubYPerm : ℂ) = 1 := by
    rw [sp18SubYPerm_sign]
    have hc : (Finset.univ.filter (fun r : Fin 18 => sp18SubYPerm r ≠ r)).card = 8 := by decide
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun r : Fin 18 => sp18SubYPerm r = r)]
    have p1 : (∏ r ∈ Finset.univ.filter (fun r : Fin 18 => sp18SubYPerm r = r), f r) = 1 :=
      Finset.prod_eq_one fun r hr => by simp [f, (Finset.mem_filter.mp hr).2]
    have p2 : (∏ r ∈ Finset.univ.filter (fun r : Fin 18 => ¬ sp18SubYPerm r = r), f r) = (-Complex.I) ^ 8 := by
      calc (∏ r ∈ Finset.univ.filter (fun r : Fin 18 => ¬ sp18SubYPerm r = r), f r)
        = ∏ _r ∈ Finset.univ.filter (fun r : Fin 18 => sp18SubYPerm r ≠ r), (-Complex.I) :=
          Finset.prod_congr (by ext x; simp) fun r hr => by simp [f, (Finset.mem_filter.mp hr).2]
        _ = (-Complex.I) ^ 8 := by rw [Finset.prod_const, hc]
    have h8 : (-Complex.I) ^ 8 = (1 : ℂ) := by
      calc (-Complex.I) ^ 8 = ((-Complex.I) ^ 2) ^ 4 := by ring
        _ = (-1 : ℂ) ^ 4 := by rw [neg_sq, Complex.I_sq]
        _ = 1 := by norm_num
    rw [p1, p2, one_mul, h8]; norm_num
  refine subDet_im_eq_zero_of_perm_conj (sp18SubMat t) sp18SubYPerm f hprod ?_
  intro r c
  rw [sp18SubMat, Matrix.of_apply, Matrix.of_apply, atiyahMat, atiyahMat, ← sp18_src_yref r]
  have hs : (0 : ℝ) < max t 1 := lt_of_lt_of_le zero_lt_one (le_max_right t 1)
  by_cases hfix : sp18SubYPerm r = r
  · have hfixN : sp18YRefPerm (sp18Src r) = sp18Src r := by rw [sp18_src_yref r, hfix]
    have hside : ∀ j : Fin 36, j ≠ sp18Src r → (sp18YRefPerm j < sp18Src r ↔ j < sp18Src r) := by
      revert r hfix; decide
    have hp := atiyahPoly_yRefl_fixed (sp18Clamp t).1 sp18YRefPerm sp18YRefFn_invol (sp18_yRef_eq t) (sp18Src r) hfixN hside
    have hc := congr_arg (fun P : Polynomial ℂ => P.coeff (2 * c.1)) hp
    simp only [Polynomial.coeff_map] at hc
    simpa [f, hfix, hfixN] using hc
  · -- Four swapped blocks: r ∈ {4,5,7,8,10,11,13,14} corresponding to 4-blocks at a = 8, 14, 20, 26
    have hblk_cases : (r.1 = 4 ∧ (sp18Src r).1 = 8 ∧ (sp18Src (sp18SubYPerm r)).1 = 10) ∨
        (r.1 = 5 ∧ (sp18Src r).1 = 10 ∧ (sp18Src (sp18SubYPerm r)).1 = 8) ∨
        (r.1 = 7 ∧ (sp18Src r).1 = 14 ∧ (sp18Src (sp18SubYPerm r)).1 = 16) ∨
        (r.1 = 8 ∧ (sp18Src r).1 = 16 ∧ (sp18Src (sp18SubYPerm r)).1 = 14) ∨
        (r.1 = 10 ∧ (sp18Src r).1 = 20 ∧ (sp18Src (sp18SubYPerm r)).1 = 22) ∨
        (r.1 = 11 ∧ (sp18Src r).1 = 22 ∧ (sp18Src (sp18SubYPerm r)).1 = 20) ∨
        (r.1 = 13 ∧ (sp18Src r).1 = 26 ∧ (sp18Src (sp18SubYPerm r)).1 = 28) ∨
        (r.1 = 14 ∧ (sp18Src r).1 = 28 ∧ (sp18Src (sp18SubYPerm r)).1 = 26) := by
      revert r hfix; decide
    have hcheck_block : ∀ (a : Fin 36) (ha3 : a.1 + 3 < 36),
        sp18YRefPerm a = ⟨a.1 + 2, by omega⟩ →
        sp18YRefPerm ⟨a.1 + 1, by omega⟩ = ⟨a.1 + 3, by omega⟩ →
        (0 < sp18BaseX a ∧ 0 < sp18BaseY a ∧
          sp18BaseX ⟨a.1 + 1, by omega⟩ = -sp18BaseX a ∧ sp18BaseY ⟨a.1 + 1, by omega⟩ = -sp18BaseY a ∧ sp18BaseZ ⟨a.1 + 1, by omega⟩ = sp18BaseZ a ∧
          sp18BaseX ⟨a.1 + 2, by omega⟩ = sp18BaseX a ∧ sp18BaseY ⟨a.1 + 2, by omega⟩ = -sp18BaseY a ∧ sp18BaseZ ⟨a.1 + 2, by omega⟩ = sp18BaseZ a ∧
          sp18BaseX ⟨a.1 + 3, by omega⟩ = -sp18BaseX a ∧ sp18BaseY ⟨a.1 + 3, by omega⟩ = sp18BaseY a ∧ sp18BaseZ ⟨a.1 + 3, by omega⟩ = sp18BaseZ a) →
        (∀ j : Fin 36, j.1 ≠ a.1 → j.1 ≠ a.1 + 1 → j.1 ≠ a.1 + 2 → j.1 ≠ a.1 + 3 →
          (sp18YRefPerm j < ⟨a.1 + 2, by omega⟩ ↔ j < a)) →
        (atiyahPoly (stereoSpinor (sp18Clamp t).1) ⟨a.1 + 2, by omega⟩).map (starRingEnd ℂ) =
          Polynomial.C (-Complex.I) * atiyahPoly (stereoSpinor (sp18Clamp t).1) a ∧
        (atiyahPoly (stereoSpinor (sp18Clamp t).1) a).map (starRingEnd ℂ) =
          Polynomial.C (-Complex.I) * atiyahPoly (stereoSpinor (sp18Clamp t).1) ⟨a.1 + 2, by omega⟩ := by
      intro a ha3 hσa hσa1 ⟨hxpos, hypos, h1x, h1y, h1z, h2x, h2y, h2z, h3x, h3y, h3z⟩ hside
      have hxR : ∃ xR yR zR : ℝ, 0 < xR ∧ 0 < yR ∧
          (sp18Clamp t).1 a = ![xR, yR, zR] ∧
          (sp18Clamp t).1 ⟨a.1 + 1, by omega⟩ = ![-xR, -yR, zR] ∧
          (sp18Clamp t).1 ⟨a.1 + 2, by omega⟩ = ![xR, -yR, zR] ∧
          (sp18Clamp t).1 ⟨a.1 + 3, by omega⟩ = ![-xR, yR, zR] := by
        refine ⟨max t 1 * (sp18BaseX a : ℝ), max t 1 * (sp18BaseY a : ℝ), (sp18BaseZ a : ℝ),
          mul_pos hs (by exact_mod_cast hxpos), mul_pos hs (by exact_mod_cast hypos), ?_, ?_, ?_, ?_⟩
        · ext kk; fin_cases kk <;> rfl
        · ext kk; fin_cases kk
          · simp [sp18Clamp, sp18Raw, h1x]
          · simp [sp18Clamp, sp18Raw, h1y]
          · simp [sp18Clamp, sp18Raw, h1z]
        · ext kk; fin_cases kk
          · simp [sp18Clamp, sp18Raw, h2x]
          · simp [sp18Clamp, sp18Raw, h2y]
          · simp [sp18Clamp, sp18Raw, h2z]
        · ext kk; fin_cases kk
          · simp [sp18Clamp, sp18Raw, h3x]
          · simp [sp18Clamp, sp18Raw, h3y]
          · simp [sp18Clamp, sp18Raw, h3z]
      exact ⟨atiyahPoly_yRefl_block (sp18Clamp t).1 sp18YRefPerm sp18YRefFn_invol (sp18_yRef_eq t) a ha3 hσa hσa1 hxR hside,
        atiyahPoly_yRefl_block_rev (sp18Clamp t).1 sp18YRefPerm sp18YRefFn_invol (sp18_yRef_eq t) a ha3 hσa hσa1 hxR hside⟩
    have hpoly_swap : (atiyahPoly (stereoSpinor (sp18Clamp t).1) (sp18YRefPerm (sp18Src r))).map (starRingEnd ℂ) =
        Polynomial.C (-Complex.I) * atiyahPoly (stereoSpinor (sp18Clamp t).1) (sp18Src r) := by
      rcases hblk_cases with ⟨_, hsr, hsyr⟩ | ⟨_, hsr, hsyr⟩ | ⟨_, hsr, hsyr⟩ | ⟨_, hsr, hsyr⟩ |
          ⟨_, hsr, hsyr⟩ | ⟨_, hsr, hsyr⟩ | ⟨_, hsr, hsyr⟩ | ⟨_, hsr, hsyr⟩
      · have hres := hcheck_block ⟨8, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
        have hs1 : sp18Src r = ⟨8, by decide⟩ := Fin.ext hsr
        have hs2 : sp18YRefPerm (sp18Src r) = ⟨10, by decide⟩ := by rw [sp18_src_yref]; exact Fin.ext hsyr
        rw [hs2, hs1]; exact hres.1
      · have hres := hcheck_block ⟨8, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
        have hs1 : sp18Src r = ⟨10, by decide⟩ := Fin.ext hsr
        have hs2 : sp18YRefPerm (sp18Src r) = ⟨8, by decide⟩ := by rw [sp18_src_yref]; exact Fin.ext hsyr
        rw [hs2, hs1]; exact hres.2
      · have hres := hcheck_block ⟨14, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
        have hs1 : sp18Src r = ⟨14, by decide⟩ := Fin.ext hsr
        have hs2 : sp18YRefPerm (sp18Src r) = ⟨16, by decide⟩ := by rw [sp18_src_yref]; exact Fin.ext hsyr
        rw [hs2, hs1]; exact hres.1
      · have hres := hcheck_block ⟨14, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
        have hs1 : sp18Src r = ⟨16, by decide⟩ := Fin.ext hsr
        have hs2 : sp18YRefPerm (sp18Src r) = ⟨14, by decide⟩ := by rw [sp18_src_yref]; exact Fin.ext hsyr
        rw [hs2, hs1]; exact hres.2
      · have hres := hcheck_block ⟨20, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
        have hs1 : sp18Src r = ⟨20, by decide⟩ := Fin.ext hsr
        have hs2 : sp18YRefPerm (sp18Src r) = ⟨22, by decide⟩ := by rw [sp18_src_yref]; exact Fin.ext hsyr
        rw [hs2, hs1]; exact hres.1
      · have hres := hcheck_block ⟨20, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
        have hs1 : sp18Src r = ⟨22, by decide⟩ := Fin.ext hsr
        have hs2 : sp18YRefPerm (sp18Src r) = ⟨20, by decide⟩ := by rw [sp18_src_yref]; exact Fin.ext hsyr
        rw [hs2, hs1]; exact hres.2
      · have hres := hcheck_block ⟨26, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
        have hs1 : sp18Src r = ⟨26, by decide⟩ := Fin.ext hsr
        have hs2 : sp18YRefPerm (sp18Src r) = ⟨28, by decide⟩ := by rw [sp18_src_yref]; exact Fin.ext hsyr
        rw [hs2, hs1]; exact hres.1
      · have hres := hcheck_block ⟨26, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
        have hs1 : sp18Src r = ⟨28, by decide⟩ := Fin.ext hsr
        have hs2 : sp18YRefPerm (sp18Src r) = ⟨26, by decide⟩ := by rw [sp18_src_yref]; exact Fin.ext hsyr
        rw [hs2, hs1]; exact hres.2
    have hc := congr_arg (fun P : Polynomial ℂ => P.coeff (2 * c.1)) hpoly_swap
    simp only [Polynomial.coeff_map, Polynomial.coeff_C_mul] at hc
    simpa [f, hfix] using hc

private lemma continuous_sp18SubMat_re : Continuous (fun t => (sp18SubMat t).det.re) := by
  refine Complex.continuous_re.comp (Continuous.matrix_det (continuous_pi fun r => continuous_pi fun c => ?_))
  exact continuous_atiyahMat_entry sp18Clamp continuous_sp18Clamp_coord sp18Clamp_z_mono (sp18Src r) ⟨2 * c.1, by omega⟩

private lemma sp18SubMat_det_zero_implies_det_zero {t : ℝ} (hsub : (sp18SubMat t).det = 0) :
    atiyahDet (sp18Clamp t) = 0 := by
  let μ : Fin 18 → ℂ := fun r =>
    if sp18RotZPerm (sp18Src r) = sp18Src r then 1
    else (-1 : ℂ) ^ (sp18Src r).1 * (-star (stereoSlope (sp18Clamp t).1 (sp18Src r) (sp18RotZPerm (sp18Src r))))
  have hμ_ne : ∀ r : Fin 18, μ r ≠ 0 := by
    intro r
    by_cases hf : sp18RotZPerm (sp18Src r) = sp18Src r
    · simp [μ, hf]
    · obtain ⟨hlt, hzB, _⟩ := sp18_paired_prop r hf
      have hz_eq : (sp18Clamp t).1 (sp18RotZPerm (sp18Src r)) 2 = (sp18Clamp t).1 (sp18Src r) 2 := by
        simp [sp18Clamp, sp18Raw, hzB]
      have hns := stereoSlope_normSq_eq_one_of_dz_zero (sp18Clamp t).1
        ((sp18Clamp t).2 _ _ hlt.ne) hz_eq
      have hstar_ne : -star (stereoSlope (sp18Clamp t).1 (sp18Src r) (sp18RotZPerm (sp18Src r))) ≠ 0 := by
        intro hz0
        have hst : star (stereoSlope (sp18Clamp t).1 (sp18Src r) (sp18RotZPerm (sp18Src r))) = 0 := neg_eq_zero.mp hz0
        rw [hst, mul_zero] at hns
        norm_num at hns
      simp only [μ, hf, ↓reduceIte]
      exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hstar_ne
  have hsub' : (Matrix.of fun r c : Fin 18 => (atiyahMat (stereoSpinor (sp18Clamp t).1)) (sp18Src r) ⟨2 * c.1, by omega⟩).det = 0 := by
    unfold sp18SubMat at hsub; exact hsub
  have hMdet : (atiyahMat (stereoSpinor (sp18Clamp t).1)).det = 0 := by
    refine det_eq_zero_of_rotZ_evenSubblock_det_zero (m := 18) (atiyahMat (stereoSpinor (sp18Clamp t).1))
      sp18Src sp18Src_inj sp18RotZPerm μ hμ_ne sp18_disj ?_ ?_ hsub'
    · intro r hfix c
      obtain ⟨heven, hside⟩ := sp18_fixed_even r hfix
      have hp := atiyahPoly_rotZ_fixed (sp18Clamp t).1 sp18RotZPerm sp18RotZFn_invol (sp18_rotZ_eq t) (sp18Src r) hfix hside
      have hc := congr_arg (fun P : Polynomial ℂ => P.coeff (2 * c.1 + 1)) hp
      have hpow_i : (-1 : ℂ) ^ (sp18Src r).1 = 1 := by
        rw [show (sp18Src r).1 = 2 * ((sp18Src r).1 / 2) by omega, pow_mul]; norm_num
      have hpow_k : (-1 : ℂ) ^ (2 * c.1 + 1) = -1 := by
        rw [pow_add, pow_mul]; norm_num
      rw [Polynomial.coeff_C_mul, coeff_comp_neg_X', hpow_i, hpow_k, one_mul] at hc
      have hcoef0 : (atiyahPoly (stereoSpinor (sp18Clamp t).1) (sp18Src r)).coeff (2 * c.1 + 1) = 0 := by
        linear_combination hc / 2
      exact hcoef0
    · intro r hnf k
      obtain ⟨hlt, hzB, hside⟩ := sp18_paired_prop r hnf
      have hz_eq : (sp18Clamp t).1 (sp18RotZPerm (sp18Src r)) 2 = (sp18Clamp t).1 (sp18Src r) 2 := by
        simp [sp18Clamp, sp18Raw, hzB]
      have hp := atiyahPoly_rotZ_pair (sp18Clamp t).1 (sp18Clamp t).2 sp18RotZPerm sp18RotZFn_invol (sp18_rotZ_eq t)
        (sp18Src r) hlt hz_eq hside
      have hc := congr_arg (fun P : Polynomial ℂ => P.coeff k.1) hp
      rw [Polynomial.coeff_C_mul, coeff_comp_neg_X'] at hc
      simp only [atiyahMat, μ, hnf, ↓reduceIte, mul_assoc] at hc ⊢
      exact hc
  rw [atiyahDet_eq_stereoMat_div (sp18Clamp t) (sp18Clamp_z_mono t), hMdet, zero_div]

section SignSp18
attribute [local irreducible] Matrix.det

private lemma sp18Clamp_7_eq_pos : 0 < (sp18SubMat 7).det.re := by
  have hp0 : ∀ i : Fin 36, (sp18Clamp 7).1 i 0 = ((7 : ℤ) : ℝ) * (sp18BaseXList.getD i.1 0 : ℝ) := fun i => by
    simp [sp18Clamp, sp18Raw, sp18BaseX]
  have hp1 : ∀ i : Fin 36, (sp18Clamp 7).1 i 1 = ((7 : ℤ) : ℝ) * (sp18BaseYList.getD i.1 0 : ℝ) := fun i => by
    simp [sp18Clamp, sp18Raw, sp18BaseY]
  have hp2 : ∀ i : Fin 36, (sp18Clamp 7).1 i 2 = (sp18BaseZList.getD i.1 0 : ℝ) := fun i => by
    simp [sp18Clamp, sp18Raw, sp18BaseZ]
  have hw := slopeTableOk_mem S_symp_pos hp0 hp1 hp2 ok_sp18_7
  have hmat := matCMem_extractSubEven S_symp_pos (by decide) (by decide) hw sp18Src_len sp18Src_getD
  have hmat' : MatCMem S_symp 18 (extractSubEven 18 (sp18SrcList.map (polyListCIv S_symp (wRead2D w_sp18_7)))) (sp18SubMat 7) := by
    unfold sp18SubMat; exact hmat
  have hg := gaussDetCIv_mem S_symp_pos gauss_sp18_7_eq (CFpIv.ofInt_mem S_symp 1) hmat'
  rw [Int.cast_one, one_mul] at hg
  exact pos_re_of_CFpMem_symp S_symp_pos hg sign_sp18_7

private lemma sp18Clamp_8_eq_neg : (sp18SubMat 8).det.re < 0 := by
  have hp0 : ∀ i : Fin 36, (sp18Clamp 8).1 i 0 = ((8 : ℤ) : ℝ) * (sp18BaseXList.getD i.1 0 : ℝ) := fun i => by
    simp [sp18Clamp, sp18Raw, sp18BaseX]
  have hp1 : ∀ i : Fin 36, (sp18Clamp 8).1 i 1 = ((8 : ℤ) : ℝ) * (sp18BaseYList.getD i.1 0 : ℝ) := fun i => by
    simp [sp18Clamp, sp18Raw, sp18BaseY]
  have hp2 : ∀ i : Fin 36, (sp18Clamp 8).1 i 2 = (sp18BaseZList.getD i.1 0 : ℝ) := fun i => by
    simp [sp18Clamp, sp18Raw, sp18BaseZ]
  have hw := slopeTableOk_mem S_symp_pos hp0 hp1 hp2 ok_sp18_8
  have hmat := matCMem_extractSubEven S_symp_pos (by decide) (by decide) hw sp18Src_len sp18Src_getD
  have hmat' : MatCMem S_symp 18 (extractSubEven 18 (sp18SrcList.map (polyListCIv S_symp (wRead2D w_sp18_8)))) (sp18SubMat 8) := by
    unfold sp18SubMat; exact hmat
  have hg := gaussDetCIv_mem S_symp_pos gauss_sp18_8_eq (CFpIv.ofInt_mem S_symp 1) hmat'
  rw [Int.cast_one, one_mul] at hg
  exact neg_re_of_CFpMem_symp S_symp_pos hg sign_sp18_8

end SignSp18

section IrredSp18
attribute [local irreducible] atiyahDet sp18SubMat sp18Clamp

private def sp18SymplecticConfig (t : ℝ) : SymplecticConfig 18 where
  p := (sp18Clamp t).1
  distinct := (sp18Clamp t).2
  antipodal := sp18AntiPerm
  involutive := sp18AntiFn_invol
  neg_eq := by
    intro i k
    have hc := sp18_anti_coords i
    fin_cases k
    · simp [sp18Clamp, sp18Raw, sp18AntiPerm, hc.1]
    · simp [sp18Clamp, sp18Raw, sp18AntiPerm, hc.2.1]
    · simp [sp18Clamp, sp18Raw, sp18AntiPerm, hc.2.2]

/-- **Strictly Non-Coplanar 3D Symplectic $\\mathrm{Sp}(18)$ (`n = 36`) C1/C2 Witness:**
There exists a strictly non-coplanar centrally symmetric $36$-point configuration with $D_{36} = 0$. -/
theorem exists_noncoplanar_symplectic_18_atiyahDet_zero :
    ∃ c : SymplecticConfig 18, Noncoplanar3D c.p ∧ atiyahDet (symplecticPoints c) = 0 := by
  let f : ℝ → ℝ := fun t => (sp18SubMat t).det.re
  have hmem : (0 : ℝ) ∈ Set.Icc (f 8) (f 7) := ⟨sp18Clamp_8_eq_neg.le, sp18Clamp_7_eq_pos.le⟩
  obtain ⟨t₀, _, hft₀⟩ := intermediate_value_Icc' (by norm_num : (7 : ℝ) ≤ 8)
    continuous_sp18SubMat_re.continuousOn hmem
  have hsub0 : (sp18SubMat t₀).det = 0 := Complex.ext hft₀ (sp18SubMat_im_zero t₀)
  exact ⟨sp18SymplecticConfig t₀, sp18Clamp_noncoplanar t₀, sp18SubMat_det_zero_implies_det_zero hsub0⟩

/-- **Disproof of Symplectic Determinant Nonzero Conjecture** at `Sp(18)` (`n = 36`). -/
theorem disproof_symplectic_18_det_nonzero : ¬ SymplecticAtiyahDetNonzeroProp 18 := by
  intro h
  obtain ⟨c, _, hc0⟩ := exists_noncoplanar_symplectic_18_atiyahDet_zero
  exact h c hc0

/-- **Disproof of Symplectic Atiyah Conjecture 1** at `Sp(18)` (`n = 36`). -/
theorem disproof_symplectic_18_conjecture_1 : ¬ SymplecticAtiyahConjecture1Prop 18 := by
  intro h
  obtain ⟨c, _, hc0⟩ := exists_noncoplanar_symplectic_18_atiyahDet_zero
  exact not_linearIndependent_of_atiyahDet_zero (by omega) (symplecticPoints c) hc0 (h c)

/-- **Disproof of Symplectic Atiyah–Sutcliffe Conjecture 2** at `Sp(18)` (`n = 36`). -/
theorem disproof_symplectic_18_conjecture_2 : ¬ SymplecticAtiyahSutcliffeConjecture2Prop 18 := by
  intro h
  obtain ⟨c, _, hc0⟩ := exists_noncoplanar_symplectic_18_atiyahDet_zero
  have hle := h c
  rw [hc0, norm_zero] at hle
  linarith

end IrredSp18

end NoncoplanarSp18

/-! ## Section 6: Strictly Non-Coplanar 3D $B_{18}$ ($\\mathrm{SO}(37)$, $N = 37$) Certified Counterexamples -/

section NoncoplanarB18

private lemma b18Clamp_noncoplanar (t : ℝ) : Noncoplanar3D (b18Clamp t).1 := by
  rintro ⟨a, b, c, d, hne, hplane⟩
  have hs : (0 : ℝ) < max t 1 := lt_of_lt_of_le zero_lt_one (le_max_right t 1)
  have h0 := hplane ⟨0, by omega⟩
  have h18 := hplane ⟨18, by omega⟩
  have h6 := hplane ⟨6, by omega⟩
  have h8 := hplane ⟨8, by omega⟩
  have v0 : b18BaseX ⟨0, by omega⟩ = 0 ∧ b18BaseY ⟨0, by omega⟩ = 0 ∧ b18BaseZ ⟨0, by omega⟩ = -5392 := by decide
  have v18 : b18BaseX ⟨18, by omega⟩ = 0 ∧ b18BaseY ⟨18, by omega⟩ = 0 ∧ b18BaseZ ⟨18, by omega⟩ = 0 := by decide
  have v6 : b18BaseX ⟨6, by omega⟩ = 1235 ∧ b18BaseY ⟨6, by omega⟩ = 0 ∧ b18BaseZ ⟨6, by omega⟩ = -5213 := by decide
  have v8 : b18BaseX ⟨8, by omega⟩ = 627 ∧ b18BaseY ⟨8, by omega⟩ = 1064 ∧ b18BaseZ ⟨8, by omega⟩ = -5213 := by decide
  simp only [b18Clamp, b18Raw, v0.1, v0.2.1, v0.2.2, v18.1, v18.2.1, v18.2.2, v6.1, v6.2.1, v6.2.2,
    v8.1, v8.2.1, v8.2.2, vec3_val0, vec3_val1, vec3_val2] at h0 h18 h6 h8
  push_cast at h0 h18 h6 h8
  have hd0 : d = 0 := by linarith
  have hc0 : c = 0 := by linarith
  have ha0 : a = 0 := by
    have hm : a * (max t 1 * 1235) = 0 := by linarith
    exact (mul_eq_zero.mp hm).resolve_right (mul_ne_zero hs.ne' (by norm_num))
  have hb0 : b = 0 := by
    have hm : b * (max t 1 * 1064) = 0 := by linarith
    exact (mul_eq_zero.mp hm).resolve_right (mul_ne_zero hs.ne' (by norm_num))
  rcases hne with h | h | h
  · exact h ha0
  · exact h hb0
  · exact h hc0

private lemma b18_rotZ_eq (t : ℝ) (i : Fin 37) :
    (b18Clamp t).1 (b18RotZPerm i) = ![-((b18Clamp t).1 i 0), -((b18Clamp t).1 i 1), (b18Clamp t).1 i 2] := by
  have hc := b18_rotz_coords i
  ext c; fin_cases c
  · simp [b18Clamp, b18Raw, b18RotZPerm, hc.1]
  · simp [b18Clamp, b18Raw, b18RotZPerm, hc.2.1]
  · simp [b18Clamp, b18Raw, b18RotZPerm, hc.2.2]

private lemma b18_yRef_eq (t : ℝ) (i : Fin 37) :
    (b18Clamp t).1 (b18YRefPerm i) = ![(b18Clamp t).1 i 0, -((b18Clamp t).1 i 1), (b18Clamp t).1 i 2] := by
  have hc := b18_yref_coords i
  ext c; fin_cases c
  · simp [b18Clamp, b18Raw, b18YRefPerm, hc.1]
  · simp [b18Clamp, b18Raw, b18YRefPerm, hc.2.1]
  · simp [b18Clamp, b18Raw, b18YRefPerm, hc.2.2]

private lemma b18_orig : ∀ r : Fin 18, b18Src r ≠ ⟨18, by omega⟩ ∧ b18RotZPerm (b18Src r) ≠ ⟨18, by omega⟩ := by
  decide

private lemma b18_disj : ∀ r s : Fin 18, b18RotZPerm (b18Src r) ≠ b18Src r →
    b18RotZPerm (b18Src r) ≠ b18Src s := by decide

private lemma b18_fixed_odd : ∀ r : Fin 18, b18RotZPerm (b18Src r) = b18Src r →
    (b18Src r).1 % 2 = 1 ∧ ∀ j : Fin 37, j ≠ b18Src r → (b18RotZPerm j < b18Src r ↔ j < b18Src r) := by
  decide

private lemma b18_paired_prop : ∀ r : Fin 18, b18RotZPerm (b18Src r) ≠ b18Src r →
    b18Src r < b18RotZPerm (b18Src r) ∧
    b18BaseZ (b18RotZPerm (b18Src r)) = b18BaseZ (b18Src r) ∧
    ∀ j : Fin 37, j ≠ b18Src r → j ≠ b18RotZPerm (b18Src r) →
      (b18RotZPerm j < b18RotZPerm (b18Src r) ↔ j < b18Src r) := by
  decide

private noncomputable def b18SubMat (t : ℝ) : Matrix (Fin 18) (Fin 18) ℂ :=
  Matrix.of fun r c : Fin 18 => atiyahMat (stereoSpinor (b18Clamp t).1) (b18Src r) ⟨2 * c.1 + 1, by omega⟩

private def b18SubYPermList : List ℕ := [0, 1, 2, 3, 5, 4, 6, 8, 7, 9, 11, 10, 12, 14, 13, 15, 16, 17]
private def b18SubYFn (r : Fin 18) : Fin 18 := ⟨b18SubYPermList.getD r.1 0, by
  have h : ∀ k : Fin 18, b18SubYPermList.getD k.1 0 < 18 := by decide
  exact h r⟩
private def b18SubYPerm : Equiv.Perm (Fin 18) where
  toFun := b18SubYFn
  invFun := b18SubYFn
  left_inv := by decide
  right_inv := by decide

private lemma b18SubYPerm_sign : Equiv.Perm.sign b18SubYPerm = 1 := by decide
private lemma b18_src_yref : ∀ r : Fin 18, b18YRefPerm (b18Src r) = b18Src (b18SubYPerm r) := by decide

private lemma b18SubMat_im_zero (t : ℝ) : (b18SubMat t).det.im = 0 := by
  let f : Fin 18 → ℂ := fun r => if b18SubYPerm r = r then 1 else -Complex.I
  have hprod' : (∏ r : Fin 18, f r) * (Equiv.Perm.sign b18SubYPerm : ℂ) = 1 := by
    rw [b18SubYPerm_sign]
    have hc : (Finset.univ.filter (fun r : Fin 18 => b18SubYPerm r ≠ r)).card = 8 := by decide
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun r : Fin 18 => b18SubYPerm r = r)]
    have p1 : (∏ r ∈ Finset.univ.filter (fun r : Fin 18 => b18SubYPerm r = r), f r) = 1 :=
      Finset.prod_eq_one fun r hr => by simp [f, (Finset.mem_filter.mp hr).2]
    have p2 : (∏ r ∈ Finset.univ.filter (fun r : Fin 18 => ¬ b18SubYPerm r = r), f r) = (-Complex.I) ^ 8 := by
      calc (∏ r ∈ Finset.univ.filter (fun r : Fin 18 => ¬ b18SubYPerm r = r), f r)
        = ∏ _r ∈ Finset.univ.filter (fun r : Fin 18 => b18SubYPerm r ≠ r), (-Complex.I) :=
          Finset.prod_congr (by ext x; simp) fun r hr => by simp [f, (Finset.mem_filter.mp hr).2]
        _ = (-Complex.I) ^ 8 := by rw [Finset.prod_const, hc]
    have h8 : (-Complex.I) ^ 8 = (1 : ℂ) := by
      calc (-Complex.I) ^ 8 = ((-Complex.I) ^ 2) ^ 4 := by ring
        _ = (-1 : ℂ) ^ 4 := by rw [neg_sq, Complex.I_sq]
        _ = 1 := by norm_num
    rw [p1, p2, one_mul, h8]; norm_num
  refine subDet_im_eq_zero_of_perm_conj (b18SubMat t) b18SubYPerm f hprod' ?_
  intro r c
  rw [b18SubMat, Matrix.of_apply, Matrix.of_apply, atiyahMat, atiyahMat, ← b18_src_yref r]
  have hs : (0 : ℝ) < max t 1 := lt_of_lt_of_le zero_lt_one (le_max_right t 1)
  by_cases hfix : b18SubYPerm r = r
  · have hfixN : b18YRefPerm (b18Src r) = b18Src r := by rw [b18_src_yref r, hfix]
    have hside : ∀ j : Fin 37, j ≠ b18Src r → (b18YRefPerm j < b18Src r ↔ j < b18Src r) := by
      revert r hfix; decide
    have hp := atiyahPoly_yRefl_fixed (b18Clamp t).1 b18YRefPerm b18YRefFn_invol (b18_yRef_eq t) (b18Src r) hfixN hside
    have hc := congr_arg (fun P : Polynomial ℂ => P.coeff (2 * c.1 + 1)) hp
    simp only [Polynomial.coeff_map] at hc
    simpa [f, hfix, hfixN] using hc
  · have hblk_cases : (r.1 = 4 ∧ (b18Src r).1 = 8 ∧ (b18Src (b18SubYPerm r)).1 = 10) ∨
        (r.1 = 5 ∧ (b18Src r).1 = 10 ∧ (b18Src (b18SubYPerm r)).1 = 8) ∨
        (r.1 = 7 ∧ (b18Src r).1 = 14 ∧ (b18Src (b18SubYPerm r)).1 = 16) ∨
        (r.1 = 8 ∧ (b18Src r).1 = 16 ∧ (b18Src (b18SubYPerm r)).1 = 14) ∨
        (r.1 = 10 ∧ (b18Src r).1 = 21 ∧ (b18Src (b18SubYPerm r)).1 = 23) ∨
        (r.1 = 11 ∧ (b18Src r).1 = 23 ∧ (b18Src (b18SubYPerm r)).1 = 21) ∨
        (r.1 = 13 ∧ (b18Src r).1 = 27 ∧ (b18Src (b18SubYPerm r)).1 = 29) ∨
        (r.1 = 14 ∧ (b18Src r).1 = 29 ∧ (b18Src (b18SubYPerm r)).1 = 27) := by
      revert r hfix; decide
    have hcheck_block : ∀ (a : Fin 37) (ha3 : a.1 + 3 < 37),
        b18YRefPerm a = ⟨a.1 + 2, by omega⟩ →
        b18YRefPerm ⟨a.1 + 1, by omega⟩ = ⟨a.1 + 3, by omega⟩ →
        (0 < b18BaseX a ∧ 0 < b18BaseY a ∧
          b18BaseX ⟨a.1 + 1, by omega⟩ = -b18BaseX a ∧ b18BaseY ⟨a.1 + 1, by omega⟩ = -b18BaseY a ∧ b18BaseZ ⟨a.1 + 1, by omega⟩ = b18BaseZ a ∧
          b18BaseX ⟨a.1 + 2, by omega⟩ = b18BaseX a ∧ b18BaseY ⟨a.1 + 2, by omega⟩ = -b18BaseY a ∧ b18BaseZ ⟨a.1 + 2, by omega⟩ = b18BaseZ a ∧
          b18BaseX ⟨a.1 + 3, by omega⟩ = -b18BaseX a ∧ b18BaseY ⟨a.1 + 3, by omega⟩ = b18BaseY a ∧ b18BaseZ ⟨a.1 + 3, by omega⟩ = b18BaseZ a) →
        (∀ j : Fin 37, j.1 ≠ a.1 → j.1 ≠ a.1 + 1 → j.1 ≠ a.1 + 2 → j.1 ≠ a.1 + 3 →
          (b18YRefPerm j < ⟨a.1 + 2, by omega⟩ ↔ j < a)) →
        (atiyahPoly (stereoSpinor (b18Clamp t).1) ⟨a.1 + 2, by omega⟩).map (starRingEnd ℂ) =
          Polynomial.C (-Complex.I) * atiyahPoly (stereoSpinor (b18Clamp t).1) a ∧
        (atiyahPoly (stereoSpinor (b18Clamp t).1) a).map (starRingEnd ℂ) =
          Polynomial.C (-Complex.I) * atiyahPoly (stereoSpinor (b18Clamp t).1) ⟨a.1 + 2, by omega⟩ := by
      intro a ha3 hσa hσa1 ⟨hxpos, hypos, h1x, h1y, h1z, h2x, h2y, h2z, h3x, h3y, h3z⟩ hside
      have hxR : ∃ xR yR zR : ℝ, 0 < xR ∧ 0 < yR ∧
          (b18Clamp t).1 a = ![xR, yR, zR] ∧
          (b18Clamp t).1 ⟨a.1 + 1, by omega⟩ = ![-xR, -yR, zR] ∧
          (b18Clamp t).1 ⟨a.1 + 2, by omega⟩ = ![xR, -yR, zR] ∧
          (b18Clamp t).1 ⟨a.1 + 3, by omega⟩ = ![-xR, yR, zR] := by
        refine ⟨max t 1 * (b18BaseX a : ℝ), max t 1 * (b18BaseY a : ℝ), (b18BaseZ a : ℝ),
          mul_pos hs (by exact_mod_cast hxpos), mul_pos hs (by exact_mod_cast hypos), ?_, ?_, ?_, ?_⟩
        · ext kk; fin_cases kk <;> rfl
        · ext kk; fin_cases kk
          · simp [b18Clamp, b18Raw, h1x]
          · simp [b18Clamp, b18Raw, h1y]
          · simp [b18Clamp, b18Raw, h1z]
        · ext kk; fin_cases kk
          · simp [b18Clamp, b18Raw, h2x]
          · simp [b18Clamp, b18Raw, h2y]
          · simp [b18Clamp, b18Raw, h2z]
        · ext kk; fin_cases kk
          · simp [b18Clamp, b18Raw, h3x]
          · simp [b18Clamp, b18Raw, h3y]
          · simp [b18Clamp, b18Raw, h3z]
      exact ⟨atiyahPoly_yRefl_block (b18Clamp t).1 b18YRefPerm b18YRefFn_invol (b18_yRef_eq t) a ha3 hσa hσa1 hxR hside,
        atiyahPoly_yRefl_block_rev (b18Clamp t).1 b18YRefPerm b18YRefFn_invol (b18_yRef_eq t) a ha3 hσa hσa1 hxR hside⟩
    have hpoly_swap : (atiyahPoly (stereoSpinor (b18Clamp t).1) (b18YRefPerm (b18Src r))).map (starRingEnd ℂ) =
        Polynomial.C (-Complex.I) * atiyahPoly (stereoSpinor (b18Clamp t).1) (b18Src r) := by
      rcases hblk_cases with ⟨_, hsr, hsyr⟩ | ⟨_, hsr, hsyr⟩ | ⟨_, hsr, hsyr⟩ | ⟨_, hsr, hsyr⟩ |
          ⟨_, hsr, hsyr⟩ | ⟨_, hsr, hsyr⟩ | ⟨_, hsr, hsyr⟩ | ⟨_, hsr, hsyr⟩
      · have hres := hcheck_block ⟨8, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
        have hs1 : b18Src r = ⟨8, by decide⟩ := Fin.ext hsr
        have hs2 : b18YRefPerm (b18Src r) = ⟨10, by decide⟩ := by rw [b18_src_yref]; exact Fin.ext hsyr
        rw [hs2, hs1]; exact hres.1
      · have hres := hcheck_block ⟨8, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
        have hs1 : b18Src r = ⟨10, by decide⟩ := Fin.ext hsr
        have hs2 : b18YRefPerm (b18Src r) = ⟨8, by decide⟩ := by rw [b18_src_yref]; exact Fin.ext hsyr
        rw [hs2, hs1]; exact hres.2
      · have hres := hcheck_block ⟨14, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
        have hs1 : b18Src r = ⟨14, by decide⟩ := Fin.ext hsr
        have hs2 : b18YRefPerm (b18Src r) = ⟨16, by decide⟩ := by rw [b18_src_yref]; exact Fin.ext hsyr
        rw [hs2, hs1]; exact hres.1
      · have hres := hcheck_block ⟨14, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
        have hs1 : b18Src r = ⟨16, by decide⟩ := Fin.ext hsr
        have hs2 : b18YRefPerm (b18Src r) = ⟨14, by decide⟩ := by rw [b18_src_yref]; exact Fin.ext hsyr
        rw [hs2, hs1]; exact hres.2
      · have hres := hcheck_block ⟨21, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
        have hs1 : b18Src r = ⟨21, by decide⟩ := Fin.ext hsr
        have hs2 : b18YRefPerm (b18Src r) = ⟨23, by decide⟩ := by rw [b18_src_yref]; exact Fin.ext hsyr
        rw [hs2, hs1]; exact hres.1
      · have hres := hcheck_block ⟨21, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
        have hs1 : b18Src r = ⟨23, by decide⟩ := Fin.ext hsr
        have hs2 : b18YRefPerm (b18Src r) = ⟨21, by decide⟩ := by rw [b18_src_yref]; exact Fin.ext hsyr
        rw [hs2, hs1]; exact hres.2
      · have hres := hcheck_block ⟨27, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
        have hs1 : b18Src r = ⟨27, by decide⟩ := Fin.ext hsr
        have hs2 : b18YRefPerm (b18Src r) = ⟨29, by decide⟩ := by rw [b18_src_yref]; exact Fin.ext hsyr
        rw [hs2, hs1]; exact hres.1
      · have hres := hcheck_block ⟨27, by decide⟩ (by decide) (by decide) (by decide) (by decide) (by decide)
        have hs1 : b18Src r = ⟨29, by decide⟩ := Fin.ext hsr
        have hs2 : b18YRefPerm (b18Src r) = ⟨27, by decide⟩ := by rw [b18_src_yref]; exact Fin.ext hsyr
        rw [hs2, hs1]; exact hres.2
    have hc := congr_arg (fun P : Polynomial ℂ => P.coeff (2 * c.1 + 1)) hpoly_swap
    simp only [Polynomial.coeff_map, Polynomial.coeff_C_mul] at hc
    simpa [f, hfix] using hc

private lemma continuous_b18SubMat_re : Continuous (fun t => (b18SubMat t).det.re) := by
  refine Complex.continuous_re.comp (Continuous.matrix_det (continuous_pi fun r => continuous_pi fun c => ?_))
  exact continuous_atiyahMat_entry b18Clamp continuous_b18Clamp_coord b18Clamp_z_mono (b18Src r) ⟨2 * c.1 + 1, by omega⟩

private lemma b18SubMat_det_zero_implies_det_zero_and_dep {t : ℝ} (hsub : (b18SubMat t).det = 0) :
    atiyahDet (b18Clamp t) = 0 ∧
    ¬ LinearIndependent ℂ (fun i : {j : Fin 37 // j ≠ ⟨18, by omega⟩} =>
      atiyahPoly (fun u v => canonicalSpinor (unitDir ((b18Clamp t).1 u) ((b18Clamp t).1 v))) i.1) := by
  let μ : Fin 18 → ℂ := fun r =>
    if b18RotZPerm (b18Src r) = b18Src r then 1
    else (-1 : ℂ) ^ (b18Src r).1 * (-star (stereoSlope (b18Clamp t).1 (b18Src r) (b18RotZPerm (b18Src r))))
  have hμ_ne : ∀ r : Fin 18, μ r ≠ 0 := by
    intro r
    by_cases hf : b18RotZPerm (b18Src r) = b18Src r
    · simp [μ, hf]
    · obtain ⟨hlt, hzB, _⟩ := b18_paired_prop r hf
      have hz_eq : (b18Clamp t).1 (b18RotZPerm (b18Src r)) 2 = (b18Clamp t).1 (b18Src r) 2 := by
        simp [b18Clamp, b18Raw, hzB]
      have hns := stereoSlope_normSq_eq_one_of_dz_zero (b18Clamp t).1
        ((b18Clamp t).2 _ _ hlt.ne) hz_eq
      have hstar_ne : -star (stereoSlope (b18Clamp t).1 (b18Src r) (b18RotZPerm (b18Src r))) ≠ 0 := by
        intro hz0
        have hst : star (stereoSlope (b18Clamp t).1 (b18Src r) (b18RotZPerm (b18Src r))) = 0 := neg_eq_zero.mp hz0
        rw [hst, mul_zero] at hns
        norm_num at hns
      simp only [μ, hf, ↓reduceIte]
      exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hstar_ne
  have hsub' : (Matrix.of fun r c : Fin 18 => (atiyahMat (stereoSpinor (b18Clamp t).1)) (b18Src r) ⟨2 * c.1 + 1, by omega⟩).det = 0 := by
    unfold b18SubMat at hsub; exact hsub
  obtain ⟨hMdet, w, hw_ne, hw_orig, hwM⟩ :=
    det_eq_zero_and_nonOrigin_vecMul_of_rotZ_oddSubblock_det_zero (m := 18) (atiyahMat (stereoSpinor (b18Clamp t).1))
      ⟨18, by omega⟩ b18Src b18Src_inj b18RotZPerm μ hμ_ne b18_orig b18_disj
      (by
        intro r hfix c
        obtain ⟨hodd, hside⟩ := b18_fixed_odd r hfix
        have hp := atiyahPoly_rotZ_fixed (b18Clamp t).1 b18RotZPerm b18RotZFn_invol (b18_rotZ_eq t) (b18Src r) hfix hside
        have hc := congr_arg (fun P : Polynomial ℂ => P.coeff (2 * c.1)) hp
        have hpow_i : (-1 : ℂ) ^ (b18Src r).1 = -1 := by
          rw [show (b18Src r).1 = 2 * ((b18Src r).1 / 2) + 1 by omega, pow_add, pow_mul]; norm_num
        have hpow_k : (-1 : ℂ) ^ (2 * c.1) = 1 := by
          rw [pow_mul]; norm_num
        rw [Polynomial.coeff_C_mul, coeff_comp_neg_X', hpow_i, hpow_k, one_mul] at hc
        have hcoef0 : (atiyahPoly (stereoSpinor (b18Clamp t).1) (b18Src r)).coeff (2 * c.1) = 0 := by
          linear_combination hc / 2
        exact hcoef0)
      (by
        intro r hnf k
        obtain ⟨hlt, hzB, hside⟩ := b18_paired_prop r hnf
        have hz_eq : (b18Clamp t).1 (b18RotZPerm (b18Src r)) 2 = (b18Clamp t).1 (b18Src r) 2 := by
          simp [b18Clamp, b18Raw, hzB]
        have hp := atiyahPoly_rotZ_pair (b18Clamp t).1 (b18Clamp t).2 b18RotZPerm b18RotZFn_invol (b18_rotZ_eq t)
          (b18Src r) hlt hz_eq hside
        have hc := congr_arg (fun P : Polynomial ℂ => P.coeff k.1) hp
        rw [Polynomial.coeff_C_mul, coeff_comp_neg_X'] at hc
        simp only [atiyahMat, μ, hnf, ↓reduceIte, mul_assoc] at hc ⊢
        exact hc)
      hsub'
  refine ⟨?_, not_linearIndependent_nonOrigin_canonical_of_stereo_vecMul_zero (b18Clamp t) (b18Clamp_z_mono t) ⟨18, by omega⟩ w hw_ne hw_orig hwM⟩
  rw [atiyahDet_eq_stereoMat_div (b18Clamp t) (b18Clamp_z_mono t), hMdet, zero_div]

section SignB18
attribute [local irreducible] Matrix.det

private lemma b18Clamp_8_eq_neg : (b18SubMat 8).det.re < 0 := by
  have hp0 : ∀ i : Fin 37, (b18Clamp 8).1 i 0 = ((8 : ℤ) : ℝ) * (b18BaseXList.getD i.1 0 : ℝ) := fun i => by
    simp [b18Clamp, b18Raw, b18BaseX]
  have hp1 : ∀ i : Fin 37, (b18Clamp 8).1 i 1 = ((8 : ℤ) : ℝ) * (b18BaseYList.getD i.1 0 : ℝ) := fun i => by
    simp [b18Clamp, b18Raw, b18BaseY]
  have hp2 : ∀ i : Fin 37, (b18Clamp 8).1 i 2 = (b18BaseZList.getD i.1 0 : ℝ) := fun i => by
    simp [b18Clamp, b18Raw, b18BaseZ]
  have hw := slopeTableOk_mem S_symp_pos hp0 hp1 hp2 ok_b18_8
  have hmat := matCMem_extractSubOdd S_symp_pos (by decide) (by decide) hw b18Src_len b18Src_getD
  have hmat' : MatCMem S_symp 18 (extractSubOdd 18 (b18SrcList.map (polyListCIv S_symp (wRead2D w_b18_8)))) (b18SubMat 8) := by
    unfold b18SubMat; exact hmat
  have hg := gaussDetCIv_mem S_symp_pos gauss_b18_8_eq (CFpIv.ofInt_mem S_symp 1) hmat'
  rw [Int.cast_one, one_mul] at hg
  exact neg_re_of_CFpMem_symp S_symp_pos hg sign_b18_8

private lemma b18Clamp_9_eq_pos : 0 < (b18SubMat 9).det.re := by
  have hp0 : ∀ i : Fin 37, (b18Clamp 9).1 i 0 = ((9 : ℤ) : ℝ) * (b18BaseXList.getD i.1 0 : ℝ) := fun i => by
    simp [b18Clamp, b18Raw, b18BaseX]
  have hp1 : ∀ i : Fin 37, (b18Clamp 9).1 i 1 = ((9 : ℤ) : ℝ) * (b18BaseYList.getD i.1 0 : ℝ) := fun i => by
    simp [b18Clamp, b18Raw, b18BaseY]
  have hp2 : ∀ i : Fin 37, (b18Clamp 9).1 i 2 = (b18BaseZList.getD i.1 0 : ℝ) := fun i => by
    simp [b18Clamp, b18Raw, b18BaseZ]
  have hw := slopeTableOk_mem S_symp_pos hp0 hp1 hp2 ok_b18_9
  have hmat := matCMem_extractSubOdd S_symp_pos (by decide) (by decide) hw b18Src_len b18Src_getD
  have hmat' : MatCMem S_symp 18 (extractSubOdd 18 (b18SrcList.map (polyListCIv S_symp (wRead2D w_b18_9)))) (b18SubMat 9) := by
    unfold b18SubMat; exact hmat
  have hg := gaussDetCIv_mem S_symp_pos gauss_b18_9_eq (CFpIv.ofInt_mem S_symp 1) hmat'
  rw [Int.cast_one, one_mul] at hg
  exact pos_re_of_CFpMem_symp S_symp_pos hg sign_b18_9

end SignB18

section IrredB18
attribute [local irreducible] atiyahDet b18SubMat b18Clamp

private def b18OrthogonalBConfig (t : ℝ) : OrthogonalBConfig 18 where
  p := (b18Clamp t).1
  distinct := (b18Clamp t).2
  originIdx := ⟨18, by omega⟩
  origin_eq := by
    intro k
    have hx : b18BaseX 18 = 0 := by decide
    have hy : b18BaseY 18 = 0 := by decide
    have hz : b18BaseZ 18 = 0 := by decide
    fin_cases k
    · simp [b18Clamp, b18Raw, hx]
    · simp [b18Clamp, b18Raw, hy]
    · simp [b18Clamp, b18Raw, hz]
  antipodal := b18AntiPerm
  involutive := b18AntiFn_invol
  fix_origin := by decide
  neg_eq := by
    intro i k
    have hc := b18_anti_coords i
    fin_cases k
    · simp [b18Clamp, b18Raw, b18AntiPerm, hc.1]
    · simp [b18Clamp, b18Raw, b18AntiPerm, hc.2.1]
    · simp [b18Clamp, b18Raw, b18AntiPerm, hc.2.2]

/-- **Strictly Non-Coplanar 3D Orthogonal $B_{18}$ (`SO(37)`, `n = 37`) C1/C2 Witness:**
There exists a strictly non-coplanar origin-augmented centrally symmetric $37$-point configuration
with $D_{37} = 0$ whose $36$ non-origin Atiyah polynomials are already linearly dependent. -/
theorem exists_noncoplanar_orthogonalB_18_atiyahDet_zero_and_nonOrigin_dep :
    ∃ c : OrthogonalBConfig 18, Noncoplanar3D c.p ∧
      atiyahDet (orthogonalBPoints c) = 0 ∧
      ¬ LinearIndependent ℂ (fun i : {j : Fin 37 // j ≠ c.originIdx} =>
        atiyahPoly (fun u v => canonicalSpinor (unitDir (c.p u) (c.p v))) i.1) := by
  let f : ℝ → ℝ := fun t => (b18SubMat t).det.re
  have hmem : (0 : ℝ) ∈ Set.Icc (f 8) (f 9) := ⟨b18Clamp_8_eq_neg.le, b18Clamp_9_eq_pos.le⟩
  obtain ⟨t₀, _, hft₀⟩ := intermediate_value_Icc (by norm_num : (8 : ℝ) ≤ 9)
    continuous_b18SubMat_re.continuousOn hmem
  have hsub0 : (b18SubMat t₀).det = 0 := Complex.ext hft₀ (b18SubMat_im_zero t₀)
  obtain ⟨hdet0, hdep⟩ := b18SubMat_det_zero_implies_det_zero_and_dep hsub0
  exact ⟨b18OrthogonalBConfig t₀, b18Clamp_noncoplanar t₀, hdet0, hdep⟩

/-- **Disproof of Orthogonal $B_{18}$ Determinant Nonzero Conjecture** (`SO(37)`, `n = 37`). -/
theorem disproof_orthogonalB_18_det_nonzero : ¬ OrthogonalBAtiyahDetNonzeroProp 18 := by
  intro h
  obtain ⟨c, _, hc0, _⟩ := exists_noncoplanar_orthogonalB_18_atiyahDet_zero_and_nonOrigin_dep
  exact h c hc0

/-- **Disproof of Orthogonal $B_{18}$ Atiyah Conjecture 1** (`SO(37)`, `n = 37`). -/
theorem disproof_orthogonalB_18_conjecture_1 : ¬ OrthogonalBAtiyahConjecture1Prop 18 := by
  intro h
  obtain ⟨c, _, hc0, _⟩ := exists_noncoplanar_orthogonalB_18_atiyahDet_zero_and_nonOrigin_dep
  exact not_linearIndependent_of_atiyahDet_zero (by omega) (orthogonalBPoints c) hc0 (h c)

/-- **Disproof of Orthogonal $B_{18}$ Atiyah–Sutcliffe Conjecture 2** (`SO(37)`, `n = 37`). -/
theorem disproof_orthogonalB_18_conjecture_2 : ¬ OrthogonalBAtiyahSutcliffeConjecture2Prop 18 := by
  intro h
  obtain ⟨c, _, hc0, _⟩ := exists_noncoplanar_orthogonalB_18_atiyahDet_zero_and_nonOrigin_dep
  have hle := h c
  rw [hc0, norm_zero] at hle
  linarith

end IrredB18

end NoncoplanarB18

end Matematyka.AtiyahSutcliffeSymplectic
""")
    return "".join(out)


def main() -> None:
    data = json.loads((ROOT / "data" / "atiyah_part2_witnesses.json").read_text(encoding="utf-8"))
    sp20_pts = data["planar_sp20_40_family"]["points_t1"]
    sp18_pts = data["sp18_36_3d_family"]["base_t1"]
    b18_pts = data["b18_37_3d_family"]["base_t1"]

    text = finish_build_lean(sp20_pts, sp18_pts, b18_pts)
    out_path = ROOT / "lean" / "Matematyka" / "AtiyahSutcliffeSymplectic.lean"
    out_path.write_text(text, encoding="utf-8")
    print(f"Generated {out_path} ({out_path.stat().st_size} bytes)")


if __name__ == "__main__":
    main()
