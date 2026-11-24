"""Generate lean/Matematyka/AtiyahSutcliffePlanar35.lean (n=35 planar, n=37 mirror, n=26 H^3)."""
from __future__ import annotations

import json
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
S35 = 10**34


def add_fp(a: tuple[int, int], b: tuple[int, int]) -> tuple[int, int]:
    return (a[0] + b[0], a[1] + b[1])


def neg_fp(a: tuple[int, int]) -> tuple[int, int]:
    return (-a[1], -a[0])


def mul_fp(a: tuple[int, int], b: tuple[int, int], S: int = S35) -> tuple[int, int]:
    p = [a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1]]
    return (min(p) // S, (max(p) + S - 1) // S)


def div_fp(a: tuple[int, int], b: tuple[int, int], S: int = S35) -> tuple[int, int]:
    assert b[0] > 0 or b[1] < 0, f"Zero in denom {b}"
    if b[0] > 0:
        n1, n2, d1, d2 = S * a[0], S * a[1], b[0], b[1]
    else:
        na = neg_fp(a)
        nb = neg_fp(b)
        n1, n2, d1, d2 = S * na[0], S * na[1], nb[0], nb[1]
    los = [n1 // d1, n1 // d2, n2 // d1, n2 // d2]
    his = [
        (n1 + d1 - 1) // d1,
        (n1 + d2 - 1) // d2,
        (n2 + d1 - 1) // d1,
        (n2 + d2 - 1) // d2,
    ]
    return (min(los), max(his))


def slope_iv(dx: int, dz: int, S: int = S35) -> tuple[int, int, int]:
    rho = math.isqrt(S * S * (dx * dx + dz * dz))
    assert rho * rho <= S * S * (dx * dx + dz * dz) <= (rho + 1) * (rho + 1)
    den_lo = S * dz + rho
    den_hi = S * dz + rho + 1
    if dx >= 0:
        return rho, (S * S * dx) // den_hi, (S * S * dx + den_lo - 1) // den_lo
    return rho, -((S * S * (-dx) + den_lo - 1) // den_lo), -((S * S * (-dx)) // den_hi)


def is_zero_iv(iv: tuple[int, int]) -> bool:
    return iv[0] == 0 and iv[1] == 0


def fmt_iv(iv: tuple[int, int]) -> str:
    return f"⟨{iv[0]}, {iv[1]}⟩"


def fmt_mat(rows: list[list[tuple[int, int]]], indent: str = "  ") -> str:
    lines = ["["]
    for idx, row in enumerate(rows):
        sep = "," if idx + 1 < len(rows) else ""
        lines.append(f"{indent}[{', '.join(fmt_iv(x) for x in row)}]{sep}")
    lines.append("]")
    return "\n".join(lines)


def main() -> None:
    data = json.loads((ROOT / "data" / "atiyah_part2_witnesses.json").read_text(encoding="utf-8"))
    pts = data["planar_35_c2"]["points"]
    assert len(pts) == 35
    xs = [int(p[0]) for p in pts]
    zs = [int(p[2]) for p in pts]
    assert all(zs[i] < zs[i + 1] for i in range(34))

    rho_table = [[0] * 35 for _ in range(35)]
    c_table: list[list[tuple[int, int]]] = [[(0, 0)] * 35 for _ in range(35)]
    for i in range(35):
        for j in range(i + 1, 35):
            dx = xs[j] - xs[i]
            if dx != 0:
                rho, lo, hi = slope_iv(dx, zs[j] - zs[i], S35)
                rho_table[i][j] = rho
                c_table[i][j] = (lo, hi)

    zero = (0, 0)
    one = (S35, S35)
    chunks = [list(range(k, min(k + 3, 35))) for k in range(0, 35, 3)]

    def step_poly_row(i: int, row: list[tuple[int, int]], j: int) -> list[tuple[int, int]]:
        if j == i:
            return row
        if j < i:
            iv = c_table[j][i]
            if is_zero_iv(iv):
                return [zero] + row
            f0 = neg_fp(iv)
            scaled = [mul_fp(f0, x) for x in row]
            right = [zero] + row
            return [add_fp(scaled[k] if k < len(scaled) else zero, right[k]) for k in range(max(len(scaled), len(right)))]
        iv = c_table[i][j]
        if is_zero_iv(iv):
            return row + [zero]
        right = [zero] + [mul_fp(iv, x) for x in row]
        return [add_fp(row[k] if k < len(row) else zero, right[k]) for k in range(max(len(row), len(right)))]

    poly_stages: list[list[list[tuple[int, int]]]] = []
    cur_rows = [[one] for _ in range(35)]
    for ch in chunks:
        nxt_rows = []
        for i in range(35):
            r = cur_rows[i][:]
            for j in ch:
                r = step_poly_row(i, r, j)
            nxt_rows.append(r)
        cur_rows = nxt_rows
        poly_stages.append(cur_rows)

    gauss_stages: list[tuple[list[tuple[int, int]], list[list[tuple[int, int]]], tuple[int, int]]] = []
    cur_g = [r[:] for r in poly_stages[-1]]
    cur_prod = one
    for step in range(35):
        piv = cur_g[0][0]
        assert piv[0] > 0 or piv[1] < 0, f"Zero pivot at step {step}: {piv}"
        cur_prod = mul_fp(cur_prod, piv)
        ptail = cur_g[0][1:]
        mults: list[tuple[int, int]] = []
        nxt_g = []
        for row in cur_g[1:]:
            rhead, rtail = row[0], row[1:]
            if is_zero_iv(rhead):
                mults.append(zero)
                nxt_g.append(rtail)
            else:
                mult = div_fp(neg_fp(rhead), piv)
                mults.append(mult)
                nxt_g.append([
                    rtail[k] if is_zero_iv(ptail[k]) else add_fp(rtail[k], mul_fp(mult, ptail[k]))
                    for k in range(len(rtail))
                ])
        cur_g = nxt_g
        gauss_stages.append((mults, cur_g, cur_prod))

    # Build denFoldIv trace matching activePairs 35 pts35X
    den = one
    den_trace: list[tuple[int, int]] = []
    for i in range(35):
        for j in range(i + 1, 35):
            if xs[j] != xs[i]:
                iv = c_table[i][j]
                den = mul_fp(den, add_fp(one, mul_fp(iv, iv)))
                den_trace.append(den)

    det_cert = gauss_stages[-1][2]
    assert det_cert[1] < 0 and -den[0] < det_cert[0], f"C2 bounds failed: det={det_cert}, den={den}"
    print(f"n=35 cert OK: det={det_cert}, den={den}")

    def fmt_int_2d(name: str, rows: list[list[int]]) -> str:
        body = ",\n  ".join("[" + ", ".join(str(v) for v in row) + "]" for row in rows)
        return f"def {name} : List (List ℤ) := [\n  {body}]\n"

    def fmt_iv_list(name: str, vals: list[tuple[int, int]], cols: int = 4) -> str:
        rows = [", ".join(fmt_iv(v) for v in vals[k : k + cols]) for k in range(0, len(vals), cols)]
        return f"def {name} : List FpIv := [\n  " + ",\n  ".join(rows) + "]\n"

    def fmt_iv_2d(name: str, rows: list[list[tuple[int, int]]]) -> str:
        return f"def {name} : List (List FpIv) := " + fmt_mat(rows) + "\n"

    parts: list[str] = []
    parts.append("""import Matematyka.AtiyahSutcliffeExtensions
import Matematyka.AtiyahSutcliffe3D26

/-!
# Part II — Planar `n = 35` Record (`D_35 < 0`, `-1 < D_35 < 0`), 3D `n = 37`, and Hyperbolic `H^2(35)`, `H^3(26, 37)`

Extends the Part I (`v1.1.0`) formalization cleanly in a separate module without modifying any Part I file:
1. **Planar `n = 35` C1 & direct C2 disproof** (`-1 < D_35 < 0` and IVT zero `D_35 = 0`), lowering the planar
   Euclidean and hyperbolic threshold from `n = 57` down to `n = 35`.
2. **Mirror-pair `n = 37` non-coplanar C1 & direct C2 disproof** in both `R^3` and `H^3`, lowering the
   certified `-1 < D_n < 0` 3D witness from `n = 59` down to `n = 37`.
3. **Hyperbolic `H^3` transfer at `n = 26`** via general permutation invariance `atiyahDetOfSpinors_perm` and
   `reflectPerm26`, lowering the certified strictly non-coplanar `H^3` C1/C2 disproof from `n = 59` to `n = 26`.
-/

namespace Matematyka.AtiyahSutcliffePlanar35

open Complex Real Matrix Polynomial Filter Topology
open Matematyka.MalkounCounterexample Matematyka.AtiyahSutcliffe Matematyka.AtiyahSutcliffe3D26
open scoped BigOperators

/-! ## Part 1: Planar `n = 35` Witness Data & Staged Kernel Intervals -/

section Planar35Cert

def S35 : ℤ := 10000000000000000000000000000000000

lemma S35_pos : 0 < S35 := by decide

""")

    parts.append(f"def pts35XList : List ℤ := [\n  " + ",\n  ".join(", ".join(str(x) for x in xs[k : k + 7]) for k in range(0, 35, 7)) + "]\n\n")
    parts.append(f"def pts35ZList : List ℤ := [\n  " + ",\n  ".join(", ".join(str(z) for z in zs[k : k + 7]) for k in range(0, 35, 7)) + "]\n\n")
    parts.append("""def pts35X (i : Fin 35) : ℤ := pts35XList.getD i.1 0
def pts35Z (i : Fin 35) : ℤ := pts35ZList.getD i.1 0

lemma pts35Z_strictMono : StrictMono pts35Z := by decide

/-- Straight-line planar homotopy at `n = 35`, starting at collinear `s = 0` (`D_35 = 1`)
and ending at the explicit integer C2 counterexample `s = 1` (`-1 < D_35 < 0`). -/
noncomputable def x35Path (s : ℝ) : DistinctPoints 35 :=
  planarPath pts35X pts35Z pts35Z_strictMono s

""")
    parts.append(fmt_int_2d("rho35Table", rho_table) + "\n")
    parts.append(fmt_iv_2d("c35Table", c_table) + "\n")

    parts.append("""def c35Lit (i j : Fin 35) : FpIv :=
  (c35Table.getD i.1 []).getD j.1 FpIv.zero

private def fpIvEq (a b : FpIv) : Bool := (a.lo == b.lo) && (a.hi == b.hi)

private def c35TableOk (tbl : List (List ℤ)) (cTbl : List (List FpIv)) : Bool :=
  (List.finRange 35).all fun i =>
    let rhoRow := tbl.getD i.1 []
    let cRow := cTbl.getD i.1 []
    (List.finRange 35).all fun j =>
      if i < j then
        let dx := pts35X j - pts35X i
        let entry := cRow.getD j.1 FpIv.zero
        if dx == 0 then fpIvEq entry FpIv.zero
        else
          let rho := rhoRow.getD j.1 0
          rhoCheck S35 dx (pts35Z j - pts35Z i) rho &&
            fpIvEq entry (FpIv.slopeIv S35 dx (pts35Z j - pts35Z i) rho)
      else true

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private lemma c35Table_ok : c35TableOk rho35Table c35Table = true := by
  decide +kernel

private lemma eq_of_fpIvEq {a b : FpIv} (h : fpIvEq a b = true) : a = b := by
  cases a; cases b
  simp only [fpIvEq, Bool.and_eq_true, beq_iff_eq] at h
  simp [h.1, h.2]

private lemma c35Lit_mem :
    ∀ i j : Fin 35, i < j → FpIv.FpMem S35 (c35Lit i j) (planarSlope (x35Path 1).1 i j) := by
  intro i j hij
  have hall_i : ((List.finRange 35).all fun ii =>
      let rhoRow := rho35Table.getD ii.1 []
      let cRow := c35Table.getD ii.1 []
      (List.finRange 35).all fun jj =>
        if ii < jj then
          let dx := pts35X jj - pts35X ii
          let entry := cRow.getD jj.1 FpIv.zero
          if dx == 0 then fpIvEq entry FpIv.zero
          else
            let rho := rhoRow.getD jj.1 0
            rhoCheck S35 dx (pts35Z jj - pts35Z ii) rho &&
              fpIvEq entry (FpIv.slopeIv S35 dx (pts35Z jj - pts35Z ii) rho)
        else true) = true := c35Table_ok
  have hi := List.all_eq_true.mp hall_i i (List.mem_finRange i)
  have hj := List.all_eq_true.mp hi j (List.mem_finRange j)
  dsimp only at hj
  simp only [hij, ↓reduceIte] at hj
  by_cases hdx : pts35X j - pts35X i = 0
  · have hdxB : (pts35X j - pts35X i == 0) = true := beq_iff_eq.mpr hdx
    simp only [hdxB, ↓reduceIte] at hj
    have heq : c35Lit i j = FpIv.zero := eq_of_fpIvEq hj
    have hsl : planarSlope (x35Path 1).1 i j = 0 := by
      rw [x35Path, planarSlope_planarPath_one, hdx, Int.cast_zero, zero_div]
    rw [heq, hsl]
    exact FpIv.zero_mem S35
  · have hdxB : (pts35X j - pts35X i == 0) = false := beq_false_of_ne hdx
    simp only [hdxB, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hj
    have hmem := slopeIv_planarPath_one_mem S35_pos pts35X pts35Z pts35Z_strictMono hij hj.1
    have heq : c35Lit i j = FpIv.slopeIv S35 (pts35X j - pts35X i) (pts35Z j - pts35Z i)
        ((rho35Table.getD i.1 []).getD j.1 0) := eq_of_fpIvEq hj.2
    rw [← heq] at hmem
    exact hmem

private def stageP35 (chunk : List (Fin 35)) (prev : List (List FpIv)) : List (List FpIv) :=
  (List.finRange 35).map fun i =>
    chunk.foldl (stepPolyFastIv S35 c35Lit i) (prev.getD i.1 [])

private def init35 : List (List FpIv) := List.replicate 35 [FpIv.ofInt S35 1]

""")
    for idx, ch in enumerate(chunks):
        parts.append(f"private def p35Chunk{idx} : List (Fin 35) := [{', '.join(str(x) for x in ch)}]\n")
    parts.append("""
private lemma finRange35_chunks :
    List.finRange 35 = """ + " ++ ".join(f"p35Chunk{idx}" for idx in range(len(chunks))) + """ := by
  decide

private lemma init35_getD : ∀ i : Fin 35, init35.getD i.1 [] = [FpIv.ofInt S35 1] := by
  decide

private lemma getD_map_finRange35 {α : Type*} (f : Fin 35 → α) (d : α) (c : Fin 35) :
    ((List.finRange 35).map f).getD c.1 d = f c := by
  simp [List.getD_eq_getElem?_getD, List.getElem_finRange]

private lemma polyRows35_eq_stages :
    (List.finRange 35).map (polyRowFastIv S35 c35Lit) =
      """ + "".join(f"stageP35 p35Chunk{idx} (" for idx in reversed(range(len(chunks)))) + "init35" + ")" * len(chunks) + """ := by
  conv_rhs => unfold stageP35
  refine List.map_congr_left fun i _ => ?_
  simp only [getD_map_finRange35, init35_getD]
  unfold polyRowFastIv
  rw [finRange35_chunks]
  simp only [List.foldl_append]

private def checkTraceLastFp {α : Type*} (step : FpIv → α → FpIv)
    (acc last : FpIv) : List α → List FpIv → Bool
  | [], [] => fpIvEq acc last
  | x :: xs, nxt :: rest =>
    fpIvEq (step acc x) nxt && checkTraceLastFp step nxt last xs rest
  | _, _ => false

private lemma foldl_eq_of_checkTraceLastFp {α : Type*} (step : FpIv → α → FpIv) :
    ∀ (acc last : FpIv) (xs : List α) (tr : List FpIv),
      checkTraceLastFp step acc last xs tr = true → xs.foldl step acc = last
  | acc, last, [], [], h => eq_of_fpIvEq h
  | acc, last, x :: xs, nxt :: rest, h => by
    simp only [checkTraceLastFp, Bool.and_eq_true] at h
    rw [List.foldl_cons, eq_of_fpIvEq h.1]
    exact foldl_eq_of_checkTraceLastFp step nxt last xs rest h.2

private def elimRowsIvWithMults (S : ℤ) (piv : FpIv) (ptail : List FpIv) :
    List FpIv → List (List FpIv) → Bool × List (List FpIv)
  | _, [] => (true, [])
  | m :: ms, row :: rows =>
    let rhead := row.headD FpIv.zero
    let rtail := row.tail
    let res := elimRowsIvWithMults S piv ptail ms rows
    if isZeroIv rhead then
      (res.1, rtail :: res.2)
    else
      (fpIvEq (FpIv.divFp S (FpIv.neg rhead) piv) m && res.1, zipElimIv S m rtail ptail :: res.2)
  | [], _ :: _ => (false, [])

private lemma elimRowsIv_eq_of_withMults (S : ℤ) (piv : FpIv) (ptail : List FpIv) :
    ∀ (ms : List FpIv) (rows out : List (List FpIv)),
      elimRowsIvWithMults S piv ptail ms rows = (true, out) → elimRowsIv S piv ptail rows = out
  | _, [], out, h => by
    simp only [elimRowsIvWithMults, Prod.mk.injEq] at h
    rcases h with ⟨_, rfl⟩
    rfl
  | [], _ :: _, _, h => by
    simp [elimRowsIvWithMults] at h
  | m :: ms, row :: rows, out, h => by
    dsimp only [elimRowsIvWithMults] at h
    by_cases hz : isZeroIv (row.headD FpIv.zero) = true
    · simp only [hz, ↓reduceIte, Prod.mk.injEq] at h
      obtain ⟨h1, rfl⟩ := h
      have hres : elimRowsIvWithMults S piv ptail ms rows =
          ((elimRowsIvWithMults S piv ptail ms rows).1, (elimRowsIvWithMults S piv ptail ms rows).2) := rfl
      rw [h1] at hres
      have ih := elimRowsIv_eq_of_withMults S piv ptail ms rows _ hres
      rw [elimRowsIv]
      dsimp only
      simp only [hz, ↓reduceIte, ih]
    · simp only [hz, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq, Bool.and_eq_true] at h
      obtain ⟨⟨hm, h1⟩, rfl⟩ := h
      have hres : elimRowsIvWithMults S piv ptail ms rows =
          ((elimRowsIvWithMults S piv ptail ms rows).1, (elimRowsIvWithMults S piv ptail ms rows).2) := rfl
      rw [h1] at hres
      have ih := elimRowsIv_eq_of_withMults S piv ptail ms rows _ hres
      have hmeq : FpIv.divFp S (FpIv.neg (row.headD FpIv.zero)) piv = m := eq_of_fpIvEq hm
      rw [elimRowsIv]
      dsimp only
      simp only [hz, Bool.false_eq_true, ↓reduceIte, hmeq, ih]

private def gaussHeadIvWithMults (S : ℤ) (rows : List (List FpIv)) (prod : FpIv) (ms : List FpIv) :
    Bool × List (List FpIv) × FpIv :=
  match rows with
  | pRow :: rest =>
    let piv := pRow.headD FpIv.zero
    let er := elimRowsIvWithMults S piv pRow.tail ms rest
    (isSepZeroIv piv && er.1, er.2, FpIv.mulFp S prod piv)
  | [] => (false, [], prod)

private lemma gaussDetIv_step_withMults {S : ℤ} {m : ℕ} {rows rows' : List (List FpIv)}
    {prod prod' : FpIv} {ms : List FpIv}
    (h : gaussHeadIvWithMults S rows prod ms = (true, rows', prod')) :
    gaussDetIv S (m + 1) rows prod = gaussDetIv S m rows' prod' := by
  cases rows with
  | nil => simp [gaussHeadIvWithMults] at h
  | cons pRow rest =>
    dsimp only [gaussHeadIvWithMults] at h
    rcases her : elimRowsIvWithMults S (pRow.headD FpIv.zero) pRow.tail ms rest with ⟨okE, rowsE⟩
    rw [her] at h
    simp only [Prod.mk.injEq, Bool.and_eq_true] at h
    obtain ⟨⟨hsep, rfl⟩, rfl, hprod'⟩ := h
    have helim := elimRowsIv_eq_of_withMults S (pRow.headD FpIv.zero) pRow.tail ms rest rowsE her
    rw [gaussDetIv]
    simp only [hsep, ↓reduceIte, helim, hprod']

section StageTables35
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

""")

    for idx, st in enumerate(poly_stages):
        parts.append(f"private def P35_{idx} : List (List FpIv) := " + fmt_mat(st) + "\n\n")

    for step, (mults_st, rows_st, prod_st) in enumerate(gauss_stages):
        parts.append(fmt_iv_list(f"M35_{step}", mults_st, cols=6) + "\n")
        parts.append(f"private def G35_{step} : List (List FpIv) := " + fmt_mat(rows_st) + "\n\n")
        parts.append(f"private def Q35_{step} : FpIv := {fmt_iv(prod_st)}\n\n")

    for idx in range(len(chunks)):
        lhs = "stageP35 p35Chunk0 init35" if idx == 0 else f"stageP35 p35Chunk{idx} P35_{idx-1}"
        parts.append(f"private lemma stP35_{idx} : {lhs} = P35_{idx} := by decide +kernel\n")
    parts.append(f"\nprivate lemma polyRows35_eq : (List.finRange 35).map (polyRowFastIv S35 c35Lit) = P35_{len(chunks)-1} := by\n")
    parts.append("  rw [polyRows35_eq_stages, " + ", ".join(f"stP35_{idx}" for idx in range(len(chunks))) + "]\n\n")

    for step in range(35):
        lhs_r = f"P35_{len(chunks)-1}" if step == 0 else f"G35_{step-1}"
        lhs_p = "(FpIv.ofInt S35 1)" if step == 0 else f"Q35_{step-1}"
        parts.append(
            f"private lemma stG35_{step} : gaussHeadIvWithMults S35 {lhs_r} {lhs_p} M35_{step} = (true, G35_{step}, Q35_{step}) := by decide +kernel\n"
        )

    parts.append(
        "\nprivate lemma gauss35_eq : gaussDetIv S35 35 ((List.finRange 35).map (polyRowFastIv S35 c35Lit)) (FpIv.ofInt S35 1) = (true, Q35_34) := by\n"
        "  rw [polyRows35_eq]\n"
        + "\n".join(f"  rw [gaussDetIv_step_withMults (m := {34 - step}) stG35_{step}]" for step in range(35))
        + "\n  rfl\n\n"
    )
    parts.append(f"private def den35_cert : FpIv := {fmt_iv(den)}\n\n")
    parts.append(fmt_iv_list("den35_trace", den_trace, cols=6) + "\n")
    parts.append("""private def denStep35 (acc : FpIv) (q : Fin 35 × Fin 35) : FpIv :=
  FpIv.mulFp S35 acc ((FpIv.ofInt S35 1).add (FpIv.mulFp S35 (c35Lit q.1 q.2) (c35Lit q.1 q.2)))

private lemma den35_trace_ok :
    checkTraceLastFp denStep35 (FpIv.ofInt S35 1) den35_cert (activePairs 35 pts35X) den35_trace = true := by
  decide +kernel

private lemma den35_eq : denFoldIv S35 c35Lit (activePairs 35 pts35X) = den35_cert := by
  change (activePairs 35 pts35X).foldl denStep35 (FpIv.ofInt S35 1) = den35_cert
  exact foldl_eq_of_checkTraceLastFp denStep35 _ _ _ _ den35_trace_ok

private lemma cert35_bounds : Q35_34.hi < 0 ∧ -den35_cert.lo < Q35_34.lo := by decide

end StageTables35

""")

    # Add Part 1 theorems (planar n=35, mirror n=37, H^2 n=35, H^3 n=37) and Part 2 (H^3 n=26)
    parts.append("""lemma x35Path_hy (s : ℝ) (i : Fin 35) : (x35Path s).1 i 1 = 0 := rfl

lemma x35Path_hz (s : ℝ) : StrictMono (fun i => (x35Path s).1 i 2) :=
  fun _ _ h => Int.cast_lt.mpr (pts35Z_strictMono h)

lemma x35Path_isCoplanar (s : ℝ) : IsCoplanar (x35Path s) :=
  ⟨![0, 1, 0], 0, Or.inr (Or.inl one_ne_zero), fun i => by simp [x35Path_hy]⟩

private lemma x35Path_zero_det : atiyahDet (x35Path 0) = 1 := by
  simp [x35Path, planarPath_zero_eq_one]

private lemma x35Path_cont_re : Continuous (fun s => (atiyahDet (x35Path s)).re) :=
  continuous_planarPath_re pts35X pts35Z pts35Z_strictMono

private lemma x35Path_det_eq (s : ℝ) :
    atiyahDet (x35Path s) = (((planarMat (x35Path s).1).det / planarDen (x35Path s).1 : ℝ) : ℂ) :=
  atiyahDet_eq_planarMat_div (x35Path s) (x35Path_hy s) (x35Path_hz s)

section Shield35
attribute [local irreducible] Matrix.det planarMat planarDen atiyahDet S35
  pts35X pts35Z x35Path c35Lit Q35_34 den35_cert

/-- Direct integer endpoint certification at `n = 35` (`-1 < D_35 < 0`). -/
theorem x35Path_one_re_neg_and_norm_lt_one :
    (atiyahDet (x35Path 1)).im = 0 ∧ (atiyahDet (x35Path 1)).re < 0 ∧
      ‖atiyahDet (x35Path 1)‖ < 1 := by
  have hy := x35Path_hy 1
  have hz := x35Path_hz 1
  have hmat : MatFpMem S35 35 ((List.finRange 35).map (polyRowFastIv S35 c35Lit))
      (planarMat (x35Path 1).1) :=
    planarMat_matFpMem_polyRowFastIv (by decide) S35_pos c35Lit_mem
  have hdet : FpIv.FpMem S35 Q35_34 (planarMat (x35Path 1).1).det := by
    have hg := gaussDetIv_mem S35_pos gauss35_eq (FpIv.ofInt_mem S35 1) hmat
    simpa [one_mul] using hg
  have hden : (den35_cert.lo : ℝ) ≤ (S35 : ℝ) * planarDen (x35Path 1).1 := by
    rw [← den35_eq]
    have hap := activePairs_valid 35 pts35X
    exact denFoldIv_lo_le_planarDen S35_pos hap.1 hap.2 c35Lit_mem
  exact planar_atiyahDet_neg_and_norm_lt_one_of_fpMem S35_pos hy hz hdet hden
    cert35_bounds.1 cert35_bounds.2

/-- **New lowered planar record (`n = 35`):** direct nonzero witness violating Conjecture 2 (`-1 < D_35 < 0`). -/
theorem exists_planar_35_violating_conjecture_2 :
    ∃ x : DistinctPoints 35, IsCoplanar x ∧
      (atiyahDet x).im = 0 ∧ (atiyahDet x).re < 0 ∧ ‖atiyahDet x‖ < 1 :=
  ⟨x35Path 1, x35Path_isCoplanar 1, x35Path_one_re_neg_and_norm_lt_one⟩

/-- **New lowered planar record (`n = 35`):** singular witness `D_35 = 0` refuting C1 and C2. -/
theorem exists_planar_35_atiyahDet_zero :
    ∃ x : DistinctPoints 35, IsCoplanar x ∧
      atiyahDet x = 0 ∧
      ¬ LinearIndependent ℂ (fun i : Fin 35 =>
          atiyahPoly (fun u v => canonicalSpinor (unitDir (x.1 u) (x.1 v))) i) := by
  let f : ℝ → ℝ := fun s => (atiyahDet (x35Path s)).re
  have hcont : ContinuousOn f (Set.Icc (0 : ℝ) 1) := x35Path_cont_re.continuousOn
  have hf0 : f 0 = 1 := by
    change (atiyahDet (x35Path 0)).re = 1
    rw [x35Path_zero_det]; simp
  have hf1 : f 1 < 0 := by
    change (atiyahDet (x35Path 1)).re < 0
    exact x35Path_one_re_neg_and_norm_lt_one.2.1
  obtain ⟨s₀, _, hs₀⟩ := intermediate_value_Icc' zero_le_one hcont ⟨hf1.le, by linarith [hf0]⟩
  have hreal := x35Path_det_eq s₀
  have hdet0 : atiyahDet (x35Path s₀) = 0 := by
    have hre0 : ((planarMat (x35Path s₀).1).det / planarDen (x35Path s₀).1 : ℝ) = 0 := by
      have hs0' : (atiyahDet (x35Path s₀)).re = 0 := hs₀
      rw [hreal, Complex.ofReal_re] at hs0'
      exact hs0'
    rw [hreal, hre0, Complex.ofReal_zero]
  exact ⟨x35Path s₀, x35Path_isCoplanar s₀, hdet0,
    not_linearIndependent_of_atiyahDet_zero (by omega) (x35Path s₀) hdet0⟩

end Shield35

private lemma pts35_val0x : pts35X ⟨0, by omega⟩ = 0 := by decide
private lemma pts35_val0z : pts35Z ⟨0, by omega⟩ = 0 := by decide
private lemma pts35_val1x : pts35X ⟨1, by omega⟩ = 0 := by decide
private lemma pts35_val1z : pts35Z ⟨1, by omega⟩ = 1000000000 := by decide
private lemma pts35_val6x : pts35X ⟨6, by omega⟩ = -389449507282221965 := by decide
private lemma pts35_val6z : pts35Z ⟨6, by omega⟩ = 4769344000000000 := by decide

private lemma vec3_eval35 (a b c : ℝ) :
    (![a, b, c] : Fin 3 → ℝ) 0 = a ∧
    (![a, b, c] : Fin 3 → ℝ) 1 = b ∧
    (![a, b, c] : Fin 3 → ℝ) 2 = c := ⟨rfl, rfl, rfl⟩

lemma not_isCoplanar_mirrorPairExt_x35Path {s H : ℝ} (hs : s ≠ 0) :
    ¬ IsCoplanar (mirrorPairExt (x35Path s) (x35Path_hy s) H) := by
  rintro ⟨normal, d, hne, hplane⟩
  have h0 := hplane ⟨0, by omega⟩
  have h1 := hplane ⟨1, by omega⟩
  have h6 := hplane ⟨6, by omega⟩
  have h35 := hplane ⟨35, by omega⟩
  simp only [mirrorPairExt, show (0 : ℕ) < 35 by omega, show (1 : ℕ) < 35 by omega,
    show (6 : ℕ) < 35 by omega, show ¬ (35 : ℕ) < 35 by omega, ↓reduceDIte, ↓reduceIte,
    x35Path, planarPath, pts35_val0x, pts35_val0z, pts35_val1x, pts35_val1z,
    pts35_val6x, pts35_val6z, Int.cast_zero, Int.cast_ofNat, Int.cast_neg,
    vec3_eval35] at h0 h1 h6 h35
  have hd0 : d = 0 := by linarith
  have hn2 : normal 2 = 0 := by linarith
  have hmul : normal 0 * (s * (-389449507282221965)) = 0 := by linarith
  have hs_ne : s * (-389449507282221965) ≠ 0 := mul_ne_zero hs (by norm_num)
  have hn0 : normal 0 = 0 := (mul_eq_zero.mp hmul).resolve_right hs_ne
  rw [hn0, hn2, hd0] at h35
  have hn1 : normal 1 = 0 := by linarith
  rcases hne with h | h | h
  · exact h hn0
  · exact h hn1
  · exact h hn2

private lemma continuous_x35Path_coord (i : Fin 35) (c : Fin 3) :
    Continuous (fun s => (x35Path s).1 i c) := by
  fin_cases c <;> simp [x35Path, planarPath] <;> continuity

private lemma pts35_abs_le : ∀ i : Fin 35,
    |pts35X i| ≤ 10 ^ 18 ∧ |pts35Z i| ≤ 10 ^ 18 := by
  decide

private lemma x35Path_norm_sq_le : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ i : Fin 35,
    (x35Path s).1 i 0 ^ 2 + (x35Path s).1 i 1 ^ 2 + (x35Path s).1 i 2 ^ 2 ≤ 10 ^ 37 := by
  intro s hs i
  have hb := pts35_abs_le i
  have hxR : |(pts35X i : ℝ)| ≤ (10 : ℝ) ^ 18 := by exact_mod_cast hb.1
  have hzR : |(pts35Z i : ℝ)| ≤ (10 : ℝ) ^ 18 := by exact_mod_cast hb.2
  have hs_abs : |s| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1], hs.2⟩
  have hx_sq : (s * (pts35X i : ℝ)) ^ 2 ≤ ((10 : ℝ) ^ 18) ^ 2 := by
    have hmul : |s * (pts35X i : ℝ)| ≤ (10 : ℝ) ^ 18 := by
      rw [abs_mul]; nlinarith [abs_nonneg s, abs_nonneg (pts35X i : ℝ)]
    have h1 : |s * (pts35X i : ℝ)| ^ 2 ≤ ((10 : ℝ) ^ 18) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) hmul 2
    rwa [sq_abs] at h1
  have hz_sq : ((pts35Z i : ℝ)) ^ 2 ≤ ((10 : ℝ) ^ 18) ^ 2 := by
    have h1 : |(pts35Z i : ℝ)| ^ 2 ≤ ((10 : ℝ) ^ 18) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hzR 2
    rwa [sq_abs] at h1
  simp only [x35Path, planarPath, vec3_eval35]
  linarith [hx_sq, hz_sq]

private lemma mirrorPair_anchor35 {n : ℕ} (x0 x1 : DistinctPoints n)
    (hy0 : ∀ i, x0.1 i 1 = 0) (hy1 : ∀ i, x1.1 i 1 = 0)
    (hre0 : 0 < (atiyahDet x0).re) (hre1 : (atiyahDet x1).re < 0)
    (hnorm1 : ‖atiyahDet x1‖ < 1) :
    ∃ H : ℝ,
      (0 < (atiyahDet (mirrorPairExt x0 hy0 H)).re) ∧
      ((atiyahDet (mirrorPairExt x1 hy1 H)).re < 0 ∧
       ‖atiyahDet (mirrorPairExt x1 hy1 H)‖ < 1) := by
  have hev0 : ∀ᶠ H : ℝ in atTop, 0 < (atiyahDet (mirrorPairExt x0 hy0 H)).re :=
    (Complex.continuous_re.continuousAt.tendsto.comp
      (tendsto_atiyahDet_mirrorPairExt_atTop x0 hy0)).eventually (lt_mem_nhds hre0)
  have ht1 := tendsto_atiyahDet_mirrorPairExt_atTop x1 hy1
  have hev1 : ∀ᶠ H : ℝ in atTop, (atiyahDet (mirrorPairExt x1 hy1 H)).re < 0 :=
    (Complex.continuous_re.continuousAt.tendsto.comp ht1).eventually (gt_mem_nhds hre1)
  have hev2 : ∀ᶠ H : ℝ in atTop, ‖atiyahDet (mirrorPairExt x1 hy1 H)‖ < 1 :=
    ht1.norm.eventually (gt_mem_nhds hnorm1)
  exact (hev0.and (hev1.and hev2)).exists

private lemma continuous_mirrorPair35 (H : ℝ) :
    Continuous (fun s => atiyahDet (mirrorPairExt (x35Path s) (x35Path_hy s) H)) := by
  rw [continuous_iff_continuousAt]
  intro s₀
  refine tendsto_atiyahDet_of_tendsto (fun s => mirrorPairExt (x35Path s) (x35Path_hy s) H)
    (mirrorPairExt (x35Path s₀) (x35Path_hy s₀) H) fun i => ?_
  rw [tendsto_pi_nhds]; intro c
  by_cases hi : i.1 < 35
  · simp only [mirrorPairExt, hi, ↓reduceDIte]
    exact (continuous_x35Path_coord ⟨i.1, hi⟩ c).continuousAt.tendsto
  · by_cases hin : i.1 = 35 <;> simp [mirrorPairExt, hi, hin]

section IrredPlanar35
attribute [local irreducible] atiyahDet rawScaledHypDet hyperbolicAtiyahDet x35Path

private lemma x35Path_zero_re_pos : 0 < (atiyahDet (x35Path 0)).re := by
  have h0 : atiyahDet (x35Path 0) = 1 := x35Path_zero_det
  rw [h0, Complex.one_re]; norm_num

/-- **Lowered strictly non-coplanar 3D C2 record (`n = 37`, `-1 < D_37 < 0`).** -/
theorem exists_noncoplanar_37_violating_conjecture_2 :
    ∃ x : DistinctPoints 37, ¬ IsCoplanar x ∧
      (atiyahDet x).im = 0 ∧ (atiyahDet x).re < 0 ∧ ‖atiyahDet x‖ < 1 := by
  obtain ⟨H, _, hre1, hnorm1⟩ := mirrorPair_anchor35 (x35Path 0) (x35Path 1)
    (x35Path_hy 0) (x35Path_hy 1) x35Path_zero_re_pos
    x35Path_one_re_neg_and_norm_lt_one.2.1 x35Path_one_re_neg_and_norm_lt_one.2.2
  refine ⟨mirrorPairExt (x35Path 1) (x35Path_hy 1) H,
    not_isCoplanar_mirrorPairExt_x35Path one_ne_zero,
    atiyahDet_mirrorPairExt_im_eq_zero (x35Path 1) (x35Path_hy 1) H,
    hre1, hnorm1⟩

/-- **Lowered strictly non-coplanar 3D mirror-pair zero (`n = 37`, `D_37 = 0`).** -/
theorem exists_noncoplanar_37_atiyahDet_zero :
    ∃ x : DistinctPoints 37, ¬ IsCoplanar x ∧
      atiyahDet x = 0 ∧
      ¬ LinearIndependent ℂ (fun i : Fin 37 =>
          atiyahPoly (fun u v => canonicalSpinor (unitDir (x.1 u) (x.1 v))) i) := by
  obtain ⟨H, hc0, hc1, _⟩ := mirrorPair_anchor35 (x35Path 0) (x35Path 1)
    (x35Path_hy 0) (x35Path_hy 1) x35Path_zero_re_pos
    x35Path_one_re_neg_and_norm_lt_one.2.1 x35Path_one_re_neg_and_norm_lt_one.2.2
  let path : ℝ → DistinctPoints 37 := fun s => mirrorPairExt (x35Path s) (x35Path_hy s) H
  let f : ℝ → ℝ := fun s => (atiyahDet (path s)).re
  have hf_cont : ContinuousOn f (Set.Icc (0 : ℝ) 1) :=
    (Complex.continuous_re.comp (continuous_mirrorPair35 H)).continuousOn
  obtain ⟨s₀, _, hs₀⟩ := intermediate_value_Icc' zero_le_one hf_cont ⟨hc1.le, hc0.le⟩
  have hs₀_ne : s₀ ≠ 0 := by
    intro hs0
    have h0 : f s₀ = 0 := hs₀
    rw [hs0] at h0
    linarith [hc0, h0]
  have him0 : (atiyahDet (path s₀)).im = 0 :=
    atiyahDet_mirrorPairExt_im_eq_zero (x35Path s₀) (x35Path_hy s₀) H
  have hdet0 : atiyahDet (path s₀) = 0 := Complex.ext hs₀ him0
  exact ⟨path s₀, not_isCoplanar_mirrorPairExt_x35Path hs₀_ne, hdet0,
    not_linearIndependent_of_atiyahDet_zero (by omega) (path s₀) hdet0⟩

/-- **Lowered planar hyperbolic `H^2` C2 record (`n = 35`, `-1 < D_35^H < 0`).** -/
theorem exists_planar_35_hyperbolic_violating_conjecture_2 :
    ∃ q : KleinBallPoints 35, IsHyperbolicCoplanar q ∧
      (hyperbolicAtiyahDet q).im = 0 ∧ (hyperbolicAtiyahDet q).re < 0 ∧ ‖hyperbolicAtiyahDet q‖ < 1 :=
  (hyperbolic_planar_c2_and_zero_of_path (by omega) x35Path x35Path_hy continuous_x35Path_coord
    (by positivity) x35Path_norm_sq_le x35Path_zero_re_pos
    x35Path_one_re_neg_and_norm_lt_one.2.1 x35Path_one_re_neg_and_norm_lt_one.2.2).1

/-- **Lowered planar hyperbolic `H^2` C1 record (`n = 35`, `D_35^H = 0`).** -/
theorem exists_planar_35_hyperbolic_atiyahDet_zero :
    ∃ q : KleinBallPoints 35, IsHyperbolicCoplanar q ∧
      hyperbolicAtiyahDet q = 0 ∧ ¬ LinearIndependent ℂ (fun i : Fin 35 => hyperbolicAtiyahPoly q i) :=
  (hyperbolic_planar_c2_and_zero_of_path (by omega) x35Path x35Path_hy continuous_x35Path_coord
    (by positivity) x35Path_norm_sq_le x35Path_zero_re_pos
    x35Path_one_re_neg_and_norm_lt_one.2.1 x35Path_one_re_neg_and_norm_lt_one.2.2).2

/-- **Lowered strictly non-coplanar `H^3` mirror-pair direct C2 record (`n = 37`, `-1 < D_37^H < 0`).** -/
theorem exists_noncoplanar_37_hyperbolic_violating_conjecture_2 :
    ∃ q : KleinBallPoints 37, ¬ IsHyperbolicCoplanar q ∧
      (hyperbolicAtiyahDet q).im = 0 ∧ (hyperbolicAtiyahDet q).re < 0 ∧ ‖hyperbolicAtiyahDet q‖ < 1 := by
  obtain ⟨_, ⟨q1, hiff1, him1, hre1, hnorm1⟩, _⟩ :=
    hyperbolic_mirrorPair_c2_and_zero_of_path (by omega) x35Path x35Path_hy continuous_x35Path_coord
      (by positivity) x35Path_norm_sq_le x35Path_zero_re_pos
      x35Path_one_re_neg_and_norm_lt_one.2.1 x35Path_one_re_neg_and_norm_lt_one.2.2
  exact ⟨q1, hiff1.not.mpr (not_isCoplanar_mirrorPairExt_x35Path one_ne_zero), him1, hre1, hnorm1⟩

/-- **Lowered strictly non-coplanar `H^3` mirror-pair zero (`n = 37`, `D_37^H = 0`).** -/
theorem exists_noncoplanar_37_hyperbolic_atiyahDet_zero :
    ∃ q : KleinBallPoints 37, ¬ IsHyperbolicCoplanar q ∧
      hyperbolicAtiyahDet q = 0 ∧ ¬ LinearIndependent ℂ (fun i : Fin 37 => hyperbolicAtiyahPoly q i) := by
  obtain ⟨_, _, ⟨s₀, _, hs₀_ne, q0, hiff0, hdet0, hdep0⟩⟩ :=
    hyperbolic_mirrorPair_c2_and_zero_of_path (by omega) x35Path x35Path_hy continuous_x35Path_coord
      (by positivity) x35Path_norm_sq_le x35Path_zero_re_pos
      x35Path_one_re_neg_and_norm_lt_one.2.1 x35Path_one_re_neg_and_norm_lt_one.2.2
  exact ⟨q0, hiff0.not.mpr (not_isCoplanar_mirrorPairExt_x35Path hs₀_ne), hdet0, hdep0⟩

end IrredPlanar35

end Planar35Cert

/-! ## Part 2: General Permutation Invariance and Hyperbolic `H^3` Upgrade at `n = 26` -/

section Hyperbolic26

private lemma atiyahDetOfSpinors_swap_lt {n : ℕ} (ψ : Fin n → Fin n → Fin 2 → ℂ)
    {u v : Fin n} (huv : u < v) :
    atiyahDetOfSpinors (fun i j => ψ (Equiv.swap u v i) (Equiv.swap u v j)) =
      atiyahDetOfSpinors ψ := by
  classical
  let τ : Equiv.Perm (Fin n) := Equiv.swap u v
  let ψ' : Fin n → Fin n → Fin 2 → ℂ := fun i j => ψ (τ i) (τ j)
  have hpoly : ∀ i : Fin n, atiyahPoly ψ' i = atiyahPoly ψ (τ i) := by
    intro i
    simp only [atiyahPoly]
    refine Finset.prod_bij (fun j _ => τ j) ?_ ?_ ?_ ?_
    · intro j hj
      exact Finset.mem_erase.mpr ⟨τ.injective.ne (Finset.mem_erase.mp hj).1, Finset.mem_univ _⟩
    · intro _ _ _ _ heq; exact τ.injective heq
    · intro b hb
      refine ⟨τ b, Finset.mem_erase.mpr ⟨fun he => ?_, Finset.mem_univ _⟩, by simp [τ]⟩
      have : b = τ i := by simpa [τ] using congrArg τ he
      exact (Finset.mem_erase.mp hb).1 this
    · intro j _; rfl
  have hmat : atiyahMat ψ' = (atiyahMat ψ).submatrix τ id := by
    ext i k; simp [atiyahMat, hpoly i]
  have hdet_mat : (atiyahMat ψ').det = -(atiyahMat ψ).det := by
    rw [hmat, Matrix.det_permute τ (atiyahMat ψ), Equiv.Perm.sign_swap (ne_of_lt huv)]
    simp
  have hden : atiyahDen ψ' = -atiyahDen ψ := by
    let E := { p : Fin n × Fin n // p.1 < p.2 }
    let swapPair : E → E := fun e =>
      if h : τ e.1.1 < τ e.1.2 then ⟨(τ e.1.1, τ e.1.2), h⟩
      else ⟨(τ e.1.2, τ e.1.1), lt_of_le_of_ne (not_lt.mp h) (fun eq => e.2.ne (τ.injective eq.symm))⟩
    have hττ : ∀ z : Fin n, τ (τ z) = z := fun z => Equiv.swap_apply_self u v z
    have hinv : ∀ e : E, swapPair (swapPair e) = e := by
      intro ⟨⟨a, b⟩, hab⟩
      dsimp only [swapPair]
      by_cases h1 : τ a < τ b
      · simp only [h1, ↓reduceDIte, hττ, hab]
      · simp only [h1, ↓reduceDIte, hττ]
        have hba : ¬ b < a := not_lt_of_gt hab
        simp [hba]
    have hterm : ∀ e : E,
        omega (ψ' e.1.1 e.1.2) (ψ' e.1.2 e.1.1) =
          (if τ e.1.1 < τ e.1.2 then (1 : ℂ) else -1) *
            omega (ψ (swapPair e).1.1 (swapPair e).1.2) (ψ (swapPair e).1.2 (swapPair e).1.1) := by
      intro e
      by_cases h1 : τ e.1.1 < τ e.1.2
      · simp only [h1, ↓reduceIte, ↓reduceDIte, swapPair, one_mul, ψ']
      · simp only [h1, ↓reduceIte, ↓reduceDIte, swapPair, ψ']
        rw [omega_swap]; ring
    have hprod_split :
        atiyahDen ψ' =
          (∏ e : E, if τ e.1.1 < τ e.1.2 then (1 : ℂ) else -1) *
            (∏ e : E, omega (ψ (swapPair e).1.1 (swapPair e).1.2) (ψ (swapPair e).1.2 (swapPair e).1.1)) := by
      simp only [atiyahDen]
      rw [Finset.prod_congr rfl fun e _ => hterm e, Finset.prod_mul_distrib]
    have hprod_bij :
        (∏ e : E, omega (ψ (swapPair e).1.1 (swapPair e).1.2) (ψ (swapPair e).1.2 (swapPair e).1.1)) =
          atiyahDen ψ := by
      refine Finset.prod_bij (fun e _ => swapPair e) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
      · intro e₁ _ e₂ _ heq; simpa [hinv] using congrArg swapPair heq
      · intro e _; exact ⟨swapPair e, Finset.mem_univ _, hinv e⟩
      · intro _ _; rfl
    let S : Finset E := Finset.univ.filter (fun e : E => ¬ τ e.1.1 < τ e.1.2)
    have hsign_prod : (∏ e : E, if τ e.1.1 < τ e.1.2 then (1 : ℂ) else -1) = (-1 : ℂ) ^ S.card := by
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun e : E => ¬ τ e.1.1 < τ e.1.2)]
      have h1 : (∏ e ∈ S, if τ e.1.1 < τ e.1.2 then (1 : ℂ) else -1) = (-1 : ℂ) ^ S.card := by
        calc
          (∏ e ∈ S, if τ e.1.1 < τ e.1.2 then (1 : ℂ) else -1)
            = ∏ _e ∈ S, (-1 : ℂ) := Finset.prod_congr rfl fun e he => by
                simp [(Finset.mem_filter.mp he).2]
          _ = (-1 : ℂ) ^ S.card := Finset.prod_const _
      have h2 : (∏ e ∈ Finset.univ.filter (fun e : E => ¬ ¬ τ e.1.1 < τ e.1.2),
          if τ e.1.1 < τ e.1.2 then (1 : ℂ) else -1) = 1 :=
        Finset.prod_eq_one fun e he => by
          have hp : τ e.1.1 < τ e.1.2 := by simpa using (Finset.mem_filter.mp he).2
          simp [hp]
      rw [h1, h2, mul_one]
    let S₁ : Finset E := Finset.univ.filter (fun e : E => e.1.1 = u ∧ u < e.1.2 ∧ e.1.2 < v)
    let S₂ : Finset E := Finset.univ.filter (fun e : E => u < e.1.1 ∧ e.1.1 < v ∧ e.1.2 = v)
    have hS_eq : S = insert (⟨(u, v), huv⟩ : E) (S₁ ∪ S₂) := by
      ext ⟨⟨a, b⟩, hab⟩
      have hab' : a.1 < b.1 := hab
      have huv' : u.1 < v.1 := huv
      simp only [S, S₁, S₂, Finset.mem_insert, Finset.mem_union, Finset.mem_filter,
        Finset.mem_univ, true_and]
      change ¬ τ a < τ b ↔ (⟨(a, b), hab⟩ : E) = ⟨(u, v), huv⟩ ∨
        (a = u ∧ u < b ∧ b < v) ∨ (u < a ∧ a < v ∧ b = v)
      simp only [τ, Subtype.ext_iff, Prod.ext_iff, Equiv.swap_apply_def, Fin.ext_iff, Fin.lt_def]
      split_ifs <;> omega
    have he_not_mem : (⟨(u, v), huv⟩ : E) ∉ S₁ ∪ S₂ := by
      intro hmem
      rcases Finset.mem_union.mp hmem with h1 | h2
      · exact lt_irrefl v (Finset.mem_filter.mp h1).2.2.2
      · exact lt_irrefl u (Finset.mem_filter.mp h2).2.1
    have hS_disj : Disjoint S₁ S₂ := by
      rw [Finset.disjoint_left]
      intro e he1 he2
      have h1 : e.1.2 < v := (Finset.mem_filter.mp he1).2.2.2
      have h2 : e.1.2 = v := (Finset.mem_filter.mp he2).2.2.2
      rw [h2] at h1
      exact lt_irrefl v h1
    have hS1_eq_S2 : S₁.card = S₂.card := by
      refine Finset.card_bij
        (fun e he => (⟨(e.1.2, v), (Finset.mem_filter.mp he).2.2.2⟩ : E)) ?_ ?_ ?_
      · intro e he
        have he' := (Finset.mem_filter.mp he).2
        simp [S₂, he'.2.1, he'.2.2]
      · intro e₁ he₁ e₂ he₂ heq
        have h1 : e₁.1.1 = u := (Finset.mem_filter.mp he₁).2.1
        have h2 : e₂.1.1 = u := (Finset.mem_filter.mp he₂).2.1
        have h12 : e₁.1.2 = e₂.1.2 := by simpa using congrArg (fun x : E => x.1.1) heq
        exact Subtype.ext (Prod.ext (h1.trans h2.symm) h12)
      · intro e' he'
        have he'' := (Finset.mem_filter.mp he').2
        refine ⟨⟨(u, e'.1.1), he''.1⟩, ?_, ?_⟩
        · simp [S₁, he''.1, he''.2.1]
        · exact Subtype.ext (Prod.ext rfl he''.2.2.symm)
    have hcard : S.card = 1 + 2 * S₁.card := by
      rw [hS_eq, Finset.card_insert_of_notMem he_not_mem, Finset.card_union_of_disjoint hS_disj,
        ← hS1_eq_S2]
      omega
    rw [hprod_split, hprod_bij, hsign_prod, hcard, pow_add, pow_mul]
    norm_num
  change (atiyahMat ψ').det / atiyahDen ψ' = (atiyahMat ψ).det / atiyahDen ψ
  rw [hdet_mat, hden, neg_div_neg_eq]

private lemma atiyahDetOfSpinors_swap {n : ℕ} (ψ : Fin n → Fin n → Fin 2 → ℂ) (u v : Fin n) :
    atiyahDetOfSpinors (fun i j => ψ (Equiv.swap u v i) (Equiv.swap u v j)) =
      atiyahDetOfSpinors ψ := by
  rcases lt_trichotomy u v with huv | rfl | hvu
  · exact atiyahDetOfSpinors_swap_lt ψ huv
  · simp
  · rw [Equiv.swap_comm]; exact atiyahDetOfSpinors_swap_lt ψ hvu

/-- Permutation invariance of `atiyahDetOfSpinors` for arbitrary spinor tables. -/
lemma atiyahDetOfSpinors_perm {n : ℕ} (ψ : Fin n → Fin n → Fin 2 → ℂ) (σ : Equiv.Perm (Fin n)) :
    atiyahDetOfSpinors (fun i j => ψ (σ i) (σ j)) = atiyahDetOfSpinors ψ := by
  revert ψ
  refine Equiv.Perm.swap_induction_on σ ?_ ?_
  · intro ψ; simp
  · intro f u v _ ih ψ
    have hcomp : (fun i j => ψ ((Equiv.swap u v * f) i) ((Equiv.swap u v * f) j)) =
        (fun i j => (fun a b => ψ (Equiv.swap u v a) (Equiv.swap u v b)) (f i) (f j)) := rfl
    rw [hcomp, ih (fun a b => ψ (Equiv.swap u v a) (Equiv.swap u v b)), atiyahDetOfSpinors_swap]

/-- Conjugation invariance of `atiyahDetOfSpinors`. -/
lemma atiyahDetOfSpinors_conj {n : ℕ} (ψ : Fin n → Fin n → Fin 2 → ℂ) :
    atiyahDetOfSpinors (fun i j k => starRingEnd ℂ (ψ i j k)) =
      starRingEnd ℂ (atiyahDetOfSpinors ψ) := by
  let φ : Fin n → Fin n → Fin 2 → ℂ := fun i j k => starRingEnd ℂ (ψ i j k)
  have hpoly : ∀ i, atiyahPoly φ i = (atiyahPoly ψ i).map (starRingEnd ℂ) := by
    intro i
    simp only [atiyahPoly, Polynomial.map_prod, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.map_X]
    rfl
  have hmat : atiyahMat φ = (starRingEnd ℂ).mapMatrix (atiyahMat ψ) := by
    ext i k; simp [atiyahMat, hpoly i, Polynomial.coeff_map]
  have hdet : (atiyahMat φ).det = starRingEnd ℂ (atiyahMat ψ).det := by
    rw [hmat, ← RingHom.map_det]
  have hden : atiyahDen φ = starRingEnd ℂ (atiyahDen ψ) := by
    simp only [atiyahDen, map_prod]
    refine Finset.prod_congr rfl fun e _ => omega_conj (ψ e.1.1 e.1.2) (ψ e.1.2 e.1.1)
  change (atiyahMat φ).det / atiyahDen φ = starRingEnd ℂ ((atiyahMat ψ).det / atiyahDen ψ)
  rw [hdet, hden, map_div₀]

/-- Any unit-direction table invariant under `y`-reflection modulo an arbitrary permutation `σ` has real determinant. -/
theorem atiyahDetOfSpinors_im_eq_zero_of_perm_yRefl {n : ℕ}
    (u : Fin n → Fin n → Fin 3 → ℝ)
    (hu_norm : ∀ i j, i ≠ j → u i j 0 ^ 2 + u i j 1 ^ 2 + u i j 2 ^ 2 = 1)
    (hu_ne : ∀ i j, i ≠ j → u i j ≠ u j i)
    (σ : Equiv.Perm (Fin n))
    (hu_sym : ∀ i j, i ≠ j → u (σ i) (σ j) = ![u i j 0, -u i j 1, u i j 2]) :
    (atiyahDetOfSpinors (fun i j => canonicalSpinor (u i j))).im = 0 := by
  let ψ0 := fun i j => canonicalSpinor (u i j)
  let φ := fun i j k => starRingEnd ℂ (ψ0 i j k)
  have hφ_ne : ∀ i j, i ≠ j → φ i j 0 ≠ 0 ∨ φ i j 1 ≠ 0 := fun i j hij => by
    simpa [φ] using isPosSpinor_ne_zero (isPosSpinor_canonicalSpinor (hu_norm i j hij))
  have hφ_mul : ∀ i j, i ≠ j → (pauliDot (u (σ i) (σ j))).mulVec (φ i j) = φ i j := by
    intro i j hij
    rw [hu_sym i j hij]
    exact pauliDot_mulVec_conj_yRefl (isPosSpinor_canonicalSpinor (hu_norm i j hij)).2
  have heq := atiyahDetOfSpinors_eq_of_unitSpinors
    (fun i j => u (σ i) (σ j))
    (fun i j hij => hu_norm (σ i) (σ j) (σ.injective.ne hij))
    (fun i j hij => hu_ne (σ i) (σ j) (σ.injective.ne hij))
    φ hφ_ne hφ_mul
  have hperm : atiyahDetOfSpinors (fun i j => ψ0 (σ i) (σ j)) = atiyahDetOfSpinors ψ0 :=
    atiyahDetOfSpinors_perm ψ0 σ
  have hconj : atiyahDetOfSpinors φ = starRingEnd ℂ (atiyahDetOfSpinors ψ0) :=
    atiyahDetOfSpinors_conj ψ0
  have hself : starRingEnd ℂ (atiyahDetOfSpinors ψ0) = atiyahDetOfSpinors ψ0 := by
    calc
      starRingEnd ℂ (atiyahDetOfSpinors ψ0) = atiyahDetOfSpinors φ := hconj.symm
      _ = atiyahDetOfSpinors (fun i j => ψ0 (σ i) (σ j)) := heq.symm
      _ = atiyahDetOfSpinors ψ0 := hperm
  exact Complex.conj_eq_iff_im.mp hself

private lemma continuous_x26Clamp_coord (i : Fin 26) (c : Fin 3) :
    Continuous (fun t => (x26Clamp t).1 i c) := by
  fin_cases c <;> simp [x26Clamp, x26ClampRaw] <;> continuity

private lemma pts26_abs_le : ∀ i : Fin 26,
    |x26BaseX i| ≤ 400 ∧ |x26BaseY i| ≤ 400 ∧ |x26BaseZ i| ≤ 4000 := by
  decide

private lemma x26Clamp_norm_sq_le : ∀ t ∈ Set.Icc (8 : ℝ) 10, ∀ i : Fin 26,
    (x26Clamp t).1 i 0 ^ 2 + (x26Clamp t).1 i 1 ^ 2 + (x26Clamp t).1 i 2 ^ 2 ≤ 10 ^ 8 := by
  intro t ht i
  have hb := pts26_abs_le i
  have hxR : |(x26BaseX i : ℝ)| ≤ 400 := by exact_mod_cast hb.1
  have hyR : |(x26BaseY i : ℝ)| ≤ 400 := by exact_mod_cast hb.2.1
  have hzR : |(x26BaseZ i : ℝ)| ≤ 4000 := by exact_mod_cast hb.2.2
  have hm : max t 1 = t := max_eq_left (by linarith [ht.1])
  have ht_abs : |t| ≤ 10 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  have hx_sq : (max t 1 * (x26BaseX i : ℝ)) ^ 2 ≤ 4000 ^ 2 := by
    rw [hm]
    have hmul : |t * (x26BaseX i : ℝ)| ≤ 4000 := by
      rw [abs_mul]; nlinarith [abs_nonneg t, abs_nonneg (x26BaseX i : ℝ)]
    have h1 : |t * (x26BaseX i : ℝ)| ^ 2 ≤ 4000 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hmul 2
    rwa [sq_abs] at h1
  have hy_sq : (max t 1 * (x26BaseY i : ℝ)) ^ 2 ≤ 4000 ^ 2 := by
    rw [hm]
    have hmul : |t * (x26BaseY i : ℝ)| ≤ 4000 := by
      rw [abs_mul]; nlinarith [abs_nonneg t, abs_nonneg (x26BaseY i : ℝ)]
    have h1 : |t * (x26BaseY i : ℝ)| ^ 2 ≤ 4000 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hmul 2
    rwa [sq_abs] at h1
  have hz_sq : ((x26BaseZ i : ℝ)) ^ 2 ≤ 4000 ^ 2 := by
    have h1 : |(x26BaseZ i : ℝ)| ^ 2 ≤ 4000 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hzR 2
    rwa [sq_abs] at h1
  simp only [x26Clamp, x26ClampRaw, vec3_eval35]
  linarith [hx_sq, hy_sq, hz_sq]

private lemma continuousOn_rawScaledHypDet_interval {n : ℕ}
    (x : ℝ → DistinctPoints n) (hcont : ∀ i c, Continuous (fun t => (x t).1 i c))
    {a b ε : ℝ} (hε0 : 0 < ε)
    (hq_ball : ∀ t ∈ Set.Icc a b,
      ∀ i : Fin n, (ε * (x t).1 i 0) ^ 2 + (ε * (x t).1 i 1) ^ 2 + (ε * (x t).1 i 2) ^ 2 < 1) :
    ContinuousOn (fun t => rawScaledHypDet (x t) ε) (Set.Icc a b) := by
  intro s₀ hs₀
  let l := nhdsWithin s₀ (Set.Icc a b)
  have hev_Icc : ∀ᶠ t in l, t ∈ Set.Icc a b := self_mem_nhdsWithin
  have hnorm : ∀ᶠ t in l, ∀ i j : Fin n, i ≠ j →
      kleinEndpoint (fun k => ε * (x t).1 i k) (fun k => ε * (x t).1 j k) 0 ^ 2 +
      kleinEndpoint (fun k => ε * (x t).1 i k) (fun k => ε * (x t).1 j k) 1 ^ 2 +
      kleinEndpoint (fun k => ε * (x t).1 i k) (fun k => ε * (x t).1 j k) 2 ^ 2 = 1 := by
    filter_upwards [hev_Icc] with t ht i j hij
    exact kleinEndpoint_norm_sq (hq_ball t ht i) fun h => (x t).2 i j hij
      (funext fun k => mul_left_cancel₀ hε0.ne' (congr_fun h k))
  have hne : ∀ᶠ t in l, ∀ i j : Fin n, i ≠ j →
      kleinEndpoint (fun k => ε * (x t).1 i k) (fun k => ε * (x t).1 j k) ≠
      kleinEndpoint (fun k => ε * (x t).1 j k) (fun k => ε * (x t).1 i k) := by
    filter_upwards [hev_Icc] with t ht i j hij
    exact kleinEndpoint_ne_swap (hq_ball t ht i) (hq_ball t ht j) fun h => (x t).2 i j hij
      (funext fun k => mul_left_cancel₀ hε0.ne' (congr_fun h k))
  have hdiff_ne : ∀ i j : Fin n, i ≠ j →
      (fun k => ε * (x s₀).1 i k) ≠ (fun k => ε * (x s₀).1 j k) := fun i j hij h =>
    (x s₀).2 i j hij (funext fun k => mul_left_cancel₀ hε0.ne' (congr_fun h k))
  refine tendsto_atiyahDetOfSpinors_unit
    (fun t i j => kleinEndpoint (fun k => ε * (x t).1 i k) (fun k => ε * (x t).1 j k))
    (fun i j => kleinEndpoint (fun k => ε * (x s₀).1 i k) (fun k => ε * (x s₀).1 j k))
    (fun i j hij => kleinEndpoint_norm_sq (hq_ball s₀ hs₀ i) (hdiff_ne i j hij))
    (fun i j hij => kleinEndpoint_ne_swap (hq_ball s₀ hs₀ i) (hq_ball s₀ hs₀ j) (hdiff_ne i j hij))
    hnorm hne ?_
  intro i j hij
  rw [tendsto_pi_nhds]; intro c
  have hpt : ∀ m k, Tendsto (fun t => ε * (x t).1 m k) l (nhds (ε * (x s₀).1 m k)) := fun m k =>
    (tendsto_const_nhds.mul ((hcont m k).continuousAt.tendsto)).mono_left nhdsWithin_le_nhds
  have hsub : ∀ k, Tendsto (fun t => ε * (x t).1 j k - ε * (x t).1 i k) l
      (nhds (ε * (x s₀).1 j k - ε * (x s₀).1 i k)) := fun k => (hpt j k).sub (hpt i k)
  have hnorm_t : Tendsto (fun t => euclidNorm (fun k => ε * (x t).1 j k - ε * (x t).1 i k)) l
      (nhds (euclidNorm (fun k => ε * (x s₀).1 j k - ε * (x s₀).1 i k))) := by
    unfold euclidNorm
    exact (((hsub 0).pow 2).add ((hsub 1).pow 2) |>.add ((hsub 2).pow 2)).sqrt
  have hr_ne : euclidNorm (fun k => ε * (x s₀).1 j k - ε * (x s₀).1 i k) ≠ 0 :=
    (euclidNorm_pos_of_ne (hdiff_ne i j hij)).ne'
  have hv_t : ∀ k, Tendsto (fun t => unitDir (fun m => ε * (x t).1 i m) (fun m => ε * (x t).1 j m) k) l
      (nhds (unitDir (fun m => ε * (x s₀).1 i m) (fun m => ε * (x s₀).1 j m) k)) := fun k =>
    (hsub k).div hnorm_t hr_ne
  have hc_t : Tendsto (fun t =>
      (ε * (x t).1 i 0) * unitDir (fun m => ε * (x t).1 i m) (fun m => ε * (x t).1 j m) 0 +
      (ε * (x t).1 i 1) * unitDir (fun m => ε * (x t).1 i m) (fun m => ε * (x t).1 j m) 1 +
      (ε * (x t).1 i 2) * unitDir (fun m => ε * (x t).1 i m) (fun m => ε * (x t).1 j m) 2) l
      (nhds ((ε * (x s₀).1 i 0) * unitDir (fun m => ε * (x s₀).1 i m) (fun m => ε * (x s₀).1 j m) 0 +
      (ε * (x s₀).1 i 1) * unitDir (fun m => ε * (x s₀).1 i m) (fun m => ε * (x s₀).1 j m) 1 +
      (ε * (x s₀).1 i 2) * unitDir (fun m => ε * (x s₀).1 i m) (fun m => ε * (x s₀).1 j m) 2)) :=
    ((hpt i 0).mul (hv_t 0)).add ((hpt i 1).mul (hv_t 1)) |>.add ((hpt i 2).mul (hv_t 2))
  have hdisc_t :=
    (((tendsto_const_nhds (x := (1 : ℝ))).sub ((((hpt i 0).pow 2).add ((hpt i 1).pow 2)).add ((hpt i 2).pow 2))).add
      (hc_t.pow 2)).sqrt
  exact (hpt i c).add ((hc_t.neg.add hdisc_t).mul (hv_t c))

private lemma rawScaledHypDet_x26_im_zero (t : ℝ) {ε : ℝ} (hε0 : 0 < ε)
    (hq : ∀ i : Fin 26, (ε * (x26Clamp t).1 i 0) ^ 2 + (ε * (x26Clamp t).1 i 1) ^ 2 + (ε * (x26Clamp t).1 i 2) ^ 2 < 1) :
    (rawScaledHypDet (x26Clamp t) ε).im = 0 := by
  refine atiyahDetOfSpinors_im_eq_zero_of_perm_yRefl
    (fun u v => kleinEndpoint (fun k => ε * (x26Clamp t).1 u k) (fun k => ε * (x26Clamp t).1 v k))
    (fun u v huv => kleinEndpoint_norm_sq (hq u) fun h => (x26Clamp t).2 u v huv
      (funext fun k => mul_left_cancel₀ hε0.ne' (congr_fun h k)))
    (fun u v huv => kleinEndpoint_ne_swap (hq u) (hq v) fun h => (x26Clamp t).2 u v huv
      (funext fun k => mul_left_cancel₀ hε0.ne' (congr_fun h k)))
    reflectPerm26 ?_
  intro u v _
  have hsmul : ∀ i : Fin 26, (fun k => ε * (x26Clamp t).1 (reflectPerm26 i) k) =
      ![(fun k => ε * (x26Clamp t).1 i k) 0, -(fun k => ε * (x26Clamp t).1 i k) 1,
        (fun k => ε * (x26Clamp t).1 i k) 2] := by
    intro i; ext c
    fin_cases c
    · change ε * (max t 1 * (x26BaseX (reflectPerm26 i) : ℝ)) = ε * (max t 1 * (x26BaseX i : ℝ))
      rw [(x26Base_reflect i).1]
    · change ε * (max t 1 * (x26BaseY (reflectPerm26 i) : ℝ)) = -(ε * (max t 1 * (x26BaseY i : ℝ)))
      rw [(x26Base_reflect i).2.1]; simp
    · change ε * (x26BaseZ (reflectPerm26 i) : ℝ) = ε * (x26BaseZ i : ℝ)
      rw [(x26Base_reflect i).2.2]
  exact (congrArg₂ kleinEndpoint (hsmul u) (hsmul v)).trans
    (kleinEndpoint_yRefl (fun k => ε * (x26Clamp t).1 u k) (fun k => ε * (x26Clamp t).1 v k))

private lemma x26Clamp_not_isCoplanar (t : ℝ) : ¬ IsCoplanar (x26Clamp t) := by
  rintro ⟨normal, d, hne, hall⟩
  exact x26Clamp_noncoplanar t ⟨normal 0, normal 1, normal 2, d, hne, hall⟩

section HypBridge26
attribute [local irreducible] atiyahDetOfSpinors

private lemma hyperbolicAtiyahDet_scaleKlein {n : ℕ} (x : DistinctPoints n) (ε : ℝ) (hε0 : 0 < ε)
    (hball : ∀ i : Fin n, (ε * x.1 i 0) ^ 2 + (ε * x.1 i 1) ^ 2 + (ε * x.1 i 2) ^ 2 < 1) :
    hyperbolicAtiyahDet (scaleKlein x ε hε0 hball) = rawScaledHypDet x ε := rfl

end HypBridge26

private lemma norm_lt_one_of_im_zero_re_bounds {z : ℂ} (him : z.im = 0) (hre : z.re < 0) (hgt : -1 < z.re) :
    ‖z‖ < 1 := by
  have hz : z = (z.re : ℂ) := Complex.ext rfl him
  rw [hz, Complex.norm_real, Real.norm_eq_abs, abs_of_neg hre]
  linarith

section IrredHyp26
attribute [local irreducible] atiyahDet rawScaledHypDet hyperbolicAtiyahDet x26Clamp

private lemma x26_hyp_uniform_family :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ t ∈ Set.Icc (8 : ℝ) 10, ∀ i : Fin 26,
        (ε * (x26Clamp t).1 i 0) ^ 2 + (ε * (x26Clamp t).1 i 1) ^ 2 + (ε * (x26Clamp t).1 i 2) ^ 2 < 1) ∧
      0 < (rawScaledHypDet (x26Clamp 8) ε).re ∧
      (rawScaledHypDet (x26Clamp 10) ε).re < 0 := by
  have hev_eps : ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε ∈ Set.Ioo (0 : ℝ) (min (1 / 2) (1 / ((10 : ℝ) ^ 8))) :=
    Ioo_mem_nhdsGT (lt_min (by norm_num) (by positivity))
  have ht0 : Tendsto (fun ε => (rawScaledHypDet (x26Clamp 8) ε).re) (nhdsWithin 0 (Set.Ioi 0)) (nhds (atiyahDet (x26Clamp 8)).re) :=
    (Complex.continuous_re.continuousAt (x := atiyahDet (x26Clamp 8))).tendsto.comp
      (tendsto_rawScaledHypDet_zero (x26Clamp 8))
  have hev0 : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < (rawScaledHypDet (x26Clamp 8) ε).re :=
    ht0.eventually (lt_mem_nhds atiyahDet_x26Clamp_8_re_pos)
  have ht1 : Tendsto (fun ε => (rawScaledHypDet (x26Clamp 10) ε).re) (nhdsWithin 0 (Set.Ioi 0)) (nhds (atiyahDet (x26Clamp 10)).re) :=
    (Complex.continuous_re.continuousAt (x := atiyahDet (x26Clamp 10))).tendsto.comp
      (tendsto_rawScaledHypDet_zero (x26Clamp 10))
  have hev1 : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), (rawScaledHypDet (x26Clamp 10) ε).re < 0 :=
    ht1.eventually (gt_mem_nhds atiyahDet_x26Clamp_10_re_neg)
  obtain ⟨ε, hmem, h0, h1⟩ := (hev_eps.and (hev0.and hev1)).exists
  have hB : (0 : ℝ) < (10 : ℝ) ^ 8 := by positivity
  exact ⟨ε, hmem.1, fun t ht => ball_of_lt_bound (x26Clamp t) hB (x26Clamp_norm_sq_le t ht) hmem.1 hmem.2, h0, h1⟩

/-- **Lowered strictly non-coplanar `H^3` C1 disproof (`n = 26`, `D_26^H = 0`).** -/
theorem exists_noncoplanar_26_hyperbolic_atiyahDet_zero :
    ∃ q : KleinBallPoints 26, ¬ IsHyperbolicCoplanar q ∧
      hyperbolicAtiyahDet q = 0 ∧ ¬ LinearIndependent ℂ (fun i : Fin 26 => hyperbolicAtiyahPoly q i) := by
  obtain ⟨ε, hε0, hq_ball, h0_re, h1_re⟩ := x26_hyp_uniform_family
  let f : ℝ → ℝ := fun t => (rawScaledHypDet (x26Clamp t) ε).re
  have hf_cont : ContinuousOn f (Set.Icc (8 : ℝ) 10) :=
    Complex.continuous_re.comp_continuousOn
      (continuousOn_rawScaledHypDet_interval x26Clamp continuous_x26Clamp_coord hε0 hq_ball)
  obtain ⟨t₀, ht₀, hft₀⟩ := intermediate_value_Icc' (by norm_num : (8 : ℝ) ≤ 10) hf_cont ⟨h1_re.le, h0_re.le⟩
  let q₀ := scaleKlein (x26Clamp t₀) ε hε0 (hq_ball t₀ ht₀)
  have hq_eq : hyperbolicAtiyahDet q₀ = rawScaledHypDet (x26Clamp t₀) ε :=
    hyperbolicAtiyahDet_scaleKlein (x26Clamp t₀) ε hε0 (hq_ball t₀ ht₀)
  have him0 : (hyperbolicAtiyahDet q₀).im = 0 := by
    rw [hq_eq]
    exact rawScaledHypDet_x26_im_zero t₀ hε0 (hq_ball t₀ ht₀)
  have hre0 : (hyperbolicAtiyahDet q₀).re = 0 := by
    rw [hq_eq]
    exact hft₀
  have hdet0 : hyperbolicAtiyahDet q₀ = 0 := Complex.ext hre0 him0
  exact ⟨q₀, (isHyperbolicCoplanar_scaleKlein_iff (x26Clamp t₀) ε hε0 (hq_ball t₀ ht₀)).not.mpr
    (x26Clamp_not_isCoplanar t₀), hdet0, not_linearIndependent_of_hyperbolicAtiyahDet_zero (by omega) q₀ hdet0⟩

private lemma exists_x26Clamp_euclid_c2 :
    ∃ t₁ : ℝ, (atiyahDet (x26Clamp t₁)).re < 0 ∧ ‖atiyahDet (x26Clamp t₁)‖ < 1 := by
  by_cases hgt : -1 < (atiyahDet (x26Clamp 10)).re
  · exact ⟨10, atiyahDet_x26Clamp_10_re_neg,
      norm_lt_one_of_im_zero_re_bounds (atiyahDet_x26Clamp_im_zero 10) atiyahDet_x26Clamp_10_re_neg hgt⟩
  · have hle : (atiyahDet (x26Clamp 10)).re ≤ -1 := not_lt.mp hgt
    have hmem : -(1 / 2 : ℝ) ∈ Set.Icc ((atiyahDet (x26Clamp 10)).re) ((atiyahDet (x26Clamp 8)).re) :=
      ⟨by linarith [hle], by linarith [atiyahDet_x26Clamp_8_re_pos]⟩
    obtain ⟨t₁, _, hft₁⟩ := intermediate_value_Icc' (by norm_num : (8 : ℝ) ≤ 10)
      continuous_atiyahDet_x26Clamp_re.continuousOn hmem
    have hre : (atiyahDet (x26Clamp t₁)).re < 0 := by linarith [hft₁]
    have hgt' : -1 < (atiyahDet (x26Clamp t₁)).re := by linarith [hft₁]
    exact ⟨t₁, hre, norm_lt_one_of_im_zero_re_bounds (atiyahDet_x26Clamp_im_zero t₁) hre hgt'⟩

/-- **Lowered strictly non-coplanar `H^3` direct nonzero C2 disproof (`n = 26`, `-1 < D_26^H < 0`).** -/
theorem exists_noncoplanar_26_hyperbolic_violating_conjecture_2 :
    ∃ q : KleinBallPoints 26, ¬ IsHyperbolicCoplanar q ∧
      (hyperbolicAtiyahDet q).im = 0 ∧ (hyperbolicAtiyahDet q).re < 0 ∧ ‖hyperbolicAtiyahDet q‖ < 1 := by
  obtain ⟨t₁, hre_t, hnorm_t⟩ := exists_x26Clamp_euclid_c2
  have hev_ball := eventually_scaleKlein_ball (x26Clamp t₁)
  have ht := tendsto_rawScaledHypDet_zero (x26Clamp t₁)
  have ht_re : Tendsto (fun ε => (rawScaledHypDet (x26Clamp t₁) ε).re)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (atiyahDet (x26Clamp t₁)).re) :=
    (Complex.continuous_re.continuousAt (x := atiyahDet (x26Clamp t₁))).tendsto.comp ht
  have hev_re : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), (rawScaledHypDet (x26Clamp t₁) ε).re < 0 :=
    ht_re.eventually (gt_mem_nhds hre_t)
  have hev_norm : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ‖rawScaledHypDet (x26Clamp t₁) ε‖ < 1 :=
    ht.norm.eventually (gt_mem_nhds hnorm_t)
  obtain ⟨ε, ⟨hε0, hball⟩, hre1, hnorm1⟩ := (hev_ball.and (hev_re.and hev_norm)).exists
  let q1 := scaleKlein (x26Clamp t₁) ε hε0 hball
  have hq_eq : hyperbolicAtiyahDet q1 = rawScaledHypDet (x26Clamp t₁) ε :=
    hyperbolicAtiyahDet_scaleKlein (x26Clamp t₁) ε hε0 hball
  refine ⟨q1, (isHyperbolicCoplanar_scaleKlein_iff (x26Clamp t₁) ε hε0 hball).not.mpr
    (x26Clamp_not_isCoplanar t₁), ?_, ?_, ?_⟩
  · rw [hq_eq]; exact rawScaledHypDet_x26_im_zero t₁ hε0 hball
  · rw [hq_eq]; exact hre1
  · rw [hq_eq]; exact hnorm1

end IrredHyp26

end Hyperbolic26

end Matematyka.AtiyahSutcliffePlanar35
""")

    out_path = ROOT / "lean" / "Matematyka" / "AtiyahSutcliffePlanar35.lean"
    out_path.write_text("".join(parts), encoding="utf-8")
    print(f"Generated {out_path} ({out_path.stat().st_size} bytes)")


if __name__ == "__main__":
    main()
