module

public import Matematyka.MalkounCounterexample

/-!
# Formal Disproof of the Atiyah–Sutcliffe Conjectures (2001 / 2002)

We formalize Sir Michael Atiyah's and Paul Sutcliffe's normalized determinant $D_n(\mathbf{x})$
on the configuration space $C_n(\mathbb{R}^3)$ of pairwise distinct points in $\mathbb{R}^3$,
and establish complete kernel-verified finite counterexamples (using standard Lean axioms
`{propext, Classical.choice, Quot.sound}` only):

1. **Outward-rounded fixed-point interval arithmetic (`FpIv`)** preventing integer bitwidth
   blowup across large products and polynomial recurrences.
2. **Literal 2001/2002 Atiyah–Sutcliffe definitions**, scale/phase invariance, equivalence of
   `atiyahDet x = 0` with linear dependence of the $n$ Atiyah polynomials, and collinear
   normalization `atiyahDet (collinear) = 1`.
3. **Ordered-height planar reduction ($y_i = 0$, $z_0 < \dots < z_{n-1}$)** proving reality,
   continuity along straight-line homotopies, and banded unit-pivot axial elimination.
4. **Conjecture 3 disproof at the sharp minimal size $n = 5$** in the Euclidean plane.
5. **Conjecture 1 & Conjecture 2 disproofs** via an explicit finite planar integer witness
   along a collision-free straight-line homotopy from $D_n = +1$ to $D_n < 0$.
-/

@[expose] public section

namespace Matematyka.AtiyahSutcliffe

open Complex Real Matrix Polynomial
open Matematyka.MalkounCounterexample

/-! ## Part 1: Outward-Rounded Fixed-Point Interval Arithmetic (`FpIv`) -/

section FixedPointIntervals

/-- Closed integer interval `[lo, hi]` representing scaled real numbers `S * x ∈ [lo, hi]`. -/
structure FpIv where
  lo : ℤ
  hi : ℤ
  deriving DecidableEq

namespace FpIv

def zmin (x y : ℤ) : ℤ := if x ≤ y then x else y
def zmax (x y : ℤ) : ℤ := if x ≤ y then y else x

private lemma zmin_le_left (x y : ℤ) : zmin x y ≤ x := by unfold zmin; split_ifs <;> omega
private lemma zmin_le_right (x y : ℤ) : zmin x y ≤ y := by unfold zmin; split_ifs <;> omega
private lemma le_zmax_left (x y : ℤ) : x ≤ zmax x y := by unfold zmax; split_ifs <;> omega
private lemma le_zmax_right (x y : ℤ) : y ≤ zmax x y := by unfold zmax; split_ifs <;> omega

/-- Fixed-point enclosure at positive scale `S`: `(a.lo : ℝ) ≤ S * x ≤ (a.hi : ℝ)`. -/
def FpMem (S : ℤ) (a : FpIv) (x : ℝ) : Prop :=
  (a.lo : ℝ) ≤ (S : ℝ) * x ∧ (S : ℝ) * x ≤ (a.hi : ℝ)

def zero : FpIv := ⟨0, 0⟩
def ofInt (S z : ℤ) : FpIv := ⟨S * z, S * z⟩
def add (a b : FpIv) : FpIv := ⟨a.lo + b.lo, a.hi + b.hi⟩
def sub (a b : FpIv) : FpIv := ⟨a.lo - b.hi, a.hi - b.lo⟩
def neg (a : FpIv) : FpIv := ⟨-a.hi, -a.lo⟩

def mulRaw (a b : FpIv) : FpIv :=
  let p1 := a.lo * b.lo
  let p2 := a.lo * b.hi
  let p3 := a.hi * b.lo
  let p4 := a.hi * b.hi
  ⟨zmin (zmin p1 p2) (zmin p3 p4), zmax (zmax p1 p2) (zmax p3 p4)⟩

/-- Outward-rounded fixed-point multiplication preserving `FpMem S` for `0 < S`. -/
def mulFp (S : ℤ) (a b : FpIv) : FpIv :=
  let m := mulRaw a b
  ⟨m.lo / S, (m.hi + S - 1) / S⟩

lemma zero_mem (S : ℤ) : FpMem S zero 0 := by
  simp [FpMem, zero]

lemma ofInt_mem (S z : ℤ) : FpMem S (ofInt S z) (z : ℝ) := by
  simp only [FpMem, ofInt, Int.cast_mul]
  exact ⟨le_rfl, le_rfl⟩

lemma add_mem {S : ℤ} {a b : FpIv} {x y : ℝ}
    (ha : FpMem S a x) (hb : FpMem S b y) : FpMem S (add a b) (x + y) := by
  refine ⟨?_, ?_⟩ <;> simp only [add, Int.cast_add] <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma sub_mem {S : ℤ} {a b : FpIv} {x y : ℝ}
    (ha : FpMem S a x) (hb : FpMem S b y) : FpMem S (sub a b) (x - y) := by
  refine ⟨?_, ?_⟩ <;> simp only [sub, Int.cast_sub] <;> linarith [ha.1, ha.2, hb.1, hb.2]

lemma neg_mem {S : ℤ} {a : FpIv} {x : ℝ}
    (ha : FpMem S a x) : FpMem S (neg a) (-x) := by
  refine ⟨?_, ?_⟩ <;> simp only [neg, Int.cast_neg] <;> linarith [ha.1, ha.2]

private lemma mul_mem_bounds {c y l h : ℝ} (hy : l ≤ y ∧ y ≤ h) :
    min (c * l) (c * h) ≤ c * y ∧ c * y ≤ max (c * l) (c * h) := by
  rcases le_total 0 c with hc | hc
  · exact ⟨le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_left hy.1 hc),
           le_trans (mul_le_mul_of_nonneg_left hy.2 hc) (le_max_right _ _)⟩
  · exact ⟨le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_left hy.2 hc),
           le_trans (mul_le_mul_of_nonpos_left hy.1 hc) (le_max_left _ _)⟩

lemma mulRaw_mem {a b : FpIv} {u v : ℝ}
    (hu : (a.lo : ℝ) ≤ u ∧ u ≤ (a.hi : ℝ))
    (hv : (b.lo : ℝ) ≤ v ∧ v ≤ (b.hi : ℝ)) :
    ((mulRaw a b).lo : ℝ) ≤ u * v ∧ u * v ≤ ((mulRaw a b).hi : ℝ) := by
  have hvu := mul_mem_bounds (c := v) (y := u) hu
  have hal := mul_mem_bounds (c := (a.lo : ℝ)) (y := v) hv
  have hah := mul_mem_bounds (c := (a.hi : ℝ)) (y := v) hv
  have hc1 : v * (a.lo : ℝ) = (a.lo : ℝ) * v := mul_comm _ _
  have hc2 : v * (a.hi : ℝ) = (a.hi : ℝ) * v := mul_comm _ _
  have hc3 : v * u = u * v := mul_comm _ _
  rw [hc1, hc2, hc3] at hvu
  let p1 := a.lo * b.lo
  let p2 := a.lo * b.hi
  let p3 := a.hi * b.lo
  let p4 := a.hi * b.hi
  have hp1 : ((zmin (zmin p1 p2) (zmin p3 p4) : ℤ) : ℝ) ≤ (a.lo : ℝ) * (b.lo : ℝ) := by
    exact_mod_cast le_trans (zmin_le_left _ _) (zmin_le_left _ _)
  have hp2 : ((zmin (zmin p1 p2) (zmin p3 p4) : ℤ) : ℝ) ≤ (a.lo : ℝ) * (b.hi : ℝ) := by
    exact_mod_cast le_trans (zmin_le_left _ _) (zmin_le_right _ _)
  have hp3 : ((zmin (zmin p1 p2) (zmin p3 p4) : ℤ) : ℝ) ≤ (a.hi : ℝ) * (b.lo : ℝ) := by
    exact_mod_cast le_trans (zmin_le_right _ _) (zmin_le_left _ _)
  have hp4 : ((zmin (zmin p1 p2) (zmin p3 p4) : ℤ) : ℝ) ≤ (a.hi : ℝ) * (b.hi : ℝ) := by
    exact_mod_cast le_trans (zmin_le_right _ _) (zmin_le_right _ _)
  have hq1 : (a.lo : ℝ) * (b.lo : ℝ) ≤ ((zmax (zmax p1 p2) (zmax p3 p4) : ℤ) : ℝ) := by
    exact_mod_cast le_trans (le_zmax_left _ _) (le_zmax_left _ _)
  have hq2 : (a.lo : ℝ) * (b.hi : ℝ) ≤ ((zmax (zmax p1 p2) (zmax p3 p4) : ℤ) : ℝ) := by
    exact_mod_cast le_trans (le_zmax_right _ _) (le_zmax_left _ _)
  have hq3 : (a.hi : ℝ) * (b.lo : ℝ) ≤ ((zmax (zmax p1 p2) (zmax p3 p4) : ℤ) : ℝ) := by
    exact_mod_cast le_trans (le_zmax_left _ _) (le_zmax_right _ _)
  have hq4 : (a.hi : ℝ) * (b.hi : ℝ) ≤ ((zmax (zmax p1 p2) (zmax p3 p4) : ℤ) : ℝ) := by
    exact_mod_cast le_trans (le_zmax_right _ _) (le_zmax_right _ _)
  refine ⟨?_, ?_⟩
  · exact le_trans (le_min (le_trans (le_min hp1 hp2) hal.1) (le_trans (le_min hp3 hp4) hah.1)) hvu.1
  · exact le_trans hvu.2 (max_le (le_trans hal.2 (max_le hq1 hq2)) (le_trans hah.2 (max_le hq3 hq4)))

lemma ediv_floor_mul_le (S z : ℤ) (hS : 0 < S) : S * (z / S) ≤ z := by
  have hmod : 0 ≤ z % S := Int.emod_nonneg z hS.ne'
  have hid := Int.mul_ediv_add_emod z S
  omega

lemma le_ediv_ceil_mul (S z : ℤ) (hS : 0 < S) : z ≤ S * ((z + S - 1) / S) := by
  have hlt : (z + S - 1) % S < S := Int.emod_lt_of_pos (z + S - 1) hS
  have hid := Int.mul_ediv_add_emod (z + S - 1) S
  omega

lemma mulFp_mem {S : ℤ} (hS : 0 < S) {a b : FpIv} {x y : ℝ}
    (ha : FpMem S a x) (hb : FpMem S b y) : FpMem S (mulFp S a b) (x * y) := by
  have hraw := mulRaw_mem ha hb
  have hSR : (0 : ℝ) < (S : ℝ) := by exact_mod_cast hS
  have hprod : ((S : ℝ) * x) * ((S : ℝ) * y) = (S : ℝ) * ((S : ℝ) * (x * y)) := by ring
  rw [hprod] at hraw
  have hloZ : ((S : ℝ) * (((mulRaw a b).lo / S : ℤ) : ℝ)) ≤ ((mulRaw a b).lo : ℝ) := by
    exact_mod_cast ediv_floor_mul_le S (mulRaw a b).lo hS
  have hhiZ : ((mulRaw a b).hi : ℝ) ≤ (S : ℝ) * ((((mulRaw a b).hi + S - 1) / S : ℤ) : ℝ) := by
    exact_mod_cast le_ediv_ceil_mul S (mulRaw a b).hi hS
  refine ⟨?_, ?_⟩
  · have h1 : (S : ℝ) * (((mulRaw a b).lo / S : ℤ) : ℝ) ≤ (S : ℝ) * ((S : ℝ) * (x * y)) :=
      le_trans hloZ hraw.1
    exact le_of_mul_le_mul_left h1 hSR
  · have h2 : (S : ℝ) * ((S : ℝ) * (x * y)) ≤ (S : ℝ) * ((((mulRaw a b).hi + S - 1) / S : ℤ) : ℝ) :=
      le_trans hraw.2 hhiZ
    exact le_of_mul_le_mul_left h2 hSR

/-- Encloses `dx / (dz + √(dx² + dz²))` at scale `S`, given `0 < dz`, `0 < S`, and
`0 ≤ rhoLo` with `rhoLo² ≤ S² * (dx² + dz²) ≤ (rhoLo + 1)²`. -/
def slopeIv (S dx dz rhoLo : ℤ) : FpIv :=
  let denLo := S * dz + rhoLo
  let denHi := S * dz + rhoLo + 1
  if 0 ≤ dx then
    ⟨(S * S * dx) / denHi, (S * S * dx + denLo - 1) / denLo⟩
  else
    ⟨-((S * S * (-dx) + denLo - 1) / denLo), -((S * S * (-dx)) / denHi)⟩

lemma slopeIv_mem {S dx dz rhoLo : ℤ} (hS : 0 < S) (hdz : 0 < dz)
    (hrho : 0 ≤ rhoLo ∧ rhoLo * rhoLo ≤ S * S * (dx * dx + dz * dz) ∧
      S * S * (dx * dx + dz * dz) ≤ (rhoLo + 1) * (rhoLo + 1)) :
    FpMem S (slopeIv S dx dz rhoLo)
      ((dx : ℝ) / ((dz : ℝ) + Real.sqrt ((dx : ℝ) ^ 2 + (dz : ℝ) ^ 2))) := by
  set r : ℝ := Real.sqrt ((dx : ℝ) ^ 2 + (dz : ℝ) ^ 2)
  have hSR : (0 : ℝ) < (S : ℝ) := by exact_mod_cast hS
  have hdzR : (0 : ℝ) < (dz : ℝ) := by exact_mod_cast hdz
  have hr_nonneg : 0 ≤ r := Real.sqrt_nonneg _
  have hr_sq : r ^ 2 = (dx : ℝ) ^ 2 + (dz : ℝ) ^ 2 := by
    dsimp [r]; exact Real.sq_sqrt (by positivity)
  have hSr_sq : ((S : ℝ) * r) ^ 2 = ((S : ℝ) ^ 2) * ((dx : ℝ) ^ 2 + (dz : ℝ) ^ 2) := by
    rw [mul_pow, hr_sq]
  have hloR : (rhoLo : ℝ) ≤ (S : ℝ) * r := by
    have hsq : (rhoLo : ℝ) ^ 2 ≤ ((S : ℝ) * r) ^ 2 := by
      rw [hSr_sq]; exact_mod_cast by nlinarith [hrho.2.1]
    have hrho_nn : (0 : ℝ) ≤ (rhoLo : ℝ) := by exact_mod_cast hrho.1
    nlinarith [mul_nonneg hSR.le hr_nonneg]
  have hhiR : (S : ℝ) * r ≤ ((rhoLo + 1 : ℤ) : ℝ) := by
    have hsq : ((S : ℝ) * r) ^ 2 ≤ ((rhoLo + 1 : ℤ) : ℝ) ^ 2 := by
      rw [hSr_sq]; exact_mod_cast by nlinarith [hrho.2.2]
    have hp_nn : (0 : ℝ) ≤ ((rhoLo + 1 : ℤ) : ℝ) := by exact_mod_cast (by omega : 0 ≤ rhoLo + 1)
    nlinarith [mul_nonneg hSR.le hr_nonneg]
  set denLo : ℤ := S * dz + rhoLo
  set denHi : ℤ := S * dz + rhoLo + 1
  have hdenLo_pos : 0 < denLo := by
    have : 0 < S * dz := mul_pos hS hdz
    omega
  have hdenHi_pos : 0 < denHi := by omega
  have hdenLo_R : (0 : ℝ) < (denLo : ℝ) := by exact_mod_cast hdenLo_pos
  have hdenHi_R : (0 : ℝ) < (denHi : ℝ) := by exact_mod_cast hdenHi_pos
  have hden_bounds : (denLo : ℝ) ≤ (S : ℝ) * ((dz : ℝ) + r) ∧
      (S : ℝ) * ((dz : ℝ) + r) ≤ (denHi : ℝ) := by
    have hlo' : (denLo : ℝ) ≤ (S : ℝ) * (dz : ℝ) + (S : ℝ) * r := by
      simp only [denLo, Int.cast_add, Int.cast_mul]; linarith
    have hhi' : (S : ℝ) * (dz : ℝ) + (S : ℝ) * r ≤ (denHi : ℝ) := by
      simp only [denHi, Int.cast_add, Int.cast_mul, Int.cast_one]
      have : (rhoLo : ℝ) + 1 = ((rhoLo + 1 : ℤ) : ℝ) := by push_cast; ring
      linarith
    exact ⟨by linarith, by linarith⟩
  have hSden_pos : (0 : ℝ) < (S : ℝ) * ((dz : ℝ) + r) := lt_of_lt_of_le hdenLo_R hden_bounds.1
  have hdz_r_pos : 0 < (dz : ℝ) + r := by linarith
  have hfrac : (S : ℝ) * ((dx : ℝ) / ((dz : ℝ) + r)) =
      ((S * S * dx : ℤ) : ℝ) / ((S : ℝ) * ((dz : ℝ) + r)) := by
    push_cast; field_simp [hSR.ne', hdz_r_pos.ne']
  unfold FpMem slopeIv
  split_ifs with hdx
  · have hdxR : (0 : ℝ) ≤ (dx : ℝ) := by exact_mod_cast hdx
    have hnum_nn : (0 : ℝ) ≤ ((S * S * dx : ℤ) : ℝ) := by
      push_cast; positivity
    have hlo_ediv : (denHi : ℝ) * (((S * S * dx) / denHi : ℤ) : ℝ) ≤ ((S * S * dx : ℤ) : ℝ) := by
      exact_mod_cast ediv_floor_mul_le denHi (S * S * dx) hdenHi_pos
    have hhi_ediv : ((S * S * dx : ℤ) : ℝ) ≤
        (denLo : ℝ) * ((((S * S * dx + denLo - 1) / denLo : ℤ) : ℝ)) := by
      exact_mod_cast le_ediv_ceil_mul denLo (S * S * dx) hdenLo_pos
    refine ⟨?_, ?_⟩
    · rw [hfrac, le_div_iff₀ hSden_pos]
      have hq_nn : (0 : ℝ) ≤ (((S * S * dx) / denHi : ℤ) : ℝ) := by
        exact_mod_cast Int.ediv_nonneg (mul_nonneg (mul_nonneg hS.le hS.le) hdx) hdenHi_pos.le
      nlinarith [hden_bounds.2, hlo_ediv]
    · rw [hfrac, div_le_iff₀ hSden_pos]
      have hq_nn : (0 : ℝ) ≤ ((((S * S * dx + denLo - 1) / denLo : ℤ) : ℝ)) := by
        exact_mod_cast Int.ediv_nonneg (by
          have : 0 ≤ S * S * dx := mul_nonneg (mul_nonneg hS.le hS.le) hdx
          omega) hdenLo_pos.le
      nlinarith [hden_bounds.1, hhi_ediv]
  · have hdx_neg : 0 < -dx := by omega
    have hfrac_neg : -((S : ℝ) * ((dx : ℝ) / ((dz : ℝ) + r))) =
        ((S * S * (-dx) : ℤ) : ℝ) / ((S : ℝ) * ((dz : ℝ) + r)) := by
      push_cast; field_simp [hSR.ne', hdz_r_pos.ne']
    have hlo_ediv : (denHi : ℝ) * (((S * S * (-dx)) / denHi : ℤ) : ℝ) ≤ ((S * S * (-dx) : ℤ) : ℝ) := by
      exact_mod_cast ediv_floor_mul_le denHi (S * S * (-dx)) hdenHi_pos
    have hhi_ediv : ((S * S * (-dx) : ℤ) : ℝ) ≤
        (denLo : ℝ) * ((((S * S * (-dx) + denLo - 1) / denLo : ℤ) : ℝ)) := by
      exact_mod_cast le_ediv_ceil_mul denLo (S * S * (-dx)) hdenLo_pos
    refine ⟨?_, ?_⟩
    · simp only [Int.cast_neg]
      have hle : -((S : ℝ) * ((dx : ℝ) / ((dz : ℝ) + r))) ≤
          ((((S * S * (-dx) + denLo - 1) / denLo : ℤ) : ℝ)) := by
        rw [hfrac_neg, div_le_iff₀ hSden_pos]
        have hq_nn : (0 : ℝ) ≤ ((((S * S * (-dx) + denLo - 1) / denLo : ℤ) : ℝ)) := by
          exact_mod_cast Int.ediv_nonneg (by
            have : 0 ≤ S * S * (-dx) := mul_nonneg (mul_nonneg hS.le hS.le) hdx_neg.le
            omega) hdenLo_pos.le
        nlinarith [hden_bounds.1, hhi_ediv]
      linarith
    · simp only [Int.cast_neg]
      have hge : (((S * S * (-dx)) / denHi : ℤ) : ℝ) ≤
          -((S : ℝ) * ((dx : ℝ) / ((dz : ℝ) + r))) := by
        rw [hfrac_neg, le_div_iff₀ hSden_pos]
        have hq_nn : (0 : ℝ) ≤ (((S * S * (-dx)) / denHi : ℤ) : ℝ) := by
          exact_mod_cast Int.ediv_nonneg (mul_nonneg (mul_nonneg hS.le hS.le) hdx_neg.le) hdenHi_pos.le
        nlinarith [hden_bounds.2, hlo_ediv]
      linarith

end FpIv

end FixedPointIntervals

/-! ## Part 2: Literal Atiyah–Sutcliffe Definitions, Invariance, and Planar Reduction -/

section AtiyahDefinitions

/-- Ordered configuration space $C_n(\mathbb{R}^3)$ of pairwise distinct points. -/
def DistinctPoints (n : ℕ) : Type :=
  { x : Fin n → Fin 3 → ℝ // ∀ i j : Fin n, i ≠ j → x i ≠ x j }

/-- Atiyah polynomial $P_i(T) = \prod_{j \neq i} (\psi_{ij,0} + \psi_{ij,1} T)$ of degree `< n`. -/
noncomputable def atiyahPoly {n : ℕ} (ψ : Fin n → Fin n → Fin 2 → ℂ) (i : Fin n) : Polynomial ℂ :=
  ∏ j ∈ Finset.univ.erase i, (Polynomial.C (ψ i j 0) + Polynomial.C (ψ i j 1) * Polynomial.X)

/-- Coefficient matrix $M(\psi)$ whose row `i` stores the `T^k` coefficients of `atiyahPoly ψ i`. -/
noncomputable def atiyahMat {n : ℕ} (ψ : Fin n → Fin n → Fin 2 → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i k => (atiyahPoly ψ i).coeff k

/-- Edge-pair skew denominator $\prod_{i < j} \omega(\psi_{ij}, \psi_{ji})$. -/
def atiyahDen {n : ℕ} (ψ : Fin n → Fin n → Fin 2 → ℂ) : ℂ :=
  ∏ e : { p : Fin n × Fin n // p.1 < p.2 }, omega (ψ e.1.1 e.1.2) (ψ e.1.2 e.1.1)

/-- Normalized Atiyah–Sutcliffe determinant for an arbitrary spinor lift `ψ`. -/
noncomputable def atiyahDetOfSpinors {n : ℕ} (ψ : Fin n → Fin n → Fin 2 → ℂ) : ℂ :=
  (atiyahMat ψ).det / atiyahDen ψ

/-- Canonical normalized Atiyah–Sutcliffe determinant $D_n(\mathbf{x})$ on $C_n(\mathbb{R}^3)$. -/
noncomputable def atiyahDet {n : ℕ} (x : DistinctPoints n) : ℂ :=
  atiyahDetOfSpinors (fun i j => canonicalSpinor (unitDir (x.1 i) (x.1 j)))

/-- **Atiyah Conjecture 1 (Linear Independence):** the $n$ Atiyah polynomials are linearly independent. -/
def AtiyahConjecture1Prop : Prop :=
  ∀ (n : ℕ) (_ : 2 ≤ n) (x : DistinctPoints n),
    LinearIndependent ℂ (fun i : Fin n =>
      atiyahPoly (fun u v => canonicalSpinor (unitDir (x.1 u) (x.1 v))) i)

/-- **Atiyah Conjecture 1 (Determinant Form):** $D_n(\mathbf{x}) \neq 0$. -/
def AtiyahDetNonzeroProp : Prop :=
  ∀ (n : ℕ) (_ : 2 ≤ n) (x : DistinctPoints n), atiyahDet x ≠ 0

/-- **Atiyah–Sutcliffe Conjecture 2:** $|D_n(\mathbf{x})| \ge 1$. -/
def AtiyahSutcliffeConjecture2Prop : Prop :=
  ∀ (n : ℕ) (_ : 2 ≤ n) (x : DistinctPoints n), 1 ≤ ‖atiyahDet x‖

/-- Deleting vertex `k` from a distinct-point configuration yields a distinct `(n - 1)`-point configuration. -/
def deletePoint {n : ℕ} (x : DistinctPoints (n + 1)) (k : Fin (n + 1)) : DistinctPoints n :=
  ⟨fun i => x.1 (k.succAbove i),
    fun i j hij => x.2 (k.succAbove i) (k.succAbove j) ((Fin.succAbove_right_injective).ne hij)⟩

/-- **Atiyah–Sutcliffe Conjecture 3:** $|D_n(\mathbf{x})|^{n-2} \ge \prod_{k=0}^{n-1} |D_{n-1}(\mathbf{x}\setminus\{x_k\})|$. -/
def AtiyahSutcliffeConjecture3Prop : Prop :=
  ∀ (m : ℕ) (_ : 2 ≤ m) (x : DistinctPoints (m + 1)),
    (∏ k : Fin (m + 1), ‖atiyahDet (deletePoint x k)‖) ≤ ‖atiyahDet x‖ ^ (m - 1)

private def ltSumEquiv (n : ℕ) :
    { p : Fin n × Fin n // p.1 < p.2 } ⊕ { p : Fin n × Fin n // p.1 < p.2 } ≃
      { p : Fin n × Fin n // p.1 ≠ p.2 } where
  toFun
    | .inl e => ⟨e.1, ne_of_lt e.2⟩
    | .inr e => ⟨(e.1.2, e.1.1), ne_of_gt e.2⟩
  invFun p :=
    if h : p.1.1 < p.1.2 then .inl ⟨p.1, h⟩
    else .inr ⟨(p.1.2, p.1.1), lt_of_le_of_ne (not_lt.mp h) p.2.symm⟩
  left_inv x := by
    cases x with
    | inl e => simp [e.2]
    | inr e => simp [not_lt.mpr e.2.le]
  right_inv p := by
    by_cases h : p.1.1 < p.1.2 <;> simp [h]

private def offDiagEquiv (n : ℕ) :
    { p : Fin n × Fin n // p.1 ≠ p.2 } ≃ Σ i : Fin n, { j : Fin n // j ∈ Finset.univ.erase i } where
  toFun p := ⟨p.1.1, ⟨p.1.2, Finset.mem_erase.mpr ⟨p.2.symm, Finset.mem_univ _⟩⟩⟩
  invFun q := ⟨(q.1, q.2.1), (Finset.mem_erase.mp q.2.2).1.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Any nonzero $+1$-eigenvector of `pauliDot v` is a nonzero scalar multiple of `canonicalSpinor v`. -/
lemma mulVec_eq_self_collinear {v : Fin 3 → ℝ} (hv : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1)
    {ψ : Fin 2 → ℂ} (hψ_ne : ψ 0 ≠ 0 ∨ ψ 1 ≠ 0) (hψ_mul : (pauliDot v).mulVec ψ = ψ) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ k, ψ k = c * canonicalSpinor v k := by
  have hcan := isPosSpinor_canonicalSpinor hv
  have hom := omega_eq_zero_of_mulVec hcan.2 hψ_mul
  have hcan_nz : canonicalSpinor v 0 ≠ 0 ∨ canonicalSpinor v 1 ≠ 0 := by
    by_contra h
    push Not at h
    have hn := hcan.1
    rw [h.1, h.2] at hn
    norm_num at hn
  have heq : canonicalSpinor v 0 * ψ 1 = canonicalSpinor v 1 * ψ 0 := sub_eq_zero.mp hom
  rcases hcan_nz with h0 | h1
  · refine ⟨ψ 0 / canonicalSpinor v 0, ?_, ?_⟩
    · intro hc
      have hψ0 : ψ 0 = 0 := (div_eq_zero_iff.mp hc).resolve_right h0
      rw [hψ0, mul_zero] at heq
      have hψ1 : ψ 1 = 0 := (mul_eq_zero.mp heq).resolve_left h0
      rcases hψ_ne with h' | h'
      · exact h' hψ0
      · exact h' hψ1
    · intro k; fin_cases k <;> dsimp
      · field_simp [h0]
      · field_simp [h0]; linear_combination heq
  · refine ⟨ψ 1 / canonicalSpinor v 1, ?_, ?_⟩
    · intro hc
      have hψ1 : ψ 1 = 0 := (div_eq_zero_iff.mp hc).resolve_right h1
      rw [hψ1, mul_zero] at heq
      have hψ0 : ψ 0 = 0 := (mul_eq_zero.mp heq.symm).resolve_left h1
      rcases hψ_ne with h' | h'
      · exact h' hψ0
      · exact h' hψ1
    · intro k; fin_cases k <;> dsimp
      · field_simp [h1]; linear_combination -heq
      · field_simp [h1]

/-- Scale & phase invariance of `atiyahDet`: any valid family of nonzero $+1$-spinors computes `atiyahDet x`. -/
theorem atiyahDet_eq_of_posSpinors {n : ℕ} (x : DistinctPoints n)
    (ψ : Fin n → Fin n → Fin 2 → ℂ)
    (hψ_ne : ∀ i j, i ≠ j → ψ i j 0 ≠ 0 ∨ ψ i j 1 ≠ 0)
    (hψ_mul : ∀ i j, i ≠ j → (pauliDot (unitDir (x.1 i) (x.1 j))).mulVec (ψ i j) = ψ i j) :
    atiyahDet x = atiyahDetOfSpinors ψ := by
  let ψ0 := fun i j => canonicalSpinor (unitDir (x.1 i) (x.1 j))
  have hcol : ∀ i j, i ≠ j → ∃ c : ℂ, c ≠ 0 ∧ ∀ k, ψ i j k = c * ψ0 i j k := fun i j hij =>
    mulVec_eq_self_collinear (unitDir_norm_sq (x.2 i j hij)) (hψ_ne i j hij) (hψ_mul i j hij)
  choose c hc_ne hc_eq using fun (p : { p : Fin n × Fin n // p.1 ≠ p.2 }) => hcol p.1.1 p.1.2 p.2
  let cFull : Fin n → Fin n → ℂ := fun i j => if h : i ≠ j then c ⟨(i, j), h⟩ else 1
  have hcFull_ne : ∀ i j, i ≠ j → cFull i j ≠ 0 := by
    intro i j hij; dsimp only [cFull]; split_ifs; exact hc_ne ⟨(i, j), hij⟩
  have hcFull_eq : ∀ i j, i ≠ j → ∀ k, ψ i j k = cFull i j * ψ0 i j k := by
    intro i j hij k; dsimp only [cFull]; split_ifs; exact hc_eq ⟨(i, j), hij⟩ k
  have hpoly : ∀ i, atiyahPoly ψ i =
      Polynomial.C (∏ j ∈ Finset.univ.erase i, cFull i j) * atiyahPoly ψ0 i := by
    intro i
    simp only [atiyahPoly]
    calc
      ∏ j ∈ Finset.univ.erase i, (Polynomial.C (ψ i j 0) + Polynomial.C (ψ i j 1) * Polynomial.X)
        = ∏ j ∈ Finset.univ.erase i,
            (Polynomial.C (cFull i j) * (Polynomial.C (ψ0 i j 0) + Polynomial.C (ψ0 i j 1) * Polynomial.X)) := by
          refine Finset.prod_congr rfl fun j hj => ?_
          have hij : i ≠ j := (Finset.mem_erase.mp hj).1.symm
          rw [hcFull_eq i j hij 0, hcFull_eq i j hij 1]
          simp only [Polynomial.C_mul]; ring
      _ = (∏ j ∈ Finset.univ.erase i, Polynomial.C (cFull i j)) *
            ∏ j ∈ Finset.univ.erase i, (Polynomial.C (ψ0 i j 0) + Polynomial.C (ψ0 i j 1) * Polynomial.X) :=
          Finset.prod_mul_distrib
      _ = Polynomial.C (∏ j ∈ Finset.univ.erase i, cFull i j) * atiyahPoly ψ0 i := by
          rw [← map_prod Polynomial.C (fun j => cFull i j)]; rfl
  have hmat : atiyahMat ψ = Matrix.of (fun i k =>
      (∏ j ∈ Finset.univ.erase i, cFull i j) * atiyahMat ψ0 i k) := by
    ext i k
    simp only [atiyahMat, Matrix.of_apply, hpoly i, Polynomial.coeff_C_mul]
  have hdet : (atiyahMat ψ).det =
      (∏ i : Fin n, ∏ j ∈ Finset.univ.erase i, cFull i j) * (atiyahMat ψ0).det := by
    rw [hmat, Matrix.det_mul_column]
  have hden : atiyahDen ψ =
      (∏ e : { p : Fin n × Fin n // p.1 < p.2 }, cFull e.1.1 e.1.2 * cFull e.1.2 e.1.1) *
        atiyahDen ψ0 := by
    simp only [atiyahDen]
    calc
      ∏ e : { p : Fin n × Fin n // p.1 < p.2 }, omega (ψ e.1.1 e.1.2) (ψ e.1.2 e.1.1)
        = ∏ e : { p : Fin n × Fin n // p.1 < p.2 },
            ((cFull e.1.1 e.1.2 * cFull e.1.2 e.1.1) * omega (ψ0 e.1.1 e.1.2) (ψ0 e.1.2 e.1.1)) := by
          refine Finset.prod_congr rfl fun e _ => ?_
          have hlt := e.2
          have h0 : ψ e.1.1 e.1.2 = fun k => cFull e.1.1 e.1.2 * ψ0 e.1.1 e.1.2 k :=
            funext (hcFull_eq e.1.1 e.1.2 (ne_of_lt hlt))
          have h1 : ψ e.1.2 e.1.1 = fun k => cFull e.1.2 e.1.1 * ψ0 e.1.2 e.1.1 k :=
            funext (hcFull_eq e.1.2 e.1.1 (ne_of_gt hlt))
          rw [h0, h1, omega_smul]
      _ = (∏ e : { p : Fin n × Fin n // p.1 < p.2 }, cFull e.1.1 e.1.2 * cFull e.1.2 e.1.1) *
            ∏ e : { p : Fin n × Fin n // p.1 < p.2 }, omega (ψ0 e.1.1 e.1.2) (ψ0 e.1.2 e.1.1) :=
          Finset.prod_mul_distrib
  have hprod_eq :
      (∏ i : Fin n, ∏ j ∈ Finset.univ.erase i, cFull i j) =
        ∏ e : { p : Fin n × Fin n // p.1 < p.2 }, cFull e.1.1 e.1.2 * cFull e.1.2 e.1.1 := by
    have hsigma :
        (∏ i : Fin n, ∏ j ∈ Finset.univ.erase i, cFull i j) =
          ∏ q : (Σ i : Fin n, { j : Fin n // j ∈ Finset.univ.erase i }), cFull q.1 q.2.1 := by
      rw [Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun i _ => ?_
      exact (Finset.prod_coe_sort (Finset.univ.erase i) (fun j => cFull i j)).symm
    calc
      (∏ i : Fin n, ∏ j ∈ Finset.univ.erase i, cFull i j)
        = ∏ q : (Σ i : Fin n, { j : Fin n // j ∈ Finset.univ.erase i }), cFull q.1 q.2.1 := hsigma
      _ = ∏ p : { p : Fin n × Fin n // p.1 ≠ p.2 }, cFull p.1.1 p.1.2 :=
          Fintype.prod_equiv (offDiagEquiv n).symm _ _ fun _ => rfl
      _ = ∏ s : { p : Fin n × Fin n // p.1 < p.2 } ⊕ { p : Fin n × Fin n // p.1 < p.2 },
            cFull (ltSumEquiv n s).1.1 (ltSumEquiv n s).1.2 :=
          (Fintype.prod_equiv (ltSumEquiv n) _ _ fun _ => rfl).symm
      _ = (∏ e : { p : Fin n × Fin n // p.1 < p.2 }, cFull e.1.1 e.1.2) *
            (∏ e : { p : Fin n × Fin n // p.1 < p.2 }, cFull e.1.2 e.1.1) := by
          simp only [Fintype.prod_sum_type, ltSumEquiv]; rfl
      _ = ∏ e : { p : Fin n × Fin n // p.1 < p.2 }, cFull e.1.1 e.1.2 * cFull e.1.2 e.1.1 :=
          Finset.prod_mul_distrib.symm
  have hS_ne : (∏ e : { p : Fin n × Fin n // p.1 < p.2 }, cFull e.1.1 e.1.2 * cFull e.1.2 e.1.1) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun e _ => mul_ne_zero
      (hcFull_ne _ _ (ne_of_lt e.2)) (hcFull_ne _ _ (ne_of_gt e.2))
  have hden0_ne : atiyahDen ψ0 ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun e _ => ?_
    have hij := x.2 e.1.1 e.1.2 (ne_of_lt e.2)
    have hpos1 : IsPosSpinor (unitDir (x.1 e.1.1) (x.1 e.1.2)) (ψ0 e.1.1 e.1.2) :=
      isPosSpinor_canonicalSpinor (unitDir_norm_sq hij)
    have hpos2 : IsPosSpinor (fun k => -unitDir (x.1 e.1.1) (x.1 e.1.2) k) (ψ0 e.1.2 e.1.1) := by
      rw [← unitDir_swap]
      exact isPosSpinor_canonicalSpinor (unitDir_norm_sq hij.symm)
    exact omega_opp_ne_zero hpos1 hpos2
  change atiyahDetOfSpinors ψ0 = atiyahDetOfSpinors ψ
  simp only [atiyahDetOfSpinors, hdet, hden, hprod_eq]
  field_simp [hS_ne, hden0_ne]

lemma atiyahDet_den_ne_zero {n : ℕ} (x : DistinctPoints n) :
    atiyahDen (fun i j => canonicalSpinor (unitDir (x.1 i) (x.1 j))) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun e _ => ?_
  have hij := x.2 e.1.1 e.1.2 (ne_of_lt e.2)
  have hpos1 := isPosSpinor_canonicalSpinor (unitDir_norm_sq hij)
  have hpos2 : IsPosSpinor (fun k => -unitDir (x.1 e.1.1) (x.1 e.1.2) k)
      (canonicalSpinor (unitDir (x.1 e.1.2) (x.1 e.1.1))) := by
    rw [← unitDir_swap]; exact isPosSpinor_canonicalSpinor (unitDir_norm_sq hij.symm)
  exact omega_opp_ne_zero hpos1 hpos2

private lemma natDegree_atiyahPoly_le {n : ℕ} (_hn : 1 ≤ n) (ψ : Fin n → Fin n → Fin 2 → ℂ)
    (i : Fin n) : (atiyahPoly ψ i).natDegree ≤ n - 1 := by
  have hcard : (Finset.univ.erase i).card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_fin]
  unfold atiyahPoly
  calc
    (∏ j ∈ Finset.univ.erase i, (Polynomial.C (ψ i j 0) + Polynomial.C (ψ i j 1) * Polynomial.X)).natDegree
      ≤ ∑ j ∈ Finset.univ.erase i, (Polynomial.C (ψ i j 0) + Polynomial.C (ψ i j 1) * Polynomial.X).natDegree :=
        Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _j ∈ Finset.univ.erase i, 1 := by
        refine Finset.sum_le_sum fun j _ => ?_
        compute_degree!
    _ = n - 1 := by simp [hcard]

/-- Vanishing of `atiyahDet x` implies linear dependence of the $n$ Atiyah polynomials. -/
theorem not_linearIndependent_of_atiyahDet_eq_zero {n : ℕ} (hn : 1 ≤ n) (x : DistinctPoints n)
    (h0 : atiyahDet x = 0) :
    ¬ LinearIndependent ℂ (fun i : Fin n =>
      atiyahPoly (fun u v => canonicalSpinor (unitDir (x.1 u) (x.1 v))) i) := by
  let ψ := fun u v => canonicalSpinor (unitDir (x.1 u) (x.1 v))
  have hden := atiyahDet_den_ne_zero x
  have hdet : (atiyahMat ψ).det = 0 := (div_eq_zero_iff.mp h0).resolve_right hden
  have hdetT : (atiyahMat ψ)ᵀ.det = 0 := by rw [Matrix.det_transpose]; exact hdet
  obtain ⟨w, hw_ne, hmul⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetT
  intro hlin
  have hsum : ∑ i : Fin n, w i • atiyahPoly ψ i = 0 := by
    ext k
    change (Polynomial.lcoeff ℂ k) (∑ i : Fin n, w i • atiyahPoly ψ i) = 0
    rw [map_sum]
    simp only [map_smul, Polynomial.lcoeff_apply, smul_eq_mul]
    by_cases hk : k < n
    · have hk' := congr_fun hmul ⟨k, hk⟩
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply] at hk'
      rw [← hk']
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [atiyahMat, mul_comm]
    · have hkge : n - 1 < k := by omega
      refine Finset.sum_eq_zero fun i _ => ?_
      have hdeg : (atiyahPoly ψ i).natDegree < k := lt_of_le_of_lt (natDegree_atiyahPoly_le hn ψ i) hkge
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hdeg, mul_zero]
  have hw0 := (Fintype.linearIndependent_iff.mp hlin) w hsum
  apply hw_ne
  ext i
  exact hw0 i

end AtiyahDefinitions

/-! ## Part 3: Smooth Ordered-Height Planar Formula ($y_i = 0$, $z_0 < \dots < z_{n-1}$) -/

section PlanarOrderedReduction

/-- Pairwise planar half-angle slope $c_{ij} = \frac{x_j - x_i}{(z_j - z_i) + \sqrt{(x_j - x_i)^2 + (z_j - z_i)^2}}$. -/
noncomputable def planarSlope {n : ℕ} (p : Fin n → Fin 3 → ℝ) (i j : Fin n) : ℝ :=
  (p j 0 - p i 0) / ((p j 2 - p i 2) + euclidNorm (fun c => p j c - p i c))

/-- Real unnormalized $+1$-spinor pair for ordered-height planar configurations (`y = 0`, `z` strictly increasing):
for `i < j`, `(1, c_{ij})`; for `j < i`, `(-c_{ji}, 1)`. -/
noncomputable def planarOrderedSpinor {n : ℕ} (p : Fin n → Fin 3 → ℝ) (i j : Fin n) : Fin 2 → ℂ :=
  if i < j then ![1, (planarSlope p i j : ℂ)]
  else if j < i then ![(-(planarSlope p j i : ℂ)), 1]
  else ![1, 0]

private lemma pauliDot_planarOrdered_pos {a b : Fin 3 → ℝ}
    (ha1 : a 1 = 0) (hb1 : b 1 = 0) (hz : a 2 < b 2) :
    let dx := b 0 - a 0
    let dz := b 2 - a 2
    let r := euclidNorm (fun c => b c - a c)
    let c := dx / (dz + r)
    0 < dz + r ∧ (pauliDot (unitDir a b)).mulVec ![1, (c : ℂ)] = ![1, (c : ℂ)] := by
  intro dx dz r c
  have hdz_pos : 0 < dz := sub_pos.mpr hz
  have hr_nonneg : 0 ≤ r := Real.sqrt_nonneg _
  have hden_pos : 0 < dz + r := by linarith
  have hne : a ≠ b := fun h => by subst h; exact lt_irrefl _ hz
  have hr_pos : 0 < r := euclidNorm_pos_of_ne hne
  have hr_sq : r ^ 2 = dx ^ 2 + dz ^ 2 := by
    dsimp [r, euclidNorm, dx, dz]
    rw [Real.sq_sqrt (by positivity), ha1, hb1]
    ring
  have hquad : c * (dz + r) = dx := div_mul_cancel₀ dx hden_pos.ne'
  have hc_ident : (1 - c ^ 2) * r = (1 + c ^ 2) * dz := by
    have h1 : (dz + r) ^ 2 * c ^ 2 = dx ^ 2 := by
      calc (dz + r) ^ 2 * c ^ 2 = (c * (dz + r)) ^ 2 := by ring
      _ = dx ^ 2 := by rw [hquad]
    have h2 : dx ^ 2 = r ^ 2 - dz ^ 2 := by linarith [hr_sq]
    have h3 : (dz + r) * ((dz + r) * c ^ 2 - (r - dz)) = 0 := by
      calc (dz + r) * ((dz + r) * c ^ 2 - (r - dz)) = (dz + r) ^ 2 * c ^ 2 - (r ^ 2 - dz ^ 2) := by ring
      _ = 0 := by rw [h1, h2, sub_self]
    have h4 : (dz + r) * c ^ 2 - (r - dz) = 0 := (mul_eq_zero.mp h3).resolve_left hden_pos.ne'
    linarith
  have hrow0 : dz / r + (dx / r) * c = 1 := by
    have hnum : dz + dx * c = r := by
      have h5 : (dz + r) * (dz + dx * c - r) = 0 := by
        have : dx * c = c ^ 2 * (dz + r) := by
          calc dx * c = (c * (dz + r)) * c := by rw [hquad]
          _ = c ^ 2 * (dz + r) := by ring
        calc (dz + r) * (dz + dx * c - r)
          = (dz + r) * (dz - r) + (dz + r) * (dx * c) := by ring
        _ = (dz ^ 2 - r ^ 2) + (dz + r) ^ 2 * c ^ 2 := by rw [this]; ring
        _ = -(dx ^ 2) + dx ^ 2 := by
          have h1' : (dz + r) ^ 2 * c ^ 2 = dx ^ 2 := by
            calc (dz + r) ^ 2 * c ^ 2 = (c * (dz + r)) ^ 2 := by ring
            _ = dx ^ 2 := by rw [hquad]
          have h2' : dz ^ 2 - r ^ 2 = -(dx ^ 2) := by linarith [hr_sq]
          linarith [h1', h2']
        _ = 0 := by ring
      have h6 : dz + dx * c - r = 0 := (mul_eq_zero.mp h5).resolve_left hden_pos.ne'
      linarith
    field_simp [hr_pos.ne']
    exact hnum
  have hrow1 : dx / r - (dz / r) * c = c := by
    have hnum : dx - dz * c = r * c := by
      have h7 : dx = c * (dz + r) := hquad.symm
      linarith
    field_simp [hr_pos.ne']
    exact hnum
  have h0_mul : dz / r * 1 + dx / r * c = 1 := by linarith [hrow0]
  have h1_mul : dx / r * 1 + -(dz / r) * c = c := by linarith [hrow1]
  refine ⟨hden_pos, ?_⟩
  ext k
  have hu0 : unitDir a b 0 = dx / r := rfl
  have hu1 : unitDir a b 1 = 0 := by simp [unitDir, ha1, hb1]
  have hu2 : unitDir a b 2 = dz / r := rfl
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, pauliDot, hu0, hu1, hu2,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.ofReal_zero, mul_zero, sub_zero, add_zero]
  fin_cases k <;> dsimp
  · exact_mod_cast h0_mul
  · exact_mod_cast h1_mul

private lemma pauliDot_planarOrdered_neg {a b : Fin 3 → ℝ}
    (ha1 : a 1 = 0) (hb1 : b 1 = 0) (hz : a 2 < b 2) :
    let dx := b 0 - a 0
    let dz := b 2 - a 2
    let r := euclidNorm (fun c => b c - a c)
    let c := dx / (dz + r)
    (pauliDot (unitDir b a)).mulVec ![-(c : ℂ), 1] = ![-(c : ℂ), 1] := by
  intro dx dz r c
  obtain ⟨_, hpos⟩ := pauliDot_planarOrdered_pos ha1 hb1 hz
  have hneg : (pauliDot (unitDir b a)).mulVec ![-(c : ℂ), 1] =
      -((pauliDot (unitDir a b)).mulVec ![-(c : ℂ), 1]) := by
    rw [unitDir_swap, pauliDot_neg, Matrix.neg_mulVec]
  have hu1 : unitDir a b 1 = 0 := by simp [unitDir, ha1, hb1]
  have h0 := congr_fun hpos 0
  have h1 := congr_fun hpos 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, pauliDot, hu1,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.ofReal_zero, mul_zero, sub_zero, add_zero] at h0 h1
  rw [hneg]
  ext k
  simp only [Pi.neg_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, pauliDot, hu1,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.ofReal_zero, mul_zero, sub_zero, add_zero]
  fin_cases k <;> dsimp
  · linear_combination -h1
  · linear_combination h0

/-- Real coefficient polynomial for planar ordered-height configurations. -/
noncomputable def planarPoly {n : ℕ} (p : Fin n → Fin 3 → ℝ) (i : Fin n) : Polynomial ℝ :=
  ∏ j ∈ Finset.univ.erase i,
    if j < i then (-Polynomial.C (planarSlope p j i) + Polynomial.X)
    else (1 + Polynomial.C (planarSlope p i j) * Polynomial.X)

/-- Real $n \times n$ Atiyah coefficient matrix for ordered-height planar configurations. -/
noncomputable def planarMat {n : ℕ} (p : Fin n → Fin 3 → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i k => (planarPoly p i).coeff k

/-- Real positive denominator $\prod_{i < j} (1 + c_{ij}^2)$ for ordered-height planar configurations. -/
noncomputable def planarDen {n : ℕ} (p : Fin n → Fin 3 → ℝ) : ℝ :=
  ∏ e : { q : Fin n × Fin n // q.1 < q.2 }, (1 + planarSlope p e.1.1 e.1.2 ^ 2)

lemma planarDen_pos {n : ℕ} (p : Fin n → Fin 3 → ℝ) : 0 < planarDen p := by
  refine Finset.prod_pos fun e _ => by positivity

/-- Exact real ordered-height reduction of `atiyahDet`. -/
theorem atiyahDet_eq_planarMat_div {n : ℕ} (x : DistinctPoints n)
    (hy : ∀ i, x.1 i 1 = 0) (hz : StrictMono (fun i => x.1 i 2)) :
    atiyahDet x = (((planarMat x.1).det / planarDen x.1 : ℝ) : ℂ) := by
  let ψ := planarOrderedSpinor x.1
  have hne : ∀ i j, i ≠ j → ψ i j 0 ≠ 0 ∨ ψ i j 1 ≠ 0 := by
    intro i j hij
    rcases lt_trichotomy i j with hlt | heq | hgt
    · left; simp [ψ, planarOrderedSpinor, hlt]
    · exact absurd heq hij
    · right; simp [ψ, planarOrderedSpinor, not_lt.mpr hgt.le, hgt]
  have hmul : ∀ i j, i ≠ j → (pauliDot (unitDir (x.1 i) (x.1 j))).mulVec (ψ i j) = ψ i j := by
    intro i j hij
    rcases lt_trichotomy i j with hlt | heq | hgt
    · simp only [ψ, planarOrderedSpinor, hlt, ↓reduceIte]
      exact (pauliDot_planarOrdered_pos (hy i) (hy j) (hz hlt)).2
    · exact absurd heq hij
    · simp only [ψ, planarOrderedSpinor, not_lt.mpr hgt.le, hgt, ↓reduceIte]
      exact pauliDot_planarOrdered_neg (hy j) (hy i) (hz hgt)
  rw [atiyahDet_eq_of_posSpinors x ψ hne hmul]
  have hpoly : ∀ i, atiyahPoly ψ i = (planarPoly x.1 i).map (algebraMap ℝ ℂ) := by
    intro i
    simp only [atiyahPoly, planarPoly, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun j hj => ?_
    have hij : j ≠ i := (Finset.mem_erase.mp hj).1
    rcases lt_trichotomy j i with hji | heq | hij_lt
    · have hnot : ¬ (i < j) := not_lt.mpr hji.le
      simp only [ψ, planarOrderedSpinor, hnot, hji, ↓reduceIte, Matrix.cons_val_zero,
        Matrix.cons_val_one, Polynomial.map_add, Polynomial.map_neg, Polynomial.map_C,
        Polynomial.map_X, Polynomial.C_neg, Polynomial.C_1, Complex.coe_algebraMap]
      ring
    · exact absurd heq hij
    · simp only [ψ, planarOrderedSpinor, hij_lt, ↓reduceIte, not_lt.mpr hij_lt.le,
        Matrix.cons_val_zero, Matrix.cons_val_one, Polynomial.map_add, Polynomial.map_one,
        Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, Polynomial.C_1,
        Complex.coe_algebraMap]
  have hmat : atiyahMat ψ = (planarMat x.1).map Complex.ofRealHom := by
    ext i k
    simp only [atiyahMat, planarMat, Matrix.map_apply, hpoly i, Polynomial.coeff_map,
      Complex.coe_algebraMap]
    rfl
  have hdet : (atiyahMat ψ).det = ((planarMat x.1).det : ℂ) := by
    rw [hmat]
    exact (RingHom.map_det Complex.ofRealHom (planarMat x.1)).symm
  have hden : atiyahDen ψ = (planarDen x.1 : ℂ) := by
    simp only [atiyahDen, planarDen, Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun e _ => ?_
    have hlt := e.2
    have hnot : ¬ (e.1.2 < e.1.1) := not_lt.mpr hlt.le
    simp only [ψ, planarOrderedSpinor, hlt, hnot, ↓reduceIte, omega, Matrix.cons_val_zero,
      Matrix.cons_val_one, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_pow]
    ring
  simp only [atiyahDetOfSpinors, hdet, hden, Complex.ofReal_div]

/-- Straight-line planar homotopy $\gamma(s)_i = (s x_i, 0, z_i)$ preserving strict height ordering. -/
noncomputable def planarPath {n : ℕ} (ptsX ptsZ : Fin n → ℤ)
    (hz : StrictMono ptsZ) (s : ℝ) : DistinctPoints n :=
  ⟨fun i => ![s * (ptsX i : ℝ), 0, (ptsZ i : ℝ)], fun i j hij => by
    intro heq
    have hz_eq : (ptsZ i : ℝ) = (ptsZ j : ℝ) := congr_fun heq 2
    have hzi : ptsZ i = ptsZ j := Int.cast_injective hz_eq
    exact hij (hz.injective hzi)⟩

lemma planarPath_zero_eq_one {n : ℕ} (ptsX ptsZ : Fin n → ℤ) (hz : StrictMono ptsZ) :
    atiyahDet (planarPath ptsX ptsZ hz 0) = 1 := by
  have hy : ∀ i, (planarPath ptsX ptsZ hz 0).1 i 1 = 0 := fun _ => rfl
  have hz' : StrictMono (fun i => (planarPath ptsX ptsZ hz 0).1 i 2) :=
    fun _ _ h => Int.cast_lt.mpr (hz h)
  rw [atiyahDet_eq_planarMat_div _ hy hz']
  have hslope : ∀ i j, planarSlope (planarPath ptsX ptsZ hz 0).1 i j = 0 := by
    intro i j; simp [planarSlope, planarPath]
  have hpoly : ∀ i, planarPoly (planarPath ptsX ptsZ hz 0).1 i = Polynomial.X ^ i.val := by
    intro i
    have hprod : planarPoly (planarPath ptsX ptsZ hz 0).1 i =
        ∏ j ∈ Finset.univ.erase i, if j < i then Polynomial.X else (1 : Polynomial ℝ) := by
      refine Finset.prod_congr rfl fun j _ => ?_
      simp [hslope]
    rw [hprod]
    have hsplit : (Finset.univ.erase i).filter (· < i) = (Finset.univ : Finset (Fin n)).filter (· < i) := by
      ext j; simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true]
      exact ⟨fun h => h.2, fun h => ⟨h.ne, h⟩⟩
    calc
      (∏ j ∈ Finset.univ.erase i, if j < i then Polynomial.X else (1 : Polynomial ℝ))
        = ∏ j ∈ (Finset.univ.erase i).filter (· < i), Polynomial.X := by
          rw [← Finset.prod_filter_mul_prod_filter_not (Finset.univ.erase i) (· < i)]
          have h1 : ∏ j ∈ (Finset.univ.erase i).filter (· < i),
              (if j < i then Polynomial.X else (1 : Polynomial ℝ)) =
              ∏ _j ∈ (Finset.univ.erase i).filter (· < i), Polynomial.X :=
            Finset.prod_congr rfl fun j hj => by
              have hlt := (Finset.mem_filter.mp hj).2
              simp [hlt]
          have h2 : ∏ j ∈ (Finset.univ.erase i).filter (fun j => ¬ j < i),
              (if j < i then Polynomial.X else (1 : Polynomial ℝ)) = 1 :=
            Finset.prod_eq_one fun j hj => by
              have hnot := (Finset.mem_filter.mp hj).2
              simp [hnot]
          rw [h1, h2, mul_one]
      _ = ∏ _j ∈ (Finset.univ : Finset (Fin n)).filter (· < i), Polynomial.X := by rw [hsplit]
      _ = Polynomial.X ^ ((Finset.univ : Finset (Fin n)).filter (· < i)).card := Finset.prod_const _
      _ = Polynomial.X ^ i.val := by
          congr 1
          have hcard : ((Finset.univ : Finset (Fin n)).filter (· < i)).card = i.val := by
            have hbi : (Finset.univ : Finset (Fin n)).filter (· < i) =
                Finset.image (fun k : Fin i.val => ⟨k.1, lt_trans k.2 i.2⟩) Finset.univ := by
              ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
              constructor
              · intro hj; exact ⟨⟨j.1, hj⟩, rfl⟩
              · rintro ⟨k, rfl⟩; exact k.2
            rw [hbi, Finset.card_image_of_injective _ (fun a b h => by ext; simpa using congr_arg Fin.val h),
              Finset.card_fin]
          exact hcard
  have hmat : planarMat (planarPath ptsX ptsZ hz 0).1 = 1 := by
    ext i k
    simp only [planarMat, hpoly i, Polynomial.coeff_X_pow, Matrix.one_apply]
    by_cases h : k.1 = i.1
    · have hik : i = k := Fin.ext h.symm
      simp [h, hik]
    · have hik : i ≠ k := fun he => h (by subst he; rfl)
      simp [h, hik]
  have hden : planarDen (planarPath ptsX ptsZ hz 0).1 = 1 := by
    simp [planarDen, hslope]
  simp [hmat, hden]

lemma continuous_planarPath_re {n : ℕ} (ptsX ptsZ : Fin n → ℤ) (hz : StrictMono ptsZ) :
    Continuous (fun s => (atiyahDet (planarPath ptsX ptsZ hz s)).re) := by
  have heq : (fun s => (atiyahDet (planarPath ptsX ptsZ hz s)).re) =
      fun s => (planarMat (planarPath ptsX ptsZ hz s).1).det /
        planarDen (planarPath ptsX ptsZ hz s).1 := by
    ext s
    have hy : ∀ i, (planarPath ptsX ptsZ hz s).1 i 1 = 0 := fun _ => rfl
    have hz' : StrictMono (fun i => (planarPath ptsX ptsZ hz s).1 i 2) :=
      fun _ _ h => Int.cast_lt.mpr (hz h)
    rw [atiyahDet_eq_planarMat_div _ hy hz']
    rfl
  rw [heq]
  have hslope_cont : ∀ i j, i < j → Continuous (fun s => planarSlope (planarPath ptsX ptsZ hz s).1 i j) := by
    intro i j hij
    have hdz : (0 : ℝ) < (ptsZ j : ℝ) - (ptsZ i : ℝ) := sub_pos.mpr (Int.cast_lt.mpr (hz hij))
    unfold planarSlope planarPath euclidNorm
    refine Continuous.div ?_ ?_ fun s => ?_
    · continuity
    · continuity
    · change ((ptsZ j : ℝ) - (ptsZ i : ℝ)) +
          Real.sqrt ((s * (ptsX j : ℝ) - s * (ptsX i : ℝ)) ^ 2 + ((0 : ℝ) - 0) ^ 2 +
            ((ptsZ j : ℝ) - (ptsZ i : ℝ)) ^ 2) ≠ 0
      have hr : 0 ≤ Real.sqrt ((s * (ptsX j : ℝ) - s * (ptsX i : ℝ)) ^ 2 + ((0 : ℝ) - 0) ^ 2 +
          ((ptsZ j : ℝ) - (ptsZ i : ℝ)) ^ 2) := Real.sqrt_nonneg _
      linarith [hr, hdz]
  have hpoly_cont : ∀ i k, Continuous (fun s => ((planarPoly (planarPath ptsX ptsZ hz s).1 i).coeff k)) := by
    have hfin : ∀ (S : Finset (Fin n)) (i : Fin n), (∀ j ∈ S, j ≠ i) →
        ∀ k, Continuous (fun s => (∏ j ∈ S,
          if j < i then (-Polynomial.C (planarSlope (planarPath ptsX ptsZ hz s).1 j i) + Polynomial.X)
          else (1 + Polynomial.C (planarSlope (planarPath ptsX ptsZ hz s).1 i j) * Polynomial.X)).coeff k) := by
      intro S i hSi
      induction S using Finset.induction_on with
      | empty => intro k; simp only [Finset.prod_empty, Polynomial.coeff_one]; exact continuous_const
      | @insert a S ha ih =>
        intro k
        have ha_ne : a ≠ i := hSi a (Finset.mem_insert_self a S)
        have hS' : ∀ j ∈ S, j ≠ i := fun j hj => hSi j (Finset.mem_insert_of_mem hj)
        have hfac : ∀ m, Continuous (fun s =>
            (if a < i then (-Polynomial.C (planarSlope (planarPath ptsX ptsZ hz s).1 a i) + Polynomial.X)
             else (1 + Polynomial.C (planarSlope (planarPath ptsX ptsZ hz s).1 i a) * Polynomial.X)).coeff m) := by
          intro m
          by_cases hlt : a < i
          · simp only [hlt, ↓reduceIte, Polynomial.coeff_add, Polynomial.coeff_neg, Polynomial.coeff_C,
              Polynomial.coeff_X]
            by_cases hm0 : m = 0
            · simp [hm0]; exact continuous_neg.comp (hslope_cont a i hlt)
            · simp [hm0]; exact continuous_const
          · have hgt : i < a := lt_of_le_of_ne (not_lt.mp hlt) ha_ne.symm
            simp only [hlt, ↓reduceIte, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_C_mul_X]
            by_cases hm1 : m = 1
            · simpa [hm1] using hslope_cont i a hgt
            · simp [hm1]; exact continuous_const
        have hprod_rw : (fun s => (∏ j ∈ insert a S,
            if j < i then (-Polynomial.C (planarSlope (planarPath ptsX ptsZ hz s).1 j i) + Polynomial.X)
            else (1 + Polynomial.C (planarSlope (planarPath ptsX ptsZ hz s).1 i j) * Polynomial.X)).coeff k) =
            fun s => ∑ xy ∈ Finset.HasAntidiagonal.antidiagonal k,
              (if a < i then (-Polynomial.C (planarSlope (planarPath ptsX ptsZ hz s).1 a i) + Polynomial.X)
               else (1 + Polynomial.C (planarSlope (planarPath ptsX ptsZ hz s).1 i a) * Polynomial.X)).coeff xy.1 *
              (∏ j ∈ S, if j < i then (-Polynomial.C (planarSlope (planarPath ptsX ptsZ hz s).1 j i) + Polynomial.X)
               else (1 + Polynomial.C (planarSlope (planarPath ptsX ptsZ hz s).1 i j) * Polynomial.X)).coeff xy.2 := by
          ext s; rw [Finset.prod_insert ha, Polynomial.coeff_mul]
        rw [hprod_rw]
        have hxy : ∀ xy ∈ Finset.HasAntidiagonal.antidiagonal k,
            Continuous fun s =>
              (if a < i then (-Polynomial.C (planarSlope (planarPath ptsX ptsZ hz s).1 a i) + Polynomial.X)
               else (1 + Polynomial.C (planarSlope (planarPath ptsX ptsZ hz s).1 i a) * Polynomial.X)).coeff xy.1 *
              (∏ j ∈ S, if j < i then (-Polynomial.C (planarSlope (planarPath ptsX ptsZ hz s).1 j i) + Polynomial.X)
               else (1 + Polynomial.C (planarSlope (planarPath ptsX ptsZ hz s).1 i j) * Polynomial.X)).coeff xy.2 :=
          fun xy _ => (hfac xy.1).mul (ih hS' xy.2)
        fun_prop
    intro i k
    exact hfin (Finset.univ.erase i) i (fun j hj => (Finset.mem_erase.mp hj).1) k
  refine Continuous.div ?_ ?_ fun s => (planarDen_pos _).ne'
  · refine Continuous.matrix_det (continuous_pi fun i => continuous_pi fun k => hpoly_cont i k.1)
  · change Continuous fun s => ∏ e : { q : Fin n × Fin n // q.1 < q.2 },
        (1 + planarSlope (planarPath ptsX ptsZ hz s).1 e.1.1 e.1.2 ^ 2)
    have hterm : ∀ e : { q : Fin n × Fin n // q.1 < q.2 },
        Continuous fun s => 1 + planarSlope (planarPath ptsX ptsZ hz s).1 e.1.1 e.1.2 ^ 2 :=
      fun e => continuous_const.add ((hslope_cont e.1.1 e.1.2 e.2).pow 2)
    fun_prop

end PlanarOrderedReduction

/-! ## Part 4: Banded Axial Elimination Theorem via Block Triangularization -/

section BandedAxialElimination

/-- Reindexing equivalence splitting `Fin (a + 2 + b)` into `(Fin a ⊕ Fin 2) ⊕ Fin b`. -/
def splitFinEquiv (a b : ℕ) : (Fin a ⊕ Fin 2) ⊕ Fin b ≃ Fin (a + 2 + b) where
  toFun
    | .inl (.inl i) => ⟨i.1, by omega⟩
    | .inl (.inr m) => ⟨a + m.1, by omega⟩
    | .inr j => ⟨a + 2 + j.1, by omega⟩
  invFun k :=
    if h1 : k.1 < a then .inl (.inl ⟨k.1, h1⟩)
    else if h2 : k.1 < a + 2 then .inl (.inr ⟨k.1 - a, by omega⟩)
    else .inr ⟨k.1 - (a + 2), by omega⟩
  left_inv x := by
    rcases x with (i | m) | j
    · simp [i.2]
    · have hm : ¬ a + m.1 < a := by omega
      have hm2 : a + m.1 < a + 2 := by omega
      simp [hm, hm2]
    · have hj1 : ¬ a + 2 + j.1 < a := by omega
      have hj2 : ¬ a + 2 + j.1 < a + 2 := by omega
      simp [hj1, hj2]
  right_inv k := by
    by_cases h1 : k.1 < a
    · simp [h1]
    · by_cases h2 : k.1 < a + 2
      · simp [h1, h2]; ext; dsimp; omega
      · simp [h1, h2]; ext; dsimp; omega

/-- If an `(a + 2 + b) × (a + 2 + b)` matrix `M` has:
- lower-block upper-triangular with diagonal `1` (`M i j = 0` for `j < i < a`, `M i i = 1` for `i < a`),
- middle rows `i ∈ {a, a+1}` supported ONLY in columns `{a, a+1}` (`M i j = 0` for `j < a` and `a + 2 ≤ j`),
- upper-block lower-triangular with diagonal `1` (`M i j = 0` for `a + 2 ≤ i < j`, `M i i = 1` for `a + 2 ≤ i`),
then `M.det` equals the `2 × 2` middle determinant! -/
theorem det_eq_two_by_two_of_banded {a b : ℕ} (M : Matrix (Fin (a + 2 + b)) (Fin (a + 2 + b)) ℝ)
    (hL_diag : ∀ i : Fin a, M ⟨i.1, by omega⟩ ⟨i.1, by omega⟩ = 1)
    (hL_zero : ∀ i j : Fin a, j < i → M ⟨i.1, by omega⟩ ⟨j.1, by omega⟩ = 0)
    (hM_zeroL : ∀ (m : Fin 2) (j : Fin a), M ⟨a + m.1, by omega⟩ ⟨j.1, by omega⟩ = 0)
    (hM_zeroU : ∀ (m : Fin 2) (j : Fin b), M ⟨a + m.1, by omega⟩ ⟨a + 2 + j.1, by omega⟩ = 0)
    (hU_diag : ∀ j : Fin b, M ⟨a + 2 + j.1, by omega⟩ ⟨a + 2 + j.1, by omega⟩ = 1)
    (hU_zero : ∀ i j : Fin b, i < j → M ⟨a + 2 + i.1, by omega⟩ ⟨a + 2 + j.1, by omega⟩ = 0)
    (hLU_zero : ∀ (i : Fin a) (j : Fin b), M ⟨i.1, by omega⟩ ⟨a + 2 + j.1, by omega⟩ = 0) :
    M.det =
      M ⟨a, by omega⟩ ⟨a, by omega⟩ * M ⟨a + 1, by omega⟩ ⟨a + 1, by omega⟩ -
      M ⟨a, by omega⟩ ⟨a + 1, by omega⟩ * M ⟨a + 1, by omega⟩ ⟨a, by omega⟩ := by
  let e := splitFinEquiv a b
  let N := Matrix.reindex e.symm e.symm M
  have hdetN : N.det = M.det := Matrix.det_reindex_self e.symm M
  let A_L : Matrix (Fin a) (Fin a) ℝ := fun i j => M ⟨i.1, by omega⟩ ⟨j.1, by omega⟩
  let B_L : Matrix (Fin a) (Fin 2) ℝ := fun i m => M ⟨i.1, by omega⟩ ⟨a + m.1, by omega⟩
  let D_M : Matrix (Fin 2) (Fin 2) ℝ := fun m₁ m₂ => M ⟨a + m₁.1, by omega⟩ ⟨a + m₂.1, by omega⟩
  let C_U : Matrix (Fin b) (Fin a ⊕ Fin 2) ℝ := fun j x => match x with
    | .inl i => M ⟨a + 2 + j.1, by omega⟩ ⟨i.1, by omega⟩
    | .inr m => M ⟨a + 2 + j.1, by omega⟩ ⟨a + m.1, by omega⟩
  let D_U : Matrix (Fin b) (Fin b) ℝ := fun i j => M ⟨a + 2 + i.1, by omega⟩ ⟨a + 2 + j.1, by omega⟩
  let TL : Matrix (Fin a ⊕ Fin 2) (Fin a ⊕ Fin 2) ℝ := Matrix.fromBlocks A_L B_L 0 D_M
  have hN_eq : N = Matrix.fromBlocks TL 0 C_U D_U := by
    ext r c
    rcases r with (i | m₁) | j₁
    · rcases c with (j | m₂) | j₂
      · dsimp [N, Matrix.reindex_apply, e, splitFinEquiv, TL, Matrix.fromBlocks, A_L]
      · dsimp [N, Matrix.reindex_apply, e, splitFinEquiv, TL, Matrix.fromBlocks, B_L]
      · dsimp [N, Matrix.reindex_apply, e, splitFinEquiv, Matrix.fromBlocks]
        exact hLU_zero i j₂
    · rcases c with (j | m₂) | j₂
      · dsimp [N, Matrix.reindex_apply, e, splitFinEquiv, TL, Matrix.fromBlocks]
        exact hM_zeroL m₁ j
      · dsimp [N, Matrix.reindex_apply, e, splitFinEquiv, TL, Matrix.fromBlocks, D_M]
      · dsimp [N, Matrix.reindex_apply, e, splitFinEquiv, Matrix.fromBlocks]
        exact hM_zeroU m₁ j₂
    · rcases c with (j | m₂) | j₂
      · dsimp [N, Matrix.reindex_apply, e, splitFinEquiv, Matrix.fromBlocks, C_U]
      · dsimp [N, Matrix.reindex_apply, e, splitFinEquiv, Matrix.fromBlocks, C_U]
      · dsimp [N, Matrix.reindex_apply, e, splitFinEquiv, Matrix.fromBlocks, D_U]
  have hAL_tri : A_L.IsUpperTriangular := fun i j hij => hL_zero i j hij
  have hAL_det : A_L.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hAL_tri]
    exact Finset.prod_eq_one fun i _ => hL_diag i
  have hDU_tri : D_U.IsLowerTriangular := fun i j hij => hU_zero i j hij
  have hDU_det : D_U.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular D_U hDU_tri]
    exact Finset.prod_eq_one fun j _ => hU_diag j
  rw [← hdetN, hN_eq, Matrix.det_fromBlocks_zero₁₂, show TL.det = A_L.det * D_M.det from
    Matrix.det_fromBlocks_zero₂₁ A_L B_L D_M, hAL_det, hDU_det, one_mul, mul_one]
  rw [Matrix.det_fin_two]
  simp [D_M]

end BandedAxialElimination

/-! ## Part 5: Shared List-Polynomial / Determinant Engine & Sharp `n = 5` Disproof of Conjecture 3 -/

section ListPolyAndDet

/-- Evaluate a coefficient list `[c₀, c₁, …]` as the polynomial `∑ k, c_k X^k`. -/
noncomputable def evalListR : List ℝ → Polynomial ℝ
  | [] => 0
  | c :: cs => Polynomial.C c + Polynomial.X * evalListR cs

lemma coeff_evalListR (ps : List ℝ) (k : ℕ) : (evalListR ps).coeff k = ps.getD k 0 := by
  induction ps generalizing k with
  | nil => simp [evalListR]
  | cons c cs ih =>
    cases k with
    | zero => simp [evalListR]
    | succ k => simp [evalListR, Polynomial.coeff_C_succ, Polynomial.coeff_X_mul, ih]

def scaleListR (s : ℝ) : List ℝ → List ℝ
  | [] => []
  | c :: cs => (s * c) :: scaleListR s cs

def addListR : List ℝ → List ℝ → List ℝ
  | [], bs => bs
  | as, [] => as
  | a :: as, b :: bs => (a + b) :: addListR as bs

def mulLinListR (a b : ℝ) (ps : List ℝ) : List ℝ :=
  addListR (scaleListR a ps) (0 :: scaleListR b ps)

lemma evalListR_scaleListR (s : ℝ) (ps : List ℝ) :
    evalListR (scaleListR s ps) = Polynomial.C s * evalListR ps := by
  induction ps with
  | nil => simp [scaleListR, evalListR]
  | cons c cs ih =>
    simp only [scaleListR, evalListR, map_mul, ih]
    ring

lemma evalListR_addListR (as bs : List ℝ) :
    evalListR (addListR as bs) = evalListR as + evalListR bs := by
  induction as generalizing bs with
  | nil => simp [addListR, evalListR]
  | cons a as ih =>
    cases bs with
    | nil => simp [addListR, evalListR]
    | cons b bs =>
      simp only [addListR, evalListR, map_add, ih]
      ring

lemma evalListR_mulLinListR (a b : ℝ) (ps : List ℝ) :
    evalListR (mulLinListR a b ps) = evalListR ps * (Polynomial.C a + Polynomial.C b * Polynomial.X) := by
  unfold mulLinListR
  rw [evalListR_addListR, evalListR_scaleListR]
  simp only [evalListR, map_zero, zero_add, evalListR_scaleListR]
  ring

/-- Pointwise fixed-point enclosure for coefficient lists of arbitrary length. -/
def ListFpMem (S : ℤ) (ivs : List FpIv) (rs : List ℝ) : Prop :=
  ∀ k : ℕ, FpIv.FpMem S (ivs.getD k FpIv.zero) (rs.getD k 0)

lemma fpMem_zero_eq_zero {S : ℤ} (hS : 0 < S) {x : ℝ}
    (hx : FpIv.FpMem S FpIv.zero x) : x = 0 := by
  have hSR : (S : ℝ) ≠ 0 := by exact_mod_cast hS.ne'
  have h0 : (S : ℝ) * x = 0 := by
    simp only [FpIv.FpMem, FpIv.zero, Int.cast_zero] at hx
    linarith
  exact (mul_eq_zero.mp h0).resolve_left hSR

private lemma fpIv_add_zero_left (a : FpIv) : FpIv.add FpIv.zero a = a := by
  cases a; simp [FpIv.add, FpIv.zero]

private lemma fpIv_add_zero_right (a : FpIv) : FpIv.add a FpIv.zero = a := by
  cases a; simp [FpIv.add, FpIv.zero]

private lemma getD_scaleListR (s : ℝ) (ps : List ℝ) (k : ℕ) :
    (scaleListR s ps).getD k 0 = s * ps.getD k 0 := by
  induction ps generalizing k with
  | nil => simp [scaleListR]
  | cons c cs ih =>
    cases k with
    | zero => simp [scaleListR]
    | succ k => rw [scaleListR, List.getD_cons_succ, List.getD_cons_succ, ih]

private lemma getD_addListR (as bs : List ℝ) (k : ℕ) :
    (addListR as bs).getD k 0 = as.getD k 0 + bs.getD k 0 := by
  induction as generalizing bs k with
  | nil => simp [addListR]
  | cons a as ih =>
    cases bs with
    | nil => simp [addListR]
    | cons b bs =>
      cases k with
      | zero => simp [addListR]
      | succ k => rw [addListR, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ, ih]

def scaleListIv (S : ℤ) (c : FpIv) : List FpIv → List FpIv
  | [] => []
  | iv :: ivs => FpIv.mulFp S c iv :: scaleListIv S c ivs

def addListIv : List FpIv → List FpIv → List FpIv
  | [], bs => bs
  | as, [] => as
  | a :: as, b :: bs => FpIv.add a b :: addListIv as bs

def mulLinListIv (S : ℤ) (f0 f1 : FpIv) (ivs : List FpIv) : List FpIv :=
  addListIv (scaleListIv S f0 ivs) (FpIv.zero :: scaleListIv S f1 ivs)

private lemma getD_addListIv (as bs : List FpIv) (k : ℕ) :
    (addListIv as bs).getD k FpIv.zero = FpIv.add (as.getD k FpIv.zero) (bs.getD k FpIv.zero) := by
  induction as generalizing bs k with
  | nil => simp [addListIv, fpIv_add_zero_left]
  | cons a as ih =>
    cases bs with
    | nil => simp [addListIv, fpIv_add_zero_right]
    | cons b bs =>
      cases k with
      | zero => simp [addListIv]
      | succ k => rw [addListIv, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ, ih]

lemma scaleListIv_mem {S : ℤ} (hS : 0 < S) {cIv : FpIv} {c : ℝ}
    (hc : FpIv.FpMem S cIv c) {ivs : List FpIv} {ps : List ℝ} (hps : ListFpMem S ivs ps) :
    ListFpMem S (scaleListIv S cIv ivs) (scaleListR c ps) := by
  induction ivs generalizing ps with
  | nil =>
    intro k
    have hk := hps k
    rw [List.getD_nil] at hk
    rw [getD_scaleListR, fpMem_zero_eq_zero hS hk, mul_zero, scaleListIv, List.getD_nil]
    exact FpIv.zero_mem S
  | cons iv ivs ih =>
    intro k
    cases k with
    | zero =>
      rw [getD_scaleListR, scaleListIv, List.getD_cons_zero]
      exact FpIv.mulFp_mem hS hc (by simpa using hps 0)
    | succ k =>
      have hps_tail : ListFpMem S ivs (ps.drop 1) := by
        intro m
        have hm := hps (m + 1)
        rw [List.getD_cons_succ] at hm
        cases ps with
        | nil => simpa using hm
        | cons _ _ => simpa using hm
      have hsub := ih hps_tail k
      rw [getD_scaleListR] at hsub ⊢
      rw [scaleListIv, List.getD_cons_succ]
      have hdrop : (ps.drop 1).getD k 0 = ps.getD (k + 1) 0 := by
        cases ps with
        | nil => simp
        | cons _ _ => simp
      simpa [hdrop] using hsub

lemma addListIv_mem {S : ℤ} {asIv bsIv : List FpIv} {asR bsR : List ℝ}
    (ha : ListFpMem S asIv asR) (hb : ListFpMem S bsIv bsR) :
    ListFpMem S (addListIv asIv bsIv) (addListR asR bsR) := by
  intro k
  rw [getD_addListIv, getD_addListR]
  exact FpIv.add_mem (ha k) (hb k)

lemma mulLinListIv_mem {S : ℤ} (hS : 0 < S) {f0Iv f1Iv : FpIv} {f0 f1 : ℝ}
    (hf0 : FpIv.FpMem S f0Iv f0) (hf1 : FpIv.FpMem S f1Iv f1)
    {ivs : List FpIv} {ps : List ℝ} (hps : ListFpMem S ivs ps) :
    ListFpMem S (mulLinListIv S f0Iv f1Iv ivs) (mulLinListR f0 f1 ps) := by
  refine addListIv_mem (scaleListIv_mem hS hf0 hps) ?_
  intro k
  cases k with
  | zero => simp [FpIv.zero_mem S]
  | succ k =>
    rw [List.getD_cons_succ, List.getD_cons_succ]
    exact scaleListIv_mem hS hf1 hps k

/-- Linear factor `(j < i ? (-c_{ji} + X) : (1 + c_{ij} X))` for `planarPoly`. -/
noncomputable def factorPolyR {n : ℕ} (c : Fin n → Fin n → ℝ) (i j : Fin n) : Polynomial ℝ :=
  if j < i then (-Polynomial.C (c j i) + Polynomial.X)
  else (1 + Polynomial.C (c i j) * Polynomial.X)

def stepPolyR {n : ℕ} (c : Fin n → Fin n → ℝ) (i : Fin n) (ps : List ℝ) (j : Fin n) : List ℝ :=
  if j = i then ps
  else if j < i then mulLinListR (-(c j i)) 1 ps
  else mulLinListR 1 (c i j) ps

def polyListR {n : ℕ} (c : Fin n → Fin n → ℝ) (i : Fin n) : List ℝ :=
  (List.finRange n).foldl (stepPolyR c i) [1]

def stepPolyIv {n : ℕ} (S : ℤ) (cIv : Fin n → Fin n → FpIv) (i : Fin n)
    (ivs : List FpIv) (j : Fin n) : List FpIv :=
  if j = i then ivs
  else if j < i then mulLinListIv S (FpIv.neg (cIv j i)) (FpIv.ofInt S 1) ivs
  else mulLinListIv S (FpIv.ofInt S 1) (cIv i j) ivs

def polyListIv {n : ℕ} (S : ℤ) (cIv : Fin n → Fin n → FpIv) (i : Fin n) : List FpIv :=
  (List.finRange n).foldl (stepPolyIv S cIv i) [FpIv.ofInt S 1]

private lemma foldl_stepPolyR_eq {n : ℕ} (c : Fin n → Fin n → ℝ) (i : Fin n)
    (l : List (Fin n)) (ps : List ℝ) :
    evalListR (l.foldl (stepPolyR c i) ps) =
      evalListR ps * (l.map fun j => if j = i then 1 else factorPolyR c i j).prod := by
  induction l generalizing ps with
  | nil => simp
  | cons j js ih =>
    simp only [List.foldl_cons, List.map_cons, List.prod_cons, ih]
    by_cases hji : j = i
    · simp [stepPolyR, hji]
    · by_cases hlt : j < i
      · have hfac : (if j = i then (1 : Polynomial ℝ) else factorPolyR c i j) =
            Polynomial.C (-(c j i)) + Polynomial.C 1 * Polynomial.X := by
          simp [factorPolyR, hji, hlt]
        have hstep : stepPolyR c i ps j = mulLinListR (-(c j i)) 1 ps := by
          simp [stepPolyR, hji, hlt]
        rw [hstep, evalListR_mulLinListR, hfac]
        ring
      · have hfac : (if j = i then (1 : Polynomial ℝ) else factorPolyR c i j) =
            Polynomial.C 1 + Polynomial.C (c i j) * Polynomial.X := by
          simp [factorPolyR, hji, hlt]
        have hstep : stepPolyR c i ps j = mulLinListR 1 (c i j) ps := by
          simp [stepPolyR, hji, hlt]
        rw [hstep, evalListR_mulLinListR, hfac]
        ring

lemma evalListR_polyListR_eq_planarPoly {n : ℕ} (p : Fin n → Fin 3 → ℝ) (i : Fin n) :
    evalListR (polyListR (planarSlope p) i) = planarPoly p i := by
  unfold polyListR
  rw [foldl_stepPolyR_eq]
  have h1 : evalListR ([1] : List ℝ) = 1 := by simp [evalListR]
  rw [h1, one_mul]
  have hlist :
      ((List.finRange n).map fun j => if j = i then (1 : Polynomial ℝ) else factorPolyR (planarSlope p) i j).prod =
        ∏ j : Fin n, if j = i then (1 : Polynomial ℝ) else factorPolyR (planarSlope p) i j := by
    rw [← Multiset.prod_coe, ← Multiset.map_coe]
    exact (Finset.prod_eq_multiset_prod Finset.univ _).symm
  rw [hlist]
  have hsplit :
      (∏ j : Fin n, if j = i then (1 : Polynomial ℝ) else factorPolyR (planarSlope p) i j) =
        (if i = i then (1 : Polynomial ℝ) else factorPolyR (planarSlope p) i i) *
          ∏ j ∈ Finset.univ.erase i,
            if j = i then (1 : Polynomial ℝ) else factorPolyR (planarSlope p) i j :=
    (Finset.mul_prod_erase Finset.univ
      (fun j => if j = i then (1 : Polynomial ℝ) else factorPolyR (planarSlope p) i j)
      (Finset.mem_univ i)).symm
  rw [hsplit]
  simp only [↓reduceIte, one_mul]
  refine Finset.prod_congr rfl fun j hj => ?_
  have hij : j ≠ i := (Finset.mem_erase.mp hj).1
  simp only [hij, ↓reduceIte, factorPolyR]

lemma polyListIv_mem {n : ℕ} {S : ℤ} (hS : 0 < S)
    {cIv : Fin n → Fin n → FpIv} {c : Fin n → Fin n → ℝ}
    (hc : ∀ i j : Fin n, i < j → FpIv.FpMem S (cIv i j) (c i j))
    (i : Fin n) :
    ListFpMem S (polyListIv S cIv i) (polyListR c i) := by
  have hinit : ListFpMem S [FpIv.ofInt S 1] [1] := by
    intro k
    cases k with
    | zero => simpa using FpIv.ofInt_mem S 1
    | succ k => simp [FpIv.zero_mem S]
  have hfold : ∀ (l : List (Fin n)) (ivs : List FpIv) (ps : List ℝ),
      ListFpMem S ivs ps →
      ListFpMem S (l.foldl (stepPolyIv S cIv i) ivs) (l.foldl (stepPolyR c i) ps) := by
    intro l
    induction l with
    | nil => intro ivs ps h; exact h
    | cons j js ih =>
      intro ivs ps h
      apply ih
      by_cases hji : j = i
      · simp [stepPolyIv, stepPolyR, hji, h]
      · by_cases hlt : j < i
        · simp only [stepPolyIv, stepPolyR, hji, hlt, ↓reduceIte]
          exact mulLinListIv_mem hS (FpIv.neg_mem (hc j i hlt))
            (by simpa using FpIv.ofInt_mem S 1) h
        · have hij : i < j := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hji)
          simp only [stepPolyIv, stepPolyR, hji, hlt, ↓reduceIte]
          exact mulLinListIv_mem hS (by simpa using FpIv.ofInt_mem S 1) (hc i j hij) h
  exact hfold (List.finRange n) [FpIv.ofInt S 1] [1] hinit

lemma planarMat_mem_of_polyListIv {n : ℕ} {S : ℤ} (hS : 0 < S)
    {p : Fin n → Fin 3 → ℝ} {cIv : Fin n → Fin n → FpIv}
    (hc : ∀ i j : Fin n, i < j → FpIv.FpMem S (cIv i j) (planarSlope p i j))
    (i k : Fin n) :
    FpIv.FpMem S ((polyListIv S cIv i).getD k.1 FpIv.zero) (planarMat p i k) := by
  have hcoeff : planarMat p i k = (polyListR (planarSlope p) i).getD k.1 0 := by
    unfold planarMat
    rw [← evalListR_polyListR_eq_planarPoly, coeff_evalListR]
  rw [hcoeff]
  exact polyListIv_mem hS hc i k.1

/-- Recursive interval sum over `Fin m` matching `Fin.sum_univ_succ`. -/
def sumFinIv : ∀ {m : ℕ}, (Fin m → FpIv) → FpIv
  | 0, _ => FpIv.zero
  | _ + 1, f => FpIv.add (f 0) (sumFinIv fun j => f j.succ)

lemma sumFinIv_mem {S : ℤ} : ∀ {m : ℕ} {fIv : Fin m → FpIv} {f : Fin m → ℝ},
    (∀ j, FpIv.FpMem S (fIv j) (f j)) → FpIv.FpMem S (sumFinIv fIv) (∑ j : Fin m, f j)
  | 0, _, _, _ => by simp only [Finset.univ_eq_empty, Finset.sum_empty]; exact FpIv.zero_mem S
  | _ + 1, _, _, hf => by
    rw [Fin.sum_univ_succ]
    exact FpIv.add_mem (hf 0) (sumFinIv_mem fun j => hf j.succ)

/-- Recursive Laplace expansion matching `Matrix.det_succ_row_zero`. -/
def detRecIv (S : ℤ) : ∀ {m : ℕ}, (Fin m → Fin m → FpIv) → FpIv
  | 0, _ => FpIv.ofInt S 1
  | _ + 1, A =>
    sumFinIv fun j =>
      let term := FpIv.mulFp S (A 0 j) (detRecIv S fun r c => A r.succ (j.succAbove c))
      if j.1 % 2 = 0 then term else FpIv.neg term

lemma detRecIv_mem {S : ℤ} (hS : 0 < S) :
    ∀ {m : ℕ} {AIv : Fin m → Fin m → FpIv} {A : Matrix (Fin m) (Fin m) ℝ},
      (∀ i j, FpIv.FpMem S (AIv i j) (A i j)) →
      FpIv.FpMem S (detRecIv S AIv) A.det
  | 0, _, A, _ => by
    rw [Matrix.det_fin_zero]
    simpa [detRecIv] using FpIv.ofInt_mem S 1
  | _ + 1, AIv, A, hA => by
    rw [Matrix.det_succ_row_zero]
    refine sumFinIv_mem fun j => ?_
    have hsub : FpIv.FpMem S (detRecIv S fun r c => AIv r.succ (j.succAbove c))
        (A.submatrix Fin.succ j.succAbove).det :=
      detRecIv_mem hS fun r c => hA r.succ (j.succAbove c)
    have hterm : FpIv.FpMem S
        (FpIv.mulFp S (AIv 0 j) (detRecIv S fun r c => AIv r.succ (j.succAbove c)))
        (A 0 j * (A.submatrix Fin.succ j.succAbove).det) :=
      FpIv.mulFp_mem hS (hA 0 j) hsub
    by_cases he : j.1 % 2 = 0
    · have hpow : (-1 : ℝ) ^ (j : ℕ) = 1 := by
        obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero he
        rw [hk]; simp [pow_mul]
      simpa [he, hpow] using hterm
    · have hpow : (-1 : ℝ) ^ (j : ℕ) = -1 := by
        have hm : (j : ℕ) % 2 = 1 := by omega
        rw [← Nat.div_add_mod j.1 2, hm, pow_add, pow_mul]
        norm_num
      have heq : (-1 : ℝ) ^ (j : ℕ) * A 0 j * (A.submatrix Fin.succ j.succAbove).det =
          -(A 0 j * (A.submatrix Fin.succ j.succAbove).det) := by
        rw [hpow]; ring
      simp only [he, ↓reduceIte, heq]
      exact FpIv.neg_mem hterm

lemma planarSlope_planarPath_one {n : ℕ} (ptsX ptsZ : Fin n → ℤ)
    (hz : StrictMono ptsZ) (i j : Fin n) :
    planarSlope (planarPath ptsX ptsZ hz 1).1 i j =
      ((ptsX j - ptsX i : ℤ) : ℝ) /
        (((ptsZ j - ptsZ i : ℤ) : ℝ) +
          Real.sqrt (((ptsX j - ptsX i : ℤ) : ℝ) ^ 2 + ((ptsZ j - ptsZ i : ℤ) : ℝ) ^ 2)) := by
  unfold planarSlope planarPath euclidNorm
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Int.cast_sub]

/-- Decidable certificate check for `slopeIv` root enclosure `rhoLo`. -/
def rhoCheck (S dx dz rhoLo : ℤ) : Bool :=
  decide (0 ≤ rhoLo ∧ rhoLo * rhoLo ≤ S * S * (dx * dx + dz * dz) ∧
    S * S * (dx * dx + dz * dz) ≤ (rhoLo + 1) * (rhoLo + 1))

lemma slopeIv_planarPath_one_mem {n : ℕ} {S : ℤ} (hS : 0 < S)
    (ptsX ptsZ : Fin n → ℤ) (hz : StrictMono ptsZ) {i j : Fin n} (hij : i < j)
    {rhoLo : ℤ} (hrho : rhoCheck S (ptsX j - ptsX i) (ptsZ j - ptsZ i) rhoLo = true) :
    FpIv.FpMem S (FpIv.slopeIv S (ptsX j - ptsX i) (ptsZ j - ptsZ i) rhoLo)
      (planarSlope (planarPath ptsX ptsZ hz 1).1 i j) := by
  rw [planarSlope_planarPath_one]
  have hdz : 0 < ptsZ j - ptsZ i := sub_pos.mpr (hz hij)
  have hr : 0 ≤ rhoLo ∧
      rhoLo * rhoLo ≤ S * S * ((ptsX j - ptsX i) * (ptsX j - ptsX i) + (ptsZ j - ptsZ i) * (ptsZ j - ptsZ i)) ∧
      S * S * ((ptsX j - ptsX i) * (ptsX j - ptsX i) + (ptsZ j - ptsZ i) * (ptsZ j - ptsZ i)) ≤
        (rhoLo + 1) * (rhoLo + 1) := of_decide_eq_true hrho
  exact FpIv.slopeIv_mem hS hdz hr

end ListPolyAndDet

section Conjecture3Disproof

def pts5X : Fin 5 → ℤ := ![1198773, 212773, -55, -56, -697578]
def pts5Z : Fin 5 → ℤ := ![-320821, -58745, 3, 4, 117714]

lemma pts5Z_strictMono : StrictMono pts5Z := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [pts5Z] at hij ⊢

noncomputable def x5 : DistinctPoints 5 :=
  planarPath pts5X pts5Z pts5Z_strictMono 1

private def S5 : ℤ := 1000000000000000000

private def rho5Lo (i j : Fin 5) : ℤ :=
  match i.1, j.1 with
  | 0, 1 => 1020235183561123812314723
  | 0, 2 => 1241014348249044218116476
  | 0, 3 => 1241015572773363710621476
  | 0, 4 => 1946396686553386013033358
  | 1, 2 => 220787420583691769348325
  | 1, 3 => 220788650618640268911658
  | 1, 4 => 927295380060744182720025
  | 2, 3 => 1414213562373095048
  | 2, 4 => 707385478399154020971205
  | 3, 4 => 707384325938877444109684
  | _, _ => 0

private lemma rho5_ok :
    (∀ i j : Fin 5, i < j →
      rhoCheck S5 (pts5X j - pts5X i) (pts5Z j - pts5Z i) (rho5Lo i j) = true) := by
  decide

private def c5Iv (i j : Fin 5) : FpIv :=
  FpIv.slopeIv S5 (pts5X j - pts5X i) (pts5Z j - pts5Z i) (rho5Lo i j)

private def c5Lit (i j : Fin 5) : FpIv :=
  match i.1, j.1 with
  | 0, 1 => ⟨-768924121258746260, -768924121258746259⟩
  | 0, 2 => ⟨-767574955080331973, -767574955080331972⟩
  | 0, 3 => ⟨-767574502096098536, -767574502096098535⟩
  | 0, 4 => ⟨-795138498386314566, -795138498386314565⟩
  | 1, 2 => ⟨-761363263215797590, -761363263215797589⟩
  | 1, 3 => ⟨-761360766712432371, -761360766712432370⟩
  | 1, 4 => ⟨-824776794951336554, -824776794951336553⟩
  | 2, 3 => ⟨-414213562373095049, -414213562373095048⟩
  | 2, 4 => ⟨-845383562117885749, -845383562117885748⟩
  | 3, 4 => ⟨-845384555524954689, -845384555524954688⟩
  | _, _ => FpIv.zero

private lemma c5Iv_eq_lit : ∀ i j : Fin 5, i < j → c5Iv i j = c5Lit i j := by decide

private def mat5RowLit : Fin 5 → List FpIv
  | 0 => [⟨1000000000000000000, 1000000000000000000⟩, ⟨-3099212076821491335, -3099212076821491331⟩, ⟨3601642016655977986, 3601642016655977997⟩, ⟨-1860092457330402225, -1860092457330402215⟩, ⟨360219817377543414, 360219817377543418⟩]
  | 1 => [⟨768924121258746259, 768924121258746260⟩, ⟨-805050008924702674, -805050008924702666⟩, ⟨-936079422531342537, -936079422531342527⟩, ⟨1467956854746025601, 1467956854746025610⟩, ⟨-478100111465374979, -478100111465374975⟩]
  | 2 => [⟨584403372562680802, 584403372562680804⟩, ⟨792825410673345475, 792825410673345483⟩, ⟨-721206041874876721, -721206041874876712⟩, ⟨-724209842526235851, -724209842526235846⟩, ⟨350169336836506140, 350169336836506142⟩]
  | 3 => [⟨242066866218062093, 242066866218062096⟩, ⟨1013067245650771271, 1013067245650771282⟩, ⟨913718279076470765, 913718279076470776⟩, ⟨-642708010967314074, -642708010967314068⟩, ⟨-845384555524954689, -845384555524954688⟩]
  | 4 => [⟨468691765355096098, 468691765355096103⟩, ⟨2266537330114487964, 2266537330114487978⟩, ⟨4109387120407964861, 4109387120407964875⟩, ⟨3310683410980491554, 3310683410980491558⟩, ⟨1000000000000000000, 1000000000000000000⟩]

private def mat4RowLit (del : Fin 5) (u : Fin 4) : List FpIv :=
  match del.1, u.1 with
  | 0, 0 => [⟨1000000000000000000, 1000000000000000000⟩, ⟨-2347500824879566515, -2347500824879566512⟩, ⟨1835579562828247694, 1835579562828247701⟩, ⟨-478100111465374979, -478100111465374975⟩]
  | 0, 1 => [⟨761363263215797589, 761363263215797590⟩, ⟨40989022960311621, 40989022960311625⟩, ⟨-992991055519026687, -992991055519026683⟩, ⟨350169336836506140, 350169336836506142⟩]
  | 0, 2 => [⟨315365955431067573, 315365955431067575⟩, ⟨908968821025731685, 908968821025731690⟩, ⟨6187618319484588, 6187618319484592⟩, ⟨-845384555524954689, -845384555524954688⟩]
  | 0, 3 => [⟨589446701808902042, 589446701808902045⟩, ⟨2109180515984498049, 2109180515984498055⟩, ⟨2515544912594176989, 2515544912594176992⟩, ⟨1000000000000000000, 1000000000000000000⟩]
  | 1, 0 => [⟨1000000000000000000, 1000000000000000000⟩, ⟨-2330287955562745075, -2330287955562745072⟩, ⟨1809827398145053881, 1809827398145053887⟩, ⟨-468472515581713564, -468472515581713561⟩]
  | 1, 1 => [⟨767574955080331972, 767574955080331973⟩, ⟨33164793749520093, 33164793749520098⟩, ⟨-990815911498189963, -990815911498189957⟩, ⟨350169336836506140, 350169336836506142⟩]
  | 1, 2 => [⟨317939768899979686, 317939768899979688⟩, ⟨913006694253977442, 913006694253977447⟩, ⟨934622394014284, 934622394014287⟩, ⟨-845384555524954689, -845384555524954688⟩]
  | 1, 3 => [⟨568264975717157308, 568264975717157312⟩, ⟨2059069029091115558, 2059069029091115565⟩, ⟨2485906616029155001, 2485906616029155004⟩, ⟨1000000000000000000, 1000000000000000000⟩]
  | 2, 0 => [⟨1000000000000000000, 1000000000000000000⟩, ⟨-2331637121741159362, -2331637121741159359⟩, ⟨1811935757671873061, 1811935757671873068⟩, ⟨-469295949526966976, -469295949526966972⟩]
  | 2, 1 => [⟨768924121258746259, 768924121258746260⟩, ⟨-219619430797803981, -219619430797803976⟩, ⟨-1103289589029154609, -1103289589029154605⟩, ⟨627952692970772217, 627952692970772220⟩]
  | 2, 2 => [⟨584401111424799107, 584401111424799110⟩, ⟨1034891594978387589, 1034891594978387595⟩, ⟨-292538262648127020, -292538262648127016⟩, ⟨-845384555524954689, -845384555524954688⟩]
  | 2, 3 => [⟨554413152038244493, 554413152038244497⟩, ⟨2025263152487809800, 2025263152487809807⟩, ⟨2465299848862605806, 2465299848862605809⟩, ⟨1000000000000000000, 1000000000000000000⟩]
  | 3, 0 => [⟨1000000000000000000, 1000000000000000000⟩, ⟨-2331637574725392799, -2331637574725392796⟩, ⟨1811936466167579869, 1811936466167579875⟩, ⟨-469296226482057812, -469296226482057809⟩]
  | 3, 1 => [⟨768924121258746259, 768924121258746260⟩, ⟨-219621350419460302, -219621350419460296⟩, ⟨-1103290502273122609, -1103290502273122604⟩, ⟨627954752028816368, 627954752028816370⟩]
  | 3, 2 => [⟨584403372562680802, 584403372562680804⟩, ⟨1034893213485384565, 1034893213485384570⟩, ⟨-292539237241355608, -292539237241355604⟩, ⟨-845383562117885749, -845383562117885748⟩]
  | 3, 3 => [⟨554412500550184120, 554412500550184124⟩, ⟨2025261543252506314, 2025261543252506322⟩, ⟨2465298855455536866, 2465298855455536869⟩, ⟨1000000000000000000, 1000000000000000000⟩]
  | 4, 0 => [⟨1000000000000000000, 1000000000000000000⟩, ⟨-2304073578435176769, -2304073578435176766⟩, ⟨1769584411327449160, 1769584411327449166⟩, ⟨-453027765739663875, -453027765739663872⟩]
  | 4, 1 => [⟨768924121258746259, 768924121258746260⟩, ⟨-170859236632141065, -170859236632141060⟩, ⟨-1077000156108631835, -1077000156108631830⟩, ⟨579672117828659109, 579672117828659112⟩]
  | 4, 2 => [⟨584403372562680802, 584403372562680804⟩, ⟨1286870415484090471, 1286870415484090476⟩, ⟨366693053951187323, 366693053951187326⟩, ⟨-414213562373095049, -414213562373095048⟩]
  | 4, 3 => [⟨242066866218062093, 242066866218062096⟩, ⟨1217706835755846366, 1217706835755846373⟩, ⟨1943148831181625953, 1943148831181625956⟩, ⟨1000000000000000000, 1000000000000000000⟩]
  | _, _ => []

private lemma mat5RowLit_eq : ∀ i : Fin 5, polyListIv S5 c5Lit i = mat5RowLit i := by decide
private lemma mat4RowLit_eq : ∀ (del : Fin 5) (u : Fin 4),
    polyListIv S5 (fun a b => c5Lit (del.succAbove a) (del.succAbove b)) u = mat4RowLit del u := by decide

private def mat5Iv (i k : Fin 5) : FpIv := (mat5RowLit i).getD k.1 FpIv.zero
private def mat4Iv (del : Fin 5) (u v : Fin 4) : FpIv := (mat4RowLit del u).getD v.1 FpIv.zero

private def det5IvRaw : FpIv := detRecIv S5 mat5Iv
private def det4IvRaw (del : Fin 5) : FpIv := detRecIv S5 (mat4Iv del)

private def det5IvCert : FpIv := ⟨94826788893308440124, 94826788893308443700⟩

private def det4IvCert (del : Fin 5) : FpIv :=
  match del.1 with
  | 0 => ⟨14449332588750239887, 14449332588750240096⟩
  | 1 => ⟨14206356753321283618, 14206356753321283839⟩
  | 2 => ⟨18803535157089667298, 18803535157089667598⟩
  | 3 => ⟨18803569143503271802, 18803569143503272090⟩
  | _ => ⟨11748553754046003130, 11748553754046003326⟩

private lemma det5IvRaw_eq : det5IvRaw = det5IvCert := by decide
private lemma det4IvRaw_eq : ∀ del : Fin 5, det4IvRaw del = det4IvCert del := by decide

private lemma c3_int_gap :
    (max (|det5IvCert.lo|) (|det5IvCert.hi|)) ^ 3 * S5 ^ 2 <
      ∏ k : Fin 5, (det4IvCert k).lo ∧
    (∀ k : Fin 5, 0 ≤ (det4IvCert k).lo) := by
  decide

private lemma planarDen_eq_prod_ite {n : ℕ} (p : Fin n → Fin 3 → ℝ) :
    planarDen p =
      ∏ i : Fin n, ∏ j : Fin n, if i < j then 1 + planarSlope p i j ^ 2 else 1 := by
  unfold planarDen
  let s : Finset (Fin n × Fin n) := (Finset.univ : Finset (Fin n × Fin n)).filter (fun q => q.1 < q.2)
  let h_eqv : { q : Fin n × Fin n // q.1 < q.2 } ≃ { q : Fin n × Fin n // q ∈ s } :=
    Equiv.subtypeEquivRight fun q => by simp [s]
  have h1 : (∏ e : { q : Fin n × Fin n // q.1 < q.2 }, (1 + planarSlope p e.1.1 e.1.2 ^ 2)) =
      ∏ q ∈ s, (1 + planarSlope p q.1 q.2 ^ 2) := by
    let f₁ : { q : Fin n × Fin n // q.1 < q.2 } → ℝ := fun e => 1 + planarSlope p e.1.1 e.1.2 ^ 2
    let f₂ : ↥s → ℝ := fun q => 1 + planarSlope p q.1.1 q.1.2 ^ 2
    exact (Fintype.prod_equiv h_eqv f₁ f₂ fun _ => rfl).trans
      (Finset.prod_coe_sort s fun q => 1 + planarSlope p q.1 q.2 ^ 2)
  rw [h1]
  let f : Fin n × Fin n → ℝ := fun q => if q.1 < q.2 then 1 + planarSlope p q.1 q.2 ^ 2 else 1
  have h2 : ∏ q ∈ s, (1 + planarSlope p q.1 q.2 ^ 2) = ∏ q : Fin n × Fin n, f q := by
    rw [← Finset.prod_filter_mul_prod_filter_not (Finset.univ : Finset (Fin n × Fin n))
        (fun q => q.1 < q.2) f]
    have hf1 : ∏ q ∈ s, f q = ∏ q ∈ s, (1 + planarSlope p q.1 q.2 ^ 2) :=
      Finset.prod_congr rfl fun q hq => by simp [f, (Finset.mem_filter.mp hq).2]
    have hf2 : ∏ q ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun q => ¬ q.1 < q.2), f q = 1 :=
      Finset.prod_eq_one fun q hq => by simp [f, (Finset.mem_filter.mp hq).2]
    change ∏ q ∈ s, (1 + planarSlope p q.1 q.2 ^ 2) = (∏ q ∈ s, f q) * _
    rw [hf1, hf2, mul_one]
  rw [h2]
  exact Fintype.prod_prod_type f

private lemma fin5_prod_upper_eq (G : Fin 5 → Fin 5 → ℝ) :
    (∏ i : Fin 5, ∏ j : Fin 5, if i.1 < j.1 then G i j else 1) =
      G 0 1 * G 0 2 * G 0 3 * G 0 4 * G 1 2 * G 1 3 * G 1 4 * G 2 3 * G 2 4 * G 3 4 := by
  have hv0 : ((0 : Fin 5) : ℕ) = 0 := rfl
  have hv1 : ((1 : Fin 5) : ℕ) = 1 := rfl
  have hv2 : ((2 : Fin 5) : ℕ) = 2 := rfl
  have hv3 : ((3 : Fin 5) : ℕ) = 3 := rfl
  have hv4 : ((4 : Fin 5) : ℕ) = 4 := rfl
  conv_lhs => simp only [Fin.prod_univ_five, hv0, hv1, hv2, hv3, hv4]; norm_num
  ring

private lemma fin5_succAbove_table :
    ∀ (k : Fin 5) (u : Fin 4),
      k.succAbove u = match k, u with
        | 0, 0 => 1 | 0, 1 => 2 | 0, 2 => 3 | 0, 3 => 4
        | 1, 0 => 0 | 1, 1 => 2 | 1, 2 => 3 | 1, 3 => 4
        | 2, 0 => 0 | 2, 1 => 1 | 2, 2 => 3 | 2, 3 => 4
        | 3, 0 => 0 | 3, 1 => 1 | 3, 2 => 2 | 3, 3 => 4
        | 4, 0 => 0 | 4, 1 => 1 | 4, 2 => 2 | 4, 3 => 3 := by
  decide

private lemma fin4_prod_upper_sa (G : Fin 5 → Fin 5 → ℝ) (k : Fin 5) :
    (∏ u : Fin 4, ∏ v : Fin 4, if (k.succAbove u).1 < (k.succAbove v).1 then G (k.succAbove u) (k.succAbove v) else 1) =
      match k with
      | 0 => G 1 2 * G 1 3 * G 1 4 * G 2 3 * G 2 4 * G 3 4
      | 1 => G 0 2 * G 0 3 * G 0 4 * G 2 3 * G 2 4 * G 3 4
      | 2 => G 0 1 * G 0 3 * G 0 4 * G 1 3 * G 1 4 * G 3 4
      | 3 => G 0 1 * G 0 2 * G 0 4 * G 1 2 * G 1 4 * G 2 4
      | 4 => G 0 1 * G 0 2 * G 0 3 * G 1 2 * G 1 3 * G 2 3 := by
  have hv0 : ((0 : Fin 5) : ℕ) = 0 := rfl
  have hv1 : ((1 : Fin 5) : ℕ) = 1 := rfl
  have hv2 : ((2 : Fin 5) : ℕ) = 2 := rfl
  have hv3 : ((3 : Fin 5) : ℕ) = 3 := rfl
  have hv4 : ((4 : Fin 5) : ℕ) = 4 := rfl
  fin_cases k <;>
    (conv_lhs => simp only [fin5_succAbove_table, Fin.prod_univ_four, hv0, hv1, hv2, hv3, hv4]; norm_num) <;>
    ring

private lemma fin5_den_ring_id (G : Fin 5 → Fin 5 → ℝ) :
    (G 0 1 * G 0 2 * G 0 3 * G 0 4 * G 1 2 * G 1 3 * G 1 4 * G 2 3 * G 2 4 * G 3 4) ^ 3 =
      (G 1 2 * G 1 3 * G 1 4 * G 2 3 * G 2 4 * G 3 4) *
      (G 0 2 * G 0 3 * G 0 4 * G 2 3 * G 2 4 * G 3 4) *
      (G 0 1 * G 0 3 * G 0 4 * G 1 3 * G 1 4 * G 3 4) *
      (G 0 1 * G 0 2 * G 0 4 * G 1 2 * G 1 4 * G 2 4) *
      (G 0 1 * G 0 2 * G 0 3 * G 1 2 * G 1 3 * G 2 3) := by
  ring

private lemma planarDen_five_pow_three (p : Fin 5 → Fin 3 → ℝ) :
    planarDen p ^ 3 = ∏ k : Fin 5, planarDen (fun i => p (k.succAbove i)) := by
  let G : Fin 5 → Fin 5 → ℝ := fun i j => 1 + planarSlope p i j ^ 2
  have hsl : ∀ (k : Fin 5) (u v : Fin 4),
      planarSlope (fun i => p (k.succAbove i)) u v = planarSlope p (k.succAbove u) (k.succAbove v) :=
    fun _ _ _ => rfl
  have hL : planarDen p = ∏ i : Fin 5, ∏ j : Fin 5, if i.1 < j.1 then G i j else 1 := by
    rw [planarDen_eq_prod_ite]; rfl
  have hR : ∀ k : Fin 5, planarDen (fun i => p (k.succAbove i)) =
      ∏ u : Fin 4, ∏ v : Fin 4,
        if (k.succAbove u).1 < (k.succAbove v).1 then G (k.succAbove u) (k.succAbove v) else 1 := by
    intro k
    rw [planarDen_eq_prod_ite]
    refine Finset.prod_congr rfl fun u _ => Finset.prod_congr rfl fun v _ => ?_
    have hlt : (u < v) ↔ ((k.succAbove u).1 < (k.succAbove v).1) :=
      (Fin.strictMono_succAbove k).lt_iff_lt.symm
    simp only [hsl, hlt, G]
  rw [hL, fin5_prod_upper_eq G]
  simp only [hR, Fin.prod_univ_five, fin4_prod_upper_sa G]
  exact fin5_den_ring_id G

private lemma mat5Iv_mem : ∀ i k : Fin 5, FpIv.FpMem S5 (mat5Iv i k) (planarMat x5.1 i k) := by
  have hc : ∀ i j : Fin 5, i < j → FpIv.FpMem S5 (c5Lit i j) (planarSlope x5.1 i j) := by
    intro i j hij
    rw [← c5Iv_eq_lit i j hij]
    exact slopeIv_planarPath_one_mem (by norm_num [S5]) pts5X pts5Z pts5Z_strictMono hij (rho5_ok i j hij)
  intro i k
  rw [mat5Iv, ← mat5RowLit_eq i]
  exact planarMat_mem_of_polyListIv (by norm_num [S5]) hc i k

private lemma mat4Iv_mem (del : Fin 5) :
    ∀ u v : Fin 4, FpIv.FpMem S5 (mat4Iv del u v) (planarMat (deletePoint x5 del).1 u v) := by
  have hc : ∀ u v : Fin 4, u < v →
      FpIv.FpMem S5 (c5Lit (del.succAbove u) (del.succAbove v))
        (planarSlope (deletePoint x5 del).1 u v) := by
    intro u v huv
    have hlt := Fin.strictMono_succAbove del huv
    rw [← c5Iv_eq_lit _ _ hlt]
    exact slopeIv_planarPath_one_mem (by norm_num [S5]) pts5X pts5Z pts5Z_strictMono hlt
      (rho5_ok _ _ hlt)
  intro u v
  rw [mat4Iv, ← mat4RowLit_eq del u]
  exact planarMat_mem_of_polyListIv (by norm_num [S5]) hc u v

private lemma det5_abs_bound :
    |(planarMat x5.1).det| ≤ ((max (|det5IvCert.lo|) (|det5IvCert.hi|) : ℤ) : ℝ) / (S5 : ℝ) := by
  have hmem : FpIv.FpMem S5 det5IvCert (planarMat x5.1).det := by
    rw [← det5IvRaw_eq]
    exact detRecIv_mem (by norm_num [S5]) mat5Iv_mem
  have hS : (0 : ℝ) < (S5 : ℝ) := by norm_num [S5]
  have hlo : -((max (|det5IvCert.lo|) (|det5IvCert.hi|) : ℤ) : ℝ) ≤ (S5 : ℝ) * (planarMat x5.1).det := by
    have h1 : -((max (|det5IvCert.lo|) (|det5IvCert.hi|) : ℤ) : ℝ) ≤ (det5IvCert.lo : ℝ) := by
      exact_mod_cast (neg_le.mpr (le_trans (neg_le_abs det5IvCert.lo) (le_max_left _ _)))
    linarith [hmem.1]
  have hhi : (S5 : ℝ) * (planarMat x5.1).det ≤ ((max (|det5IvCert.lo|) (|det5IvCert.hi|) : ℤ) : ℝ) := by
    have h1 : (det5IvCert.hi : ℝ) ≤ ((max (|det5IvCert.lo|) (|det5IvCert.hi|) : ℤ) : ℝ) := by
      exact_mod_cast le_trans (le_abs_self det5IvCert.hi) (le_max_right _ _)
    linarith [hmem.2]
  have habs : (S5 : ℝ) * |(planarMat x5.1).det| ≤ ((max (|det5IvCert.lo|) (|det5IvCert.hi|) : ℤ) : ℝ) := by
    rw [← abs_of_pos hS, ← abs_mul, abs_le]
    exact ⟨hlo, hhi⟩
  exact (le_div_iff₀ hS).mpr (by linarith)

private lemma det4_abs_lower (del : Fin 5) :
    ((det4IvCert del).lo : ℝ) / (S5 : ℝ) ≤ |(planarMat (deletePoint x5 del).1).det| := by
  have hmem : FpIv.FpMem S5 (det4IvCert del) (planarMat (deletePoint x5 del).1).det := by
    rw [← det4IvRaw_eq del]
    exact detRecIv_mem (by norm_num [S5]) (mat4Iv_mem del)
  have hS : (0 : ℝ) < (S5 : ℝ) := by norm_num [S5]
  have hlo : ((det4IvCert del).lo : ℝ) / (S5 : ℝ) ≤ (planarMat (deletePoint x5 del).1).det :=
    (div_le_iff₀ hS).mpr (by linarith [hmem.1])
  exact le_trans hlo (le_abs_self _)

private lemma c3_gap_of_bounds
    {d5 den5 : ℝ} {d4 den4 : Fin 5 → ℝ} {B5 : ℤ} {B4 : Fin 5 → ℤ} {S : ℤ}
    (hden5 : 0 < den5) (hden_eq : den5 ^ 3 = ∏ k : Fin 5, den4 k) (hS : 0 < S)
    (hB5 : |d5| ≤ (B5 : ℝ) / (S : ℝ))
    (hB4 : ∀ k : Fin 5, 0 ≤ B4 k ∧ (B4 k : ℝ) / (S : ℝ) ≤ |d4 k|)
    (hgap : B5 ^ 3 * S ^ 2 < ∏ k : Fin 5, B4 k) :
    (|d5| / den5) ^ 3 < ∏ k : Fin 5, (|d4 k| / den4 k) := by
  have hden5_pos : 0 < den5 ^ 3 := pow_pos hden5 3
  rw [div_pow, Finset.prod_div_distrib, ← hden_eq, div_lt_div_iff_of_pos_right hden5_pos]
  have hS_pos : (0 : ℝ) < (S : ℝ) := by exact_mod_cast hS
  have h_num5 : |d5| ^ 3 ≤ (B5 : ℝ) ^ 3 / (S : ℝ) ^ 3 := by
    simpa [div_pow] using pow_le_pow_left₀ (abs_nonneg d5) hB5 3
  have h_num4 : (∏ k : Fin 5, (B4 k : ℝ)) / (S : ℝ) ^ 5 ≤ ∏ k : Fin 5, |d4 k| := by
    have hnn : ∀ k : Fin 5, 0 ≤ (B4 k : ℝ) / (S : ℝ) := fun k =>
      div_nonneg (by exact_mod_cast (hB4 k).1) hS_pos.le
    have hle : ∀ k : Fin 5, (B4 k : ℝ) / (S : ℝ) ≤ |d4 k| := fun k => (hB4 k).2
    have h1 : ∏ k : Fin 5, (B4 k : ℝ) / (S : ℝ) ≤ ∏ k : Fin 5, |d4 k| := by
      simp only [Fin.prod_univ_five]
      exact mul_le_mul
        (mul_le_mul
          (mul_le_mul
            (mul_le_mul (hle 0) (hle 1) (hnn 1) (by positivity))
            (hle 2) (hnn 2) (by positivity))
          (hle 3) (hnn 3) (by positivity))
        (hle 4) (hnn 4) (by positivity)
    simpa [Finset.prod_div_distrib, Finset.prod_const, Finset.card_fin] using h1
  have hgapR : (B5 : ℝ) ^ 3 * (S : ℝ) ^ 2 < ∏ k : Fin 5, (B4 k : ℝ) := by exact_mod_cast hgap
  have hlt_frac : (B5 : ℝ) ^ 3 / (S : ℝ) ^ 3 < (∏ k : Fin 5, (B4 k : ℝ)) / (S : ℝ) ^ 5 := by
    rw [div_lt_div_iff₀ (pow_pos hS_pos 3) (pow_pos hS_pos 5)]
    have hp : (B5 : ℝ) ^ 3 * (S : ℝ) ^ 5 = ((B5 : ℝ) ^ 3 * (S : ℝ) ^ 2) * (S : ℝ) ^ 3 := by ring
    rw [hp]
    exact mul_lt_mul_of_pos_right hgapR (pow_pos hS_pos 3)
  exact lt_of_le_of_lt h_num5 (lt_of_lt_of_le hlt_frac h_num4)

private lemma S5_pos : 0 < S5 := by decide

private lemma x5_norm_eq :
    ‖atiyahDet x5‖ = |(planarMat x5.1).det| / planarDen x5.1 := by
  have h5_hy : ∀ i, x5.1 i 1 = 0 := fun _ => rfl
  have h5_hz : StrictMono (fun i => x5.1 i 2) := fun _ _ h => Int.cast_lt.mpr (pts5Z_strictMono h)
  rw [atiyahDet_eq_planarMat_div x5 h5_hy h5_hz, Complex.norm_real, Real.norm_eq_abs,
    abs_div, abs_of_pos (planarDen_pos _)]

private lemma x5_del_norm_eq (k : Fin 5) :
    ‖atiyahDet (deletePoint x5 k)‖ =
      |(planarMat (deletePoint x5 k).1).det| / planarDen (deletePoint x5 k).1 := by
  have h4_hy : ∀ i, (deletePoint x5 k).1 i 1 = 0 := fun _ => rfl
  have h4_hz : StrictMono (fun i => (deletePoint x5 k).1 i 2) := fun _ _ h =>
    (Int.cast_lt.mpr (pts5Z_strictMono (Fin.strictMono_succAbove k h)))
  rw [atiyahDet_eq_planarMat_div (deletePoint x5 k) h4_hy h4_hz,
    Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos (planarDen_pos _)]

section ShieldC3
attribute [local irreducible] Matrix.det planarMat planarDen atiyahDet x5 S5 det5IvCert det4IvCert

private lemma x5_det_gap :
    (|(planarMat x5.1).det| / planarDen x5.1) ^ 3 <
      ∏ k : Fin 5, (|(planarMat (deletePoint x5 k).1).det| / planarDen (deletePoint x5 k).1) :=
  c3_gap_of_bounds (planarDen_pos x5.1) (planarDen_five_pow_three x5.1) S5_pos
    det5_abs_bound (fun k => ⟨c3_int_gap.2 k, det4_abs_lower k⟩) c3_int_gap.1

theorem x5_violates_conjecture_3 :
    ‖atiyahDet x5‖ ^ (5 - 2) < ∏ k : Fin 5, ‖atiyahDet (deletePoint x5 k)‖ := by
  have hR : (∏ k : Fin 5, ‖atiyahDet (deletePoint x5 k)‖) =
      ∏ k : Fin 5, (|(planarMat (deletePoint x5 k).1).det| / planarDen (deletePoint x5 k).1) :=
    Finset.prod_congr rfl fun k _ => x5_del_norm_eq k
  rw [show (5 - 2 : ℕ) = 3 from rfl, x5_norm_eq, hR]
  exact x5_det_gap

/-- Explicit minimal 5-point planar witness violating Atiyah–Sutcliffe Conjecture 3. -/
theorem exists_five_planar_points_violating_conjecture_3 :
    ∃ x : DistinctPoints 5,
      ‖atiyahDet x‖ ^ (5 - 2) < ∏ k : Fin 5, ‖atiyahDet (deletePoint x k)‖ :=
  ⟨x5, x5_violates_conjecture_3⟩

end ShieldC3

/-- **Disproof of Atiyah–Sutcliffe Conjecture 3 (2002)** at the sharp minimal dimension `n = 5`
(Bou Khuzam–Johnson proved `n = 4` holds; `n = 5` is the first case where it fails). -/
theorem disproof_atiyah_sutcliffe_conjecture_3 : ¬ AtiyahSutcliffeConjecture3Prop := by
  intro hC3
  obtain ⟨x, hx⟩ := exists_five_planar_points_violating_conjecture_3
  have hle := hC3 4 (by norm_num) x
  simp only [Nat.reduceSub] at hle hx
  linarith

end Conjecture3Disproof

/-! ## Part 6: Planar `n = 63` Disproof of Conjectures 1 & 2 (`det = 0` & `|det| < 1`) -/

section AxialTwoOffAxisReduction

private lemma prod_erase_ite_lt_X {n : ℕ} (i : Fin n) :
    (∏ j ∈ Finset.univ.erase i, if j < i then (Polynomial.X : Polynomial ℝ) else 1) =
      Polynomial.X ^ i.1 := by
  have hsplit : (Finset.univ.erase i).filter (· < i) = (Finset.univ : Finset (Fin n)).filter (· < i) := by
    ext j; simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true]
    exact ⟨fun h => h.2, fun h => ⟨h.ne, h⟩⟩
  calc
    (∏ j ∈ Finset.univ.erase i, if j < i then (Polynomial.X : Polynomial ℝ) else 1)
      = ∏ j ∈ (Finset.univ.erase i).filter (· < i), Polynomial.X := by
        rw [← Finset.prod_filter_mul_prod_filter_not (Finset.univ.erase i) (· < i)]
        have h1 : ∏ j ∈ (Finset.univ.erase i).filter (· < i),
            (if j < i then (Polynomial.X : Polynomial ℝ) else 1) =
            ∏ _j ∈ (Finset.univ.erase i).filter (· < i), Polynomial.X :=
          Finset.prod_congr rfl fun j hj => by simp [(Finset.mem_filter.mp hj).2]
        have h2 : ∏ j ∈ (Finset.univ.erase i).filter (fun j => ¬ j < i),
            (if j < i then (Polynomial.X : Polynomial ℝ) else 1) = 1 :=
          Finset.prod_eq_one fun j hj => by simp [(Finset.mem_filter.mp hj).2]
        rw [h1, h2, mul_one]
    _ = ∏ _j ∈ (Finset.univ : Finset (Fin n)).filter (· < i), Polynomial.X := by rw [hsplit]
    _ = Polynomial.X ^ ((Finset.univ : Finset (Fin n)).filter (· < i)).card := Finset.prod_const _
    _ = Polynomial.X ^ i.val := by
        congr 1
        have hbi : (Finset.univ : Finset (Fin n)).filter (· < i) =
            Finset.image (fun k : Fin i.val => ⟨k.1, lt_trans k.2 i.2⟩) Finset.univ := by
          ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
          constructor
          · intro hj; exact ⟨⟨j.1, hj⟩, rfl⟩
          · rintro ⟨k, rfl⟩; exact k.2
        rw [hbi, Finset.card_image_of_injective _ (fun a b h => by ext; simpa using congr_arg Fin.val h),
          Finset.card_fin]

private lemma planarSlope_eq_zero_of_x_eq_zero {n : ℕ} (p : Fin n → Fin 3 → ℝ)
    {u v : Fin n} (hu : p u 0 = 0) (hv : p v 0 = 0) :
    planarSlope p u v = 0 := by
  simp [planarSlope, hu, hv]

private lemma length_scaleListR (s : ℝ) (ps : List ℝ) : (scaleListR s ps).length = ps.length := by
  induction ps with
  | nil => rfl
  | cons _ _ ih => simp [scaleListR, ih]

private lemma length_scaleListIv (S : ℤ) (c : FpIv) (ivs : List FpIv) :
    (scaleListIv S c ivs).length = ivs.length := by
  induction ivs with
  | nil => rfl
  | cons _ _ ih => simp [scaleListIv, ih]

private lemma length_addListR (as bs : List ℝ) :
    (addListR as bs).length = max as.length bs.length := by
  induction as generalizing bs with
  | nil => simp [addListR]
  | cons a as ih =>
    cases bs with
    | nil => simp [addListR]
    | cons b bs => simp [addListR, ih]

private lemma length_addListIv (as bs : List FpIv) :
    (addListIv as bs).length = max as.length bs.length := by
  induction as generalizing bs with
  | nil => simp [addListIv]
  | cons a as ih =>
    cases bs with
    | nil => simp [addListIv]
    | cons b bs => simp [addListIv, ih]

private lemma length_mulLinListR (a b : ℝ) {ps : List ℝ} (hne : ps ≠ []) :
    (mulLinListR a b ps).length = ps.length + 1 := by
  unfold mulLinListR
  rw [length_addListR, length_scaleListR, List.length_cons, length_scaleListR]
  cases ps with
  | nil => exact absurd rfl hne
  | cons _ _ => simp

private lemma length_mulLinListIv (S : ℤ) (f0 f1 : FpIv) {ivs : List FpIv} (hne : ivs ≠ []) :
    (mulLinListIv S f0 f1 ivs).length = ivs.length + 1 := by
  unfold mulLinListIv
  rw [length_addListIv, length_scaleListIv, List.length_cons, length_scaleListIv]
  cases ivs with
  | nil => exact absurd rfl hne
  | cons _ _ => simp

private lemma countP_finRange_ne {n : ℕ} (i : Fin n) :
    (List.finRange n).countP (fun j => decide (j ≠ i)) = n - 1 := by
  have h1 : ∀ (l : List (Fin n)),
      l.countP (fun j => decide (j ≠ i)) + l.countP (fun j => decide (j = i)) = l.length := by
    intro l
    induction l with
    | nil => simp
    | cons x xs ih =>
      by_cases hxi : x = i
      · have h1 : decide (x ≠ i) = false := decide_eq_false (not_not.mpr hxi)
        have h2 : decide (x = i) = true := decide_eq_true hxi
        rw [List.countP_cons, List.countP_cons, List.length_cons, h1, h2]
        simp only [Bool.false_eq_true, ↓reduceIte]
        omega
      · have h1 : decide (x ≠ i) = true := decide_eq_true hxi
        have h2 : decide (x = i) = false := decide_eq_false hxi
        rw [List.countP_cons, List.countP_cons, List.length_cons, h1, h2]
        simp only [Bool.false_eq_true, ↓reduceIte]
        omega
  have htot := h1 (List.finRange n)
  rw [List.length_finRange] at htot
  have hmem : i ∈ List.finRange n := List.mem_finRange i
  have hnd : (List.finRange n).Nodup := List.nodup_finRange n
  have hcnt : (List.finRange n).countP (fun j => decide (j = i)) = 1 := by
    rw [List.countP_eq_length_filter]
    have hf : (List.finRange n).filter (fun j => decide (j = i)) = [i] := by
      have hndf : ((List.finRange n).filter (fun j => decide (j = i))).Nodup :=
        hnd.filter _
      have hall : ∀ x ∈ (List.finRange n).filter (fun j => decide (j = i)), x = i := by
        intro x hx; simpa using (List.mem_filter.mp hx).2
      have hin : i ∈ (List.finRange n).filter (fun j => decide (j = i)) :=
        List.mem_filter.mpr ⟨hmem, decide_eq_true rfl⟩
      cases hL : (List.finRange n).filter (fun j => decide (j = i)) with
      | nil => simp [hL] at hin
      | cons a as =>
        rw [hL] at hall hndf
        have ha : a = i := hall a (by simp)
        subst ha
        cases as with
        | nil => rfl
        | cons b bs =>
          have hb : b = a := hall b (by simp)
          subst hb
          simp at hndf
    rw [hf]; simp
  omega

private lemma length_polyListR {n : ℕ} (c : Fin n → Fin n → ℝ) (i : Fin n) :
    (polyListR c i).length = n := by
  have hfold : ∀ (l : List (Fin n)) (ps : List ℝ), ps ≠ [] →
      (l.foldl (stepPolyR c i) ps).length = ps.length + l.countP (fun j => decide (j ≠ i)) := by
    intro l
    induction l with
    | nil => intro ps _; simp
    | cons j js ih =>
      intro ps hne
      simp only [List.foldl_cons, List.countP_cons]
      by_cases hji : j = i
      · simp [stepPolyR, hji, ih ps hne]
      · have hstep : (stepPolyR c i ps j).length = ps.length + 1 := by
          by_cases hlt : j < i
          · simp only [stepPolyR, hji, hlt, ↓reduceIte]
            exact length_mulLinListR (-(c j i)) 1 hne
          · simp only [stepPolyR, hji, hlt, ↓reduceIte]
            exact length_mulLinListR 1 (c i j) hne
        have hne' : stepPolyR c i ps j ≠ [] := by
          intro hnil
          rw [hnil] at hstep
          simp at hstep
        rw [ih _ hne', hstep]
        simp [hji]; omega
  unfold polyListR
  rw [hfold (List.finRange n) [1] (by simp), countP_finRange_ne i]
  have hpos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  simp; omega

private lemma length_polyListIv {n : ℕ} (S : ℤ) (cIv : Fin n → Fin n → FpIv) (i : Fin n) :
    (polyListIv S cIv i).length = n := by
  have hfold : ∀ (l : List (Fin n)) (ivs : List FpIv), ivs ≠ [] →
      (l.foldl (stepPolyIv S cIv i) ivs).length = ivs.length + l.countP (fun j => decide (j ≠ i)) := by
    intro l
    induction l with
    | nil => intro ivs _; simp
    | cons j js ih =>
      intro ivs hne
      simp only [List.foldl_cons, List.countP_cons]
      by_cases hji : j = i
      · simp [stepPolyIv, hji, ih ivs hne]
      · have hstep : (stepPolyIv S cIv i ivs j).length = ivs.length + 1 := by
          by_cases hlt : j < i
          · simp only [stepPolyIv, hji, hlt, ↓reduceIte]
            exact length_mulLinListIv S (FpIv.neg (cIv j i)) (FpIv.ofInt S 1) hne
          · simp only [stepPolyIv, hji, hlt, ↓reduceIte]
            exact length_mulLinListIv S (FpIv.ofInt S 1) (cIv i j) hne
        have hne' : stepPolyIv S cIv i ivs j ≠ [] := by
          intro hnil
          rw [hnil] at hstep
          simp at hstep
        rw [ih _ hne', hstep]
        simp [hji]; omega
  unfold polyListIv
  rw [hfold (List.finRange n) [FpIv.ofInt S 1] (by simp), countP_finRange_ne i]
  have hpos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  simp; omega

private lemma list_forall2_of_getD {S : ℤ} (ivs : List FpIv) (ps : List ℝ)
    (hlen : ivs.length = ps.length) (hmem : ListFpMem S ivs ps) :
    List.Forall₂ (FpIv.FpMem S) ivs ps := by
  induction ivs generalizing ps with
  | nil =>
    cases ps with
    | nil => exact List.Forall₂.nil
    | cons _ _ => simp at hlen
  | cons iv ivs ih =>
    cases ps with
    | nil => simp at hlen
    | cons r rs =>
      refine List.Forall₂.cons (by simpa using hmem 0) ?_
      refine ih rs (by simp at hlen; exact hlen) fun k => ?_
      have hk := hmem (k + 1)
      simpa [List.getD_cons_succ] using hk

lemma polyListR_eq_ofFn {n : ℕ} (p : Fin n → Fin 3 → ℝ) (i : Fin n) :
    polyListR (planarSlope p) i = List.ofFn (planarMat p i) := by
  refine List.ext_getElem (by rw [length_polyListR, List.length_ofFn]) fun k hk1 hk2 => ?_
  have hkn : k < n := by rwa [length_polyListR] at hk1
  have hc : planarMat p i ⟨k, hkn⟩ = (polyListR (planarSlope p) i).getD k 0 := by
    unfold planarMat
    rw [← evalListR_polyListR_eq_planarPoly, coeff_evalListR]
  rw [List.getElem_ofFn, hc, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk1]
  rfl

lemma polyListIv_forall2_ofFn {n : ℕ} {S : ℤ} (hS : 0 < S)
    {p : Fin n → Fin 3 → ℝ} {cIv : Fin n → Fin n → FpIv}
    (hc : ∀ i j : Fin n, i < j → FpIv.FpMem S (cIv i j) (planarSlope p i j))
    (i : Fin n) :
    List.Forall₂ (FpIv.FpMem S) (polyListIv S cIv i) (List.ofFn (planarMat p i)) := by
  rw [← polyListR_eq_ofFn p i]
  exact list_forall2_of_getD _ _ (by rw [length_polyListIv, length_polyListR])
    (polyListIv_mem hS hc i)

/-- Front elimination recurrence on a scalar row given `(c1, c2)` pivot multiplier pairs. -/
def elimFrontR : List (ℝ × ℝ) → List ℝ → List ℝ
  | [], cur => cur
  | (c1, c2) :: rest, piv :: p1 :: p2 :: tail =>
      elimFrontR rest ((p1 - piv * c1) :: (p2 - piv * c2) :: tail)
  | _ :: rest, cur => elimFrontR rest cur

/-- Front elimination recurrence on an `FpIv` interval row. -/
def elimFrontIv (S : ℤ) : List (FpIv × FpIv) → List FpIv → List FpIv
  | [], cur => cur
  | (c1, c2) :: rest, piv :: p1 :: p2 :: tail =>
      elimFrontIv S rest
        (FpIv.sub p1 (FpIv.mulFp S piv c1) :: FpIv.sub p2 (FpIv.mulFp S piv c2) :: tail)
  | _ :: rest, cur => elimFrontIv S rest cur

lemma elimFrontIv_forall2 {S : ℤ} (hS : 0 < S)
    {pairsIv : List (FpIv × FpIv)} {pairsR : List (ℝ × ℝ)}
    (hpairs : List.Forall₂ (fun a b => FpIv.FpMem S a.1 b.1 ∧ FpIv.FpMem S a.2 b.2) pairsIv pairsR)
    {ivs : List FpIv} {rs : List ℝ}
    (hrow : List.Forall₂ (FpIv.FpMem S) ivs rs) :
    List.Forall₂ (FpIv.FpMem S) (elimFrontIv S pairsIv ivs) (elimFrontR pairsR rs) := by
  induction hpairs generalizing ivs rs with
  | nil => exact hrow
  | @cons pIv pR restIv restR hp _ ih =>
    rcases pIv with ⟨c1Iv, c2Iv⟩
    rcases pR with ⟨c1R, c2R⟩
    rcases hp with ⟨hc1, hc2⟩
    rcases hrow with _ | ⟨hpiv, _ | ⟨hp1, _ | ⟨hp2, htail⟩⟩⟩
    · exact ih List.Forall₂.nil
    · exact ih (List.Forall₂.cons hpiv List.Forall₂.nil)
    · exact ih (List.Forall₂.cons hpiv (List.Forall₂.cons hp1 List.Forall₂.nil))
    · apply ih
      refine List.Forall₂.cons (FpIv.sub_mem hp1 (FpIv.mulFp_mem hS hpiv hc1)) ?_
      exact List.Forall₂.cons (FpIv.sub_mem hp2 (FpIv.mulFp_mem hS hpiv hc2)) htail

private lemma planarPoly_axial_lower {a b : ℕ} (p : Fin (a + 2 + b) → Fin 3 → ℝ)
    (haxL : ∀ i : Fin a, p ⟨i.1, by omega⟩ 0 = 0)
    (haxU : ∀ k : Fin b, p ⟨a + 2 + k.1, by omega⟩ 0 = 0)
    (i₀ : Fin a) :
    let i : Fin (a + 2 + b) := ⟨i₀.1, by omega⟩
    let idxA : Fin (a + 2 + b) := ⟨a, by omega⟩
    let idxB : Fin (a + 2 + b) := ⟨a + 1, by omega⟩
    planarPoly p i =
      Polynomial.X ^ i₀.1 +
        Polynomial.C (planarSlope p i idxA + planarSlope p i idxB) * Polynomial.X ^ (i₀.1 + 1) +
        Polynomial.C (planarSlope p i idxA * planarSlope p i idxB) * Polynomial.X ^ (i₀.1 + 2) := by
  intro i idxA idxB
  have hpi : p i 0 = 0 := haxL i₀
  have hax_all : ∀ j : Fin (a + 2 + b), j ≠ idxA → j ≠ idxB → p j 0 = 0 := by
    intro j hjA hjB
    have h1 : j.1 ≠ a := fun h => hjA (Fin.ext h)
    have h2 : j.1 ≠ a + 1 := fun h => hjB (Fin.ext h)
    by_cases hlt : j.1 < a
    · exact haxL ⟨j.1, hlt⟩
    · have hge : a + 2 ≤ j.1 := by omega
      have heq : (⟨a + 2 + (j.1 - (a + 2)), by omega⟩ : Fin (a + 2 + b)) = j := by
        ext; dsimp; omega
      simpa [heq] using haxU ⟨j.1 - (a + 2), by omega⟩
  let fac : Fin (a + 2 + b) → Polynomial ℝ := fun j =>
    if j < i then (-Polynomial.C (planarSlope p j i) + Polynomial.X)
    else (1 + Polynomial.C (planarSlope p i j) * Polynomial.X)
  have hA_mem : idxA ∈ Finset.univ.erase i :=
    Finset.mem_erase.mpr ⟨Fin.ne_of_val_ne (by dsimp [i, idxA]; omega), Finset.mem_univ _⟩
  have hB_mem : idxB ∈ (Finset.univ.erase i).erase idxA :=
    Finset.mem_erase.mpr ⟨Fin.ne_of_val_ne (by dsimp [idxA, idxB]; omega),
      Finset.mem_erase.mpr ⟨Fin.ne_of_val_ne (by dsimp [i, idxB]; omega), Finset.mem_univ _⟩⟩
  have hpeel : (∏ j ∈ Finset.univ.erase i, fac j) =
      fac idxA * fac idxB * ∏ j ∈ ((Finset.univ.erase i).erase idxA).erase idxB, fac j := by
    rw [← Finset.mul_prod_erase (Finset.univ.erase i) fac hA_mem,
        ← Finset.mul_prod_erase ((Finset.univ.erase i).erase idxA) fac hB_mem]
    ring
  let g : Fin (a + 2 + b) → Polynomial ℝ := fun j => if j < i then Polynomial.X else 1
  have hrem_fac : ∏ j ∈ ((Finset.univ.erase i).erase idxA).erase idxB, fac j =
      ∏ j ∈ ((Finset.univ.erase i).erase idxA).erase idxB, g j := by
    refine Finset.prod_congr rfl fun j hj => ?_
    have hjB : j ≠ idxB := (Finset.mem_erase.mp hj).1
    have hjA : j ≠ idxA := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
    have hpj := hax_all j hjA hjB
    simp [fac, g, planarSlope_eq_zero_of_x_eq_zero p hpi hpj,
      planarSlope_eq_zero_of_x_eq_zero p hpj hpi]
  have hnotA : ¬ idxA < i := not_lt.mpr (Fin.mk_le_mk.mpr (by omega))
  have hnotB : ¬ idxB < i := not_lt.mpr (Fin.mk_le_mk.mpr (by omega))
  have hgA : g idxA = 1 := by simp [g, hnotA]
  have hgB : g idxB = 1 := by simp [g, hnotB]
  have hrem_eq : (∏ j ∈ ((Finset.univ.erase i).erase idxA).erase idxB, g j) =
      Polynomial.X ^ i₀.1 := by
    calc (∏ j ∈ ((Finset.univ.erase i).erase idxA).erase idxB, g j)
      _ = g idxB * ∏ j ∈ ((Finset.univ.erase i).erase idxA).erase idxB, g j := by rw [hgB, one_mul]
      _ = ∏ j ∈ (Finset.univ.erase i).erase idxA, g j :=
          Finset.mul_prod_erase _ g hB_mem
      _ = g idxA * ∏ j ∈ (Finset.univ.erase i).erase idxA, g j := by rw [hgA, one_mul]
      _ = ∏ j ∈ Finset.univ.erase i, g j := Finset.mul_prod_erase _ g hA_mem
      _ = Polynomial.X ^ i₀.1 := prod_erase_ite_lt_X i
  change (∏ j ∈ Finset.univ.erase i, fac j) = _
  rw [hpeel, hrem_fac, hrem_eq]
  have hfA : fac idxA = 1 + Polynomial.C (planarSlope p i idxA) * Polynomial.X := by simp [fac, hnotA]
  have hfB : fac idxB = 1 + Polynomial.C (planarSlope p i idxB) * Polynomial.X := by simp [fac, hnotB]
  rw [hfA, hfB]
  simp only [map_add, map_mul]
  ring

private lemma planarMat_axial_lower {a b : ℕ} (p : Fin (a + 2 + b) → Fin 3 → ℝ)
    (haxL : ∀ i : Fin a, p ⟨i.1, by omega⟩ 0 = 0)
    (haxU : ∀ k : Fin b, p ⟨a + 2 + k.1, by omega⟩ 0 = 0)
    (i₀ : Fin a) (col : Fin (a + 2 + b)) :
    let i : Fin (a + 2 + b) := ⟨i₀.1, by omega⟩
    let c1 := planarSlope p i ⟨a, by omega⟩
    let c2 := planarSlope p i ⟨a + 1, by omega⟩
    planarMat p i col =
      if col.1 = i₀.1 then 1
      else if col.1 = i₀.1 + 1 then c1 + c2
      else if col.1 = i₀.1 + 2 then c1 * c2
      else 0 := by
  dsimp only
  unfold planarMat
  rw [planarPoly_axial_lower p haxL haxU i₀]
  simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul_X_pow]
  simp only [eq_comm (a := col.1)]
  split_ifs <;> first | omega | ring

private lemma planarPoly_axial_upper {a b : ℕ} (p : Fin (a + 2 + b) → Fin 3 → ℝ)
    (haxL : ∀ i : Fin a, p ⟨i.1, by omega⟩ 0 = 0)
    (haxU : ∀ k : Fin b, p ⟨a + 2 + k.1, by omega⟩ 0 = 0)
    (k₀ : Fin b) :
    let i : Fin (a + 2 + b) := ⟨a + 2 + k₀.1, by omega⟩
    let idxA : Fin (a + 2 + b) := ⟨a, by omega⟩
    let idxB : Fin (a + 2 + b) := ⟨a + 1, by omega⟩
    planarPoly p i =
      Polynomial.C (planarSlope p idxA i * planarSlope p idxB i) * Polynomial.X ^ (a + k₀.1) +
        Polynomial.C (-(planarSlope p idxA i + planarSlope p idxB i)) * Polynomial.X ^ (a + k₀.1 + 1) +
        Polynomial.X ^ (a + k₀.1 + 2) := by
  intro i idxA idxB
  have hpi : p i 0 = 0 := haxU k₀
  have hax_all : ∀ j : Fin (a + 2 + b), j ≠ idxA → j ≠ idxB → p j 0 = 0 := by
    intro j hjA hjB
    have h1 : j.1 ≠ a := fun h => hjA (Fin.ext h)
    have h2 : j.1 ≠ a + 1 := fun h => hjB (Fin.ext h)
    by_cases hlt : j.1 < a
    · exact haxL ⟨j.1, hlt⟩
    · have hge : a + 2 ≤ j.1 := by omega
      have heq : (⟨a + 2 + (j.1 - (a + 2)), by omega⟩ : Fin (a + 2 + b)) = j := by
        ext; dsimp; omega
      simpa [heq] using haxU ⟨j.1 - (a + 2), by omega⟩
  let fac : Fin (a + 2 + b) → Polynomial ℝ := fun j =>
    if j < i then (-Polynomial.C (planarSlope p j i) + Polynomial.X)
    else (1 + Polynomial.C (planarSlope p i j) * Polynomial.X)
  have hA_mem : idxA ∈ Finset.univ.erase i :=
    Finset.mem_erase.mpr ⟨Fin.ne_of_val_ne (by dsimp [i, idxA]; omega), Finset.mem_univ _⟩
  have hB_mem : idxB ∈ (Finset.univ.erase i).erase idxA :=
    Finset.mem_erase.mpr ⟨Fin.ne_of_val_ne (by dsimp [idxA, idxB]; omega),
      Finset.mem_erase.mpr ⟨Fin.ne_of_val_ne (by dsimp [i, idxB]; omega), Finset.mem_univ _⟩⟩
  have hpeel : (∏ j ∈ Finset.univ.erase i, fac j) =
      fac idxA * fac idxB * ∏ j ∈ ((Finset.univ.erase i).erase idxA).erase idxB, fac j := by
    rw [← Finset.mul_prod_erase (Finset.univ.erase i) fac hA_mem,
        ← Finset.mul_prod_erase ((Finset.univ.erase i).erase idxA) fac hB_mem]
    ring
  let g : Fin (a + 2 + b) → Polynomial ℝ := fun j => if j < i then Polynomial.X else 1
  have hrem_fac : ∏ j ∈ ((Finset.univ.erase i).erase idxA).erase idxB, fac j =
      ∏ j ∈ ((Finset.univ.erase i).erase idxA).erase idxB, g j := by
    refine Finset.prod_congr rfl fun j hj => ?_
    have hjB : j ≠ idxB := (Finset.mem_erase.mp hj).1
    have hjA : j ≠ idxA := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
    have hpj := hax_all j hjA hjB
    simp [fac, g, planarSlope_eq_zero_of_x_eq_zero p hpi hpj,
      planarSlope_eq_zero_of_x_eq_zero p hpj hpi]
  have hAlt : idxA < i := Fin.mk_lt_mk.mpr (by omega)
  have hBlt : idxB < i := Fin.mk_lt_mk.mpr (by omega)
  have hgA : g idxA = Polynomial.X := by simp [g, hAlt]
  have hgB : g idxB = Polynomial.X := by simp [g, hBlt]
  have hrem_mul : (∏ j ∈ ((Finset.univ.erase i).erase idxA).erase idxB, g j) * (Polynomial.X * Polynomial.X) =
      Polynomial.X ^ (a + k₀.1) * (Polynomial.X * Polynomial.X) := by
    have h1 : (∏ j ∈ ((Finset.univ.erase i).erase idxA).erase idxB, g j) * (Polynomial.X * Polynomial.X) =
        g idxA * (g idxB * ∏ j ∈ ((Finset.univ.erase i).erase idxA).erase idxB, g j) := by
      rw [hgA, hgB]; ring
    rw [h1, Finset.mul_prod_erase _ g hB_mem, Finset.mul_prod_erase _ g hA_mem, prod_erase_ite_lt_X i]
    change Polynomial.X ^ (a + 2 + k₀.1) = _
    ring
  have hrem_eq : (∏ j ∈ ((Finset.univ.erase i).erase idxA).erase idxB, g j) =
      Polynomial.X ^ (a + k₀.1) :=
    mul_right_cancel₀ (mul_ne_zero Polynomial.X_ne_zero Polynomial.X_ne_zero) hrem_mul
  change (∏ j ∈ Finset.univ.erase i, fac j) = _
  rw [hpeel, hrem_fac, hrem_eq]
  have hfA : fac idxA = -Polynomial.C (planarSlope p idxA i) + Polynomial.X := by simp [fac, hAlt]
  have hfB : fac idxB = -Polynomial.C (planarSlope p idxB i) + Polynomial.X := by simp [fac, hBlt]
  rw [hfA, hfB]
  simp only [map_neg, map_add, map_mul]
  ring

private lemma planarMat_axial_upper {a b : ℕ} (p : Fin (a + 2 + b) → Fin 3 → ℝ)
    (haxL : ∀ i : Fin a, p ⟨i.1, by omega⟩ 0 = 0)
    (haxU : ∀ k : Fin b, p ⟨a + 2 + k.1, by omega⟩ 0 = 0)
    (k₀ : Fin b) (col : Fin (a + 2 + b)) :
    let i : Fin (a + 2 + b) := ⟨a + 2 + k₀.1, by omega⟩
    let u0 := planarSlope p ⟨a, by omega⟩ i * planarSlope p ⟨a + 1, by omega⟩ i
    let u1 := -(planarSlope p ⟨a, by omega⟩ i + planarSlope p ⟨a + 1, by omega⟩ i)
    planarMat p i col =
      if col.1 = a + k₀.1 then u0
      else if col.1 = a + k₀.1 + 1 then u1
      else if col.1 = a + k₀.1 + 2 then 1
      else 0 := by
  dsimp only
  unfold planarMat
  rw [planarPoly_axial_upper p haxL haxU k₀]
  simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul_X_pow]
  simp only [eq_comm (a := col.1)]
  split_ifs <;> first | omega | ring

section RowEliminationDet
attribute [local irreducible] Matrix.det

private noncomputable def takeTailR {a b : ℕ} (t : ℕ) (f : Fin (a + 2 + b) → ℝ) : List ℝ :=
  (List.finRange (a + 2 + b - t)).map fun k => f ⟨t + k.1, by omega⟩

private noncomputable def takeRevFromR {a b : ℕ} (m : ℕ) (hm : m ≤ 2 + b)
    (f : Fin (a + 2 + b) → ℝ) : List ℝ :=
  (List.finRange m).map fun q => f ⟨a + m - 1 - q.1, by omega⟩

private noncomputable def elimOneLeftR {a b : ℕ} (p : Fin (a + 2 + b) → Fin 3 → ℝ)
    (j : Fin a) (r : Fin (a + 2 + b) → ℝ) : Fin (a + 2 + b) → ℝ :=
  r + (-r ⟨j.1, by omega⟩) • planarMat p ⟨j.1, by omega⟩

private noncomputable def elimLeftLoopR {a b : ℕ} (p : Fin (a + 2 + b) → Fin 3 → ℝ) :
    ∀ t : ℕ, t ≤ a → (Fin (a + 2 + b) → ℝ) → (Fin (a + 2 + b) → ℝ)
  | 0, _, r => r
  | t + 1, ht, r => elimOneLeftR p ⟨t, by omega⟩ (elimLeftLoopR p t (by omega) r)

private noncomputable def elimOneRightR {a b : ℕ} (p : Fin (a + 2 + b) → Fin 3 → ℝ)
    (k : Fin b) (r : Fin (a + 2 + b) → ℝ) : Fin (a + 2 + b) → ℝ :=
  r + (-r ⟨a + 2 + k.1, by omega⟩) • planarMat p ⟨a + 2 + k.1, by omega⟩

private noncomputable def elimRightPrefixR {a b : ℕ} (p : Fin (a + 2 + b) → Fin 3 → ℝ) :
    ∀ s : ℕ, s ≤ b → (Fin (a + 2 + b) → ℝ) → (Fin (a + 2 + b) → ℝ)
  | 0, _, r => r
  | s + 1, hs, r => elimOneRightR p ⟨b - 1 - s, by omega⟩ (elimRightPrefixR p s (by omega) r)

private lemma elimOneLeftR_eq {a b : ℕ} (p : Fin (a + 2 + b) → Fin 3 → ℝ)
    (haxL : ∀ i : Fin a, p ⟨i.1, by omega⟩ 0 = 0)
    (haxU : ∀ k : Fin b, p ⟨a + 2 + k.1, by omega⟩ 0 = 0)
    (j : Fin a) (r : Fin (a + 2 + b) → ℝ) (col : Fin (a + 2 + b)) :
    let idxJ : Fin (a + 2 + b) := ⟨j.1, by omega⟩
    let s1 := planarSlope p idxJ ⟨a, by omega⟩ + planarSlope p idxJ ⟨a + 1, by omega⟩
    let s2 := planarSlope p idxJ ⟨a, by omega⟩ * planarSlope p idxJ ⟨a + 1, by omega⟩
    elimOneLeftR p j r col =
      if col.1 = j.1 then 0
      else if col.1 = j.1 + 1 then r col - r idxJ * s1
      else if col.1 = j.1 + 2 then r col - r idxJ * s2
      else r col := by
  intro idxJ s1 s2
  change r col + (-r idxJ) * planarMat p idxJ col = _
  rw [planarMat_axial_lower p haxL haxU j col]
  split_ifs with h0
  · rw [show col = idxJ from Fin.ext h0]; ring
  · ring
  · ring
  · ring

private lemma elimOneRightR_eq {a b : ℕ} (p : Fin (a + 2 + b) → Fin 3 → ℝ)
    (haxL : ∀ i : Fin a, p ⟨i.1, by omega⟩ 0 = 0)
    (haxU : ∀ k : Fin b, p ⟨a + 2 + k.1, by omega⟩ 0 = 0)
    (k : Fin b) (r : Fin (a + 2 + b) → ℝ) (col : Fin (a + 2 + b)) :
    let idxK : Fin (a + 2 + b) := ⟨a + 2 + k.1, by omega⟩
    let u0 := planarSlope p ⟨a, by omega⟩ idxK * planarSlope p ⟨a + 1, by omega⟩ idxK
    let u1 := -(planarSlope p ⟨a, by omega⟩ idxK + planarSlope p ⟨a + 1, by omega⟩ idxK)
    elimOneRightR p k r col =
      if col.1 = a + k.1 then r col - r idxK * u0
      else if col.1 = a + k.1 + 1 then r col - r idxK * u1
      else if col.1 = a + k.1 + 2 then 0
      else r col := by
  intro idxK u0 u1
  change r col + (-r idxK) * planarMat p idxK col = _
  rw [planarMat_axial_upper p haxL haxU k col]
  split_ifs with h0 h1 h2
  · ring
  · ring
  · rw [show col = idxK from Fin.ext (by dsimp [idxK]; omega)]; ring
  · ring

private lemma elimLeftLoopR_zero_lt {a b : ℕ} (p : Fin (a + 2 + b) → Fin 3 → ℝ)
    (haxL : ∀ i : Fin a, p ⟨i.1, by omega⟩ 0 = 0)
    (haxU : ∀ k : Fin b, p ⟨a + 2 + k.1, by omega⟩ 0 = 0) :
    ∀ (t : ℕ) (ht : t ≤ a) (r : Fin (a + 2 + b) → ℝ) (j : ℕ) (hj : j < t),
      elimLeftLoopR p t ht r ⟨j, by omega⟩ = 0
  | 0, _, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | t + 1, ht, r, j, hj => by
    rw [elimLeftLoopR, elimOneLeftR_eq p haxL haxU ⟨t, by omega⟩]
    by_cases hjt : j = t
    · simp [hjt]
    · have hlt : j < t := by omega
      have hne1 : ¬ j = t + 1 := by omega
      have hne2 : ¬ j = t + 2 := by omega
      simp only [hjt, hne1, hne2, ↓reduceIte]
      exact elimLeftLoopR_zero_lt p haxL haxU t (by omega) r j hlt

private lemma elimRightPrefixR_zero_left {a b : ℕ} (p : Fin (a + 2 + b) → Fin 3 → ℝ)
    (haxL : ∀ i : Fin a, p ⟨i.1, by omega⟩ 0 = 0)
    (haxU : ∀ k : Fin b, p ⟨a + 2 + k.1, by omega⟩ 0 = 0)
    (r : Fin (a + 2 + b) → ℝ) (hr : ∀ j : Fin a, r ⟨j.1, by omega⟩ = 0) :
    ∀ (s : ℕ) (hs : s ≤ b) (j : Fin a),
      elimRightPrefixR p s hs r ⟨j.1, by omega⟩ = 0
  | 0, _, j => hr j
  | s + 1, hs, j => by
    rw [elimRightPrefixR, elimOneRightR_eq p haxL haxU]
    have h0 : ¬ j.1 = a + (b - 1 - s) := by omega
    have h1 : ¬ j.1 = a + (b - 1 - s) + 1 := by omega
    have h2 : ¬ j.1 = a + (b - 1 - s) + 2 := by omega
    simp only [h0, h1, h2, ↓reduceIte]
    exact elimRightPrefixR_zero_left p haxL haxU r hr s (by omega) j

private lemma elimRightPrefixR_zero_right {a b : ℕ} (p : Fin (a + 2 + b) → Fin 3 → ℝ)
    (haxL : ∀ i : Fin a, p ⟨i.1, by omega⟩ 0 = 0)
    (haxU : ∀ k : Fin b, p ⟨a + 2 + k.1, by omega⟩ 0 = 0)
    (r : Fin (a + 2 + b) → ℝ) :
    ∀ (s : ℕ) (hs : s ≤ b) (j : Fin b), b - s ≤ j.1 →
      elimRightPrefixR p s hs r ⟨a + 2 + j.1, by omega⟩ = 0
  | 0, _, j, hj => by omega
  | s + 1, hs, j, hj => by
    rw [elimRightPrefixR, elimOneRightR_eq p haxL haxU]
    by_cases heq : j.1 = b - 1 - s
    · have h2 : a + 2 + j.1 = a + (b - 1 - s) + 2 := by omega
      simp [h2]
    · have hgt : b - s ≤ j.1 := by omega
      have h0 : ¬ a + 2 + j.1 = a + (b - 1 - s) := by omega
      have h1 : ¬ a + 2 + j.1 = a + (b - 1 - s) + 1 := by omega
      have h2 : ¬ a + 2 + j.1 = a + (b - 1 - s) + 2 := by omega
      simp only [h0, h1, h2, ↓reduceIte]
      exact elimRightPrefixR_zero_right p haxL haxU r s (by omega) j hgt

private lemma det_updateRow_elimLeftLoopR {a b : ℕ} (p : Fin (a + 2 + b) → Fin 3 → ℝ)
    (N : Matrix (Fin (a + 2 + b)) (Fin (a + 2 + b)) ℝ)
    (hN_ax : ∀ j : Fin a, N ⟨j.1, by omega⟩ = planarMat p ⟨j.1, by omega⟩)
    {m : Fin (a + 2 + b)} (hm : a ≤ m.1) :
    ∀ (t : ℕ) (ht : t ≤ a), (N.updateRow m (elimLeftLoopR p t ht (N m))).det = N.det
  | 0, _ => by simp [elimLeftLoopR]
  | t + 1, ht => by
    have hprev := det_updateRow_elimLeftLoopR p N hN_ax hm t (by omega)
    let j : Fin a := ⟨t, by omega⟩
    let jdx : Fin (a + 2 + b) := ⟨t, by omega⟩
    have hm_ne : m ≠ jdx := Fin.ne_of_val_ne (by dsimp [jdx]; omega)
    have hrow : (N.updateRow m (elimLeftLoopR p t (by omega) (N m))).updateRow m
        ((N.updateRow m (elimLeftLoopR p t (by omega) (N m))) m +
          (-(elimLeftLoopR p t (by omega) (N m) jdx)) •
            (N.updateRow m (elimLeftLoopR p t (by omega) (N m))) jdx) =
        N.updateRow m (elimLeftLoopR p (t + 1) ht (N m)) := by
      ext row col
      by_cases hr : row = m
      · subst hr
        simp [elimLeftLoopR, elimOneLeftR, Matrix.updateRow_self, Matrix.updateRow_ne hm_ne.symm,
          hN_ax j, j, jdx]
      · simp [Matrix.updateRow_ne hr]
    rw [← hrow, Matrix.det_updateRow_add_smul_self _ hm_ne]
    exact hprev

private lemma det_updateRow_elimRightPrefixR {a b : ℕ} (p : Fin (a + 2 + b) → Fin 3 → ℝ)
    (N : Matrix (Fin (a + 2 + b)) (Fin (a + 2 + b)) ℝ)
    (hN_ax : ∀ k : Fin b, N ⟨a + 2 + k.1, by omega⟩ = planarMat p ⟨a + 2 + k.1, by omega⟩)
    {m : Fin (a + 2 + b)} (hm : m.1 < a + 2) :
    ∀ (s : ℕ) (hs : s ≤ b), (N.updateRow m (elimRightPrefixR p s hs (N m))).det = N.det
  | 0, _ => by simp [elimRightPrefixR]
  | s + 1, hs => by
    have hprev := det_updateRow_elimRightPrefixR p N hN_ax hm s (by omega)
    let k : Fin b := ⟨b - 1 - s, by omega⟩
    let kdx : Fin (a + 2 + b) := ⟨a + 2 + k.1, by omega⟩
    have hm_ne : m ≠ kdx := Fin.ne_of_val_ne (by dsimp [kdx, k]; omega)
    have hrow : (N.updateRow m (elimRightPrefixR p s (by omega) (N m))).updateRow m
        ((N.updateRow m (elimRightPrefixR p s (by omega) (N m))) m +
          (-(elimRightPrefixR p s (by omega) (N m) kdx)) •
            (N.updateRow m (elimRightPrefixR p s (by omega) (N m))) kdx) =
        N.updateRow m (elimRightPrefixR p (s + 1) hs (N m)) := by
      ext row col
      by_cases hr : row = m
      · subst hr
        simp [elimRightPrefixR, elimOneRightR, Matrix.updateRow_self, Matrix.updateRow_ne hm_ne.symm,
          hN_ax k, k, kdx]
      · simp [Matrix.updateRow_ne hr]
    rw [← hrow, Matrix.det_updateRow_add_smul_self _ hm_ne]
    exact hprev

private lemma elimFrontR_append (xs ys : List (ℝ × ℝ)) (cur : List ℝ) :
    elimFrontR (xs ++ ys) cur = elimFrontR ys (elimFrontR xs cur) := by
  induction xs generalizing cur with
  | nil => simp [elimFrontR]
  | cons p xs ih =>
    rcases p with ⟨c1, c2⟩
    rcases cur with _ | ⟨piv, _ | ⟨p1, _ | ⟨p2, tail⟩⟩⟩ <;> simp [elimFrontR, ih]

private lemma takeTailR_eq_cons_three {a b t : ℕ} (ht : t < a) (f : Fin (a + 2 + b) → ℝ) :
    takeTailR (a := a) (b := b) t f =
      f ⟨t, by omega⟩ :: f ⟨t + 1, by omega⟩ :: f ⟨t + 2, by omega⟩ ::
        takeTailR (a := a) (b := b) (t + 3) f := by
  refine List.ext_getElem (by simp [takeTailR]; omega) fun k hk1 _ => ?_
  rcases k with _ | _ | _ | k
  · simp [takeTailR]
  · simp [takeTailR]
  · simp [takeTailR]
  · simp only [List.getElem_cons_succ, takeTailR, List.getElem_map, List.getElem_finRange,
      Fin.val_cast]
    exact congrArg f (Fin.ext (by dsimp; omega))

private lemma takeTailR_elimStep {a b : ℕ} (p : Fin (a + 2 + b) → Fin 3 → ℝ)
    (haxL : ∀ i : Fin a, p ⟨i.1, by omega⟩ 0 = 0)
    (haxU : ∀ k : Fin b, p ⟨a + 2 + k.1, by omega⟩ 0 = 0)
    (t : ℕ) (ht : t < a) (f : Fin (a + 2 + b) → ℝ) :
    let idxT : Fin (a + 2 + b) := ⟨t, by omega⟩
    let s1 := planarSlope p idxT ⟨a, by omega⟩ + planarSlope p idxT ⟨a + 1, by omega⟩
    let s2 := planarSlope p idxT ⟨a, by omega⟩ * planarSlope p idxT ⟨a + 1, by omega⟩
    elimFrontR [(s1, s2)] (takeTailR (a := a) (b := b) t f) =
      takeTailR (a := a) (b := b) (t + 1) (elimOneLeftR p ⟨t, ht⟩ f) := by
  intro idxT s1 s2
  rw [takeTailR_eq_cons_three ht]
  simp only [elimFrontR]
  refine List.ext_getElem (by simp [takeTailR]; omega) fun q hq1 _ => ?_
  rcases q with _ | _ | q
  · simp only [List.getElem_cons_zero, takeTailR, List.getElem_map, List.getElem_finRange,
      Fin.val_cast]
    rw [elimOneLeftR_eq p haxL haxU ⟨t, ht⟩]
    have h0 : ¬ t + 1 + 0 = t := by omega
    have h1 : t + 1 + 0 = t + 1 := by omega
    simp only [h0, h1, ↓reduceIte]
    rfl
  · simp only [List.getElem_cons_succ, List.getElem_cons_zero, takeTailR, List.getElem_map,
      List.getElem_finRange, Fin.val_cast]
    rw [elimOneLeftR_eq p haxL haxU ⟨t, ht⟩]
    have h0 : ¬ t + 1 + 1 = t := by omega
    have h1 : ¬ t + 1 + 1 = t + 1 := by omega
    have h2 : t + 1 + 1 = t + 2 := by omega
    simp only [h0, h1, h2, ↓reduceIte]
    rfl
  · simp only [List.getElem_cons_succ, takeTailR, List.getElem_map, List.getElem_finRange,
      Fin.val_cast]
    rw [elimOneLeftR_eq p haxL haxU ⟨t, ht⟩]
    have h0 : ¬ t + 1 + (q + 2) = t := by omega
    have h1 : ¬ t + 1 + (q + 2) = t + 1 := by omega
    have h2 : ¬ t + 1 + (q + 2) = t + 2 := by omega
    simp only [h0, h1, h2, ↓reduceIte]
    exact congrArg f (Fin.ext (by dsimp; omega))

private lemma takeTailR_elimFrontR {a b : ℕ} (p : Fin (a + 2 + b) → Fin 3 → ℝ)
    (haxL : ∀ i : Fin a, p ⟨i.1, by omega⟩ 0 = 0)
    (haxU : ∀ k : Fin b, p ⟨a + 2 + k.1, by omega⟩ 0 = 0)
    (lPairs : List (ℝ × ℝ))
    (hl : ∀ t (ht : t < a), lPairs[t]? = some
      (planarSlope p ⟨t, by omega⟩ ⟨a, by omega⟩ + planarSlope p ⟨t, by omega⟩ ⟨a + 1, by omega⟩,
       planarSlope p ⟨t, by omega⟩ ⟨a, by omega⟩ * planarSlope p ⟨t, by omega⟩ ⟨a + 1, by omega⟩))
    (r : Fin (a + 2 + b) → ℝ) :
    ∀ t (ht : t ≤ a),
      elimFrontR (lPairs.take t) (takeTailR (a := a) (b := b) 0 r) =
        takeTailR (a := a) (b := b) t (elimLeftLoopR p t ht r)
  | 0, _ => by simp [elimFrontR, elimLeftLoopR]
  | t + 1, ht => by
    have hprev := takeTailR_elimFrontR p haxL haxU lPairs hl r t (by omega)
    have hsome := hl t (by omega)
    rw [List.take_add_one, hsome, Option.toList_some, elimFrontR_append, hprev]
    exact takeTailR_elimStep p haxL haxU t (by omega) _

private lemma takeTailR_reverse_eq {a b : ℕ} (f : Fin (a + 2 + b) → ℝ) :
    (takeTailR (a := a) (b := b) a f).reverse = takeRevFromR (a := a) (b := b) (2 + b) le_rfl f := by
  have hlen : (takeTailR (a := a) (b := b) a f).reverse.length =
      (takeRevFromR (a := a) (b := b) (2 + b) le_rfl f).length := by
    rw [List.length_reverse]
    simp [takeTailR, takeRevFromR]
    omega
  refine List.ext_getElem hlen fun q hq1 hq2 => ?_
  have hqb : q < 2 + b := by simpa [takeRevFromR] using hq2
  simp only [List.getElem_reverse, takeTailR, takeRevFromR, List.length_map, List.length_finRange,
    List.getElem_map, List.getElem_finRange, Fin.val_cast]
  exact congrArg f (Fin.ext (by dsimp; omega))

private lemma takeRevFromR_eq_cons_three {a b s : ℕ} (hs : s < b) (f : Fin (a + 2 + b) → ℝ) :
    takeRevFromR (a := a) (b := b) (2 + b - s) (by omega) f =
      f ⟨a + 2 + (b - 1 - s), by omega⟩ ::
        f ⟨a + (b - 1 - s) + 1, by omega⟩ ::
        f ⟨a + (b - 1 - s), by omega⟩ ::
        takeRevFromR (a := a) (b := b) (2 + b - s - 3) (by omega) f := by
  refine List.ext_getElem (by simp [takeRevFromR]; omega) fun q hq1 _ => ?_
  rcases q with _ | _ | _ | q
  · simp only [List.getElem_cons_zero, takeRevFromR, List.getElem_map, List.getElem_finRange,
      Fin.val_cast]
    exact congrArg f (Fin.ext (by dsimp; omega))
  · simp only [List.getElem_cons_succ, List.getElem_cons_zero, takeRevFromR, List.getElem_map,
      List.getElem_finRange, Fin.val_cast]
    exact congrArg f (Fin.ext (by dsimp; omega))
  · simp only [List.getElem_cons_succ, List.getElem_cons_zero, takeRevFromR, List.getElem_map,
      List.getElem_finRange, Fin.val_cast]
    exact congrArg f (Fin.ext (by dsimp; omega))
  · simp only [List.getElem_cons_succ, takeRevFromR, List.getElem_map, List.getElem_finRange,
      Fin.val_cast]
    exact congrArg f (Fin.ext (by dsimp; omega))

private lemma takeRevFromR_elimStep {a b : ℕ} (p : Fin (a + 2 + b) → Fin 3 → ℝ)
    (haxL : ∀ i : Fin a, p ⟨i.1, by omega⟩ 0 = 0)
    (haxU : ∀ k : Fin b, p ⟨a + 2 + k.1, by omega⟩ 0 = 0)
    (s : ℕ) (hs : s < b) (f : Fin (a + 2 + b) → ℝ) :
    let idxK : Fin (a + 2 + b) := ⟨a + 2 + (b - 1 - s), by omega⟩
    let u1 := -(planarSlope p ⟨a, by omega⟩ idxK + planarSlope p ⟨a + 1, by omega⟩ idxK)
    let u0 := planarSlope p ⟨a, by omega⟩ idxK * planarSlope p ⟨a + 1, by omega⟩ idxK
    elimFrontR [(u1, u0)] (takeRevFromR (a := a) (b := b) (2 + b - s) (by omega) f) =
      takeRevFromR (a := a) (b := b) (2 + b - (s + 1)) (by omega)
        (elimOneRightR p ⟨b - 1 - s, by omega⟩ f) := by
  intro idxK u1 u0
  rw [takeRevFromR_eq_cons_three hs]
  simp only [elimFrontR]
  refine List.ext_getElem (by simp [takeRevFromR]; omega) fun q hq1 hq2 => ?_
  have hqb : q < 2 + b - (s + 1) := by simpa [takeRevFromR] using hq2
  rcases q with _ | _ | q
  · simp only [List.getElem_cons_zero, takeRevFromR, List.getElem_map, List.getElem_finRange,
      Fin.val_cast]
    rw [elimOneRightR_eq p haxL haxU ⟨b - 1 - s, by omega⟩]
    dsimp only
    have hb : a + (2 + b - (s + 1)) - 1 - 0 = a + (b - 1 - s) + 1 := by omega
    have hne : ¬ a + (b - 1 - s) + 1 = a + (b - 1 - s) := by omega
    simp only [hb, hne, ↓reduceIte, u1, idxK]
  · simp only [List.getElem_cons_succ, List.getElem_cons_zero, takeRevFromR, List.getElem_map,
      List.getElem_finRange, Fin.val_cast]
    rw [elimOneRightR_eq p haxL haxU ⟨b - 1 - s, by omega⟩]
    dsimp only
    have ha : a + (2 + b - (s + 1)) - 1 - (0 + 1) = a + (b - 1 - s) := by omega
    simp only [ha, ↓reduceIte, u0, idxK]
  · simp only [List.getElem_cons_succ, takeRevFromR, List.getElem_map, List.getElem_finRange,
      Fin.val_cast]
    rw [elimOneRightR_eq p haxL haxU ⟨b - 1 - s, by omega⟩]
    dsimp only
    have ha : ¬ a + (2 + b - (s + 1)) - 1 - (q + 2) = a + (b - 1 - s) := by omega
    have hb : ¬ a + (2 + b - (s + 1)) - 1 - (q + 2) = a + (b - 1 - s) + 1 := by omega
    have hc : ¬ a + (2 + b - (s + 1)) - 1 - (q + 2) = a + (b - 1 - s) + 2 := by omega
    simp only [ha, hb, hc, ↓reduceIte]
    exact congrArg f (Fin.ext (by dsimp; omega))

private lemma takeRevFromR_elimFrontR {a b : ℕ} (p : Fin (a + 2 + b) → Fin 3 → ℝ)
    (haxL : ∀ i : Fin a, p ⟨i.1, by omega⟩ 0 = 0)
    (haxU : ∀ k : Fin b, p ⟨a + 2 + k.1, by omega⟩ 0 = 0)
    (uPairsRev : List (ℝ × ℝ))
    (hu : ∀ s (hs : s < b), uPairsRev[s]? = some
      (-(planarSlope p ⟨a, by omega⟩ ⟨a + 2 + (b - 1 - s), by omega⟩ +
          planarSlope p ⟨a + 1, by omega⟩ ⟨a + 2 + (b - 1 - s), by omega⟩),
       planarSlope p ⟨a, by omega⟩ ⟨a + 2 + (b - 1 - s), by omega⟩ *
          planarSlope p ⟨a + 1, by omega⟩ ⟨a + 2 + (b - 1 - s), by omega⟩))
    (r : Fin (a + 2 + b) → ℝ) :
    ∀ s (hs : s ≤ b),
      elimFrontR (uPairsRev.take s) (takeRevFromR (a := a) (b := b) (2 + b) le_rfl r) =
        takeRevFromR (a := a) (b := b) (2 + b - s) (by omega) (elimRightPrefixR p s hs r)
  | 0, _ => by simp [elimFrontR, elimRightPrefixR]
  | s + 1, hs => by
    have hprev := takeRevFromR_elimFrontR p haxL haxU uPairsRev hu r s (by omega)
    have hsome := hu s (by omega)
    rw [List.take_add_one, hsome, Option.toList_some, elimFrontR_append, hprev]
    exact takeRevFromR_elimStep p haxL haxU s (by omega) _

theorem planarMat_det_eq_elimFront {a b : ℕ} (p : Fin (a + 2 + b) → Fin 3 → ℝ)
    (haxL : ∀ i : Fin a, p ⟨i.1, by omega⟩ 0 = 0)
    (haxU : ∀ k : Fin b, p ⟨a + 2 + k.1, by omega⟩ 0 = 0)
    (lPairs uPairsRev : List (ℝ × ℝ))
    (hlenL : lPairs.length = a) (hlenU : uPairsRev.length = b)
    (hl : ∀ t (ht : t < a), lPairs[t]? = some
      (planarSlope p ⟨t, by omega⟩ ⟨a, by omega⟩ + planarSlope p ⟨t, by omega⟩ ⟨a + 1, by omega⟩,
       planarSlope p ⟨t, by omega⟩ ⟨a, by omega⟩ * planarSlope p ⟨t, by omega⟩ ⟨a + 1, by omega⟩))
    (hu : ∀ s (hs : s < b), uPairsRev[s]? = some
      (-(planarSlope p ⟨a, by omega⟩ ⟨a + 2 + (b - 1 - s), by omega⟩ +
          planarSlope p ⟨a + 1, by omega⟩ ⟨a + 2 + (b - 1 - s), by omega⟩),
       planarSlope p ⟨a, by omega⟩ ⟨a + 2 + (b - 1 - s), by omega⟩ *
          planarSlope p ⟨a + 1, by omega⟩ ⟨a + 2 + (b - 1 - s), by omega⟩)) :
    let curA := elimFrontR uPairsRev (elimFrontR lPairs (List.ofFn (planarMat p ⟨a, by omega⟩))).reverse
    let curB := elimFrontR uPairsRev (elimFrontR lPairs (List.ofFn (planarMat p ⟨a + 1, by omega⟩))).reverse
    (planarMat p).det = curA.getD 1 0 * curB.getD 0 0 - curA.getD 0 0 * curB.getD 1 0 := by
  intro curA curB
  let idxA : Fin (a + 2 + b) := ⟨a, by omega⟩
  let idxB : Fin (a + 2 + b) := ⟨a + 1, by omega⟩
  let M := planarMat p
  let rA₁ := elimLeftLoopR p a le_rfl (M idxA)
  let rA₂ := elimRightPrefixR p b le_rfl rA₁
  let rB₁ := elimLeftLoopR p a le_rfl (M idxB)
  let rB₂ := elimRightPrefixR p b le_rfl rB₁
  let N₁ := M.updateRow idxA rA₁
  let N₂ := N₁.updateRow idxA rA₂
  let N₃ := N₂.updateRow idxB rB₁
  let N₄ := N₃.updateRow idxB rB₂
  have hAB : idxA ≠ idxB := Fin.ne_of_val_ne (by dsimp [idxA, idxB]; omega)
  have hM_axL : ∀ j : Fin a, M ⟨j.1, by omega⟩ = planarMat p ⟨j.1, by omega⟩ := fun _ => rfl
  have hN₁_det : N₁.det = M.det := det_updateRow_elimLeftLoopR p M hM_axL (by dsimp [idxA]; omega) a le_rfl
  have hN₁_axU : ∀ k : Fin b, N₁ ⟨a + 2 + k.1, by omega⟩ = planarMat p ⟨a + 2 + k.1, by omega⟩ := by
    intro k
    exact Matrix.updateRow_ne (Fin.ne_of_val_ne (by dsimp [idxA]; omega))
  have hN₂_det : N₂.det = N₁.det := by
    have hsub : N₁ idxA = rA₁ := Matrix.updateRow_self
    dsimp [N₂, rA₂]; rw [← hsub]
    exact det_updateRow_elimRightPrefixR p N₁ hN₁_axU (by dsimp [idxA]; omega) b le_rfl
  have hN₂_axL : ∀ j : Fin a, N₂ ⟨j.1, by omega⟩ = planarMat p ⟨j.1, by omega⟩ := by
    intro j
    have hne : (⟨j.1, by omega⟩ : Fin (a + 2 + b)) ≠ idxA := Fin.ne_of_val_ne (by dsimp [idxA]; omega)
    dsimp [N₂, N₁]; rw [Matrix.updateRow_ne hne, Matrix.updateRow_ne hne]
  have hN₂_B : N₂ idxB = M idxB := by
    dsimp [N₂, N₁]; rw [Matrix.updateRow_ne hAB.symm, Matrix.updateRow_ne hAB.symm]
  have hN₃_det : N₃.det = N₂.det := by
    dsimp [N₃, rB₁]; rw [← hN₂_B]
    exact det_updateRow_elimLeftLoopR p N₂ hN₂_axL (by dsimp [idxB]; omega) a le_rfl
  have hN₃_axU : ∀ k : Fin b, N₃ ⟨a + 2 + k.1, by omega⟩ = planarMat p ⟨a + 2 + k.1, by omega⟩ := by
    intro k
    have hneB : (⟨a + 2 + k.1, by omega⟩ : Fin (a + 2 + b)) ≠ idxB := Fin.ne_of_val_ne (by dsimp [idxB]; omega)
    have hneA : (⟨a + 2 + k.1, by omega⟩ : Fin (a + 2 + b)) ≠ idxA := Fin.ne_of_val_ne (by dsimp [idxA]; omega)
    dsimp [N₃, N₂, N₁]; rw [Matrix.updateRow_ne hneB, Matrix.updateRow_ne hneA, Matrix.updateRow_ne hneA]
  have hN₄_det : N₄.det = N₃.det := by
    have hsub : N₃ idxB = rB₁ := Matrix.updateRow_self
    dsimp [N₄, rB₂]; rw [← hsub]
    exact det_updateRow_elimRightPrefixR p N₃ hN₃_axU (by dsimp [idxB]; omega) b le_rfl
  have hN₄_ax : ∀ i : Fin (a + 2 + b), i ≠ idxA → i ≠ idxB → N₄ i = planarMat p i := by
    intro i hiA hiB
    dsimp [N₄, N₃, N₂, N₁]
    rw [Matrix.updateRow_ne hiB, Matrix.updateRow_ne hiB, Matrix.updateRow_ne hiA, Matrix.updateRow_ne hiA]
  have hN₄_A : N₄ idxA = rA₂ := by
    dsimp [N₄, N₃, N₂]; rw [Matrix.updateRow_ne hAB, Matrix.updateRow_ne hAB, Matrix.updateRow_self]
  have hN₄_B : N₄ idxB = rB₂ := Matrix.updateRow_self
  have hbanded : N₄.det = rA₂ idxA * rB₂ idxB - rA₂ idxB * rB₂ idxA := by
    have hL_diag : ∀ i : Fin a, N₄ ⟨i.1, by omega⟩ ⟨i.1, by omega⟩ = 1 := by
      intro i
      rw [show N₄ ⟨i.1, by omega⟩ = planarMat p ⟨i.1, by omega⟩ from
        hN₄_ax _ (Fin.ne_of_val_ne (by dsimp [idxA]; omega)) (Fin.ne_of_val_ne (by dsimp [idxB]; omega))]
      rw [planarMat_axial_lower p haxL haxU i]; simp
    have hL_zero : ∀ i j : Fin a, j < i → N₄ ⟨i.1, by omega⟩ ⟨j.1, by omega⟩ = 0 := by
      intro i j hij
      rw [show N₄ ⟨i.1, by omega⟩ = planarMat p ⟨i.1, by omega⟩ from
        hN₄_ax _ (Fin.ne_of_val_ne (by dsimp [idxA]; omega)) (Fin.ne_of_val_ne (by dsimp [idxB]; omega))]
      rw [planarMat_axial_lower p haxL haxU i]
      have h0 : ¬ j.1 = i.1 := by omega
      have h1 : ¬ j.1 = i.1 + 1 := by omega
      have h2 : ¬ j.1 = i.1 + 2 := by omega
      simp [h0, h1, h2]
    have hM_zeroL : ∀ (m : Fin 2) (j : Fin a), N₄ ⟨a + m.1, by omega⟩ ⟨j.1, by omega⟩ = 0 := by
      intro m j
      fin_cases m
      · change N₄ idxA ⟨j.1, by omega⟩ = 0
        rw [hN₄_A]
        exact elimRightPrefixR_zero_left p haxL haxU rA₁
          (fun j' => elimLeftLoopR_zero_lt p haxL haxU a le_rfl (M idxA) j'.1 j'.isLt) b le_rfl j
      · change N₄ idxB ⟨j.1, by omega⟩ = 0
        rw [hN₄_B]
        exact elimRightPrefixR_zero_left p haxL haxU rB₁
          (fun j' => elimLeftLoopR_zero_lt p haxL haxU a le_rfl (M idxB) j'.1 j'.isLt) b le_rfl j
    have hM_zeroU : ∀ (m : Fin 2) (j : Fin b), N₄ ⟨a + m.1, by omega⟩ ⟨a + 2 + j.1, by omega⟩ = 0 := by
      intro m j
      fin_cases m
      · change N₄ idxA ⟨a + 2 + j.1, by omega⟩ = 0
        rw [hN₄_A]
        exact elimRightPrefixR_zero_right p haxL haxU rA₁ b le_rfl j (by simp)
      · change N₄ idxB ⟨a + 2 + j.1, by omega⟩ = 0
        rw [hN₄_B]
        exact elimRightPrefixR_zero_right p haxL haxU rB₁ b le_rfl j (by simp)
    have hU_diag : ∀ j : Fin b, N₄ ⟨a + 2 + j.1, by omega⟩ ⟨a + 2 + j.1, by omega⟩ = 1 := by
      intro j
      rw [show N₄ ⟨a + 2 + j.1, by omega⟩ = planarMat p ⟨a + 2 + j.1, by omega⟩ from
        hN₄_ax _ (Fin.ne_of_val_ne (by dsimp [idxA]; omega)) (Fin.ne_of_val_ne (by dsimp [idxB]; omega))]
      rw [planarMat_axial_upper p haxL haxU j]
      have h0 : ¬ a + 2 + j.1 = a + j.1 := by omega
      have h1 : ¬ a + 2 + j.1 = a + j.1 + 1 := by omega
      have h2 : a + 2 + j.1 = a + j.1 + 2 := by omega
      simp [h2]
    have hU_zero : ∀ i j : Fin b, i < j → N₄ ⟨a + 2 + i.1, by omega⟩ ⟨a + 2 + j.1, by omega⟩ = 0 := by
      intro i j hij
      rw [show N₄ ⟨a + 2 + i.1, by omega⟩ = planarMat p ⟨a + 2 + i.1, by omega⟩ from
        hN₄_ax _ (Fin.ne_of_val_ne (by dsimp [idxA]; omega)) (Fin.ne_of_val_ne (by dsimp [idxB]; omega))]
      rw [planarMat_axial_upper p haxL haxU i]
      have h0 : ¬ a + 2 + j.1 = a + i.1 := by omega
      have h1 : ¬ a + 2 + j.1 = a + i.1 + 1 := by omega
      have h2 : ¬ a + 2 + j.1 = a + i.1 + 2 := by omega
      simp [h0, h1, h2]
    have hLU_zero : ∀ (i : Fin a) (j : Fin b), N₄ ⟨i.1, by omega⟩ ⟨a + 2 + j.1, by omega⟩ = 0 := by
      intro i j
      rw [show N₄ ⟨i.1, by omega⟩ = planarMat p ⟨i.1, by omega⟩ from
        hN₄_ax _ (Fin.ne_of_val_ne (by dsimp [idxA]; omega)) (Fin.ne_of_val_ne (by dsimp [idxB]; omega))]
      rw [planarMat_axial_lower p haxL haxU i]
      have h0 : ¬ a + 2 + j.1 = i.1 := by omega
      have h1 : ¬ a + 2 + j.1 = i.1 + 1 := by omega
      have h2 : ¬ a + 2 + j.1 = i.1 + 2 := by omega
      simp [h0, h1, h2]
    have hd := det_eq_two_by_two_of_banded N₄ hL_diag hL_zero hM_zeroL hM_zeroU hU_diag hU_zero hLU_zero
    simpa [hN₄_A, hN₄_B, idxA, idxB] using hd
  have htakeL : lPairs.take a = lPairs := List.take_of_length_le hlenL.le
  have htakeU : uPairsRev.take b = uPairsRev := List.take_of_length_le hlenU.le
  have hcurA : curA = takeRevFromR (a := a) (b := b) 2 (by omega) rA₂ := by
    have hof : List.ofFn (M idxA) = takeTailR (a := a) (b := b) 0 (M idxA) := by
      refine List.ext_getElem (by simp [takeTailR]) fun k hk1 _ => ?_
      simp [takeTailR]
    have h1 := takeTailR_elimFrontR p haxL haxU lPairs hl (M idxA) a le_rfl
    rw [htakeL] at h1
    have h2 := takeRevFromR_elimFrontR p haxL haxU uPairsRev hu rA₁ b le_rfl
    rw [htakeU] at h2
    calc curA
      _ = elimFrontR uPairsRev (elimFrontR lPairs (List.ofFn (M idxA))).reverse := rfl
      _ = elimFrontR uPairsRev (elimFrontR lPairs (takeTailR 0 (M idxA))).reverse := by rw [hof]
      _ = elimFrontR uPairsRev (takeTailR a rA₁).reverse := by rw [h1]
      _ = elimFrontR uPairsRev (takeRevFromR (2 + b) le_rfl rA₁) := by rw [takeTailR_reverse_eq]
      _ = takeRevFromR 2 (by omega) rA₂ := by simpa [rA₂] using h2
  have hcurB : curB = takeRevFromR (a := a) (b := b) 2 (by omega) rB₂ := by
    have hof : List.ofFn (M idxB) = takeTailR (a := a) (b := b) 0 (M idxB) := by
      refine List.ext_getElem (by simp [takeTailR]) fun k hk1 _ => ?_
      simp [takeTailR]
    have h1 := takeTailR_elimFrontR p haxL haxU lPairs hl (M idxB) a le_rfl
    rw [htakeL] at h1
    have h2 := takeRevFromR_elimFrontR p haxL haxU uPairsRev hu rB₁ b le_rfl
    rw [htakeU] at h2
    calc curB
      _ = elimFrontR uPairsRev (elimFrontR lPairs (List.ofFn (M idxB))).reverse := rfl
      _ = elimFrontR uPairsRev (elimFrontR lPairs (takeTailR 0 (M idxB))).reverse := by rw [hof]
      _ = elimFrontR uPairsRev (takeTailR a rB₁).reverse := by rw [h1]
      _ = elimFrontR uPairsRev (takeRevFromR (2 + b) le_rfl rB₁) := by rw [takeTailR_reverse_eq]
      _ = takeRevFromR 2 (by omega) rB₂ := by simpa [rB₂] using h2
  have hcurA0 : curA.getD 0 0 = rA₂ idxB := by
    rw [hcurA]; simp [takeRevFromR, idxB]
  have hcurA1 : curA.getD 1 0 = rA₂ idxA := by
    rw [hcurA]; simp [takeRevFromR, idxA]
  have hcurB0 : curB.getD 0 0 = rB₂ idxB := by
    rw [hcurB]; simp [takeRevFromR, idxB]
  have hcurB1 : curB.getD 1 0 = rB₂ idxA := by
    rw [hcurB]; simp [takeRevFromR, idxA]
  rw [← hN₁_det, ← hN₂_det, ← hN₃_det, ← hN₄_det, hbanded, hcurA0, hcurA1, hcurB0, hcurB1]

end RowEliminationDet

end AxialTwoOffAxisReduction

section Conjectures1And2Disproof

private lemma forall2_map_same {α β γ : Type*} {R : β → γ → Prop}
    {l : List α} {f : α → β} {g : α → γ} (h : ∀ x ∈ l, R (f x) (g x)) :
    List.Forall₂ R (l.map f) (l.map g) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    exact List.Forall₂.cons (h x (by simp)) (ih fun y hy => h y (by simp [hy]))

private lemma forall2_reverseAux {α β : Type*} {R : α → β → Prop}
    {xs : List α} {ys : List β} (h : List.Forall₂ R xs ys) :
    ∀ {ax : List α} {ay : List β}, List.Forall₂ R ax ay →
      List.Forall₂ R (List.reverseAux xs ax) (List.reverseAux ys ay) := by
  induction h with
  | nil => intro ax ay hacc; exact hacc
  | cons hr _ ih => intro ax ay hacc; exact ih (List.Forall₂.cons hr hacc)

private lemma forall2_reverse {α β : Type*} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) : List.Forall₂ R xs.reverse ys.reverse :=
  forall2_reverseAux h List.Forall₂.nil

def pts63X (i : Fin 63) : ℤ :=
  if i.1 < 31 then 0 else if i.1 = 31 then 3097 else if i.1 = 32 then 80093 else 0

def pts63Z (i : Fin 63) : ℤ :=
  if i.1 < 31 then i.1
  else if i.1 = 31 then 38539
  else if i.1 = 32 then 40720
  else 40830 + ((i.1 : ℤ) - 33)

lemma pts63Z_strictMono : StrictMono pts63Z := by
  intro i j hij
  have hi := i.2
  have hj := j.2
  have hlt : i.1 < j.1 := hij
  dsimp [pts63Z]
  split_ifs <;> omega

noncomputable def x63Path : ℝ → DistinctPoints 63 :=
  planarPath pts63X pts63Z pts63Z_strictMono

def S63 : ℤ := 100000000000000000000000000000000000

private def cLA_rho : List ℤ := [
  3866323744851173220231438558648652443724, 3866224066191715174632515115565423650839, 3866124387548853814037768502197986139321, 3866024708922590422196136015082078919050, 3865925030312926282988741395925990077625, 3865825351719862680428911818334974540570, 3865725673143400898662194877150931619597, 3865625994583542221966375580407811337405, 3865526316040287934751493343903218613471, 3865426637513639321559858988386684491275, 3865326959003597667066071739365073683377, 3865227280510164256077036229525597806832, 3865127602033340373531979503776903777438, 3865027923573127304502468026908706927410, 3864928245129526334192424693870438507148, 3864828566702538747938145842669377327886, 3864728888292165831208318269888735398156, 3864629209898408869604036248826167503143, 3864529531521269148858818550253174772195, 3864429853160747954838625465795872375962, 3864330174816846573541875833937591590849, 3864230496489566291099464068643786564723, 3864130818178908393774777190609716214088, 3864031139884874167963711861131371779219, 3863931461607464900194691418600120660072, 3863831783346681877128682917621537252123, 3863732105102526385559214170758891597629, 3863632426874999712412390792901766764210, 3863532748664103144746913248260275959036, 3863433070469837969754093899985350483323, 3863333392292205474757874062415569728306]

private def cLB_rho : List ℤ := [
  8984991401776631639115624530196730587955, 8984946082197711218494594761113079688399, 8984900763503178502982582769018848368966, 8984855445693046874863755030019939440235, 8984810128767329716431109711831283384374, 8984764812726040409986463723757774844418, 8984719497569192337840439766070959325864, 8984674183296798882312453378781475088293, 8984628869908873425730699989807255207710, 8984583557405429350432141962537494793196, 8984538245786480038762495642792388344448, 8984492935052038873076218405178642239712, 8984447625202119235736495698840767346562, 8984402316236734509115228092608156750932, 8984357008155898075593018319537953602752, 8984311700959623317559158320853714079483, 8984266394647923617411616289279870471798, 8984221089220812357557023711771999398605, 8984175784678302920410662411642900161554, 8984130481020408688396451590084488252114, 8984085178247143043946934867085509027269, 8984039876358519369503267321745076572803, 8983994575354551047515202531982042776137, 8983949275235251460441079613640201633575, 8983903976000633990747810258989333819822, 8983858677650712020910865774622096550532, 8983813380185498933414264118746763771645, 8983768083605008110750556937875821712180, 8983722787909252935420816602910424840129, 8983677493098246789934623244620717264026, 8983632199172003056810051788522024625746]

private def cAB_rho : ℤ := 7702688346934464932013151924220254266539

private def cAU_rho : List ℤ := [
  385228373825189569200114674423694584774, 385287853429095270252235604540536722122, 385347349802746145732014138641960553235, 385406862938375813245705564416573249029, 385466392828220499329615750898202761496, 385525939464519040811183992374450296766, 385585502839512886165541195532298657777, 385645082945446096867548900724627081707, 385704679774565348739324627861629363490, 385764293319119933293259037034443597937, 385823923571361759070530393564824620186, 385883570523545352975121826744469964084, 385943234167927861603346871080692633197, 386002914496769052568888778401564887404, 386062611502331315823359088693482243014, 386122325176879664972380947047361574686, 386182055512681738587202653576437156909, 386241802502007801511846932638899210257, 386301566137130746165801407152476496395, 386361346410326093842255763225543164233, 386421143313871996001891089750475770124, 386480956840049235562226877009844514598, 386540786981141228182531157734638547910, 386600633729434023544299273426143941726, 386660497077216306627306748109359803531, 386720377016779398981241751025998176568, 386780273540417259992922629099211927466, 386840186640426488149105989310276835910, 386900116309106322294890810419564578667, 386960062538758642887724062740327210029]

private def cBU_rho : List ℤ := [
  8009307553715239870280483404977890806666, 8009307691679724698975731630036233990647, 8009307830892754492818825107859027210652, 8009307971354329186705364786593290729023, 8009308113064448714947061393138196057395, 8009308256023113011271735586743657018244, 8009308400230322008823318113974209769026, 8009308545686075640161849965038180943451, 8009308692390373837263482531482143056931, 8009308840343216531520477765250656315846, 8009308989544603653741208339111295962777, 8009309139994535134150157808444964282436, 8009309291693010902387920774401486385569, 8009309444640030887511203048420488880645, 8009309598835595017992821818117560535711, 8009309754279703221721705814535694025338, 8009309910972355426002895480762007850133, 8009310068913551557557543141909747508848, 8009310228103291542522913176465564995659, 8009310388541575306452382189002075687750, 8009310550228402774315439184255691680882, 8009310713163773870497685742569730623181, 8009310877347688518800836196702799089925, 8009311042780146642442717810002449534669, 8009311209461148164057270955944109844591, 8009311377390693005694549299035284520503, 8009311546568781088820719977085026494504, 8009311716995412334318063784838678590833, 8009311888670586662484975358977883627991, 8009312061594303993035963364485862152797]

def cLA_lit : List FpIv := [
  ⟨4011541766604204143183260784195170, 4011541766604204143183260784195171⟩, ⟨4011645525255141954315503895842315, 4011645525255141954315503895842316⟩, ⟨4011749289265035207545528639969693, 4011749289265035207545528639969694⟩, ⟨4011853058634298416576046200219218, 4011853058634298416576046200219219⟩, ⟨4011956833363346137791861777846327, 4011956833363346137791861777846328⟩, ⟨4012060613452592970265359488206180, 4012060613452592970265359488206181⟩, ⟨4012164398902453555761988101689253, 4012164398902453555761988101689254⟩, ⟨4012268189713342578745747629257777, 4012268189713342578745747629257778⟩, ⟨4012371985885674766384676752734457, 4012371985885674766384676752734458⟩, ⟨4012475787419864888556341099994992, 4012475787419864888556341099994993⟩, ⟨4012579594316327757853322365215913, 4012579594316327757853322365215914⟩, ⟨4012683406575478229588708274329288, 4012683406575478229588708274329289⟩, ⟨4012787224197731201801583395835898, 4012787224197731201801583395835899⟩, ⟨4012891047183501615262520797128488, 4012891047183501615262520797128489⟩, ⟨4012994875533204453479074546476754, 4012994875533204453479074546476755⟩, ⟨4013098709247254742701273060825743, 4013098709247254742701273060825744⟩, ⟨4013202548326067551927113299559379, 4013202548326067551927113299559380⟩, ⟨4013306392770057992908055804380853, 4013306392770057992908055804380854⟩, ⟨4013410242579641220154520585461663, 4013410242579641220154520585461664⟩, ⟨4013514097755232430941383854011099, 4013514097755232430941383854011100⟩, ⟨4013617958297246865313475601418014, 4013617958297246865313475601418015⟩, ⟨4013721824206099806091078025116746, 4013721824206099806091078025116747⟩, ⟨4013825695482206578875424801329097, 4013825695482206578875424801329098⟩, ⟨4013929572125982552054201204834284, 4013929572125982552054201204834285⟩, ⟨4014033454137843136807045075918844, 4014033454137843136807045075918845⟩, ⟨4014137341518203787111048634658460, 4014137341518203787111048634658461⟩, ⟨4014241234267479999746261142683757, 4014241234267479999746261142683758⟩, ⟨4014345132386087314301192412582100, 4014345132386087314301192412582101⟩, ⟨4014449035874441313178317165087490, 4014449035874441313178317165087491⟩, ⟨4014552944732957621599580234210682, 4014552944732957621599580234210683⟩, ⟨4014656858962051907611902620461649, 4014656858962051907611902620461650⟩]

def cLB_lit : List FpIv := [
  ⟨61341083512624469543101451190450233, 61341083512624469543101451190450234⟩, ⟨61341766224235716211087045823144091, 61341766224235716211087045823144092⟩, ⟨61342448946888972856336793090767587, 61342448946888972856336793090767588⟩, ⟨61343131680584406563167255940218738, 61343131680584406563167255940218739⟩, ⟨61343814425322184416005265277006522, 61343814425322184416005265277006523⟩, ⟨61344497181102473499387758277974040, 61344497181102473499387758277974041⟩, ⟨61345179947925440897961616696477336, 61345179947925440897961616696477337⟩, ⟨61345862725791253696483505160019915, 61345862725791253696483505160019916⟩, ⟨61346545514700078979819709460343041, 61346545514700078979819709460343042⟩, ⟨61347228314652083832945974835971867, 61347228314652083832945974835971868⟩, ⟨61347911125647435340947344247217464, 61347911125647435340947344247217465⟩, ⟨61348593947686300589017996643634802, 61348593947686300589017996643634803⟩, ⟨61349276780768846662461085223936765, 61349276780768846662461085223936766⟩, ⟨61349959624895240646688575688364235, 61349959624895240646688575688364236⟩, ⟨61350642480065649627221084483512336, 61350642480065649627221084483512337⟩, ⟨61351325346280240689687717039612876, 61351325346280240689687717039612877⟩, ⟨61352008223539180919825906000273063, 61352008223539180919825906000273064⟩, ⟨61352691111842637403481249444670562, 61352691111842637403481249444670563⟩, ⟨61353374011190777226607349102204938, 61353374011190777226607349102204939⟩, ⟨61354056921583767475265648559605561, 61354056921583767475265648559605562⟩, ⟨61354739843021775235625271460496036, 61354739843021775235625271460496037⟩, ⟨61355422775504967593962859697415211, 61355422775504967593962859697415212⟩, ⟨61356105719033511636662411596294841, 61356105719033511636662411596294842⟩, ⟨61356788673607574450215120093393949, 61356788673607574450215120093393950⟩, ⟨61357471639227323121219210904689970, 61357471639227323121219210904689971⟩, ⟨61358154615892924736379780687726724, 61358154615892924736379780687726725⟩, ⟨61358837603604546382508635195919290, 61358837603604546382508635195919291⟩, ⟨61359520602362355146524127425315841, 61359520602362355146524127425315842⟩, ⟨61360203612166518115450995753816498, 61360203612166518115450995753816499⟩, ⟨61360886633017202376420202072849278, 61360886633017202376420202072849279⟩, ⟨61361569664914575016668769911503185, 61361569664914575016668769911503186⟩]

def cAU_lit : List FpIv := [
  ⟨-50412778115979841524092565199772227, -50412778115979841524092565199772226⟩, ⟨-50399694358765021069498096396686059, -50399694358765021069498096396686058⟩, ⟨-50386616016385581443982608537927205, -50386616016385581443982608537927204⟩, ⟨-50373543086333811186860046631118260, -50373543086333811186860046631118259⟩, ⟨-50360475566102841243014449757249843, -50360475566102841243014449757249842⟩, ⟨-50347413453186645402384240353390474, -50347413453186645402384240353390473⟩, ⟨-50334356745080040737985532945527497, -50334356745080040737985532945527496⟩, ⟨-50321305439278688042476235300170192, -50321305439278688042476235300170191⟩, ⟨-50308259533279092263262714840694015, -50308259533279092263262714840694014⟩, ⟨-50295219024578602936150803046316952, -50295219024578602936150803046316951⟩, ⟨-50282183910675414617542910418089965, -50282183910675414617542910418089964⟩, ⟨-50269154189068567315183024457368410, -50269154189068567315183024457368409⟩, ⟨-50256129857257946917451362957924648, -50256129857257946917451362957924647⟩, ⟨-50243110912744285621210454763178847, -50243110912744285621210454763178846⟩, ⟨-50230097353029162358204419984979737, -50230097353029162358204419984979736⟩, ⟨-50217089175615003220013221519974678, -50217089175615003220013221519974677⟩, ⟨-50204086378005081881563659533883487, -50204086378005081881563659533883486⟩, ⟨-50191088957703520023198880412947760, -50191088957703520023198880412947759⟩, ⟨-50178096912215287751308171505481594, -50178096912215287751308171505481593⟩, ⟨-50165110239046204017518812794815359, -50165110239046204017518812794815358⟩, ⟨-50152128935702937036451756458016071, -50152128935702937036451756458016070⟩, ⟨-50139152999693004702042905072600748, -50139152999693004702042905072600747⟩, ⟨-50126182428524775002431759036047320, -50126182428524775002431759036047319⟩, ⟨-50113217219707466433419203560266046, -50113217219707466433419203560266045⟩, ⟨-50100257370751148410496205395337360, -50100257370751148410496205395337359⟩, ⟨-50087302879166741679445189223764346, -50087302879166741679445189223764345⟩, ⟨-50074353742466018725515863448244084, -50074353742466018725515863448244083⟩, ⟨-50061409958161604181177264872546606, -50061409958161604181177264872546605⟩, ⟨-50048471523766975232447791546517462, -50048471523766975232447791546517461⟩, ⟨-50035538436796462023804992812504750, -50035538436796462023804992812504749⟩]

def cBU_lit : List FpIv := [
  ⟨-99862753969950431002465676213625296, -99862753969950431002465676213625295⟩, ⟨-99861507143941726480163455358598555, -99861507143941726480163455358598554⟩, ⟨-99860260333521712169837877315858156, -99860260333521712169837877315858155⟩, ⟨-99859013538690387258628903731827885, -99859013538690387258628903731827884⟩, ⟨-99857766759447750926386343290152649, -99857766759447750926386343290152648⟩, ⟨-99856519995793802345669853629451476, -99856519995793802345669853629451475⟩, ⟨-99855273247728540681748943278116812, -99855273247728540681748943278116811⟩, ⟨-99854026515251965092602973606160101, -99854026515251965092602973606160100⟩, ⟨-99852779798364074728921160794103643, -99852779798364074728921160794103642⟩, ⟨-99851533097064868734102577818918711, -99851533097064868734102577818918710⟩, ⟨-99850286411354346244256156457009926, -99850286411354346244256156457009925⟩, ⟨-99849039741232506388200689304245868, -99849039741232506388200689304245867⟩, ⟨-99847793086699348287464831813035926, -99847793086699348287464831813035925⟩, ⟨-99846546447754871056287104346453359, -99846546447754871056287104346453358⟩, ⟨-99845299824399073801615894249404574, -99845299824399073801615894249404573⟩, ⟨-99844053216631955623109457936844594, -99844053216631955623109457936844593⟩, ⟨-99842806624453515613135922999038716, -99842806624453515613135922999038715⟩, ⟨-99841560047863752856773290323870345, -99841560047863752856773290323870344⟩, ⟨-99840313486862666431809436236194986, -99840313486862666431809436236194985⟩, ⟨-99839066941450255408742114654240392, -99839066941450255408742114654240391⟩, ⟨-99837820411626518850778959263052848, -99837820411626518850778959263052847⟩, ⟨-99836573897391455813837485704989583, -99836573897391455813837485704989582⟩, ⟨-99835327398745065346545093787257303, -99835327398745065346545093787257302⟩, ⟨-99834080915687346490239069706496817, -99834080915687346490239069706496816⟩, ⟨-99832834448218298278966588290413768, -99832834448218298278966588290413767⟩, ⟨-99831587996337919739484715256455428, -99831587996337919739484715256455427⟩, ⟨-99830341560046209891260409487533574, -99830341560046209891260409487533573⟩, ⟨-99829095139343167746470525324793411, -99829095139343167746470525324793410⟩, ⟨-99827848734228792310001814877428535, -99827848734228792310001814877428534⟩, ⟨-99826602344703082579450930349541935, -99826602344703082579450930349541934⟩]

def cAB_lit : FpIv := ⟨97207495804125732921361524289836540, 97207495804125732921361524289836541⟩

private def rowALit : List FpIv := [
  ⟨-1, 0⟩, ⟨-1, 32⟩, ⟨-273, 32⟩, ⟨-273, 1465⟩, ⟨-5830, 1405⟩,
  ⟨3405, 27042⟩, ⟨-1068142, -1004827⟩, ⟨93508118, 93651659⟩,
  ⟨-7202317385, -7202034909⟩, ⟨473452667133, 473453160270⟩,
  ⟨-26867125327183, -26867124548128⟩, ⟨1327150298139259, 1327150299274246⟩,
  ⟨-57435389731763086, -57435389730210705⟩, ⟨2188581651436562857, 2188581651438587937⟩,
  ⟨-73707385993090280972, -73707385993087730880⟩, ⟨2200028832762557789876, 2200028832762560912411⟩,
  ⟨-58309701784630066427676, -58309701784630062697687⟩, ⟨1373844234344880349093548, 1373844234344880353446235⟩,
  ⟨-28787144377385634564332922, -28787144377385634559362315⟩, ⟨536306495248717229899880532, 536306495248717229905452255⟩,
  ⟨-8875412586638607923645431059, -8875412586638607923639275690⟩, ⟨130273275842818728412431837316, 130273275842818728412438568009⟩,
  ⟨-1692256114132280448864623157466, -1692256114132280448864615842915⟩, ⟨19399642687771418434485230187781, 19399642687771418434485238118081⟩,
  ⟨-195582573116668585847860250558502, -195582573116668585847860241954920⟩, ⟨1726992592350240454546436027814456, 1726992592350240454546436037166169⟩,
  ⟨-13293194195710423056175632608166095, -13293194195710423056175632597994819⟩, ⟨88731771773504025061032648702308063, 88731771773504025061032648713342959⟩,
  ⟨-510766611310601496531707014834208783, -510766611310601496531707014822304796⟩, ⟨2521226248620101637113541779805093782, 2521226248620101637113541779817844976⟩,
  ⟨-10615494589343712558838927058993802017, -10615494589343712558838927058980224925⟩, ⟨37952622146875163334003725791451267961, 37952622146875163334003725791465678700⟩,
  ⟨-114828887628500228747109427782786040229, -114828887628500228747109427782770743728⟩, ⟨293363275019213551623791178962002125631, 293363275019213551623791178962018398969⟩,
  ⟨-631807277688830634926064445922204333715, -631807277688830634926064445922186991003⟩, ⟨1144321883747205937370277862994394727165, 1144321883747205937370277862994413145554⟩,
  ⟨-1733704411876067732212547157208405428730, -1733704411876067732212547157208386151535⟩, ⟨2169725919670815656550214275600563287430, 2169725919670815656550214275600582854436⟩,
  ⟨-2175608748503514485536204503180844785387, -2175608748503514485536204503180825863616⟩, ⟨1602006480663444978965397094949537433168, 1602006480663444978965397094949554588707⟩,
  ⟨-563736358154110659660047351211256843719, -563736358154110659660047351211242428027⟩, ⟨-588612235332689738258515989327596508827, -588612235332689738258515989327585337930⟩,
  ⟨1460409885258878466443713062511076374348, 1460409885258878466443713062511084376817⟩, ⟨-1825618301413467226226704415056153693070, -1825618301413467226226704415056148390556⟩,
  ⟨1708979489845694134389698161881307273016, 1708979489845694134389698161881310522875⟩, ⟨-1308086971070838327242573930886191168472, -1308086971070838327242573930886189325076⟩,
  ⟨847095640097369081354820442001936077950, 847095640097369081354820442001937046553⟩, ⟨-471760432742841378683488099989484842708, -471760432742841378683488099989484370444⟩,
  ⟨227850433025283211864882356657387522912, 227850433025283211864882356657387737369⟩, ⟨-95822396037663811955828557417294521556, -95822396037663811955828557417294430131⟩,
  ⟨35130302485652708701093242836140278442, 35130302485652708701093242836140315605⟩, ⟨-11216310067102334799995294546433649170, -11216310067102334799995294546433634375⟩,
  ⟨3109406523388941193025278844413309527, 3109406523388941193025278844413315509⟩, ⟨-744748398116380763984521131102572625, -744748398116380763984521131102570089⟩,
  ⟨153010559740220445834749475477803408, 153010559740220445834749475477804546⟩, ⟨-26699162341555384103664793309767933, -26699162341555384103664793309767399⟩,
  ⟨3903481539659388517777337739261746, 3903481539659388517777337739262003⟩, ⟨-469333119230344000753633209273254, -469333119230344000753633209273127⟩,
  ⟨45197807727320187382553753577431, 45197807727320187382553753577494⟩, ⟨-3352187165761198233571713998166, -3352187165761198233571713998136⟩,
  ⟨179771774832307597453562806975, 179771774832307597453562806989⟩, ⟨-6204821255735210013070885684, -6204821255735210013070885678⟩,
  ⟨103502911797250217401503952, 103502911797250217401503954⟩]

private def rowBLit : List FpIv := [
  ⟨25718296907366656322168637274, 25718296907366656322168637277⟩, ⟨-2096318603171057455596725197082, -2096318603171057455596725196949⟩,
  ⟨83979029981406738983901468093785, 83979029981406738983901468095982⟩, ⟨-2203960193786195524489319769899983, -2203960193786195524489319769876377⟩,
  ⟨42617375750259464595702878759869666, 42617375750259464595702878760056640⟩, ⟨-647474356184435986450837889751858799, -647474356184435986450837889750690775⟩,
  ⟨8048407105479852494768056836652415301, 8048407105479852494768056836658430878⟩, ⟨-84168294911469203837229652895897462068, -84168294911469203837229652895871068481⟩,
  ⟨755707428781060436505213562021233845453, 755707428781060436505213562021335180326⟩, ⟨-5915892787347506256687955055282601294308, -5915892787347506256687955055282252576895⟩,
  ⟨40868950618332550952325480340157143788028, 40868950618332550952325480340158244564432⟩, ⟨-251583728550413410750154155722511339495921, -251583728550413410750154155722508076551757⟩,
  ⟨1391009560973866435019503523989307247066474, 1391009560973866435019503523989316545940624⟩, ⟨-6953361714435836999774682046651661001733748, -6953361714435836999774682046651634966456641⟩,
  ⟨31599453078481584309983399200857948382357343, 31599453078481584309983399200858021147203960⟩, ⟨-131166869287019663002725037845118279377026680, -131166869287019663002725037845118075058931435⟩,
  ⟨499314121960676111284177688841603106220318075, 499314121960676111284177688841603680420337499⟩, ⟨-1749166440540591442498546456271559794287355351, -1749166440540591442498546456271558196774942367⟩,
  ⟨5655818457500169857549451799853527611544639204, 5655818457500169857549451799853531953381466095⟩, ⟨-16923657011174825851526122918141613014278852357, -16923657011174825851526122918141601624984400096⟩,
  ⟨46968553021968169913713607343628727705627286040, 46968553021968169913713607343628756270865565137⟩, ⟨-121139566723124456367978615463906123256871297120, -121139566723124456367978615463906055207595597144⟩,
  ⟨290850565325022843857703272300875307844138681192, 290850565325022843857703272300875461146260788692⟩, ⟨-651025887659103236408732164155549969910987085508, -651025887659103236408732164155549644224702300002⟩,
  ⟨1360256834187289493903614905282284397981913536953, 1360256834187289493903614905282285049357050646115⟩, ⟨-2655868533984436672560903985494707219229334662334, -2655868533984436672560903985494705994054931339402⟩,
  ⟨4850086807079592980297229442938994128548680644588, 4850086807079592980297229442938996294465776345474⟩, ⟨-8290391940829447162020504423809526382822474358887, -8290391940829447162020504423809522785189936875570⟩,
  ⟨13272231430419982810653277233819837012283876449552, 13272231430419982810653277233819842625840646695795⟩, ⟨-19909283750439323015340289485130260749658159189834, -19909283750439323015340289485130252522518305776611⟩,
  ⟨27993092740744518042792241783383130284452735771958, 27993092740744518042792241783383141608385532416381⟩, ⟨-36898902745465069199091232706983617682832367667668, -36898902745465069199091232706983603046882336779567⟩,
  ⟨45600662315203930694738937031391016006140729478869, 45600662315203930694738937031391033765837871127151⟩, ⟨-52831892346359811227990884982767840858181879645476, -52831892346359811227990884982767820631400014351885⟩,
  ⟨57372626164071180351078456222364440811380685532826, 57372626164071180351078456222364462425793365447839⟩, ⟨-58378923957435054552722986762756763598608868742473, -58378923957435054552722986762756741936939002862286⟩,
  ⟨55635341058391931608416834003119414120190504459468, 55635341058391931608416834003119434468633928675403⟩, ⟨-49628141651711197972487884291373771998888843032085, -49628141651711197972487884291373754094167029364810⟩,
  ⟨41405928165109856468005946048131884931789612652136, 41405928165109856468005946048131899676952922380201⟩, ⟨-32281967896476116752671796357775740385633897568158, -32281967896476116752671796357775729031289843347303⟩,
  ⟨23493718056807723216774260801754782188178596075390, 23493718056807723216774260801754790354369440172239⟩, ⟨-15939985106353123005285149243389853396265217079497, -15939985106353123005285149243389847917803507167746⟩,
  ⟨10067672604952115045599447185382785269108452780119, 10067672604952115045599447185382788692282498758193⟩, ⟨-5909300487109144155493812049758958955113123044590, -5909300487109144155493812049758956966353277094050⟩,
  ⟨3217045624248779870684308367389869762590930489575, 3217045624248779870684308367389870834750739301202⟩, ⟨-1620737700866764615539877061885501440736111087882, -1620737700866764615539877061885500905587560567974⟩,
  ⟨753659574724769419245960886104904803166751228976, 753659574724769419245960886104905049824034176428⟩, ⟨-322511516922376564644996224680127562943469346443, -322511516922376564644996224680127458275432105902⟩,
  ⟨126566936964251382654985333498821781937628612460, 126566936964251382654985333498821822687688383020⟩, ⟨-45368568443384536519083080565074202142932167299, -45368568443384536519083080565074187645597761511⟩,
  ⟨14784608716702070097762938173683721862203589961, 14784608716702070097762938173683726553066782559⟩, ⟨-4355937578864408152720125382106317342986348641, -4355937578864408152720125382106315970140961282⟩,
  ⟨1152688262796827078949392793825279974478712203, 1152688262796827078949392793825280335511220472⟩, ⟨-271805267170261133749073616974974206506934221, -271805267170261133749073616974974121860065402⟩,
  ⟨56560124057943051198651590219202457015067335, 56560124057943051198651590219202474540473051⟩, ⟨-10261814838047767215891759443707455663864735, -10261814838047767215891759443707452497139769⟩,
  ⟨1598469867460509384168886176662432175953026, 1598469867460509384168886176662432668043729⟩, ⟨-209476760947093440168654194300751211968294, -209476760947093440168654194300751147428697⟩,
  ⟨22460458760870346289060395314690038907534, 22460458760870346289060395314690045879683⟩, ⟨-1892143998549314337885721388586637798563, -1892143998549314337885721388586637197939⟩,
  ⟨117446393511738600594764450168419056486, 117446393511738600594764450168419095955⟩, ⟨-4775780769250000121954306984242509412, -4775780769250000121954306984242507559⟩,
  ⟨95443735446661736848869453813286932, 95443735446661736848869453813286987⟩]

def cLA_arr : Array FpIv := cLA_lit.toArray
def cLB_arr : Array FpIv := cLB_lit.toArray
def cAU_arr : Array FpIv := cAU_lit.toArray
def cBU_arr : Array FpIv := cBU_lit.toArray

private theorem rho63_LA_ok :
    ∀ i : Fin 31,
      rhoCheck S63 (pts63X ⟨31, by omega⟩ - pts63X ⟨i.1, by omega⟩)
        (pts63Z ⟨31, by omega⟩ - pts63Z ⟨i.1, by omega⟩) (cLA_rho[i.1]?.getD 0) = true ∧
      FpIv.slopeIv S63 (pts63X ⟨31, by omega⟩ - pts63X ⟨i.1, by omega⟩)
        (pts63Z ⟨31, by omega⟩ - pts63Z ⟨i.1, by omega⟩) (cLA_rho[i.1]?.getD 0) =
        cLA_arr[i.1]?.getD FpIv.zero := by
  decide

private theorem rho63_LB_ok :
    ∀ i : Fin 31,
      rhoCheck S63 (pts63X ⟨32, by omega⟩ - pts63X ⟨i.1, by omega⟩)
        (pts63Z ⟨32, by omega⟩ - pts63Z ⟨i.1, by omega⟩) (cLB_rho[i.1]?.getD 0) = true ∧
      FpIv.slopeIv S63 (pts63X ⟨32, by omega⟩ - pts63X ⟨i.1, by omega⟩)
        (pts63Z ⟨32, by omega⟩ - pts63Z ⟨i.1, by omega⟩) (cLB_rho[i.1]?.getD 0) =
        cLB_arr[i.1]?.getD FpIv.zero := by
  decide

private theorem rho63_AB_ok :
    rhoCheck S63 (pts63X ⟨32, by omega⟩ - pts63X ⟨31, by omega⟩)
      (pts63Z ⟨32, by omega⟩ - pts63Z ⟨31, by omega⟩) cAB_rho = true ∧
    FpIv.slopeIv S63 (pts63X ⟨32, by omega⟩ - pts63X ⟨31, by omega⟩)
      (pts63Z ⟨32, by omega⟩ - pts63Z ⟨31, by omega⟩) cAB_rho = cAB_lit := by
  decide

private theorem rho63_AU_ok :
    ∀ k : Fin 30,
      rhoCheck S63 (pts63X ⟨33 + k.1, by omega⟩ - pts63X ⟨31, by omega⟩)
        (pts63Z ⟨33 + k.1, by omega⟩ - pts63Z ⟨31, by omega⟩) (cAU_rho[k.1]?.getD 0) = true ∧
      FpIv.slopeIv S63 (pts63X ⟨33 + k.1, by omega⟩ - pts63X ⟨31, by omega⟩)
        (pts63Z ⟨33 + k.1, by omega⟩ - pts63Z ⟨31, by omega⟩) (cAU_rho[k.1]?.getD 0) =
        cAU_arr[k.1]?.getD FpIv.zero := by
  decide

private theorem rho63_BU_ok :
    ∀ k : Fin 30,
      rhoCheck S63 (pts63X ⟨33 + k.1, by omega⟩ - pts63X ⟨32, by omega⟩)
        (pts63Z ⟨33 + k.1, by omega⟩ - pts63Z ⟨32, by omega⟩) (cBU_rho[k.1]?.getD 0) = true ∧
      FpIv.slopeIv S63 (pts63X ⟨33 + k.1, by omega⟩ - pts63X ⟨32, by omega⟩)
        (pts63Z ⟨33 + k.1, by omega⟩ - pts63Z ⟨32, by omega⟩) (cBU_rho[k.1]?.getD 0) =
        cBU_arr[k.1]?.getD FpIv.zero := by
  decide

def c63Lit (i j : Fin 63) : FpIv :=
  if i.1 < 31 then
    if j.1 = 31 then cLA_arr[i.1]?.getD FpIv.zero
    else if j.1 = 32 then cLB_arr[i.1]?.getD FpIv.zero
    else FpIv.zero
  else if i.1 = 31 then
    if j.1 = 32 then cAB_lit
    else if 33 ≤ j.1 then cAU_arr[j.1 - 33]?.getD FpIv.zero
    else FpIv.zero
  else if i.1 = 32 then
    if 33 ≤ j.1 then cBU_arr[j.1 - 33]?.getD FpIv.zero
    else FpIv.zero
  else FpIv.zero

lemma S63_pos : 0 < S63 := by decide

lemma x63Path_one_ax (i : Fin 63) (h31 : i.1 ≠ 31) (h32 : i.1 ≠ 32) :
    (x63Path 1).1 i 0 = 0 := by
  have hx : pts63X i = 0 := by
    dsimp [pts63X]; split_ifs <;> omega
  simp [x63Path, planarPath, hx]

lemma c63Lit_mem :
    ∀ i j : Fin 63, i < j → FpIv.FpMem S63 (c63Lit i j) (planarSlope (x63Path 1).1 i j) := by
  intro ⟨iv, hi⟩ ⟨jv, hj⟩ hij
  have hlt : iv < jv := hij
  unfold c63Lit
  dsimp only
  by_cases hi31 : iv < 31
  · simp only [hi31, ↓reduceIte]
    by_cases hj31 : jv = 31
    · subst hj31
      have hrok := rho63_LA_ok ⟨iv, hi31⟩
      simp only [↓reduceIte]
      rw [← hrok.2]
      exact slopeIv_planarPath_one_mem S63_pos pts63X pts63Z pts63Z_strictMono hij hrok.1
    · by_cases hj32 : jv = 32
      · subst hj32
        have hrok := rho63_LB_ok ⟨iv, hi31⟩
        simp only [hj31, ↓reduceIte]
        rw [← hrok.2]
        exact slopeIv_planarPath_one_mem S63_pos pts63X pts63Z pts63Z_strictMono hij hrok.1
      · simp only [hj31, hj32, ↓reduceIte]
        rw [planarSlope_eq_zero_of_x_eq_zero _
          (x63Path_one_ax ⟨iv, hi⟩ (by dsimp; omega) (by dsimp; omega))
          (x63Path_one_ax ⟨jv, hj⟩ (by dsimp; omega) (by dsimp; omega))]
        exact FpIv.zero_mem S63
  · by_cases hi_eq31 : iv = 31
    · subst hi_eq31
      simp only [hi31, ↓reduceIte]
      by_cases hj32 : jv = 32
      · subst hj32
        simp only [↓reduceIte]
        rw [← rho63_AB_ok.2]
        exact slopeIv_planarPath_one_mem S63_pos pts63X pts63Z pts63Z_strictMono hij rho63_AB_ok.1
      · have hj33 : 33 ≤ jv := by omega
        have hj_eq : (⟨jv, hj⟩ : Fin 63) = ⟨33 + (jv - 33), by omega⟩ := Fin.ext (by dsimp; omega)
        have hrok := rho63_AU_ok ⟨jv - 33, by omega⟩
        simp only [hj32, hj33, ↓reduceIte]
        rw [← hrok.2, hj_eq]
        exact slopeIv_planarPath_one_mem S63_pos pts63X pts63Z pts63Z_strictMono
          (show (⟨31, hi⟩ : Fin 63) < ⟨33 + (jv - 33), by omega⟩ from Fin.mk_lt_mk.mpr (by omega))
          hrok.1
    · by_cases hi_eq32 : iv = 32
      · subst hi_eq32
        have hj33 : 33 ≤ jv := by omega
        have hj_eq : (⟨jv, hj⟩ : Fin 63) = ⟨33 + (jv - 33), by omega⟩ := Fin.ext (by dsimp; omega)
        have hrok := rho63_BU_ok ⟨jv - 33, by omega⟩
        simp only [hi31, hi_eq31, hj33, ↓reduceIte]
        rw [← hrok.2, hj_eq]
        exact slopeIv_planarPath_one_mem S63_pos pts63X pts63Z pts63Z_strictMono
          (show (⟨32, hi⟩ : Fin 63) < ⟨33 + (jv - 33), by omega⟩ from Fin.mk_lt_mk.mpr (by omega))
          hrok.1
      · simp only [hi31, hi_eq31, hi_eq32, ↓reduceIte]
        rw [planarSlope_eq_zero_of_x_eq_zero _
          (x63Path_one_ax ⟨iv, hi⟩ (by dsimp; omega) (by dsimp; omega))
          (x63Path_one_ax ⟨jv, hj⟩ (by dsimp; omega) (by dsimp; omega))]
        exact FpIv.zero_mem S63

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private lemma rowA63_eq_lit : polyListIv S63 c63Lit ⟨31, by omega⟩ = rowALit := by decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private lemma rowB63_eq_lit : polyListIv S63 c63Lit ⟨32, by omega⟩ = rowBLit := by decide

private def lPairs63Iv : List (FpIv × FpIv) :=
  (List.finRange 31).map fun j =>
    (FpIv.add (c63Lit ⟨j.1, by omega⟩ ⟨31, by omega⟩) (c63Lit ⟨j.1, by omega⟩ ⟨32, by omega⟩),
     FpIv.mulFp S63 (c63Lit ⟨j.1, by omega⟩ ⟨31, by omega⟩) (c63Lit ⟨j.1, by omega⟩ ⟨32, by omega⟩))

private def uPairsRev63Iv : List (FpIv × FpIv) :=
  (List.finRange 30).map fun s =>
    let k := 29 - s.1
    (FpIv.neg (FpIv.add (c63Lit ⟨31, by omega⟩ ⟨33 + k, by omega⟩) (c63Lit ⟨32, by omega⟩ ⟨33 + k, by omega⟩)),
     FpIv.mulFp S63 (c63Lit ⟨31, by omega⟩ ⟨33 + k, by omega⟩) (c63Lit ⟨32, by omega⟩ ⟨33 + k, by omega⟩))

private noncomputable def lPairs63R : List (ℝ × ℝ) :=
  (List.finRange 31).map fun j =>
    (planarSlope (x63Path 1).1 ⟨j.1, by omega⟩ ⟨31, by omega⟩ +
      planarSlope (x63Path 1).1 ⟨j.1, by omega⟩ ⟨32, by omega⟩,
     planarSlope (x63Path 1).1 ⟨j.1, by omega⟩ ⟨31, by omega⟩ *
      planarSlope (x63Path 1).1 ⟨j.1, by omega⟩ ⟨32, by omega⟩)

private noncomputable def uPairsRev63R : List (ℝ × ℝ) :=
  (List.finRange 30).map fun s =>
    let k := 29 - s.1
    (-(planarSlope (x63Path 1).1 ⟨31, by omega⟩ ⟨33 + k, by omega⟩ +
        planarSlope (x63Path 1).1 ⟨32, by omega⟩ ⟨33 + k, by omega⟩),
     planarSlope (x63Path 1).1 ⟨31, by omega⟩ ⟨33 + k, by omega⟩ *
      planarSlope (x63Path 1).1 ⟨32, by omega⟩ ⟨33 + k, by omega⟩)

private def curA63Iv : List FpIv := elimFrontIv S63 uPairsRev63Iv (elimFrontIv S63 lPairs63Iv rowALit).reverse
private def curB63Iv : List FpIv := elimFrontIv S63 uPairsRev63Iv (elimFrontIv S63 lPairs63Iv rowBLit).reverse

private def det2_63_iv : FpIv :=
  FpIv.sub
    (FpIv.mulFp S63 (curA63Iv.getD 1 FpIv.zero) (curB63Iv.getD 0 FpIv.zero))
    (FpIv.mulFp S63 (curA63Iv.getD 0 FpIv.zero) (curB63Iv.getD 1 FpIv.zero))

def det2_63_cert : FpIv :=
  ⟨-2284921978047217236203059003854910729281077760362662,
   -2284921978047217236203058848881996895089575621129377⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private lemma det2_63_eq_cert : det2_63_iv = det2_63_cert := by decide
private lemma det2_63_cert_neg : det2_63_cert.hi < 0 := by decide

section ShieldC12
attribute [local irreducible] Matrix.det planarMat planarDen atiyahDet S63
  rowALit rowBLit det2_63_cert

lemma x63Path_one_mat_det_fpMem :
    FpIv.FpMem S63 det2_63_cert (planarMat (x63Path 1).1).det := by
  have haxL : ∀ i : Fin 31, (x63Path 1).1 ⟨i.1, by omega⟩ 0 = 0 :=
    fun i => x63Path_one_ax _ (by dsimp; omega) (by dsimp; omega)
  have haxU : ∀ k : Fin 30, (x63Path 1).1 ⟨31 + 2 + k.1, by omega⟩ 0 = 0 :=
    fun k => x63Path_one_ax _ (by dsimp; omega) (by dsimp; omega)
  have hlenL : lPairs63R.length = 31 := by simp [lPairs63R]
  have hlenU : uPairsRev63R.length = 30 := by simp [uPairsRev63R]
  have hl : ∀ t (ht : t < 31), lPairs63R[t]? = some
      (planarSlope (x63Path 1).1 ⟨t, by omega⟩ ⟨31, by omega⟩ +
        planarSlope (x63Path 1).1 ⟨t, by omega⟩ ⟨32, by omega⟩,
       planarSlope (x63Path 1).1 ⟨t, by omega⟩ ⟨31, by omega⟩ *
        planarSlope (x63Path 1).1 ⟨t, by omega⟩ ⟨32, by omega⟩) := by
    intro t ht
    rw [List.getElem?_eq_getElem (by rw [hlenL]; exact ht)]
    simp only [lPairs63R, List.getElem_map, List.getElem_finRange, Fin.val_cast]
  have hu : ∀ s (hs : s < 30), uPairsRev63R[s]? = some
      (-(planarSlope (x63Path 1).1 ⟨31, by omega⟩ ⟨31 + 2 + (30 - 1 - s), by omega⟩ +
          planarSlope (x63Path 1).1 ⟨32, by omega⟩ ⟨31 + 2 + (30 - 1 - s), by omega⟩),
       planarSlope (x63Path 1).1 ⟨31, by omega⟩ ⟨31 + 2 + (30 - 1 - s), by omega⟩ *
        planarSlope (x63Path 1).1 ⟨32, by omega⟩ ⟨31 + 2 + (30 - 1 - s), by omega⟩) := by
    intro s hs
    rw [List.getElem?_eq_getElem (by rw [hlenU]; exact hs)]
    simp only [uPairsRev63R, List.getElem_map, List.getElem_finRange, Fin.val_cast]
  have hdet_eq := planarMat_det_eq_elimFront (a := 31) (b := 30) (x63Path 1).1 haxL haxU
    lPairs63R uPairsRev63R hlenL hlenU hl hu
  have hl_f2 : List.Forall₂ (fun a b => FpIv.FpMem S63 a.1 b.1 ∧ FpIv.FpMem S63 a.2 b.2)
      lPairs63Iv lPairs63R := by
    refine forall2_map_same fun j _ => ?_
    have hc1 := c63Lit_mem ⟨j.1, by omega⟩ ⟨31, by omega⟩ (Fin.mk_lt_mk.mpr (by omega))
    have hc2 := c63Lit_mem ⟨j.1, by omega⟩ ⟨32, by omega⟩ (Fin.mk_lt_mk.mpr (by omega))
    exact ⟨FpIv.add_mem hc1 hc2, FpIv.mulFp_mem S63_pos hc1 hc2⟩
  have hu_f2 : List.Forall₂ (fun a b => FpIv.FpMem S63 a.1 b.1 ∧ FpIv.FpMem S63 a.2 b.2)
      uPairsRev63Iv uPairsRev63R := by
    refine forall2_map_same fun s _ => ?_
    have hc1 := c63Lit_mem ⟨31, by omega⟩ ⟨33 + (29 - s.1), by omega⟩ (Fin.mk_lt_mk.mpr (by omega))
    have hc2 := c63Lit_mem ⟨32, by omega⟩ ⟨33 + (29 - s.1), by omega⟩ (Fin.mk_lt_mk.mpr (by omega))
    exact ⟨FpIv.neg_mem (FpIv.add_mem hc1 hc2), FpIv.mulFp_mem S63_pos hc1 hc2⟩
  have hrowA_f2 : List.Forall₂ (FpIv.FpMem S63) curA63Iv
      (elimFrontR uPairsRev63R (elimFrontR lPairs63R (List.ofFn (planarMat (x63Path 1).1 ⟨31, by omega⟩))).reverse) := by
    unfold curA63Iv
    refine elimFrontIv_forall2 S63_pos hu_f2 (forall2_reverse ?_)
    refine elimFrontIv_forall2 S63_pos hl_f2 ?_
    rw [← rowA63_eq_lit]
    exact polyListIv_forall2_ofFn S63_pos c63Lit_mem ⟨31, by omega⟩
  have hrowB_f2 : List.Forall₂ (FpIv.FpMem S63) curB63Iv
      (elimFrontR uPairsRev63R (elimFrontR lPairs63R (List.ofFn (planarMat (x63Path 1).1 ⟨32, by omega⟩))).reverse) := by
    unfold curB63Iv
    refine elimFrontIv_forall2 S63_pos hu_f2 (forall2_reverse ?_)
    refine elimFrontIv_forall2 S63_pos hl_f2 ?_
    rw [← rowB63_eq_lit]
    exact polyListIv_forall2_ofFn S63_pos c63Lit_mem ⟨32, by omega⟩
  have getD_f2 : ∀ {ivs : List FpIv} {rs : List ℝ},
      List.Forall₂ (FpIv.FpMem S63) ivs rs → ∀ k : ℕ, FpIv.FpMem S63 (ivs.getD k FpIv.zero) (rs.getD k 0) := by
    intro ivs rs hf2 k
    induction hf2 generalizing k with
    | nil => simp [FpIv.zero_mem S63]
    | cons ha _ ih =>
      cases k with
      | zero => simpa using ha
      | succ k => simpa [List.getD_cons_succ] using ih k
  rw [← det2_63_eq_cert, hdet_eq]
  unfold det2_63_iv
  exact FpIv.sub_mem
    (FpIv.mulFp_mem S63_pos (getD_f2 hrowA_f2 1) (getD_f2 hrowB_f2 0))
    (FpIv.mulFp_mem S63_pos (getD_f2 hrowA_f2 0) (getD_f2 hrowB_f2 1))

lemma x63Path_one_mat_det_neg : (planarMat (x63Path 1).1).det < 0 := by
  have hmem_det := x63Path_one_mat_det_fpMem
  have hS : (0 : ℝ) < (S63 : ℝ) := by exact_mod_cast S63_pos
  have hhi : (det2_63_cert.hi : ℝ) < 0 := by exact_mod_cast det2_63_cert_neg
  have hprod_neg : (S63 : ℝ) * (planarMat (x63Path 1).1).det < 0 := lt_of_le_of_lt hmem_det.2 hhi
  exact (mul_neg_iff.mp hprod_neg).resolve_right (fun h => by linarith [h.1]) |>.2

/-- Explicit `63`-point planar witness with strictly negative Atiyah–Sutcliffe determinant. -/
theorem exists_planar_63_atiyahDet_neg :
    ∃ x : DistinctPoints 63, (atiyahDet x).re < 0 := by
  refine ⟨x63Path 1, ?_⟩
  have hy : ∀ i, (x63Path 1).1 i 1 = 0 := fun _ => rfl
  have hz : StrictMono (fun i => (x63Path 1).1 i 2) :=
    fun _ _ h => Int.cast_lt.mpr (pts63Z_strictMono h)
  rw [atiyahDet_eq_planarMat_div (x63Path 1) hy hz]
  exact div_neg_of_neg_of_pos x63Path_one_mat_det_neg (planarDen_pos _)

/-- Explicit `63`-point planar witness where Atiyah's determinant vanishes (`D_63(x₀) = 0`),
obtained along the collision-free homotopy `s ↦ x63Path s` from `D_63(0) = +1` to `D_63(1) < 0`. -/
theorem exists_planar_63_atiyahDet_zero :
    ∃ x : DistinctPoints 63, atiyahDet x = 0 := by
  let f : ℝ → ℝ := fun s => (atiyahDet (x63Path s)).re
  have hcont : ContinuousOn f (Set.Icc (0 : ℝ) 1) :=
    (continuous_planarPath_re pts63X pts63Z pts63Z_strictMono).continuousOn
  have hf0 : f 0 = 1 := by
    simp [f, x63Path, planarPath_zero_eq_one]
  have hf1 : f 1 < 0 := by
    have hy : ∀ i, (x63Path 1).1 i 1 = 0 := fun _ => rfl
    have hz : StrictMono (fun i => (x63Path 1).1 i 2) :=
      fun _ _ h => Int.cast_lt.mpr (pts63Z_strictMono h)
    dsimp [f]
    rw [atiyahDet_eq_planarMat_div (x63Path 1) hy hz]
    exact div_neg_of_neg_of_pos x63Path_one_mat_det_neg (planarDen_pos _)
  have hmem : (0 : ℝ) ∈ Set.Icc (f 1) (f 0) := ⟨hf1.le, by linarith [hf0]⟩
  obtain ⟨s₀, _, hs₀⟩ := intermediate_value_Icc' zero_le_one hcont hmem
  refine ⟨x63Path s₀, ?_⟩
  have hy : ∀ i, (x63Path s₀).1 i 1 = 0 := fun _ => rfl
  have hz : StrictMono (fun i => (x63Path s₀).1 i 2) :=
    fun _ _ h => Int.cast_lt.mpr (pts63Z_strictMono h)
  have hreal := atiyahDet_eq_planarMat_div (x63Path s₀) hy hz
  rw [hreal]
  have hre0 : ((planarMat (x63Path s₀).1).det / planarDen (x63Path s₀).1 : ℝ) = 0 := by
    have h1 : (atiyahDet (x63Path s₀)).re = 0 := hs₀
    simpa [hreal] using h1
  simp [hre0]

end ShieldC12

/-- **Disproof of Atiyah–Sutcliffe Conjecture 1 (Determinant Form, 2001/2002)** at `n = 63`
(giving the first explicit finite configuration with `D_n(x) = 0`). -/
theorem disproof_atiyah_det_nonzero : ¬ AtiyahDetNonzeroProp := by
  intro h
  obtain ⟨x, hx⟩ := exists_planar_63_atiyahDet_zero
  exact h 63 (by norm_num) x hx

/-- **Disproof of Atiyah Conjecture 1 (Linear Independence Form, 2001)** at `n = 63`:
the 63 Atiyah polynomials become linearly dependent on a planar configuration. -/
theorem disproof_atiyah_conjecture_1 : ¬ AtiyahConjecture1Prop := by
  intro h
  obtain ⟨x, hx⟩ := exists_planar_63_atiyahDet_zero
  have hli := h 63 (by norm_num) x
  exact not_linearIndependent_of_atiyahDet_eq_zero (by norm_num) x hx hli

/-- **Disproof of Atiyah–Sutcliffe Conjecture 2 (2002)** at `n = 63`:
`|D_63(x₀)| = 0 < 1` at the singular planar witness `x₀` (while the rational integer
endpoint `x63Path 1` itself already violates Conjecture 2 numerically with `D_63 ≈ -0.6396`). -/
theorem disproof_atiyah_sutcliffe_conjecture_2 : ¬ AtiyahSutcliffeConjecture2Prop := by
  intro h
  obtain ⟨x, hx⟩ := exists_planar_63_atiyahDet_zero
  have hle := h 63 (by norm_num) x
  rw [hx, norm_zero] at hle
  linarith

end Conjectures1And2Disproof

end Matematyka.AtiyahSutcliffe
