module

public import Matematyka.AtiyahSutcliffe

/-!
# Formally Verified Non-Coplanar 3D Disproof of Atiyah–Sutcliffe Conjectures 1 & 2 (`n = 36`)

We construct an explicit one-parameter family `x36Clamp t` (`t : ℝ`) of `36` pairwise distinct,
genuinely non-coplanar points in `ℝ³`, built from two coaxial Pythagorean `(33, 56, 65)` hexagonal
rings (`6 + 6` points) separated by `18` lower and `6` upper collinear points along the `z`-axis,
and establish via kernel-checked interval arithmetic (`S = 10^18`, standard axioms
`{propext, Classical.choice, Quot.sound}` only):

1. `exists_noncoplanar_3d_36_atiyahDet_neg` (`t = 10`, where `(atiyahDet (x36Clamp 10)).re < 0`).
2. Reflection symmetry (`reflectPerm36`) yields `(atiyahDet (x36Clamp t)).im = 0` for all `t : ℝ`.
3. `exists_noncoplanar_3d_36_atiyahDet_zero` via the Intermediate Value Theorem on `Set.Icc 9 10`
   (from `(atiyahDet (x36Clamp 9)).re > 0` to `(atiyahDet (x36Clamp 10)).re < 0`).
4. Corollaries `disproof_atiyah_det_nonzero_3d_36`, `disproof_atiyah_conjecture_1_3d_36`, and
   `disproof_atiyah_sutcliffe_conjecture_2_3d_36`.
-/

@[expose] public section

namespace Matematyka.AtiyahSutcliffe3D36

open Complex Real Matrix Polynomial
open Matematyka.MalkounCounterexample Matematyka.AtiyahSutcliffe

/-! ## Part 1: 3D Slopes, Complex Fixed-Point Intervals & Memoized List Reductions -/

section ComplexIntervals

/-- Outward-rounded interval for `S * (d / (dz + r))` assuming `0 < S`, `0 ≤ dz`,
`0 < rhoLo`, and `rhoLo ≤ S * r ≤ rhoLo + 1`. -/
def slopeIv3D (S d dz rhoLo : ℤ) : FpIv :=
  let denLo := S * dz + rhoLo
  let denHi := S * dz + rhoLo + 1
  if 0 ≤ d then
    ⟨(S * S * d) / denHi, (S * S * d + denLo - 1) / denLo⟩
  else
    FpIv.neg ⟨(S * S * (-d)) / denHi, (S * S * (-d) + denLo - 1) / denLo⟩

private lemma slopeIv3D_mem_nonneg {S d dz rhoLo : ℤ} {r : ℝ}
    (hS : 0 < S) (hdz : 0 ≤ dz) (hrhoPos : 0 < rhoLo)
    (hr : (rhoLo : ℝ) ≤ (S : ℝ) * r ∧ (S : ℝ) * r ≤ (rhoLo + 1 : ℝ))
    (hd : 0 ≤ d) :
    FpIv.FpMem S (slopeIv3D S d dz rhoLo) ((d : ℝ) / ((dz : ℝ) + r)) := by
  have hdenLo : 0 < S * dz + rhoLo := by nlinarith
  have hdenHi : 0 < S * dz + rhoLo + 1 := by omega
  have hS_pos : (0 : ℝ) < (S : ℝ) := by exact_mod_cast hS
  have hdenLoR : ((S * dz + rhoLo : ℤ) : ℝ) ≤ (S : ℝ) * ((dz : ℝ) + r) := by
    push_cast; linarith [hr.1]
  have hdenHiR : (S : ℝ) * ((dz : ℝ) + r) ≤ ((S * dz + rhoLo + 1 : ℤ) : ℝ) := by
    push_cast; linarith [hr.2]
  have hposLoR : (0 : ℝ) < ((S * dz + rhoLo : ℤ) : ℝ) := by exact_mod_cast hdenLo
  have hdenR_pos : (0 : ℝ) < (dz : ℝ) + r := by nlinarith
  have hflo : (S * dz + rhoLo + 1) * ((S * S * d) / (S * dz + rhoLo + 1)) ≤ S * S * d :=
    FpIv.ediv_floor_mul_le (S * dz + rhoLo + 1) (S * S * d) hdenHi
  have hchi : S * S * d ≤ (S * dz + rhoLo) * ((S * S * d + (S * dz + rhoLo) - 1) / (S * dz + rhoLo)) :=
    FpIv.le_ediv_ceil_mul (S * dz + rhoLo) (S * S * d) hdenLo
  have hlo_nn : (0 : ℤ) ≤ (S * S * d) / (S * dz + rhoLo + 1) :=
    Int.ediv_nonneg (mul_nonneg (mul_nonneg hS.le hS.le) hd) hdenHi.le
  have hhi_nn : (0 : ℤ) ≤ (S * S * d + (S * dz + rhoLo) - 1) / (S * dz + rhoLo) :=
    Int.ediv_nonneg (by nlinarith) hdenLo.le
  have hlo_nnR : (0 : ℝ) ≤ ((S * S * d) / (S * dz + rhoLo + 1) : ℤ) := by exact_mod_cast hlo_nn
  have hhi_nnR : (0 : ℝ) ≤ ((S * S * d + (S * dz + rhoLo) - 1) / (S * dz + rhoLo) : ℤ) := by
    exact_mod_cast hhi_nn
  have hfloR : ((S * dz + rhoLo + 1 : ℤ) : ℝ) * (((S * S * d) / (S * dz + rhoLo + 1) : ℤ) : ℝ) ≤
      ((S * S * d : ℤ) : ℝ) := by exact_mod_cast hflo
  have hchiR : ((S * S * d : ℤ) : ℝ) ≤
      ((S * dz + rhoLo : ℤ) : ℝ) *
        (((S * S * d + (S * dz + rhoLo) - 1) / (S * dz + rhoLo) : ℤ) : ℝ) := by
    exact_mod_cast hchi
  simp only [slopeIv3D, hd, ↓reduceIte, FpIv.FpMem]
  constructor
  · have hm1 : (S : ℝ) * ((dz : ℝ) + r) * (((S * S * d) / (S * dz + rhoLo + 1) : ℤ) : ℝ) ≤
        ((S * S * d : ℤ) : ℝ) :=
      le_trans (mul_le_mul_of_nonneg_right hdenHiR hlo_nnR) hfloR
    have hm2 : (S : ℝ) * (((((S * S * d) / (S * dz + rhoLo + 1) : ℤ) : ℝ)) * ((dz : ℝ) + r)) ≤
        (S : ℝ) * ((S : ℝ) * (d : ℝ)) := by
      push_cast at hm1 ⊢; linarith
    have hm3 : (((((S * S * d) / (S * dz + rhoLo + 1) : ℤ) : ℝ)) * ((dz : ℝ) + r)) ≤
        (S : ℝ) * (d : ℝ) := le_of_mul_le_mul_left hm2 hS_pos
    rw [← mul_div_assoc]
    exact (le_div_iff₀ hdenR_pos).mpr hm3
  · have hm1 : ((S * S * d : ℤ) : ℝ) ≤
        (S : ℝ) * ((dz : ℝ) + r) *
          (((S * S * d + (S * dz + rhoLo) - 1) / (S * dz + rhoLo) : ℤ) : ℝ) :=
      le_trans hchiR (mul_le_mul_of_nonneg_right hdenLoR hhi_nnR)
    have hm2 : (S : ℝ) * ((S : ℝ) * (d : ℝ)) ≤
        (S : ℝ) * (((((S * S * d + (S * dz + rhoLo) - 1) / (S * dz + rhoLo) : ℤ) : ℝ)) * ((dz : ℝ) + r)) := by
      push_cast at hm1 ⊢; linarith
    have hm3 : (S : ℝ) * (d : ℝ) ≤
        (((((S * S * d + (S * dz + rhoLo) - 1) / (S * dz + rhoLo) : ℤ) : ℝ)) * ((dz : ℝ) + r)) :=
      le_of_mul_le_mul_left hm2 hS_pos
    rw [← mul_div_assoc]
    exact (div_le_iff₀ hdenR_pos).mpr hm3

lemma slopeIv3D_mem {S d dz rhoLo : ℤ} {r : ℝ}
    (hS : 0 < S) (hdz : 0 ≤ dz) (hrhoPos : 0 < rhoLo)
    (hr : (rhoLo : ℝ) ≤ (S : ℝ) * r ∧ (S : ℝ) * r ≤ (rhoLo + 1 : ℝ)) :
    FpIv.FpMem S (slopeIv3D S d dz rhoLo) ((d : ℝ) / ((dz : ℝ) + r)) := by
  by_cases hd : 0 ≤ d
  · exact slopeIv3D_mem_nonneg hS hdz hrhoPos hr hd
  · have hnd : 0 ≤ -d := by omega
    have hmem := slopeIv3D_mem_nonneg hS hdz hrhoPos hr hnd
    have hneg_eq : slopeIv3D S d dz rhoLo = FpIv.neg (slopeIv3D S (-d) dz rhoLo) := by
      dsimp [slopeIv3D]
      simp only [hd, ↓reduceIte, hnd]
    have hval : (d : ℝ) / ((dz : ℝ) + r) = -((((-d : ℤ) : ℝ)) / ((dz : ℝ) + r)) := by
      push_cast; ring
    rw [hneg_eq, hval]
    exact FpIv.neg_mem hmem

lemma sqrt_rho_bounds {S dx dy dz rhoLo : ℤ}
    (hS : 0 < S) (hrhoPos : 0 < rhoLo)
    (hlo : rhoLo * rhoLo ≤ S * S * (dx * dx + dy * dy + dz * dz))
    (hhi : S * S * (dx * dx + dy * dy + dz * dz) ≤ (rhoLo + 1) * (rhoLo + 1)) :
    (rhoLo : ℝ) ≤ (S : ℝ) * Real.sqrt ((dx : ℝ) ^ 2 + (dy : ℝ) ^ 2 + (dz : ℝ) ^ 2) ∧
      (S : ℝ) * Real.sqrt ((dx : ℝ) ^ 2 + (dy : ℝ) ^ 2 + (dz : ℝ) ^ 2) ≤ (rhoLo + 1 : ℝ) := by
  have hS_nn : (0 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS.le
  have hsq_nn : (0 : ℝ) ≤ (dx : ℝ) ^ 2 + (dy : ℝ) ^ 2 + (dz : ℝ) ^ 2 := by positivity
  have hR_nn : (0 : ℝ) ≤ (S : ℝ) * Real.sqrt ((dx : ℝ) ^ 2 + (dy : ℝ) ^ 2 + (dz : ℝ) ^ 2) :=
    mul_nonneg hS_nn (Real.sqrt_nonneg _)
  have hR_sq :
      ((S : ℝ) * Real.sqrt ((dx : ℝ) ^ 2 + (dy : ℝ) ^ 2 + (dz : ℝ) ^ 2)) *
        ((S : ℝ) * Real.sqrt ((dx : ℝ) ^ 2 + (dy : ℝ) ^ 2 + (dz : ℝ) ^ 2)) =
        (S : ℝ) * (S : ℝ) * ((dx : ℝ) * (dx : ℝ) + (dy : ℝ) * (dy : ℝ) + (dz : ℝ) * (dz : ℝ)) := by
    calc
      ((S : ℝ) * Real.sqrt ((dx : ℝ) ^ 2 + (dy : ℝ) ^ 2 + (dz : ℝ) ^ 2)) *
          ((S : ℝ) * Real.sqrt ((dx : ℝ) ^ 2 + (dy : ℝ) ^ 2 + (dz : ℝ) ^ 2))
        = (S : ℝ) * (S : ℝ) *
            (Real.sqrt ((dx : ℝ) ^ 2 + (dy : ℝ) ^ 2 + (dz : ℝ) ^ 2) *
              Real.sqrt ((dx : ℝ) ^ 2 + (dy : ℝ) ^ 2 + (dz : ℝ) ^ 2)) := by ring
      _ = (S : ℝ) * (S : ℝ) * ((dx : ℝ) ^ 2 + (dy : ℝ) ^ 2 + (dz : ℝ) ^ 2) := by
          rw [Real.mul_self_sqrt hsq_nn]
      _ = (S : ℝ) * (S : ℝ) * ((dx : ℝ) * (dx : ℝ) + (dy : ℝ) * (dy : ℝ) + (dz : ℝ) * (dz : ℝ)) := by
          ring
  have hloR : (rhoLo : ℝ) * (rhoLo : ℝ) ≤
      (S : ℝ) * (S : ℝ) * ((dx : ℝ) * (dx : ℝ) + (dy : ℝ) * (dy : ℝ) + (dz : ℝ) * (dz : ℝ)) := by
    exact_mod_cast hlo
  have hhiR :
      (S : ℝ) * (S : ℝ) * ((dx : ℝ) * (dx : ℝ) + (dy : ℝ) * (dy : ℝ) + (dz : ℝ) * (dz : ℝ)) ≤
        ((rhoLo : ℝ) + 1) * ((rhoLo : ℝ) + 1) := by
    exact_mod_cast hhi
  have hrho_posR : (0 : ℝ) < (rhoLo : ℝ) := by exact_mod_cast hrhoPos
  constructor
  · by_contra hlt
    push Not at hlt
    nlinarith
  · by_contra hlt
    push Not at hlt
    nlinarith

/-- Closed complex rectangle interval `re + I * im` scaled by `S`. -/
structure CFpIv where
  re : FpIv
  im : FpIv
  deriving DecidableEq

namespace CFpIv

def CFpMem (S : ℤ) (a : CFpIv) (z : ℂ) : Prop :=
  FpIv.FpMem S a.re z.re ∧ FpIv.FpMem S a.im z.im

def zero : CFpIv := ⟨FpIv.zero, FpIv.zero⟩
def ofInt (S z : ℤ) : CFpIv := ⟨FpIv.ofInt S z, FpIv.zero⟩
def add (a b : CFpIv) : CFpIv := ⟨FpIv.add a.re b.re, FpIv.add a.im b.im⟩
def sub (a b : CFpIv) : CFpIv := ⟨FpIv.sub a.re b.re, FpIv.sub a.im b.im⟩
def neg (a : CFpIv) : CFpIv := ⟨FpIv.neg a.re, FpIv.neg a.im⟩
def conj (a : CFpIv) : CFpIv := ⟨a.re, FpIv.neg a.im⟩

def mul (S : ℤ) (a b : CFpIv) : CFpIv :=
  ⟨FpIv.sub (FpIv.mulFp S a.re b.re) (FpIv.mulFp S a.im b.im),
   FpIv.add (FpIv.mulFp S a.re b.im) (FpIv.mulFp S a.im b.re)⟩

def cslopeIv (S dx dy dz rhoLo : ℤ) : CFpIv :=
  ⟨slopeIv3D S dx dz rhoLo, slopeIv3D S dy dz rhoLo⟩

lemma zero_mem (S : ℤ) : CFpMem S zero 0 :=
  ⟨FpIv.zero_mem S, FpIv.zero_mem S⟩

lemma ofInt_mem (S z : ℤ) : CFpMem S (ofInt S z) (z : ℂ) :=
  ⟨by simpa [ofInt] using FpIv.ofInt_mem S z, by simpa [ofInt] using FpIv.zero_mem S⟩

lemma add_mem {S : ℤ} {a b : CFpIv} {x y : ℂ}
    (hx : CFpMem S a x) (hy : CFpMem S b y) : CFpMem S (add a b) (x + y) :=
  ⟨by simpa [add] using FpIv.add_mem hx.1 hy.1, by simpa [add] using FpIv.add_mem hx.2 hy.2⟩

lemma sub_mem {S : ℤ} {a b : CFpIv} {x y : ℂ}
    (hx : CFpMem S a x) (hy : CFpMem S b y) : CFpMem S (sub a b) (x - y) :=
  ⟨by simpa [sub] using FpIv.sub_mem hx.1 hy.1, by simpa [sub] using FpIv.sub_mem hx.2 hy.2⟩

lemma neg_mem {S : ℤ} {a : CFpIv} {x : ℂ}
    (hx : CFpMem S a x) : CFpMem S (neg a) (-x) :=
  ⟨by simpa [neg] using FpIv.neg_mem hx.1, by simpa [neg] using FpIv.neg_mem hx.2⟩

lemma conj_mem {S : ℤ} {a : CFpIv} {x : ℂ}
    (hx : CFpMem S a x) : CFpMem S (conj a) (star x) :=
  ⟨by simpa [conj] using hx.1, by simpa [conj] using FpIv.neg_mem hx.2⟩

lemma mul_mem {S : ℤ} (hS : 0 < S) {a b : CFpIv} {x y : ℂ}
    (hx : CFpMem S a x) (hy : CFpMem S b y) : CFpMem S (mul S a b) (x * y) := by
  constructor
  · simpa [mul, Complex.mul_re] using
      FpIv.sub_mem (FpIv.mulFp_mem hS hx.1 hy.1) (FpIv.mulFp_mem hS hx.2 hy.2)
  · simpa [mul, Complex.mul_im] using
      FpIv.add_mem (FpIv.mulFp_mem hS hx.1 hy.2) (FpIv.mulFp_mem hS hx.2 hy.1)

lemma cslopeIv_mem {S dx dy dz rhoLo : ℤ} {r : ℝ}
    (hS : 0 < S) (hdz : 0 ≤ dz) (hrhoPos : 0 < rhoLo)
    (hr : (rhoLo : ℝ) ≤ (S : ℝ) * r ∧ (S : ℝ) * r ≤ (rhoLo + 1 : ℝ)) :
    CFpMem S (cslopeIv S dx dy dz rhoLo)
      (((dx : ℂ) + Complex.I * (dy : ℂ)) / ((dz : ℂ) + (r : ℂ))) := by
  have hden_ne : ((dz : ℝ) + r) ≠ 0 := by
    have hS_pos : (0 : ℝ) < (S : ℝ) := by exact_mod_cast hS
    have hdz_nn : (0 : ℝ) ≤ (dz : ℝ) := by exact_mod_cast hdz
    have hrho_posR : (0 : ℝ) < (rhoLo : ℝ) := by exact_mod_cast hrhoPos
    nlinarith [hr.1]
  have hz : (((dx : ℂ) + Complex.I * (dy : ℂ)) / ((dz : ℂ) + (r : ℂ))) =
      (((dx : ℝ) / ((dz : ℝ) + r) : ℝ) : ℂ) +
        Complex.I * (((dy : ℝ) / ((dz : ℝ) + r) : ℝ) : ℂ) := by
    have hdC : ((dz : ℂ) + (r : ℂ)) ≠ 0 := by
      have hd_eq : ((dz : ℂ) + (r : ℂ)) = (((dz : ℝ) + r : ℝ) : ℂ) := by push_cast; ring
      rw [hd_eq]
      exact Complex.ofReal_ne_zero.mpr hden_ne
    push_cast
    field_simp [hdC]
  rw [hz]
  constructor
  · simpa only [cslopeIv, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] using
      slopeIv3D_mem hS hdz hrhoPos hr
  · simpa only [cslopeIv, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, one_mul, zero_add] using
      slopeIv3D_mem hS hdz hrhoPos hr

end CFpIv

noncomputable def evalListC : List ℂ → Polynomial ℂ
  | [] => 0
  | a :: as => Polynomial.C a + Polynomial.X * evalListC as

lemma coeff_evalListC (ps : List ℂ) (k : ℕ) : (evalListC ps).coeff k = ps.getD k 0 := by
  induction ps generalizing k with
  | nil => simp [evalListC]
  | cons a as ih =>
    cases k with
    | zero => simp [evalListC]
    | succ k => simp [evalListC, ih]

private lemma evalListC_append_zero (as : List ℂ) : evalListC (as ++ [0]) = evalListC as := by
  induction as with
  | nil => simp [evalListC]
  | cons a as ih => simp [evalListC, ih]

noncomputable def scaleListC (s : ℂ) : List ℂ → List ℂ
  | [] => []
  | a :: as => (s * a) :: scaleListC s as

noncomputable def addListC : List ℂ → List ℂ → List ℂ
  | [], bs => bs
  | as, [] => as
  | a :: as, b :: bs => (a + b) :: addListC as bs

noncomputable def mulLinListC (a b : ℂ) (ps : List ℂ) : List ℂ :=
  addListC (scaleListC a ps ++ [0]) (0 :: scaleListC b ps)

lemma evalListC_scaleListC (s : ℂ) (ps : List ℂ) :
    evalListC (scaleListC s ps) = Polynomial.C s * evalListC ps := by
  induction ps with
  | nil => simp [scaleListC, evalListC]
  | cons a as ih =>
    simp only [scaleListC, evalListC, ih, map_mul]
    ring

lemma evalListC_addListC (as bs : List ℂ) :
    evalListC (addListC as bs) = evalListC as + evalListC bs := by
  induction as generalizing bs with
  | nil => cases bs <;> simp [addListC, evalListC]
  | cons a as ih =>
    cases bs with
    | nil => simp [addListC, evalListC]
    | cons b bs =>
      simp only [addListC, evalListC, ih, map_add]
      ring

lemma evalListC_mulLinListC (a b : ℂ) (ps : List ℂ) :
    evalListC (mulLinListC a b ps) = (Polynomial.C a + Polynomial.C b * Polynomial.X) * evalListC ps := by
  unfold mulLinListC
  rw [evalListC_addListC, evalListC_append_zero, evalListC_scaleListC]
  simp only [evalListC, map_zero, zero_add, evalListC_scaleListC]
  ring

def ListCFpMem (S : ℤ) (ivs : List CFpIv) (ps : List ℂ) : Prop :=
  ∀ k : ℕ, CFpIv.CFpMem S (ivs.getD k CFpIv.zero) (ps.getD k 0)

def scaleListCIv (S : ℤ) (c : CFpIv) : List CFpIv → List CFpIv
  | [] => []
  | a :: as => CFpIv.mul S c a :: scaleListCIv S c as

def addListCIv : List CFpIv → List CFpIv → List CFpIv
  | [], bs => bs
  | as, [] => as
  | a :: as, b :: bs => CFpIv.add a b :: addListCIv as bs

def mulLinListCIv (S : ℤ) (f0 f1 : CFpIv) (ivs : List CFpIv) : List CFpIv :=
  addListCIv (scaleListCIv S f0 ivs ++ [CFpIv.zero]) (CFpIv.zero :: scaleListCIv S f1 ivs)

private lemma cfpIv_add_zero_left (a : CFpIv) : CFpIv.add CFpIv.zero a = a := by
  rcases a with ⟨⟨alo, ahi⟩, ⟨blo, bhi⟩⟩
  simp [CFpIv.add, CFpIv.zero, FpIv.add, FpIv.zero]

private lemma cfpIv_add_zero_right (a : CFpIv) : CFpIv.add a CFpIv.zero = a := by
  rcases a with ⟨⟨alo, ahi⟩, ⟨blo, bhi⟩⟩
  simp [CFpIv.add, CFpIv.zero, FpIv.add, FpIv.zero]

private lemma getD_scaleListC (s : ℂ) (ps : List ℂ) (k : ℕ) :
    (scaleListC s ps).getD k 0 = s * ps.getD k 0 := by
  induction ps generalizing k with
  | nil => simp [scaleListC]
  | cons a as ih =>
    cases k with
    | zero => simp [scaleListC]
    | succ k =>
      simpa [scaleListC, List.getD_eq_getElem?_getD] using ih k

private lemma getD_addListC (as bs : List ℂ) (k : ℕ) :
    (addListC as bs).getD k 0 = as.getD k 0 + bs.getD k 0 := by
  induction as generalizing bs k with
  | nil => cases bs <;> simp [addListC]
  | cons a as ih =>
    cases bs with
    | nil => simp [addListC]
    | cons b bs =>
      cases k with
      | zero => simp [addListC]
      | succ k => simpa [addListC, List.getD_eq_getElem?_getD] using ih bs k

private lemma getD_addListCIv (as bs : List CFpIv) (k : ℕ) :
    (addListCIv as bs).getD k CFpIv.zero =
      CFpIv.add (as.getD k CFpIv.zero) (bs.getD k CFpIv.zero) := by
  induction as generalizing bs k with
  | nil =>
    cases bs with
    | nil => simp [addListCIv, cfpIv_add_zero_left]
    | cons b bs => cases k <;> simp [addListCIv, cfpIv_add_zero_left]
  | cons a as ih =>
    cases bs with
    | nil => cases k <;> simp [addListCIv, cfpIv_add_zero_right]
    | cons b bs =>
      cases k with
      | zero => simp [addListCIv]
      | succ k => simpa [addListCIv, List.getD_eq_getElem?_getD] using ih bs k

private lemma getD_append_zero_C (ps : List ℂ) (k : ℕ) :
    (ps ++ [0]).getD k 0 = ps.getD k 0 := by
  induction ps generalizing k with
  | nil => cases k <;> simp
  | cons a as ih =>
    cases k with
    | zero => simp
    | succ k => simpa [List.getD_eq_getElem?_getD] using ih k

private lemma getD_append_zero_CIv (ivs : List CFpIv) (k : ℕ) :
    (ivs ++ [CFpIv.zero]).getD k CFpIv.zero = ivs.getD k CFpIv.zero := by
  induction ivs generalizing k with
  | nil => cases k <;> simp
  | cons a as ih =>
    cases k with
    | zero => simp
    | succ k => simpa [List.getD_eq_getElem?_getD] using ih k

lemma scaleListCIv_mem {S : ℤ} (hS : 0 < S) {cIv : CFpIv} {c : ℂ}
    (hc : CFpIv.CFpMem S cIv c) {ivs : List CFpIv} {ps : List ℂ}
    (hps : ListCFpMem S ivs ps) :
    ListCFpMem S (scaleListCIv S cIv ivs) (scaleListC c ps) := by
  intro k
  induction ivs generalizing ps k with
  | nil =>
    rw [scaleListCIv, List.getD_nil, getD_scaleListC]
    have h0 : CFpIv.CFpMem S CFpIv.zero (ps.getD k 0) := by simpa using hps k
    have hre0 : (ps.getD k 0).re = 0 := by
      have hS_pos : (0 : ℝ) < (S : ℝ) := by exact_mod_cast hS
      have : (0 : ℝ) ≤ (S : ℝ) * (ps.getD k 0).re ∧ (S : ℝ) * (ps.getD k 0).re ≤ 0 := by
        simpa [CFpIv.CFpMem, CFpIv.zero, FpIv.FpMem, FpIv.zero] using h0.1
      nlinarith
    have him0 : (ps.getD k 0).im = 0 := by
      have hS_pos : (0 : ℝ) < (S : ℝ) := by exact_mod_cast hS
      have : (0 : ℝ) ≤ (S : ℝ) * (ps.getD k 0).im ∧ (S : ℝ) * (ps.getD k 0).im ≤ 0 := by
        simpa [CFpIv.CFpMem, CFpIv.zero, FpIv.FpMem, FpIv.zero] using h0.2
      nlinarith
    have hzero : ps.getD k 0 = 0 := Complex.ext hre0 him0
    rw [hzero, mul_zero]
    exact CFpIv.zero_mem S
  | cons a as ih =>
    cases ps with
    | nil =>
      have hhd : CFpIv.CFpMem S a 0 := by simpa using hps 0
      have htl : ListCFpMem S as [] := fun m => by simpa using hps (m + 1)
      cases k with
      | zero => simpa [scaleListCIv, scaleListC] using CFpIv.mul_mem hS hc hhd
      | succ k =>
        have hih := ih htl k
        simpa [scaleListCIv, scaleListC, List.getD_eq_getElem?_getD] using hih
    | cons b bs =>
      have hhd : CFpIv.CFpMem S a b := by simpa using hps 0
      have htl : ListCFpMem S as bs := fun m => by simpa using hps (m + 1)
      cases k with
      | zero => simpa [scaleListCIv, scaleListC] using CFpIv.mul_mem hS hc hhd
      | succ k =>
        simpa [scaleListCIv, scaleListC] using ih htl k

lemma addListCIv_mem {S : ℤ} {asIv bsIv : List CFpIv} {asC bsC : List ℂ}
    (ha : ListCFpMem S asIv asC) (hb : ListCFpMem S bsIv bsC) :
    ListCFpMem S (addListCIv asIv bsIv) (addListC asC bsC) := by
  intro k
  rw [getD_addListCIv, getD_addListC]
  exact CFpIv.add_mem (ha k) (hb k)

lemma mulLinListCIv_mem {S : ℤ} (hS : 0 < S) {f0Iv f1Iv : CFpIv} {f0 f1 : ℂ}
    (hf0 : CFpIv.CFpMem S f0Iv f0) (hf1 : CFpIv.CFpMem S f1Iv f1)
    {ivs : List CFpIv} {ps : List ℂ} (hps : ListCFpMem S ivs ps) :
    ListCFpMem S (mulLinListCIv S f0Iv f1Iv ivs) (mulLinListC f0 f1 ps) := by
  unfold mulLinListCIv mulLinListC
  refine addListCIv_mem ?_ ?_
  · intro k
    rw [getD_append_zero_CIv, getD_append_zero_C]
    exact scaleListCIv_mem hS hf0 hps k
  · intro k
    cases k with
    | zero => simpa using CFpIv.zero_mem S
    | succ k => simpa using scaleListCIv_mem hS hf1 hps k

def stepPolyCIv {n : ℕ} (S : ℤ) (wIv : Fin n → Fin n → CFpIv) (i : Fin n)
    (ivs : List CFpIv) (j : Fin n) : List CFpIv :=
  if j = i then ivs
  else if j < i then
    mulLinListCIv S (CFpIv.neg (CFpIv.conj (wIv j i))) (CFpIv.ofInt S 1) ivs
  else
    mulLinListCIv S (CFpIv.ofInt S 1) (wIv i j) ivs

def polyListCIv {n : ℕ} (S : ℤ) (wIv : Fin n → Fin n → CFpIv) (i : Fin n) : List CFpIv :=
  (List.finRange n).foldl (stepPolyCIv S wIv i) [CFpIv.ofInt S 1]

noncomputable def stepPolyC {n : ℕ} (w : Fin n → Fin n → ℂ) (i : Fin n)
    (ps : List ℂ) (j : Fin n) : List ℂ :=
  if j = i then ps
  else if j < i then mulLinListC (-star (w j i)) 1 ps
  else mulLinListC 1 (w i j) ps

noncomputable def polyListC {n : ℕ} (w : Fin n → Fin n → ℂ) (i : Fin n) : List ℂ :=
  (List.finRange n).foldl (stepPolyC w i) [1]

lemma polyListCIv_mem {n : ℕ} {S : ℤ} (hS : 0 < S)
    {wIv : Fin n → Fin n → CFpIv} {w : Fin n → Fin n → ℂ}
    (hw : ∀ i j : Fin n, i < j → CFpIv.CFpMem S (wIv i j) (w i j)) (i : Fin n) :
    ListCFpMem S (polyListCIv S wIv i) (polyListC w i) := by
  have hinit : ListCFpMem S [CFpIv.ofInt S 1] [1] := by
    intro k
    cases k with
    | zero => simpa using CFpIv.ofInt_mem S 1
    | succ k => simp [CFpIv.zero_mem S]
  have hfold : ∀ (l : List (Fin n)) (ivs : List CFpIv) (ps : List ℂ),
      ListCFpMem S ivs ps →
      ListCFpMem S (l.foldl (stepPolyCIv S wIv i) ivs) (l.foldl (stepPolyC w i) ps) := by
    intro l
    induction l with
    | nil => intro ivs ps h; exact h
    | cons j js ih =>
      intro ivs ps h
      apply ih
      by_cases hji : j = i
      · simp [stepPolyCIv, stepPolyC, hji, h]
      · by_cases hlt : j < i
        · simp only [stepPolyCIv, stepPolyC, hji, hlt, ↓reduceIte]
          exact mulLinListCIv_mem hS (CFpIv.neg_mem (CFpIv.conj_mem (hw j i hlt)))
            (by simpa using CFpIv.ofInt_mem S 1) h
        · have hij : i < j := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hji)
          simp only [stepPolyCIv, stepPolyC, hji, hlt, ↓reduceIte]
          exact mulLinListCIv_mem hS (by simpa using CFpIv.ofInt_mem S 1) (hw i j hij) h
  exact hfold (List.finRange n) [CFpIv.ofInt S 1] [1] hinit

lemma evalListC_polyListC_eq {n : ℕ} (w : Fin n → Fin n → ℂ) (ψ : Fin n → Fin n → Fin 2 → ℂ)
    (hψ_lt : ∀ i j, j < i → ψ i j = ![-star (w j i), 1])
    (hψ_gt : ∀ i j, i < j → ψ i j = ![1, w i j]) (i : Fin n) :
    evalListC (polyListC w i) = atiyahPoly ψ i := by
  classical
  have hfold : ∀ (l : List (Fin n)) (ps : List ℂ),
      evalListC (l.foldl (stepPolyC w i) ps) =
        evalListC ps *
          (l.map fun j =>
            if j = i then (1 : Polynomial ℂ)
            else Polynomial.C (ψ i j 0) + Polynomial.C (ψ i j 1) * Polynomial.X).prod := by
    intro l
    induction l with
    | nil => intro ps; simp
    | cons j js ih =>
      intro ps
      simp only [List.foldl_cons, List.map_cons, List.prod_cons, ih]
      by_cases hji : j = i
      · simp [stepPolyC, hji]
      · by_cases hlt : j < i
        · have hfac : Polynomial.C (ψ i j 0) + Polynomial.C (ψ i j 1) * Polynomial.X =
              Polynomial.C (-star (w j i)) + Polynomial.C 1 * Polynomial.X := by
            rw [hψ_lt i j hlt]
            simp
          simp only [stepPolyC, hji, hlt, ↓reduceIte, evalListC_mulLinListC, hfac]
          ring
        · have hij : i < j := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hji)
          have hfac : Polynomial.C (ψ i j 0) + Polynomial.C (ψ i j 1) * Polynomial.X =
              Polynomial.C 1 + Polynomial.C (w i j) * Polynomial.X := by
            rw [hψ_gt i j hij]
            simp
          simp only [stepPolyC, hji, hlt, ↓reduceIte, evalListC_mulLinListC, hfac]
          ring
  unfold polyListC
  rw [hfold (List.finRange n) [1]]
  have h1 : evalListC ([1] : List ℂ) = 1 := by simp [evalListC]
  rw [h1, one_mul]
  have hlist :
      ((List.finRange n).map fun j =>
          if j = i then (1 : Polynomial ℂ)
          else Polynomial.C (ψ i j 0) + Polynomial.C (ψ i j 1) * Polynomial.X).prod =
        ∏ j : Fin n,
          if j = i then (1 : Polynomial ℂ)
          else Polynomial.C (ψ i j 0) + Polynomial.C (ψ i j 1) * Polynomial.X := by
    rw [← Multiset.prod_coe, ← Multiset.map_coe]
    exact (Finset.prod_eq_multiset_prod Finset.univ _).symm
  rw [hlist]
  have hsplit := (Finset.mul_prod_erase Finset.univ
    (fun j => if j = i then (1 : Polynomial ℂ)
      else Polynomial.C (ψ i j 0) + Polynomial.C (ψ i j 1) * Polynomial.X)
    (Finset.mem_univ i)).symm
  rw [hsplit]
  simp only [↓reduceIte, one_mul, atiyahPoly]
  refine Finset.prod_congr rfl fun j hj => ?_
  have hij : j ≠ i := (Finset.mem_erase.mp hj).1
  simp [hij]

/-- Memoize a `Fin m`-indexed table as a concrete `List`. -/
def memoFin {α : Type*} {m : ℕ} (_d : α) (f : Fin m → α) : List α :=
  List.ofFn f

def readMemo {α : Type*} {m : ℕ} (d : α) (xs : List α) (i : Fin m) : α :=
  xs.getD i.1 d

lemma readMemo_memoFin {α : Type*} {m : ℕ} (d : α) (f : Fin m → α) (i : Fin m) :
    readMemo d (memoFin d f) i = f i := by
  simp [readMemo, memoFin, List.getD_eq_getElem?_getD]

/-- Recursive complex interval determinant matching the `1x1`-base `foldl` Laplace expansion. -/
def detRecFinCIv (S : ℤ) : ∀ {m : ℕ}, (Fin m → Fin m → CFpIv) → CFpIv
  | 0, _ => CFpIv.ofInt S 1
  | 1, A => A 0 0
  | m + 2, A =>
    (List.finRange (m + 2)).foldl
      (fun acc j =>
        let sub : Fin (m + 1) → Fin (m + 1) → CFpIv := fun r c => A r.succ (j.succAbove c)
        let term := CFpIv.mul S (A 0 j) (detRecFinCIv S sub)
        if j.1 % 2 = 0 then CFpIv.add acc term else CFpIv.sub acc term)
      CFpIv.zero

private lemma foldl_altSum_mem {k : ℕ} {S : ℤ} (fIv : Fin k → CFpIv) (f : Fin k → ℂ)
    (hf : ∀ j, CFpIv.CFpMem S (fIv j) (f j)) (l : List (Fin k))
    (accIv : CFpIv) (acc : ℂ) (hacc : CFpIv.CFpMem S accIv acc) :
    CFpIv.CFpMem S
      (l.foldl
        (fun a j => if j.1 % 2 = 0 then CFpIv.add a (fIv j) else CFpIv.sub a (fIv j))
        accIv)
      (acc + (l.map fun (j : Fin k) => (-1 : ℂ) ^ j.1 * f j).sum) := by
  induction l generalizing accIv acc with
  | nil => simpa using hacc
  | cons j js ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    by_cases hj : j.1 % 2 = 0
    · obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hj
      have hpow : (-1 : ℂ) ^ j.1 = 1 := by
        rw [hq, pow_mul]; norm_num
      have hacc' : CFpIv.CFpMem S (CFpIv.add accIv (fIv j)) (acc + f j) :=
        CFpIv.add_mem hacc (hf j)
      have hsum :
          acc + ((-1 : ℂ) ^ j.1 * f j + (js.map fun (x : Fin k) => (-1 : ℂ) ^ x.1 * f x).sum) =
          (acc + f j) + (js.map fun (x : Fin k) => (-1 : ℂ) ^ x.1 * f x).sum := by
        rw [hpow]; ring
      simpa only [hj, ↓reduceIte, hsum] using ih (CFpIv.add accIv (fIv j)) (acc + f j) hacc'
    · have hm : j.1 % 2 = 1 := by omega
      have hpow : (-1 : ℂ) ^ j.1 = -1 := by
        calc
          (-1 : ℂ) ^ j.1 = (-1 : ℂ) ^ (2 * (j.1 / 2) + 1) := by congr 1; omega
          _ = -1 := by rw [pow_add, pow_mul]; norm_num
      have hacc' : CFpIv.CFpMem S (CFpIv.sub accIv (fIv j)) (acc - f j) :=
        CFpIv.sub_mem hacc (hf j)
      have hsum :
          acc + ((-1 : ℂ) ^ j.1 * f j + (js.map fun (x : Fin k) => (-1 : ℂ) ^ x.1 * f x).sum) =
          (acc - f j) + (js.map fun (x : Fin k) => (-1 : ℂ) ^ x.1 * f x).sum := by
        rw [hpow]; ring
      simpa only [hj, ↓reduceIte, hsum] using ih (CFpIv.sub accIv (fIv j)) (acc - f j) hacc'

lemma detRecFinCIv_mem {S : ℤ} (hS : 0 < S) :
    ∀ {m : ℕ} {AIv : Fin m → Fin m → CFpIv} {A : Matrix (Fin m) (Fin m) ℂ},
      (∀ i j, CFpIv.CFpMem S (AIv i j) (A i j)) →
      CFpIv.CFpMem S (detRecFinCIv S AIv) A.det
  | 0, _, A, _ => by
    rw [Matrix.det_fin_zero]
    simpa [detRecFinCIv] using CFpIv.ofInt_mem S 1
  | 1, AIv, A, hA => by
    simpa [detRecFinCIv, Matrix.det_succ_row_zero] using hA 0 0
  | m + 2, AIv, A, hA => by
    have hterms :
        ∀ j : Fin (m + 2),
          CFpIv.CFpMem S
            (CFpIv.mul S (AIv 0 j)
              (detRecFinCIv S fun r c => AIv r.succ (j.succAbove c)))
            (A 0 j * (A.submatrix Fin.succ j.succAbove).det) := by
      intro j
      exact CFpIv.mul_mem hS (hA 0 j)
        (detRecFinCIv_mem hS fun r c => hA r.succ (j.succAbove c))
    have hfold := foldl_altSum_mem
      (fun j => CFpIv.mul S (AIv 0 j)
        (detRecFinCIv S fun r c => AIv r.succ (j.succAbove c)))
      (fun j => A 0 j * (A.submatrix Fin.succ j.succAbove).det)
      hterms (List.finRange (m + 2)) CFpIv.zero 0 (CFpIv.zero_mem S)
    have hdet : A.det =
        0 + ((List.finRange (m + 2)).map fun (j : Fin (m + 2)) =>
          (-1 : ℂ) ^ j.1 * (A 0 j * (A.submatrix Fin.succ j.succAbove).det)).sum := by
      rw [zero_add, Matrix.det_succ_row_zero]
      have hl :
          ((List.finRange (m + 2)).map fun (j : Fin (m + 2)) =>
            (-1 : ℂ) ^ j.1 * (A 0 j * (A.submatrix Fin.succ j.succAbove).det)).sum =
          ∑ j : Fin (m + 2),
            (-1 : ℂ) ^ (j : ℕ) * A 0 j * (A.submatrix Fin.succ j.succAbove).det := by
        rw [Fin.sum_univ_def]
        congr 1
        refine List.map_congr_left fun j _ => ?_
        ring
      exact hl.symm
    change CFpIv.CFpMem S (detRecFinCIv S AIv) A.det
    rw [hdet]
    exact hfold

end ComplexIntervals

/-! ## Part 2: Permutation Invariance and Weakly-Ordered 3D Stereographic Spinors -/

section PermAndStereo

def permPoints {n : ℕ} (x : DistinctPoints n) (σ : Equiv.Perm (Fin n)) : DistinctPoints n :=
  ⟨fun i => x.1 (σ i), fun _ _ hij => x.2 _ _ (σ.injective.ne hij)⟩

private lemma atiyahDet_swap_lt {n : ℕ} (x : DistinctPoints n) {u v : Fin n} (huv : u < v) :
    atiyahDet (permPoints x (Equiv.swap u v)) = atiyahDet x := by
  classical
  let τ : Equiv.Perm (Fin n) := Equiv.swap u v
  let ψ : Fin n → Fin n → Fin 2 → ℂ :=
    fun i j => canonicalSpinor (unitDir (x.1 i) (x.1 j))
  let ψ' : Fin n → Fin n → Fin 2 → ℂ :=
    fun i j => canonicalSpinor (unitDir ((permPoints x τ).1 i) ((permPoints x τ).1 j))
  have hψ' : ∀ i j, ψ' i j = ψ (τ i) (τ j) := fun _ _ => rfl
  have hpoly : ∀ i : Fin n, atiyahPoly ψ' i = atiyahPoly ψ (τ i) := by
    intro i
    simp only [atiyahPoly]
    refine Finset.prod_bij (fun j _ => τ j) ?_ ?_ ?_ ?_
    · intro j hj
      exact Finset.mem_erase.mpr ⟨τ.injective.ne (Finset.mem_erase.mp hj).1, Finset.mem_univ _⟩
    · intro j₁ _ j₂ _ heq; exact τ.injective heq
    · intro b hb
      refine ⟨τ b, Finset.mem_erase.mpr ⟨fun he => ?_, Finset.mem_univ _⟩, ?_⟩
      · have : b = τ i := by
          have := congrArg τ he
          simpa [τ] using this
        exact (Finset.mem_erase.mp hb).1 this
      · simp [τ]
    · intro j _; rfl
  have hmat : atiyahMat ψ' = (atiyahMat ψ).submatrix τ id := by
    ext i k
    simp [atiyahMat, hpoly i]
  have hdet_mat : (atiyahMat ψ').det = -(atiyahMat ψ).det := by
    have hsgn : Equiv.Perm.sign τ = -1 := Equiv.Perm.sign_swap (ne_of_lt huv)
    rw [hmat, Matrix.det_permute τ (atiyahMat ψ), hsgn]
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
      · have hnot : ¬ (τ b < τ a) ↔ False := by
          have hlt : τ b < τ a := lt_of_le_of_ne (not_lt.mp h1) (fun eq => hab.ne (τ.injective eq.symm))
          simp [hlt]
        simp only [h1, ↓reduceDIte, hττ]
        have hba : ¬ b < a := not_lt_of_gt hab
        simp [hba]
    have hterm : ∀ e : E,
        omega (ψ' e.1.1 e.1.2) (ψ' e.1.2 e.1.1) =
          (if τ e.1.1 < τ e.1.2 then (1 : ℂ) else -1) *
            omega (ψ (swapPair e).1.1 (swapPair e).1.2) (ψ (swapPair e).1.2 (swapPair e).1.1) := by
      intro e
      by_cases h1 : τ e.1.1 < τ e.1.2
      · simp only [h1, ↓reduceIte, ↓reduceDIte, swapPair, one_mul, hψ']
      · simp only [h1, ↓reduceIte, ↓reduceDIte, swapPair, hψ']
        rw [omega_swap]; ring
    have hprod_split :
        atiyahDen ψ' =
          (∏ e : E, if τ e.1.1 < τ e.1.2 then (1 : ℂ) else -1) *
            (∏ e : E, omega (ψ (swapPair e).1.1 (swapPair e).1.2) (ψ (swapPair e).1.2 (swapPair e).1.1)) := by
      simp only [atiyahDen]
      calc
        ∏ e : E, omega (ψ' e.1.1 e.1.2) (ψ' e.1.2 e.1.1)
          = ∏ e : E,
              (if τ e.1.1 < τ e.1.2 then (1 : ℂ) else -1) *
                omega (ψ (swapPair e).1.1 (swapPair e).1.2) (ψ (swapPair e).1.2 (swapPair e).1.1) :=
            Finset.prod_congr rfl fun e _ => hterm e
        _ = _ := Finset.prod_mul_distrib
    have hprod_bij :
        (∏ e : E, omega (ψ (swapPair e).1.1 (swapPair e).1.2) (ψ (swapPair e).1.2 (swapPair e).1.1)) =
          atiyahDen ψ := by
      refine Finset.prod_bij (fun e _ => swapPair e) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
      · intro e₁ _ e₂ _ heq
        have := congrArg swapPair heq
        simpa [hinv] using this
      · intro e _
        exact ⟨swapPair e, Finset.mem_univ _, hinv e⟩
      · intro _ _; rfl
    let S : Finset E := Finset.univ.filter (fun e : E => ¬ τ e.1.1 < τ e.1.2)
    have hsign_prod : (∏ e : E, if τ e.1.1 < τ e.1.2 then (1 : ℂ) else -1) = (-1 : ℂ) ^ S.card := by
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun e : E => ¬ τ e.1.1 < τ e.1.2)]
      have h1 : (∏ e ∈ S, if τ e.1.1 < τ e.1.2 then (1 : ℂ) else -1) = (-1 : ℂ) ^ S.card := by
        calc
          (∏ e ∈ S, if τ e.1.1 < τ e.1.2 then (1 : ℂ) else -1)
            = ∏ _e ∈ S, (-1 : ℂ) := Finset.prod_congr rfl fun e he => by
                have hn : ¬ τ e.1.1 < τ e.1.2 := (Finset.mem_filter.mp he).2
                simp [hn]
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
      have ha_lt : a.1 < n := a.isLt
      have hb_lt : b.1 < n := b.isLt
      have hu_lt : u.1 < n := u.isLt
      have hv_lt : v.1 < n := v.isLt
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

lemma atiyahDet_swap {n : ℕ} (x : DistinctPoints n) (u v : Fin n) :
    atiyahDet (permPoints x (Equiv.swap u v)) = atiyahDet x := by
  rcases lt_trichotomy u v with huv | rfl | hvu
  · exact atiyahDet_swap_lt x huv
  · have h1 : permPoints x (Equiv.swap u u) = x := Subtype.ext (by ext i k; simp [permPoints])
    rw [h1]
  · rw [Equiv.swap_comm]
    exact atiyahDet_swap_lt x hvu

lemma atiyahDet_perm {n : ℕ} (x : DistinctPoints n) (σ : Equiv.Perm (Fin n)) :
    atiyahDet (permPoints x σ) = atiyahDet x := by
  revert x
  refine Equiv.Perm.swap_induction_on σ ?_ ?_
  · intro x
    have h1 : permPoints x 1 = x := Subtype.ext (by ext i k; simp [permPoints])
    rw [h1]
  · intro f u v _ ih x
    have hcomp : permPoints x (Equiv.swap u v * f) = permPoints (permPoints x (Equiv.swap u v)) f :=
      Subtype.ext (by ext i k; simp [permPoints, Equiv.Perm.mul_apply])
    rw [hcomp, ih (permPoints x (Equiv.swap u v)), atiyahDet_swap x u v]

noncomputable def stereoDenomR (a b : Fin 3 → ℝ) : ℝ :=
  (b 2 - a 2) + euclidNorm (fun k => b k - a k)

noncomputable def stereoSlope {n : ℕ} (p : Fin n → Fin 3 → ℝ) (i j : Fin n) : ℂ :=
  (((p j 0 - p i 0 : ℝ) : ℂ) + Complex.I * ((p j 1 - p i 1 : ℝ) : ℂ)) /
    (stereoDenomR (p i) (p j) : ℂ)

noncomputable def stereoSpinor {n : ℕ} (p : Fin n → Fin 3 → ℝ) (i j : Fin n) : Fin 2 → ℂ :=
  if i = j then ![1, 0]
  else if i < j then ![1, stereoSlope p i j]
  else ![-star (stereoSlope p j i), 1]

noncomputable def stereoDenR {n : ℕ} (p : Fin n → Fin 3 → ℝ) : ℝ :=
  ∏ e : { p : Fin n × Fin n // p.1 < p.2 }, (1 + Complex.normSq (stereoSlope p e.1.1 e.1.2))

lemma stereoDenomR_pos {a b : Fin 3 → ℝ} (hab : a ≠ b) (hz : a 2 ≤ b 2) :
    0 < stereoDenomR a b := by
  unfold stereoDenomR
  have hr : 0 < euclidNorm (fun k => b k - a k) := euclidNorm_pos_of_ne hab
  linarith [sub_nonneg.mpr hz]

lemma stereoDenR_pos {n : ℕ} (p : Fin n → Fin 3 → ℝ) : 0 < stereoDenR p := by
  refine Finset.prod_pos fun e _ => ?_
  have hns : 0 ≤ Complex.normSq (stereoSlope p e.1.1 e.1.2) := Complex.normSq_nonneg _
  linarith

private lemma pauliDot_stereoPair {a b : Fin 3 → ℝ} (hab : a ≠ b) (hz : a 2 ≤ b 2) :
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
  have hrsqC : (dx : ℂ) ^ 2 + (dy : ℂ) ^ 2 + (dz : ℂ) ^ 2 = (r : ℂ) ^ 2 := by
    exact_mod_cast hrsq
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr_pos.ne'
  have hdenC : ((dz + r : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hden_pos.ne'
  have hdenC' : (dz : ℂ) + (r : ℂ) ≠ 0 := by simpa [Complex.ofReal_add] using hdenC
  have hden_eq : (stereoDenomR a b : ℂ) = ((dz + r : ℝ) : ℂ) := by
    simp [stereoDenomR, dz, r]
  have hstar_w :
      star ((((dx : ℂ) + Complex.I * (dy : ℂ)) / ((dz + r : ℝ) : ℂ))) =
        ((dx : ℂ) - Complex.I * (dy : ℂ)) / ((dz + r : ℝ) : ℂ) := by
    simp [Complex.conj_ofReal, Complex.conj_I, sub_eq_add_neg]
  have hI2 : (Complex.I : ℂ) ^ 2 = -1 := Complex.I_sq
  constructor
  · ext k
    fin_cases k
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
        _ = (dz : ℂ) ^ 2 + (dz : ℂ) * (r : ℂ) + (dx : ℂ) ^ 2 + (dy : ℂ) ^ 2 := by rw [hI2]; ring
        _ = ((dx : ℂ) ^ 2 + (dy : ℂ) ^ 2 + (dz : ℂ) ^ 2) + (dz : ℂ) * (r : ℂ) := by ring
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
    ext k
    fin_cases k
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

lemma atiyahDet_eq_stereoMat_div {n : ℕ} (x : DistinctPoints n)
    (hz : Monotone (fun i => x.1 i 2)) :
    atiyahDet x = (atiyahMat (stereoSpinor x.1)).det / (stereoDenR x.1 : ℂ) := by
  have hne : ∀ i j : Fin n, i ≠ j →
      stereoSpinor x.1 i j 0 ≠ 0 ∨ stereoSpinor x.1 i j 1 ≠ 0 := by
    intro i j hij
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · left; simp [stereoSpinor, hij, hlt]
    · exact absurd rfl hij
    · right; simp [stereoSpinor, hij, not_lt_of_gt hgt]
  have hmul : ∀ i j : Fin n, i ≠ j →
      (pauliDot (unitDir (x.1 i) (x.1 j))).mulVec (stereoSpinor x.1 i j) =
        stereoSpinor x.1 i j := by
    intro i j hij
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · simp only [stereoSpinor, hij, ↓reduceIte, hlt]
      exact (pauliDot_stereoPair (x.2 i j hij) (hz hlt.le)).1
    · exact absurd rfl hij
    · have hnot : ¬ i < j := not_lt_of_gt hgt
      simp only [stereoSpinor, hij, ↓reduceIte, hnot]
      exact (pauliDot_stereoPair (x.2 j i hij.symm) (hz hgt.le)).2
  rw [atiyahDet_eq_of_posSpinors x (stereoSpinor x.1) hne hmul]
  unfold atiyahDetOfSpinors
  congr 1
  unfold atiyahDen stereoDenR
  rw [Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun e _ => ?_
  have hij : e.1.1 ≠ e.1.2 := ne_of_lt e.2
  have hji : e.1.2 ≠ e.1.1 := hij.symm
  have hnot : ¬ e.1.2 < e.1.1 := not_lt_of_gt e.2
  simp only [stereoSpinor, hij, hji, ↓reduceIte, e.2, hnot, omega,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  have hnormSq :
      stereoSlope x.1 e.1.1 e.1.2 * star (stereoSlope x.1 e.1.1 e.1.2) =
        ((Complex.normSq (stereoSlope x.1 e.1.1 e.1.2) : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [Complex.normSq_apply]
    · simp [Complex.normSq_apply]; ring
  rw [Complex.ofReal_add, Complex.ofReal_one, ← hnormSq]
  ring

end PermAndStereo

/-! ## Part 3: The Non-Coplanar 3D `n = 36` Family `x36Clamp`, Reality & Continuity -/

section X36Family

def x36BaseArr : List (ℤ × ℤ × ℤ) := [
  (0, 0, 0), (0, 0, 10), (0, 0, 20), (0, 0, 30), (0, 0, 40), (0, 0, 50),
  (0, 0, 60), (0, 0, 70), (0, 0, 80), (0, 0, 90), (0, 0, 100), (0, 0, 110),
  (0, 0, 120), (0, 0, 130), (0, 0, 140), (0, 0, 150), (0, 0, 160), (0, 0, 170),
  (520, 0, 104040), (-520, 0, 104040),
  (264, 448, 104040), (-264, -448, 104040),
  (-264, 448, 104040), (264, -448, 104040),
  (11960, 0, 107780), (-11960, 0, 107780),
  (6072, 10304, 107780), (-6072, -10304, 107780),
  (-6072, 10304, 107780), (6072, -10304, 107780),
  (0, 0, 107790), (0, 0, 107800), (0, 0, 107810),
  (0, 0, 107820), (0, 0, 107830), (0, 0, 107840)]

def x36BaseX (i : Fin 36) : ℤ := (x36BaseArr.getD i.1 (0, 0, 0)).1
def x36BaseY (i : Fin 36) : ℤ := (x36BaseArr.getD i.1 (0, 0, 0)).2.1
def x36BaseZ (i : Fin 36) : ℤ := (x36BaseArr.getD i.1 (0, 0, 0)).2.2

lemma x36BaseZ_monotone : Monotone x36BaseZ := by decide

lemma x36Base_distinct : ∀ i j : Fin 36, i ≠ j →
    x36BaseZ i ≠ x36BaseZ j ∨ x36BaseX i ≠ x36BaseX j ∨ x36BaseY i ≠ x36BaseY j := by
  decide

noncomputable def x36ClampRaw (t : ℝ) (i : Fin 36) : Fin 3 → ℝ :=
  ![(max t 1) * (x36BaseX i : ℝ), (max t 1) * (x36BaseY i : ℝ), (x36BaseZ i : ℝ)]

noncomputable def x36Clamp (t : ℝ) : DistinctPoints 36 :=
  ⟨x36ClampRaw t, by
    intro i j hij hEq
    have hs : max t 1 ≠ 0 := by linarith [le_max_right t (1 : ℝ)]
    have h0 : max t 1 * (x36BaseX i : ℝ) = max t 1 * (x36BaseX j : ℝ) := by
      simpa [x36ClampRaw] using congrFun hEq 0
    have h1 : max t 1 * (x36BaseY i : ℝ) = max t 1 * (x36BaseY j : ℝ) := by
      simpa [x36ClampRaw] using congrFun hEq 1
    have h2 : (x36BaseZ i : ℝ) = (x36BaseZ j : ℝ) := by
      simpa [x36ClampRaw] using congrFun hEq 2
    have hx : x36BaseX i = x36BaseX j := Int.cast_injective (mul_left_cancel₀ hs h0)
    have hy : x36BaseY i = x36BaseY j := Int.cast_injective (mul_left_cancel₀ hs h1)
    have hz : x36BaseZ i = x36BaseZ j := Int.cast_injective h2
    rcases x36Base_distinct i j hij with h | h | h
    · exact h hz
    · exact h hx
    · exact h hy⟩

lemma x36Clamp_z_monotone (t : ℝ) : Monotone (fun i => (x36Clamp t).1 i 2) := by
  intro i j hij
  exact Int.cast_le.mpr (x36BaseZ_monotone hij)

def Noncoplanar3D {n : ℕ} (p : Fin n → Fin 3 → ℝ) : Prop :=
  ¬ ∃ (a b c d : ℝ), (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) ∧
    ∀ i : Fin n, a * p i 0 + b * p i 1 + c * p i 2 = d

private lemma x36Clamp_coords (t : ℝ) (i : Fin 36) :
    (x36Clamp t).1 i 0 = max t 1 * (x36BaseX i : ℝ) ∧
      (x36Clamp t).1 i 1 = max t 1 * (x36BaseY i : ℝ) ∧
      (x36Clamp t).1 i 2 = (x36BaseZ i : ℝ) :=
  ⟨rfl, rfl, rfl⟩

theorem x36Clamp_noncoplanar (t : ℝ) : Noncoplanar3D (x36Clamp t).1 := by
  rintro ⟨a, b, c, d, hne, hall⟩
  have hs : (1 : ℝ) ≤ max t 1 := le_max_right t 1
  have h0 := hall 0
  rw [(x36Clamp_coords t 0).1, (x36Clamp_coords t 0).2.1, (x36Clamp_coords t 0).2.2] at h0
  have hd0 : d = 0 := by
    have hx0 : x36BaseX 0 = 0 ∧ x36BaseY 0 = 0 ∧ x36BaseZ 0 = 0 := by decide
    rw [hx0.1, hx0.2.1, hx0.2.2] at h0
    norm_num at h0
    linarith
  have h1 := hall 1
  rw [(x36Clamp_coords t 1).1, (x36Clamp_coords t 1).2.1, (x36Clamp_coords t 1).2.2, hd0] at h1
  have hc0 : c = 0 := by
    have hz1 : x36BaseX 1 = 0 ∧ x36BaseY 1 = 0 ∧ x36BaseZ 1 = 10 := by decide
    rw [hz1.1, hz1.2.1, hz1.2.2] at h1
    norm_num at h1
    exact h1
  have h18 := hall 18
  rw [(x36Clamp_coords t 18).1, (x36Clamp_coords t 18).2.1, (x36Clamp_coords t 18).2.2, hc0, hd0] at h18
  have ha0 : a = 0 := by
    have hx18 : x36BaseX 18 = 520 ∧ x36BaseY 18 = 0 := by decide
    rw [hx18.1, hx18.2] at h18
    have hpos : (0 : ℝ) < max t 1 * (520 : ℝ) := by linarith
    have hmul : a * (max t 1 * (520 : ℝ)) = 0 := by push_cast at h18; linarith
    exact (mul_eq_zero.mp hmul).resolve_right hpos.ne'
  have h20 := hall 20
  rw [(x36Clamp_coords t 20).1, (x36Clamp_coords t 20).2.1, (x36Clamp_coords t 20).2.2, ha0, hc0, hd0] at h20
  have hb0 : b = 0 := by
    have hy20 : x36BaseY 20 = 448 := by decide
    rw [hy20] at h20
    have hpos : (0 : ℝ) < max t 1 * (448 : ℝ) := by linarith
    have hmul : b * (max t 1 * (448 : ℝ)) = 0 := by push_cast at h20; linarith
    exact (mul_eq_zero.mp hmul).resolve_right hpos.ne'
  rcases hne with h | h | h
  · exact h ha0
  · exact h hb0
  · exact h hc0

def reflectPerm36 : Equiv.Perm (Fin 36) :=
  Equiv.swap ⟨20, by decide⟩ ⟨23, by decide⟩ *
    Equiv.swap ⟨21, by decide⟩ ⟨22, by decide⟩ *
    Equiv.swap ⟨26, by decide⟩ ⟨29, by decide⟩ *
    Equiv.swap ⟨27, by decide⟩ ⟨28, by decide⟩

lemma x36Base_reflect : ∀ i : Fin 36,
    x36BaseX (reflectPerm36 i) = x36BaseX i ∧
      x36BaseY (reflectPerm36 i) = -x36BaseY i ∧
      x36BaseZ (reflectPerm36 i) = x36BaseZ i := by
  decide

lemma atiyahDet_x36Clamp_im_zero (t : ℝ) : (atiyahDet (x36Clamp t)).im = 0 := by
  let x := x36Clamp t
  let q := permPoints x reflectPerm36
  have hperm : atiyahDet q = atiyahDet x := atiyahDet_perm x reflectPerm36
  have hqz : Monotone (fun i => q.1 i 2) := by
    intro i j hij
    change (x36Clamp t).1 (reflectPerm36 i) 2 ≤ (x36Clamp t).1 (reflectPerm36 j) 2
    have hzi : (x36Clamp t).1 (reflectPerm36 i) 2 = (x36BaseZ (reflectPerm36 i) : ℝ) := rfl
    have hzj : (x36Clamp t).1 (reflectPerm36 j) 2 = (x36BaseZ (reflectPerm36 j) : ℝ) := rfl
    rw [hzi, hzj, (x36Base_reflect i).2.2, (x36Base_reflect j).2.2]
    exact x36Clamp_z_monotone t hij
  have hslope : ∀ i j : Fin 36, stereoSlope q.1 i j = star (stereoSlope x.1 i j) := by
    intro i j
    have hq0i : q.1 i 0 = x.1 i 0 := by
      simp [q, x, permPoints, x36Clamp, x36ClampRaw, (x36Base_reflect i).1]
    have hq0j : q.1 j 0 = x.1 j 0 := by
      simp [q, x, permPoints, x36Clamp, x36ClampRaw, (x36Base_reflect j).1]
    have hq1i : q.1 i 1 = -x.1 i 1 := by
      simp [q, x, permPoints, x36Clamp, x36ClampRaw, (x36Base_reflect i).2.1]
    have hq1j : q.1 j 1 = -x.1 j 1 := by
      simp [q, x, permPoints, x36Clamp, x36ClampRaw, (x36Base_reflect j).2.1]
    have hq2i : q.1 i 2 = x.1 i 2 := by
      simp [q, x, permPoints, x36Clamp, x36ClampRaw, (x36Base_reflect i).2.2]
    have hq2j : q.1 j 2 = x.1 j 2 := by
      simp [q, x, permPoints, x36Clamp, x36ClampRaw, (x36Base_reflect j).2.2]
    have hden : stereoDenomR (q.1 i) (q.1 j) = stereoDenomR (x.1 i) (x.1 j) := by
      unfold stereoDenomR euclidNorm
      have hsq : (q.1 j 0 - q.1 i 0) ^ 2 + (q.1 j 1 - q.1 i 1) ^ 2 + (q.1 j 2 - q.1 i 2) ^ 2 =
          (x.1 j 0 - x.1 i 0) ^ 2 + (x.1 j 1 - x.1 i 1) ^ 2 + (x.1 j 2 - x.1 i 2) ^ 2 := by
        rw [hq0i, hq0j, hq1i, hq1j, hq2i, hq2j]; ring
      rw [hq2i, hq2j, hsq]
    unfold stereoSlope
    rw [hden, hq0i, hq0j, hq1i, hq1j]
    have hsub1 : (-x.1 j 1 - -x.1 i 1 : ℝ) = -(x.1 j 1 - x.1 i 1) := by ring
    rw [hsub1]
    simp [Complex.conj_ofReal, sub_eq_add_neg]
    ring
  have hsp : ∀ i j k, stereoSpinor q.1 i j k = starRingEnd ℂ (stereoSpinor x.1 i j k) := by
    intro i j k
    unfold stereoSpinor
    split_ifs <;> fin_cases k <;> simp [hslope, map_neg]
  have hpoly : ∀ i : Fin 36,
      atiyahPoly (stereoSpinor q.1) i = (atiyahPoly (stereoSpinor x.1) i).map (starRingEnd ℂ) := by
    intro i
    simp only [atiyahPoly, Polynomial.map_prod, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.map_X]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp [hsp i j 0, hsp i j 1]
  have hmat :
      atiyahMat (stereoSpinor q.1) = (starRingEnd ℂ).mapMatrix (atiyahMat (stereoSpinor x.1)) := by
    ext i k
    simp [atiyahMat, hpoly i, Polynomial.coeff_map]
  have hdenR : stereoDenR q.1 = stereoDenR x.1 := by
    refine Finset.prod_congr rfl fun e _ => ?_
    rw [hslope e.1.1 e.1.2]
    simp [Complex.normSq_apply]
  have hdet_star : atiyahDet q = starRingEnd ℂ (atiyahDet x) := by
    rw [atiyahDet_eq_stereoMat_div q hqz, atiyahDet_eq_stereoMat_div x (x36Clamp_z_monotone t),
      hmat, hdenR, ← RingHom.map_det (starRingEnd ℂ)]
    simp [Complex.conj_ofReal]
  have hself : starRingEnd ℂ (atiyahDet x) = atiyahDet x := hdet_star.symm.trans hperm
  have him := congrArg Complex.im hself
  simp at him
  linarith

private lemma continuous_poly_coeff_of_continuous {n : ℕ}
    {c0 c1 : ℝ → Fin n → ℂ}
    (hc0 : ∀ j, Continuous (fun t => c0 t j))
    (hc1 : ∀ j, Continuous (fun t => c1 t j)) :
    ∀ (S : Finset (Fin n)) (k : ℕ),
      Continuous (fun t => (∏ j ∈ S, (Polynomial.C (c0 t j) + Polynomial.C (c1 t j) * Polynomial.X)).coeff k) := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro k
    simp only [Finset.prod_empty, Polynomial.coeff_one]
    exact continuous_const
  | insert a s ha ih =>
    intro k
    have heq :
        (fun t => (∏ j ∈ insert a s,
            (Polynomial.C (c0 t j) + Polynomial.C (c1 t j) * Polynomial.X)).coeff k) =
          fun t => ∑ m ∈ Finset.HasAntidiagonal.antidiagonal k,
            ((Polynomial.C (c0 t a) + Polynomial.C (c1 t a) * Polynomial.X).coeff m.1) *
              ((∏ j ∈ s, (Polynomial.C (c0 t j) + Polynomial.C (c1 t j) * Polynomial.X)).coeff m.2) := by
      ext t
      rw [Finset.prod_insert ha, Polynomial.coeff_mul]
    rw [heq]
    have hterm : ∀ m ∈ Finset.HasAntidiagonal.antidiagonal k, Continuous fun t =>
        ((Polynomial.C (c0 t a) + Polynomial.C (c1 t a) * Polynomial.X).coeff m.1) *
          ((∏ j ∈ s, (Polynomial.C (c0 t j) + Polynomial.C (c1 t j) * Polynomial.X)).coeff m.2) := by
      intro m _
      refine Continuous.mul ?_ (ih m.2)
      rcases m with ⟨m1, m2⟩
      rcases m1 with _ | _ | m1'
      · simp only [Polynomial.coeff_add, Polynomial.coeff_C_zero, Polynomial.coeff_mul_X_zero, add_zero]
        exact hc0 a
      · simp only [Polynomial.coeff_add, Polynomial.coeff_C_succ, zero_add,
          Polynomial.coeff_mul_X, Polynomial.coeff_C_zero]
        exact hc1 a
      · simp only [Polynomial.coeff_add, Polynomial.coeff_C_succ, zero_add,
          Polynomial.coeff_mul_X]
        exact continuous_const
    fun_prop

private lemma stereoSlope_x36Clamp_continuous (i j : Fin 36) (hij : i < j) :
    Continuous (fun t : ℝ => stereoSlope (x36Clamp t).1 i j) := by
  let fx : ℝ → ℝ := fun t => max t 1 * ((x36BaseX j : ℝ) - (x36BaseX i : ℝ))
  let fy : ℝ → ℝ := fun t => max t 1 * ((x36BaseY j : ℝ) - (x36BaseY i : ℝ))
  let dz : ℝ := (x36BaseZ j : ℝ) - (x36BaseZ i : ℝ)
  have hmax : Continuous (fun t : ℝ => max t 1) := continuous_id.max continuous_const
  have hfx : Continuous fx := hmax.mul continuous_const
  have hfy : Continuous fy := hmax.mul continuous_const
  have heq : (fun t : ℝ => stereoSlope (x36Clamp t).1 i j) =
      fun t => ((fx t : ℂ) + Complex.I * (fy t : ℂ)) /
        ((dz + Real.sqrt (fx t ^ 2 + fy t ^ 2 + dz ^ 2) : ℝ) : ℂ) := by
    ext t
    have h0 : (x36Clamp t).1 j 0 - (x36Clamp t).1 i 0 = fx t := by
      simp [x36Clamp, x36ClampRaw, fx]; ring
    have h1 : (x36Clamp t).1 j 1 - (x36Clamp t).1 i 1 = fy t := by
      simp [x36Clamp, x36ClampRaw, fy]; ring
    have h2 : (x36Clamp t).1 j 2 - (x36Clamp t).1 i 2 = dz := rfl
    simp only [stereoSlope, stereoDenomR, euclidNorm, h0, h1, h2]
  rw [heq]
  have hnum : Continuous (fun t : ℝ => (fx t : ℂ) + Complex.I * (fy t : ℂ)) :=
    (Complex.continuous_ofReal.comp hfx).add
      (continuous_const.mul (Complex.continuous_ofReal.comp hfy))
  have hden : Continuous (fun t : ℝ => ((dz + Real.sqrt (fx t ^ 2 + fy t ^ 2 + dz ^ 2) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (continuous_const.add (((hfx.pow 2).add (hfy.pow 2)).add continuous_const).sqrt)
  refine hnum.div hden fun t => Complex.ofReal_ne_zero.mpr ?_
  have hr : 0 < Real.sqrt (fx t ^ 2 + fy t ^ 2 + dz ^ 2) := by
    have h0 : (x36Clamp t).1 j 0 - (x36Clamp t).1 i 0 = fx t := by
      simp [x36Clamp, x36ClampRaw, fx]; ring
    have h1 : (x36Clamp t).1 j 1 - (x36Clamp t).1 i 1 = fy t := by
      simp [x36Clamp, x36ClampRaw, fy]; ring
    have h2 : (x36Clamp t).1 j 2 - (x36Clamp t).1 i 2 = dz := rfl
    have heu : 0 < euclidNorm (fun k => (x36Clamp t).1 j k - (x36Clamp t).1 i k) :=
      euclidNorm_pos_of_ne ((x36Clamp t).2 i j hij.ne)
    simpa [euclidNorm, h0, h1, h2] using heu
  have hdz_nn : 0 ≤ dz := sub_nonneg.mpr (x36Clamp_z_monotone t hij.le)
  linarith

private lemma continuous_finset_prod_aux {α β ι : Type*} [TopologicalSpace α]
    [CommMonoid β] [TopologicalSpace β] [ContinuousMul β]
    (s : Finset ι) {f : ι → α → β} (hf : ∀ i ∈ s, Continuous (f i)) :
    Continuous (fun a => ∏ i ∈ s, f i a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using continuous_const
  | insert i s hi ih =>
    have h1 : Continuous (f i) := hf i (Finset.mem_insert_self i s)
    have h2 : Continuous (fun a => ∏ j ∈ s, f j a) :=
      ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    have heq : (fun a => ∏ j ∈ insert i s, f j a) = fun a => f i a * ∏ j ∈ s, f j a :=
      funext fun a => Finset.prod_insert hi
    rw [heq]
    exact h1.mul h2

private lemma continuous_stereoMat_x36Clamp_det_re :
    Continuous (fun t : ℝ => ((atiyahMat (stereoSpinor (x36Clamp t).1)).det).re) := by
  have hspinor_cont : ∀ i j : Fin 36, ∀ m : Fin 2,
      Continuous (fun t : ℝ => stereoSpinor (x36Clamp t).1 i j m) := by
    intro i j m
    by_cases hij : i = j
    · simp only [stereoSpinor, hij, ↓reduceIte]
      exact continuous_const
    · by_cases hlt : i < j
      · simp only [stereoSpinor, hij, ↓reduceIte, hlt]
        fin_cases m
        · exact continuous_const
        · exact stereoSlope_x36Clamp_continuous i j hlt
      · have hgt : j < i := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hij)
        simp only [stereoSpinor, hij, ↓reduceIte, hlt]
        fin_cases m
        · exact continuous_neg.comp (Complex.continuous_conj.comp (stereoSlope_x36Clamp_continuous j i hgt))
        · exact continuous_const
  have hmat_cont : ∀ i k : Fin 36,
      Continuous (fun t : ℝ => atiyahMat (stereoSpinor (x36Clamp t).1) i k) := by
    intro i k
    simpa [atiyahMat, atiyahPoly] using
      continuous_poly_coeff_of_continuous
        (c0 := fun t j => stereoSpinor (x36Clamp t).1 i j 0)
        (c1 := fun t j => stereoSpinor (x36Clamp t).1 i j 1)
        (fun j => hspinor_cont i j 0) (fun j => hspinor_cont i j 1)
        (Finset.univ.erase i) k.1
  exact Complex.continuous_re.comp
    (Continuous.matrix_det (continuous_pi fun i => continuous_pi fun k => hmat_cont i k))

private lemma continuous_stereoDenR_x36Clamp :
    Continuous (fun t : ℝ => stereoDenR (x36Clamp t).1) := by
  have hfac : ∀ e : { p : Fin 36 × Fin 36 // p.1 < p.2 }, Continuous fun t : ℝ =>
      1 + ((stereoSlope (x36Clamp t).1 e.1.1 e.1.2).re ^ 2 +
        (stereoSlope (x36Clamp t).1 e.1.1 e.1.2).im ^ 2) :=
    fun e => continuous_const.add
      (((Complex.continuous_re.comp (stereoSlope_x36Clamp_continuous e.1.1 e.1.2 e.2)).pow 2).add
        ((Complex.continuous_im.comp (stereoSlope_x36Clamp_continuous e.1.1 e.1.2 e.2)).pow 2))
  have hns : (fun t : ℝ => stereoDenR (x36Clamp t).1) =
      fun t => ∏ e : { p : Fin 36 × Fin 36 // p.1 < p.2 },
        (1 + ((stereoSlope (x36Clamp t).1 e.1.1 e.1.2).re ^ 2 +
          (stereoSlope (x36Clamp t).1 e.1.1 e.1.2).im ^ 2)) := by
    ext t
    unfold stereoDenR
    refine Finset.prod_congr rfl fun e _ => ?_
    simp [Complex.normSq_apply]; ring
  rw [hns]
  exact continuous_finset_prod_aux Finset.univ (fun e _ => hfac e)

section
attribute [local irreducible] Matrix.det stereoDenR

lemma continuous_atiyahDet_x36Clamp_re :
    Continuous (fun t : ℝ => (atiyahDet (x36Clamp t)).re) := by
  have hformula : (fun t : ℝ => (atiyahDet (x36Clamp t)).re) =
      fun t => ((atiyahMat (stereoSpinor (x36Clamp t).1)).det).re / stereoDenR (x36Clamp t).1 := by
    ext t
    rw [atiyahDet_eq_stereoMat_div (x36Clamp t) (x36Clamp_z_monotone t)]
    have hdiv : ∀ (z : ℂ) (r : ℝ), (z / (r : ℂ)).re = z.re / r := by
      intro z r
      by_cases hr : r = 0
      · subst hr; simp
      · simp [div_eq_mul_inv, ← Complex.ofReal_inv]
    exact hdiv _ _
  rw [hformula]
  have hdet_cont : Continuous (fun t : ℝ => ((atiyahMat (stereoSpinor (x36Clamp t).1)).det).re) :=
    continuous_stereoMat_x36Clamp_det_re
  have hden_cont : Continuous (fun t : ℝ => stereoDenR (x36Clamp t).1) :=
    continuous_stereoDenR_x36Clamp
  have hden_ne : ∀ t : ℝ, stereoDenR (x36Clamp t).1 ≠ 0 :=
    fun t => (stereoDenR_pos (x36Clamp t).1).ne'
  exact Continuous.div hdet_cont hden_cont hden_ne

end

end X36Family

/-! ## Part 4: Antipodal `36 → 18 × 18` Parity Block Reduction & `18 → 6` Elimination -/

section AntipodalReduce

private lemma coeff_comp_neg_X (P : Polynomial ℂ) (k : ℕ) :
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

def antipodalPerm36 : Equiv.Perm (Fin 36) :=
  Equiv.swap ⟨18, by decide⟩ ⟨19, by decide⟩ *
    Equiv.swap ⟨20, by decide⟩ ⟨21, by decide⟩ *
    Equiv.swap ⟨22, by decide⟩ ⟨23, by decide⟩ *
    Equiv.swap ⟨24, by decide⟩ ⟨25, by decide⟩ *
    Equiv.swap ⟨26, by decide⟩ ⟨27, by decide⟩ *
    Equiv.swap ⟨28, by decide⟩ ⟨29, by decide⟩

lemma x36Base_antipodal : ∀ i : Fin 36,
    x36BaseX (antipodalPerm36 i) = -x36BaseX i ∧
      x36BaseY (antipodalPerm36 i) = -x36BaseY i ∧
      x36BaseZ (antipodalPerm36 i) = x36BaseZ i := by
  decide

lemma antipodal_involutive (i : Fin 36) : antipodalPerm36 (antipodalPerm36 i) = i := by
  revert i; decide

lemma antipodal_axial_fix : ∀ i : Fin 36, i.1 < 18 ∨ 30 ≤ i.1 → antipodalPerm36 i = i := by
  decide

lemma antipodal_lt_iff_axial : ∀ i j : Fin 36,
    (i.1 < 18 ∨ 30 ≤ i.1) → j ≠ i → (j < i ↔ antipodalPerm36 j < i) := by
  decide

lemma antipodal_ringPair : ∀ q : Fin 6,
    antipodalPerm36 ⟨18 + 2 * q.1, by omega⟩ = ⟨18 + 2 * q.1 + 1, by omega⟩ := by
  decide

lemma antipodal_lt_iff_ring : ∀ (q : Fin 6) (j : Fin 36),
    j ≠ ⟨18 + 2 * q.1, by omega⟩ → j ≠ ⟨18 + 2 * q.1 + 1, by omega⟩ →
      (j < ⟨18 + 2 * q.1, by omega⟩ ↔ antipodalPerm36 j < ⟨18 + 2 * q.1 + 1, by omega⟩) := by
  decide

lemma antipodal_lt_ring_card_even : ∀ q : Fin 6,
    ((((Finset.univ : Finset (Fin 36)).erase ⟨18 + 2 * q.1, by omega⟩).erase
        ⟨18 + 2 * q.1 + 1, by omega⟩).filter
      (fun j => j < ⟨18 + 2 * q.1, by omega⟩)).card % 2 = 0 := by
  decide

lemma stereoSlope_antipodal (t : ℝ) (i j : Fin 36) :
    stereoSlope (x36Clamp t).1 (antipodalPerm36 i) (antipodalPerm36 j) =
      -stereoSlope (x36Clamp t).1 i j := by
  let p := (x36Clamp t).1
  have hpi := x36Base_antipodal i
  have hpj := x36Base_antipodal j
  have h0i : p (antipodalPerm36 i) 0 = -p i 0 := by
    simp [p, x36Clamp, x36ClampRaw, hpi.1]
  have h0j : p (antipodalPerm36 j) 0 = -p j 0 := by
    simp [p, x36Clamp, x36ClampRaw, hpj.1]
  have h1i : p (antipodalPerm36 i) 1 = -p i 1 := by
    simp [p, x36Clamp, x36ClampRaw, hpi.2.1]
  have h1j : p (antipodalPerm36 j) 1 = -p j 1 := by
    simp [p, x36Clamp, x36ClampRaw, hpj.2.1]
  have h2i : p (antipodalPerm36 i) 2 = p i 2 := by
    simp [p, x36Clamp, x36ClampRaw, hpi.2.2]
  have h2j : p (antipodalPerm36 j) 2 = p j 2 := by
    simp [p, x36Clamp, x36ClampRaw, hpj.2.2]
  have hden : stereoDenomR (p (antipodalPerm36 i)) (p (antipodalPerm36 j)) =
      stereoDenomR (p i) (p j) := by
    unfold stereoDenomR euclidNorm
    have hsq :
        (p (antipodalPerm36 j) 0 - p (antipodalPerm36 i) 0) ^ 2 +
          (p (antipodalPerm36 j) 1 - p (antipodalPerm36 i) 1) ^ 2 +
          (p (antipodalPerm36 j) 2 - p (antipodalPerm36 i) 2) ^ 2 =
          (p j 0 - p i 0) ^ 2 + (p j 1 - p i 1) ^ 2 + (p j 2 - p i 2) ^ 2 := by
      rw [h0i, h0j, h1i, h1j, h2i, h2j]; ring
    rw [h2i, h2j, hsq]
  unfold stereoSlope
  change (((p (antipodalPerm36 j) 0 - p (antipodalPerm36 i) 0 : ℝ) : ℂ) +
      Complex.I * ((p (antipodalPerm36 j) 1 - p (antipodalPerm36 i) 1 : ℝ) : ℂ)) /
      (stereoDenomR (p (antipodalPerm36 i)) (p (antipodalPerm36 j)) : ℂ) =
    -((((p j 0 - p i 0 : ℝ) : ℂ) + Complex.I * ((p j 1 - p i 1 : ℝ) : ℂ)) /
      (stereoDenomR (p i) (p j) : ℂ))
  rw [hden, h0i, h0j, h1i, h1j]
  push_cast
  ring

private lemma prod_filter_split_neg {α : Type*} [DecidableEq α]
    (s : Finset α) (pred : α → Prop) [DecidablePred pred] (f : α → Polynomial ℂ) :
    (∏ a ∈ s, (if pred a then -(f a) else f a)) =
      ((-1 : ℂ) ^ (s.filter pred).card : ℂ) • (∏ a ∈ s, f a) := by
  have hrw : ∀ a ∈ s, (if pred a then -(f a) else f a) =
      (if pred a then (-1 : Polynomial ℂ) else 1) * f a := by
    intro a _
    by_cases h : pred a <;> simp [h]
  rw [Finset.prod_congr rfl hrw, Finset.prod_mul_distrib]
  have hpref : (∏ a ∈ s, if pred a then (-1 : Polynomial ℂ) else 1) =
      Polynomial.C ((-1 : ℂ) ^ (s.filter pred).card) := by
    rw [← Finset.prod_filter_mul_prod_filter_not s pred]
    have h1 : (∏ a ∈ s.filter pred, if pred a then (-1 : Polynomial ℂ) else 1) =
        (-1 : Polynomial ℂ) ^ (s.filter pred).card := by
      calc
        (∏ a ∈ s.filter pred, if pred a then (-1 : Polynomial ℂ) else 1)
          = ∏ _a ∈ s.filter pred, (-1 : Polynomial ℂ) :=
              Finset.prod_congr rfl fun a ha => by simp [(Finset.mem_filter.mp ha).2]
        _ = (-1 : Polynomial ℂ) ^ (s.filter pred).card := Finset.prod_const _
    have h2 : (∏ a ∈ s.filter (fun a => ¬ pred a),
        if pred a then (-1 : Polynomial ℂ) else 1) = 1 :=
      Finset.prod_eq_one fun a ha => by simp [(Finset.mem_filter.mp ha).2]
    rw [h1, h2, mul_one]
    simp
  rw [hpref, Algebra.smul_def]
  simp

private lemma atiyahPoly_axial_antipodal (t : ℝ) (i : Fin 36) (hi : i.1 < 18 ∨ 30 ≤ i.1) :
    atiyahPoly (stereoSpinor (x36Clamp t).1) i =
      ((-1 : ℂ) ^ i.1) • (atiyahPoly (stereoSpinor (x36Clamp t).1) i).comp (-Polynomial.X) := by
  classical
  have hfix : antipodalPerm36 i = i := antipodal_axial_fix i hi
  have hpoly : atiyahPoly (stereoSpinor (x36Clamp t).1) i =
      ∏ j ∈ Finset.univ.erase i,
        (if j < i then
          -((Polynomial.C (stereoSpinor (x36Clamp t).1 i j 0) +
              Polynomial.C (stereoSpinor (x36Clamp t).1 i j 1) * Polynomial.X).comp (-Polynomial.X))
         else
          (Polynomial.C (stereoSpinor (x36Clamp t).1 i j 0) +
              Polynomial.C (stereoSpinor (x36Clamp t).1 i j 1) * Polynomial.X).comp (-Polynomial.X)) := by
    unfold atiyahPoly
    refine Finset.prod_bij (fun j _ => antipodalPerm36 j) ?_ ?_ ?_ ?_
    · intro j hj
      exact Finset.mem_erase.mpr
        ⟨fun heq => (Finset.mem_erase.mp hj).1 (antipodalPerm36.injective (heq.trans hfix.symm)),
         Finset.mem_univ _⟩
    · intro j₁ _ j₂ _ heq; exact antipodalPerm36.injective heq
    · intro b hb
      refine ⟨antipodalPerm36 b, Finset.mem_erase.mpr ⟨fun heq => ?_, Finset.mem_univ _⟩,
        antipodal_involutive b⟩
      have hb' := congrArg antipodalPerm36 heq
      rw [antipodal_involutive, hfix] at hb'
      exact (Finset.mem_erase.mp hb).1 hb'
    · intro j hj
      have hj_ne : j ≠ i := (Finset.mem_erase.mp hj).1
      have hτj_ne : antipodalPerm36 j ≠ i :=
        fun heq => hj_ne (antipodalPerm36.injective (heq.trans hfix.symm))
      have hlt_iff := antipodal_lt_iff_axial i j hi hj_ne
      by_cases hlt : j < i
      · have hτlt : antipodalPerm36 j < i := hlt_iff.mp hlt
        have hnot1 : ¬ i < j := not_lt_of_gt hlt
        have hnot2 : ¬ i < antipodalPerm36 j := not_lt_of_gt hτlt
        have hss : stereoSlope (x36Clamp t).1 (antipodalPerm36 j) i =
            -stereoSlope (x36Clamp t).1 j i := by
          have := stereoSlope_antipodal t j i
          rwa [hfix] at this
        simp only [stereoSpinor, hj_ne.symm, hτj_ne.symm, ↓reduceIte, hnot1, hnot2, hτlt,
          Matrix.cons_val_zero, Matrix.cons_val_one, Polynomial.add_comp, Polynomial.C_comp,
          Polynomial.mul_comp, Polynomial.X_comp, hss, star_neg, neg_neg, map_neg]
        ring
      · have hgt : i < j := lt_of_le_of_ne (not_lt.mp hlt) hj_ne.symm
        have hτnot : ¬ antipodalPerm36 j < i := fun h => hlt (hlt_iff.mpr h)
        have hτgt : i < antipodalPerm36 j := lt_of_le_of_ne (not_lt.mp hτnot) hτj_ne.symm
        have hss : stereoSlope (x36Clamp t).1 i (antipodalPerm36 j) =
            -stereoSlope (x36Clamp t).1 i j := by
          have := stereoSlope_antipodal t i j
          rwa [hfix] at this
        simp only [stereoSpinor, hj_ne.symm, hτj_ne.symm, ↓reduceIte, hgt, hτgt, hτnot,
          Matrix.cons_val_zero, Matrix.cons_val_one, Polynomial.add_comp, Polynomial.neg_comp,
          Polynomial.C_comp, Polynomial.mul_comp, Polynomial.X_comp, hss, map_neg]
        ring
  conv_lhs => rw [hpoly, prod_filter_split_neg]
  have hcomp_prod :
      (∏ j ∈ Finset.univ.erase i,
          (Polynomial.C (stereoSpinor (x36Clamp t).1 i j 0) +
              Polynomial.C (stereoSpinor (x36Clamp t).1 i j 1) * Polynomial.X).comp (-Polynomial.X)) =
        (atiyahPoly (stereoSpinor (x36Clamp t).1) i).comp (-Polynomial.X) := by
    simp [atiyahPoly, Polynomial.prod_comp]
  have hcard : ((Finset.univ.erase i).filter (· < i)).card = i.1 := by
    have hfilt : (Finset.univ.erase i).filter (· < i) = Finset.univ.filter (· < i) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true]
      exact ⟨fun h => h.2, fun h => ⟨h.ne, h⟩⟩
    rw [hfilt]
    have himg : Finset.univ.filter (· < i) =
        Finset.image (fun k : Fin i.1 => ⟨k.1, lt_trans k.2 i.2⟩) Finset.univ := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hj; exact ⟨⟨j.1, hj⟩, rfl⟩
      · rintro ⟨k, rfl⟩; exact k.2
    rw [himg, Finset.card_image_of_injective _ (fun a b h => by ext; simpa using congr_arg Fin.val h),
      Finset.card_fin]
  rw [hcomp_prod, hcard]

lemma atiyahMat_axial_parity_zero (t : ℝ) (i k : Fin 36) (hi : i.1 < 18 ∨ 30 ≤ i.1)
    (hne : i.1 % 2 ≠ k.1 % 2) :
    atiyahMat (stereoSpinor (x36Clamp t).1) i k = 0 := by
  have hpoly := atiyahPoly_axial_antipodal t i hi
  have hcoeff := congrArg (fun P : Polynomial ℂ => P.coeff k.1) hpoly
  rw [Polynomial.smul_eq_C_mul, Polynomial.coeff_C_mul, coeff_comp_neg_X] at hcoeff
  have hpow : (-1 : ℂ) ^ i.1 * (-1 : ℂ) ^ k.1 = -1 := by
    rcases Nat.mod_two_eq_zero_or_one i.1 with hi0 | hi1 <;>
      rcases Nat.mod_two_eq_zero_or_one k.1 with hk0 | hk1
    · exact absurd (hi0.trans hk0.symm) hne
    · have hiE : (-1 : ℂ) ^ i.1 = 1 := by
        rw [← Nat.div_add_mod i.1 2, hi0, add_zero, pow_mul]; norm_num
      have hkO : (-1 : ℂ) ^ k.1 = -1 := by
        rw [← Nat.div_add_mod k.1 2, hk1, pow_add, pow_mul]; norm_num
      rw [hiE, hkO, one_mul]
    · have hiO : (-1 : ℂ) ^ i.1 = -1 := by
        rw [← Nat.div_add_mod i.1 2, hi1, pow_add, pow_mul]; norm_num
      have hkE : (-1 : ℂ) ^ k.1 = 1 := by
        rw [← Nat.div_add_mod k.1 2, hk0, add_zero, pow_mul]; norm_num
      rw [hiO, hkE, mul_one]
    · exact absurd (hi1.trans hk1.symm) hne
  have hneg : atiyahMat (stereoSpinor (x36Clamp t).1) i k =
      -atiyahMat (stereoSpinor (x36Clamp t).1) i k := by
    calc
      atiyahMat (stereoSpinor (x36Clamp t).1) i k
        = ((-1 : ℂ) ^ i.1 * (-1 : ℂ) ^ k.1) * atiyahMat (stereoSpinor (x36Clamp t).1) i k := by
            simpa [atiyahMat, mul_assoc] using hcoeff
      _ = -atiyahMat (stereoSpinor (x36Clamp t).1) i k := by rw [hpow]; ring
  have : (2 : ℂ) * atiyahMat (stereoSpinor (x36Clamp t).1) i k = 0 := by
    linear_combination hneg
  exact (mul_eq_zero.mp this).resolve_left (by norm_num)

noncomputable def lam36 (q : Fin 6) : ℂ :=
  match q.1 with
  | 0 | 3 => 1
  | 1 | 4 => (33 - 56 * Complex.I) / 65
  | _ => (-33 - 56 * Complex.I) / 65

lemma lam36_ne_zero (q : Fin 6) : lam36 q ≠ 0 := by
  fin_cases q <;> simp [lam36, Complex.ext_iff]

lemma prod_lam36_eq_one : (∏ q : Fin 6, lam36 q) = 1 := by
  simp only [Fin.prod_univ_six, Fin.isValue, lam36]
  apply Complex.ext <;> norm_num

private lemma ringPair_slope_helper (t : ℝ) (a b : Fin 36) (c₁ c₂ r₀ : ℝ)
    (hr₀ : 0 < r₀) (hpy : c₁ ^ 2 + c₂ ^ 2 = r₀ ^ 2)
    (hdx : (x36Clamp t).1 b 0 - (x36Clamp t).1 a 0 = c₁ * max t 1)
    (hdy : (x36Clamp t).1 b 1 - (x36Clamp t).1 a 1 = c₂ * max t 1)
    (hdz : (x36Clamp t).1 b 2 - (x36Clamp t).1 a 2 = 0) :
    stereoSlope (x36Clamp t).1 a b = ((c₁ : ℂ) + Complex.I * (c₂ : ℂ)) / (r₀ : ℂ) := by
  have hs : 0 < max t 1 := by linarith [le_max_right t (1 : ℝ)]
  have hnorm : euclidNorm (fun k => (x36Clamp t).1 b k - (x36Clamp t).1 a k) = r₀ * max t 1 := by
    unfold euclidNorm
    have hsq : ((x36Clamp t).1 b 0 - (x36Clamp t).1 a 0) ^ 2 +
        ((x36Clamp t).1 b 1 - (x36Clamp t).1 a 1) ^ 2 +
        ((x36Clamp t).1 b 2 - (x36Clamp t).1 a 2) ^ 2 = (r₀ * max t 1) ^ 2 := by
      rw [hdx, hdy, hdz]
      calc
        (c₁ * max t 1) ^ 2 + (c₂ * max t 1) ^ 2 + 0 ^ 2
          = (c₁ ^ 2 + c₂ ^ 2) * (max t 1) ^ 2 := by ring
        _ = r₀ ^ 2 * (max t 1) ^ 2 := by rw [hpy]
        _ = (r₀ * max t 1) ^ 2 := by ring
    rw [hsq, Real.sqrt_sq (mul_nonneg hr₀.le hs.le)]
  unfold stereoSlope stereoDenomR
  rw [hdx, hdy, hdz, hnorm, zero_add]
  have hsC : ((max t 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hr₀C : (r₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr₀.ne'
  simp only [Complex.ofReal_mul]
  field_simp [hsC, hr₀C]

private lemma stereoSlope_ringPair_eq (t : ℝ) (q : Fin 6) :
    -star (stereoSlope (x36Clamp t).1 ⟨18 + 2 * q.1, by omega⟩ ⟨18 + 2 * q.1 + 1, by omega⟩) =
        lam36 q ∧
      lam36 q *
          (-stereoSlope (x36Clamp t).1 ⟨18 + 2 * q.1, by omega⟩ ⟨18 + 2 * q.1 + 1, by omega⟩) =
        1 := by
  have hslope :
      ∀ (a b : Fin 36) (c₁ c₂ r₀ : ℤ), 0 < r₀ → c₁ ^ 2 + c₂ ^ 2 = r₀ ^ 2 →
        x36BaseX b - x36BaseX a = c₁ →
        x36BaseY b - x36BaseY a = c₂ →
        x36BaseZ b = x36BaseZ a →
        stereoSlope (x36Clamp t).1 a b = ((c₁ : ℂ) + Complex.I * (c₂ : ℂ)) / (r₀ : ℂ) := by
    intro a b c₁ c₂ r₀ hr₀ hpy hbx hby hbz
    have hr₀R : (0 : ℝ) < (r₀ : ℝ) := by exact_mod_cast hr₀
    have hpyR : (c₁ : ℝ) ^ 2 + (c₂ : ℝ) ^ 2 = (r₀ : ℝ) ^ 2 := by exact_mod_cast hpy
    have h1 := ringPair_slope_helper t a b (c₁ : ℝ) (c₂ : ℝ) (r₀ : ℝ) hr₀R hpyR
      (by simp [x36Clamp, x36ClampRaw, ← hbx, Int.cast_sub]; ring)
      (by simp [x36Clamp, x36ClampRaw, ← hby, Int.cast_sub]; ring)
      (by simp [x36Clamp, x36ClampRaw, hbz])
    simpa using h1
  fin_cases q <;> dsimp only
  · have hw := hslope ⟨18, by decide⟩ ⟨19, by decide⟩ (-1040) 0 1040 (by decide) (by decide)
      (by decide) (by decide) (by decide)
    rw [hw]
    constructor <;> (apply Complex.ext <;> simp [lam36])
  · have hw := hslope ⟨20, by decide⟩ ⟨21, by decide⟩ (-528) (-896) 1040 (by decide) (by decide)
      (by decide) (by decide) (by decide)
    rw [hw]
    constructor <;> (apply Complex.ext <;> simp [lam36] <;> norm_num)
  · have hw := hslope ⟨22, by decide⟩ ⟨23, by decide⟩ 528 (-896) 1040 (by decide) (by decide)
      (by decide) (by decide) (by decide)
    rw [hw]
    constructor <;> (apply Complex.ext <;> simp [lam36] <;> norm_num)
  · have hw := hslope ⟨24, by decide⟩ ⟨25, by decide⟩ (-23920) 0 23920 (by decide) (by decide)
      (by decide) (by decide) (by decide)
    rw [hw]
    constructor <;> (apply Complex.ext <;> simp [lam36])
  · have hw := hslope ⟨26, by decide⟩ ⟨27, by decide⟩ (-12144) (-20608) 23920 (by decide) (by decide)
      (by decide) (by decide) (by decide)
    rw [hw]
    constructor <;> (apply Complex.ext <;> simp [lam36] <;> norm_num)
  · have hw := hslope ⟨28, by decide⟩ ⟨29, by decide⟩ 12144 (-20608) 23920 (by decide) (by decide)
      (by decide) (by decide) (by decide)
    rw [hw]
    constructor <;> (apply Complex.ext <;> simp [lam36] <;> norm_num)

private lemma atiyahPoly_ringPair (t : ℝ) (q : Fin 6) :
    atiyahPoly (stereoSpinor (x36Clamp t).1) ⟨18 + 2 * q.1 + 1, by omega⟩ =
      Polynomial.C (lam36 q) *
        (atiyahPoly (stereoSpinor (x36Clamp t).1) ⟨18 + 2 * q.1, by omega⟩).comp (-Polynomial.X) := by
  classical
  set a : Fin 36 := ⟨18 + 2 * q.1, by omega⟩
  set b : Fin 36 := ⟨18 + 2 * q.1 + 1, by omega⟩
  have hab : a < b := by change 18 + 2 * q.1 < 18 + 2 * q.1 + 1; omega
  have hτa : antipodalPerm36 a = b := antipodal_ringPair q
  have hτb : antipodalPerm36 b = a := by rw [← hτa, antipodal_involutive]
  have hpair_slope := stereoSlope_ringPair_eq t q
  have ha_mem : a ∈ Finset.univ.erase b := Finset.mem_erase.mpr ⟨hab.ne, Finset.mem_univ _⟩
  have hb_mem : b ∈ Finset.univ.erase a := Finset.mem_erase.mpr ⟨hab.ne', Finset.mem_univ _⟩
  let Sb : Finset (Fin 36) := (Finset.univ.erase b).erase a
  let Sa : Finset (Fin 36) := (Finset.univ.erase a).erase b
  have hsplit_b : atiyahPoly (stereoSpinor (x36Clamp t).1) b =
      (Polynomial.C (stereoSpinor (x36Clamp t).1 b a 0) +
          Polynomial.C (stereoSpinor (x36Clamp t).1 b a 1) * Polynomial.X) *
        ∏ j ∈ Sb, (Polynomial.C (stereoSpinor (x36Clamp t).1 b j 0) +
          Polynomial.C (stereoSpinor (x36Clamp t).1 b j 1) * Polynomial.X) := by
    unfold atiyahPoly
    exact (Finset.mul_prod_erase (Finset.univ.erase b)
      (fun j => Polynomial.C (stereoSpinor (x36Clamp t).1 b j 0) +
        Polynomial.C (stereoSpinor (x36Clamp t).1 b j 1) * Polynomial.X) ha_mem).symm
  have hsplit_a : (atiyahPoly (stereoSpinor (x36Clamp t).1) a).comp (-Polynomial.X) =
      (Polynomial.C (stereoSpinor (x36Clamp t).1 a b 0) +
          Polynomial.C (stereoSpinor (x36Clamp t).1 a b 1) * (-Polynomial.X)) *
        ∏ j ∈ Sa, (Polynomial.C (stereoSpinor (x36Clamp t).1 a j 0) +
          Polynomial.C (stereoSpinor (x36Clamp t).1 a j 1) * (-Polynomial.X)) := by
    unfold atiyahPoly
    rw [← Finset.mul_prod_erase (Finset.univ.erase a)
      (fun j => Polynomial.C (stereoSpinor (x36Clamp t).1 a j 0) +
        Polynomial.C (stereoSpinor (x36Clamp t).1 a j 1) * Polynomial.X) hb_mem]
    simp only [Polynomial.mul_comp, Polynomial.prod_comp, Polynomial.add_comp, Polynomial.C_comp, Polynomial.X_comp]
    rfl
  have hfac_partner :
      Polynomial.C (stereoSpinor (x36Clamp t).1 b a 0) +
          Polynomial.C (stereoSpinor (x36Clamp t).1 b a 1) * Polynomial.X =
        Polynomial.C (lam36 q) *
          (Polynomial.C (stereoSpinor (x36Clamp t).1 a b 0) +
            Polynomial.C (stereoSpinor (x36Clamp t).1 a b 1) * (-Polynomial.X)) := by
    have hnot : ¬ b < a := not_lt_of_gt hab
    simp only [stereoSpinor, hab.ne, hab.ne', ↓reduceIte, hab, hnot,
      Matrix.cons_val_zero, Matrix.cons_val_one, map_one]
    rw [hpair_slope.1]
    calc
      Polynomial.C (lam36 q) + 1 * Polynomial.X
        = Polynomial.C (lam36 q) * 1 +
            Polynomial.C (lam36 q * (-stereoSlope (x36Clamp t).1 a b)) * Polynomial.X := by
            rw [hpair_slope.2]; simp
      _ = Polynomial.C (lam36 q) *
            (1 + Polynomial.C (stereoSlope (x36Clamp t).1 a b) * (-Polynomial.X)) := by
            simp only [map_mul, map_neg]; ring
  have hrest :
      (∏ j ∈ Sb, (Polynomial.C (stereoSpinor (x36Clamp t).1 b j 0) +
          Polynomial.C (stereoSpinor (x36Clamp t).1 b j 1) * Polynomial.X)) =
        ∏ j ∈ Sa, (Polynomial.C (stereoSpinor (x36Clamp t).1 a j 0) +
          Polynomial.C (stereoSpinor (x36Clamp t).1 a j 1) * (-Polynomial.X)) := by
    have hprod_bij :
        (∏ j ∈ Sb, (Polynomial.C (stereoSpinor (x36Clamp t).1 b j 0) +
            Polynomial.C (stereoSpinor (x36Clamp t).1 b j 1) * Polynomial.X)) =
          ∏ k ∈ Sa,
            (if k < a then
              -(Polynomial.C (stereoSpinor (x36Clamp t).1 a k 0) +
                Polynomial.C (stereoSpinor (x36Clamp t).1 a k 1) * (-Polynomial.X))
             else
              (Polynomial.C (stereoSpinor (x36Clamp t).1 a k 0) +
                Polynomial.C (stereoSpinor (x36Clamp t).1 a k 1) * (-Polynomial.X))) := by
      refine Finset.prod_bij (fun j _ => antipodalPerm36 j) ?_ ?_ ?_ ?_
      · intro j hj
        have hj1 : j ≠ a := (Finset.mem_erase.mp hj).1
        have hj2 : j ≠ b := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
        exact Finset.mem_erase.mpr
          ⟨fun he => hj1 (antipodalPerm36.injective (he.trans hτa.symm)),
           Finset.mem_erase.mpr
            ⟨fun he => hj2 (antipodalPerm36.injective (he.trans hτb.symm)), Finset.mem_univ _⟩⟩
      · intro j₁ _ j₂ _ heq; exact antipodalPerm36.injective heq
      · intro y hy
        have hy1 : y ≠ b := (Finset.mem_erase.mp hy).1
        have hy2 : y ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hy).2).1
        refine ⟨antipodalPerm36 y, ?_, antipodal_involutive y⟩
        exact Finset.mem_erase.mpr
          ⟨fun he => hy1 (antipodalPerm36.injective (he.trans hτb.symm)),
           Finset.mem_erase.mpr
            ⟨fun he => hy2 (antipodalPerm36.injective (he.trans hτa.symm)), Finset.mem_univ _⟩⟩
      · intro j hj
        have hj1 : j ≠ a := (Finset.mem_erase.mp hj).1
        have hj2 : j ≠ b := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
        have hτj1 : antipodalPerm36 j ≠ b :=
          fun he => hj1 (antipodalPerm36.injective (he.trans hτa.symm))
        have hτj2 : antipodalPerm36 j ≠ a :=
          fun he => hj2 (antipodalPerm36.injective (he.trans hτb.symm))
        have hlt_iff := antipodal_lt_iff_ring q (antipodalPerm36 j) hτj2 hτj1
        rw [antipodal_involutive] at hlt_iff
        by_cases hklt : antipodalPerm36 j < a
        · have hjlt : j < b := hlt_iff.mp hklt
          have hnot1 : ¬ a < antipodalPerm36 j := not_lt_of_gt hklt
          have hnot2 : ¬ b < j := not_lt_of_gt hjlt
          have hss : stereoSlope (x36Clamp t).1 (antipodalPerm36 j) a =
              -stereoSlope (x36Clamp t).1 j b := by
            have := stereoSlope_antipodal t j b
            rwa [hτb] at this
          simp only [stereoSpinor, hτj2.symm, hj2.symm, ↓reduceIte, hnot1, hnot2, hklt,
            Matrix.cons_val_zero, Matrix.cons_val_one, hss, star_neg, neg_neg, map_neg]
          ring
        · have hkgt : a < antipodalPerm36 j := lt_of_le_of_ne (not_lt.mp hklt) hτj2.symm
          have hjnot : ¬ j < b := fun h => hklt (hlt_iff.mpr h)
          have hjgt : b < j := lt_of_le_of_ne (not_lt.mp hjnot) hj2.symm
          have hss : stereoSlope (x36Clamp t).1 a (antipodalPerm36 j) =
              -stereoSlope (x36Clamp t).1 b j := by
            have := stereoSlope_antipodal t b j
            rwa [hτb] at this
          simp only [stereoSpinor, hτj2.symm, hj2.symm, ↓reduceIte, hkgt, hjgt, hklt,
            Matrix.cons_val_zero, Matrix.cons_val_one, hss, map_neg]
          ring
    rw [hprod_bij, prod_filter_split_neg]
    have heven := antipodal_lt_ring_card_even q
    have hpow : (-1 : ℂ) ^ (Sa.filter (· < a)).card = 1 := by
      have hm : (Sa.filter (· < a)).card = 2 * ((Sa.filter (· < a)).card / 2) := by
        have : (Sa.filter (· < a)).card % 2 = 0 := heven
        omega
      rw [hm, pow_mul]; norm_num
    rw [hpow, one_smul]
  rw [hsplit_b, hsplit_a, hfac_partner, hrest, mul_assoc]

def evenSrcRow (r : Fin 18) : Fin 36 :=
  if r.1 < 9 then ⟨2 * r.1, by omega⟩
  else if r.1 < 15 then ⟨18 + 2 * (r.1 - 9), by omega⟩
  else ⟨30 + 2 * (r.1 - 15), by omega⟩

def oddSrcRow (r : Fin 18) : Fin 36 :=
  if r.1 < 9 then ⟨2 * r.1 + 1, by omega⟩
  else if r.1 < 15 then ⟨18 + 2 * (r.1 - 9), by omega⟩
  else ⟨31 + 2 * (r.1 - 15), by omega⟩

def parityEquiv : Fin 18 ⊕ Fin 18 ≃ Fin 36 where
  toFun
    | Sum.inl r => ⟨2 * r.1, by omega⟩
    | Sum.inr r => ⟨2 * r.1 + 1, by omega⟩
  invFun k :=
    if hk : k.1 % 2 = 0 then Sum.inl ⟨k.1 / 2, by omega⟩
    else Sum.inr ⟨k.1 / 2, by omega⟩
  left_inv x := by
    rcases x with r | r
    · simp
    · simp [Fin.ext_iff]; omega
  right_inv k := by
    by_cases hk : k.1 % 2 = 0
    · simp only [hk, ↓reduceDIte]; apply Fin.ext; dsimp; omega
    · simp only [hk, ↓reduceDIte]; apply Fin.ext; dsimp; omega

noncomputable def evenMat18 (p : Fin 36 → Fin 3 → ℝ) : Matrix (Fin 18) (Fin 18) ℂ :=
  fun r c => atiyahMat (stereoSpinor p) (evenSrcRow r) ⟨2 * c.1, by omega⟩

noncomputable def oddMat18 (p : Fin 36 → Fin 3 → ℝ) : Matrix (Fin 18) (Fin 18) ℂ :=
  fun r c => atiyahMat (stereoSpinor p) (oddSrcRow r) ⟨2 * c.1 + 1, by omega⟩

private lemma det_foldl_updateRow_add {α ι : Type*} [DecidableEq ι] [Fintype ι]
    (l : List α) (hnodup : l.Nodup) (target partner : α → ι) (scale : α → ℂ)
    (htarg_inj : Function.Injective target) (hne : ∀ a₁ a₂, target a₁ ≠ partner a₂)
    (B : Matrix ι ι ℂ) :
    let step := fun (M : Matrix ι ι ℂ) (a : α) =>
      M.updateRow (target a) (M (target a) + scale a • M (partner a))
    (l.foldl step B).det = B.det ∧
      (∀ x, (∀ a ∈ l, x ≠ target a) → (l.foldl step B) x = B x) ∧
      (∀ a ∈ l, (l.foldl step B) (target a) = B (target a) + scale a • B (partner a)) := by
  intro step
  induction l generalizing B with
  | nil => simp [step]
  | cons a as ih =>
    simp only [List.foldl_cons]
    have hnodup' : as.Nodup := (List.nodup_cons.mp hnodup).2
    have ha_not_in : a ∉ as := (List.nodup_cons.mp hnodup).1
    let B₁ := step B a
    have ihB₁ := ih hnodup' B₁
    refine ⟨?_, ?_, ?_⟩
    · have hdet1 : B₁.det = B.det := Matrix.det_updateRow_add_smul_self B (hne a a) (scale a)
      exact ihB₁.1.trans hdet1
    · intro x hx
      have hxa : x ≠ target a := hx a List.mem_cons_self
      have hxas : ∀ b ∈ as, x ≠ target b := fun b hb => hx b (List.mem_cons_of_mem a hb)
      rw [ihB₁.2.1 x hxas]
      simp [B₁, step, hxa]
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hbs
      · have has : ∀ b' ∈ as, target b ≠ target b' :=
          fun b' hb' heq => ha_not_in (htarg_inj heq ▸ hb')
        rw [ihB₁.2.1 (target b) has]
        simp [B₁, step]
      · have hba : target b ≠ target a := fun heq => ha_not_in (htarg_inj heq.symm ▸ hbs)
        rw [ihB₁.2.2 b hbs]
        have ht1 : B₁ (target b) = B (target b) := by
          simp [B₁, step, hba]
        have hp1 : B₁ (partner b) = B (partner b) := by
          simp [B₁, step, (hne a b).symm]
        rw [ht1, hp1]

private lemma det_block_antipodal_abstract
    (M0 : Matrix (Fin 18 ⊕ Fin 18) (Fin 18 ⊕ Fin 18) ℂ)
    (evenBlock oddBlock : Matrix (Fin 18) (Fin 18) ℂ)
    (h_even_ax : ∀ r : Fin 18, r.1 < 9 ∨ 15 ≤ r.1 → ∀ c : Fin 18,
      M0 (Sum.inl r) (Sum.inl c) = evenBlock r c ∧ M0 (Sum.inl r) (Sum.inr c) = 0)
    (h_odd_ax : ∀ r : Fin 18, r.1 < 9 ∨ 15 ≤ r.1 → ∀ c : Fin 18,
      M0 (Sum.inr r) (Sum.inl c) = 0 ∧ M0 (Sum.inr r) (Sum.inr c) = oddBlock r c)
    (h_ring : ∀ (q : Fin 6) (c : Fin 18),
      M0 (Sum.inl ⟨9 + q.1, by omega⟩) (Sum.inl c) = evenBlock ⟨9 + q.1, by omega⟩ c ∧
      M0 (Sum.inr ⟨9 + q.1, by omega⟩) (Sum.inl c) =
        lam36 q * M0 (Sum.inl ⟨9 + q.1, by omega⟩) (Sum.inl c) ∧
      M0 (Sum.inl ⟨9 + q.1, by omega⟩) (Sum.inr c) = oddBlock ⟨9 + q.1, by omega⟩ c ∧
      M0 (Sum.inr ⟨9 + q.1, by omega⟩) (Sum.inr c) =
        -lam36 q * M0 (Sum.inl ⟨9 + q.1, by omega⟩) (Sum.inr c)) :
    M0.det = (64 : ℂ) * evenBlock.det * oddBlock.det := by
  let targ1 : Fin 6 → Fin 18 ⊕ Fin 18 := fun q => Sum.inr ⟨9 + q.1, by omega⟩
  let part1 : Fin 6 → Fin 18 ⊕ Fin 18 := fun q => Sum.inl ⟨9 + q.1, by omega⟩
  have hinj1 : Function.Injective targ1 := by
    intro a b h
    have := Sum.inr.inj h
    exact Fin.ext (by have := congrArg Fin.val this; dsimp at this; omega)
  have hne1 : ∀ a₁ a₂, targ1 a₁ ≠ part1 a₂ := fun _ _ h => by cases h
  have h1 := det_foldl_updateRow_add (List.finRange 6) (List.nodup_finRange 6)
    targ1 part1 (fun q => -lam36 q) hinj1 hne1 M0
  let M1 := (List.finRange 6).foldl
    (fun (M : Matrix (Fin 18 ⊕ Fin 18) (Fin 18 ⊕ Fin 18) ℂ) (q : Fin 6) =>
      M.updateRow (targ1 q) (M (targ1 q) + (-lam36 q) • M (part1 q)))
    M0
  have hM1_det : M1.det = M0.det := h1.1
  have hM1_inl : ∀ r c, M1 (Sum.inl r) c = M0 (Sum.inl r) c := by
    intro r c
    have hu := h1.2.1 (Sum.inl r) (fun _ _ h => by cases h)
    exact congrFun hu c
  have hM1_inr_ring : ∀ (q : Fin 6) (c : Fin 18 ⊕ Fin 18),
      M1 (targ1 q) c = M0 (targ1 q) c + (-lam36 q) * M0 (part1 q) c := by
    intro q c
    exact congrFun (h1.2.2 q (List.mem_finRange q)) c
  have hM1_inr_ax : ∀ (r : Fin 18), r.1 < 9 ∨ 15 ≤ r.1 → ∀ c,
      M1 (Sum.inr r) c = M0 (Sum.inr r) c := by
    intro r hr c
    refine congrFun (h1.2.1 (Sum.inr r) fun q _ he => ?_) c
    have hrv := congrArg Fin.val (Sum.inr.inj he)
    dsimp [targ1] at hrv
    omega
  have hinj2 : Function.Injective part1 := by
    intro a b h
    have := Sum.inl.inj h
    exact Fin.ext (by have := congrArg Fin.val this; dsimp at this; omega)
  have hne2 : ∀ a₁ a₂, part1 a₁ ≠ targ1 a₂ := fun _ _ h => by cases h
  have h2 := det_foldl_updateRow_add (List.finRange 6) (List.nodup_finRange 6)
    part1 targ1 (fun q => (2 * lam36 q)⁻¹) hinj2 hne2 M1
  let M2 := (List.finRange 6).foldl
    (fun (M : Matrix (Fin 18 ⊕ Fin 18) (Fin 18 ⊕ Fin 18) ℂ) (q : Fin 6) =>
      M.updateRow (part1 q) (M (part1 q) + (2 * lam36 q)⁻¹ • M (targ1 q)))
    M1
  have hM2_det : M2.det = M0.det := h2.1.trans hM1_det
  have hM2_inl_ring : ∀ (q : Fin 6) (c : Fin 18 ⊕ Fin 18),
      M2 (part1 q) c = M1 (part1 q) c + (2 * lam36 q)⁻¹ * M1 (targ1 q) c := by
    intro q c
    exact congrFun (h2.2.2 q (List.mem_finRange q)) c
  have hM2_inl_ax : ∀ (r : Fin 18), r.1 < 9 ∨ 15 ≤ r.1 → ∀ c,
      M2 (Sum.inl r) c = M1 (Sum.inl r) c := by
    intro r hr c
    refine congrFun (h2.2.1 (Sum.inl r) fun q _ he => ?_) c
    have hrv := congrArg Fin.val (Sum.inl.inj he)
    dsimp [part1] at hrv
    omega
  have hM2_inr : ∀ r c, M2 (Sum.inr r) c = M1 (Sum.inr r) c := by
    intro r c
    exact congrFun (h2.2.1 (Sum.inr r) fun _ _ h => by cases h) c
  let dO : Fin 18 → ℂ := fun r =>
    if h : 9 ≤ r.1 ∧ r.1 < 15 then -2 * lam36 ⟨r.1 - 9, by omega⟩ else 1
  have hM2_eq : M2 = Matrix.fromBlocks evenBlock 0 0 (Matrix.diagonal dO * oddBlock) := by
    ext r c
    rcases r with r | r <;> rcases c with c | c
    · by_cases hr : 9 ≤ r.1 ∧ r.1 < 15
      · let q : Fin 6 := ⟨r.1 - 9, by omega⟩
        have hreq : (⟨9 + q.1, by omega⟩ : Fin 18) = r := by apply Fin.ext; dsimp [q]; omega
        rw [← hreq]
        change M2 (part1 q) (Sum.inl c) = evenBlock ⟨9 + q.1, by omega⟩ c
        rw [hM2_inl_ring, hM1_inl, hM1_inr_ring]
        have hrq := h_ring q c
        rw [hrq.2.1]
        change M0 (part1 q) (Sum.inl c) + (2 * lam36 q)⁻¹ *
            (lam36 q * M0 (part1 q) (Sum.inl c) + (-lam36 q) * M0 (part1 q) (Sum.inl c)) =
          evenBlock ⟨9 + q.1, by omega⟩ c
        have h0 : lam36 q * M0 (part1 q) (Sum.inl c) + (-lam36 q) * M0 (part1 q) (Sum.inl c) = 0 := by ring
        rw [h0, mul_zero, add_zero]
        exact hrq.1
      · have hrax : r.1 < 9 ∨ 15 ≤ r.1 := by omega
        change M2 (Sum.inl r) (Sum.inl c) = evenBlock r c
        rw [hM2_inl_ax r hrax, hM1_inl]
        exact (h_even_ax r hrax c).1
    · by_cases hr : 9 ≤ r.1 ∧ r.1 < 15
      · let q : Fin 6 := ⟨r.1 - 9, by omega⟩
        have hreq : (⟨9 + q.1, by omega⟩ : Fin 18) = r := by apply Fin.ext; dsimp [q]; omega
        rw [← hreq]
        change M2 (part1 q) (Sum.inr c) = 0
        rw [hM2_inl_ring, hM1_inl, hM1_inr_ring]
        have hrq := h_ring q c
        have hlam := lam36_ne_zero q
        change M0 (part1 q) (Sum.inr c) + (2 * lam36 q)⁻¹ *
            (M0 (targ1 q) (Sum.inr c) + (-lam36 q) * M0 (part1 q) (Sum.inr c)) = 0
        rw [hrq.2.2.2]
        field_simp [hlam]
        ring
      · have hrax : r.1 < 9 ∨ 15 ≤ r.1 := by omega
        change M2 (Sum.inl r) (Sum.inr c) = 0
        rw [hM2_inl_ax r hrax, hM1_inl]
        exact (h_even_ax r hrax c).2
    · change M2 (Sum.inr r) (Sum.inl c) = 0
      rw [hM2_inr]
      by_cases hr : 9 ≤ r.1 ∧ r.1 < 15
      · let q : Fin 6 := ⟨r.1 - 9, by omega⟩
        have hreq : (⟨9 + q.1, by omega⟩ : Fin 18) = r := by apply Fin.ext; dsimp [q]; omega
        rw [← hreq]
        change M1 (targ1 q) (Sum.inl c) = 0
        rw [hM1_inr_ring, (h_ring q c).2.1]
        ring
      · have hrax : r.1 < 9 ∨ 15 ≤ r.1 := by omega
        rw [hM1_inr_ax r hrax]
        exact (h_odd_ax r hrax c).1
    · change M2 (Sum.inr r) (Sum.inr c) = (Matrix.diagonal dO * oddBlock) r c
      rw [hM2_inr, Matrix.diagonal_mul]
      by_cases hr : 9 ≤ r.1 ∧ r.1 < 15
      · let q : Fin 6 := ⟨r.1 - 9, by omega⟩
        have hreq : (⟨9 + q.1, by omega⟩ : Fin 18) = r := by apply Fin.ext; dsimp [q]; omega
        rw [← hreq]
        have hd : dO ⟨9 + q.1, by omega⟩ = -2 * lam36 q := by
          have hlt15 : 9 + q.1 < 15 := by omega
          simp [dO, hlt15]
        rw [hd]
        change M1 (targ1 q) (Sum.inr c) = -2 * lam36 q * oddBlock ⟨9 + q.1, by omega⟩ c
        rw [hM1_inr_ring, (h_ring q c).2.2.2, (h_ring q c).2.2.1]
        ring
      · have hrax : r.1 < 9 ∨ 15 ≤ r.1 := by omega
        have hd : dO r = 1 := by simp [dO, hr]
        rw [hd, one_mul, hM1_inr_ax r hrax]
        exact (h_odd_ax r hrax c).2
  have hprod_dO : (Matrix.diagonal dO).det = 64 := by
    rw [Matrix.det_diagonal, ← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun r : Fin 18 => 9 ≤ r.1 ∧ r.1 < 15)]
    have h1 : (∏ r ∈ Finset.univ.filter (fun r : Fin 18 => 9 ≤ r.1 ∧ r.1 < 15), dO r) = 64 := by
      have hbij :
          (∏ r ∈ Finset.univ.filter (fun r : Fin 18 => 9 ≤ r.1 ∧ r.1 < 15), dO r) =
            ∏ q : Fin 6, (-2 * lam36 q) := by
        refine (Finset.prod_bij (fun (r : Fin 18) hr =>
            (⟨r.1 - 9, by have := (Finset.mem_filter.mp hr).2; omega⟩ : Fin 6))
          (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_)
        · intro r₁ hr₁ r₂ hr₂ heq
          have h1' := (Finset.mem_filter.mp hr₁).2
          have h2' := (Finset.mem_filter.mp hr₂).2
          apply Fin.ext
          have := congrArg Fin.val heq
          dsimp at this
          omega
        · intro q _
          refine ⟨⟨9 + q.1, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega⟩, ?_⟩
          apply Fin.ext; dsimp; omega
        · intro r hr
          have h := (Finset.mem_filter.mp hr).2
          simp [dO, h]
      rw [hbij, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_fin, prod_lam36_eq_one]
      norm_num
    have h2 : (∏ r ∈ Finset.univ.filter (fun r : Fin 18 => ¬ (9 ≤ r.1 ∧ r.1 < 15)), dO r) = 1 :=
      Finset.prod_eq_one fun r hr => by simp [dO, (Finset.mem_filter.mp hr).2]
    rw [h1, h2, mul_one]
  rw [← hM2_det, hM2_eq, Matrix.det_fromBlocks_zero₁₂, Matrix.det_mul, hprod_dO]
  ring

theorem det_stereoMat_eq_even_odd (t : ℝ) :
    (atiyahMat (stereoSpinor (x36Clamp t).1)).det =
      (64 : ℂ) * (evenMat18 (x36Clamp t).1).det * (oddMat18 (x36Clamp t).1).det := by
  let p := (x36Clamp t).1
  let M0 : Matrix (Fin 18 ⊕ Fin 18) (Fin 18 ⊕ Fin 18) ℂ :=
    Matrix.reindex parityEquiv.symm parityEquiv.symm (atiyahMat (stereoSpinor p))
  have hM0_det : M0.det = (atiyahMat (stereoSpinor p)).det :=
    Matrix.det_reindex_self parityEquiv.symm (atiyahMat (stereoSpinor p))
  rw [← hM0_det]
  refine det_block_antipodal_abstract M0 (evenMat18 p) (oddMat18 p) ?_ ?_ ?_
  · intro r hr c
    have hsrc : parityEquiv (Sum.inl r) = evenSrcRow r := by
      apply Fin.ext; dsimp [parityEquiv, evenSrcRow]
      rcases hr with hr | hr
      · simp [hr]
      · have h1' : ¬ r.1 < 9 := by omega
        have h2' : ¬ r.1 < 15 := by omega
        simp [h1', h2']; omega
    constructor
    · change atiyahMat (stereoSpinor p) (parityEquiv (Sum.inl r)) ⟨2 * c.1, by omega⟩ =
        evenMat18 p r c
      rw [hsrc]; rfl
    · change atiyahMat (stereoSpinor p) (parityEquiv (Sum.inl r)) ⟨2 * c.1 + 1, by omega⟩ = 0
      refine atiyahMat_axial_parity_zero t (parityEquiv (Sum.inl r)) ⟨2 * c.1 + 1, by omega⟩ ?_ ?_
      · dsimp [parityEquiv]; omega
      · dsimp [parityEquiv]; omega
  · intro r hr c
    have hsrc : parityEquiv (Sum.inr r) = oddSrcRow r := by
      apply Fin.ext; dsimp [parityEquiv, oddSrcRow]
      rcases hr with hr | hr
      · simp [hr]
      · have h1' : ¬ r.1 < 9 := by omega
        have h2' : ¬ r.1 < 15 := by omega
        simp [h1', h2']; omega
    constructor
    · change atiyahMat (stereoSpinor p) (parityEquiv (Sum.inr r)) ⟨2 * c.1, by omega⟩ = 0
      refine atiyahMat_axial_parity_zero t (parityEquiv (Sum.inr r)) ⟨2 * c.1, by omega⟩ ?_ ?_
      · dsimp [parityEquiv]; omega
      · dsimp [parityEquiv]; omega
    · change atiyahMat (stereoSpinor p) (parityEquiv (Sum.inr r)) ⟨2 * c.1 + 1, by omega⟩ =
        oddMat18 p r c
      rw [hsrc]; rfl
  · intro q c
    have hring_entries : ∀ k : Fin 36,
        atiyahMat (stereoSpinor p) ⟨18 + 2 * q.1 + 1, by omega⟩ k =
          lam36 q * (-1 : ℂ) ^ k.1 * atiyahMat (stereoSpinor p) ⟨18 + 2 * q.1, by omega⟩ k := by
      intro k
      have hp := atiyahPoly_ringPair t q
      have hc := congrArg (fun P : Polynomial ℂ => P.coeff k.1) hp
      rw [Polynomial.coeff_C_mul, coeff_comp_neg_X] at hc
      simpa [atiyahMat, mul_assoc] using hc
    have hsrcE : parityEquiv (Sum.inl ⟨9 + q.1, by omega⟩) = evenSrcRow ⟨9 + q.1, by omega⟩ := by
      have h1 : ¬ 9 + q.1 < 9 := by omega
      have h2 : 9 + q.1 < 15 := by omega
      apply Fin.ext; dsimp [parityEquiv, evenSrcRow]; simp only [h1, h2, ↓reduceIte]; omega
    have hsrcO : parityEquiv (Sum.inl ⟨9 + q.1, by omega⟩) = oddSrcRow ⟨9 + q.1, by omega⟩ := by
      have h1 : ¬ 9 + q.1 < 9 := by omega
      have h2 : 9 + q.1 < 15 := by omega
      apply Fin.ext; dsimp [parityEquiv, oddSrcRow]; simp only [h1, h2, ↓reduceIte]; omega
    have he1 : parityEquiv (Sum.inl ⟨9 + q.1, by omega⟩) = ⟨18 + 2 * q.1, by omega⟩ := by
      apply Fin.ext; dsimp [parityEquiv]; omega
    have he2 : parityEquiv (Sum.inr ⟨9 + q.1, by omega⟩) = ⟨18 + 2 * q.1 + 1, by omega⟩ := by
      apply Fin.ext; dsimp [parityEquiv]; omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · change atiyahMat (stereoSpinor p) (parityEquiv (Sum.inl ⟨9 + q.1, by omega⟩)) ⟨2 * c.1, by omega⟩ =
        evenMat18 p ⟨9 + q.1, by omega⟩ c
      rw [hsrcE]; rfl
    · change atiyahMat (stereoSpinor p) (parityEquiv (Sum.inr ⟨9 + q.1, by omega⟩)) ⟨2 * c.1, by omega⟩ =
        lam36 q * atiyahMat (stereoSpinor p) (parityEquiv (Sum.inl ⟨9 + q.1, by omega⟩)) ⟨2 * c.1, by omega⟩
      rw [he1, he2, hring_entries]
      have hpow : (-1 : ℂ) ^ (2 * c.1) = 1 := by rw [pow_mul]; norm_num
      change lam36 q * (-1 : ℂ) ^ (2 * c.1) * _ = _
      rw [hpow, mul_one]
    · change atiyahMat (stereoSpinor p) (parityEquiv (Sum.inl ⟨9 + q.1, by omega⟩)) ⟨2 * c.1 + 1, by omega⟩ =
        oddMat18 p ⟨9 + q.1, by omega⟩ c
      rw [hsrcO]; rfl
    · change atiyahMat (stereoSpinor p) (parityEquiv (Sum.inr ⟨9 + q.1, by omega⟩)) ⟨2 * c.1 + 1, by omega⟩ =
        -lam36 q * atiyahMat (stereoSpinor p) (parityEquiv (Sum.inl ⟨9 + q.1, by omega⟩)) ⟨2 * c.1 + 1, by omega⟩
      rw [he1, he2, hring_entries]
      have hpow : (-1 : ℂ) ^ (2 * c.1 + 1) = -1 := by rw [pow_add, pow_mul]; norm_num
      change lam36 q * (-1 : ℂ) ^ (2 * c.1 + 1) * _ = _
      rw [hpow]; ring

private lemma x36Base_axial_xy (i : Fin 36) (hi : i.1 < 18 ∨ 30 ≤ i.1) :
    x36BaseX i = 0 ∧ x36BaseY i = 0 := by
  revert i hi; decide

private lemma stereoSlope_axial_zero (t : ℝ) {i j : Fin 36}
    (hi : i.1 < 18 ∨ 30 ≤ i.1) (hj : j.1 < 18 ∨ 30 ≤ j.1) :
    stereoSlope (x36Clamp t).1 i j = 0 := by
  have hxi := x36Base_axial_xy i hi
  have hxj := x36Base_axial_xy j hj
  unfold stereoSlope
  simp [x36Clamp, x36ClampRaw, hxi.1, hxi.2, hxj.1, hxj.2]

private lemma atiyahPoly_lower_axial (t : ℝ) (i : Fin 36) (hi : i.1 < 18) :
    (∀ k < i.1, (atiyahPoly (stereoSpinor (x36Clamp t).1) i).coeff k = 0) ∧
      (atiyahPoly (stereoSpinor (x36Clamp t).1) i).coeff i.1 = 1 := by
  classical
  let Ilo := (Finset.univ.erase i).filter (· < i)
  let Ihi := (Finset.univ.erase i).filter (fun j => ¬ j < i)
  have hsplit : atiyahPoly (stereoSpinor (x36Clamp t).1) i =
      (∏ j ∈ Ilo, (Polynomial.C (stereoSpinor (x36Clamp t).1 i j 0) +
          Polynomial.C (stereoSpinor (x36Clamp t).1 i j 1) * Polynomial.X)) *
        (∏ j ∈ Ihi, (Polynomial.C (stereoSpinor (x36Clamp t).1 i j 0) +
          Polynomial.C (stereoSpinor (x36Clamp t).1 i j 1) * Polynomial.X)) := by
    unfold atiyahPoly
    exact (Finset.prod_filter_mul_prod_filter_not (Finset.univ.erase i) (· < i) _).symm
  have hlo :
      (∏ j ∈ Ilo, (Polynomial.C (stereoSpinor (x36Clamp t).1 i j 0) +
          Polynomial.C (stereoSpinor (x36Clamp t).1 i j 1) * Polynomial.X)) =
        Polynomial.X ^ i.1 := by
    have hfac : ∀ j ∈ Ilo,
        Polynomial.C (stereoSpinor (x36Clamp t).1 i j 0) +
          Polynomial.C (stereoSpinor (x36Clamp t).1 i j 1) * Polynomial.X = Polynomial.X := by
      intro j hj
      have hlt : j < i := (Finset.mem_filter.mp hj).2
      have hne : j ≠ i := ne_of_lt hlt
      have hnot : ¬ i < j := not_lt_of_gt hlt
      have hj_ax : j.1 < 18 ∨ 30 ≤ j.1 := Or.inl (lt_trans hlt hi)
      have hs := stereoSlope_axial_zero t hj_ax (Or.inl hi)
      simp [stereoSpinor, hne.symm, hnot, hs]
    have hcard : Ilo.card = i.1 := by
      have hfilt : Ilo = Finset.univ.filter (· < i) := by
        ext j; simp only [Ilo, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true]
        exact ⟨fun h => h.2, fun h => ⟨h.ne, h⟩⟩
      rw [hfilt]
      have himg : Finset.univ.filter (· < i) =
          Finset.image (fun k : Fin i.1 => ⟨k.1, lt_trans k.2 i.2⟩) Finset.univ := by
        ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
        exact ⟨fun h => ⟨⟨j.1, h⟩, rfl⟩, fun ⟨k, hk⟩ => hk ▸ k.2⟩
      rw [himg, Finset.card_image_of_injective _ (fun a b h => by ext; simpa using congr_arg Fin.val h),
        Finset.card_fin]
    rw [Finset.prod_congr rfl hfac, Finset.prod_const, hcard]
  have hhi0 :
      (∏ j ∈ Ihi, (Polynomial.C (stereoSpinor (x36Clamp t).1 i j 0) +
          Polynomial.C (stereoSpinor (x36Clamp t).1 i j 1) * Polynomial.X)).coeff 0 = 1 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod]
    refine Finset.prod_eq_one fun j hj => ?_
    have hj_mem := Finset.mem_filter.mp hj
    have hne : j ≠ i := (Finset.mem_erase.mp hj_mem.1).1
    have hgt : i < j := lt_of_le_of_ne (not_lt.mp hj_mem.2) hne.symm
    simp [stereoSpinor, hne.symm, hgt]
  rw [hsplit, hlo]
  constructor
  · intro k hk
    rw [Polynomial.coeff_X_pow_mul']
    simp [not_le_of_gt hk]
  · simpa using Polynomial.coeff_X_pow_mul
      (∏ j ∈ Ihi, (Polynomial.C (stereoSpinor (x36Clamp t).1 i j 0) +
        Polynomial.C (stereoSpinor (x36Clamp t).1 i j 1) * Polynomial.X)) i.1 0 |>.trans hhi0

private lemma atiyahPoly_upper_axial (t : ℝ) (i : Fin 36) (hi : 30 ≤ i.1) :
    (∀ k < 18, (atiyahPoly (stereoSpinor (x36Clamp t).1) i).coeff k = 0) ∧
      (∀ k, i.1 < k → (atiyahPoly (stereoSpinor (x36Clamp t).1) i).coeff k = 0) ∧
      (atiyahPoly (stereoSpinor (x36Clamp t).1) i).coeff i.1 = 1 := by
  classical
  let Ilo := (Finset.univ.erase i).filter (· < i)
  let Ihi := (Finset.univ.erase i).filter (fun j => ¬ j < i)
  have hsplit : atiyahPoly (stereoSpinor (x36Clamp t).1) i =
      (∏ j ∈ Ilo, (Polynomial.C (stereoSpinor (x36Clamp t).1 i j 0) +
          Polynomial.C (stereoSpinor (x36Clamp t).1 i j 1) * Polynomial.X)) *
        (∏ j ∈ Ihi, (Polynomial.C (stereoSpinor (x36Clamp t).1 i j 0) +
          Polynomial.C (stereoSpinor (x36Clamp t).1 i j 1) * Polynomial.X)) := by
    unfold atiyahPoly
    exact (Finset.prod_filter_mul_prod_filter_not (Finset.univ.erase i) (· < i) _).symm
  have hhi_one :
      (∏ j ∈ Ihi, (Polynomial.C (stereoSpinor (x36Clamp t).1 i j 0) +
          Polynomial.C (stereoSpinor (x36Clamp t).1 i j 1) * Polynomial.X)) = 1 := by
    refine Finset.prod_eq_one fun j hj => ?_
    have hj_mem := Finset.mem_filter.mp hj
    have hne : j ≠ i := (Finset.mem_erase.mp hj_mem.1).1
    have hgt : i < j := lt_of_le_of_ne (not_lt.mp hj_mem.2) hne.symm
    have hj_ax : j.1 < 18 ∨ 30 ≤ j.1 := Or.inr (le_trans hi hgt.le)
    have hs := stereoSlope_axial_zero t (Or.inr hi) hj_ax
    simp [stereoSpinor, hne.symm, hgt, hs]
  have hpoly_lo : atiyahPoly (stereoSpinor (x36Clamp t).1) i =
      ∏ j ∈ Ilo, (Polynomial.C (stereoSpinor (x36Clamp t).1 i j 0) +
        Polynomial.C (stereoSpinor (x36Clamp t).1 i j 1) * Polynomial.X) := by
    rw [hsplit, hhi_one, mul_one]
  have hmonic_fac : ∀ j ∈ Ilo,
      (Polynomial.C (stereoSpinor (x36Clamp t).1 i j 0) +
          Polynomial.C (stereoSpinor (x36Clamp t).1 i j 1) * Polynomial.X).Monic ∧
        (Polynomial.C (stereoSpinor (x36Clamp t).1 i j 0) +
          Polynomial.C (stereoSpinor (x36Clamp t).1 i j 1) * Polynomial.X).natDegree = 1 := by
    intro j hj
    have hlt : j < i := (Finset.mem_filter.mp hj).2
    have hne : j ≠ i := ne_of_lt hlt
    have hnot : ¬ i < j := not_lt_of_gt hlt
    have heq :
        Polynomial.C (stereoSpinor (x36Clamp t).1 i j 0) +
          Polynomial.C (stereoSpinor (x36Clamp t).1 i j 1) * Polynomial.X =
        Polynomial.X + Polynomial.C (-star (stereoSlope (x36Clamp t).1 j i)) := by
      simp only [stereoSpinor, hne.symm, ↓reduceIte, hnot, Matrix.cons_val_zero,
        Matrix.cons_val_one, map_one, one_mul]
      ring
    rw [heq]
    exact ⟨Polynomial.monic_X_add_C _, Polynomial.natDegree_X_add_C _⟩
  have hmonic : (atiyahPoly (stereoSpinor (x36Clamp t).1) i).Monic := by
    rw [hpoly_lo]
    exact Polynomial.monic_prod_of_monic Ilo _ fun j hj => (hmonic_fac j hj).1
  have hcard : Ilo.card = i.1 := by
    have hfilt : Ilo = Finset.univ.filter (· < i) := by
      ext j; simp only [Ilo, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true]
      exact ⟨fun h => h.2, fun h => ⟨h.ne, h⟩⟩
    rw [hfilt]
    have himg : Finset.univ.filter (· < i) =
        Finset.image (fun k : Fin i.1 => ⟨k.1, lt_trans k.2 i.2⟩) Finset.univ := by
      ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      exact ⟨fun h => ⟨⟨j.1, h⟩, rfl⟩, fun ⟨k, hk⟩ => hk ▸ k.2⟩
    rw [himg, Finset.card_image_of_injective _ (fun a b h => by ext; simpa using congr_arg Fin.val h),
      Finset.card_fin]
  have hdeg : (atiyahPoly (stereoSpinor (x36Clamp t).1) i).natDegree = i.1 := by
    rw [hpoly_lo, Polynomial.natDegree_prod_of_monic Ilo _ fun j hj => (hmonic_fac j hj).1]
    simp only [Finset.sum_congr rfl fun j hj => (hmonic_fac j hj).2, Finset.sum_const, smul_eq_mul,
      mul_one, hcard]
  have hdvd : Polynomial.X ^ 18 ∣ atiyahPoly (stereoSpinor (x36Clamp t).1) i := by
    let I18 := Ilo.filter (fun j : Fin 36 => j.1 < 18)
    have hI18_sub : I18 ⊆ Ilo := Finset.filter_subset _ _
    have hdiv_prod := Finset.prod_dvd_prod_of_subset I18 Ilo
      (fun j => Polynomial.C (stereoSpinor (x36Clamp t).1 i j 0) +
        Polynomial.C (stereoSpinor (x36Clamp t).1 i j 1) * Polynomial.X) hI18_sub
    have hI18_eq :
        (∏ j ∈ I18, (Polynomial.C (stereoSpinor (x36Clamp t).1 i j 0) +
            Polynomial.C (stereoSpinor (x36Clamp t).1 i j 1) * Polynomial.X)) =
          Polynomial.X ^ 18 := by
      have hfac18 : ∀ j ∈ I18,
          Polynomial.C (stereoSpinor (x36Clamp t).1 i j 0) +
            Polynomial.C (stereoSpinor (x36Clamp t).1 i j 1) * Polynomial.X = Polynomial.X := by
        intro j hj
        have hlt : j < i := (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2
        have hj18 : j.1 < 18 := (Finset.mem_filter.mp hj).2
        have hne : j ≠ i := ne_of_lt hlt
        have hnot : ¬ i < j := not_lt_of_gt hlt
        have hs := stereoSlope_axial_zero t (Or.inl hj18) (Or.inr hi)
        simp [stereoSpinor, hne.symm, hnot, hs]
      have hI18_card : I18.card = 18 := by
        have himg : I18 = Finset.image (fun k : Fin 18 => ⟨k.1, by omega⟩) Finset.univ := by
          ext j
          simp only [I18, Ilo, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and,
            and_true, Finset.mem_image]
          constructor
          · intro h; exact ⟨⟨j.1, h.2⟩, rfl⟩
          · rintro ⟨k, rfl⟩
            have hk18 : k.1 < 18 := k.isLt
            have hi30 : 30 ≤ i.1 := hi
            have hk_lt : (⟨k.1, by omega⟩ : Fin 36) < i := Fin.lt_def.mpr (by dsimp; omega)
            exact ⟨⟨Fin.ne_of_lt hk_lt, hk_lt⟩, hk18⟩
        rw [himg, Finset.card_image_of_injective _ (fun a b h => by ext; simpa using congr_arg Fin.val h),
          Finset.card_fin]
      rw [Finset.prod_congr rfl hfac18, Finset.prod_const, hI18_card]
    rw [hpoly_lo, ← hI18_eq]
    exact hdiv_prod
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    rcases hdvd with ⟨Q, hQ⟩
    rw [hQ, Polynomial.coeff_X_pow_mul']
    simp [not_le_of_gt hk]
  · intro k hk
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (hdeg ▸ hk)
  · rw [← hdeg]
    exact hmonic.leadingCoeff

lemma evenMat18_triangular (t : ℝ) :
    (∀ r c : Fin 18, r.1 < 9 → c.1 < r.1 → evenMat18 (x36Clamp t).1 r c = 0) ∧
      (∀ r : Fin 18, r.1 < 9 → evenMat18 (x36Clamp t).1 r r = 1) ∧
      (∀ r c : Fin 18, 15 ≤ r.1 → c.1 < 9 → evenMat18 (x36Clamp t).1 r c = 0) ∧
      (∀ r c : Fin 18, 15 ≤ r.1 → r.1 < c.1 → evenMat18 (x36Clamp t).1 r c = 0) ∧
      (∀ r : Fin 18, 15 ≤ r.1 → evenMat18 (x36Clamp t).1 r r = 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r c hr hlt
    have hs : evenSrcRow r = ⟨2 * r.1, by omega⟩ := by simp [evenSrcRow, hr]
    have hax := (atiyahPoly_lower_axial t ⟨2 * r.1, by omega⟩ (by dsimp; omega)).1
      (2 * c.1) (by dsimp; omega)
    simpa [evenMat18, hs, atiyahMat] using hax
  · intro r hr
    have hs : evenSrcRow r = ⟨2 * r.1, by omega⟩ := by simp [evenSrcRow, hr]
    have hax := (atiyahPoly_lower_axial t ⟨2 * r.1, by omega⟩ (by dsimp; omega)).2
    simpa [evenMat18, hs, atiyahMat] using hax
  · intro r c hr hc
    have hs : evenSrcRow r = ⟨30 + 2 * (r.1 - 15), by omega⟩ := by
      have h1 : ¬ r.1 < 9 := by omega
      have h2 : ¬ r.1 < 15 := by omega
      simp [evenSrcRow, h1, h2]
    have hax := (atiyahPoly_upper_axial t ⟨30 + 2 * (r.1 - 15), by omega⟩ (by dsimp; omega)).1
      (2 * c.1) (by omega)
    simpa [evenMat18, hs, atiyahMat] using hax
  · intro r c hr hlt
    have hs : evenSrcRow r = ⟨30 + 2 * (r.1 - 15), by omega⟩ := by
      have h1 : ¬ r.1 < 9 := by omega
      have h2 : ¬ r.1 < 15 := by omega
      simp [evenSrcRow, h1, h2]
    have hax := (atiyahPoly_upper_axial t ⟨30 + 2 * (r.1 - 15), by omega⟩ (by dsimp; omega)).2.1
      (2 * c.1) (by dsimp; omega)
    simpa [evenMat18, hs, atiyahMat] using hax
  · intro r hr
    have hs : evenSrcRow r = ⟨30 + 2 * (r.1 - 15), by omega⟩ := by
      have h1 : ¬ r.1 < 9 := by omega
      have h2 : ¬ r.1 < 15 := by omega
      simp [evenSrcRow, h1, h2]
    have hax := (atiyahPoly_upper_axial t ⟨30 + 2 * (r.1 - 15), by omega⟩ (by dsimp; omega)).2.2
    have hi : 30 + 2 * (r.1 - 15) = 2 * r.1 := by omega
    simpa [evenMat18, hs, atiyahMat, hi] using hax

lemma oddMat18_triangular (t : ℝ) :
    (∀ r c : Fin 18, r.1 < 9 → c.1 < r.1 → oddMat18 (x36Clamp t).1 r c = 0) ∧
      (∀ r : Fin 18, r.1 < 9 → oddMat18 (x36Clamp t).1 r r = 1) ∧
      (∀ r c : Fin 18, 15 ≤ r.1 → c.1 < 9 → oddMat18 (x36Clamp t).1 r c = 0) ∧
      (∀ r c : Fin 18, 15 ≤ r.1 → r.1 < c.1 → oddMat18 (x36Clamp t).1 r c = 0) ∧
      (∀ r : Fin 18, 15 ≤ r.1 → oddMat18 (x36Clamp t).1 r r = 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r c hr hlt
    have hs : oddSrcRow r = ⟨2 * r.1 + 1, by omega⟩ := by simp [oddSrcRow, hr]
    have hax := (atiyahPoly_lower_axial t ⟨2 * r.1 + 1, by omega⟩ (by dsimp; omega)).1
      (2 * c.1 + 1) (by dsimp; omega)
    simpa [oddMat18, hs, atiyahMat] using hax
  · intro r hr
    have hs : oddSrcRow r = ⟨2 * r.1 + 1, by omega⟩ := by simp [oddSrcRow, hr]
    have hax := (atiyahPoly_lower_axial t ⟨2 * r.1 + 1, by omega⟩ (by dsimp; omega)).2
    simpa [oddMat18, hs, atiyahMat] using hax
  · intro r c hr hc
    have hs : oddSrcRow r = ⟨31 + 2 * (r.1 - 15), by omega⟩ := by
      have h1 : ¬ r.1 < 9 := by omega
      have h2 : ¬ r.1 < 15 := by omega
      simp [oddSrcRow, h1, h2]
    have hax := (atiyahPoly_upper_axial t ⟨31 + 2 * (r.1 - 15), by omega⟩ (by dsimp; omega)).1
      (2 * c.1 + 1) (by omega)
    simpa [oddMat18, hs, atiyahMat] using hax
  · intro r c hr hlt
    have hs : oddSrcRow r = ⟨31 + 2 * (r.1 - 15), by omega⟩ := by
      have h1 : ¬ r.1 < 9 := by omega
      have h2 : ¬ r.1 < 15 := by omega
      simp [oddSrcRow, h1, h2]
    have hax := (atiyahPoly_upper_axial t ⟨31 + 2 * (r.1 - 15), by omega⟩ (by dsimp; omega)).2.1
      (2 * c.1 + 1) (by dsimp; omega)
    simpa [oddMat18, hs, atiyahMat] using hax
  · intro r hr
    have hs : oddSrcRow r = ⟨31 + 2 * (r.1 - 15), by omega⟩ := by
      have h1 : ¬ r.1 < 9 := by omega
      have h2 : ¬ r.1 < 15 := by omega
      simp [oddSrcRow, h1, h2]
    have hax := (atiyahPoly_upper_axial t ⟨31 + 2 * (r.1 - 15), by omega⟩ (by dsimp; omega)).2.2
    have hi : 31 + 2 * (r.1 - 15) = 2 * r.1 + 1 := by omega
    simpa [oddMat18, hs, atiyahMat, hi] using hax

noncomputable def elimRow18C (M : Fin 18 → Fin 18 → ℂ) (curRow : Fin 18 → ℂ) (r : Fin 18) :
    Fin 18 → ℂ :=
  fun c => curRow c - curRow r * M r c

def pivFinSchedule : List (Fin 18) :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 17, 16, 15]

noncomputable def elimSchedule18C (M : Fin 18 → Fin 18 → ℂ) (q : Fin 6) : Fin 18 → ℂ :=
  pivFinSchedule.foldl (elimRow18C M) (fun c => M ⟨9 + q.1, by omega⟩ c)

noncomputable def reduce18To6C (M : Fin 18 → Fin 18 → ℂ) (q c : Fin 6) : ℂ :=
  elimSchedule18C M q ⟨9 + c.1, by omega⟩

private def midRestEquiv : Fin 6 ⊕ (Fin 9 ⊕ Fin 3) ≃ Fin 18 where
  toFun
    | Sum.inl q => ⟨9 + q.1, by omega⟩
    | Sum.inr (Sum.inl a) => ⟨a.1, by omega⟩
    | Sum.inr (Sum.inr b) => ⟨15 + b.1, by omega⟩
  invFun i :=
    if h1 : i.1 < 9 then Sum.inr (Sum.inl ⟨i.1, h1⟩)
    else if h2 : i.1 < 15 then Sum.inl ⟨i.1 - 9, by omega⟩
    else Sum.inr (Sum.inr ⟨i.1 - 15, by omega⟩)
  left_inv x := by
    rcases x with q | (a | b)
    · dsimp only
      have h1 : ¬ 9 + q.1 < 9 := by omega
      have h2 : 9 + q.1 < 15 := by omega
      simp only [h1, ↓reduceDIte, h2]
      congr 1; apply Fin.ext; dsimp; omega
    · dsimp only
      simp only [a.isLt, ↓reduceDIte]
    · dsimp only
      have h1 : ¬ 15 + b.1 < 9 := by omega
      have h2 : ¬ 15 + b.1 < 15 := by omega
      simp only [h1, h2, ↓reduceDIte]
      congr 1; congr 1; apply Fin.ext; dsimp; omega
  right_inv i := by
    by_cases h1 : i.1 < 9
    · simp only [h1, ↓reduceDIte]
    · by_cases h2 : i.1 < 15
      · simp only [h1, h2, ↓reduceDIte]; apply Fin.ext; dsimp; omega
      · simp only [h1, h2, ↓reduceDIte]; apply Fin.ext; dsimp; omega

private lemma elimSchedule18C_zeros (M : Fin 18 → Fin 18 → ℂ)
    (h1 : ∀ r c : Fin 18, r.1 < 9 → c.1 < r.1 → M r c = 0)
    (h2 : ∀ r : Fin 18, r.1 < 9 → M r r = 1)
    (h3 : ∀ r c : Fin 18, 15 ≤ r.1 → c.1 < 9 → M r c = 0)
    (h4 : ∀ r c : Fin 18, 15 ≤ r.1 → r.1 < c.1 → M r c = 0)
    (h5 : ∀ r : Fin 18, 15 ≤ r.1 → M r r = 1)
    (q : Fin 6) :
    (∀ c : Fin 18, c.1 < 9 → elimSchedule18C M q c = 0) ∧
      (∀ c : Fin 18, 15 ≤ c.1 → elimSchedule18C M q c = 0) := by
  let step := elimRow18C M
  have hpref : ∀ (k : ℕ) (hk : k ≤ 9) (row : Fin 18 → ℂ),
      (∀ c : Fin 18, c.1 < k → ((List.range k).foldl (fun rw n =>
        if hn : n < 18 then step rw ⟨n, hn⟩ else rw) row) c = 0) := by
    intro k
    induction k with
    | zero => intro _ _ c hc; omega
    | succ k ih =>
      intro hk row
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      set cur := (List.range k).foldl (fun rw n =>
        if hn : n < 18 then step rw ⟨n, hn⟩ else rw) row
      have hk18 : k < 18 := by omega
      simp only [hk18, ↓reduceDIte]
      intro c hc
      rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hlt | heq
      · have hcur0 : cur c = 0 := ih (by omega) row c hlt
        have hm0 : M ⟨k, hk18⟩ c = 0 := h1 ⟨k, hk18⟩ c (by dsimp; omega) hlt
        dsimp only [step, elimRow18C]
        rw [hcur0, hm0]
        ring
      · have hc' : c = ⟨k, hk18⟩ := Fin.ext heq
        rw [hc']
        have hm1 : M ⟨k, hk18⟩ ⟨k, hk18⟩ = 1 := h2 ⟨k, hk18⟩ (by dsimp; omega)
        dsimp only [step, elimRow18C]
        rw [hm1]
        ring
  have hsched_eq :
      pivFinSchedule.foldl step (fun c => M ⟨9 + q.1, by omega⟩ c) =
        ([17, 16, 15] : List (Fin 18)).foldl step
          ((List.range 9).foldl (fun rw n =>
            if hn : n < 18 then step rw ⟨n, hn⟩ else rw)
            (fun c => M ⟨9 + q.1, by omega⟩ c)) := by
    have hsplit : pivFinSchedule =
        [0, 1, 2, 3, 4, 5, 6, 7, 8] ++ [17, 16, 15] := rfl
    rw [hsplit, List.foldl_append]
    congr 1
  rw [show elimSchedule18C M q = pivFinSchedule.foldl step (fun c => M ⟨9 + q.1, by omega⟩ c) from rfl,
    hsched_eq]
  set cur9 := (List.range 9).foldl (fun rw n =>
    if hn : n < 18 then step rw ⟨n, hn⟩ else rw) (fun c => M ⟨9 + q.1, by omega⟩ c)
  have hcur9 : ∀ c : Fin 18, c.1 < 9 → cur9 c = 0 := hpref 9 (le_refl 9) _
  have hsuf_pres : ∀ (rw : Fin 18 → ℂ) (r : Fin 18), 15 ≤ r.1 →
      (∀ c : Fin 18, c.1 < 9 → rw c = 0) → ∀ c : Fin 18, c.1 < 9 → step rw r c = 0 := by
    intro rw r hr hrw c hc
    simp [step, elimRow18C, hrw c hc, h3 r c hr hc]
  have hcur17_0 : ∀ c : Fin 18, c.1 < 9 → step cur9 17 c = 0 :=
    hsuf_pres cur9 17 (by decide) hcur9
  have hcur16_0 : ∀ c : Fin 18, c.1 < 9 → step (step cur9 17) 16 c = 0 :=
    hsuf_pres _ 16 (by decide) hcur17_0
  have hcur15_0 : ∀ c : Fin 18, c.1 < 9 → step (step (step cur9 17) 16) 15 c = 0 :=
    hsuf_pres _ 15 (by decide) hcur16_0
  have h17_17 : step cur9 17 17 = 0 := by
    have hm : M (17 : Fin 18) (17 : Fin 18) = 1 := h5 17 (by decide)
    change elimRow18C M cur9 17 17 = 0; dsimp only [elimRow18C]; rw [hm]; ring
  have h16_17 : step (step cur9 17) 16 17 = 0 := by
    have hm : M (16 : Fin 18) (17 : Fin 18) = 0 := h4 16 17 (by decide) (by decide)
    change elimRow18C M (step cur9 17) 16 17 = 0; dsimp only [elimRow18C]; rw [h17_17, hm]; ring
  have h16_16 : step (step cur9 17) 16 16 = 0 := by
    have hm : M (16 : Fin 18) (16 : Fin 18) = 1 := h5 16 (by decide)
    change elimRow18C M (step cur9 17) 16 16 = 0; dsimp only [elimRow18C]; rw [hm]; ring
  have h15_17 : step (step (step cur9 17) 16) 15 17 = 0 := by
    have hm : M (15 : Fin 18) (17 : Fin 18) = 0 := h4 15 17 (by decide) (by decide)
    change elimRow18C M (step (step cur9 17) 16) 15 17 = 0; dsimp only [elimRow18C]; rw [h16_17, hm]; ring
  have h15_16 : step (step (step cur9 17) 16) 15 16 = 0 := by
    have hm : M (15 : Fin 18) (16 : Fin 18) = 0 := h4 15 16 (by decide) (by decide)
    change elimRow18C M (step (step cur9 17) 16) 15 16 = 0; dsimp only [elimRow18C]; rw [h16_16, hm]; ring
  have h15_15 : step (step (step cur9 17) 16) 15 15 = 0 := by
    have hm : M (15 : Fin 18) (15 : Fin 18) = 1 := h5 15 (by decide)
    change elimRow18C M (step (step cur9 17) 16) 15 15 = 0; dsimp only [elimRow18C]; rw [hm]; ring
  simp only [List.foldl_cons, List.foldl_nil]
  refine ⟨hcur15_0, fun c hc => ?_⟩
  have hcases : c = 15 ∨ c = 16 ∨ c = 17 := by
    have hc18 : c.1 < 18 := c.isLt
    have hc15 : c.1 = 15 ∨ c.1 = 16 ∨ c.1 = 17 := by omega
    rcases hc15 with h | h | h
    · exact Or.inl (Fin.ext (by simpa using h))
    · exact Or.inr (Or.inl (Fin.ext (by simpa using h)))
    · exact Or.inr (Or.inr (Fin.ext (by simpa using h)))
  rcases hcases with rfl | rfl | rfl
  · exact h15_15
  · exact h15_16
  · exact h15_17

theorem det_18_eq_det_6 (M : Matrix (Fin 18) (Fin 18) ℂ)
    (h1 : ∀ r c : Fin 18, r.1 < 9 → c.1 < r.1 → M r c = 0)
    (h2 : ∀ r : Fin 18, r.1 < 9 → M r r = 1)
    (h3 : ∀ r c : Fin 18, 15 ≤ r.1 → c.1 < 9 → M r c = 0)
    (h4 : ∀ r c : Fin 18, 15 ≤ r.1 → r.1 < c.1 → M r c = 0)
    (h5 : ∀ r : Fin 18, 15 ≤ r.1 → M r r = 1) :
    M.det = (Matrix.of (reduce18To6C M)).det := by
  let stepRow := fun (r : Fin 18) (A : Matrix (Fin 18) (Fin 18) ℂ) (q : Fin 6) =>
    A.updateRow ⟨9 + q.1, by omega⟩ (A ⟨9 + q.1, by omega⟩ + (-A ⟨9 + q.1, by omega⟩ r) • A r)
  let stepAll := fun (A : Matrix (Fin 18) (Fin 18) ℂ) (r : Fin 18) =>
    (List.finRange 6).foldl (stepRow r) A
  have hinner : ∀ (r : Fin 18) (hr : r.1 < 9 ∨ 15 ≤ r.1)
      (l : List (Fin 6)) (hnodup : l.Nodup) (B : Matrix (Fin 18) (Fin 18) ℂ)
      (hB : ∀ x : Fin 18, (x.1 < 9 ∨ 15 ≤ x.1) → B x = M x),
      (l.foldl (stepRow r) B).det = B.det ∧
        (∀ x : Fin 18, (x.1 < 9 ∨ 15 ≤ x.1) → (l.foldl (stepRow r) B) x = M x) ∧
        (∀ q : Fin 6, q ∈ l →
          (l.foldl (stepRow r) B) ⟨9 + q.1, by omega⟩ = elimRow18C M (B ⟨9 + q.1, by omega⟩) r) ∧
        (∀ q : Fin 6, q ∉ l →
          (l.foldl (stepRow r) B) ⟨9 + q.1, by omega⟩ = B ⟨9 + q.1, by omega⟩) := by
    intro r hr l hnodup B hB
    induction l generalizing B with
    | nil =>
      exact ⟨rfl, hB, fun _ h => absurd h (List.not_mem_nil), fun _ _ => rfl⟩
    | cons q qs ih =>
      simp only [List.foldl_cons]
      have hnodup' : qs.Nodup := (List.nodup_cons.mp hnodup).2
      have hq_not_in : q ∉ qs := (List.nodup_cons.mp hnodup).1
      have hne_qr : (⟨9 + q.1, by omega⟩ : Fin 18) ≠ r := by
        intro heq
        have := congrArg Fin.val heq
        dsimp at this
        omega
      let B₁ := stepRow r B q
      have hB₁_ax : ∀ x : Fin 18, (x.1 < 9 ∨ 15 ≤ x.1) → B₁ x = M x := by
        intro x hx
        have hne_x : x ≠ ⟨9 + q.1, by omega⟩ := by
          intro heq; have := congrArg Fin.val heq; dsimp at this; omega
        simpa [B₁, stepRow, Matrix.updateRow_apply, hne_x] using hB x hx
      have ih1 := ih hnodup' B₁ hB₁_ax
      refine ⟨?_, ih1.2.1, ?_, ?_⟩
      · have hdet1 : B₁.det = B.det := Matrix.det_updateRow_add_smul_self B hne_qr _
        exact ih1.1.trans hdet1
      · intro q' hq'
        rcases List.mem_cons.mp hq' with rfl | hqs
        · rw [ih1.2.2.2 q' hq_not_in]
          ext c
          have hBr : B r c = M r c := congrFun (hB r hr) c
          simp [B₁, stepRow, Matrix.updateRow_apply, elimRow18C, hBr]
          ring
        · have hqq' : (⟨9 + q'.1, by omega⟩ : Fin 18) ≠ ⟨9 + q.1, by omega⟩ := by
            intro heq
            apply hq_not_in
            have : q' = q := Fin.ext (by have := congrArg Fin.val heq; dsimp at this; omega)
            rw [← this]; exact hqs
          have hBq' : B₁ ⟨9 + q'.1, by omega⟩ = B ⟨9 + q'.1, by omega⟩ := by
            simp [B₁, stepRow, hqq']
          rw [ih1.2.2.1 q' hqs, hBq']
      · intro q' hq'
        have hnq : q' ≠ q := fun he => hq' (he ▸ List.mem_cons_self)
        have hnqs : q' ∉ qs := fun hs => hq' (List.mem_cons_of_mem q hs)
        have hqq' : (⟨9 + q'.1, by omega⟩ : Fin 18) ≠ ⟨9 + q.1, by omega⟩ := by
          intro heq
          apply hnq
          exact Fin.ext (by have := congrArg Fin.val heq; dsimp at this; omega)
        rw [ih1.2.2.2 q' hnqs]
        simp [B₁, stepRow, hqq']
  have houter : ∀ (sched : List (Fin 18)), (∀ r ∈ sched, r.1 < 9 ∨ 15 ≤ r.1) →
      ∀ (A : Matrix (Fin 18) (Fin 18) ℂ), (∀ x : Fin 18, (x.1 < 9 ∨ 15 ≤ x.1) → A x = M x) →
      (sched.foldl stepAll A).det = A.det ∧
        (∀ x : Fin 18, (x.1 < 9 ∨ 15 ≤ x.1) → (sched.foldl stepAll A) x = M x) ∧
        (∀ q : Fin 6, (sched.foldl stepAll A) ⟨9 + q.1, by omega⟩ =
          sched.foldl (elimRow18C M) (A ⟨9 + q.1, by omega⟩)) := by
    intro sched
    induction sched with
    | nil => intro _ A hA; exact ⟨rfl, hA, fun _ => rfl⟩
    | cons r rs ih =>
      intro hrs A hA
      simp only [List.foldl_cons]
      have hr : r.1 < 9 ∨ 15 ≤ r.1 := hrs r List.mem_cons_self
      have hrs' : ∀ r' ∈ rs, r'.1 < 9 ∨ 15 ≤ r'.1 := fun r' hr' => hrs r' (List.mem_cons_of_mem r hr')
      have hs1 := hinner r hr (List.finRange 6) (List.nodup_finRange 6) A hA
      have ih1 := ih hrs' (stepAll A r) hs1.2.1
      refine ⟨ih1.1.trans hs1.1, ih1.2.1, fun q => ?_⟩
      rw [ih1.2.2 q]
      congr 1
      exact hs1.2.2.1 q (List.mem_finRange q)
  have hpiv : ∀ r ∈ pivFinSchedule, r.1 < 9 ∨ 15 ≤ r.1 := by decide
  have hfinal := houter pivFinSchedule hpiv M (fun _ _ => rfl)
  let Mfin := pivFinSchedule.foldl stepAll M
  let R := Matrix.reindex midRestEquiv.symm midRestEquiv.symm Mfin
  have hR_det : R.det = M.det := (Matrix.det_reindex_self midRestEquiv.symm Mfin).trans hfinal.1
  let TL : Matrix (Fin 9) (Fin 9) ℂ := fun a a' => M ⟨a.1, by omega⟩ ⟨a'.1, by omega⟩
  let TR : Matrix (Fin 9) (Fin 3) ℂ := fun a b' => M ⟨a.1, by omega⟩ ⟨15 + b'.1, by omega⟩
  let D3 : Matrix (Fin 3) (Fin 3) ℂ := fun b b' => M ⟨15 + b.1, by omega⟩ ⟨15 + b'.1, by omega⟩
  let BL : Matrix (Fin 9 ⊕ Fin 3) (Fin 6) ℂ := fun u c => R (Sum.inr u) (Sum.inl c)
  have hBR_eq : Matrix.submatrix R Sum.inr Sum.inr = Matrix.fromBlocks TL TR 0 D3 := by
    ext u v
    rcases u with a | b <;> rcases v with a' | b'
    · have ha := congrFun (hfinal.2.1 ⟨a.1, by omega⟩ (Or.inl a.2)) ⟨a'.1, by omega⟩
      change Mfin ⟨a.1, by omega⟩ ⟨a'.1, by omega⟩ = TL a a'
      exact ha
    · have ha := congrFun (hfinal.2.1 ⟨a.1, by omega⟩ (Or.inl a.2)) ⟨15 + b'.1, by omega⟩
      change Mfin ⟨a.1, by omega⟩ ⟨15 + b'.1, by omega⟩ = TR a b'
      exact ha
    · have hb := congrFun (hfinal.2.1 ⟨15 + b.1, by omega⟩ (Or.inr (by dsimp; omega))) ⟨a'.1, by omega⟩
      have hz := h3 ⟨15 + b.1, by omega⟩ ⟨a'.1, by omega⟩ (by dsimp; omega) a'.2
      change Mfin ⟨15 + b.1, by omega⟩ ⟨a'.1, by omega⟩ = 0
      exact hb.trans hz
    · have hb := congrFun (hfinal.2.1 ⟨15 + b.1, by omega⟩ (Or.inr (by dsimp; omega))) ⟨15 + b'.1, by omega⟩
      change Mfin ⟨15 + b.1, by omega⟩ ⟨15 + b'.1, by omega⟩ = D3 b b'
      exact hb
  have hTL_ut : TL.IsUpperTriangular := by
    intro a a' hlt
    exact h1 ⟨a.1, by omega⟩ ⟨a'.1, by omega⟩ a.2 hlt
  have hD3_lt : D3.IsLowerTriangular := by
    intro b b' hlt
    have hbb : b < b' := OrderDual.toDual_lt_toDual.mp hlt
    exact h4 ⟨15 + b.1, by omega⟩ ⟨15 + b'.1, by omega⟩ (by dsimp; omega) (by dsimp; omega)
  have hTL_det : TL.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hTL_ut]
    exact Finset.prod_eq_one fun a _ => h2 ⟨a.1, by omega⟩ a.2
  have hD3_det : D3.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular D3 hD3_lt]
    exact Finset.prod_eq_one fun b _ => h5 ⟨15 + b.1, by omega⟩ (by dsimp; omega)
  have hR_blocks : R = Matrix.fromBlocks (Matrix.of (reduce18To6C M)) 0 BL (Matrix.fromBlocks TL TR 0 D3) := by
    rw [← hBR_eq]
    ext u v
    rcases u with q | u' <;> rcases v with c | v'
    · have hq := congrFun (hfinal.2.2 q) ⟨9 + c.1, by omega⟩
      change Mfin ⟨9 + q.1, by omega⟩ ⟨9 + c.1, by omega⟩ = reduce18To6C M q c
      exact hq
    · have hzeros := elimSchedule18C_zeros M h1 h2 h3 h4 h5 q
      have hq := hfinal.2.2 q
      rcases v' with a' | b'
      · change Mfin ⟨9 + q.1, by omega⟩ ⟨a'.1, by omega⟩ = 0
        exact (congrFun hq ⟨a'.1, by omega⟩).trans (hzeros.1 ⟨a'.1, by omega⟩ a'.2)
      · change Mfin ⟨9 + q.1, by omega⟩ ⟨15 + b'.1, by omega⟩ = 0
        exact (congrFun hq ⟨15 + b'.1, by omega⟩).trans
          (hzeros.2 ⟨15 + b'.1, by omega⟩ (by dsimp; omega))
    · rfl
    · rfl
  rw [← hR_det, hR_blocks, Matrix.det_fromBlocks_zero₁₂, Matrix.det_fromBlocks_zero₂₁,
    hTL_det, hD3_det, mul_one, mul_one]

end AntipodalReduce

/-! ## Part 5: Kernel Interval Certification (`t = 9` & `t = 10`) and Main Theorems -/

section CertificationAndDisproofs

def S36 : ℤ := 1000000000000000000

private lemma S36_pos : 0 < S36 := by decide

private def rho9List : List ℤ := [
  104145206322710792352063, 104135216425568540708128, 104125226530365829499914, 104115236637103217026274, 104105246745781261800247, 104095256856400522549164, 104085266968961558214750, 104075277083464927953223, 104065287199911191135404, 104055297318300907346814, 104045307438634636387778, 104035317560912938273532,
  104025327685136373234318, 104015337811305501715498, 104005347939420884377648, 103995358069483082096664, 103985368201492655963869, 103975378335450167286110, 0, 9360000000000000000000, 4643860463019964599763, 8126755810284938049585, 8126755810284938049585, 4643860463019964599763,
  103027904957831691318103, 112382249488075295422244, 105407562916519419925451, 110153369807736703666146, 110153369807736703666146, 105407562916519419925451, 5997074286683465787865, 6003332407921453752689, 6009600652289634461381, 6015878988144625237596, 6022167383924163229136, 6028465808147210516946,
  104145206322710792352063, 104135216425568540708128, 104125226530365829499914, 104115236637103217026274, 104105246745781261800247, 104095256856400522549164, 104085266968961558214750, 104075277083464927953223, 104065287199911191135404, 104055297318300907346814, 104045307438634636387778, 104035317560912938273532,
  104025327685136373234318, 104015337811305501715498, 104005347939420884377648, 103995358069483082096664, 103985368201492655963869, 103975378335450167286110, 0, 0, 8126755810284938049585, 4643860463019964599763, 4643860463019964599763, 8126755810284938049585,
  112382249488075295422244, 103027904957831691318103, 110153369807736703666146, 105407562916519419925451, 105407562916519419925451, 110153369807736703666146, 5997074286683465787865, 6003332407921453752689, 6009600652289634461381, 6015878988144625237596, 6022167383924163229136, 6028465808147210516946,
  104145206322710792352063, 104135216425568540708128, 104125226530365829499914, 104115236637103217026274, 104105246745781261800247, 104095256856400522549164, 104085266968961558214750, 104075277083464927953223, 104065287199911191135404, 104055297318300907346814, 104045307438634636387778, 104035317560912938273532,
  104025327685136373234318, 104015337811305501715498, 104005347939420884377648, 103995358069483082096664, 103985368201492655963869, 103975378335450167286110, 0, 0, 0, 9360000000000000000000, 4752000000000000000000, 8064000000000000000000,
  105407562916519419925451, 110153369807736703666146, 103027904957831691318103, 112382249488075295422244, 105518357606626914367155, 110047241710094669687200, 5997074286683465787865, 6003332407921453752689, 6009600652289634461381, 6015878988144625237596, 6022167383924163229136, 6028465808147210516946,
  104145206322710792352063, 104135216425568540708128, 104125226530365829499914, 104115236637103217026274, 104105246745781261800247, 104095256856400522549164, 104085266968961558214750, 104075277083464927953223, 104065287199911191135404, 104055297318300907346814, 104045307438634636387778, 104035317560912938273532,
  104025327685136373234318, 104015337811305501715498, 104005347939420884377648, 103995358069483082096664, 103985368201492655963869, 103975378335450167286110, 0, 0, 0, 0, 8064000000000000000000, 4752000000000000000000,
  110153369807736703666146, 105407562916519419925451, 112382249488075295422244, 103027904957831691318103, 110047241710094669687200, 105518357606626914367155, 5997074286683465787865, 6003332407921453752689, 6009600652289634461381, 6015878988144625237596, 6022167383924163229136, 6028465808147210516946,
  104145206322710792352063, 104135216425568540708128, 104125226530365829499914, 104115236637103217026274, 104105246745781261800247, 104095256856400522549164, 104085266968961558214750, 104075277083464927953223, 104065287199911191135404, 104055297318300907346814, 104045307438634636387778, 104035317560912938273532,
  104025327685136373234318, 104015337811305501715498, 104005347939420884377648, 103995358069483082096664, 103985368201492655963869, 103975378335450167286110, 0, 0, 0, 0, 0, 9360000000000000000000,
  110153369807736703666146, 105407562916519419925451, 105518357606626914367155, 110047241710094669687200, 103027904957831691318103, 112382249488075295422244, 5997074286683465787865, 6003332407921453752689, 6009600652289634461381, 6015878988144625237596, 6022167383924163229136, 6028465808147210516946,
  104145206322710792352063, 104135216425568540708128, 104125226530365829499914, 104115236637103217026274, 104105246745781261800247, 104095256856400522549164, 104085266968961558214750, 104075277083464927953223, 104065287199911191135404, 104055297318300907346814, 104045307438634636387778, 104035317560912938273532,
  104025327685136373234318, 104015337811305501715498, 104005347939420884377648, 103995358069483082096664, 103985368201492655963869, 103975378335450167286110, 0, 0, 0, 0, 0, 0,
  105407562916519419925451, 110153369807736703666146, 110047241710094669687200, 105518357606626914367155, 112382249488075295422244, 103027904957831691318103, 5997074286683465787865, 6003332407921453752689, 6009600652289634461381, 6015878988144625237596, 6022167383924163229136, 6028465808147210516946,
  152324974971276460078772, 152317899473436804613020, 152310824303461768114099, 152303749461397042784261, 152296674947288327198284, 152289600761181326303972, 152282526903121751422652, 152275453373155320249663, 152268380171327756854859, 152261307297684791683102, 152254234752272161554753, 152247162535135609666175,
  152240090646320885590219, 152233019085873745276725, 152225947853839951053013, 152218876950265271624380, 152211806375195482074591, 152204736128676363866372, 0, 0, 0, 0, 0, 0,
  0, 215280000000000000000000, 106808790649459185794552, 186915383636553575140467, 186915383636553575140467, 106808790649459185794552, 107640000464511333074271, 107640001858045320269730, 107640004180601925504308, 107640007432181088641231, 107640011612782725489025, 107640016722406727801529,
  152324974971276460078772, 152317899473436804613020, 152310824303461768114099, 152303749461397042784261, 152296674947288327198284, 152289600761181326303972, 152282526903121751422652, 152275453373155320249663, 152268380171327756854859, 152261307297684791683102, 152254234752272161554753, 152247162535135609666175,
  152240090646320885590219, 152233019085873745276725, 152225947853839951053013, 152218876950265271624380, 152211806375195482074591, 152204736128676363866372, 0, 0, 0, 0, 0, 0,
  0, 0, 186915383636553575140467, 106808790649459185794552, 106808790649459185794552, 186915383636553575140467, 107640000464511333074271, 107640001858045320269730, 107640004180601925504308, 107640007432181088641231, 107640011612782725489025, 107640016722406727801529,
  152324974971276460078772, 152317899473436804613020, 152310824303461768114099, 152303749461397042784261, 152296674947288327198284, 152289600761181326303972, 152282526903121751422652, 152275453373155320249663, 152268380171327756854859, 152261307297684791683102, 152254234752272161554753, 152247162535135609666175,
  152240090646320885590219, 152233019085873745276725, 152225947853839951053013, 152218876950265271624380, 152211806375195482074591, 152204736128676363866372, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 215280000000000000000000, 109296000000000000000000, 185472000000000000000000, 107640000464511333074271, 107640001858045320269730, 107640004180601925504308, 107640007432181088641231, 107640011612782725489025, 107640016722406727801529,
  152324974971276460078772, 152317899473436804613020, 152310824303461768114099, 152303749461397042784261, 152296674947288327198284, 152289600761181326303972, 152282526903121751422652, 152275453373155320249663, 152268380171327756854859, 152261307297684791683102, 152254234752272161554753, 152247162535135609666175,
  152240090646320885590219, 152233019085873745276725, 152225947853839951053013, 152218876950265271624380, 152211806375195482074591, 152204736128676363866372, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 185472000000000000000000, 109296000000000000000000, 107640000464511333074271, 107640001858045320269730, 107640004180601925504308, 107640007432181088641231, 107640011612782725489025, 107640016722406727801529,
  152324974971276460078772, 152317899473436804613020, 152310824303461768114099, 152303749461397042784261, 152296674947288327198284, 152289600761181326303972, 152282526903121751422652, 152275453373155320249663, 152268380171327756854859, 152261307297684791683102, 152254234752272161554753, 152247162535135609666175,
  152240090646320885590219, 152233019085873745276725, 152225947853839951053013, 152218876950265271624380, 152211806375195482074591, 152204736128676363866372, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 215280000000000000000000, 107640000464511333074271, 107640001858045320269730, 107640004180601925504308, 107640007432181088641231, 107640011612782725489025, 107640016722406727801529,
  152324974971276460078772, 152317899473436804613020, 152310824303461768114099, 152303749461397042784261, 152296674947288327198284, 152289600761181326303972, 152282526903121751422652, 152275453373155320249663, 152268380171327756854859, 152261307297684791683102, 152254234752272161554753, 152247162535135609666175,
  152240090646320885590219, 152233019085873745276725, 152225947853839951053013, 152218876950265271624380, 152211806375195482074591, 152204736128676363866372, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 107640000464511333074271, 107640001858045320269730, 107640004180601925504308, 107640007432181088641231, 107640011612782725489025, 107640016722406727801529]

private def mat6ELit9 : List (List CFpIv) := [
  [⟨⟨6280778329458916978, 6280778329459419568⟩, ⟨-251156, 251180⟩⟩, ⟨⟨43655138928934095691, 43655138928934702247⟩, ⟨-303104, 303300⟩⟩, ⟨⟨84654692346370770370, 84654692346371510435⟩, ⟨-369744, 369837⟩⟩, ⟨⟨6813733363856889218, 6813733363857621363⟩, ⟨-365764, 365798⟩⟩, ⟨⟨-34942566425714744067, -34942566425714327782⟩, ⟨-208116, 208023⟩⟩, ⟨⟨-69667267699256832438, -69667267699256702819⟩, ⟨-64665, 64654⟩⟩],
  [⟨⟨-5417698212360460017, -5417698212356801416⟩, ⟨-3203937292367226485, -3203937292363567886⟩⟩, ⟨⟨38304941251586392309, 38304941251590710081⟩, ⟨-21904140805893232240, -21904140805888914472⟩⟩, ⟨⟨-399287597766970566, -399287597762289802⟩, ⟨86144935301707747980, 86144935301712428699⟩⟩, ⟨⟨-6035878288754613975, -6035878288750750640⟩, ⟨-6723969945046512241, -6723969945042648938⟩⟩, ⟨⟨-31977540360247896837, -31977540360246007685⟩, ⟨20868501810010862310, 20868501810012751476⟩⟩, ⟨⟨-852807934044580570, -852807934044090271⟩, ⟨-69538664795134156861, -69538664795133666566⟩⟩],
  [⟨⟨-3203937292367229295, -3203937292363565127⟩, ⟨-5417698212360462742, -5417698212356798567⟩⟩, ⟨⟨-21904140805893232106, -21904140805888914237⟩, ⟨38304941251586392161, 38304941251590710044⟩⟩, ⟨⟨86144935301707751319, 86144935301712425551⟩, ⟨-399287597766967366, -399287597762293084⟩⟩, ⟨⟨-6723969945046505806, -6723969945042655385⟩, ⟨-6035878288754607594, -6035878288750757148⟩⟩, ⟨⟨20868501810010867324, 20868501810012746263⟩, ⟨-31977540360247891670, -31977540360246012729⟩⟩, ⟨⟨-69538664795134153857, -69538664795133669604⟩, ⟨-852807934044577566, -852807934044093303⟩⟩],
  [⟨⟨3007493434278595381464391, 3007493434278595622111899⟩, ⟨-109536674, 110977983⟩⟩, ⟨⟨5220767975419529938580513, 5220767975419530359813441⟩, ⟨-200107731, 202419431⟩⟩, ⟨⟨5707963163220533992229389, 5707963163220534448535884⟩, ⟨-218787500, 216486444⟩⟩, ⟨⟨3879756438133607986085873, 3879756438133608287191298⟩, ⟨-145751577, 145964029⟩⟩, ⟨⟨1538929683903558207819438, 1538929683903558322160040⟩, ⟨-53497484, 54920154⟩⟩, ⟨⟨346541447005842810992083, 346541447005842830251728⟩, ⟨-8867788, 8867695⟩⟩],
  [⟨⟨-2489931286009339282074959, -2489931286009331284444397⟩, ⟨-1682679783027746972350204, -1682679783027738970921612⟩⟩, ⟨⟨4672263122974192348234315, 4672263122974200833791090⟩, ⟨-2357301875344762717892130, -2357301875344754234787612⟩⟩, ⟨⟨-232628583276658508395755, -232628583276652634365560⟩, ⟨5715903407215267390811592, 5715903407215273265763906⟩⟩, ⟨⟨-3318164957459365946827421, -3318164957459363393595088⟩, ⟨-2025619814960651930096629, -2025619814960649380760641⟩⟩, ⟨⟨1344495160184306176375700, 1344495160184306838320252⟩, ⟨-758590800284167142324726, -758590800284166480381414⟩⟩, ⟨⟨875637836896529135805, 875637836896619885762⟩, ⟨344941986754832863213780, 344941986754832953945125⟩⟩],
  [⟨⟨-1682679783027746972382372, -1682679783027738967577415⟩, ⟨-2489931286009339280889574, -2489931286009331279956647⟩⟩, ⟨⟨-2357301875344762720565385, -2357301875344754233398333⟩, ⟨4672263122974192347582819, 4672263122974200837015808⟩⟩, ⟨⟨5715903407215267390117290, 5715903407215273266502748⟩, ⟨-232628583276658510357497, -232628583276652634845077⟩⟩, ⟨⟨-2025619814960651929352273, -2025619814960649381877543⟩, ⟨-3318164957459365947024815, -3318164957459363395555064⟩⟩, ⟨⟨-758590800284167141892402, -758590800284166481854829⟩, ⟨1344495160184306178668087, 1344495160184306838703050⟩⟩, ⟨⟨344941986754832863817470, 344941986754832953705638⟩, ⟨875637836896529600435, 875637836896619502276⟩⟩]]

private def mat6OLit9 : List (List CFpIv) := [
  [⟨⟨-19485934907565250388, -19485934907564705073⟩, ⟨-272600, 272525⟩⟩, ⟨⟨-70749901281673667492, -70749901281673024977⟩, ⟨-321185, 321156⟩⟩, ⟨⟨-74318716176735837479, -74318716176735130499⟩, ⟨-353251, 353256⟩⟩, ⟨⟨10994565140865763529, 10994565140866322618⟩, ⟨-279399, 279460⟩⟩, ⟨⟨58869938620915620495, 58869938620915867612⟩, ⟨-123464, 123497⟩⟩, ⟨⟨58911198976770956053, 58911198976771011965⟩, ⟨-27782, 27798⟩⟩],
  [⟨⟨-128775878833035756, -128775878829047665⟩, ⟨19562178737732509840, 19562178737736497952⟩⟩, ⟨⟨-62149588208985947117, -62149588208981401738⟩, ⟨-35948322433176912593, -35948322433172367221⟩⟩, ⟨⟨66741866536930447550, 66741866536934804517⟩, ⟨-37507285941141627121, -37507285941137270075⟩⟩, ⟨⟨-3216239340633181452, -3216239340630340722⟩, ⟨-10716315047942483076, -10716315047939642397⟩⟩, ⟨⟨54605139461769687923, 54605139461770725630⟩, ⟨28929075352363700207, 28929075352364737870⟩⟩, ⟨⟨-50478333446705933609, -50478333446705744847⟩, ⟨30447559531492237318, 30447559531492426105⟩⟩],
  [⟨⟨-19562178737736499522, -19562178737732508162⟩, ⟨128775878829046058, 128775878833037382⟩⟩, ⟨⟨35948322433172368835, 35948322433176911017⟩, ⟨62149588208981403311, 62149588208985945495⟩⟩, ⟨⟨37507285941137274709, 37507285941141622558⟩, ⟨-66741866536934799978, -66741866536930452204⟩⟩, ⟨⟨10716315047939648243, 10716315047942477111⟩, ⟨3216239340630346681, 3216239340633175595⟩⟩, ⟨⟨-28929075352364733790, -28929075352363704281⟩, ⟨-54605139461770721533, -54605139461769691994⟩⟩, ⟨⟨-30447559531492424194, -30447559531492239281⟩, ⟨50478333446705746814, 50478333446705931698⟩⟩],
  [⟨⟨-4203114677096766482868536, -4203114677096766113456650⟩, ⟨-171122482, 170767809⟩⟩, ⟨⟨-5788717209517086452464439, -5788717209517085889305114⟩, ⟨-269792812, 268439685⟩⟩, ⟨⟨-4989821922210803702760504, -4989821922210803228883811⟩, ⟨-234499759, 232826550⟩⟩, ⟨⟨-2611258212886004746668839, -2611258212886004498752252⟩, ⟨-120223092, 118270535⟩⟩, ⟨⟨-787354317679984918947077, -787354317679984831155611⟩, ⟨-41070725, 43541372⟩⟩, ⟨⟨-128000864009640807023845, -128000864009640792929875⟩, ⟨-5791182, 5780602⟩⟩],
  [⟨⟨-261006653947308408311420, -261006653947299646151810⟩, ⟨4189228387178554588997092, 4189228387178563346837949⟩⟩, ⟨⟨-4880155734908818513898890, -4880155734908810885745013⟩, ⟨-3141366693531092826691432, -3141366693531085199176951⟩⟩, ⟨⟨4410388888022440286330116, 4410388888022444545862915⟩, ⟨-2356518467587454661940350, -2356518467587450397673758⟩⟩, ⟨⟨-44279046190844877873619, -44279046190843419367481⟩, ⟨2615998153768088155730165, 2615998153768089614080869⟩⟩, ⟨⟨-682765697246317628436676, -682765697246317313303525⟩, ⟨-395770083758880698544072, -395770083758880383420241⟩⟩, ⟨⟨109778441645646103151465, 109778441645646138779220⟩, ⟨-65114865485570619871132, -65114865485570585131377⟩⟩],
  [⟨⟨-4189228387178563348551414, -4189228387178554586756332⟩, ⟨261006653947299643937649, 261006653947308410214949⟩⟩, ⟨⟨3141366693531085198993516, 3141366693531092829497445⟩, ⟨4880155734908810885066394, 4880155734908818516304662⟩⟩, ⟨⟨2356518467587450397439940, 2356518467587454661443601⟩, ⟨-4410388888022444544881488, -4410388888022440285737179⟩⟩, ⟨⟨-2615998153768089612028170, -2615998153768088155819887⟩, ⟨44279046190843420889462, 44279046190844877218691⟩⟩, ⟨⟨395770083758880382935510, 395770083758880696645846⟩, ⟨682765697246317313211322, 682765697246317626941018⟩⟩, ⟨⟨65114865485570585372142, 65114865485570619731278⟩, ⟨-109778441645646138658541, -109778441645646103410208⟩⟩]]

private def prod9Cert : CFpIv := ⟨⟨472736742228441677151215500134227492941685890943607065579074385339120, 472736742258569477122291186505474993805100684374282010086458905127736⟩, ⟨-15063514283962775174250924844691940788580650763264216021321, 15063335845842245926860193275922723546082597575032875251758⟩⟩

private def rho10List : List ℤ := [
  104169868964110730516095, 104159881432344190240955, 104149893902970443688522, 104139906375990179300869, 104129918851404085784025, 104119931329212852108108, 104109943809417167507448, 104099956292017721480716, 104089968777015203791048, 104079981264410304466173, 104069993754203713798543, 104060006246396122345452,
  104050018740988220929171, 104040031237980700637071, 104030043737374252821750, 104020056239169569101164, 104010068743367341358747, 104000081249968261743545, 0, 10400000000000000000000, 5159844958911071777514, 9029728678094375610650, 9029728678094375610650, 5159844958911071777514,
  114461118289137818470370, 124856027487662765219115, 117105506275324218846706, 122379228629698430535449, 122379228629698430535449, 117105506275324218846706, 6411123146532126940033, 6416977481649752524710, 6422842050058525298780, 6428716823752621941272, 6434601774779850352506, 6440496875241847363286,
  104169868964110730516095, 104159881432344190240955, 104149893902970443688522, 104139906375990179300869, 104129918851404085784025, 104119931329212852108108, 104109943809417167507448, 104099956292017721480716, 104089968777015203791048, 104079981264410304466173, 104069993754203713798543, 104060006246396122345452,
  104050018740988220929171, 104040031237980700637071, 104030043737374252821750, 104020056239169569101164, 104010068743367341358747, 104000081249968261743545, 0, 0, 9029728678094375610650, 5159844958911071777514, 5159844958911071777514, 9029728678094375610650,
  124856027487662765219115, 114461118289137818470370, 122379228629698430535449, 117105506275324218846706, 117105506275324218846706, 122379228629698430535449, 6411123146532126940033, 6416977481649752524710, 6422842050058525298780, 6428716823752621941272, 6434601774779850352506, 6440496875241847363286,
  104169868964110730516095, 104159881432344190240955, 104149893902970443688522, 104139906375990179300869, 104129918851404085784025, 104119931329212852108108, 104109943809417167507448, 104099956292017721480716, 104089968777015203791048, 104079981264410304466173, 104069993754203713798543, 104060006246396122345452,
  104050018740988220929171, 104040031237980700637071, 104030043737374252821750, 104020056239169569101164, 104010068743367341358747, 104000081249968261743545, 0, 0, 0, 10400000000000000000000, 5280000000000000000000, 8960000000000000000000,
  117105506275324218846706, 122379228629698430535449, 114461118289137818470370, 124856027487662765219115, 117228626196846647171533, 122261295592677243639263, 6411123146532126940033, 6416977481649752524710, 6422842050058525298780, 6428716823752621941272, 6434601774779850352506, 6440496875241847363286,
  104169868964110730516095, 104159881432344190240955, 104149893902970443688522, 104139906375990179300869, 104129918851404085784025, 104119931329212852108108, 104109943809417167507448, 104099956292017721480716, 104089968777015203791048, 104079981264410304466173, 104069993754203713798543, 104060006246396122345452,
  104050018740988220929171, 104040031237980700637071, 104030043737374252821750, 104020056239169569101164, 104010068743367341358747, 104000081249968261743545, 0, 0, 0, 0, 8960000000000000000000, 5280000000000000000000,
  122379228629698430535449, 117105506275324218846706, 124856027487662765219115, 114461118289137818470370, 122261295592677243639263, 117228626196846647171533, 6411123146532126940033, 6416977481649752524710, 6422842050058525298780, 6428716823752621941272, 6434601774779850352506, 6440496875241847363286,
  104169868964110730516095, 104159881432344190240955, 104149893902970443688522, 104139906375990179300869, 104129918851404085784025, 104119931329212852108108, 104109943809417167507448, 104099956292017721480716, 104089968777015203791048, 104079981264410304466173, 104069993754203713798543, 104060006246396122345452,
  104050018740988220929171, 104040031237980700637071, 104030043737374252821750, 104020056239169569101164, 104010068743367341358747, 104000081249968261743545, 0, 0, 0, 0, 0, 10400000000000000000000,
  122379228629698430535449, 117105506275324218846706, 117228626196846647171533, 122261295592677243639263, 114461118289137818470370, 124856027487662765219115, 6411123146532126940033, 6416977481649752524710, 6422842050058525298780, 6428716823752621941272, 6434601774779850352506, 6440496875241847363286,
  104169868964110730516095, 104159881432344190240955, 104149893902970443688522, 104139906375990179300869, 104129918851404085784025, 104119931329212852108108, 104109943809417167507448, 104099956292017721480716, 104089968777015203791048, 104079981264410304466173, 104069993754203713798543, 104060006246396122345452,
  104050018740988220929171, 104040031237980700637071, 104030043737374252821750, 104020056239169569101164, 104010068743367341358747, 104000081249968261743545, 0, 0, 0, 0, 0, 0,
  117105506275324218846706, 122379228629698430535449, 122261295592677243639263, 117228626196846647171533, 124856027487662765219115, 114461118289137818470370, 6411123146532126940033, 6416977481649752524710, 6422842050058525298780, 6428716823752621941272, 6434601774779850352506, 6440496875241847363286,
  160999032295228408307573, 160992338016441018453094, 160985644080458304696804, 160978950487323031248856, 160972257237077967241877, 160965564329765886731072, 160958871765429568694345, 160952179544111797032404, 160945487665855360568875, 160938796130703053050417, 160932104938697673146828, 160925414089882024451157,
  160918723584298915479818, 160912033421991159672699, 160905343603001575393270, 160898654127372985928695, 160891964995148219489943, 160885276206370109211893, 0, 0, 0, 0, 0, 0,
  0, 239200000000000000000000, 118676434054954650882836, 207683759596170639044963, 207683759596170639044963, 118676434054954650882836, 119600000418060199938234, 119600001672240790984994, 119600003762541746836453, 119600006688963023652899, 119600010451504560058747, 119600015050166277142537,
  160999032295228408307573, 160992338016441018453094, 160985644080458304696804, 160978950487323031248856, 160972257237077967241877, 160965564329765886731072, 160958871765429568694345, 160952179544111797032404, 160945487665855360568875, 160938796130703053050417, 160932104938697673146828, 160925414089882024451157,
  160918723584298915479818, 160912033421991159672699, 160905343603001575393270, 160898654127372985928695, 160891964995148219489943, 160885276206370109211893, 0, 0, 0, 0, 0, 0,
  0, 0, 207683759596170639044963, 118676434054954650882836, 118676434054954650882836, 207683759596170639044963, 119600000418060199938234, 119600001672240790984994, 119600003762541746836453, 119600006688963023652899, 119600010451504560058747, 119600015050166277142537,
  160999032295228408307573, 160992338016441018453094, 160985644080458304696804, 160978950487323031248856, 160972257237077967241877, 160965564329765886731072, 160958871765429568694345, 160952179544111797032404, 160945487665855360568875, 160938796130703053050417, 160932104938697673146828, 160925414089882024451157,
  160918723584298915479818, 160912033421991159672699, 160905343603001575393270, 160898654127372985928695, 160891964995148219489943, 160885276206370109211893, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 239200000000000000000000, 121440000000000000000000, 206080000000000000000000, 119600000418060199938234, 119600001672240790984994, 119600003762541746836453, 119600006688963023652899, 119600010451504560058747, 119600015050166277142537,
  160999032295228408307573, 160992338016441018453094, 160985644080458304696804, 160978950487323031248856, 160972257237077967241877, 160965564329765886731072, 160958871765429568694345, 160952179544111797032404, 160945487665855360568875, 160938796130703053050417, 160932104938697673146828, 160925414089882024451157,
  160918723584298915479818, 160912033421991159672699, 160905343603001575393270, 160898654127372985928695, 160891964995148219489943, 160885276206370109211893, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 206080000000000000000000, 121440000000000000000000, 119600000418060199938234, 119600001672240790984994, 119600003762541746836453, 119600006688963023652899, 119600010451504560058747, 119600015050166277142537,
  160999032295228408307573, 160992338016441018453094, 160985644080458304696804, 160978950487323031248856, 160972257237077967241877, 160965564329765886731072, 160958871765429568694345, 160952179544111797032404, 160945487665855360568875, 160938796130703053050417, 160932104938697673146828, 160925414089882024451157,
  160918723584298915479818, 160912033421991159672699, 160905343603001575393270, 160898654127372985928695, 160891964995148219489943, 160885276206370109211893, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 239200000000000000000000, 119600000418060199938234, 119600001672240790984994, 119600003762541746836453, 119600006688963023652899, 119600010451504560058747, 119600015050166277142537,
  160999032295228408307573, 160992338016441018453094, 160985644080458304696804, 160978950487323031248856, 160972257237077967241877, 160965564329765886731072, 160958871765429568694345, 160952179544111797032404, 160945487665855360568875, 160938796130703053050417, 160932104938697673146828, 160925414089882024451157,
  160918723584298915479818, 160912033421991159672699, 160905343603001575393270, 160898654127372985928695, 160891964995148219489943, 160885276206370109211893, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 119600000418060199938234, 119600001672240790984994, 119600003762541746836453, 119600006688963023652899, 119600010451504560058747, 119600015050166277142537]

private def mat6ELit10 : List (List CFpIv) := [
  [⟨⟨7776910414954046233, 7776910414954650381⟩, ⟨-301955, 301914⟩⟩, ⟨⟨50404502681390746806, 50404502681391495574⟩, ⟨-374260, 374438⟩⟩, ⟨⟨99247734683930639274, 99247734683931578482⟩, ⟨-469405, 469437⟩⟩, ⟨⟨6883252770988441120, 6883252770989384786⟩, ⟨-471456, 471450⟩⟩, ⟨⟨-41015248000989422523, -41015248000988884281⟩, ⟨-269152, 269086⟩⟩, ⟨⟨-83652282947648170376, -83652282947648001988⟩, ⟨-84000, 84053⟩⟩],
  [⟨⟨-6713093979178444382, -6713093979174259123⟩, ⟨-3959864564560078276, -3959864564555892998⟩⟩, ⟨⟨44304762812184598863, 44304762812189714818⟩, ⟨-25290030051081882096, -25290030051076766171⟩⟩, ⟨⟨-519989644715520355, -519989644709859562⟩, ⟨100863709053417705123, 100863709053423365912⟩⟩, ⟨⟨-6127974893691480219, -6127974893686687242⟩, ⟨-7376244655814907133, -7376244655810114217⟩⟩, ⟨⟨-37639242399560879269, -37639242399558474381⟩, ⟨24548632634063990906, 24548632634066395877⟩⟩, ⟨⟨-974019897210292715, -974019897209651818⟩, ⟨-83403582200460476809, -83403582200459835914⟩⟩],
  [⟨⟨-3959864564560074410, -3959864564555896916⟩, ⟨-6713093979178440445, -6713093979174262970⟩⟩, ⟨⟨-25290030051081875381, -25290030051076772453⟩, ⟨44304762812184605302, 44304762812189708251⟩⟩, ⟨⟨100863709053417711231, 100863709053423359901⟩, ⟨-519989644715514356, -519989644709865686⟩⟩, ⟨⟨-7376244655814907382, -7376244655810114070⟩, ⟨-6127974893691480399, -6127974893686687039⟩⟩, ⟨⟨24548632634063988251, 24548632634066398496⟩, ⟨-37639242399560881839, -37639242399558471652⟩⟩, ⟨⟨-83403582200460476700, -83403582200459835963⟩, ⟨-974019897210292713, -974019897209651967⟩⟩],
  [⟨⟨5007578059394214698409948, 5007578059394215106739319⟩, ⟨-187804104, 187361668⟩⟩, ⟨⟨8091014254499929474181594, 8091014254499930179450967⟩, ⟨-337489082, 337805062⟩⟩, ⟨⟨8273327003852720730207135, 8273327003852721447387018⟩, ⟨-345543877, 346422290⟩⟩, ⟨⟨5260055891496008917662654, 5260055891496009360804493⟩, ⟨-211909782, 214429608⟩⟩, ⟨⟨1965429052844864125170183, 1965429052844864283934700⟩, ⟨-72679307, 76161198⟩⟩, ⟨⟨417437843599414769577952, 417437843599414796871119⟩, ⟨-11766640, 11718838⟩⟩],
  [⟨⟨-4143685458838793567330952, -4143685458838781709439929⟩, ⟨-2799310468998025122865649, -2799310468998013252980393⟩⟩, ⟨⟨7242955793288621984498787, 7242955793288634070910608⟩, ⟨-3652351345403831712622137, -3652351345403819629012639⟩⟩, ⟨⟨-339854809631456366701173, -339854809631448351001815⟩, ⟨8284581152601828414181155, 8284581152601836426025278⟩⟩, ⟨⟨-4497721670557225611409570, -4497721670557222299854057⟩, ⟨-2747686044667526751825443, -2747686044667523444724247⟩⟩, ⟨⟨1717002663049344895935120, 1717002663049345716107833⟩, ⟨-968417389526105874266190, -968417389526105052488405⟩⟩, ⟨⟨1038992210820406300716, 1038992210820514277906⟩, ⟨415568903242908782078355, 415568903242908891817369⟩⟩],
  [⟨⟨-2799310468998025123564415, -2799310468998013248850546⟩, ⟨-4143685458838793569028717, -4143685458838781706402659⟩⟩, ⟨⟨-3652351345403831716754841, -3652351345403819627758499⟩, ⟨7242955793288621980686976, 7242955793288634072195802⟩⟩, ⟨⟨8284581152601828415114138, 8284581152601836428232629⟩, ⟨-339854809631456363654506, -339854809631448346631859⟩⟩, ⟨⟨-2747686044667526750431673, -2747686044667523446425585⟩, ⟨-4497721670557225609637381, -4497721670557222301046205⟩⟩, ⟨⟨-968417389526105872686479, -968417389526105053608602⟩, ⟨1717002663049344901883084, 1717002663049345719353388⟩⟩, ⟨⟨415568903242908782808332, 415568903242908891451231⟩, ⟨1038992210820406920034, 1038992210820513795391⟩⟩]]

private def mat6OLit10 : List (List CFpIv) := [
  [⟨⟨-22797181502580710244, -22797181502580047410⟩, ⟨-331301, 331276⟩⟩, ⟨⟨-81984344358690237597, -81984344358689434756⟩, ⟨-401324, 401344⟩⟩, ⟨⟨-88497812098006899012, -88497812098005996776⟩, ⟨-450835, 450870⟩⟩, ⟨⟨13263540473882659144, 13263540473883378542⟩, ⟨-359557, 359505⟩⟩, ⟨⟨69650543411071272474, 69650543411071591874⟩, ⟨-159575, 159639⟩⟩, ⟨⟨71979879296357353699, 71979879296357426534⟩, ⟨-36262, 36244⟩⟩],
  [⟨⟨-149399001852642708, -149399001847985524⟩, ⟨22888932591993611354, 22888932591998268598⟩⟩, ⟨⟨-72035831675000160518, -72035831674994725103⟩, ⟨-41688286946440234222, -41688286946434798751⟩⟩, ⟨⟨79361163271355303877, 79361163271360626650⟩, ⟨-44636293538599307760, -44636293538593984919⟩⟩, ⟨⟨-3830269777139352518, -3830269777135789859⟩, ⟨-12857638032216587971, -12857638032213025290⟩⟩, ⟨⟨64713651530108426290, 64713651530109763820⟩, ⟨34244855256930347182, 34244855256931684656⟩⟩, ⟨⟨-61643656146030851302, -61643656146030601565⟩, ⟨37165681226447906516, 37165681226448156256⟩⟩],
  [⟨⟨-22888932591998263620, -22888932591993616287⟩, ⟨149399001847990491, 149399001852637768⟩⟩, ⟨⟨41688286946434806076, 41688286946440226993⟩, ⟨72035831674994732362, 72035831675000153229⟩⟩, ⟨⟨44636293538593987780, 44636293538599304879⟩, ⟨-79361163271360623828, -79361163271355306776⟩⟩, ⟨⟨12857638032213022675, 12857638032216590522⟩, ⟨3830269777135787252, 3830269777139355069⟩⟩, ⟨⟨-34244855256931685900, -34244855256930345838⟩, ⟨-64713651530109765067, -64713651530108424962⟩⟩, ⟨⟨-37165681226448155654, -37165681226447907212⟩, ⟨61643656146030602218, 61643656146030850653⟩⟩],
  [⟨⟨-6750839462556539950208937, -6750839462556539327001070⟩, ⟨-291536232, 288231402⟩⟩, ⟨⟨-8670175698550767231275417, -8670175698550766272622973⟩, ⟨-466362697, 463281792⟩⟩, ⟨⟨-7006798843552365525004624, -7006798843552364706456828⟩, ⟨-394814401, 398115264⟩⟩, ⟨⟨-3435770481878430051974691, -3435770481878429649826758⟩, ⟨-195213704, 201881731⟩⟩, ⟨⟨-976359123861371497151837, -976359123861371356195630⟩, ⟨-66318418, 66298414⟩⟩, ⟨⟨-149895183535471587228359, -149895183535471565514311⟩, ⟨-8855046, 12173711⟩⟩],
  [⟨⟨-417024629401207851942900, -417024629401195085096008⟩, ⟨6723488637812331507858891, 6723488637812344266057263⟩⟩, ⟨⟨-7310385586172091348049880, -7310385586172080597323595⟩, ⟨-4707456868849563631932779, -4707456868849552880272195⟩⟩, ⟨⟨6194148657893098027406961, 6194148657893103881609102⟩, ⟨-3306834513519827810896766, -3306834513519821956873204⟩⟩, ⟨⟨-59151807399249570463575, -59151807399247632397917⟩, ⟨3441909847081456388077295, 3441909847081458329475620⟩⟩, ⟨⟨-846510602767471182044951, -846510602767470762785824⟩, ⟨-490867819644441378898243, -490867819644440961458261⟩⟩, ⟨⟨128571642847854887810006, 128571642847854936585642⟩, ⟨-76251228248779158679291, -76251228248779109901703⟩⟩],
  [⟨⟨-6723488637812344264846851, -6723488637812331501163151⟩, ⟨417024629401195082572900, 417024629401207855147606⟩⟩, ⟨⟨4707456868849552874740521, 4707456868849563629978883⟩, ⟨7310385586172080597933993, 7310385586172091352398587⟩⟩, ⟨⟨3306834513519821955878221, 3306834513519827808827245⟩, ⟨-6194148657893103882776068, -6194148657893098029810635⟩⟩, ⟨⟨-3441909847081458334876849, -3441909847081456396724678⟩, ⟨59151807399247630751098, 59151807399249565522999⟩⟩, ⟨⟨490867819644440962527573, 490867819644441378066493⟩, ⟨846510602767470764152348, 846510602767471181521804⟩⟩, ⟨⟨76251228248779107207791, 76251228248779155505645⟩, ⟨-128571642847854937842572, -128571642847854889545279⟩⟩]]

private def prod10Cert : CFpIv := ⟨⟨-4585143774856221395415556107739059029629954086953438783205437550542878, -4585143774050048118690606954353467657150045291166285160626921022843757⟩, ⟨-403073935198555558857316649124684388380817763812430482183479, 403073442683988620326079716327925214981958824214450553231997⟩⟩

def ringSlot (i j : ℕ) : ℕ :=
  if 18 ≤ i then (i - 18) * 36 + j else (j - 18) * 36 + i

def pts36OfSn (sn : ℤ) (i : Fin 36) : Fin 3 → ℤ := fun k =>
  match k.1 with
  | 0 => sn * x36BaseX i
  | 1 => sn * x36BaseY i
  | _ => x36BaseZ i

private lemma x36Clamp_int_coords {sn : ℤ} (hsn : 1 ≤ sn) (i : Fin 36) (k : Fin 3) :
    (x36Clamp (sn : ℝ)).1 i k = ((pts36OfSn sn i k : ℤ) : ℝ) := by
  have hs : (1 : ℝ) ≤ (sn : ℝ) := by exact_mod_cast hsn
  have hmax : max (sn : ℝ) 1 = (sn : ℝ) := max_eq_left hs
  fin_cases k <;> simp [x36Clamp, x36ClampRaw, pts36OfSn, hmax]

def rhoTableOk (pts : Fin 36 → Fin 3 → ℤ) (tbl : List ℤ) : Bool :=
  tbl.length == 432 &&
    (List.finRange 36).all fun i =>
      (List.finRange 36).all fun j =>
        if i < j then
          let dx := pts j 0 - pts i 0
          let dy := pts j 1 - pts i 1
          let dz := pts j 2 - pts i 2
          if dx != 0 || dy != 0 then
            let r := tbl.getD (ringSlot i.1 j.1) 0
            let n2 := S36 * S36 * (dx * dx + dy * dy + dz * dz)
            (0 < r) && (r * r ≤ n2) && (n2 ≤ (r + 1) * (r + 1))
          else true
        else true

private lemma rhoTableOk_spec {pts : Fin 36 → Fin 3 → ℤ} {tbl : List ℤ}
    (hok : rhoTableOk pts tbl = true) {i j : Fin 36} (hij : i < j)
    (hne : pts j 0 - pts i 0 ≠ 0 ∨ pts j 1 - pts i 1 ≠ 0) :
    let r := tbl.getD (ringSlot i.1 j.1) 0
    let dx := pts j 0 - pts i 0
    let dy := pts j 1 - pts i 1
    let dz := pts j 2 - pts i 2
    0 < r ∧ r * r ≤ S36 * S36 * (dx * dx + dy * dy + dz * dz) ∧
      S36 * S36 * (dx * dx + dy * dy + dz * dz) ≤ (r + 1) * (r + 1) := by
  simp only [rhoTableOk, Bool.and_eq_true, List.all_eq_true] at hok
  have hi := hok.2 i (List.mem_finRange i) j (List.mem_finRange j)
  simp only [hij, ↓reduceIte] at hi
  have hcond : (pts j 0 - pts i 0 != 0 || pts j 1 - pts i 1 != 0) = true := by
    rcases hne with h | h <;> simp [h]
  simp only [hcond, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hi
  exact ⟨hi.1.1, hi.1.2, hi.2⟩

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
private lemma rho9_ok : rhoTableOk (pts36OfSn 9) rho9List = true := by decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
private lemma rho10_ok : rhoTableOk (pts36OfSn 10) rho10List = true := by decide

def mkWEntry (pts : Fin 36 → Fin 3 → ℤ) (tbl : List ℤ) (i j : Fin 36) : CFpIv :=
  if j ≤ i then CFpIv.zero
  else
    let dx := pts j 0 - pts i 0
    let dy := pts j 1 - pts i 1
    let dz := pts j 2 - pts i 2
    if dx = 0 ∧ dy = 0 then CFpIv.zero
    else CFpIv.cslopeIv S36 dx dy dz (tbl.getD (ringSlot i.1 j.1) 0)

private lemma mkWEntry_mem {sn : ℤ} (hsn : 1 ≤ sn) {tbl : List ℤ}
    (hok : rhoTableOk (pts36OfSn sn) tbl = true) (i j : Fin 36) (hij : i < j) :
    CFpIv.CFpMem S36 (mkWEntry (pts36OfSn sn) tbl i j) (stereoSlope (x36Clamp (sn : ℝ)).1 i j) := by
  have hnot_ji : ¬ j ≤ i := not_le_of_gt hij
  have hc0i := x36Clamp_int_coords hsn i 0
  have hc0j := x36Clamp_int_coords hsn j 0
  have hc1i := x36Clamp_int_coords hsn i 1
  have hc1j := x36Clamp_int_coords hsn j 1
  have hc2i := x36Clamp_int_coords hsn i 2
  have hc2j := x36Clamp_int_coords hsn j 2
  set dx := pts36OfSn sn j 0 - pts36OfSn sn i 0
  set dy := pts36OfSn sn j 1 - pts36OfSn sn i 1
  set dz := pts36OfSn sn j 2 - pts36OfSn sn i 2
  have hdz_nn : 0 ≤ dz := by
    have hz := x36BaseZ_monotone hij.le
    change 0 ≤ x36BaseZ j - x36BaseZ i
    omega
  by_cases hxy : dx = 0 ∧ dy = 0
  · have hif : mkWEntry (pts36OfSn sn) tbl i j = CFpIv.zero := by
      change (if j ≤ i then CFpIv.zero else if dx = 0 ∧ dy = 0 then CFpIv.zero
        else CFpIv.cslopeIv S36 dx dy dz (tbl.getD (ringSlot i.1 j.1) 0)) = CFpIv.zero
      simp only [hnot_ji, hxy, and_self, ↓reduceIte]
    rw [hif]
    have hdx0 : (x36Clamp (sn : ℝ)).1 j 0 - (x36Clamp (sn : ℝ)).1 i 0 = 0 := by
      rw [hc0i, hc0j]; exact_mod_cast hxy.1
    have hdy0 : (x36Clamp (sn : ℝ)).1 j 1 - (x36Clamp (sn : ℝ)).1 i 1 = 0 := by
      rw [hc1i, hc1j]; exact_mod_cast hxy.2
    have hslope0 : stereoSlope (x36Clamp (sn : ℝ)).1 i j = 0 := by
      unfold stereoSlope; rw [hdx0, hdy0]; simp
    rw [hslope0]
    exact CFpIv.zero_mem S36
  · have hif : mkWEntry (pts36OfSn sn) tbl i j =
        CFpIv.cslopeIv S36 dx dy dz (tbl.getD (ringSlot i.1 j.1) 0) := by
      change (if j ≤ i then CFpIv.zero else if dx = 0 ∧ dy = 0 then CFpIv.zero
        else CFpIv.cslopeIv S36 dx dy dz (tbl.getD (ringSlot i.1 j.1) 0)) = _
      simp only [hnot_ji, hxy, ↓reduceIte]
    rw [hif]
    have hne : dx ≠ 0 ∨ dy ≠ 0 := not_and_or.mp hxy
    have hspec := rhoTableOk_spec hok hij hne
    have hrb := sqrt_rho_bounds S36_pos hspec.1 hspec.2.1 hspec.2.2
    have hcmem := @CFpIv.cslopeIv_mem S36 dx dy dz (tbl.getD (ringSlot i.1 j.1) 0)
      (Real.sqrt ((dx : ℝ) ^ 2 + (dy : ℝ) ^ 2 + (dz : ℝ) ^ 2)) S36_pos hdz_nn hspec.1 hrb
    have heuclid :
        euclidNorm (fun k => (x36Clamp (sn : ℝ)).1 j k - (x36Clamp (sn : ℝ)).1 i k) =
          Real.sqrt ((dx : ℝ) ^ 2 + (dy : ℝ) ^ 2 + (dz : ℝ) ^ 2) := by
      unfold euclidNorm
      dsimp only
      rw [hc0i, hc0j, hc1i, hc1j, hc2i, hc2j]
      simp [dx, dy, dz, Int.cast_sub]
    have hsl_eq :
        stereoSlope (x36Clamp (sn : ℝ)).1 i j =
          (((dx : ℂ) + Complex.I * (dy : ℂ)) /
            ((dz : ℂ) + (Real.sqrt ((dx : ℝ) ^ 2 + (dy : ℝ) ^ 2 + (dz : ℝ) ^ 2) : ℂ))) := by
      unfold stereoSlope stereoDenomR
      rw [heuclid, hc0i, hc0j, hc1i, hc1j, hc2i, hc2j]
      simp [dx, dy, dz, Int.cast_sub]
    rw [hsl_eq]
    exact hcmem

def wRowsOf (pts : Fin 36 → Fin 3 → ℤ) (tbl : List ℤ) : List (List CFpIv) :=
  memoFin [] fun i : Fin 36 => memoFin CFpIv.zero fun j : Fin 36 => mkWEntry pts tbl i j

def wRead (ws : List (List CFpIv)) (i j : Fin 36) : CFpIv :=
  readMemo CFpIv.zero (readMemo [] ws i) j

private lemma wRead_wRowsOf (pts : Fin 36 → Fin 3 → ℤ) (tbl : List ℤ) (i j : Fin 36) :
    wRead (wRowsOf pts tbl) i j = mkWEntry pts tbl i j := by
  simp [wRead, wRowsOf, readMemo_memoFin]

def elimRow18CIv (S : ℤ) (M18 : List (List CFpIv)) (curRow : List CFpIv) (r : ℕ) : List CFpIv :=
  let piv := curRow.getD r CFpIv.zero
  let mRow := M18.getD r []
  (List.range 18).map fun c =>
    CFpIv.sub (curRow.getD c CFpIv.zero) (CFpIv.mul S piv (mRow.getD c CFpIv.zero))

def pivIdxSchedule : List ℕ :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 17, 16, 15]

def reduce18To6ListCIv (S : ℤ) (M18 : List (List CFpIv)) : List (List CFpIv) :=
  (List.range 6).map fun q =>
    let cur := pivIdxSchedule.foldl (elimRow18CIv S M18) (M18.getD (9 + q) [])
    (List.range 6).map fun c => cur.getD (9 + c) CFpIv.zero

private lemma elimRow18CIv_mem {S : ℤ} (hS : 0 < S)
    {M18Iv : List (List CFpIv)} {M18 : Fin 18 → Fin 18 → ℂ}
    (hM : ∀ r c : Fin 18, CFpIv.CFpMem S ((M18Iv.getD r.1 []).getD c.1 CFpIv.zero) (M18 r c))
    {curIv : List CFpIv} {cur : Fin 18 → ℂ}
    (hcur : ∀ c : Fin 18, CFpIv.CFpMem S (curIv.getD c.1 CFpIv.zero) (cur c))
    (r : Fin 18) (c : Fin 18) :
    CFpIv.CFpMem S ((elimRow18CIv S M18Iv curIv r.1).getD c.1 CFpIv.zero)
      (elimRow18C M18 cur r c) := by
  unfold elimRow18CIv elimRow18C
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range c.2]
  dsimp
  exact CFpIv.sub_mem (hcur c) (CFpIv.mul_mem hS (hcur r) (hM r c))

private lemma foldl_elim18CIv_mem {S : ℤ} (hS : 0 < S)
    {M18Iv : List (List CFpIv)} {M18 : Fin 18 → Fin 18 → ℂ}
    (hM : ∀ r c : Fin 18, CFpIv.CFpMem S ((M18Iv.getD r.1 []).getD c.1 CFpIv.zero) (M18 r c)) :
    ∀ (ns : List ℕ) (rs : List (Fin 18)) (_hfor : List.Forall₂ (fun n (r : Fin 18) => n = r.1) ns rs)
      (curIv : List CFpIv) (cur : Fin 18 → ℂ)
      (_hcur : ∀ c : Fin 18, CFpIv.CFpMem S (curIv.getD c.1 CFpIv.zero) (cur c)),
      ∀ c : Fin 18,
        CFpIv.CFpMem S ((ns.foldl (elimRow18CIv S M18Iv) curIv).getD c.1 CFpIv.zero)
          ((rs.foldl (elimRow18C M18) cur) c)
  | [], [], .nil, _, _, hcur, c => hcur c
  | n :: ns, r :: rs, .cons hnr htl, curIv, cur, hcur, c => by
    simp only [List.foldl_cons]
    refine foldl_elim18CIv_mem hS hM ns rs htl _ _ ?_ c
    intro c'
    rw [hnr]
    exact elimRow18CIv_mem hS hM hcur r c'

lemma reduce18To6ListCIv_mem {S : ℤ} (hS : 0 < S)
    {M18Iv : List (List CFpIv)} {M18 : Matrix (Fin 18) (Fin 18) ℂ}
    (hM : ∀ r c : Fin 18, CFpIv.CFpMem S ((M18Iv.getD r.1 []).getD c.1 CFpIv.zero) (M18 r c))
    (q c : Fin 6) :
    CFpIv.CFpMem S
      (((reduce18To6ListCIv S M18Iv).getD q.1 []).getD c.1 CFpIv.zero)
      (reduce18To6C M18 q c) := by
  have hfor : List.Forall₂ (fun n (r : Fin 18) => n = r.1) pivIdxSchedule pivFinSchedule := by
    unfold pivIdxSchedule pivFinSchedule
    exact .cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl
      (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl (.cons rfl .nil)))))))))))
  have hinit : ∀ c' : Fin 18,
      CFpIv.CFpMem S ((M18Iv.getD (9 + q.1) []).getD c'.1 CFpIv.zero)
        (M18 ⟨9 + q.1, by omega⟩ c') := fun c' => hM ⟨9 + q.1, by omega⟩ c'
  have hfold := foldl_elim18CIv_mem hS hM pivIdxSchedule pivFinSchedule hfor
    (M18Iv.getD (9 + q.1) []) (fun c' => M18 ⟨9 + q.1, by omega⟩ c') hinit ⟨9 + c.1, by omega⟩
  dsimp only [reduce18To6ListCIv, reduce18To6C, elimSchedule18C]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range q.2,
    List.getElem?_range c.2, Option.map_some, Option.getD_some]
  exact hfold

def polyRowsOf (ws : List (List CFpIv)) : List (List CFpIv) :=
  memoFin [] fun i : Fin 36 => polyListCIv S36 (wRead ws) i

def mkMat18EvenIv (rows : List (List CFpIv)) : List (List CFpIv) :=
  (List.finRange 18).map fun r =>
    let row := readMemo [] rows (evenSrcRow r)
    (List.finRange 18).map fun c => row.getD (2 * c.1) CFpIv.zero

def mkMat18OddIv (rows : List (List CFpIv)) : List (List CFpIv) :=
  (List.finRange 18).map fun r =>
    let row := readMemo [] rows (oddSrcRow r)
    (List.finRange 18).map fun c => row.getD (2 * c.1 + 1) CFpIv.zero

def extractEven18 : ℕ → List CFpIv → List CFpIv
  | 0, _ => []
  | k + 1, a :: _ :: rest => a :: extractEven18 k rest
  | k + 1, [a] => a :: List.replicate k CFpIv.zero
  | k + 1, [] => List.replicate (k + 1) CFpIv.zero

def extractOdd18 : ℕ → List CFpIv → List CFpIv
  | 0, _ => []
  | k + 1, _ :: b :: rest => b :: extractOdd18 k rest
  | k + 1, [_] => List.replicate (k + 1) CFpIv.zero
  | k + 1, [] => List.replicate (k + 1) CFpIv.zero

private lemma getD_extractEven18 : ∀ (k : ℕ) (xs : List CFpIv) (c : ℕ), c < k →
    (extractEven18 k xs).getD c CFpIv.zero = xs.getD (2 * c) CFpIv.zero
  | 0, _, _, hc => by omega
  | k + 1, [], c, hc => by
    simp [extractEven18, List.getD_eq_getElem?_getD, hc]
  | k + 1, [_], 0, _ => by simp [extractEven18]
  | k + 1, [_], c + 1, hc => by
    have hc' : c < k := by omega
    rw [show 2 * (c + 1) = (2 * c + 1) + 1 by omega]
    simp [extractEven18, List.getD_eq_getElem?_getD, hc']
  | k + 1, _ :: _ :: _, 0, _ => by simp [extractEven18]
  | k + 1, _ :: _ :: rest, c + 1, hc => by
    have ih := getD_extractEven18 k rest c (by omega)
    rw [show 2 * (c + 1) = (2 * c + 1) + 1 by omega]
    simpa [extractEven18, List.getD_cons_succ] using ih

private lemma length_extractEven18 : ∀ (k : ℕ) (xs : List CFpIv),
    (extractEven18 k xs).length = k
  | 0, _ => rfl
  | k + 1, [] => by simp [extractEven18]
  | k + 1, [_] => by simp [extractEven18]
  | k + 1, _ :: _ :: rest => by simp [extractEven18, length_extractEven18 k rest]

private lemma getD_extractOdd18 : ∀ (k : ℕ) (xs : List CFpIv) (c : ℕ), c < k →
    (extractOdd18 k xs).getD c CFpIv.zero = xs.getD (2 * c + 1) CFpIv.zero
  | 0, _, _, hc => by omega
  | k + 1, [], c, hc => by
    simp [extractOdd18, List.getD_eq_getElem?_getD, hc]
  | k + 1, [_], c, hc => by
    rw [show 2 * c + 1 = (2 * c) + 1 by omega]
    simp [extractOdd18, List.getD_eq_getElem?_getD, hc]
  | k + 1, _ :: _ :: _, 0, _ => by simp [extractOdd18]
  | k + 1, _ :: _ :: rest, c + 1, hc => by
    have ih := getD_extractOdd18 k rest c (by omega)
    rw [show 2 * (c + 1) + 1 = (2 * c + 1) + 1 + 1 by omega]
    simpa [extractOdd18, List.getD_cons_succ] using ih

private lemma length_extractOdd18 : ∀ (k : ℕ) (xs : List CFpIv),
    (extractOdd18 k xs).length = k
  | 0, _ => rfl
  | k + 1, [] => by simp [extractOdd18]
  | k + 1, [_] => by simp [extractOdd18]
  | k + 1, _ :: _ :: rest => by simp [extractOdd18, length_extractOdd18 k rest]

def mkMat18EvenFast (ws : List (List CFpIv)) : List (List CFpIv) :=
  (List.finRange 18).map fun r =>
    extractEven18 18 (polyListCIv S36 (wRead ws) (evenSrcRow r))

def mkMat18OddFast (ws : List (List CFpIv)) : List (List CFpIv) :=
  (List.finRange 18).map fun r =>
    extractOdd18 18 (polyListCIv S36 (wRead ws) (oddSrcRow r))

private lemma map_extractEven18 (xs : List CFpIv) :
    ((List.finRange 18).map fun c => xs.getD (2 * c.1) CFpIv.zero) = extractEven18 18 xs := by
  refine List.ext_getElem (by simp [length_extractEven18]) fun i hi1 hi2 => ?_
  have hi18 : i < 18 := by simpa using hi1
  simp only [List.getElem_map, List.getElem_finRange]
  have hget := getD_extractEven18 18 xs i hi18
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi2, Option.getD_some] at hget
  exact hget.symm

private lemma map_extractOdd18 (xs : List CFpIv) :
    ((List.finRange 18).map fun c => xs.getD (2 * c.1 + 1) CFpIv.zero) = extractOdd18 18 xs := by
  refine List.ext_getElem (by simp [length_extractOdd18]) fun i hi1 hi2 => ?_
  have hi18 : i < 18 := by simpa using hi1
  simp only [List.getElem_map, List.getElem_finRange]
  have hget := getD_extractOdd18 18 xs i hi18
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi2, Option.getD_some] at hget
  exact hget.symm

private lemma mkMat18EvenIv_polyRowsOf (ws : List (List CFpIv)) :
    mkMat18EvenIv (polyRowsOf ws) = mkMat18EvenFast ws := by
  unfold mkMat18EvenIv mkMat18EvenFast polyRowsOf
  refine List.map_congr_left fun r _ => ?_
  rw [readMemo_memoFin]
  exact map_extractEven18 _

private lemma mkMat18OddIv_polyRowsOf (ws : List (List CFpIv)) :
    mkMat18OddIv (polyRowsOf ws) = mkMat18OddFast ws := by
  unfold mkMat18OddIv mkMat18OddFast polyRowsOf
  refine List.map_congr_left fun r _ => ?_
  rw [readMemo_memoFin]
  exact map_extractOdd18 _

def stepFactorCIv (S : ℤ) (ivs : List CFpIv) (f : CFpIv × CFpIv) : List CFpIv :=
  mulLinListCIv S f.1 f.2 ivs

def rowFactorsCIv (S : ℤ) (ws : List (List CFpIv)) (i : Fin 36) : List (CFpIv × CFpIv) :=
  (List.finRange 36).filterMap fun j =>
    if j = i then none
    else if j < i then some (CFpIv.neg (CFpIv.conj (wRead ws j i)), CFpIv.ofInt S 1)
    else some (CFpIv.ofInt S 1, wRead ws i j)

def evalFactorsCIv (S : ℤ) (fs : List (CFpIv × CFpIv)) : List CFpIv :=
  fs.foldl (stepFactorCIv S) [CFpIv.ofInt S 1]

private lemma foldl_stepPolyCIv_eq_filterMap (S : ℤ) (ws : List (List CFpIv)) (i : Fin 36) :
    ∀ (l : List (Fin 36)) (ivs : List CFpIv),
      l.foldl (stepPolyCIv S (wRead ws) i) ivs =
        (l.filterMap fun j =>
          if j = i then none
          else if j < i then some (CFpIv.neg (CFpIv.conj (wRead ws j i)), CFpIv.ofInt S 1)
          else some (CFpIv.ofInt S 1, wRead ws i j)).foldl (stepFactorCIv S) ivs := by
  intro l
  induction l with
  | nil => intro ivs; rfl
  | cons j js ih =>
    intro ivs
    dsimp only [List.foldl_cons, stepPolyCIv, stepFactorCIv]
    by_cases hji : j = i
    · simp only [hji, ↓reduceIte, List.filterMap]
      exact ih ivs
    · by_cases hlt : j < i
      · simp only [hji, hlt, ↓reduceIte, List.filterMap, List.foldl_cons]
        exact ih _
      · simp only [hji, hlt, ↓reduceIte, List.filterMap, List.foldl_cons]
        exact ih _

private lemma polyListCIv_eq_evalFactorsCIv (S : ℤ) (ws : List (List CFpIv)) (i : Fin 36) :
    polyListCIv S (wRead ws) i = evalFactorsCIv S (rowFactorsCIv S ws i) :=
  foldl_stepPolyCIv_eq_filterMap S ws i (List.finRange 36) [CFpIv.ofInt S 1]

private lemma getD_map_finRange {α : Type*} {n : ℕ} (d : α) (f : Fin n → α) (c : Fin n) :
    ((List.finRange n).map f).getD c.1 d = f c := by
  simp [List.getD_eq_getElem?_getD, List.getElem_finRange]

def isActiveSrc36 (i : Fin 36) : Bool :=
  decide (i.1 < 18 ∨ 30 ≤ i.1 ∨ i.1 % 2 = 0)

private lemma isActiveSrc36_evenSrcRow : ∀ r : Fin 18, isActiveSrc36 (evenSrcRow r) = true := by
  decide

private lemma isActiveSrc36_oddSrcRow : ∀ r : Fin 18, isActiveSrc36 (oddSrcRow r) = true := by
  decide

def activeRowFactors36 (ws : List (List CFpIv)) : List (List (CFpIv × CFpIv)) :=
  (List.finRange 36).map fun i => if isActiveSrc36 i then rowFactorsCIv S36 ws i else []

def mkEvenFromRows36 (rows36 : List (List CFpIv)) : List (List CFpIv) :=
  (List.finRange 18).map fun r => extractEven18 18 (rows36.getD (evenSrcRow r).1 [])

def mkOddFromRows36 (rows36 : List (List CFpIv)) : List (List CFpIv) :=
  (List.finRange 18).map fun r => extractOdd18 18 (rows36.getD (oddSrcRow r).1 [])

private lemma mkMat18EvenFast_eq_active (ws : List (List CFpIv)) :
    mkMat18EvenFast ws = mkEvenFromRows36 ((activeRowFactors36 ws).map (evalFactorsCIv S36)) := by
  unfold mkMat18EvenFast mkEvenFromRows36 activeRowFactors36
  rw [List.map_map]
  dsimp only [Function.comp_def]
  refine List.map_congr_left fun r _ => ?_
  rw [getD_map_finRange]
  simp [isActiveSrc36_evenSrcRow r, polyListCIv_eq_evalFactorsCIv]

private lemma mkMat18OddFast_eq_active (ws : List (List CFpIv)) :
    mkMat18OddFast ws = mkOddFromRows36 ((activeRowFactors36 ws).map (evalFactorsCIv S36)) := by
  unfold mkMat18OddFast mkOddFromRows36 activeRowFactors36
  rw [List.map_map]
  dsimp only [Function.comp_def]
  refine List.map_congr_left fun r _ => ?_
  rw [getD_map_finRange]
  simp [isActiveSrc36_oddSrcRow r, polyListCIv_eq_evalFactorsCIv]

private lemma foldl_eq_chunks9 {α β : Type*} (f : β → α → β) (fs : List α) (init : β) :
    fs.foldl f init =
      (fs.drop 32).foldl f
        (((fs.drop 28).take 4).foldl f
          (((fs.drop 24).take 4).foldl f
            (((fs.drop 20).take 4).foldl f
              (((fs.drop 16).take 4).foldl f
                (((fs.drop 12).take 4).foldl f
                  (((fs.drop 8).take 4).foldl f
                    (((fs.drop 4).take 4).foldl f
                      (((fs.drop 0).take 4).foldl f init)))))))) := by
  have hchunk : ∀ (k : ℕ), (fs.drop k).take 4 ++ fs.drop (k + 4) = fs.drop k := by
    intro k
    rw [show fs.drop (k + 4) = (fs.drop k).drop 4 by simp [List.drop_drop],
      List.take_append_drop]
  have hfs : fs = (fs.drop 0).take 4 ++ ((fs.drop 4).take 4 ++
      ((fs.drop 8).take 4 ++ ((fs.drop 12).take 4 ++ ((fs.drop 16).take 4 ++
        ((fs.drop 20).take 4 ++ ((fs.drop 24).take 4 ++
          ((fs.drop 28).take 4 ++ fs.drop 32))))))) := by
    rw [hchunk 28, hchunk 24, hchunk 20, hchunk 16, hchunk 12, hchunk 8, hchunk 4,
      List.drop_zero, List.take_append_drop]
  conv_lhs => rw [hfs]
  simp only [List.foldl_append]

def stepRowsTake (k len : ℕ) (facs : List (List (CFpIv × CFpIv)))
    (curs : List (List CFpIv)) : List (List CFpIv) :=
  List.zipWith (fun fs cur => ((fs.drop k).take len).foldl (stepFactorCIv S36) cur) facs curs

def stepRowsTail (k : ℕ) (facs : List (List (CFpIv × CFpIv)))
    (curs : List (List CFpIv)) : List (List CFpIv) :=
  List.zipWith (fun fs cur => (fs.drop k).foldl (stepFactorCIv S36) cur) facs curs

private lemma map_evalFactorsCIv_eq_stages9 :
    ∀ facs : List (List (CFpIv × CFpIv)),
      facs.map (evalFactorsCIv S36) =
        stepRowsTail 32 facs
          (stepRowsTake 28 4 facs
            (stepRowsTake 24 4 facs
              (stepRowsTake 20 4 facs
                (stepRowsTake 16 4 facs
                  (stepRowsTake 12 4 facs
                    (stepRowsTake 8 4 facs
                      (stepRowsTake 4 4 facs
                        (stepRowsTake 0 4 facs
                          (List.replicate facs.length [CFpIv.ofInt S36 1])))))))))
  | [] => rfl
  | fs :: rest => by
    have ih := map_evalFactorsCIv_eq_stages9 rest
    unfold evalFactorsCIv stepRowsTake stepRowsTail at ih ⊢
    rw [List.map_cons, List.length_cons, List.replicate_succ]
    simp only [List.zipWith_cons_cons]
    exact congrArg₂ List.cons (foldl_eq_chunks9 (stepFactorCIv S36) fs [CFpIv.ofInt S36 1]) ih

private lemma map_eq_of_chunks3_12 {α β : Type*} (g : α → β) (as : List α) (bs : List β)
    (h1 : (as.take 12).map g = bs.take 12)
    (h2 : ((as.drop 12).take 12).map g = (bs.drop 12).take 12)
    (h3 : (as.drop 24).map g = bs.drop 24) :
    as.map g = bs := by
  have ha : as = as.take 12 ++ ((as.drop 12).take 12 ++ as.drop 24) := by
    have hdrop : (as.drop 12).take 12 ++ as.drop 24 = as.drop 12 := by
      rw [show as.drop 24 = (as.drop 12).drop 12 by simp [List.drop_drop], List.take_append_drop]
    rw [hdrop, List.take_append_drop]
  have hb : bs = bs.take 12 ++ ((bs.drop 12).take 12 ++ bs.drop 24) := by
    have hdrop : (bs.drop 12).take 12 ++ bs.drop 24 = bs.drop 12 := by
      rw [show bs.drop 24 = (bs.drop 12).drop 12 by simp [List.drop_drop], List.take_append_drop]
    rw [hdrop, List.take_append_drop]
  rw [ha, List.map_append, List.map_append, h1, h2, h3, ← hb]

private lemma polyRowsOf_evenMat18_mem {sn : ℤ} (hsn : 1 ≤ sn) {tbl : List ℤ}
    (hok : rhoTableOk (pts36OfSn sn) tbl = true) :
    let rows := polyRowsOf (wRowsOf (pts36OfSn sn) tbl)
    let M18Iv := mkMat18EvenIv rows
    ∀ r c : Fin 18, CFpIv.CFpMem S36 ((M18Iv.getD r.1 []).getD c.1 CFpIv.zero)
      (evenMat18 (x36Clamp (sn : ℝ)).1 r c) := by
  intro rows M18Iv r c
  have hw : ∀ i j : Fin 36, i < j →
      CFpIv.CFpMem S36 (wRead (wRowsOf (pts36OfSn sn) tbl) i j)
        (stereoSlope (x36Clamp (sn : ℝ)).1 i j) := by
    intro i j hij
    rw [wRead_wRowsOf]
    exact mkWEntry_mem hsn hok i j hij
  have hpoly := polyListCIv_mem S36_pos hw (evenSrcRow r) (2 * c.1)
  have heval : (polyListC (stereoSlope (x36Clamp (sn : ℝ)).1) (evenSrcRow r)).getD (2 * c.1) 0 =
      evenMat18 (x36Clamp (sn : ℝ)).1 r c := by
    rw [← coeff_evalListC]
    rw [evalListC_polyListC_eq (stereoSlope (x36Clamp (sn : ℝ)).1)
      (stereoSpinor (x36Clamp (sn : ℝ)).1)]
    · rfl
    · intro i j hlt; simp [stereoSpinor, hlt.ne', not_lt_of_gt hlt]
    · intro i j hgt; simp [stereoSpinor, hgt.ne, hgt]
  have hrow : M18Iv.getD r.1 [] =
      (List.finRange 18).map fun c' =>
        (polyListCIv S36 (wRead (wRowsOf (pts36OfSn sn) tbl)) (evenSrcRow r)).getD (2 * c'.1) CFpIv.zero := by
    simp [M18Iv, mkMat18EvenIv, rows, polyRowsOf, readMemo_memoFin, List.getD_eq_getElem?_getD]
  rw [hrow, getD_map_finRange]
  rw [← heval]
  exact hpoly

private lemma polyRowsOf_oddMat18_mem {sn : ℤ} (hsn : 1 ≤ sn) {tbl : List ℤ}
    (hok : rhoTableOk (pts36OfSn sn) tbl = true) :
    let rows := polyRowsOf (wRowsOf (pts36OfSn sn) tbl)
    let M18Iv := mkMat18OddIv rows
    ∀ r c : Fin 18, CFpIv.CFpMem S36 ((M18Iv.getD r.1 []).getD c.1 CFpIv.zero)
      (oddMat18 (x36Clamp (sn : ℝ)).1 r c) := by
  intro rows M18Iv r c
  have hw : ∀ i j : Fin 36, i < j →
      CFpIv.CFpMem S36 (wRead (wRowsOf (pts36OfSn sn) tbl) i j)
        (stereoSlope (x36Clamp (sn : ℝ)).1 i j) := by
    intro i j hij
    rw [wRead_wRowsOf]
    exact mkWEntry_mem hsn hok i j hij
  have hpoly := polyListCIv_mem S36_pos hw (oddSrcRow r) (2 * c.1 + 1)
  have heval : (polyListC (stereoSlope (x36Clamp (sn : ℝ)).1) (oddSrcRow r)).getD (2 * c.1 + 1) 0 =
      oddMat18 (x36Clamp (sn : ℝ)).1 r c := by
    rw [← coeff_evalListC]
    rw [evalListC_polyListC_eq (stereoSlope (x36Clamp (sn : ℝ)).1)
      (stereoSpinor (x36Clamp (sn : ℝ)).1)]
    · rfl
    · intro i j hlt; simp [stereoSpinor, hlt.ne', not_lt_of_gt hlt]
    · intro i j hgt; simp [stereoSpinor, hgt.ne, hgt]
  have hrow : M18Iv.getD r.1 [] =
      (List.finRange 18).map fun c' =>
        (polyListCIv S36 (wRead (wRowsOf (pts36OfSn sn) tbl)) (oddSrcRow r)).getD (2 * c'.1 + 1) CFpIv.zero := by
    simp [M18Iv, mkMat18OddIv, rows, polyRowsOf, readMemo_memoFin, List.getD_eq_getElem?_getD]
  rw [hrow, getD_map_finRange]
  rw [← heval]
  exact hpoly

private def w9Cached : List (List CFpIv) := wRowsOf (pts36OfSn 9) rho9List
private def rows9Cached : List (List CFpIv) := polyRowsOf w9Cached
private def w10Cached : List (List CFpIv) := wRowsOf (pts36OfSn 10) rho10List
private def rows10Cached : List (List CFpIv) := polyRowsOf w10Cached

section MidLitTables

private abbrev z : CFpIv := CFpIv.zero

private abbrev o : CFpIv := CFpIv.ofInt S36 1

private def w9Lit : List (List CFpIv) := [
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨22479983485212041, 22479983485212042⟩, ⟨0, 0⟩⟩, ⟨⟨-22479983485212042, -22479983485212041⟩, ⟨0, 0⟩⟩, ⟨⟨11412914692492266, 11412914692492267⟩, ⟨19367370387259604, 19367370387259605⟩⟩, ⟨⟨-11412914692492267, -11412914692492266⟩, ⟨-19367370387259605, -19367370387259604⟩⟩, ⟨⟨-11412914692492267, -11412914692492266⟩, ⟨19367370387259604, 19367370387259605⟩⟩, ⟨⟨11412914692492266, 11412914692492267⟩, ⟨-19367370387259605, -19367370387259604⟩⟩, ⟨⟨413832915006284467, 413832915006284468⟩, ⟨0, 0⟩⟩, ⟨⟨-413832915006284468, -413832915006284467⟩, ⟨0, 0⟩⟩, ⟨⟨210099787618575191, 210099787618575192⟩, ⟨356532972928491233, 356532972928491234⟩⟩, ⟨⟨-210099787618575192, -210099787618575191⟩, ⟨-356532972928491234, -356532972928491233⟩⟩, ⟨⟨-210099787618575192, -210099787618575191⟩, ⟨356532972928491233, 356532972928491234⟩⟩, ⟨⟨210099787618575191, 210099787618575192⟩, ⟨-356532972928491234, -356532972928491233⟩⟩, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨22482142215500151, 22482142215500152⟩, ⟨0, 0⟩⟩, ⟨⟨-22482142215500152, -22482142215500151⟩, ⟨0, 0⟩⟩, ⟨⟨11414010663253922, 11414010663253923⟩, ⟨19369230216430899, 19369230216430900⟩⟩, ⟨⟨-11414010663253923, -11414010663253922⟩, ⟨-19369230216430900, -19369230216430899⟩⟩, ⟨⟨-11414010663253923, -11414010663253922⟩, ⟨19369230216430899, 19369230216430900⟩⟩, ⟨⟨11414010663253922, 11414010663253923⟩, ⟨-19369230216430900, -19369230216430899⟩⟩, ⟨⟨413860084294284695, 413860084294284696⟩, ⟨0, 0⟩⟩, ⟨⟨-413860084294284696, -413860084294284695⟩, ⟨0, 0⟩⟩, ⟨⟨210113581257098383, 210113581257098384⟩, ⟨356556380315076045, 356556380315076046⟩⟩, ⟨⟨-210113581257098384, -210113581257098383⟩, ⟨-356556380315076046, -356556380315076045⟩⟩, ⟨⟨-210113581257098384, -210113581257098383⟩, ⟨356556380315076045, 356556380315076046⟩⟩, ⟨⟨210113581257098383, 210113581257098384⟩, ⟨-356556380315076046, -356556380315076045⟩⟩, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨22484301360219978, 22484301360219979⟩, ⟨0, 0⟩⟩, ⟨⟨-22484301360219979, -22484301360219978⟩, ⟨0, 0⟩⟩, ⟨⟨11415106844419373, 11415106844419374⟩, ⟨19371090402651058, 19371090402651059⟩⟩, ⟨⟨-11415106844419374, -11415106844419373⟩, ⟨-19371090402651059, -19371090402651058⟩⟩, ⟨⟨-11415106844419374, -11415106844419373⟩, ⟨19371090402651058, 19371090402651059⟩⟩, ⟨⟨11415106844419373, 11415106844419374⟩, ⟨-19371090402651059, -19371090402651058⟩⟩, ⟨⟨413887256628221554, 413887256628221555⟩, ⟨0, 0⟩⟩, ⟨⟨-413887256628221555, -413887256628221554⟩, ⟨0, 0⟩⟩, ⟨⟨210127376442020173, 210127376442020174⟩, ⟨356579790325852416, 356579790325852417⟩⟩, ⟨⟨-210127376442020174, -210127376442020173⟩, ⟨-356579790325852417, -356579790325852416⟩⟩, ⟨⟨-210127376442020174, -210127376442020173⟩, ⟨356579790325852416, 356579790325852417⟩⟩, ⟨⟨210127376442020173, 210127376442020174⟩, ⟨-356579790325852417, -356579790325852416⟩⟩, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨22486460919490817, 22486460919490818⟩, ⟨0, 0⟩⟩, ⟨⟨-22486460919490818, -22486460919490817⟩, ⟨0, 0⟩⟩, ⟨⟨11416203236049184, 11416203236049185⟩, ⟨19372950946022858, 19372950946022859⟩⟩, ⟨⟨-11416203236049185, -11416203236049184⟩, ⟨-19372950946022859, -19372950946022858⟩⟩, ⟨⟨-11416203236049185, -11416203236049184⟩, ⟨19372950946022858, 19372950946022859⟩⟩, ⟨⟨11416203236049184, 11416203236049185⟩, ⟨-19372950946022859, -19372950946022858⟩⟩, ⟨⟨413914432008519535, 413914432008519536⟩, ⟨0, 0⟩⟩, ⟨⟨-413914432008519536, -413914432008519535⟩, ⟨0, 0⟩⟩, ⟨⟨210141173173556071, 210141173173556072⟩, ⟨356603202961186061, 356603202961186062⟩⟩, ⟨⟨-210141173173556072, -210141173173556071⟩, ⟨-356603202961186062, -356603202961186061⟩⟩, ⟨⟨-210141173173556072, -210141173173556071⟩, ⟨356603202961186061, 356603202961186062⟩⟩, ⟨⟨210141173173556071, 210141173173556072⟩, ⟨-356603202961186062, -356603202961186061⟩⟩, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨22488620893432008, 22488620893432009⟩, ⟨0, 0⟩⟩, ⟨⟨-22488620893432009, -22488620893432008⟩, ⟨0, 0⟩⟩, ⟨⟨11417299838203942, 11417299838203943⟩, ⟨19374811846649115, 19374811846649116⟩⟩, ⟨⟨-11417299838203943, -11417299838203942⟩, ⟨-19374811846649116, -19374811846649115⟩⟩, ⟨⟨-11417299838203943, -11417299838203942⟩, ⟨19374811846649115, 19374811846649116⟩⟩, ⟨⟨11417299838203942, 11417299838203943⟩, ⟨-19374811846649116, -19374811846649115⟩⟩, ⟨⟨413941610435603188, 413941610435603189⟩, ⟨0, 0⟩⟩, ⟨⟨-413941610435603189, -413941610435603188⟩, ⟨0, 0⟩⟩, ⟨⟨210154971451921618, 210154971451921619⟩, ⟨356626618221442746, 356626618221442747⟩⟩, ⟨⟨-210154971451921619, -210154971451921618⟩, ⟨-356626618221442747, -356626618221442746⟩⟩, ⟨⟨-210154971451921619, -210154971451921618⟩, ⟨356626618221442746, 356626618221442747⟩⟩, ⟨⟨210154971451921618, 210154971451921619⟩, ⟨-356626618221442747, -356626618221442746⟩⟩, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨22490781282162937, 22490781282162938⟩, ⟨0, 0⟩⟩, ⟨⟨-22490781282162938, -22490781282162937⟩, ⟨0, 0⟩⟩, ⟨⟨11418396650944260, 11418396650944261⟩, ⟨19376673104632684, 19376673104632685⟩⟩, ⟨⟨-11418396650944261, -11418396650944260⟩, ⟨-19376673104632685, -19376673104632684⟩⟩, ⟨⟨-11418396650944261, -11418396650944260⟩, ⟨19376673104632684, 19376673104632685⟩⟩, ⟨⟨11418396650944260, 11418396650944261⟩, ⟨-19376673104632685, -19376673104632684⟩⟩, ⟨⟨413968791909897122, 413968791909897123⟩, ⟨0, 0⟩⟩, ⟨⟨-413968791909897123, -413968791909897122⟩, ⟨0, 0⟩⟩, ⟨⟨210168771277332385, 210168771277332386⟩, ⟨356650036106988290, 356650036106988291⟩⟩, ⟨⟨-210168771277332386, -210168771277332385⟩, ⟨-356650036106988291, -356650036106988290⟩⟩, ⟨⟨-210168771277332386, -210168771277332385⟩, ⟨356650036106988290, 356650036106988291⟩⟩, ⟨⟨210168771277332385, 210168771277332386⟩, ⟨-356650036106988291, -356650036106988290⟩⟩, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨22492942085803037, 22492942085803038⟩, ⟨0, 0⟩⟩, ⟨⟨-22492942085803038, -22492942085803037⟩, ⟨0, 0⟩⟩, ⟨⟨11419493674330772, 11419493674330773⟩, ⟨19378534720076462, 19378534720076463⟩⟩, ⟨⟨-11419493674330773, -11419493674330772⟩, ⟨-19378534720076463, -19378534720076462⟩⟩, ⟨⟨-11419493674330773, -11419493674330772⟩, ⟨19378534720076462, 19378534720076463⟩⟩, ⟨⟨11419493674330772, 11419493674330773⟩, ⟨-19378534720076463, -19378534720076462⟩⟩, ⟨⟨413995976431826007, 413995976431826008⟩, ⟨0, 0⟩⟩, ⟨⟨-413995976431826008, -413995976431826007⟩, ⟨0, 0⟩⟩, ⟨⟨210182572650003972, 210182572650003973⟩, ⟨356673456618188560, 356673456618188561⟩⟩, ⟨⟨-210182572650003973, -210182572650003972⟩, ⟨-356673456618188561, -356673456618188560⟩⟩, ⟨⟨-210182572650003973, -210182572650003972⟩, ⟨356673456618188560, 356673456618188561⟩⟩, ⟨⟨210182572650003972, 210182572650003973⟩, ⟨-356673456618188561, -356673456618188560⟩⟩, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨22495103304471784, 22495103304471785⟩, ⟨0, 0⟩⟩, ⟨⟨-22495103304471785, -22495103304471784⟩, ⟨0, 0⟩⟩, ⟨⟨11420590908424136, 11420590908424137⟩, ⟨19380396693083383, 19380396693083384⟩⟩, ⟨⟨-11420590908424137, -11420590908424136⟩, ⟨-19380396693083384, -19380396693083383⟩⟩, ⟨⟨-11420590908424137, -11420590908424136⟩, ⟨19380396693083383, 19380396693083384⟩⟩, ⟨⟨11420590908424136, 11420590908424137⟩, ⟨-19380396693083384, -19380396693083383⟩⟩, ⟨⟨414023164001814569, 414023164001814570⟩, ⟨0, 0⟩⟩, ⟨⟨-414023164001814570, -414023164001814569⟩, ⟨0, 0⟩⟩, ⟨⟨210196375570152012, 210196375570152013⟩, ⟨356696879755409475, 356696879755409476⟩⟩, ⟨⟨-210196375570152013, -210196375570152012⟩, ⟨-356696879755409476, -356696879755409475⟩⟩, ⟨⟨-210196375570152013, -210196375570152012⟩, ⟨356696879755409475, 356696879755409476⟩⟩, ⟨⟨210196375570152012, 210196375570152013⟩, ⟨-356696879755409476, -356696879755409475⟩⟩, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨22497264938288704, 22497264938288705⟩, ⟨0, 0⟩⟩, ⟨⟨-22497264938288705, -22497264938288704⟩, ⟨0, 0⟩⟩, ⟨⟨11421688353285034, 11421688353285035⟩, ⟨19382259023756422, 19382259023756423⟩⟩, ⟨⟨-11421688353285035, -11421688353285034⟩, ⟨-19382259023756423, -19382259023756422⟩⟩, ⟨⟨-11421688353285035, -11421688353285034⟩, ⟨19382259023756422, 19382259023756423⟩⟩, ⟨⟨11421688353285034, 11421688353285035⟩, ⟨-19382259023756423, -19382259023756422⟩⟩, ⟨⟨414050354620287596, 414050354620287597⟩, ⟨0, 0⟩⟩, ⟨⟨-414050354620287597, -414050354620287596⟩, ⟨0, 0⟩⟩, ⟨⟨210210180037992164, 210210180037992165⟩, ⟨356720305519017005, 356720305519017006⟩⟩, ⟨⟨-210210180037992165, -210210180037992164⟩, ⟨-356720305519017006, -356720305519017005⟩⟩, ⟨⟨-210210180037992165, -210210180037992164⟩, ⟨356720305519017005, 356720305519017006⟩⟩, ⟨⟨210210180037992164, 210210180037992165⟩, ⟨-356720305519017006, -356720305519017005⟩⟩, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨22499426987373364, 22499426987373365⟩, ⟨0, 0⟩⟩, ⟨⟨-22499426987373365, -22499426987373364⟩, ⟨0, 0⟩⟩, ⟨⟨11422786008974169, 11422786008974170⟩, ⟨19384121712198591, 19384121712198592⟩⟩, ⟨⟨-11422786008974170, -11422786008974169⟩, ⟨-19384121712198592, -19384121712198591⟩⟩, ⟨⟨-11422786008974170, -11422786008974169⟩, ⟨19384121712198591, 19384121712198592⟩⟩, ⟨⟨11422786008974169, 11422786008974170⟩, ⟨-19384121712198592, -19384121712198591⟩⟩, ⟨⟨414077548287669933, 414077548287669934⟩, ⟨0, 0⟩⟩, ⟨⟨-414077548287669934, -414077548287669933⟩, ⟨0, 0⟩⟩, ⟨⟨210223986053740120, 210223986053740121⟩, ⟨356743733909377173, 356743733909377174⟩⟩, ⟨⟨-210223986053740121, -210223986053740120⟩, ⟨-356743733909377174, -356743733909377173⟩⟩, ⟨⟨-210223986053740121, -210223986053740120⟩, ⟨356743733909377173, 356743733909377174⟩⟩, ⟨⟨210223986053740120, 210223986053740121⟩, ⟨-356743733909377174, -356743733909377173⟩⟩, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨22501589451845382, 22501589451845383⟩, ⟨0, 0⟩⟩, ⟨⟨-22501589451845383, -22501589451845382⟩, ⟨0, 0⟩⟩, ⟨⟨11423883875552270, 11423883875552271⟩, ⟨19385984758512944, 19385984758512945⟩⟩, ⟨⟨-11423883875552271, -11423883875552270⟩, ⟨-19385984758512945, -19385984758512944⟩⟩, ⟨⟨-11423883875552271, -11423883875552270⟩, ⟨19385984758512944, 19385984758512945⟩⟩, ⟨⟨11423883875552270, 11423883875552271⟩, ⟨-19385984758512945, -19385984758512944⟩⟩, ⟨⟨414104745004386487, 414104745004386488⟩, ⟨0, 0⟩⟩, ⟨⟨-414104745004386488, -414104745004386487⟩, ⟨0, 0⟩⟩, ⟨⟨210237793617611601, 210237793617611602⟩, ⟨356767164926856051, 356767164926856052⟩⟩, ⟨⟨-210237793617611602, -210237793617611601⟩, ⟨-356767164926856052, -356767164926856051⟩⟩, ⟨⟨-210237793617611602, -210237793617611601⟩, ⟨356767164926856051, 356767164926856052⟩⟩, ⟨⟨210237793617611601, 210237793617611602⟩, ⟨-356767164926856052, -356767164926856051⟩⟩, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨22503752331824417, 22503752331824418⟩, ⟨0, 0⟩⟩, ⟨⟨-22503752331824418, -22503752331824417⟩, ⟨0, 0⟩⟩, ⟨⟨11424981953080088, 11424981953080089⟩, ⟨19387848162802575, 19387848162802576⟩⟩, ⟨⟨-11424981953080089, -11424981953080088⟩, ⟨-19387848162802576, -19387848162802575⟩⟩, ⟨⟨-11424981953080089, -11424981953080088⟩, ⟨19387848162802575, 19387848162802576⟩⟩, ⟨⟨11424981953080088, 11424981953080089⟩, ⟨-19387848162802576, -19387848162802575⟩⟩, ⟨⟨414131944770862222, 414131944770862223⟩, ⟨0, 0⟩⟩, ⟨⟨-414131944770862223, -414131944770862222⟩, ⟨0, 0⟩⟩, ⟨⟨210251602729822359, 210251602729822360⟩, ⟨356790598571819761, 356790598571819762⟩⟩, ⟨⟨-210251602729822360, -210251602729822359⟩, ⟨-356790598571819762, -356790598571819761⟩⟩, ⟨⟨-210251602729822360, -210251602729822359⟩, ⟨356790598571819761, 356790598571819762⟩⟩, ⟨⟨210251602729822359, 210251602729822360⟩, ⟨-356790598571819762, -356790598571819761⟩⟩, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨22505915627430178, 22505915627430179⟩, ⟨0, 0⟩⟩, ⟨⟨-22505915627430179, -22505915627430178⟩, ⟨0, 0⟩⟩, ⟨⟨11426080241618398, 11426080241618399⟩, ⟨19389711925170615, 19389711925170616⟩⟩, ⟨⟨-11426080241618399, -11426080241618398⟩, ⟨-19389711925170616, -19389711925170615⟩⟩, ⟨⟨-11426080241618399, -11426080241618398⟩, ⟨19389711925170615, 19389711925170616⟩⟩, ⟨⟨11426080241618398, 11426080241618399⟩, ⟨-19389711925170616, -19389711925170615⟩⟩, ⟨⟨414159147587522162, 414159147587522163⟩, ⟨0, 0⟩⟩, ⟨⟨-414159147587522163, -414159147587522162⟩, ⟨0, 0⟩⟩, ⟨⟨210265413390588174, 210265413390588175⟩, ⟨356814034844634478, 356814034844634479⟩⟩, ⟨⟨-210265413390588175, -210265413390588174⟩, ⟨-356814034844634479, -356814034844634478⟩⟩, ⟨⟨-210265413390588175, -210265413390588174⟩, ⟨356814034844634478, 356814034844634479⟩⟩, ⟨⟨210265413390588174, 210265413390588175⟩, ⟨-356814034844634479, -356814034844634478⟩⟩, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨22508079338782417, 22508079338782418⟩, ⟨0, 0⟩⟩, ⟨⟨-22508079338782418, -22508079338782417⟩, ⟨0, 0⟩⟩, ⟨⟨11427178741227996, 11427178741227997⟩, ⟨19391576045720236, 19391576045720237⟩⟩, ⟨⟨-11427178741227997, -11427178741227996⟩, ⟨-19391576045720237, -19391576045720236⟩⟩, ⟨⟨-11427178741227997, -11427178741227996⟩, ⟨19391576045720236, 19391576045720237⟩⟩, ⟨⟨11427178741227996, 11427178741227997⟩, ⟨-19391576045720237, -19391576045720236⟩⟩, ⟨⟨414186353454791390, 414186353454791391⟩, ⟨0, 0⟩⟩, ⟨⟨-414186353454791391, -414186353454791390⟩, ⟨0, 0⟩⟩, ⟨⟨210279225600124859, 210279225600124860⟩, ⟨356837473745666428, 356837473745666429⟩⟩, ⟨⟨-210279225600124860, -210279225600124859⟩, ⟨-356837473745666429, -356837473745666428⟩⟩, ⟨⟨-210279225600124860, -210279225600124859⟩, ⟨356837473745666428, 356837473745666429⟩⟩, ⟨⟨210279225600124859, 210279225600124860⟩, ⟨-356837473745666429, -356837473745666428⟩⟩, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨22510243466000935, 22510243466000936⟩, ⟨0, 0⟩⟩, ⟨⟨-22510243466000936, -22510243466000935⟩, ⟨0, 0⟩⟩, ⟨⟨11428277451969705, 11428277451969706⟩, ⟨19393440524554652, 19393440524554653⟩⟩, ⟨⟨-11428277451969706, -11428277451969705⟩, ⟨-19393440524554653, -19393440524554652⟩⟩, ⟨⟨-11428277451969706, -11428277451969705⟩, ⟨19393440524554652, 19393440524554653⟩⟩, ⟨⟨11428277451969705, 11428277451969706⟩, ⟨-19393440524554653, -19393440524554652⟩⟩, ⟨⟨414213562373095048, 414213562373095049⟩, ⟨0, 0⟩⟩, ⟨⟨-414213562373095049, -414213562373095048⟩, ⟨0, 0⟩⟩, ⟨⟨210293039358648255, 210293039358648256⟩, ⟨356860915275281888, 356860915275281889⟩⟩, ⟨⟨-210293039358648256, -210293039358648255⟩, ⟨-356860915275281889, -356860915275281888⟩⟩, ⟨⟨-210293039358648256, -210293039358648255⟩, ⟨356860915275281888, 356860915275281889⟩⟩, ⟨⟨210293039358648255, 210293039358648256⟩, ⟨-356860915275281889, -356860915275281888⟩⟩, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨22512408009205576, 22512408009205577⟩, ⟨0, 0⟩⟩, ⟨⟨-22512408009205577, -22512408009205576⟩, ⟨0, 0⟩⟩, ⟨⟨11429376373904369, 11429376373904370⟩, ⟨19395305361777111, 19395305361777112⟩⟩, ⟨⟨-11429376373904370, -11429376373904369⟩, ⟨-19395305361777112, -19395305361777111⟩⟩, ⟨⟨-11429376373904370, -11429376373904369⟩, ⟨19395305361777111, 19395305361777112⟩⟩, ⟨⟨11429376373904369, 11429376373904370⟩, ⟨-19395305361777112, -19395305361777111⟩⟩, ⟨⟨414240774342858339, 414240774342858340⟩, ⟨0, 0⟩⟩, ⟨⟨-414240774342858340, -414240774342858339⟩, ⟨0, 0⟩⟩, ⟨⟨210306854666374233, 210306854666374234⟩, ⟨356884359433847184, 356884359433847185⟩⟩, ⟨⟨-210306854666374234, -210306854666374233⟩, ⟨-356884359433847185, -356884359433847184⟩⟩, ⟨⟨-210306854666374234, -210306854666374233⟩, ⟨356884359433847184, 356884359433847185⟩⟩, ⟨⟨210306854666374233, 210306854666374234⟩, ⟨-356884359433847185, -356884359433847184⟩⟩, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨22514572968516231, 22514572968516232⟩, ⟨0, 0⟩⟩, ⟨⟨-22514572968516232, -22514572968516231⟩, ⟨0, 0⟩⟩, ⟨⟨11430475507092856, 11430475507092857⟩, ⟨19397170557490907, 19397170557490908⟩⟩, ⟨⟨-11430475507092857, -11430475507092856⟩, ⟨-19397170557490908, -19397170557490907⟩⟩, ⟨⟨-11430475507092857, -11430475507092856⟩, ⟨19397170557490907, 19397170557490908⟩⟩, ⟨⟨11430475507092856, 11430475507092857⟩, ⟨-19397170557490908, -19397170557490907⟩⟩, ⟨⟨414267989364506522, 414267989364506523⟩, ⟨0, 0⟩⟩, ⟨⟨-414267989364506523, -414267989364506522⟩, ⟨0, 0⟩⟩, ⟨⟨210320671523518696, 210320671523518697⟩, ⟨356907806221728696, 356907806221728697⟩⟩, ⟨⟨-210320671523518697, -210320671523518696⟩, ⟨-356907806221728697, -356907806221728696⟩⟩, ⟨⟨-210320671523518697, -210320671523518696⟩, ⟨356907806221728696, 356907806221728697⟩⟩, ⟨⟨210320671523518696, 210320671523518697⟩, ⟨-356907806221728697, -356907806221728696⟩⟩, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨22516738344052838, 22516738344052839⟩, ⟨0, 0⟩⟩, ⟨⟨-22516738344052839, -22516738344052838⟩, ⟨0, 0⟩⟩, ⟨⟨11431574851596056, 11431574851596057⟩, ⟨19399036111799368, 19399036111799369⟩⟩, ⟨⟨-11431574851596057, -11431574851596056⟩, ⟨-19399036111799369, -19399036111799368⟩⟩, ⟨⟨-11431574851596057, -11431574851596056⟩, ⟨19399036111799368, 19399036111799369⟩⟩, ⟨⟨11431574851596056, 11431574851596057⟩, ⟨-19399036111799369, -19399036111799368⟩⟩, ⟨⟨414295207438464918, 414295207438464919⟩, ⟨0, 0⟩⟩, ⟨⟨-414295207438464919, -414295207438464918⟩, ⟨0, 0⟩⟩, ⟨⟨210334489930297574, 210334489930297575⟩, ⟨356931255639292853, 356931255639292854⟩⟩, ⟨⟨-210334489930297575, -210334489930297574⟩, ⟨-356931255639292854, -356931255639292853⟩⟩, ⟨⟨-210334489930297575, -210334489930297574⟩, ⟨356931255639292853, 356931255639292854⟩⟩, ⟨⟨210334489930297574, 210334489930297575⟩, ⟨-356931255639292854, -356931255639292853⟩⟩, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨-1000000000000000000, -999999999999999999⟩, ⟨0, 0⟩⟩, ⟨⟨-496138938356833825, -496138938356833824⟩, ⟨868243142124459193, 868243142124459194⟩⟩, ⟨⟨-868243142124459194, -868243142124459193⟩, ⟨-496138938356833825, -496138938356833824⟩⟩, ⟨⟨-868243142124459194, -868243142124459193⟩, ⟨496138938356833824, 496138938356833825⟩⟩, ⟨⟨-496138938356833825, -496138938356833824⟩, ⟨-868243142124459194, -868243142124459193⟩⟩, ⟨⟨964334741237681539, 964334741237681540⟩, ⟨0, 0⟩⟩, ⟨⟨-967256494730015095, -967256494730015094⟩, ⟨0, 0⟩⟩, ⟨⟨457802251051794875, 457802251051794876⟩, ⟨849638759877106340, 849638759877106341⟩⟩, ⟨⟨-520908285531910629, -520908285531910628⟩, ⟨-814235281268326323, -814235281268326322⟩⟩, ⟨⟨-520908285531910629, -520908285531910628⟩, ⟨814235281268326322, 814235281268326323⟩⟩, ⟨⟨457802251051794875, 457802251051794876⟩, ⟨-849638759877106341, -849638759877106340⟩⟩, ⟨⟨-480144078351167904, -480144078351167903⟩, ⟨0, 0⟩⟩, ⟨⟨-479344531607148238, -479344531607148237⟩, ⟨0, 0⟩⟩, ⟨⟨-478547147925135569, -478547147925135568⟩, ⟨0, 0⟩⟩, ⟨⟨-477751920543723342, -477751920543723341⟩, ⟨0, 0⟩⟩, ⟨⟨-476958842718838297, -476958842718838296⟩, ⟨0, 0⟩⟩, ⟨⟨-476167907723762931, -476167907723762930⟩, ⟨0, 0⟩⟩],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨868243142124459193, 868243142124459194⟩, ⟨496138938356833824, 496138938356833825⟩⟩, ⟨⟨496138938356833824, 496138938356833825⟩, ⟨-868243142124459194, -868243142124459193⟩⟩, ⟨⟨496138938356833824, 496138938356833825⟩, ⟨868243142124459193, 868243142124459194⟩⟩, ⟨⟨868243142124459193, 868243142124459194⟩, ⟨-496138938356833825, -496138938356833824⟩⟩, ⟨⟨967256494730015094, 967256494730015095⟩, ⟨0, 0⟩⟩, ⟨⟨-964334741237681540, -964334741237681539⟩, ⟨0, 0⟩⟩, ⟨⟨520908285531910628, 520908285531910629⟩, ⟨814235281268326322, 814235281268326323⟩⟩, ⟨⟨-457802251051794876, -457802251051794875⟩, ⟨-849638759877106341, -849638759877106340⟩⟩, ⟨⟨-457802251051794876, -457802251051794875⟩, ⟨849638759877106340, 849638759877106341⟩⟩, ⟨⟨520908285531910628, 520908285531910629⟩, ⟨-814235281268326323, -814235281268326322⟩⟩, ⟨⟨480144078351167903, 480144078351167904⟩, ⟨0, 0⟩⟩, ⟨⟨479344531607148237, 479344531607148238⟩, ⟨0, 0⟩⟩, ⟨⟨478547147925135568, 478547147925135569⟩, ⟨0, 0⟩⟩, ⟨⟨477751920543723341, 477751920543723342⟩, ⟨0, 0⟩⟩, ⟨⟨476958842718838296, 476958842718838297⟩, ⟨0, 0⟩⟩, ⟨⟨476167907723762930, 476167907723762931⟩, ⟨0, 0⟩⟩],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨-507692307692307693, -507692307692307692⟩, ⟨-861538461538461539, -861538461538461538⟩⟩, ⟨⟨-1000000000000000000, -999999999999999999⟩, ⟨0, 0⟩⟩, ⟨⟨0, 0⟩, ⟨-1000000000000000000, -999999999999999999⟩⟩, ⟨⟨964419151351187476, 964419151351187477⟩, ⟨-36940815646830711, -36940815646830710⟩⟩, ⟨⟨-965956141131989613, -965956141131989612⟩, ⟨-35401533968188101, -35401533968188100⟩⟩, ⟨⟨489585330166822935, 489585330166822936⟩, ⟨830811469374002557, 830811469374002558⟩⟩, ⟨⟨-491068681939853818, -491068681939853817⟩, ⟨-833328672382782236, -833328672382782235⟩⟩, ⟨⟨-521918883361846255, -521918883361846254⟩, ⟨811873818562871951, 811873818562871952⟩⟩, ⟨⟨459383663883669601, 459383663883669602⟩, ⟨-850429262065636288, -850429262065636287⟩⟩, ⟨⟨-243765455162900628, -243765455162900627⟩, ⟨-413662590579467733, -413662590579467732⟩⟩, ⟨⟨-243359531431321414, -243359531431321413⟩, ⟨-412973750307696944, -412973750307696943⟩⟩, ⟨⟨-242954705869684212, -242954705869684211⟩, ⟨-412286773597039875, -412286773597039874⟩⟩, ⟨⟨-242550975045274928, -242550975045274927⟩, ⟨-411601654622284725, -411601654622284724⟩⟩, ⟨⟨-242148335534179444, -242148335534179443⟩, ⟨-410918387573152995, -410918387573152994⟩⟩, ⟨⟨-241746783921295027, -241746783921295026⟩, ⟨-410236966654318833, -410236966654318832⟩⟩],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨0, 0⟩, ⟨999999999999999999, 1000000000000000000⟩⟩, ⟨⟨999999999999999999, 1000000000000000000⟩, ⟨0, 0⟩⟩, ⟨⟨965956141131989612, 965956141131989613⟩, ⟨35401533968188100, 35401533968188101⟩⟩, ⟨⟨-964419151351187477, -964419151351187476⟩, ⟨36940815646830710, 36940815646830711⟩⟩, ⟨⟨491068681939853817, 491068681939853818⟩, ⟨833328672382782235, 833328672382782236⟩⟩, ⟨⟨-489585330166822936, -489585330166822935⟩, ⟨-830811469374002558, -830811469374002557⟩⟩, ⟨⟨-459383663883669602, -459383663883669601⟩, ⟨850429262065636287, 850429262065636288⟩⟩, ⟨⟨521918883361846254, 521918883361846255⟩, ⟨-811873818562871952, -811873818562871951⟩⟩, ⟨⟨243765455162900627, 243765455162900628⟩, ⟨413662590579467732, 413662590579467733⟩⟩, ⟨⟨243359531431321413, 243359531431321414⟩, ⟨412973750307696943, 412973750307696944⟩⟩, ⟨⟨242954705869684211, 242954705869684212⟩, ⟨412286773597039874, 412286773597039875⟩⟩, ⟨⟨242550975045274927, 242550975045274928⟩, ⟨411601654622284724, 411601654622284725⟩⟩, ⟨⟨242148335534179443, 242148335534179444⟩, ⟨410918387573152994, 410918387573152995⟩⟩, ⟨⟨241746783921295026, 241746783921295027⟩, ⟨410236966654318832, 410236966654318833⟩⟩],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨507692307692307692, 507692307692307693⟩, ⟨-861538461538461539, -861538461538461538⟩⟩, ⟨⟨965956141131989612, 965956141131989613⟩, ⟨-35401533968188101, -35401533968188100⟩⟩, ⟨⟨-964419151351187477, -964419151351187476⟩, ⟨-36940815646830711, -36940815646830710⟩⟩, ⟨⟨521918883361846254, 521918883361846255⟩, ⟨811873818562871951, 811873818562871952⟩⟩, ⟨⟨-459383663883669602, -459383663883669601⟩, ⟨-850429262065636288, -850429262065636287⟩⟩, ⟨⟨-489585330166822936, -489585330166822935⟩, ⟨830811469374002557, 830811469374002558⟩⟩, ⟨⟨491068681939853817, 491068681939853818⟩, ⟨-833328672382782236, -833328672382782235⟩⟩, ⟨⟨243765455162900627, 243765455162900628⟩, ⟨-413662590579467733, -413662590579467732⟩⟩, ⟨⟨243359531431321413, 243359531431321414⟩, ⟨-412973750307696944, -412973750307696943⟩⟩, ⟨⟨242954705869684211, 242954705869684212⟩, ⟨-412286773597039875, -412286773597039874⟩⟩, ⟨⟨242550975045274927, 242550975045274928⟩, ⟨-411601654622284725, -411601654622284724⟩⟩, ⟨⟨242148335534179443, 242148335534179444⟩, ⟨-410918387573152995, -410918387573152994⟩⟩, ⟨⟨241746783921295026, 241746783921295027⟩, ⟨-410236966654318833, -410236966654318832⟩⟩],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨964419151351187476, 964419151351187477⟩, ⟨36940815646830710, 36940815646830711⟩⟩, ⟨⟨-965956141131989613, -965956141131989612⟩, ⟨35401533968188100, 35401533968188101⟩⟩, ⟨⟨459383663883669601, 459383663883669602⟩, ⟨850429262065636287, 850429262065636288⟩⟩, ⟨⟨-521918883361846255, -521918883361846254⟩, ⟨-811873818562871952, -811873818562871951⟩⟩, ⟨⟨-491068681939853818, -491068681939853817⟩, ⟨833328672382782235, 833328672382782236⟩⟩, ⟨⟨489585330166822935, 489585330166822936⟩, ⟨-830811469374002558, -830811469374002557⟩⟩, ⟨⟨-243765455162900628, -243765455162900627⟩, ⟨413662590579467732, 413662590579467733⟩⟩, ⟨⟨-243359531431321414, -243359531431321413⟩, ⟨412973750307696943, 412973750307696944⟩⟩, ⟨⟨-242954705869684212, -242954705869684211⟩, ⟨412286773597039874, 412286773597039875⟩⟩, ⟨⟨-242550975045274928, -242550975045274927⟩, ⟨411601654622284724, 411601654622284725⟩⟩, ⟨⟨-242148335534179444, -242148335534179443⟩, ⟨410918387573152994, 410918387573152995⟩⟩, ⟨⟨-241746783921295027, -241746783921295026⟩, ⟨410236966654318832, 410236966654318833⟩⟩],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨-1000000000000000000, -999999999999999999⟩, ⟨0, 0⟩⟩, ⟨⟨-496138938356833825, -496138938356833824⟩, ⟨868243142124459193, 868243142124459194⟩⟩, ⟨⟨-868243142124459194, -868243142124459193⟩, ⟨-496138938356833825, -496138938356833824⟩⟩, ⟨⟨-868243142124459194, -868243142124459193⟩, ⟨496138938356833824, 496138938356833825⟩⟩, ⟨⟨-496138938356833825, -496138938356833824⟩, ⟨-868243142124459194, -868243142124459193⟩⟩, ⟨⟨-999907102048600271, -999907102048600270⟩, ⟨0, 0⟩⟩, ⟨⟨-999814212728031590, -999814212728031589⟩, ⟨0, 0⟩⟩, ⟨⟨-999721332038293623, -999721332038293622⟩, ⟨0, 0⟩⟩, ⟨⟨-999628459979385811, -999628459979385810⟩, ⟨0, 0⟩⟩, ⟨⟨-999535596551307372, -999535596551307371⟩, ⟨0, 0⟩⟩, ⟨⟨-999442741754057301, -999442741754057300⟩, ⟨0, 0⟩⟩],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨868243142124459193, 868243142124459194⟩, ⟨496138938356833824, 496138938356833825⟩⟩, ⟨⟨496138938356833824, 496138938356833825⟩, ⟨-868243142124459194, -868243142124459193⟩⟩, ⟨⟨496138938356833824, 496138938356833825⟩, ⟨868243142124459193, 868243142124459194⟩⟩, ⟨⟨868243142124459193, 868243142124459194⟩, ⟨-496138938356833825, -496138938356833824⟩⟩, ⟨⟨999907102048600270, 999907102048600271⟩, ⟨0, 0⟩⟩, ⟨⟨999814212728031589, 999814212728031590⟩, ⟨0, 0⟩⟩, ⟨⟨999721332038293622, 999721332038293623⟩, ⟨0, 0⟩⟩, ⟨⟨999628459979385810, 999628459979385811⟩, ⟨0, 0⟩⟩, ⟨⟨999535596551307371, 999535596551307372⟩, ⟨0, 0⟩⟩, ⟨⟨999442741754057300, 999442741754057301⟩, ⟨0, 0⟩⟩],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨-507692307692307693, -507692307692307692⟩, ⟨-861538461538461539, -861538461538461538⟩⟩, ⟨⟨-1000000000000000000, -999999999999999999⟩, ⟨0, 0⟩⟩, ⟨⟨0, 0⟩, ⟨-1000000000000000000, -999999999999999999⟩⟩, ⟨⟨-507645144116981676, -507645144116981675⟩, ⟨-861458426380332541, -861458426380332540⟩⟩, ⟨⟨-507597984923462192, -507597984923462191⟩, ⟨-861378398657996447, -861378398657996446⟩⟩, ⟨⟨-507550830111749070, -507550830111749069⟩, ⟨-861298378371452967, -861298378371452966⟩⟩, ⟨⟨-507503679681842027, -507503679681842026⟩, ⟨-861218365520701622, -861218365520701621⟩⟩, ⟨⟨-507456533633740666, -507456533633740665⟩, ⟨-861138360105741736, -861138360105741735⟩⟩, ⟨⟨-507409391967444476, -507409391967444475⟩, ⟨-861058362126572444, -861058362126572443⟩⟩],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨0, 0⟩, ⟨999999999999999999, 1000000000000000000⟩⟩, ⟨⟨999999999999999999, 1000000000000000000⟩, ⟨0, 0⟩⟩, ⟨⟨507645144116981675, 507645144116981676⟩, ⟨861458426380332540, 861458426380332541⟩⟩, ⟨⟨507597984923462191, 507597984923462192⟩, ⟨861378398657996446, 861378398657996447⟩⟩, ⟨⟨507550830111749069, 507550830111749070⟩, ⟨861298378371452966, 861298378371452967⟩⟩, ⟨⟨507503679681842026, 507503679681842027⟩, ⟨861218365520701621, 861218365520701622⟩⟩, ⟨⟨507456533633740665, 507456533633740666⟩, ⟨861138360105741735, 861138360105741736⟩⟩, ⟨⟨507409391967444475, 507409391967444476⟩, ⟨861058362126572443, 861058362126572444⟩⟩],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨507692307692307692, 507692307692307693⟩, ⟨-861538461538461539, -861538461538461538⟩⟩, ⟨⟨507645144116981675, 507645144116981676⟩, ⟨-861458426380332541, -861458426380332540⟩⟩, ⟨⟨507597984923462191, 507597984923462192⟩, ⟨-861378398657996447, -861378398657996446⟩⟩, ⟨⟨507550830111749069, 507550830111749070⟩, ⟨-861298378371452967, -861298378371452966⟩⟩, ⟨⟨507503679681842026, 507503679681842027⟩, ⟨-861218365520701622, -861218365520701621⟩⟩, ⟨⟨507456533633740665, 507456533633740666⟩, ⟨-861138360105741736, -861138360105741735⟩⟩, ⟨⟨507409391967444475, 507409391967444476⟩, ⟨-861058362126572444, -861058362126572443⟩⟩],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨-507645144116981676, -507645144116981675⟩, ⟨861458426380332540, 861458426380332541⟩⟩, ⟨⟨-507597984923462192, -507597984923462191⟩, ⟨861378398657996446, 861378398657996447⟩⟩, ⟨⟨-507550830111749070, -507550830111749069⟩, ⟨861298378371452966, 861298378371452967⟩⟩, ⟨⟨-507503679681842027, -507503679681842026⟩, ⟨861218365520701621, 861218365520701622⟩⟩, ⟨⟨-507456533633740666, -507456533633740665⟩, ⟨861138360105741735, 861138360105741736⟩⟩, ⟨⟨-507409391967444476, -507409391967444475⟩, ⟨861058362126572443, 861058362126572444⟩⟩],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z]
]

private def fac9Lit : List (List (CFpIv × CFpIv)) := [
  [(o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, ⟨⟨22479983485212041, 22479983485212042⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-22479983485212042, -22479983485212041⟩, ⟨0, 0⟩⟩), (o, ⟨⟨11412914692492266, 11412914692492267⟩, ⟨19367370387259604, 19367370387259605⟩⟩), (o, ⟨⟨-11412914692492267, -11412914692492266⟩, ⟨-19367370387259605, -19367370387259604⟩⟩), (o, ⟨⟨-11412914692492267, -11412914692492266⟩, ⟨19367370387259604, 19367370387259605⟩⟩), (o, ⟨⟨11412914692492266, 11412914692492267⟩, ⟨-19367370387259605, -19367370387259604⟩⟩), (o, ⟨⟨413832915006284467, 413832915006284468⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-413832915006284468, -413832915006284467⟩, ⟨0, 0⟩⟩), (o, ⟨⟨210099787618575191, 210099787618575192⟩, ⟨356532972928491233, 356532972928491234⟩⟩), (o, ⟨⟨-210099787618575192, -210099787618575191⟩, ⟨-356532972928491234, -356532972928491233⟩⟩), (o, ⟨⟨-210099787618575192, -210099787618575191⟩, ⟨356532972928491233, 356532972928491234⟩⟩), (o, ⟨⟨210099787618575191, 210099787618575192⟩, ⟨-356532972928491234, -356532972928491233⟩⟩), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z)],
  [(z, o), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, ⟨⟨22482142215500151, 22482142215500152⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-22482142215500152, -22482142215500151⟩, ⟨0, 0⟩⟩), (o, ⟨⟨11414010663253922, 11414010663253923⟩, ⟨19369230216430899, 19369230216430900⟩⟩), (o, ⟨⟨-11414010663253923, -11414010663253922⟩, ⟨-19369230216430900, -19369230216430899⟩⟩), (o, ⟨⟨-11414010663253923, -11414010663253922⟩, ⟨19369230216430899, 19369230216430900⟩⟩), (o, ⟨⟨11414010663253922, 11414010663253923⟩, ⟨-19369230216430900, -19369230216430899⟩⟩), (o, ⟨⟨413860084294284695, 413860084294284696⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-413860084294284696, -413860084294284695⟩, ⟨0, 0⟩⟩), (o, ⟨⟨210113581257098383, 210113581257098384⟩, ⟨356556380315076045, 356556380315076046⟩⟩), (o, ⟨⟨-210113581257098384, -210113581257098383⟩, ⟨-356556380315076046, -356556380315076045⟩⟩), (o, ⟨⟨-210113581257098384, -210113581257098383⟩, ⟨356556380315076045, 356556380315076046⟩⟩), (o, ⟨⟨210113581257098383, 210113581257098384⟩, ⟨-356556380315076046, -356556380315076045⟩⟩), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z)],
  [(z, o), (z, o), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, ⟨⟨22484301360219978, 22484301360219979⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-22484301360219979, -22484301360219978⟩, ⟨0, 0⟩⟩), (o, ⟨⟨11415106844419373, 11415106844419374⟩, ⟨19371090402651058, 19371090402651059⟩⟩), (o, ⟨⟨-11415106844419374, -11415106844419373⟩, ⟨-19371090402651059, -19371090402651058⟩⟩), (o, ⟨⟨-11415106844419374, -11415106844419373⟩, ⟨19371090402651058, 19371090402651059⟩⟩), (o, ⟨⟨11415106844419373, 11415106844419374⟩, ⟨-19371090402651059, -19371090402651058⟩⟩), (o, ⟨⟨413887256628221554, 413887256628221555⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-413887256628221555, -413887256628221554⟩, ⟨0, 0⟩⟩), (o, ⟨⟨210127376442020173, 210127376442020174⟩, ⟨356579790325852416, 356579790325852417⟩⟩), (o, ⟨⟨-210127376442020174, -210127376442020173⟩, ⟨-356579790325852417, -356579790325852416⟩⟩), (o, ⟨⟨-210127376442020174, -210127376442020173⟩, ⟨356579790325852416, 356579790325852417⟩⟩), (o, ⟨⟨210127376442020173, 210127376442020174⟩, ⟨-356579790325852417, -356579790325852416⟩⟩), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z)],
  [(z, o), (z, o), (z, o), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, ⟨⟨22486460919490817, 22486460919490818⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-22486460919490818, -22486460919490817⟩, ⟨0, 0⟩⟩), (o, ⟨⟨11416203236049184, 11416203236049185⟩, ⟨19372950946022858, 19372950946022859⟩⟩), (o, ⟨⟨-11416203236049185, -11416203236049184⟩, ⟨-19372950946022859, -19372950946022858⟩⟩), (o, ⟨⟨-11416203236049185, -11416203236049184⟩, ⟨19372950946022858, 19372950946022859⟩⟩), (o, ⟨⟨11416203236049184, 11416203236049185⟩, ⟨-19372950946022859, -19372950946022858⟩⟩), (o, ⟨⟨413914432008519535, 413914432008519536⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-413914432008519536, -413914432008519535⟩, ⟨0, 0⟩⟩), (o, ⟨⟨210141173173556071, 210141173173556072⟩, ⟨356603202961186061, 356603202961186062⟩⟩), (o, ⟨⟨-210141173173556072, -210141173173556071⟩, ⟨-356603202961186062, -356603202961186061⟩⟩), (o, ⟨⟨-210141173173556072, -210141173173556071⟩, ⟨356603202961186061, 356603202961186062⟩⟩), (o, ⟨⟨210141173173556071, 210141173173556072⟩, ⟨-356603202961186062, -356603202961186061⟩⟩), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z)],
  [(z, o), (z, o), (z, o), (z, o), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, ⟨⟨22488620893432008, 22488620893432009⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-22488620893432009, -22488620893432008⟩, ⟨0, 0⟩⟩), (o, ⟨⟨11417299838203942, 11417299838203943⟩, ⟨19374811846649115, 19374811846649116⟩⟩), (o, ⟨⟨-11417299838203943, -11417299838203942⟩, ⟨-19374811846649116, -19374811846649115⟩⟩), (o, ⟨⟨-11417299838203943, -11417299838203942⟩, ⟨19374811846649115, 19374811846649116⟩⟩), (o, ⟨⟨11417299838203942, 11417299838203943⟩, ⟨-19374811846649116, -19374811846649115⟩⟩), (o, ⟨⟨413941610435603188, 413941610435603189⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-413941610435603189, -413941610435603188⟩, ⟨0, 0⟩⟩), (o, ⟨⟨210154971451921618, 210154971451921619⟩, ⟨356626618221442746, 356626618221442747⟩⟩), (o, ⟨⟨-210154971451921619, -210154971451921618⟩, ⟨-356626618221442747, -356626618221442746⟩⟩), (o, ⟨⟨-210154971451921619, -210154971451921618⟩, ⟨356626618221442746, 356626618221442747⟩⟩), (o, ⟨⟨210154971451921618, 210154971451921619⟩, ⟨-356626618221442747, -356626618221442746⟩⟩), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z)],
  [(z, o), (z, o), (z, o), (z, o), (z, o), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, ⟨⟨22490781282162937, 22490781282162938⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-22490781282162938, -22490781282162937⟩, ⟨0, 0⟩⟩), (o, ⟨⟨11418396650944260, 11418396650944261⟩, ⟨19376673104632684, 19376673104632685⟩⟩), (o, ⟨⟨-11418396650944261, -11418396650944260⟩, ⟨-19376673104632685, -19376673104632684⟩⟩), (o, ⟨⟨-11418396650944261, -11418396650944260⟩, ⟨19376673104632684, 19376673104632685⟩⟩), (o, ⟨⟨11418396650944260, 11418396650944261⟩, ⟨-19376673104632685, -19376673104632684⟩⟩), (o, ⟨⟨413968791909897122, 413968791909897123⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-413968791909897123, -413968791909897122⟩, ⟨0, 0⟩⟩), (o, ⟨⟨210168771277332385, 210168771277332386⟩, ⟨356650036106988290, 356650036106988291⟩⟩), (o, ⟨⟨-210168771277332386, -210168771277332385⟩, ⟨-356650036106988291, -356650036106988290⟩⟩), (o, ⟨⟨-210168771277332386, -210168771277332385⟩, ⟨356650036106988290, 356650036106988291⟩⟩), (o, ⟨⟨210168771277332385, 210168771277332386⟩, ⟨-356650036106988291, -356650036106988290⟩⟩), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z)],
  [(z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, ⟨⟨22492942085803037, 22492942085803038⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-22492942085803038, -22492942085803037⟩, ⟨0, 0⟩⟩), (o, ⟨⟨11419493674330772, 11419493674330773⟩, ⟨19378534720076462, 19378534720076463⟩⟩), (o, ⟨⟨-11419493674330773, -11419493674330772⟩, ⟨-19378534720076463, -19378534720076462⟩⟩), (o, ⟨⟨-11419493674330773, -11419493674330772⟩, ⟨19378534720076462, 19378534720076463⟩⟩), (o, ⟨⟨11419493674330772, 11419493674330773⟩, ⟨-19378534720076463, -19378534720076462⟩⟩), (o, ⟨⟨413995976431826007, 413995976431826008⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-413995976431826008, -413995976431826007⟩, ⟨0, 0⟩⟩), (o, ⟨⟨210182572650003972, 210182572650003973⟩, ⟨356673456618188560, 356673456618188561⟩⟩), (o, ⟨⟨-210182572650003973, -210182572650003972⟩, ⟨-356673456618188561, -356673456618188560⟩⟩), (o, ⟨⟨-210182572650003973, -210182572650003972⟩, ⟨356673456618188560, 356673456618188561⟩⟩), (o, ⟨⟨210182572650003972, 210182572650003973⟩, ⟨-356673456618188561, -356673456618188560⟩⟩), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z)],
  [(z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, ⟨⟨22495103304471784, 22495103304471785⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-22495103304471785, -22495103304471784⟩, ⟨0, 0⟩⟩), (o, ⟨⟨11420590908424136, 11420590908424137⟩, ⟨19380396693083383, 19380396693083384⟩⟩), (o, ⟨⟨-11420590908424137, -11420590908424136⟩, ⟨-19380396693083384, -19380396693083383⟩⟩), (o, ⟨⟨-11420590908424137, -11420590908424136⟩, ⟨19380396693083383, 19380396693083384⟩⟩), (o, ⟨⟨11420590908424136, 11420590908424137⟩, ⟨-19380396693083384, -19380396693083383⟩⟩), (o, ⟨⟨414023164001814569, 414023164001814570⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-414023164001814570, -414023164001814569⟩, ⟨0, 0⟩⟩), (o, ⟨⟨210196375570152012, 210196375570152013⟩, ⟨356696879755409475, 356696879755409476⟩⟩), (o, ⟨⟨-210196375570152013, -210196375570152012⟩, ⟨-356696879755409476, -356696879755409475⟩⟩), (o, ⟨⟨-210196375570152013, -210196375570152012⟩, ⟨356696879755409475, 356696879755409476⟩⟩), (o, ⟨⟨210196375570152012, 210196375570152013⟩, ⟨-356696879755409476, -356696879755409475⟩⟩), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z)],
  [(z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, ⟨⟨22497264938288704, 22497264938288705⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-22497264938288705, -22497264938288704⟩, ⟨0, 0⟩⟩), (o, ⟨⟨11421688353285034, 11421688353285035⟩, ⟨19382259023756422, 19382259023756423⟩⟩), (o, ⟨⟨-11421688353285035, -11421688353285034⟩, ⟨-19382259023756423, -19382259023756422⟩⟩), (o, ⟨⟨-11421688353285035, -11421688353285034⟩, ⟨19382259023756422, 19382259023756423⟩⟩), (o, ⟨⟨11421688353285034, 11421688353285035⟩, ⟨-19382259023756423, -19382259023756422⟩⟩), (o, ⟨⟨414050354620287596, 414050354620287597⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-414050354620287597, -414050354620287596⟩, ⟨0, 0⟩⟩), (o, ⟨⟨210210180037992164, 210210180037992165⟩, ⟨356720305519017005, 356720305519017006⟩⟩), (o, ⟨⟨-210210180037992165, -210210180037992164⟩, ⟨-356720305519017006, -356720305519017005⟩⟩), (o, ⟨⟨-210210180037992165, -210210180037992164⟩, ⟨356720305519017005, 356720305519017006⟩⟩), (o, ⟨⟨210210180037992164, 210210180037992165⟩, ⟨-356720305519017006, -356720305519017005⟩⟩), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z)],
  [(z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, ⟨⟨22499426987373364, 22499426987373365⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-22499426987373365, -22499426987373364⟩, ⟨0, 0⟩⟩), (o, ⟨⟨11422786008974169, 11422786008974170⟩, ⟨19384121712198591, 19384121712198592⟩⟩), (o, ⟨⟨-11422786008974170, -11422786008974169⟩, ⟨-19384121712198592, -19384121712198591⟩⟩), (o, ⟨⟨-11422786008974170, -11422786008974169⟩, ⟨19384121712198591, 19384121712198592⟩⟩), (o, ⟨⟨11422786008974169, 11422786008974170⟩, ⟨-19384121712198592, -19384121712198591⟩⟩), (o, ⟨⟨414077548287669933, 414077548287669934⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-414077548287669934, -414077548287669933⟩, ⟨0, 0⟩⟩), (o, ⟨⟨210223986053740120, 210223986053740121⟩, ⟨356743733909377173, 356743733909377174⟩⟩), (o, ⟨⟨-210223986053740121, -210223986053740120⟩, ⟨-356743733909377174, -356743733909377173⟩⟩), (o, ⟨⟨-210223986053740121, -210223986053740120⟩, ⟨356743733909377173, 356743733909377174⟩⟩), (o, ⟨⟨210223986053740120, 210223986053740121⟩, ⟨-356743733909377174, -356743733909377173⟩⟩), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z)],
  [(z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, ⟨⟨22501589451845382, 22501589451845383⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-22501589451845383, -22501589451845382⟩, ⟨0, 0⟩⟩), (o, ⟨⟨11423883875552270, 11423883875552271⟩, ⟨19385984758512944, 19385984758512945⟩⟩), (o, ⟨⟨-11423883875552271, -11423883875552270⟩, ⟨-19385984758512945, -19385984758512944⟩⟩), (o, ⟨⟨-11423883875552271, -11423883875552270⟩, ⟨19385984758512944, 19385984758512945⟩⟩), (o, ⟨⟨11423883875552270, 11423883875552271⟩, ⟨-19385984758512945, -19385984758512944⟩⟩), (o, ⟨⟨414104745004386487, 414104745004386488⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-414104745004386488, -414104745004386487⟩, ⟨0, 0⟩⟩), (o, ⟨⟨210237793617611601, 210237793617611602⟩, ⟨356767164926856051, 356767164926856052⟩⟩), (o, ⟨⟨-210237793617611602, -210237793617611601⟩, ⟨-356767164926856052, -356767164926856051⟩⟩), (o, ⟨⟨-210237793617611602, -210237793617611601⟩, ⟨356767164926856051, 356767164926856052⟩⟩), (o, ⟨⟨210237793617611601, 210237793617611602⟩, ⟨-356767164926856052, -356767164926856051⟩⟩), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z)],
  [(z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, ⟨⟨22503752331824417, 22503752331824418⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-22503752331824418, -22503752331824417⟩, ⟨0, 0⟩⟩), (o, ⟨⟨11424981953080088, 11424981953080089⟩, ⟨19387848162802575, 19387848162802576⟩⟩), (o, ⟨⟨-11424981953080089, -11424981953080088⟩, ⟨-19387848162802576, -19387848162802575⟩⟩), (o, ⟨⟨-11424981953080089, -11424981953080088⟩, ⟨19387848162802575, 19387848162802576⟩⟩), (o, ⟨⟨11424981953080088, 11424981953080089⟩, ⟨-19387848162802576, -19387848162802575⟩⟩), (o, ⟨⟨414131944770862222, 414131944770862223⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-414131944770862223, -414131944770862222⟩, ⟨0, 0⟩⟩), (o, ⟨⟨210251602729822359, 210251602729822360⟩, ⟨356790598571819761, 356790598571819762⟩⟩), (o, ⟨⟨-210251602729822360, -210251602729822359⟩, ⟨-356790598571819762, -356790598571819761⟩⟩), (o, ⟨⟨-210251602729822360, -210251602729822359⟩, ⟨356790598571819761, 356790598571819762⟩⟩), (o, ⟨⟨210251602729822359, 210251602729822360⟩, ⟨-356790598571819762, -356790598571819761⟩⟩), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z)],
  [(z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (o, z), (o, z), (o, z), (o, z), (o, z), (o, ⟨⟨22505915627430178, 22505915627430179⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-22505915627430179, -22505915627430178⟩, ⟨0, 0⟩⟩), (o, ⟨⟨11426080241618398, 11426080241618399⟩, ⟨19389711925170615, 19389711925170616⟩⟩), (o, ⟨⟨-11426080241618399, -11426080241618398⟩, ⟨-19389711925170616, -19389711925170615⟩⟩), (o, ⟨⟨-11426080241618399, -11426080241618398⟩, ⟨19389711925170615, 19389711925170616⟩⟩), (o, ⟨⟨11426080241618398, 11426080241618399⟩, ⟨-19389711925170616, -19389711925170615⟩⟩), (o, ⟨⟨414159147587522162, 414159147587522163⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-414159147587522163, -414159147587522162⟩, ⟨0, 0⟩⟩), (o, ⟨⟨210265413390588174, 210265413390588175⟩, ⟨356814034844634478, 356814034844634479⟩⟩), (o, ⟨⟨-210265413390588175, -210265413390588174⟩, ⟨-356814034844634479, -356814034844634478⟩⟩), (o, ⟨⟨-210265413390588175, -210265413390588174⟩, ⟨356814034844634478, 356814034844634479⟩⟩), (o, ⟨⟨210265413390588174, 210265413390588175⟩, ⟨-356814034844634479, -356814034844634478⟩⟩), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z)],
  [(z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (o, z), (o, z), (o, z), (o, z), (o, ⟨⟨22508079338782417, 22508079338782418⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-22508079338782418, -22508079338782417⟩, ⟨0, 0⟩⟩), (o, ⟨⟨11427178741227996, 11427178741227997⟩, ⟨19391576045720236, 19391576045720237⟩⟩), (o, ⟨⟨-11427178741227997, -11427178741227996⟩, ⟨-19391576045720237, -19391576045720236⟩⟩), (o, ⟨⟨-11427178741227997, -11427178741227996⟩, ⟨19391576045720236, 19391576045720237⟩⟩), (o, ⟨⟨11427178741227996, 11427178741227997⟩, ⟨-19391576045720237, -19391576045720236⟩⟩), (o, ⟨⟨414186353454791390, 414186353454791391⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-414186353454791391, -414186353454791390⟩, ⟨0, 0⟩⟩), (o, ⟨⟨210279225600124859, 210279225600124860⟩, ⟨356837473745666428, 356837473745666429⟩⟩), (o, ⟨⟨-210279225600124860, -210279225600124859⟩, ⟨-356837473745666429, -356837473745666428⟩⟩), (o, ⟨⟨-210279225600124860, -210279225600124859⟩, ⟨356837473745666428, 356837473745666429⟩⟩), (o, ⟨⟨210279225600124859, 210279225600124860⟩, ⟨-356837473745666429, -356837473745666428⟩⟩), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z)],
  [(z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (o, z), (o, z), (o, z), (o, ⟨⟨22510243466000935, 22510243466000936⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-22510243466000936, -22510243466000935⟩, ⟨0, 0⟩⟩), (o, ⟨⟨11428277451969705, 11428277451969706⟩, ⟨19393440524554652, 19393440524554653⟩⟩), (o, ⟨⟨-11428277451969706, -11428277451969705⟩, ⟨-19393440524554653, -19393440524554652⟩⟩), (o, ⟨⟨-11428277451969706, -11428277451969705⟩, ⟨19393440524554652, 19393440524554653⟩⟩), (o, ⟨⟨11428277451969705, 11428277451969706⟩, ⟨-19393440524554653, -19393440524554652⟩⟩), (o, ⟨⟨414213562373095048, 414213562373095049⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-414213562373095049, -414213562373095048⟩, ⟨0, 0⟩⟩), (o, ⟨⟨210293039358648255, 210293039358648256⟩, ⟨356860915275281888, 356860915275281889⟩⟩), (o, ⟨⟨-210293039358648256, -210293039358648255⟩, ⟨-356860915275281889, -356860915275281888⟩⟩), (o, ⟨⟨-210293039358648256, -210293039358648255⟩, ⟨356860915275281888, 356860915275281889⟩⟩), (o, ⟨⟨210293039358648255, 210293039358648256⟩, ⟨-356860915275281889, -356860915275281888⟩⟩), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z)],
  [(z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (o, z), (o, z), (o, ⟨⟨22512408009205576, 22512408009205577⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-22512408009205577, -22512408009205576⟩, ⟨0, 0⟩⟩), (o, ⟨⟨11429376373904369, 11429376373904370⟩, ⟨19395305361777111, 19395305361777112⟩⟩), (o, ⟨⟨-11429376373904370, -11429376373904369⟩, ⟨-19395305361777112, -19395305361777111⟩⟩), (o, ⟨⟨-11429376373904370, -11429376373904369⟩, ⟨19395305361777111, 19395305361777112⟩⟩), (o, ⟨⟨11429376373904369, 11429376373904370⟩, ⟨-19395305361777112, -19395305361777111⟩⟩), (o, ⟨⟨414240774342858339, 414240774342858340⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-414240774342858340, -414240774342858339⟩, ⟨0, 0⟩⟩), (o, ⟨⟨210306854666374233, 210306854666374234⟩, ⟨356884359433847184, 356884359433847185⟩⟩), (o, ⟨⟨-210306854666374234, -210306854666374233⟩, ⟨-356884359433847185, -356884359433847184⟩⟩), (o, ⟨⟨-210306854666374234, -210306854666374233⟩, ⟨356884359433847184, 356884359433847185⟩⟩), (o, ⟨⟨210306854666374233, 210306854666374234⟩, ⟨-356884359433847185, -356884359433847184⟩⟩), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z)],
  [(z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (o, z), (o, ⟨⟨22514572968516231, 22514572968516232⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-22514572968516232, -22514572968516231⟩, ⟨0, 0⟩⟩), (o, ⟨⟨11430475507092856, 11430475507092857⟩, ⟨19397170557490907, 19397170557490908⟩⟩), (o, ⟨⟨-11430475507092857, -11430475507092856⟩, ⟨-19397170557490908, -19397170557490907⟩⟩), (o, ⟨⟨-11430475507092857, -11430475507092856⟩, ⟨19397170557490907, 19397170557490908⟩⟩), (o, ⟨⟨11430475507092856, 11430475507092857⟩, ⟨-19397170557490908, -19397170557490907⟩⟩), (o, ⟨⟨414267989364506522, 414267989364506523⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-414267989364506523, -414267989364506522⟩, ⟨0, 0⟩⟩), (o, ⟨⟨210320671523518696, 210320671523518697⟩, ⟨356907806221728696, 356907806221728697⟩⟩), (o, ⟨⟨-210320671523518697, -210320671523518696⟩, ⟨-356907806221728697, -356907806221728696⟩⟩), (o, ⟨⟨-210320671523518697, -210320671523518696⟩, ⟨356907806221728696, 356907806221728697⟩⟩), (o, ⟨⟨210320671523518696, 210320671523518697⟩, ⟨-356907806221728697, -356907806221728696⟩⟩), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z)],
  [(z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (o, ⟨⟨22516738344052838, 22516738344052839⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-22516738344052839, -22516738344052838⟩, ⟨0, 0⟩⟩), (o, ⟨⟨11431574851596056, 11431574851596057⟩, ⟨19399036111799368, 19399036111799369⟩⟩), (o, ⟨⟨-11431574851596057, -11431574851596056⟩, ⟨-19399036111799369, -19399036111799368⟩⟩), (o, ⟨⟨-11431574851596057, -11431574851596056⟩, ⟨19399036111799368, 19399036111799369⟩⟩), (o, ⟨⟨11431574851596056, 11431574851596057⟩, ⟨-19399036111799369, -19399036111799368⟩⟩), (o, ⟨⟨414295207438464918, 414295207438464919⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-414295207438464919, -414295207438464918⟩, ⟨0, 0⟩⟩), (o, ⟨⟨210334489930297574, 210334489930297575⟩, ⟨356931255639292853, 356931255639292854⟩⟩), (o, ⟨⟨-210334489930297575, -210334489930297574⟩, ⟨-356931255639292854, -356931255639292853⟩⟩), (o, ⟨⟨-210334489930297575, -210334489930297574⟩, ⟨356931255639292853, 356931255639292854⟩⟩), (o, ⟨⟨210334489930297574, 210334489930297575⟩, ⟨-356931255639292854, -356931255639292853⟩⟩), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z)],
  [(⟨⟨-22479983485212042, -22479983485212041⟩, ⟨0, 0⟩⟩, o), (⟨⟨-22482142215500152, -22482142215500151⟩, ⟨0, 0⟩⟩, o), (⟨⟨-22484301360219979, -22484301360219978⟩, ⟨0, 0⟩⟩, o), (⟨⟨-22486460919490818, -22486460919490817⟩, ⟨0, 0⟩⟩, o), (⟨⟨-22488620893432009, -22488620893432008⟩, ⟨0, 0⟩⟩, o), (⟨⟨-22490781282162938, -22490781282162937⟩, ⟨0, 0⟩⟩, o), (⟨⟨-22492942085803038, -22492942085803037⟩, ⟨0, 0⟩⟩, o), (⟨⟨-22495103304471785, -22495103304471784⟩, ⟨0, 0⟩⟩, o), (⟨⟨-22497264938288705, -22497264938288704⟩, ⟨0, 0⟩⟩, o), (⟨⟨-22499426987373365, -22499426987373364⟩, ⟨0, 0⟩⟩, o), (⟨⟨-22501589451845383, -22501589451845382⟩, ⟨0, 0⟩⟩, o), (⟨⟨-22503752331824418, -22503752331824417⟩, ⟨0, 0⟩⟩, o), (⟨⟨-22505915627430179, -22505915627430178⟩, ⟨0, 0⟩⟩, o), (⟨⟨-22508079338782418, -22508079338782417⟩, ⟨0, 0⟩⟩, o), (⟨⟨-22510243466000936, -22510243466000935⟩, ⟨0, 0⟩⟩, o), (⟨⟨-22512408009205577, -22512408009205576⟩, ⟨0, 0⟩⟩, o), (⟨⟨-22514572968516232, -22514572968516231⟩, ⟨0, 0⟩⟩, o), (⟨⟨-22516738344052839, -22516738344052838⟩, ⟨0, 0⟩⟩, o), (o, ⟨⟨-1000000000000000000, -999999999999999999⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-496138938356833825, -496138938356833824⟩, ⟨868243142124459193, 868243142124459194⟩⟩), (o, ⟨⟨-868243142124459194, -868243142124459193⟩, ⟨-496138938356833825, -496138938356833824⟩⟩), (o, ⟨⟨-868243142124459194, -868243142124459193⟩, ⟨496138938356833824, 496138938356833825⟩⟩), (o, ⟨⟨-496138938356833825, -496138938356833824⟩, ⟨-868243142124459194, -868243142124459193⟩⟩), (o, ⟨⟨964334741237681539, 964334741237681540⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-967256494730015095, -967256494730015094⟩, ⟨0, 0⟩⟩), (o, ⟨⟨457802251051794875, 457802251051794876⟩, ⟨849638759877106340, 849638759877106341⟩⟩), (o, ⟨⟨-520908285531910629, -520908285531910628⟩, ⟨-814235281268326323, -814235281268326322⟩⟩), (o, ⟨⟨-520908285531910629, -520908285531910628⟩, ⟨814235281268326322, 814235281268326323⟩⟩), (o, ⟨⟨457802251051794875, 457802251051794876⟩, ⟨-849638759877106341, -849638759877106340⟩⟩), (o, ⟨⟨-480144078351167904, -480144078351167903⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-479344531607148238, -479344531607148237⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-478547147925135569, -478547147925135568⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-477751920543723342, -477751920543723341⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-476958842718838297, -476958842718838296⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-476167907723762931, -476167907723762930⟩, ⟨0, 0⟩⟩)],
  [],
  [(⟨⟨-11412914692492267, -11412914692492266⟩, ⟨19367370387259604, 19367370387259605⟩⟩, o), (⟨⟨-11414010663253923, -11414010663253922⟩, ⟨19369230216430899, 19369230216430900⟩⟩, o), (⟨⟨-11415106844419374, -11415106844419373⟩, ⟨19371090402651058, 19371090402651059⟩⟩, o), (⟨⟨-11416203236049185, -11416203236049184⟩, ⟨19372950946022858, 19372950946022859⟩⟩, o), (⟨⟨-11417299838203943, -11417299838203942⟩, ⟨19374811846649115, 19374811846649116⟩⟩, o), (⟨⟨-11418396650944261, -11418396650944260⟩, ⟨19376673104632684, 19376673104632685⟩⟩, o), (⟨⟨-11419493674330773, -11419493674330772⟩, ⟨19378534720076462, 19378534720076463⟩⟩, o), (⟨⟨-11420590908424137, -11420590908424136⟩, ⟨19380396693083383, 19380396693083384⟩⟩, o), (⟨⟨-11421688353285035, -11421688353285034⟩, ⟨19382259023756422, 19382259023756423⟩⟩, o), (⟨⟨-11422786008974170, -11422786008974169⟩, ⟨19384121712198591, 19384121712198592⟩⟩, o), (⟨⟨-11423883875552271, -11423883875552270⟩, ⟨19385984758512944, 19385984758512945⟩⟩, o), (⟨⟨-11424981953080089, -11424981953080088⟩, ⟨19387848162802575, 19387848162802576⟩⟩, o), (⟨⟨-11426080241618399, -11426080241618398⟩, ⟨19389711925170615, 19389711925170616⟩⟩, o), (⟨⟨-11427178741227997, -11427178741227996⟩, ⟨19391576045720236, 19391576045720237⟩⟩, o), (⟨⟨-11428277451969706, -11428277451969705⟩, ⟨19393440524554652, 19393440524554653⟩⟩, o), (⟨⟨-11429376373904370, -11429376373904369⟩, ⟨19395305361777111, 19395305361777112⟩⟩, o), (⟨⟨-11430475507092857, -11430475507092856⟩, ⟨19397170557490907, 19397170557490908⟩⟩, o), (⟨⟨-11431574851596057, -11431574851596056⟩, ⟨19399036111799368, 19399036111799369⟩⟩, o), (⟨⟨496138938356833824, 496138938356833825⟩, ⟨868243142124459193, 868243142124459194⟩⟩, o), (⟨⟨-868243142124459194, -868243142124459193⟩, ⟨496138938356833824, 496138938356833825⟩⟩, o), (o, ⟨⟨-507692307692307693, -507692307692307692⟩, ⟨-861538461538461539, -861538461538461538⟩⟩), (o, ⟨⟨-1000000000000000000, -999999999999999999⟩, ⟨0, 0⟩⟩), (o, ⟨⟨0, 0⟩, ⟨-1000000000000000000, -999999999999999999⟩⟩), (o, ⟨⟨964419151351187476, 964419151351187477⟩, ⟨-36940815646830711, -36940815646830710⟩⟩), (o, ⟨⟨-965956141131989613, -965956141131989612⟩, ⟨-35401533968188101, -35401533968188100⟩⟩), (o, ⟨⟨489585330166822935, 489585330166822936⟩, ⟨830811469374002557, 830811469374002558⟩⟩), (o, ⟨⟨-491068681939853818, -491068681939853817⟩, ⟨-833328672382782236, -833328672382782235⟩⟩), (o, ⟨⟨-521918883361846255, -521918883361846254⟩, ⟨811873818562871951, 811873818562871952⟩⟩), (o, ⟨⟨459383663883669601, 459383663883669602⟩, ⟨-850429262065636288, -850429262065636287⟩⟩), (o, ⟨⟨-243765455162900628, -243765455162900627⟩, ⟨-413662590579467733, -413662590579467732⟩⟩), (o, ⟨⟨-243359531431321414, -243359531431321413⟩, ⟨-412973750307696944, -412973750307696943⟩⟩), (o, ⟨⟨-242954705869684212, -242954705869684211⟩, ⟨-412286773597039875, -412286773597039874⟩⟩), (o, ⟨⟨-242550975045274928, -242550975045274927⟩, ⟨-411601654622284725, -411601654622284724⟩⟩), (o, ⟨⟨-242148335534179444, -242148335534179443⟩, ⟨-410918387573152995, -410918387573152994⟩⟩), (o, ⟨⟨-241746783921295027, -241746783921295026⟩, ⟨-410236966654318833, -410236966654318832⟩⟩)],
  [],
  [(⟨⟨11412914692492266, 11412914692492267⟩, ⟨19367370387259604, 19367370387259605⟩⟩, o), (⟨⟨11414010663253922, 11414010663253923⟩, ⟨19369230216430899, 19369230216430900⟩⟩, o), (⟨⟨11415106844419373, 11415106844419374⟩, ⟨19371090402651058, 19371090402651059⟩⟩, o), (⟨⟨11416203236049184, 11416203236049185⟩, ⟨19372950946022858, 19372950946022859⟩⟩, o), (⟨⟨11417299838203942, 11417299838203943⟩, ⟨19374811846649115, 19374811846649116⟩⟩, o), (⟨⟨11418396650944260, 11418396650944261⟩, ⟨19376673104632684, 19376673104632685⟩⟩, o), (⟨⟨11419493674330772, 11419493674330773⟩, ⟨19378534720076462, 19378534720076463⟩⟩, o), (⟨⟨11420590908424136, 11420590908424137⟩, ⟨19380396693083383, 19380396693083384⟩⟩, o), (⟨⟨11421688353285034, 11421688353285035⟩, ⟨19382259023756422, 19382259023756423⟩⟩, o), (⟨⟨11422786008974169, 11422786008974170⟩, ⟨19384121712198591, 19384121712198592⟩⟩, o), (⟨⟨11423883875552270, 11423883875552271⟩, ⟨19385984758512944, 19385984758512945⟩⟩, o), (⟨⟨11424981953080088, 11424981953080089⟩, ⟨19387848162802575, 19387848162802576⟩⟩, o), (⟨⟨11426080241618398, 11426080241618399⟩, ⟨19389711925170615, 19389711925170616⟩⟩, o), (⟨⟨11427178741227996, 11427178741227997⟩, ⟨19391576045720236, 19391576045720237⟩⟩, o), (⟨⟨11428277451969705, 11428277451969706⟩, ⟨19393440524554652, 19393440524554653⟩⟩, o), (⟨⟨11429376373904369, 11429376373904370⟩, ⟨19395305361777111, 19395305361777112⟩⟩, o), (⟨⟨11430475507092856, 11430475507092857⟩, ⟨19397170557490907, 19397170557490908⟩⟩, o), (⟨⟨11431574851596056, 11431574851596057⟩, ⟨19399036111799368, 19399036111799369⟩⟩, o), (⟨⟨868243142124459193, 868243142124459194⟩, ⟨496138938356833824, 496138938356833825⟩⟩, o), (⟨⟨-496138938356833825, -496138938356833824⟩, ⟨868243142124459193, 868243142124459194⟩⟩, o), (⟨⟨999999999999999999, 1000000000000000000⟩, ⟨0, 0⟩⟩, o), (⟨⟨0, 0⟩, ⟨999999999999999999, 1000000000000000000⟩⟩, o), (o, ⟨⟨507692307692307692, 507692307692307693⟩, ⟨-861538461538461539, -861538461538461538⟩⟩), (o, ⟨⟨965956141131989612, 965956141131989613⟩, ⟨-35401533968188101, -35401533968188100⟩⟩), (o, ⟨⟨-964419151351187477, -964419151351187476⟩, ⟨-36940815646830711, -36940815646830710⟩⟩), (o, ⟨⟨521918883361846254, 521918883361846255⟩, ⟨811873818562871951, 811873818562871952⟩⟩), (o, ⟨⟨-459383663883669602, -459383663883669601⟩, ⟨-850429262065636288, -850429262065636287⟩⟩), (o, ⟨⟨-489585330166822936, -489585330166822935⟩, ⟨830811469374002557, 830811469374002558⟩⟩), (o, ⟨⟨491068681939853817, 491068681939853818⟩, ⟨-833328672382782236, -833328672382782235⟩⟩), (o, ⟨⟨243765455162900627, 243765455162900628⟩, ⟨-413662590579467733, -413662590579467732⟩⟩), (o, ⟨⟨243359531431321413, 243359531431321414⟩, ⟨-412973750307696944, -412973750307696943⟩⟩), (o, ⟨⟨242954705869684211, 242954705869684212⟩, ⟨-412286773597039875, -412286773597039874⟩⟩), (o, ⟨⟨242550975045274927, 242550975045274928⟩, ⟨-411601654622284725, -411601654622284724⟩⟩), (o, ⟨⟨242148335534179443, 242148335534179444⟩, ⟨-410918387573152995, -410918387573152994⟩⟩), (o, ⟨⟨241746783921295026, 241746783921295027⟩, ⟨-410236966654318833, -410236966654318832⟩⟩)],
  [],
  [(⟨⟨-413832915006284468, -413832915006284467⟩, ⟨0, 0⟩⟩, o), (⟨⟨-413860084294284696, -413860084294284695⟩, ⟨0, 0⟩⟩, o), (⟨⟨-413887256628221555, -413887256628221554⟩, ⟨0, 0⟩⟩, o), (⟨⟨-413914432008519536, -413914432008519535⟩, ⟨0, 0⟩⟩, o), (⟨⟨-413941610435603189, -413941610435603188⟩, ⟨0, 0⟩⟩, o), (⟨⟨-413968791909897123, -413968791909897122⟩, ⟨0, 0⟩⟩, o), (⟨⟨-413995976431826008, -413995976431826007⟩, ⟨0, 0⟩⟩, o), (⟨⟨-414023164001814570, -414023164001814569⟩, ⟨0, 0⟩⟩, o), (⟨⟨-414050354620287597, -414050354620287596⟩, ⟨0, 0⟩⟩, o), (⟨⟨-414077548287669934, -414077548287669933⟩, ⟨0, 0⟩⟩, o), (⟨⟨-414104745004386488, -414104745004386487⟩, ⟨0, 0⟩⟩, o), (⟨⟨-414131944770862223, -414131944770862222⟩, ⟨0, 0⟩⟩, o), (⟨⟨-414159147587522163, -414159147587522162⟩, ⟨0, 0⟩⟩, o), (⟨⟨-414186353454791391, -414186353454791390⟩, ⟨0, 0⟩⟩, o), (⟨⟨-414213562373095049, -414213562373095048⟩, ⟨0, 0⟩⟩, o), (⟨⟨-414240774342858340, -414240774342858339⟩, ⟨0, 0⟩⟩, o), (⟨⟨-414267989364506523, -414267989364506522⟩, ⟨0, 0⟩⟩, o), (⟨⟨-414295207438464919, -414295207438464918⟩, ⟨0, 0⟩⟩, o), (⟨⟨-964334741237681540, -964334741237681539⟩, ⟨0, 0⟩⟩, o), (⟨⟨-967256494730015095, -967256494730015094⟩, ⟨0, 0⟩⟩, o), (⟨⟨-964419151351187477, -964419151351187476⟩, ⟨-36940815646830711, -36940815646830710⟩⟩, o), (⟨⟨-965956141131989613, -965956141131989612⟩, ⟨35401533968188100, 35401533968188101⟩⟩, o), (⟨⟨-965956141131989613, -965956141131989612⟩, ⟨-35401533968188101, -35401533968188100⟩⟩, o), (⟨⟨-964419151351187477, -964419151351187476⟩, ⟨36940815646830710, 36940815646830711⟩⟩, o), (o, ⟨⟨-1000000000000000000, -999999999999999999⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-496138938356833825, -496138938356833824⟩, ⟨868243142124459193, 868243142124459194⟩⟩), (o, ⟨⟨-868243142124459194, -868243142124459193⟩, ⟨-496138938356833825, -496138938356833824⟩⟩), (o, ⟨⟨-868243142124459194, -868243142124459193⟩, ⟨496138938356833824, 496138938356833825⟩⟩), (o, ⟨⟨-496138938356833825, -496138938356833824⟩, ⟨-868243142124459194, -868243142124459193⟩⟩), (o, ⟨⟨-999907102048600271, -999907102048600270⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-999814212728031590, -999814212728031589⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-999721332038293623, -999721332038293622⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-999628459979385811, -999628459979385810⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-999535596551307372, -999535596551307371⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-999442741754057301, -999442741754057300⟩, ⟨0, 0⟩⟩)],
  [],
  [(⟨⟨-210099787618575192, -210099787618575191⟩, ⟨356532972928491233, 356532972928491234⟩⟩, o), (⟨⟨-210113581257098384, -210113581257098383⟩, ⟨356556380315076045, 356556380315076046⟩⟩, o), (⟨⟨-210127376442020174, -210127376442020173⟩, ⟨356579790325852416, 356579790325852417⟩⟩, o), (⟨⟨-210141173173556072, -210141173173556071⟩, ⟨356603202961186061, 356603202961186062⟩⟩, o), (⟨⟨-210154971451921619, -210154971451921618⟩, ⟨356626618221442746, 356626618221442747⟩⟩, o), (⟨⟨-210168771277332386, -210168771277332385⟩, ⟨356650036106988290, 356650036106988291⟩⟩, o), (⟨⟨-210182572650003973, -210182572650003972⟩, ⟨356673456618188560, 356673456618188561⟩⟩, o), (⟨⟨-210196375570152013, -210196375570152012⟩, ⟨356696879755409475, 356696879755409476⟩⟩, o), (⟨⟨-210210180037992165, -210210180037992164⟩, ⟨356720305519017005, 356720305519017006⟩⟩, o), (⟨⟨-210223986053740121, -210223986053740120⟩, ⟨356743733909377173, 356743733909377174⟩⟩, o), (⟨⟨-210237793617611602, -210237793617611601⟩, ⟨356767164926856051, 356767164926856052⟩⟩, o), (⟨⟨-210251602729822360, -210251602729822359⟩, ⟨356790598571819761, 356790598571819762⟩⟩, o), (⟨⟨-210265413390588175, -210265413390588174⟩, ⟨356814034844634478, 356814034844634479⟩⟩, o), (⟨⟨-210279225600124860, -210279225600124859⟩, ⟨356837473745666428, 356837473745666429⟩⟩, o), (⟨⟨-210293039358648256, -210293039358648255⟩, ⟨356860915275281888, 356860915275281889⟩⟩, o), (⟨⟨-210306854666374234, -210306854666374233⟩, ⟨356884359433847184, 356884359433847185⟩⟩, o), (⟨⟨-210320671523518697, -210320671523518696⟩, ⟨356907806221728696, 356907806221728697⟩⟩, o), (⟨⟨-210334489930297575, -210334489930297574⟩, ⟨356931255639292853, 356931255639292854⟩⟩, o), (⟨⟨-457802251051794876, -457802251051794875⟩, ⟨849638759877106340, 849638759877106341⟩⟩, o), (⟨⟨-520908285531910629, -520908285531910628⟩, ⟨814235281268326322, 814235281268326323⟩⟩, o), (⟨⟨-489585330166822936, -489585330166822935⟩, ⟨830811469374002557, 830811469374002558⟩⟩, o), (⟨⟨-491068681939853818, -491068681939853817⟩, ⟨833328672382782235, 833328672382782236⟩⟩, o), (⟨⟨-521918883361846255, -521918883361846254⟩, ⟨811873818562871951, 811873818562871952⟩⟩, o), (⟨⟨-459383663883669602, -459383663883669601⟩, ⟨850429262065636287, 850429262065636288⟩⟩, o), (⟨⟨496138938356833824, 496138938356833825⟩, ⟨868243142124459193, 868243142124459194⟩⟩, o), (⟨⟨-868243142124459194, -868243142124459193⟩, ⟨496138938356833824, 496138938356833825⟩⟩, o), (o, ⟨⟨-507692307692307693, -507692307692307692⟩, ⟨-861538461538461539, -861538461538461538⟩⟩), (o, ⟨⟨-1000000000000000000, -999999999999999999⟩, ⟨0, 0⟩⟩), (o, ⟨⟨0, 0⟩, ⟨-1000000000000000000, -999999999999999999⟩⟩), (o, ⟨⟨-507645144116981676, -507645144116981675⟩, ⟨-861458426380332541, -861458426380332540⟩⟩), (o, ⟨⟨-507597984923462192, -507597984923462191⟩, ⟨-861378398657996447, -861378398657996446⟩⟩), (o, ⟨⟨-507550830111749070, -507550830111749069⟩, ⟨-861298378371452967, -861298378371452966⟩⟩), (o, ⟨⟨-507503679681842027, -507503679681842026⟩, ⟨-861218365520701622, -861218365520701621⟩⟩), (o, ⟨⟨-507456533633740666, -507456533633740665⟩, ⟨-861138360105741736, -861138360105741735⟩⟩), (o, ⟨⟨-507409391967444476, -507409391967444475⟩, ⟨-861058362126572444, -861058362126572443⟩⟩)],
  [],
  [(⟨⟨210099787618575191, 210099787618575192⟩, ⟨356532972928491233, 356532972928491234⟩⟩, o), (⟨⟨210113581257098383, 210113581257098384⟩, ⟨356556380315076045, 356556380315076046⟩⟩, o), (⟨⟨210127376442020173, 210127376442020174⟩, ⟨356579790325852416, 356579790325852417⟩⟩, o), (⟨⟨210141173173556071, 210141173173556072⟩, ⟨356603202961186061, 356603202961186062⟩⟩, o), (⟨⟨210154971451921618, 210154971451921619⟩, ⟨356626618221442746, 356626618221442747⟩⟩, o), (⟨⟨210168771277332385, 210168771277332386⟩, ⟨356650036106988290, 356650036106988291⟩⟩, o), (⟨⟨210182572650003972, 210182572650003973⟩, ⟨356673456618188560, 356673456618188561⟩⟩, o), (⟨⟨210196375570152012, 210196375570152013⟩, ⟨356696879755409475, 356696879755409476⟩⟩, o), (⟨⟨210210180037992164, 210210180037992165⟩, ⟨356720305519017005, 356720305519017006⟩⟩, o), (⟨⟨210223986053740120, 210223986053740121⟩, ⟨356743733909377173, 356743733909377174⟩⟩, o), (⟨⟨210237793617611601, 210237793617611602⟩, ⟨356767164926856051, 356767164926856052⟩⟩, o), (⟨⟨210251602729822359, 210251602729822360⟩, ⟨356790598571819761, 356790598571819762⟩⟩, o), (⟨⟨210265413390588174, 210265413390588175⟩, ⟨356814034844634478, 356814034844634479⟩⟩, o), (⟨⟨210279225600124859, 210279225600124860⟩, ⟨356837473745666428, 356837473745666429⟩⟩, o), (⟨⟨210293039358648255, 210293039358648256⟩, ⟨356860915275281888, 356860915275281889⟩⟩, o), (⟨⟨210306854666374233, 210306854666374234⟩, ⟨356884359433847184, 356884359433847185⟩⟩, o), (⟨⟨210320671523518696, 210320671523518697⟩, ⟨356907806221728696, 356907806221728697⟩⟩, o), (⟨⟨210334489930297574, 210334489930297575⟩, ⟨356931255639292853, 356931255639292854⟩⟩, o), (⟨⟨520908285531910628, 520908285531910629⟩, ⟨814235281268326322, 814235281268326323⟩⟩, o), (⟨⟨457802251051794875, 457802251051794876⟩, ⟨849638759877106340, 849638759877106341⟩⟩, o), (⟨⟨521918883361846254, 521918883361846255⟩, ⟨811873818562871951, 811873818562871952⟩⟩, o), (⟨⟨459383663883669601, 459383663883669602⟩, ⟨850429262065636287, 850429262065636288⟩⟩, o), (⟨⟨489585330166822935, 489585330166822936⟩, ⟨830811469374002557, 830811469374002558⟩⟩, o), (⟨⟨491068681939853817, 491068681939853818⟩, ⟨833328672382782235, 833328672382782236⟩⟩, o), (⟨⟨868243142124459193, 868243142124459194⟩, ⟨496138938356833824, 496138938356833825⟩⟩, o), (⟨⟨-496138938356833825, -496138938356833824⟩, ⟨868243142124459193, 868243142124459194⟩⟩, o), (⟨⟨999999999999999999, 1000000000000000000⟩, ⟨0, 0⟩⟩, o), (⟨⟨0, 0⟩, ⟨999999999999999999, 1000000000000000000⟩⟩, o), (o, ⟨⟨507692307692307692, 507692307692307693⟩, ⟨-861538461538461539, -861538461538461538⟩⟩), (o, ⟨⟨507645144116981675, 507645144116981676⟩, ⟨-861458426380332541, -861458426380332540⟩⟩), (o, ⟨⟨507597984923462191, 507597984923462192⟩, ⟨-861378398657996447, -861378398657996446⟩⟩), (o, ⟨⟨507550830111749069, 507550830111749070⟩, ⟨-861298378371452967, -861298378371452966⟩⟩), (o, ⟨⟨507503679681842026, 507503679681842027⟩, ⟨-861218365520701622, -861218365520701621⟩⟩), (o, ⟨⟨507456533633740665, 507456533633740666⟩, ⟨-861138360105741736, -861138360105741735⟩⟩), (o, ⟨⟨507409391967444475, 507409391967444476⟩, ⟨-861058362126572444, -861058362126572443⟩⟩)],
  [],
  [(z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (⟨⟨480144078351167903, 480144078351167904⟩, ⟨0, 0⟩⟩, o), (⟨⟨-480144078351167904, -480144078351167903⟩, ⟨0, 0⟩⟩, o), (⟨⟨243765455162900627, 243765455162900628⟩, ⟨-413662590579467733, -413662590579467732⟩⟩, o), (⟨⟨-243765455162900628, -243765455162900627⟩, ⟨413662590579467732, 413662590579467733⟩⟩, o), (⟨⟨-243765455162900628, -243765455162900627⟩, ⟨-413662590579467733, -413662590579467732⟩⟩, o), (⟨⟨243765455162900627, 243765455162900628⟩, ⟨413662590579467732, 413662590579467733⟩⟩, o), (⟨⟨999907102048600270, 999907102048600271⟩, ⟨0, 0⟩⟩, o), (⟨⟨-999907102048600271, -999907102048600270⟩, ⟨0, 0⟩⟩, o), (⟨⟨507645144116981675, 507645144116981676⟩, ⟨-861458426380332541, -861458426380332540⟩⟩, o), (⟨⟨-507645144116981676, -507645144116981675⟩, ⟨861458426380332540, 861458426380332541⟩⟩, o), (⟨⟨-507645144116981676, -507645144116981675⟩, ⟨-861458426380332541, -861458426380332540⟩⟩, o), (⟨⟨507645144116981675, 507645144116981676⟩, ⟨861458426380332540, 861458426380332541⟩⟩, o), (o, z), (o, z), (o, z), (o, z), (o, z)],
  [(z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (⟨⟨479344531607148237, 479344531607148238⟩, ⟨0, 0⟩⟩, o), (⟨⟨-479344531607148238, -479344531607148237⟩, ⟨0, 0⟩⟩, o), (⟨⟨243359531431321413, 243359531431321414⟩, ⟨-412973750307696944, -412973750307696943⟩⟩, o), (⟨⟨-243359531431321414, -243359531431321413⟩, ⟨412973750307696943, 412973750307696944⟩⟩, o), (⟨⟨-243359531431321414, -243359531431321413⟩, ⟨-412973750307696944, -412973750307696943⟩⟩, o), (⟨⟨243359531431321413, 243359531431321414⟩, ⟨412973750307696943, 412973750307696944⟩⟩, o), (⟨⟨999814212728031589, 999814212728031590⟩, ⟨0, 0⟩⟩, o), (⟨⟨-999814212728031590, -999814212728031589⟩, ⟨0, 0⟩⟩, o), (⟨⟨507597984923462191, 507597984923462192⟩, ⟨-861378398657996447, -861378398657996446⟩⟩, o), (⟨⟨-507597984923462192, -507597984923462191⟩, ⟨861378398657996446, 861378398657996447⟩⟩, o), (⟨⟨-507597984923462192, -507597984923462191⟩, ⟨-861378398657996447, -861378398657996446⟩⟩, o), (⟨⟨507597984923462191, 507597984923462192⟩, ⟨861378398657996446, 861378398657996447⟩⟩, o), (z, o), (o, z), (o, z), (o, z), (o, z)],
  [(z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (⟨⟨478547147925135568, 478547147925135569⟩, ⟨0, 0⟩⟩, o), (⟨⟨-478547147925135569, -478547147925135568⟩, ⟨0, 0⟩⟩, o), (⟨⟨242954705869684211, 242954705869684212⟩, ⟨-412286773597039875, -412286773597039874⟩⟩, o), (⟨⟨-242954705869684212, -242954705869684211⟩, ⟨412286773597039874, 412286773597039875⟩⟩, o), (⟨⟨-242954705869684212, -242954705869684211⟩, ⟨-412286773597039875, -412286773597039874⟩⟩, o), (⟨⟨242954705869684211, 242954705869684212⟩, ⟨412286773597039874, 412286773597039875⟩⟩, o), (⟨⟨999721332038293622, 999721332038293623⟩, ⟨0, 0⟩⟩, o), (⟨⟨-999721332038293623, -999721332038293622⟩, ⟨0, 0⟩⟩, o), (⟨⟨507550830111749069, 507550830111749070⟩, ⟨-861298378371452967, -861298378371452966⟩⟩, o), (⟨⟨-507550830111749070, -507550830111749069⟩, ⟨861298378371452966, 861298378371452967⟩⟩, o), (⟨⟨-507550830111749070, -507550830111749069⟩, ⟨-861298378371452967, -861298378371452966⟩⟩, o), (⟨⟨507550830111749069, 507550830111749070⟩, ⟨861298378371452966, 861298378371452967⟩⟩, o), (z, o), (z, o), (o, z), (o, z), (o, z)],
  [(z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (⟨⟨477751920543723341, 477751920543723342⟩, ⟨0, 0⟩⟩, o), (⟨⟨-477751920543723342, -477751920543723341⟩, ⟨0, 0⟩⟩, o), (⟨⟨242550975045274927, 242550975045274928⟩, ⟨-411601654622284725, -411601654622284724⟩⟩, o), (⟨⟨-242550975045274928, -242550975045274927⟩, ⟨411601654622284724, 411601654622284725⟩⟩, o), (⟨⟨-242550975045274928, -242550975045274927⟩, ⟨-411601654622284725, -411601654622284724⟩⟩, o), (⟨⟨242550975045274927, 242550975045274928⟩, ⟨411601654622284724, 411601654622284725⟩⟩, o), (⟨⟨999628459979385810, 999628459979385811⟩, ⟨0, 0⟩⟩, o), (⟨⟨-999628459979385811, -999628459979385810⟩, ⟨0, 0⟩⟩, o), (⟨⟨507503679681842026, 507503679681842027⟩, ⟨-861218365520701622, -861218365520701621⟩⟩, o), (⟨⟨-507503679681842027, -507503679681842026⟩, ⟨861218365520701621, 861218365520701622⟩⟩, o), (⟨⟨-507503679681842027, -507503679681842026⟩, ⟨-861218365520701622, -861218365520701621⟩⟩, o), (⟨⟨507503679681842026, 507503679681842027⟩, ⟨861218365520701621, 861218365520701622⟩⟩, o), (z, o), (z, o), (z, o), (o, z), (o, z)],
  [(z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (⟨⟨476958842718838296, 476958842718838297⟩, ⟨0, 0⟩⟩, o), (⟨⟨-476958842718838297, -476958842718838296⟩, ⟨0, 0⟩⟩, o), (⟨⟨242148335534179443, 242148335534179444⟩, ⟨-410918387573152995, -410918387573152994⟩⟩, o), (⟨⟨-242148335534179444, -242148335534179443⟩, ⟨410918387573152994, 410918387573152995⟩⟩, o), (⟨⟨-242148335534179444, -242148335534179443⟩, ⟨-410918387573152995, -410918387573152994⟩⟩, o), (⟨⟨242148335534179443, 242148335534179444⟩, ⟨410918387573152994, 410918387573152995⟩⟩, o), (⟨⟨999535596551307371, 999535596551307372⟩, ⟨0, 0⟩⟩, o), (⟨⟨-999535596551307372, -999535596551307371⟩, ⟨0, 0⟩⟩, o), (⟨⟨507456533633740665, 507456533633740666⟩, ⟨-861138360105741736, -861138360105741735⟩⟩, o), (⟨⟨-507456533633740666, -507456533633740665⟩, ⟨861138360105741735, 861138360105741736⟩⟩, o), (⟨⟨-507456533633740666, -507456533633740665⟩, ⟨-861138360105741736, -861138360105741735⟩⟩, o), (⟨⟨507456533633740665, 507456533633740666⟩, ⟨861138360105741735, 861138360105741736⟩⟩, o), (z, o), (z, o), (z, o), (z, o), (o, z)],
  [(z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (⟨⟨476167907723762930, 476167907723762931⟩, ⟨0, 0⟩⟩, o), (⟨⟨-476167907723762931, -476167907723762930⟩, ⟨0, 0⟩⟩, o), (⟨⟨241746783921295026, 241746783921295027⟩, ⟨-410236966654318833, -410236966654318832⟩⟩, o), (⟨⟨-241746783921295027, -241746783921295026⟩, ⟨410236966654318832, 410236966654318833⟩⟩, o), (⟨⟨-241746783921295027, -241746783921295026⟩, ⟨-410236966654318833, -410236966654318832⟩⟩, o), (⟨⟨241746783921295026, 241746783921295027⟩, ⟨410236966654318832, 410236966654318833⟩⟩, o), (⟨⟨999442741754057300, 999442741754057301⟩, ⟨0, 0⟩⟩, o), (⟨⟨-999442741754057301, -999442741754057300⟩, ⟨0, 0⟩⟩, o), (⟨⟨507409391967444475, 507409391967444476⟩, ⟨-861058362126572444, -861058362126572443⟩⟩, o), (⟨⟨-507409391967444476, -507409391967444475⟩, ⟨861058362126572443, 861058362126572444⟩⟩, o), (⟨⟨-507409391967444476, -507409391967444475⟩, ⟨-861058362126572444, -861058362126572443⟩⟩, o), (⟨⟨507409391967444475, 507409391967444476⟩, ⟨861058362126572443, 861058362126572444⟩⟩, o), (z, o), (z, o), (z, o), (z, o), (z, o)]
]

private def st9_1 : List (List CFpIv) := [
  [o, z, z, z, z],
  [z, o, z, z, z],
  [z, z, o, z, z],
  [z, z, z, o, z],
  [z, z, z, z, o],
  [z, z, z, z, o],
  [z, z, z, z, o],
  [z, z, z, z, o],
  [z, z, z, z, o],
  [z, z, z, z, o],
  [z, z, z, z, o],
  [z, z, z, z, o],
  [z, z, z, z, o],
  [z, z, z, z, o],
  [z, z, z, z, o],
  [z, z, z, z, o],
  [z, z, z, z, o],
  [z, z, z, z, o],
  [⟨⟨255525463396, 255525463397⟩, ⟨0, 0⟩⟩, ⟨⟨-45460649082694, -45460649082692⟩, ⟨0, 0⟩⟩, ⟨⟨3032971616032474, 3032971616032477⟩, ⟨0, 0⟩⟩, ⟨⟨-89932887980422991, -89932887980422987⟩, ⟨0, 0⟩⟩, o],
  [o],
  [⟨⟨-135562706189, -135562706187⟩, ⟨216601050631, 216601050633⟩⟩, ⟨⟨45444426438686, 45444426438690⟩, ⟨1214380779864, 1214380779868⟩⟩, ⟨⟨-1469465774678932, -1469465774678926⟩, ⟨-2653222033812082, -2653222033812076⟩⟩, ⟨⟨-45658235436214749, -45658235436214745⟩, ⟨77480641952364419, 77480641952364423⟩⟩, o],
  [o],
  [⟨⟨-135562706189, -135562706187⟩, ⟨-216601050633, -216601050631⟩⟩, ⟨⟨-45444426438690, -45444426438686⟩, ⟨1214380779864, 1214380779868⟩⟩, ⟨⟨-1469465774678932, -1469465774678926⟩, ⟨2653222033812076, 2653222033812082⟩⟩, ⟨⟨45658235436214745, 45658235436214749⟩, ⟨77480641952364419, 77480641952364423⟩⟩, o],
  [o],
  [⟨⟨29340749003051926, 29340749003051928⟩, ⟨0, 0⟩⟩, ⟨⟨-283572028348314071, -283572028348314065⟩, ⟨0, 0⟩⟩, ⟨⟨1027748496324905242, 1027748496324905250⟩, ⟨0, 0⟩⟩, ⟨⟨-1655494687937310255, -1655494687937310251⟩, ⟨0, 0⟩⟩, o],
  [o],
  [⟨⟨-15566007722079503, -15566007722079498⟩, ⟨24871247569357149, 24871247569357154⟩⟩, ⟨⟨283470835599008155, 283470835599008167⟩, ⟨7575000090899337, 7575000090899349⟩⟩, ⟨⟨-497941105793391968, -497941105793391955⟩, ⟨-899067086962568003, -899067086962567990⟩⟩, ⟨⟨-840481918491249822, -840481918491249818⟩, ⟨1426272346530605755, 1426272346530605759⟩⟩, o],
  [o],
  [⟨⟨-15566007722079503, -15566007722079498⟩, ⟨-24871247569357154, -24871247569357149⟩⟩, ⟨⟨-283470835599008167, -283470835599008155⟩, ⟨7575000090899337, 7575000090899349⟩⟩, ⟨⟨-497941105793391968, -497941105793391955⟩, ⟨899067086962567990, 899067086962568003⟩⟩, ⟨⟨840481918491249818, 840481918491249822⟩, ⟨1426272346530605755, 1426272346530605759⟩⟩, o],
  [o],
  [z, z, z, z, o],
  [z, z, z, z, o],
  [z, z, z, z, o],
  [z, z, z, z, o],
  [z, z, z, z, o],
  [z, z, z, z, o]
]

private def st9_2 : List (List CFpIv) := [
  [o, z, z, z, z, z, z, z, z],
  [z, o, z, z, z, z, z, z, z],
  [z, z, o, z, z, z, z, z, z],
  [z, z, z, o, z, z, z, z, z],
  [z, z, z, z, o, z, z, z, z],
  [z, z, z, z, z, o, z, z, z],
  [z, z, z, z, z, z, o, z, z],
  [z, z, z, z, z, z, z, o, z],
  [z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, o],
  [⟨⟨65393, 65394⟩, ⟨0, 0⟩⟩, ⟨⟨-23263971, -23263969⟩, ⟨0, 0⟩⟩, ⟨⟨3620844754, 3620844757⟩, ⟨0, 0⟩⟩, ⟨⟨-322031184093, -322031184089⟩, ⟨0, 0⟩⟩, ⟨⟨17900533205088, 17900533205094⟩, ⟨0, 0⟩⟩, ⟨⟨-636816015616924, -636816015616918⟩, ⟨0, 0⟩⟩, ⟨⟨14159307096254807, 14159307096254814⟩, ⟨0, 0⟩⟩, ⟨⟨-179900335546292761, -179900335546292753⟩, ⟨0, 0⟩⟩, o],
  [o],
  [⟨⟨-28584, -28582⟩, ⟨-58817, -58815⟩⟩, ⟨⟨-12864501, -12864497⟩, ⟨19383418, 19383422⟩⟩, ⟨⟨3615677276, 3615677282⟩, ⟨193376697, 193376704⟩⟩, ⟨⟨-148442203075, -148442203067⟩, ⟨-285777878566, -285777878558⟩⟩, ⟨⟨-9496684562176, -9496684562166⟩, ⟨15173729645444, 15173729645455⟩⟩, ⟨⟨636588767662320, 636588767662333⟩, ⟨17011132601053, 17011132601065⟩⟩, ⟨⟨-6860142396694349, -6860142396694335⟩, ⟨-12386461308345044, -12386461308345030⟩⟩, ⟨⟨-91334016508117863, -91334016508117855⟩, ⟨154991058316806063, 154991058316806071⟩⟩, o],
  [o],
  [⟨⟨-28584, -28582⟩, ⟨58815, 58817⟩⟩, ⟨⟨12864497, 12864501⟩, ⟨19383418, 19383422⟩⟩, ⟨⟨3615677276, 3615677282⟩, ⟨-193376704, -193376697⟩⟩, ⟨⟨148442203067, 148442203075⟩, ⟨-285777878566, -285777878558⟩⟩, ⟨⟨-9496684562176, -9496684562166⟩, ⟨-15173729645455, -15173729645444⟩⟩, ⟨⟨-636588767662333, -636588767662320⟩, ⟨17011132601053, 17011132601065⟩⟩, ⟨⟨-6860142396694349, -6860142396694335⟩, ⟨12386461308345030, 12386461308345044⟩⟩, ⟨⟨91334016508117855, 91334016508117863⟩, ⟨154991058316806063, 154991058316806071⟩⟩, o],
  [o],
  [⟨⟨861784430026571, 861784430026573⟩, ⟨0, 0⟩⟩, ⟨⟨-16655735093814655, -16655735093814651⟩, ⟨0, 0⟩⟩, ⟨⟨140833840420835678, 140833840420835689⟩, ⟨0, 0⟩⟩, ⟨⟨-680475024088255822, -680475024088255797⟩, ⟨0, 0⟩⟩, ⟨⟨2054931610928142636, 2054931610928142675⟩, ⟨0, 0⟩⟩, ⟨⟨-3971572810128197208, -3971572810128197164⟩, ⟨0, 0⟩⟩, ⟨⟨4797419550140011794, 4797419550140011823⟩, ⟨0, 0⟩⟩, ⟨⟨-3311424230716451145, -3311424230716451137⟩, ⟨0, 0⟩⟩, o],
  [o],
  [⟨⟨-376673868700558, -376673868700553⟩, ⟨-775105928550662, -775105928550657⟩⟩, ⟨⟨-9210280457441681, -9210280457441666⟩, ⟨13877472587275997, 13877472587276014⟩⟩, ⟨⟨140632849924147126, 140632849924147162⟩, ⟨7521444667995456, 7521444667995495⟩⟩, ⟨⟨-313669037968059035, -313669037968058965⟩, ⟨-603869185360624878, -603869185360624808⟩⟩, ⟨⟨-1090193073146344953, -1090193073146344860⟩, ⟨1741902118046665547, 1741902118046665642⟩⟩, ⟨⟨3970155553376653898, 3970155553376653984⟩, ⟨106091791115522775, 106091791115522862⟩⟩, ⟨⟨-2324335578493870836, -2324335578493870788⟩, ⟨-4196748557944966564, -4196748557944966519⟩⟩, ⟨⟨-1681184609440659813, -1681184609440659805⟩, ⟨2852919337232634826, 2852919337232634834⟩⟩, o],
  [o],
  [⟨⟨-376673868700558, -376673868700553⟩, ⟨775105928550657, 775105928550662⟩⟩, ⟨⟨9210280457441666, 9210280457441681⟩, ⟨13877472587275997, 13877472587276014⟩⟩, ⟨⟨140632849924147126, 140632849924147162⟩, ⟨-7521444667995495, -7521444667995456⟩⟩, ⟨⟨313669037968058965, 313669037968059035⟩, ⟨-603869185360624878, -603869185360624808⟩⟩, ⟨⟨-1090193073146344953, -1090193073146344860⟩, ⟨-1741902118046665642, -1741902118046665547⟩⟩, ⟨⟨-3970155553376653984, -3970155553376653898⟩, ⟨106091791115522775, 106091791115522862⟩⟩, ⟨⟨-2324335578493870836, -2324335578493870788⟩, ⟨4196748557944966519, 4196748557944966564⟩⟩, ⟨⟨1681184609440659805, 1681184609440659813⟩, ⟨2852919337232634826, 2852919337232634834⟩⟩, o],
  [o],
  [z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, o]
]

private def st9_3 : List (List CFpIv) := [
  [o, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, o, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, o, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, o, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, o, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, o, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, o, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, o, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, o, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, o, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, o, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, o, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, o],
  [⟨⟨0, 1⟩, ⟨0, 0⟩⟩, ⟨⟨-10, -8⟩, ⟨0, 0⟩⟩, ⟨⟨2186, 2189⟩, ⟨0, 0⟩⟩, ⟨⟨-324081, -324077⟩, ⟨0, 0⟩⟩, ⟨⟨32419675, 32419680⟩, ⟨0, 0⟩⟩, ⟨⟨-2306233344, -2306233337⟩, ⟨0, 0⟩⟩, ⟨⟨119625732793, 119625732800⟩, ⟨0, 0⟩⟩, ⟨⟨-4558819448930, -4558819448922⟩, ⟨0, 0⟩⟩, ⟨⟨126679685431130, 126679685431140⟩, ⟨0, 0⟩⟩, ⟨⟨-2503220001719232, -2503220001719220⟩, ⟨0, 0⟩⟩, ⟨⟨33388340425652618, 33388340425652631⟩, ⟨0, 0⟩⟩, ⟨⟨-269902369255624632, -269902369255624620⟩, ⟨0, 0⟩⟩, o],
  [o],
  [⟨⟨-1, 2⟩, ⟨-1, 2⟩⟩, ⟨⟨-5, -1⟩, ⟨-11, -7⟩⟩, ⟨⟨-1260, -1254⟩, ⟨1785, 1792⟩⟩, ⟨⟨323033, 323044⟩, ⟨25941, 25951⟩⟩, ⟨⟨-14170190, -14170180⟩, ⟨-29158903, -29158892⟩⟩, ⟨⟨-1275299822, -1275299809⟩, ⟨1921541720, 1921541732⟩⟩, ⟨⟨119455009365, 119455009379⟩, ⟨6388793532, 6388793550⟩⟩, ⟨⟨-2101415129435, -2101415129416⟩, ⟨-4045601218833, -4045601218813⟩⟩, ⟨⟨-67206769719712, -67206769719692⟩, ⟨107382460414966, 107382460414989⟩⟩, ⟨⟨2502326727034941, 2502326727034966⟩, ⟨66867990651285, 66867990651308⟩⟩, ⟨⟨-16176552154156445, -16176552154156419⟩, ⟨-29207883127387492, -29207883127387468⟩⟩, ⟨⟨-137027356699009428, -137027356699009416⟩, ⟨232531271974076595, 232531271974076607⟩⟩, o],
  [o],
  [⟨⟨-1, 2⟩, ⟨-2, 1⟩⟩, ⟨⟨1, 5⟩, ⟨-11, -7⟩⟩, ⟨⟨-1260, -1254⟩, ⟨-1792, -1785⟩⟩, ⟨⟨-323044, -323033⟩, ⟨25941, 25951⟩⟩, ⟨⟨-14170190, -14170180⟩, ⟨29158892, 29158903⟩⟩, ⟨⟨1275299809, 1275299822⟩, ⟨1921541720, 1921541732⟩⟩, ⟨⟨119455009365, 119455009379⟩, ⟨-6388793550, -6388793532⟩⟩, ⟨⟨2101415129416, 2101415129435⟩, ⟨-4045601218833, -4045601218813⟩⟩, ⟨⟨-67206769719712, -67206769719692⟩, ⟨-107382460414989, -107382460414966⟩⟩, ⟨⟨-2502326727034966, -2502326727034941⟩, ⟨66867990651285, 66867990651308⟩⟩, ⟨⟨-16176552154156445, -16176552154156419⟩, ⟨29207883127387468, 29207883127387492⟩⟩, ⟨⟨137027356699009416, 137027356699009428⟩, ⟨232531271974076595, 232531271974076607⟩⟩, o],
  [o],
  [⟨⟨25338588946737, 25338588946738⟩, ⟨0, 0⟩⟩, ⟨⟨-734483112211638, -734483112211633⟩, ⟨0, 0⟩⟩, ⟨⟨9758041131319472, 9758041131319482⟩, ⟨0, 0⟩⟩, ⟨⟨-78570501995615154, -78570501995615134⟩, ⟨0, 0⟩⟩, ⟨⟨427031765756154822, 427031765756154861⟩, ⟨0, 0⟩⟩, ⟨⟨-1650434521693295982, -1650434521693295905⟩, ⟨0, 0⟩⟩, ⟨⟨4651180791439608100, 4651180791439608236⟩, ⟨0, 0⟩⟩, ⟨⟨-9630183473985321953, -9630183473985321762⟩, ⟨0, 0⟩⟩, ⟨⟨14538938745596549307, 14538938745596549507⟩, ⟨0, 0⟩⟩, ⟨⟨-15608756830524694691, -15608756830524694548⟩, ⟨0, 0⟩⟩, ⟨⟨11311174269363288807, 11311174269363288870⟩, ⟨0, 0⟩⟩, ⟨⟨-4967788823399657387, -4967788823399657375⟩, ⟨0, 0⟩⟩, o],
  [o],
  [⟨⟨25194044667716, 25194044667720⟩, ⟨2702628922502, 2702628922507⟩⟩, ⟨⟨-303270991282166, -303270991282150⟩, ⟨-668948539105092, -668948539105076⟩⟩, ⟨⟨-5611255694735418, -5611255694735378⟩, ⟨7983306097652895, 7983306097652938⟩⟩, ⟨⟨78318280915567998, 78318280915568091⟩, ⟨6290521303765912, 6290521303766010⟩⟩, ⟨⟨-186649586208514731, -186649586208514534⟩, ⟨-384080800005688697, -384080800005688502⟩⟩, ⟨⟨-912656495544526271, -912656495544525924⟩, ⟨1375133532256908680, 1375133532256909028⟩⟩, ⟨⟨4644542875902644848, 4644542875902645348⟩, ⟨248403358589948169, 248403358589948672⟩⟩, ⟨⟨-4439090751035560240, -4439090751035559679⟩, ⟨-8546046281567316400, -8546046281567315839⟩⟩, ⟨⟨-7713273875907407479, -7713273875907407011⟩, ⟨12324209750059144594, 12324209750059145061⟩⟩, ⟨⟨15603186841742204111, 15603186841742204390⟩, ⟨416953446003565300, 416953446003565580⟩⟩, ⟨⟨-5480230468493882244, -5480230468493882145⟩, ⟨-9894934934808690122, -9894934934808690024⟩⟩, ⟨⟨-2522108171879826061, -2522108171879826049⟩, ⟨4279941140159704816, 4279941140159704828⟩⟩, o],
  [o],
  [⟨⟨25194044667716, 25194044667720⟩, ⟨-2702628922507, -2702628922502⟩⟩, ⟨⟨303270991282150, 303270991282166⟩, ⟨-668948539105092, -668948539105076⟩⟩, ⟨⟨-5611255694735418, -5611255694735378⟩, ⟨-7983306097652938, -7983306097652895⟩⟩, ⟨⟨-78318280915568091, -78318280915567998⟩, ⟨6290521303765912, 6290521303766010⟩⟩, ⟨⟨-186649586208514731, -186649586208514534⟩, ⟨384080800005688502, 384080800005688697⟩⟩, ⟨⟨912656495544525924, 912656495544526271⟩, ⟨1375133532256908680, 1375133532256909028⟩⟩, ⟨⟨4644542875902644848, 4644542875902645348⟩, ⟨-248403358589948672, -248403358589948169⟩⟩, ⟨⟨4439090751035559679, 4439090751035560240⟩, ⟨-8546046281567316400, -8546046281567315839⟩⟩, ⟨⟨-7713273875907407479, -7713273875907407011⟩, ⟨-12324209750059145061, -12324209750059144594⟩⟩, ⟨⟨-15603186841742204390, -15603186841742204111⟩, ⟨416953446003565300, 416953446003565580⟩⟩, ⟨⟨-5480230468493882244, -5480230468493882145⟩, ⟨9894934934808690024, 9894934934808690122⟩⟩, ⟨⟨2522108171879826049, 2522108171879826061⟩, ⟨4279941140159704816, 4279941140159704828⟩⟩, o],
  [o],
  [z, z, z, z, z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, o]
]

private def st9_4 : List (List CFpIv) := [
  [o, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, o, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, o, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, o, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, o, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, o, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, o, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, o, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, o, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, o, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, o, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, o, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, o, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, o, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, o, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, o, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, o],
  [⟨⟨0, 1⟩, ⟨0, 0⟩⟩, ⟨⟨-2, 0⟩, ⟨0, 0⟩⟩, ⟨⟨0, 3⟩, ⟨0, 0⟩⟩, ⟨⟨-4, 0⟩, ⟨0, 0⟩⟩, ⟨⟨29, 35⟩, ⟨0, 0⟩⟩, ⟨⟨-3266, -3260⟩, ⟨0, 0⟩⟩, ⟨⟨265833, 265840⟩, ⟨0, 0⟩⟩, ⟨⟨-16881320, -16881311⟩, ⟨0, 0⟩⟩, ⟨⟨844208891, 844208901⟩, ⟨0, 0⟩⟩, ⟨⟨-33357116324, -33357116313⟩, ⟨0, 0⟩⟩, ⟨⟨1037952863651, 1037952863662⟩, ⟨0, 0⟩⟩, ⟨⟨-25166758580134, -25166758580122⟩, ⟨0, 0⟩⟩, ⟨⟨466130072027835, 466130072027849⟩, ⟨0, 0⟩⟩, ⟨⟨-6375508602082352, -6375508602082335⟩, ⟨0, 0⟩⟩, ⟨⟨60729418746720434, 60729418746720455⟩, ⟨0, 0⟩⟩, ⟨⟨-359939015697043742, -359939015697043726⟩, ⟨0, 0⟩⟩, o],
  [o],
  [⟨⟨-2, 2⟩, ⟨-2, 2⟩⟩, ⟨⟨-4, 4⟩, ⟨-4, 4⟩⟩, ⟨⟨-6, 6⟩, ⟨-6, 6⟩⟩, ⟨⟨-8, 7⟩, ⟨-7, 8⟩⟩, ⟨⟨25, 38⟩, ⟨-3, 8⟩⟩, ⟨⟨-1352, -1339⟩, ⟨-2978, -2966⟩⟩, ⟨⟨-152875, -152858⟩, ⟨217478, 217495⟩⟩, ⟨⟨16827114, 16827134⟩, ⟨1351544, 1351564⟩⟩, ⟨⟨-368991859, -368991839⟩, ⟨-759298157, -759298133⟩⟩, ⟨⟨-18445802303, -18445802281⟩, ⟨27792977284, 27792977306⟩⟩, ⟨⟨1036471553037, 1036471553061⟩, ⟨55433445587, 55433445617⟩⟩, ⟨⟨-11600768100475, -11600768100447⟩, ⟨-22333560327690, -22333560327658⟩⟩, ⟨⟨-247293765401989, -247293765401959⟩, ⟨395124078792955, 395124078792990⟩⟩, ⟨⟨6373233500241620, 6373233500241654⟩, ⟨170307623504311, 170307623504345⟩⟩, ⟨⟨-29423223709949546, -29423223709949507⟩, ⟨-53125664304823392, -53125664304823358⟩⟩, ⟨⟨-182738269507729900, -182738269507729884⟩, ⟨310101305831299209, 310101305831299225⟩⟩, o],
  [o],
  [⟨⟨-2, 2⟩, ⟨-2, 2⟩⟩, ⟨⟨-4, 4⟩, ⟨-4, 4⟩⟩, ⟨⟨-6, 6⟩, ⟨-6, 6⟩⟩, ⟨⟨-7, 8⟩, ⟨-7, 8⟩⟩, ⟨⟨25, 38⟩, ⟨-8, 3⟩⟩, ⟨⟨1339, 1352⟩, ⟨-2978, -2966⟩⟩, ⟨⟨-152875, -152858⟩, ⟨-217495, -217478⟩⟩, ⟨⟨-16827134, -16827114⟩, ⟨1351544, 1351564⟩⟩, ⟨⟨-368991859, -368991839⟩, ⟨759298133, 759298157⟩⟩, ⟨⟨18445802281, 18445802303⟩, ⟨27792977284, 27792977306⟩⟩, ⟨⟨1036471553037, 1036471553061⟩, ⟨-55433445617, -55433445587⟩⟩, ⟨⟨11600768100447, 11600768100475⟩, ⟨-22333560327690, -22333560327658⟩⟩, ⟨⟨-247293765401989, -247293765401959⟩, ⟨-395124078792990, -395124078792955⟩⟩, ⟨⟨-6373233500241654, -6373233500241620⟩, ⟨170307623504311, 170307623504345⟩⟩, ⟨⟨-29423223709949546, -29423223709949507⟩, ⟨53125664304823358, 53125664304823392⟩⟩, ⟨⟨182738269507729884, 182738269507729900⟩, ⟨310101305831299209, 310101305831299225⟩⟩, o],
  [o],
  [⟨⟨745800430470, 745800430472⟩, ⟨0, 0⟩⟩, ⟨⟨-28820646452775, -28820646452771⟩, ⟨0, 0⟩⟩, ⟨⟨522066810040617, 522066810040626⟩, ⟨0, 0⟩⟩, ⟨⟨-5884288606137529, -5884288606137511⟩, ⟨0, 0⟩⟩, ⟨⟨46188985551242282, 46188985551242319⟩, ⟨0, 0⟩⟩, ⟨⟨-267738459713145490, -267738459713145422⟩, ⟨0, 0⟩⟩, ⟨⟨1185532018132940189, 1185532018132940313⟩, ⟨0, 0⟩⟩, ⟨⟨-4090499437215185356, -4090499437215185119⟩, ⟨0, 0⟩⟩, ⟨⟨11114500421808807930, 11114500421808808357⟩, ⟨0, 0⟩⟩, ⟨⟨-23861542162663281741, -23861542162663281073⟩, ⟨0, 0⟩⟩, ⟨⟨40342019057856193306, 40342019057856194161⟩, ⟨0, 0⟩⟩, ⟨⟨-53146818836717894551, -53146818836717893695⟩, ⟨0, 0⟩⟩, ⟨⟨53484397652444601267, 53484397652444601910⟩, ⟨0, 0⟩⟩, ⟨⟨-39747042740564927142, -39747042740564926803⟩, ⟨0, 0⟩⟩, ⟨⟨20571175622536792213, 20571175622536792325⟩, ⟨0, 0⟩⟩, ⟨⟨-6624588661157924330, -6624588661157924314⟩, ⟨0, 0⟩⟩, o],
  [o],
  [⟨⟨-460838841495, -460838841490⟩, ⟨586383700541, 586383700545⟩⟩, ⟨⟨28563896905075, 28563896905089⟩, ⟨3838418365877, 3838418365892⟩⟩, ⟨⟨-202784997763540, -202784997763498⟩, ⟨-481073797694345, -481073797694303⟩⟩, ⟨⟨-3511086601327300, -3511086601327199⟩, ⟨4721982981576661, 4721982981576761⟩⟩, ⟨⟨45925499939269889, 45925499939270120⟩, ⟨4926544588347859, 4926544588348091⟩⟩, ⟨⟨-110550272336510279, -110550272336509784⟩, ⟨-243849379937475331, -243849379937474836⟩⟩, ⟨⟨-681727326060173458, -681727326060172487⟩, ⟨969914438969339105, 969914438969340076⟩⟩, ⟨⟨4077368425451456058, 4077368425451457744⟩, ⟨327494074739152747, 327494074739154438⟩⟩, ⟨⟨-4857992006687328619, -4857992006687326105⟩, ⟨-9996601086836977195, -9996601086836974686⟩⟩, ⟨⟨-13194944217551435911, -13194944217551432803⟩, ⟨19881313877011835283, 19881313877011838388⟩⟩, ⟨⟨40284445093930846654, 40284445093930849791⟩, ⟨2154526662286439225, 2154526662286442366⟩⟩, ⟨⟨-24498344458582065450, -24498344458582062967⟩, ⟨-47163709260951619502, -47163709260951617017⟩⟩, ⟨⟨-28374822564418021551, -28374822564418020068⟩, ⟨45337073534609790440, 45337073534609791920⟩⟩, ⟨⟨39732858998412626750, 39732858998412627395⟩, ⟨1061754412543592933, 1061754412543593581⟩⟩, ⟨⟨-9966673727652737082, -9966673727652736914⟩, ⟨-17995518367075972681, -17995518367075972513⟩⟩, ⟨⟨-3363252704895561586, -3363252704895561570⟩, ⟨5707337923459134794, 5707337923459134810⟩⟩, o],
  [o],
  [⟨⟨-460838841495, -460838841490⟩, ⟨-586383700545, -586383700541⟩⟩, ⟨⟨-28563896905089, -28563896905075⟩, ⟨3838418365877, 3838418365892⟩⟩, ⟨⟨-202784997763540, -202784997763498⟩, ⟨481073797694303, 481073797694345⟩⟩, ⟨⟨3511086601327199, 3511086601327300⟩, ⟨4721982981576661, 4721982981576761⟩⟩, ⟨⟨45925499939269889, 45925499939270120⟩, ⟨-4926544588348091, -4926544588347859⟩⟩, ⟨⟨110550272336509784, 110550272336510279⟩, ⟨-243849379937475331, -243849379937474836⟩⟩, ⟨⟨-681727326060173458, -681727326060172487⟩, ⟨-969914438969340076, -969914438969339105⟩⟩, ⟨⟨-4077368425451457744, -4077368425451456058⟩, ⟨327494074739152747, 327494074739154438⟩⟩, ⟨⟨-4857992006687328619, -4857992006687326105⟩, ⟨9996601086836974686, 9996601086836977195⟩⟩, ⟨⟨13194944217551432803, 13194944217551435911⟩, ⟨19881313877011835283, 19881313877011838388⟩⟩, ⟨⟨40284445093930846654, 40284445093930849791⟩, ⟨-2154526662286442366, -2154526662286439225⟩⟩, ⟨⟨24498344458582062967, 24498344458582065450⟩, ⟨-47163709260951619502, -47163709260951617017⟩⟩, ⟨⟨-28374822564418021551, -28374822564418020068⟩, ⟨-45337073534609791920, -45337073534609790440⟩⟩, ⟨⟨-39732858998412627395, -39732858998412626750⟩, ⟨1061754412543592933, 1061754412543593581⟩⟩, ⟨⟨-9966673727652737082, -9966673727652736914⟩, ⟨17995518367075972513, 17995518367075972681⟩⟩, ⟨⟨3363252704895561570, 3363252704895561586⟩, ⟨5707337923459134794, 5707337923459134810⟩⟩, o],
  [o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, o]
]

private def st9_5 : List (List CFpIv) := [
  [o, ⟨⟨11412914692492265, 11412914692492268⟩, ⟨19367370387259604, 19367370387259605⟩⟩, ⟨⟨-505349657495408, -505349657495405⟩, ⟨-1, 1⟩⟩, ⟨⟨-5767512530876, -5767512530875⟩, ⟨-9787293991789, -9787293991788⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, o, ⟨⟨11414010663253921, 11414010663253924⟩, ⟨19369230216430899, 19369230216430900⟩⟩, ⟨⟨-505446718597976, -505446718597973⟩, ⟨-1, 1⟩⟩, ⟨⟨-5769174235784, -5769174235783⟩, ⟨-9790113854664, -9790113854663⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, o, ⟨⟨11415106844419372, 11415106844419375⟩, ⟨19371090402651058, 19371090402651059⟩⟩, ⟨⟨-505543807657191, -505543807657188⟩, ⟨-1, 1⟩⟩, ⟨⟨-5770836578942, -5770836578941⟩, ⟨-9792934800628, -9792934800627⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, o, ⟨⟨11416203236049183, 11416203236049186⟩, ⟨19372950946022858, 19372950946022859⟩⟩, ⟨⟨-505640924683789, -505640924683786⟩, ⟨-1, 1⟩⟩, ⟨⟨-5772499560654, -5772499560653⟩, ⟨-9795756830201, -9795756830200⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, o, ⟨⟨11417299838203941, 11417299838203944⟩, ⟨19374811846649115, 19374811846649116⟩⟩, ⟨⟨-505738069688508, -505738069688505⟩, ⟨-1, 1⟩⟩, ⟨⟨-5774163181229, -5774163181228⟩, ⟨-9798579943903, -9798579943902⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, o, ⟨⟨11418396650944259, 11418396650944262⟩, ⟨19376673104632684, 19376673104632685⟩⟩, ⟨⟨-505835242682092, -505835242682089⟩, ⟨-1, 1⟩⟩, ⟨⟨-5775827440971, -5775827440970⟩, ⟨-9801404142254, -9801404142253⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, o, ⟨⟨11419493674330771, 11419493674330774⟩, ⟨19378534720076462, 19378534720076463⟩⟩, ⟨⟨-505932443675291, -505932443675288⟩, ⟨-1, 1⟩⟩, ⟨⟨-5777492340189, -5777492340188⟩, ⟨-9804229425775, -9804229425774⟩⟩, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, o, ⟨⟨11420590908424135, 11420590908424138⟩, ⟨19380396693083383, 19380396693083384⟩⟩, ⟨⟨-506029672678859, -506029672678856⟩, ⟨-1, 1⟩⟩, ⟨⟨-5779157879190, -5779157879188⟩, ⟨-9807055794988, -9807055794987⟩⟩, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, o, ⟨⟨11421688353285033, 11421688353285036⟩, ⟨19382259023756422, 19382259023756423⟩⟩, ⟨⟨-506126929703556, -506126929703553⟩, ⟨-1, 1⟩⟩, ⟨⟨-5780824058280, -5780824058278⟩, ⟨-9809883250413, -9809883250412⟩⟩, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, o, ⟨⟨11422786008974168, 11422786008974171⟩, ⟨19384121712198591, 19384121712198592⟩⟩, ⟨⟨-506224214760146, -506224214760143⟩, ⟨-1, 1⟩⟩, ⟨⟨-5782490877767, -5782490877766⟩, ⟨-9812711792573, -9812711792572⟩⟩, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, o, ⟨⟨11423883875552269, 11423883875552272⟩, ⟨19385984758512944, 19385984758512945⟩⟩, ⟨⟨-506321527859401, -506321527859398⟩, ⟨-1, 1⟩⟩, ⟨⟨-5784158337958, -5784158337957⟩, ⟨-9815541421990, -9815541421989⟩⟩, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨11424981953080087, 11424981953080090⟩, ⟨19387848162802575, 19387848162802576⟩⟩, ⟨⟨-506418869012094, -506418869012091⟩, ⟨-1, 1⟩⟩, ⟨⟨-5785826439163, -5785826439162⟩, ⟨-9818372139185, -9818372139184⟩⟩, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨11426080241618397, 11426080241618400⟩, ⟨19389711925170615, 19389711925170616⟩⟩, ⟨⟨-506516238229007, -506516238229004⟩, ⟨-1, 1⟩⟩, ⟨⟨-5787495181688, -5787495181687⟩, ⟨-9821203944682, -9821203944681⟩⟩, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨11427178741227995, 11427178741227998⟩, ⟨19391576045720236, 19391576045720237⟩⟩, ⟨⟨-506613635520925, -506613635520922⟩, ⟨-1, 1⟩⟩, ⟨⟨-5789164565841, -5789164565840⟩, ⟨-9824036839003, -9824036839002⟩⟩, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨11428277451969704, 11428277451969707⟩, ⟨19393440524554652, 19393440524554653⟩⟩, ⟨⟨-506711060898639, -506711060898636⟩, ⟨-1, 1⟩⟩, ⟨⟨-5790834591932, -5790834591931⟩, ⟨-9826870822672, -9826870822671⟩⟩, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨11429376373904368, 11429376373904371⟩, ⟨19395305361777111, 19395305361777112⟩⟩, ⟨⟨-506808514372945, -506808514372942⟩, ⟨-1, 1⟩⟩, ⟨⟨-5792505260268, -5792505260267⟩, ⟨-9829705896212, -9829705896211⟩⟩, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨11430475507092855, 11430475507092858⟩, ⟨19397170557490907, 19397170557490908⟩⟩, ⟨⟨-506905995954643, -506905995954640⟩, ⟨-1, 1⟩⟩, ⟨⟨-5794176571159, -5794176571158⟩, ⟨-9832542060147, -9832542060146⟩⟩, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨11431574851596055, 11431574851596058⟩, ⟨19399036111799368, 19399036111799369⟩⟩, ⟨⟨-507003505654541, -507003505654538⟩, ⟨-1, 1⟩⟩, ⟨⟨-5795848524912, -5795848524911⟩, ⟨-9835379315002, -9835379315001⟩⟩],
  [⟨⟨0, 1⟩, ⟨0, 0⟩⟩, ⟨⟨-4, 0⟩, ⟨0, 1⟩⟩, ⟨⟨0, 7⟩, ⟨-3, 0⟩⟩, ⟨⟨-10, 0⟩, ⟨0, 5⟩⟩, ⟨⟨0, 13⟩, ⟨-7, 0⟩⟩, ⟨⟨-18, -2⟩, ⟨0, 8⟩⟩, ⟨⟨311, 333⟩, ⟨-12, -1⟩⟩, ⟨⟨-24276, -24251⟩, ⟨270, 284⟩⟩, ⟨⟨1489737, 1489764⟩, ⟨-20937, -20922⟩⟩, ⟨⟨-73994902, -73994871⟩, ⟨1283074, 1283090⟩⟩, ⟨⟨2980674378, 2980674414⟩, ⟨-63608975, -63608956⟩⟩, ⟨⟨-97189216336, -97189216294⟩, ⟨2556391207, 2556391230⟩⟩, ⟨⟨2547902357345, 2547902357388⟩, ⟨-83115545341, -83115545316⟩⟩, ⟨⟨-53037402834404, -53037402834361⟩, ⟨2170961890153, 2170961890179⟩⟩, ⟨⟨859102388942832, 859102388942880⟩, ⟨-44972262559657, -44972262559632⟩⟩, ⟨⟨-10490205561090353, -10490205561090297⟩, ⟨723597266980513, 723597266980542⟩⟩, ⟨⟨91737059982980477, 91737059982980542⟩, ⟨-8749044258054931, -8749044258054896⟩⟩, ⟨⟨-525449130190789374, -525449130190789308⟩, ⟨75309331679054647, 75309331679054687⟩⟩, ⟨⟨1644315305270073420, 1644315305270073462⟩, ⟨-418853711955806135, -418853711955806097⟩⟩, ⟨⟨-1697060486465402953, -1697060486465402940⟩, ⟨1219855851314455149, 1219855851314455168⟩⟩, ⟨⟨496138938356833823, 496138938356833825⟩, ⟨-868243142124459194, -868243142124459192⟩⟩],
  [o],
  [⟨⟨-5, 5⟩, ⟨-5, 5⟩⟩, ⟨⟨-14, 14⟩, ⟨-14, 14⟩⟩, ⟨⟨-27, 27⟩, ⟨-27, 27⟩⟩, ⟨⟨-37, 37⟩, ⟨-37, 37⟩⟩, ⟨⟨-48, 48⟩, ⟨-48, 48⟩⟩, ⟨⟨-53, 61⟩, ⟨-58, 56⟩⟩, ⟨⟨-311, -196⟩, ⟨-248, -133⟩⟩, ⟨⟨-2757, -2650⟩, ⟨24017, 24124⟩⟩, ⟨⟨1357740, 1357855⟩, ⟨-605725, -605606⟩⟩, ⟨⟨-60069514, -60069378⟩, ⟨-42897380, -42897247⟩⟩, ⟨⟨-265294240, -265294090⟩, ⟨2960006429, 2960006577⟩⟩, ⟨⟨87580217364, 87580217522⟩, ⟨-41331926210, -41331926050⟩⟩, ⟨⟨-2093666970675, -2093666970506⟩, ⟨-1432756577151, -1432756576976⟩⟩, ⟨⟨-3759070360993, -3759070360799⟩, ⟨52628470547704, 52628470547895⟩⟩, ⟨⟨766427959445418, 766427959445630⟩, ⟨-376020564256853, -376020564256639⟩⟩, ⟨⟨-8651882115055927, -8651882115055703⟩, ⟨-5788639985791791, -5788639985791563⟩⟩, ⟨⟨-6280016407628781, -6280016407628546⟩, ⟨90663757343478035, 90663757343478277⟩⟩, ⟨⟨469951081499749881, 469951081499750082⟩, ⟨-221943388404530457, -221943388404530255⟩⟩, ⟨⟨-1298585056815715805, -1298585056815715703⟩, ⟨-985784179004326872, -985784179004326774⟩⟩, ⟨⟨-577704523634044184, -577704523634044164⟩, ⟨1713279592981882501, 1713279592981882521⟩⟩, o],
  [o],
  [⟨⟨-5, 5⟩, ⟨-5, 5⟩⟩, ⟨⟨-14, 14⟩, ⟨-14, 14⟩⟩, ⟨⟨-27, 27⟩, ⟨-27, 27⟩⟩, ⟨⟨-37, 37⟩, ⟨-37, 37⟩⟩, ⟨⟨-48, 48⟩, ⟨-48, 48⟩⟩, ⟨⟨-61, 53⟩, ⟨-58, 56⟩⟩, ⟨⟨-311, -197⟩, ⟨134, 248⟩⟩, ⟨⟨2650, 2756⟩, ⟨24016, 24124⟩⟩, ⟨⟨1357738, 1357856⟩, ⟨605607, 605723⟩⟩, ⟨⟨60069378, 60069514⟩, ⟨-42897381, -42897247⟩⟩, ⟨⟨-265294240, -265294090⟩, ⟨-2960006578, -2960006428⟩⟩, ⟨⟨-87580217523, -87580217364⟩, ⟨-41331926211, -41331926050⟩⟩, ⟨⟨-2093666970675, -2093666970506⟩, ⟨1432756576976, 1432756577150⟩⟩, ⟨⟨3759070360799, 3759070360993⟩, ⟨52628470547703, 52628470547895⟩⟩, ⟨⟨766427959445418, 766427959445631⟩, ⟨376020564256639, 376020564256853⟩⟩, ⟨⟨8651882115055702, 8651882115055926⟩, ⟨-5788639985791790, -5788639985791562⟩⟩, ⟨⟨-6280016407628781, -6280016407628546⟩, ⟨-90663757343478276, -90663757343478035⟩⟩, ⟨⟨-469951081499750081, -469951081499749881⟩, ⟨-221943388404530456, -221943388404530255⟩⟩, ⟨⟨-1298585056815715806, -1298585056815715703⟩, ⟨985784179004326775, 985784179004326872⟩⟩, ⟨⟨577704523634044164, 577704523634044184⟩, ⟨1713279592981882501, 1713279592981882521⟩⟩, o],
  [o],
  [⟨⟨119394242120, 119394242124⟩, ⟨0, 0⟩⟩, ⟨⟨-5437498273700, -5437498273688⟩, ⟨0, 0⟩⟩, ⟨⟨117422858657144, 117422858657166⟩, ⟨0, 0⟩⟩, ⟨⟨-1598575398730700, -1598575398730659⟩, ⟨0, 0⟩⟩, ⟨⟨15385151308719391, 15385151308719465⟩, ⟨0, 0⟩⟩, ⟨⟨-111257344918350769, -111257344918350628⟩, ⟨0, 0⟩⟩, ⟨⟨627169063406794703, 627169063406794972⟩, ⟨0, 0⟩⟩, ⟨⟨-2821666737873199761, -2821666737873199256⟩, ⟨0, 0⟩⟩, ⟨⟨10288575702830281760, 10288575702830282704⟩, ⟨0, 0⟩⟩, ⟨⟨-30698565967976448149, -30698565967976446383⟩, ⟨0, 0⟩⟩, ⟨⟨75349028092248190748, 75349028092248193851⟩, ⟨0, 0⟩⟩, ⟨⟨-152370355728581901695, -152370355728581896859⟩, ⟨0, 0⟩⟩, ⟨⟨253350355085756500462, 253350355085756506881⟩, ⟨0, 0⟩⟩, ⟨⟨-344394527415964936777, -344394527415964929723⟩, ⟨0, 0⟩⟩, ⟨⟨378890397267851185492, 378890397267851191746⟩, ⟨0, 0⟩⟩, ⟨⟨-332059813289115306776, -332059813289115302428⟩, ⟨0, 0⟩⟩, ⟨⟨226310050981601549790, 226310050981601552067⟩, ⟨0, 0⟩⟩, ⟨⟨-115549442293061345901, -115549442293061345059⟩, ⟨0, 0⟩⟩, ⟨⟨41560897074448959699, 41560897074448959892⟩, ⟨0, 0⟩⟩, ⟨⟨-9384743093928592407, -9384743093928592387⟩, ⟨0, 0⟩⟩, o],
  [o],
  [⟨⟨-40625542924, -40625542910⟩, ⟨-112288582137, -112288582123⟩⟩, ⟨⟨-3466528807698, -3466528807652⟩, ⟨4190004647268, 4190004647314⟩⟩, ⟨⟨115955558558196, 115955558558315⟩, ⟨18561020695683, 18561020695803⟩⟩, ⟨⟨-583657455985492, -583657455985194⟩, ⟨-1488282815536796, -1488282815536498⟩⟩, ⟨⟨-9488746041847145, -9488746041846426⟩, ⟨12110637237601838, 12110637237602556⟩⟩, ⟨⟨110283460595192644, 110283460595194297⟩, ⟨14659074880172678, 14659074880174330⟩⟩, ⟨⟨-244389270415431463, -244389270415427880⟩, ⟨-577545037850102640, -577545037850099053⟩⟩, ⟨⟨-1680474442958845198, -1680474442958837956⟩, ⟨2266291726039992314, 2266291726039999554⟩⟩, ⟨⟨10229782684006888681, 10229782684006902012⟩, ⟨1084304145853019062, 1084304145853032392⟩⟩, ⟨⟨-12706783312815381525, -12706783312815359681⟩, ⟨-27939247941110941111, -27939247941110919266⟩⟩, ⟨⟨-43249838486388827767, -43249838486388796578⟩, ⟨61680779671216394430, 61680779671216425613⟩⟩, ⟨⟨151857213791820841006, 151857213791820879154⟩, ⟨12036093983163557616, 12036093983163595776⟩⟩, ⟨⟨-110927756089099664557, -110927756089099625192⟩, ⟨-227699362802162044596, -227699362802162005233⟩⟩, ⟨⟨-190134108712450519679, -190134108712450485998⟩, ⟨287033234064153758477, 287033234064153792153⟩⟩, ⟨⟨378251174559835010728, 378251174559835034187⟩, ⟨19930362707073616472, 19930362707073639932⟩⟩, ⟨⟨-153220259338190890513, -153220259338190877653⟩, ⟨-294482434271179869263, -294482434271179856398⟩⟩, ⟨⟨-119917849794971766008, -119917849794971760653⟩, ⟨191848103576281607543, 191848103576281612895⟩⟩, ⟨⟨115478717253978193319, 115478717253978194916⟩, ⟨3033975978846122365, 3033975978846123964⟩⟩, ⟨⟨-20143190797459859216, -20143190797459858933⟩, ⟨-36343062981237767045, -36343062981237766759⟩⟩, ⟨⟨-4762618402933083363, -4762618402933083343⟩, ⟨8085051026465589005, 8085051026465589025⟩⟩, o],
  [o],
  [⟨⟨-40625542923, -40625542910⟩, ⟨112288582124, 112288582137⟩⟩, ⟨⟨3466528807654, 3466528807698⟩, ⟨4190004647268, 4190004647313⟩⟩, ⟨⟨115955558558196, 115955558558314⟩, ⟨-18561020695802, -18561020695685⟩⟩, ⟨⟨583657455985194, 583657455985491⟩, ⟨-1488282815536796, -1488282815536499⟩⟩, ⟨⟨-9488746041847144, -9488746041846425⟩, ⟨-12110637237602558, -12110637237601838⟩⟩, ⟨⟨-110283460595194297, -110283460595192645⟩, ⟨14659074880172677, 14659074880174328⟩⟩, ⟨⟨-244389270415431464, -244389270415427880⟩, ⟨577545037850099053, 577545037850102640⟩⟩, ⟨⟨1680474442958837955, 1680474442958845199⟩, ⟨2266291726039992314, 2266291726039999554⟩⟩, ⟨⟨10229782684006888683, 10229782684006902012⟩, ⟨-1084304145853032393, -1084304145853019061⟩⟩, ⟨⟨12706783312815359680, 12706783312815381524⟩, ⟨-27939247941110941111, -27939247941110919266⟩⟩, ⟨⟨-43249838486388827767, -43249838486388796575⟩, ⟨-61680779671216425613, -61680779671216394428⟩⟩, ⟨⟨-151857213791820879153, -151857213791820841008⟩, ⟨12036093983163557617, 12036093983163595775⟩⟩, ⟨⟨-110927756089099664557, -110927756089099625193⟩, ⟨227699362802162005234, 227699362802162044596⟩⟩, ⟨⟨190134108712450485996, 190134108712450519680⟩, ⟨287033234064153758478, 287033234064153792155⟩⟩, ⟨⟨378251174559835010731, 378251174559835034185⟩, ⟨-19930362707073639928, -19930362707073616475⟩⟩, ⟨⟨153220259338190877653, 153220259338190890512⟩, ⟨-294482434271179869263, -294482434271179856399⟩⟩, ⟨⟨-119917849794971766008, -119917849794971760653⟩, ⟨-191848103576281612895, -191848103576281607542⟩⟩, ⟨⟨-115478717253978194916, -115478717253978193319⟩, ⟨3033975978846122366, 3033975978846123965⟩⟩, ⟨⟨-20143190797459859218, -20143190797459858933⟩, ⟨36343062981237766760, 36343062981237767045⟩⟩, ⟨⟨4762618402933083343, 4762618402933083363⟩, ⟨8085051026465589005, 8085051026465589025⟩⟩, o],
  [o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨-230538335975692464, -230538335975692462⟩, ⟨0, 0⟩⟩, ⟨⟨-1, 1⟩, ⟨0, 0⟩⟩, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨-229771179981676337, -229771179981676335⟩, ⟨0, 0⟩⟩, ⟨⟨-1, 1⟩, ⟨0, 0⟩⟩, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨-229007372787281585, -229007372787281583⟩, ⟨0, 0⟩⟩, ⟨⟨-1, 1⟩, ⟨0, 0⟩⟩, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨-228246897583216142, -228246897583216140⟩, ⟨0, 0⟩⟩, ⟨⟨-1, 1⟩, ⟨0, 0⟩⟩, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨-227489737647693528, -227489737647693527⟩, ⟨0, 0⟩⟩, ⟨⟨-1, 1⟩, ⟨0, 0⟩⟩, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨-226735876346026010, -226735876346026008⟩, ⟨0, 0⟩⟩, ⟨⟨-1, 1⟩, ⟨0, 0⟩⟩, o]
]

private def st9_6 : List (List CFpIv) := [
  [o, ⟨⟨413832915006284464, 413832915006284471⟩, ⟨-2, 2⟩⟩, ⟨⟨-15668829617024, -15668829617009⟩, ⟨-6, 6⟩⟩, ⟨⟨-6484277435154, -6484277435140⟩, ⟨-9, 8⟩⟩, ⟨⟨7918237674, 7918237687⟩, ⟨-8, 7⟩⟩, ⟨⟨3276827377, 3276827385⟩, ⟨-5, 4⟩⟩, ⟨⟨-129055326, -129055322⟩, ⟨-2, 2⟩⟩, ⟨⟨-53407342, -53407340⟩, ⟨-1, 1⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, o, ⟨⟨413860084294284692, 413860084294284699⟩, ⟨-2, 2⟩⟩, ⟨⟨-15671839085532, -15671839085517⟩, ⟨-6, 6⟩⟩, ⟨⟨-6485948644988, -6485948644974⟩, ⟨-8, 8⟩⟩, ⟨⟨7921279633, 7921279647⟩, ⟨-8, 7⟩⟩, ⟨⟨3278301455, 3278301464⟩, ⟨-5, 4⟩⟩, ⟨⟨-129129703, -129129699⟩, ⟨-2, 2⟩⟩, ⟨⟨-53441630, -53441628⟩, ⟨-1, 1⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, o, ⟨⟨413887256628221551, 413887256628221558⟩, ⟨-2, 2⟩⟩, ⟨⟨-15674849420859, -15674849420843⟩, ⟨-6, 6⟩⟩, ⟨⟨-6487620424863, -6487620424850⟩, ⟨-7, 7⟩⟩, ⟨⟨7924323054, 7924323067⟩, ⟨-7, 6⟩⟩, ⟨⟨3279776327, 3279776337⟩, ⟨-5, 4⟩⟩, ⟨⟨-129204130, -129204124⟩, ⟨-2, 2⟩⟩, ⟨⟨-53475943, -53475940⟩, ⟨-1, 1⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, o, ⟨⟨413914432008519532, 413914432008519539⟩, ⟨-2, 2⟩⟩, ⟨⟨-15677860623339, -15677860623323⟩, ⟨-6, 6⟩⟩, ⟨⟨-6489292775022, -6489292775008⟩, ⟨-7, 7⟩⟩, ⟨⟨7927367936, 7927367949⟩, ⟨-7, 7⟩⟩, ⟨⟨3281251994, 3281252005⟩, ⟨-5, 5⟩⟩, ⟨⟨-129278606, -129278600⟩, ⟨-3, 3⟩⟩, ⟨⟨-53510280, -53510279⟩, ⟨-1, 1⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, o, ⟨⟨413941610435603185, 413941610435603192⟩, ⟨-2, 2⟩⟩, ⟨⟨-15680872693308, -15680872693293⟩, ⟨-6, 6⟩⟩, ⟨⟨-6490965695707, -6490965695694⟩, ⟨-7, 7⟩⟩, ⟨⟨7930414280, 7930414293⟩, ⟨-6, 7⟩⟩, ⟨⟨3282728457, 3282728466⟩, ⟨-4, 5⟩⟩, ⟨⟨-129353131, -129353127⟩, ⟨-2, 2⟩⟩, ⟨⟨-53544643, -53544642⟩, ⟨-1, 1⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, o, ⟨⟨413968791909897119, 413968791909897126⟩, ⟨-2, 2⟩⟩, ⟨⟨-15683885631098, -15683885631083⟩, ⟨-6, 6⟩⟩, ⟨⟨-6492639187162, -6492639187149⟩, ⟨-7, 7⟩⟩, ⟨⟨7933462088, 7933462101⟩, ⟨-6, 7⟩⟩, ⟨⟨3284205715, 3284205723⟩, ⟨-4, 5⟩⟩, ⟨⟨-129427708, -129427704⟩, ⟨-3, 3⟩⟩, ⟨⟨-53579032, -53579030⟩, ⟨-1, 1⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, o, ⟨⟨413995976431826004, 413995976431826011⟩, ⟨-2, 2⟩⟩, ⟨⟨-15686899437041, -15686899437026⟩, ⟨-6, 6⟩⟩, ⟨⟨-6494313249629, -6494313249616⟩, ⟨-7, 7⟩⟩, ⟨⟨7936511360, 7936511373⟩, ⟨-6, 7⟩⟩, ⟨⟨3285683768, 3285683777⟩, ⟨-4, 5⟩⟩, ⟨⟨-129502334, -129502330⟩, ⟨-2, 2⟩⟩, ⟨⟨-53613445, -53613443⟩, ⟨-1, 1⟩⟩, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, o, ⟨⟨414023164001814566, 414023164001814573⟩, ⟨-2, 2⟩⟩, ⟨⟨-15689914111471, -15689914111456⟩, ⟨-6, 6⟩⟩, ⟨⟨-6495987883353, -6495987883337⟩, ⟨-9, 9⟩⟩, ⟨⟨7939562094, 7939562109⟩, ⟨-8, 7⟩⟩, ⟨⟨3287162618, 3287162626⟩, ⟨-5, 4⟩⟩, ⟨⟨-129577011, -129577007⟩, ⟨-2, 2⟩⟩, ⟨⟨-53647884, -53647882⟩, ⟨-1, 1⟩⟩, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, o, ⟨⟨414050354620287593, 414050354620287600⟩, ⟨-2, 2⟩⟩, ⟨⟨-15692929654722, -15692929654705⟩, ⟨-6, 6⟩⟩, ⟨⟨-6497663088574, -6497663088557⟩, ⟨-8, 8⟩⟩, ⟨⟨7942614296, 7942614311⟩, ⟨-7, 8⟩⟩, ⟨⟨3288642264, 3288642273⟩, ⟨-5, 5⟩⟩, ⟨⟨-129651739, -129651734⟩, ⟨-3, 2⟩⟩, ⟨⟨-53682348, -53682346⟩, ⟨-1, 1⟩⟩, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, o, ⟨⟨414077548287669930, 414077548287669937⟩, ⟨-2, 2⟩⟩, ⟨⟨-15695946067128, -15695946067113⟩, ⟨-6, 6⟩⟩, ⟨⟨-6499338865536, -6499338865522⟩, ⟨-9, 8⟩⟩, ⟨⟨7945667967, 7945667980⟩, ⟨-7, 8⟩⟩, ⟨⟨3290122710, 3290122718⟩, ⟨-4, 5⟩⟩, ⟨⟨-129726515, -129726511⟩, ⟨-2, 2⟩⟩, ⟨⟨-53716837, -53716836⟩, ⟨-1, 1⟩⟩, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, o, ⟨⟨414104745004386484, 414104745004386491⟩, ⟨-2, 2⟩⟩, ⟨⟨-15698963349021, -15698963349006⟩, ⟨-6, 6⟩⟩, ⟨⟨-6501015214483, -6501015214469⟩, ⟨-7, 7⟩⟩, ⟨⟨7948723102, 7948723116⟩, ⟨-7, 7⟩⟩, ⟨⟨3291603952, 3291603960⟩, ⟨-5, 5⟩⟩, ⟨⟨-129801343, -129801339⟩, ⟨-2, 2⟩⟩, ⟨⟨-53751352, -53751350⟩, ⟨-1, 1⟩⟩, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨414131944770862219, 414131944770862226⟩, ⟨-2, 2⟩⟩, ⟨⟨-15701981500736, -15701981500721⟩, ⟨-6, 6⟩⟩, ⟨⟨-6502692135660, -6502692135646⟩, ⟨-9, 9⟩⟩, ⟨⟨7951779707, 7951779720⟩, ⟨-8, 7⟩⟩, ⟨⟨3293085993, 3293086002⟩, ⟨-5, 5⟩⟩, ⟨⟨-129876221, -129876217⟩, ⟨-2, 3⟩⟩, ⟨⟨-53785892, -53785890⟩, ⟨-1, 1⟩⟩, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨414159147587522159, 414159147587522166⟩, ⟨-2, 2⟩⟩, ⟨⟨-15705000522611, -15705000522596⟩, ⟨-6, 6⟩⟩, ⟨⟨-6504369629311, -6504369629295⟩, ⟨-7, 7⟩⟩, ⟨⟨7954837778, 7954837793⟩, ⟨-6, 7⟩⟩, ⟨⟨3294568832, 3294568841⟩, ⟨-5, 5⟩⟩, ⟨⟨-129951149, -129951145⟩, ⟨-3, 2⟩⟩, ⟨⟨-53820457, -53820455⟩, ⟨-1, 1⟩⟩, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨414186353454791387, 414186353454791394⟩, ⟨-2, 2⟩⟩, ⟨⟨-15708020414977, -15708020414962⟩, ⟨-6, 6⟩⟩, ⟨⟨-6506047695676, -6506047695662⟩, ⟨-7, 7⟩⟩, ⟨⟨7957897323, 7957897337⟩, ⟨-7, 6⟩⟩, ⟨⟨3296052472, 3296052480⟩, ⟨-5, 4⟩⟩, ⟨⟨-130026128, -130026124⟩, ⟨-2, 2⟩⟩, ⟨⟨-53855048, -53855046⟩, ⟨-1, 1⟩⟩, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨414213562373095045, 414213562373095052⟩, ⟨-2, 2⟩⟩, ⟨⟨-15711041178167, -15711041178152⟩, ⟨-6, 6⟩⟩, ⟨⟨-6507726335003, -6507726334989⟩, ⟨-7, 7⟩⟩, ⟨⟨7960958338, 7960958351⟩, ⟨-6, 7⟩⟩, ⟨⟨3297536910, 3297536921⟩, ⟨-5, 5⟩⟩, ⟨⟨-130101159, -130101153⟩, ⟨-3, 2⟩⟩, ⟨⟨-53889664, -53889662⟩, ⟨-1, 1⟩⟩, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨414240774342858336, 414240774342858343⟩, ⟨-2, 2⟩⟩, ⟨⟨-15714062812519, -15714062812503⟩, ⟨-6, 6⟩⟩, ⟨⟨-6509405547534, -6509405547520⟩, ⟨-7, 7⟩⟩, ⟨⟨7964020822, 7964020835⟩, ⟨-7, 6⟩⟩, ⟨⟨3299022150, 3299022159⟩, ⟨-6, 4⟩⟩, ⟨⟨-130176239, -130176233⟩, ⟨-3, 2⟩⟩, ⟨⟨-53924306, -53924303⟩, ⟨-1, 1⟩⟩, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨414267989364506519, 414267989364506526⟩, ⟨-2, 2⟩⟩, ⟨⟨-15717085318363, -15717085318348⟩, ⟨-6, 6⟩⟩, ⟨⟨-6511085333512, -6511085333499⟩, ⟨-7, 8⟩⟩, ⟨⟨7967084780, 7967084793⟩, ⟨-7, 7⟩⟩, ⟨⟨3300508190, 3300508201⟩, ⟨-5, 4⟩⟩, ⟨⟨-130251369, -130251363⟩, ⟨-2, 2⟩⟩, ⟨⟨-53958972, -53958971⟩, ⟨-1, 1⟩⟩, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨414295207438464915, 414295207438464922⟩, ⟨-2, 2⟩⟩, ⟨⟨-15720108696043, -15720108696028⟩, ⟨-6, 6⟩⟩, ⟨⟨-6512765693186, -6512765693172⟩, ⟨-7, 7⟩⟩, ⟨⟨7970150213, 7970150226⟩, ⟨-6, 7⟩⟩, ⟨⟨3301995034, 3301995043⟩, ⟨-5, 5⟩⟩, ⟨⟨-130326549, -130326545⟩, ⟨-3, 2⟩⟩, ⟨⟨-53993665, -53993663⟩, ⟨-1, 1⟩⟩],
  [⟨⟨0, 1⟩, ⟨0, 0⟩⟩, ⟨⟨-7, 1⟩, ⟨-2, 2⟩⟩, ⟨⟨-9, 23⟩, ⟨-11, 12⟩⟩, ⟨⟨-49, 29⟩, ⟨-33, 33⟩⟩, ⟨⟨-57, 82⟩, ⟨-64, 62⟩⟩, ⟨⟨-118, 88⟩, ⟨-95, 96⟩⟩, ⟨⟨188, 465⟩, ⟨-129, 129⟩⟩, ⟨⟨-24839, -24483⟩, ⟨-166, 166⟩⟩, ⟨⟨1520431, 1520874⟩, ⟨-210, 207⟩⟩, ⟨⟨-75895442, -75894914⟩, ⟨-249, 248⟩⟩, ⟨⟨3075183124, 3075183721⟩, ⟨-281, 280⟩⟩, ⟨⟨-101002140043, -101002139377⟩, ⟨-313, 310⟩⟩, ⟨⟨2672462380664, 2672462381421⟩, ⟨-357, 356⟩⟩, ⟨⟨-56310489108785, -56310489107933⟩, ⟨-404, 405⟩⟩, ⟨⟨927438030142036, 927438030142957⟩, ⟨-436, 438⟩⟩, ⟨⟨-11601433925064502, -11601433925063533⟩, ⟨-456, 454⟩⟩, ⟨⟨105378246584106231, 105378246584107270⟩, ⟨-484, 487⟩⟩, ⟨⟨-645652794739939608, -645652794739938453⟩, ⟨-544, 545⟩⟩, ⟨⟨2340752757853514327, 2340752757853515599⟩, ⟨-617, 615⟩⟩, ⟨⟨-3913622081614214331, -3913622081614213053⟩, ⟨-639, 638⟩⟩, ⟨⟨2731304916817666361, 2731304916817667439⟩, ⟨-543, 542⟩⟩, ⟨⟨989463387335884361, 989463387335885069⟩, ⟨-350, 351⟩⟩, ⟨⟨-3618865736880285607, -3618865736880285268⟩, ⟨-165, 164⟩⟩, ⟨⟨2986303777803950302, 2986303777803950414⟩, ⟨-53, 54⟩⟩, ⟨⟨-964334741237681549, -964334741237681528⟩, ⟨-9, 11⟩⟩],
  [o],
  [⟨⟨-5, 5⟩, ⟨-5, 5⟩⟩, ⟨⟨-38, 38⟩, ⟨-38, 38⟩⟩, ⟨⟨-130, 130⟩, ⟨-130, 130⟩⟩, ⟨⟨-291, 291⟩, ⟨-291, 291⟩⟩, ⟨⟨-492, 492⟩, ⟨-492, 492⟩⟩, ⟨⟨-691, 699⟩, ⟨-696, 694⟩⟩, ⟨⟨-1139, 624⟩, ⟨-1079, 684⟩⟩, ⟨⟨-3950, -1920⟩, ⟨23643, 25673⟩⟩, ⟨⟨1404493, 1406628⟩, ⟨-614473, -612336⟩⟩, ⟨⟨-61967923, -61965750⟩, ⟨-45194552, -45192382⟩⟩, ⟨⟨-316312683, -316310383⟩, ⟨3099352210, 3099354500⟩⟩, ⟨⟨93485513407, 93485515938⟩, ⟨-42391597698, -42391595164⟩⟩, ⟨⟨-2221039503032, -2221039500242⟩, ⟨-1582428058195, -1582428055391⟩⟩, ⟨⟨-5485562489043, -5485562485998⟩, ⟨57515661205533, 57515661208579⟩⟩, ⟨⟨873343976592884, 873343976596209⟩, ⟨-395970889227281, -395970889223965⟩⟩, ⟨⟨-9806868573965032, -9806868573961385⟩, ⟨-7145236644951803, -7145236644948153⟩⟩, ⟨⟨-13869821442990414, -13869821442986432⟩, ⟨111447398377245794, 111447398377249785⟩⟩, ⟨⟨666530835152613874, 666530835152618106⟩, ⟨-252671906144023289, -252671906144019058⟩⟩, ⟨⟨-2015019122068108310, -2015019122068104151⟩, ⟨-1951212741266291595, -1951212741266287451⟩⟩, ⟨⟨-2662085107840879708, -2662085107840876250⟩, ⟨5470243775297436616, 5470243775297440069⟩⟩, ⟨⟨8349314750123406367, 8349314750123408568⟩, ⟨1981710286280400653, 1981710286280402863⟩⟩, ⟨⟨703664899459059882, 703664899459060875⟩, ⟨-8826797555110438264, -8826797555110437275⟩⟩, ⟨⟨-6863754432001352487, -6863754432001352199⟩, ⟨513258074075507058, 513258074075507344⟩⟩, ⟨⟨1032029512719405098, 1032029512719405144⟩, ⟨3482962100141691966, 3482962100141692018⟩⟩, ⟨⟨812129623989555154, 812129623989555159⟩, ⟨-521454118012487795, -521454118012487788⟩⟩],
  [o],
  [⟨⟨-5, 5⟩, ⟨-5, 5⟩⟩, ⟨⟨-38, 38⟩, ⟨-38, 38⟩⟩, ⟨⟨-127, 127⟩, ⟨-127, 127⟩⟩, ⟨⟨-283, 283⟩, ⟨-283, 283⟩⟩, ⟨⟨-483, 483⟩, ⟨-483, 483⟩⟩, ⟨⟨-689, 691⟩, ⟨-694, 686⟩⟩, ⟨⟨-1073, 682⟩, ⟨-1143, 612⟩⟩, ⟨⟨-26047, -24025⟩, ⟨1417, 3437⟩⟩, ⟨⟨-662422, -660294⟩, ⟨1409617, 1411746⟩⟩, ⟨⟨43959680, 43961843⟩, ⟨64681235, 64683404⟩⟩, ⟨⟨3185208017, 3185210313⟩, ⟨-194050534, -194048239⟩⟩, ⟨⟨48453281719, 48453284262⟩, ⟨-93970261590, -93970259052⟩⟩, ⟨⟨-1494588553787, -1494588550977⟩, ⟨-2401679952506, -2401679949700⟩⟩, ⟨⟨-60475535320292, -60475535317240⟩, ⟨1024718659848, 1024718662901⟩⟩, ⟨⟨-509695916447563, -509695916444245⟩, ⟨879433174699614, 879433174702938⟩⟩, ⟨⟨6269616367278216, 6269616367281866⟩, ⟨11493812141488972, 11493812141492617⟩⟩, ⟨⟨124318509086050883, 124318509086054875⟩, ⟨6666688437193304, 6666688437197285⟩⟩, ⟨⟨479483070186240957, 479483070186245181⟩, ⟨-672851974080635856, -672851974080631631⟩⟩, ⟨⟨-1243460619468051541, -1243460619468047410⟩, ⟨-3299002482732065529, -3299002482732061379⟩⟩, ⟨⟨-8503713866107995153, -8503713866107991712⟩, ⟨-2442814687689881490, -2442814687689878045⟩⟩, ⟨⟨-11318968328633637174, -11318968328633634976⟩, ⟨8444395834832395703, 8444395834832397889⟩⟩, ⟨⟨-191551373630216573, -191551373630215596⟩, ⟨15017056516013876230, 15017056516013877205⟩⟩, ⟨⟨8275168432610130644, 8275168432610130919⟩, ⟨6619714800576334341, 6619714800576334616⟩⟩, ⟨⟨4506028505806635773, 4506028505806635815⟩, ⟨-990414179002605895, -990414179002605853⟩⟩, ⟨⟨459908719309801900, 459908719309801903⟩, ⟨-850181454220640396, -850181454220640392⟩⟩],
  [o],
  [⟨⟨103908124649, 103908124660⟩, ⟨-3, 4⟩⟩, ⟨⟨-5162243104738, -5162243104697⟩, ⟨-10, 10⟩⟩, ⟨⟨122444223804341, 122444223804447⟩, ⟨-15, 15⟩⟩, ⟨⟨-1845018443399441, -1845018443399222⟩, ⟨-22, 20⟩⟩, ⟨⟨19824918850375317, 19824918850375722⟩, ⟨-28, 31⟩⟩, ⟨⟨-161637213488132015, -161637213488131278⟩, ⟨-47, 43⟩⟩, ⟨⟨1038859726228811454, 1038859726228812817⟩, ⟨-75, 80⟩⟩, ⟨⟨-5397704350699152346, -5397704350699149774⟩, ⟨-145, 141⟩⟩, ⟨⟨23068960369652233294, 23068960369652238172⟩, ⟨-281, 284⟩⟩, ⟨⟨-82084670323909195345, -82084670323909186084⟩, ⟨-582, 579⟩⟩, ⟨⟨245198227487016583605, 245198227487016601012⟩, ⟨-1196, 1199⟩⟩, ⟨⟨-618203890156087527598, -618203890156087496218⟩, ⟨-2336, 2332⟩⟩, ⟨⟨1319448584955585432459, 1319448584955585484488⟩, ⟨-4079, 4084⟩⟩, ⟨⟨-2385889492955897989167, -2385889492955897912551⟩, ⟨-6218, 6217⟩⟩, ⟨⟨3650527648775526028616, 3650527648775526126428⟩, ⟨-8108, 8104⟩⟩, ⟨⟨-4710025912899650083643, -4710025912899649977276⟩, ⟨-8921, 8923⟩⟩, ⟨⟨5094708424004666003661, 5094708424004666100701⟩, ⟨-8189, 8185⟩⟩, ⟨⟨-4579778539214919415631, -4579778539214919342542⟩, ⟨-6172, 6176⟩⟩, ⟨⟨3378789976647941580677, 3378789976647941625232⟩, ⟨-3753, 3753⟩⟩, ⟨⟨-2009811541455522766075, -2009811541455522744684⟩, ⟨-1794, 1790⟩⟩, ⟨⟨939503086843339512504, 939503086843339520276⟩, ⟨-646, 652⟩⟩, ⟨⟨-332088173177318763897, -332088173177318761893⟩, ⟨-172, 168⟩⟩, ⟨⟨83385189330136153284, 83385189330136153611⟩, ⟨-29, 29⟩⟩, ⟨⟨-13245493678894946587, -13245493678894946563⟩, ⟨-2, 2⟩⟩, o],
  [o],
  [⟨⟨101545497819, 101545497874⟩, ⟨22034242976, 22034243031⟩⟩, ⟨⟨-1618123824145, -1618123823848⟩, ⟨-4902103321717, -4902103321420⟩⟩, ⟨⟨-80688950602191, -80688950601217⟩, ⟨92097538576228, 92097538577202⟩⟩, ⟨⟨1812868211335130, 1812868211337742⟩, ⟨342946210062954, 342946210065563⟩⟩, ⟨⟨-6714778268218518, -6714778268212018⟩, ⟨-18653137379884113, -18653137379877610⟩⟩, ⟨⟨-103231051250814690, -103231051250799154⟩, ⟨124378093895317001, 124378093895332535⟩⟩, ⟨⟨1025547321012188267, 1025547321012223772⟩, ⟨165767438184910833, 165767438184946337⟩⟩, ⟨⟨-1963209253718804817, -1963209253718728050⟩, ⟨-5028008726122619235, -5028008726122542467⟩⟩, ⟨⟨-14253791495550466321, -14253791495550311420⟩, ⟨18138427986266479445, 18138427986266634349⟩⟩, ⟨⟨81353476147133998465, 81353476147134285514⟩, ⟨10929047869049741754, 10929047869050028797⟩⟩, ⟨⟨-95249602170436475384, -95249602170435995061⟩, ⟨-225940323178241472866, -225940323178240992536⟩⟩, ⟨⟨-368855138854926401123, -368855138854925686166⟩, ⟨496101918278323813514, 496101918278324528471⟩⟩, ⟨⟨1311917168839145659571, 1311917168839146594979⟩, ⟨140688163747644606377, 140688163747645541774⟩⟩, ⟨⟨-985203947272187486071, -985203947272186421594⟩, ⟨-2172959464836533910704, -2172959464836532846207⟩⟩, ⟨⟨-2099091114362158693451, -2099091114362157649827⟩, ⟨2986627565700574356760, 2986627565700575400363⟩⟩, ⟨⟨4694874626671833224188, 4694874626671834097597⟩, ⟨376964502848080824675, 376964502848081698093⟩⟩, ⟨⟨-2226917731659828000346, -2226917731659827385011⟩, ⟨-4582184508525817666172, -4582184508525817050828⟩⟩, ⟨⟨-2532416189194240309701, -2532416189194239949998⟩, ⟨3815868287909969649380, 3815868287909970009080⟩⟩, ⟨⟨3373940666933534363385, 3373940666933534535259⟩, ⟨180382498573886446638, 180382498573886618502⟩⟩, ⟨⟨-926456058078224663212, -926456058078224598543⟩, ⟨-1783522216948609481459, -1783522216948609416780⟩⟩, ⟨⟨-498415400721154835461, -498415400721154817083⟩, ⟨796388226872254482368, 796388226872254500743⟩⟩, ⟨⟨331967535168662588504, 331967535168662592259⟩, ⟨8867499825237348002, 8867499825237351756⟩⟩, ⟨⟨-40400189815466307664, -40400189815466307201⟩, ⟨-72944118374618595833, -72944118374618595367⟩⟩, ⟨⟨-6724574962285275974, -6724574962285275950⟩, ⟨11411494248850882035, 11411494248850882059⟩⟩, o],
  [o],
  [⟨⟨101545497821, 101545497872⟩, ⟨-22034243028, -22034242977⟩⟩, ⟨⟨1618123823854, 1618123824139⟩, ⟨-4902103321714, -4902103321429⟩⟩, ⟨⟨-80688950602186, -80688950601240⟩, ⟨-92097538577185, -92097538576242⟩⟩, ⟨⟨-1812868211337720, -1812868211335153⟩, ⟨342946210062986, 342946210065557⟩⟩, ⟨⟨-6714778268218491, -6714778268212023⟩, ⟨18653137379877631, 18653137379884095⟩⟩, ⟨⟨103231051250799163, 103231051250814684⟩, ⟨124378093895317003, 124378093895332527⟩⟩, ⟨⟨1025547321012188270, 1025547321012223776⟩, ⟨-165767438184946328, -165767438184910823⟩⟩, ⟨⟨1963209253718728067, 1963209253718804834⟩, ⟨-5028008726122619232, -5028008726122542467⟩⟩, ⟨⟨-14253791495550466318, -14253791495550311412⟩, ⟨-18138427986266634364, -18138427986266479452⟩⟩, ⟨⟨-81353476147134285531, -81353476147133998464⟩, ⟨10929047869049741745, 10929047869050028802⟩⟩, ⟨⟨-95249602170436475392, -95249602170435995054⟩, ⟨225940323178240992535, 225940323178241472883⟩⟩, ⟨⟨368855138854925686162, 368855138854926401130⟩, ⟨496101918278323813507, 496101918278324528471⟩⟩, ⟨⟨1311917168839145659549, 1311917168839146594985⟩, ⟨-140688163747645541785, -140688163747644606359⟩⟩, ⟨⟨985203947272186421606, 985203947272187486068⟩, ⟨-2172959464836533910693, -2172959464836532846211⟩⟩, ⟨⟨-2099091114362158693419, -2099091114362157649854⟩, ⟨-2986627565700575400342, -2986627565700574356802⟩⟩, ⟨⟨-4694874626671834097607, -4694874626671833224194⟩, ⟨376964502848080824662, 376964502848081698088⟩⟩, ⟨⟨-2226917731659828000330, -2226917731659827385045⟩, ⟨4582184508525817050856, 4582184508525817666146⟩⟩, ⟨⟨2532416189194239950032, 2532416189194240309669⟩, ⟨3815868287909969649413, 3815868287909970009049⟩⟩, ⟨⟨3373940666933534363383, 3373940666933534535262⟩, ⟨-180382498573886618512, -180382498573886446640⟩⟩, ⟨⟨926456058078224598535, 926456058078224663213⟩, ⟨-1783522216948609481470, -1783522216948609416782⟩⟩, ⟨⟨-498415400721154835469, -498415400721154817084⟩, ⟨-796388226872254500751, -796388226872254482372⟩⟩, ⟨⟨-331967535168662592266, -331967535168662588507⟩, ⟨8867499825237347997, 8867499825237351756⟩⟩, ⟨⟨-40400189815466307667, -40400189815466307201⟩, ⟨72944118374618595368, 72944118374618595833⟩⟩, ⟨⟨6724574962285275950, 6724574962285275974⟩, ⟨11411494248850882035, 11411494248850882059⟩⟩, o],
  [o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨-12252634041234869, -12252634041234865⟩, ⟨-2, 3⟩⟩, ⟨⟨-6, 7⟩, ⟨-6, 7⟩⟩, ⟨⟨1647900139747163, 1647900139747182⟩, ⟨-11, 9⟩⟩, ⟨⟨-11, 10⟩, ⟨-12, 11⟩⟩, ⟨⟨-7148052547412010, -7148052547411994⟩, ⟨-8, 8⟩⟩, ⟨⟨-3, 3⟩, ⟨-2, 2⟩⟩, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨-12130722378545883, -12130722378545878⟩, ⟨-3, 2⟩⟩, ⟨⟨-6, 6⟩, ⟨-6, 7⟩⟩, ⟨⟨1636951044892893, 1636951044892914⟩, ⟨-9, 10⟩⟩, ⟨⟨-10, 11⟩, ⟨-11, 13⟩⟩, ⟨⟨-7124266172212932, -7124266172212915⟩, ⟨-8, 7⟩⟩, ⟨⟨-3, 3⟩, ⟨-2, 2⟩⟩, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨-12010148946357844, -12010148946357839⟩, ⟨-2, 2⟩⟩, ⟨⟨-6, 6⟩, ⟨-7, 6⟩⟩, ⟨⟨1626086002275070, 1626086002275090⟩, ⟨-10, 10⟩⟩, ⟨⟨-11, 12⟩, ⟨-11, 12⟩⟩, ⟨⟨-7100583629617497, -7100583629617480⟩, ⟨-8, 7⟩⟩, ⟨⟨-3, 3⟩, ⟨-2, 2⟩⟩, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨-11890897882505165, -11890897882505160⟩, ⟨-2, 2⟩⟩, ⟨⟨-6, 5⟩, ⟨-5, 6⟩⟩, ⟨⟨1615304298126280, 1615304298126300⟩, ⟨-9, 8⟩⟩, ⟨⟨-12, 11⟩, ⟨-12, 12⟩⟩, ⟨⟨-7077004398438191, -7077004398438174⟩, ⟨-8, 8⟩⟩, ⟨⟨-3, 3⟩, ⟨-2, 2⟩⟩, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨-11772953524262321, -11772953524262316⟩, ⟨-3, 3⟩⟩, ⟨⟨-6, 6⟩, ⟨-6, 6⟩⟩, ⟨⟨1604605225156712, 1604605225156732⟩, ⟨-8, 9⟩⟩, ⟨⟨-10, 10⟩, ⟨-11, 11⟩⟩, ⟨⟨-7053527960200683, -7053527960200667⟩, ⟨-8, 8⟩⟩, ⟨⟨-3, 3⟩, ⟨-2, 2⟩⟩, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨-11656300405725940, -11656300405725934⟩, ⟨-2, 3⟩⟩, ⟨⟨-6, 7⟩, ⟨-5, 7⟩⟩, ⟨⟨1593988082493352, 1593988082493371⟩, ⟨-10, 10⟩⟩, ⟨⟨-10, 11⟩, ⟨-11, 11⟩⟩, ⟨⟨-7030153799131230, -7030153799131212⟩, ⟨-8, 8⟩⟩, ⟨⟨-3, 3⟩, ⟨-2, 2⟩⟩, o]
]

private def st9_7 : List (List CFpIv) := [
  [o, ⟨⟨-210099787618575197, -210099787618575186⟩, ⟨356532972928491230, 356532972928491237⟩⟩, ⟨⟨-88299510344357838, -88299510344357801⟩, ⟨-149815003782590470, -149815003782590436⟩⟩, ⟨⟨71965697058073862, 71965697058073927⟩, ⟨-5586454405700, -5586454405630⟩⟩, ⟨⟨-14208516249149138, -14208516249149053⟩, ⟨25659317633870388, 25659317633870475⟩⟩, ⟨⟨-6163186552999027, -6163186552998943⟩, ⟨-10456821724525684, -10456821724525599⟩⟩, ⟨⟨221824511252, 221824511320⟩, ⟨-403200965520, -403200965453⟩⟩, ⟨⟨97149156179, 97149156227⟩, ⟨163800189670, 163800189716⟩⟩, ⟨⟨-101123939, -101123909⟩, ⟨222492397, 222492427⟩⟩, ⟨⟨-58079776, -58079756⟩, ⟨-82799631, -82799613⟩⟩, ⟨⟨1833858, 1833870⟩, ⟨-3311174, -3311164⟩⟩, ⟨⟨795245, 795248⟩, ⟨1349507, 1349511⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, o, ⟨⟨-210113581257098389, -210113581257098378⟩, ⟨356556380315076042, 356556380315076049⟩⟩, ⟨⟨-88311105896452114, -88311105896452077⟩, ⟨-149834675976137226, -149834675976137194⟩⟩, ⟨⟨71979872436412144, 71979872436412207⟩, ⟨-5587894217250, -5587894217182⟩⟩, ⟨⟨-14212247846885291, -14212247846885206⟩, ⟨25666056863933660, 25666056863933747⟩⟩, ⟨⟨-6165210039542611, -6165210039542525⟩, ⟨-10460254772855622, -10460254772855536⟩⟩, ⟨⟨221925328816, 221925328887⟩, ⟨-403384395158, -403384395088⟩⟩, ⟨⟨97199754160, 97199754208⟩, ⟨163885431814, 163885431862⟩⟩, ⟨⟨-101188666, -101188635⟩, ⟨222637505, 222637536⟩⟩, ⟨⟨-58121729, -58121708⟩, ⟨-82858635, -82858616⟩⟩, ⟨⟨1835397, 1835409⟩, ⟨-3313953, -3313942⟩⟩, ⟨⟨795964, 795968⟩, ⟨1350727, 1350732⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, o, ⟨⟨-210127376442020179, -210127376442020168⟩, ⟨356579790325852413, 356579790325852420⟩⟩, ⟨⟨-88322703510233779, -88322703510233741⟩, ⟨-149854351666834044, -149854351666834012⟩⟩, ⟨⟨71994051265648025, 71994051265648088⟩, ⟨-5589334519909, -5589334519843⟩⟩, ⟨⟨-14215980598045527, -14215980598045445⟩, ⟨25672798177212131, 25672798177212213⟩⟩, ⟨⟨-6167234284490325, -6167234284490243⟩, ⟨-10463689107830558, -10463689107830477⟩⟩, ⟨⟨222026198988, 222026199057⟩, ⟨-403567920618, -403567920551⟩⟩, ⟨⟨97250381777, 97250381827⟩, ⟨163970723838, 163970723887⟩⟩, ⟨⟨-101253438, -101253406⟩, ⟨222782717, 222782751⟩⟩, ⟨⟨-58163715, -58163694⟩, ⟨-82917685, -82917666⟩⟩, ⟨⟨1836937, 1836950⟩, ⟨-3316733, -3316723⟩⟩, ⟨⟨796684, 796688⟩, ⟨1351950, 1351954⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, o, ⟨⟨-210141173173556077, -210141173173556066⟩, ⟨356603202961186058, 356603202961186065⟩⟩, ⟨⟨-88334303186140314, -88334303186140275⟩, ⟨-149874030855422744, -149874030855422710⟩⟩, ⟨⟨72008233546751453, 72008233546751520⟩, ⟨-5590775313893, -5590775313825⟩⟩, ⟨⟨-14219714503031929, -14219714503031844⟩, ⟨25679541574432069, 25679541574432154⟩⟩, ⟨⟨-6169259288157322, -6169259288157235⟩, ⟨-10467124729985114, -10467124729985029⟩⟩, ⟨⟨222127121792, 222127121865⟩, ⟨-403751541965, -403751541890⟩⟩, ⟨⟨97301039051, 97301039104⟩, ⟨164056065773, 164056065826⟩⟩, ⟨⟨-101318256, -101318223⟩, ⟨222928038, 222928068⟩⟩, ⟨⟨-58205735, -58205714⟩, ⟨-82976782, -82976761⟩⟩, ⟨⟨1838479, 1838491⟩, ⟨-3319518, -3319506⟩⟩, ⟨⟨797405, 797410⟩, ⟨1353173, 1353178⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, o, ⟨⟨-210154971451921624, -210154971451921613⟩, ⟨356626618221442743, 356626618221442750⟩⟩, ⟨⟨-88345904924609301, -88345904924609263⟩, ⟨-149893713542645318, -149893713542645284⟩⟩, ⟨⟨72022419280692681, 72022419280692746⟩, ⟨-5592216599406, -5592216599339⟩⟩, ⟨⟨-14223449562246719, -14223449562246637⟩, ⟨25686287056320031, 25686287056320114⟩⟩, ⟨⟨-6171285050858887, -6171285050858805⟩, ⟨-10470561639854142, -10470561639854061⟩⟩, ⟨⟨222228097267, 222228097332⟩, ⟨-403935259245, -403935259177⟩⟩, ⟨⟨97351726006, 97351726052⟩, ⟨164141457659, 164141457704⟩⟩, ⟨⟨-101383118, -101383090⟩, ⟨223073464, 223073494⟩⟩, ⟨⟨-58247786, -58247767⟩, ⟨-83035925, -83035906⟩⟩, ⟨⟨1840022, 1840034⟩, ⟨-3322303, -3322292⟩⟩, ⟨⟨798127, 798131⟩, ⟨1354399, 1354402⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, o, ⟨⟨-210168771277332391, -210168771277332380⟩, ⟨356650036106988287, 356650036106988294⟩⟩, ⟨⟨-88357508726078417, -88357508726078380⟩, ⟨-149913399729243934, -149913399729243902⟩⟩, ⟨⟨72036608468442253, 72036608468442315⟩, ⟨-5593658376659, -5593658376593⟩⟩, ⟨⟨-14227185776092283, -14227185776092201⟩, ⟨25693034623602840, 25693034623602922⟩⟩, ⟨⟨-6173311572910461, -6173311572910380⟩, ⟨-10473999837972743, -10473999837972661⟩⟩, ⟨⟨222329125433, 222329125500⟩, ⟨-404119072524, -404119072456⟩⟩, ⟨⟨97402442653, 97402442700⟩, ⟨164226899515, 164226899565⟩⟩, ⟨⟨-101448031, -101447997⟩, ⟨223218996, 223219025⟩⟩, ⟨⟨-58289874, -58289853⟩, ⟨-83095113, -83095093⟩⟩, ⟨⟨1841566, 1841578⟩, ⟨-3325091, -3325081⟩⟩, ⟨⟨798849, 798853⟩, ⟨1355624, 1355628⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, o, ⟨⟨-210182572650003978, -210182572650003967⟩, ⟨356673456618188557, 356673456618188564⟩⟩, ⟨⟨-88369114590985448, -88369114590985410⟩, ⟨-149933089415960932, -149933089415960898⟩⟩, ⟨⟨72050801110971010, 72050801110971074⟩, ⟨-5595100645862, -5595100645796⟩⟩, ⟨⟨-14230923144971153, -14230923144971070⟩, ⟨25699784277007598, 25699784277007679⟩⟩, ⟨⟨-6175338854627616, -6175338854627532⟩, ⟨-10477439324876257, -10477439324876175⟩⟩, ⟨⟨222430206328, 222430206396⟩, ⟨-404302981853, -404302981786⟩⟩, ⟨⟨97453189015, 97453189063⟩, ⟨164312391386, 164312391432⟩⟩, ⟨⟨-101512987, -101512956⟩, ⟨223364633, 223364665⟩⟩, ⟨⟨-58331995, -58331973⟩, ⟨-83154349, -83154328⟩⟩, ⟨⟨1843112, 1843125⟩, ⟨-3327884, -3327873⟩⟩, ⟨⟨799573, 799577⟩, ⟨1356851, 1356856⟩⟩, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, o, ⟨⟨-210196375570152018, -210196375570152007⟩, ⟨356696879755409472, 356696879755409479⟩⟩, ⟨⟨-88380722519768277, -88380722519768239⟩, ⟨-149952782603538820, -149952782603538788⟩⟩, ⟨⟨72064997209250105, 72064997209250172⟩, ⟨-5596543407225, -5596543407154⟩⟩, ⟨⟨-14234661669286024, -14234661669285930⟩, ⟨25706536017261683, 25706536017261773⟩⟩, ⟨⟨-6177366896326073, -6177366896325981⟩, ⟨-10480880101100268, -10480880101100176⟩⟩, ⟨⟨222531339981, 222531340051⟩, ⟨-404486987292, -404486987222⟩⟩, ⟨⟨97503965110, 97503965159⟩, ⟨164397933294, 164397933342⟩⟩, ⟨⟨-101577990, -101577960⟩, ⟨223510376, 223510409⟩⟩, ⟨⟨-58374148, -58374128⟩, ⟨-83213631, -83213612⟩⟩, ⟨⟨1844661, 1844671⟩, ⟨-3330676, -3330666⟩⟩, ⟨⟨800296, 800300⟩, ⟨1358079, 1358083⟩⟩, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, o, ⟨⟨-210210180037992170, -210210180037992159⟩, ⟨356720305519017002, 356720305519017009⟩⟩, ⟨⟨-88392332512864892, -88392332512864853⟩, ⟨-149972479292720286, -149972479292720252⟩⟩, ⟨⟨72079196764250983, 72079196764251053⟩, ⟨-5597986660953, -5597986660883⟩⟩, ⟨⟨-14238401349439721, -14238401349439632⟩, ⟨25713289845092762, 25713289845092854⟩⟩, ⟨⟨-6179395698321685, -6179395698321594⟩, ⟨-10484322167180587, -10484322167180495⟩⟩, ⟨⟨222632526423, 222632526498⟩, ⟨-404671088898, -404671088823⟩⟩, ⟨⟨97554770958, 97554771010⟩, ⟨164483525276, 164483525330⟩⟩, ⟨⟨-101643041, -101643009⟩, ⟨223656227, 223656259⟩⟩, ⟨⟨-58416336, -58416314⟩, ⟨-83272959, -83272940⟩⟩, ⟨⟨1846209, 1846220⟩, ⟨-3333474, -3333463⟩⟩, ⟨⟨801021, 801025⟩, ⟨1359309, 1359313⟩⟩, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, o, ⟨⟨-210223986053740126, -210223986053740115⟩, ⟨356743733909377170, 356743733909377177⟩⟩, ⟨⟨-88403944570713381, -88403944570713342⟩, ⟨-149992179484248184, -149992179484248150⟩⟩, ⟨⟨72093399776945397, 72093399776945463⟩, ⟨-5599430407260, -5599430407190⟩⟩, ⟨⟨-14242142185835246, -14242142185835160⟩, ⟨25720045761228767, 25720045761228854⟩⟩, ⟨⟨-6181425260930455, -6181425260930370⟩, ⟨-10487765523653276, -10487765523653191⟩⟩, ⟨⟨222733765691, 222733765759⟩, ⟨-404855286722, -404855286654⟩⟩, ⟨⟨97605606583, 97605606630⟩, ⟨164569167372, 164569167417⟩⟩, ⟨⟨-101708134, -101708107⟩, ⟨223802186, 223802215⟩⟩, ⟨⟨-58458555, -58458538⟩, ⟨-83332335, -83332316⟩⟩, ⟨⟨1847759, 1847771⟩, ⟨-3336272, -3336260⟩⟩, ⟨⟨801746, 801750⟩, ⟨1360539, 1360544⟩⟩, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, o, ⟨⟨-210237793617611607, -210237793617611596⟩, ⟨356767164926856048, 356767164926856055⟩⟩, ⟨⟨-88415558693751931, -88415558693751893⟩, ⟨-150011883178865542, -150011883178865510⟩⟩, ⟨⟨72107606248305388, 72107606248305452⟩, ⟨-5600874646351, -5600874646285⟩⟩, ⟨⟨-14245884178875755, -14245884178875671⟩, ⟨25726803766397904, 25726803766397988⟩⟩, ⟨⟨-6183455584468530, -6183455584468445⟩, ⟨-10491210171054647, -10491210171054562⟩⟩, ⟨⟨222835057806, 222835057875⟩, ⟨-405039580828, -405039580757⟩⟩, ⟨⟨97656471998, 97656472046⟩, ⟨164654859601, 164654859650⟩⟩, ⟨⟨-101773278, -101773248⟩, ⟨223948248, 223948280⟩⟩, ⟨⟨-58500812, -58500792⟩, ⟨-83391757, -83391739⟩⟩, ⟨⟨1849311, 1849322⟩, ⟨-3339073, -3339063⟩⟩, ⟨⟨802472, 802476⟩, ⟨1361771, 1361775⟩⟩, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨-210251602729822365, -210251602729822354⟩, ⟨356790598571819758, 356790598571819765⟩⟩, ⟨⟨-88427174882418837, -88427174882418800⟩, ⟨-150031590377315564, -150031590377315530⟩⟩, ⟨⟨72121816179303303, 72121816179303367⟩, ⟨-5602319378444, -5602319378374⟩⟩, ⟨⟨-14249627328964539, -14249627328964453⟩, ⟨25733563861328662, 25733563861328751⟩⟩, ⟨⟨-6185486669252198, -6185486669252111⟩, ⟨-10494656109921244, -10494656109921156⟩⟩, ⟨⟨222936402803, 222936402874⟩, ⟨-405223971268, -405223971197⟩⟩, ⟨⟨97707367223, 97707367273⟩, ⟨164740602003, 164740602054⟩⟩, ⟨⟨-101838467, -101838435⟩, ⟨224094418, 224094450⟩⟩, ⟨⟨-58543101, -58543079⟩, ⟨-83451225, -83451207⟩⟩, ⟨⟨1850863, 1850875⟩, ⟨-3341877, -3341867⟩⟩, ⟨⟨803198, 803203⟩, ⟨1363004, 1363009⟩⟩, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨-210265413390588180, -210265413390588169⟩, ⟨356814034844634475, 356814034844634482⟩⟩, ⟨⟨-88438793137152496, -88438793137152459⟩, ⟨-150051301080341620, -150051301080341588⟩⟩, ⟨⟨72136029570911793, 72136029570911860⟩, ⟨-5603764603740, -5603764603675⟩⟩, ⟨⟨-14253371636505061, -14253371636504974⟩, ⟨25740326046749816, 25740326046749902⟩⟩, ⟨⟨-6187518515597889, -6187518515597802⟩, ⟨-10498103340789853, -10498103340789765⟩⟩, ⟨⟨223037800720, 223037800789⟩, ⟨-405408458103, -405408458030⟩⟩, ⟨⟨97758292281, 97758292332⟩, ⟨164826394614, 164826394663⟩⟩, ⟨⟨-101903704, -101903673⟩, ⟨224240694, 224240727⟩⟩, ⟨⟨-58585421, -58585401⟩, ⟨-83510742, -83510721⟩⟩, ⟨⟨1852417, 1852428⟩, ⟨-3344684, -3344672⟩⟩, ⟨⟨803926, 803929⟩, ⟨1364238, 1364243⟩⟩, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨-210279225600124865, -210279225600124854⟩, ⟨356837473745666425, 356837473745666432⟩⟩, ⟨⟨-88450413458391401, -88450413458391364⟩, ⟨-150071015288687262, -150071015288687228⟩⟩, ⟨⟨72150246424103809, 72150246424103874⟩, ⟨-5605210322456, -5605210322391⟩⟩, ⟨⟨-14257117101900918, -14257117101900835⟩, ⟨25747090323390401, 25747090323390483⟩⟩, ⟨⟨-6189551123822169, -6189551123822086⟩, ⟨-10501551864197498, -10501551864197417⟩⟩, ⟨⟨223139251580, 223139251647⟩, ⟨-405593041382, -405593041315⟩⟩, ⟨⟨97809247192, 97809247236⟩, ⟨164912237459, 164912237506⟩⟩, ⟨⟨-101968984, -101968955⟩, ⟨224387081, 224387109⟩⟩, ⟨⟨-58627778, -58627759⟩, ⟨-83570303, -83570286⟩⟩, ⟨⟨1853975, 1853985⟩, ⟨-3347493, -3347483⟩⟩, ⟨⟨804654, 804657⟩, ⟨1365474, 1365478⟩⟩, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨-210293039358648261, -210293039358648250⟩, ⟨356860915275281885, 356860915275281892⟩⟩, ⟨⟨-88462035846574146, -88462035846574109⟩, ⟨-150090733003096206, -150090733003096172⟩⟩, ⟨⟨72164466739852597, 72164466739852662⟩, ⟨-5606656534799, -5606656534733⟩⟩, ⟨⟨-14260863725555882, -14260863725555798⟩, ⟨25753856691979743, 25753856691979826⟩⟩, ⟨⟨-6191584494241757, -6191584494241673⟩, ⟨-10505001680681457, -10505001680681372⟩⟩, ⟨⟨223240755412, 223240755484⟩, ⟨-405777721175, -405777721104⟩⟩, ⟨⟨97860231966, 97860232020⟩, ⟨164998130572, 164998130627⟩⟩, ⟨⟨-102034318, -102034283⟩, ⟨224533568, 224533603⟩⟩, ⟨⟨-58670167, -58670147⟩, ⟨-83629914, -83629893⟩⟩, ⟨⟨1855530, 1855542⟩, ⟨-3350306, -3350294⟩⟩, ⟨⟨805383, 805387⟩, ⟨1366711, 1366716⟩⟩, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨-210306854666374239, -210306854666374228⟩, ⟨356884359433847181, 356884359433847188⟩⟩, ⟨⟨-88473660302139438, -88473660302139400⟩, ⟨-150110454224312344, -150110454224312312⟩⟩, ⟨⟨72178690519131711, 72178690519131776⟩, ⟨-5608103240979, -5608103240913⟩⟩, ⟨⟨-14264611507873868, -14264611507873785⟩, ⟨25760625153247436, 25760625153247520⟩⟩, ⟨⟨-6193618627173509, -6193618627173426⟩, ⟨-10508452790779241, -10508452790779159⟩⟩, ⟨⟨223342312258, 223342312330⟩, ⟨-405962497524, -405962497457⟩⟩, ⟨⟨97911246633, 97911246685⟩, ⟨165084073991, 165084074044⟩⟩, ⟨⟨-102099692, -102099658⟩, ⟨224680164, 224680199⟩⟩, ⟨⟨-58712593, -58712570⟩, ⟨-83689569, -83689549⟩⟩, ⟨⟨1857090, 1857102⟩, ⟨-3353119, -3353109⟩⟩, ⟨⟨806112, 806116⟩, ⟨1367949, 1367954⟩⟩, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨-210320671523518702, -210320671523518691⟩, ⟨356907806221728693, 356907806221728700⟩⟩, ⟨⟨-88485286825526070, -88485286825526033⟩, ⟨-150130178953079744, -150130178953079712⟩⟩, ⟨⟨72192917762915002, 72192917762915065⟩, ⟨-5609550441207, -5609550441139⟩⟩, ⟨⟨-14268360449258942, -14268360449258861⟩, ⟨25767395707923364, 25767395707923448⟩⟩, ⟨⟨-6195653522934427, -6195653522934341⟩, ⟨-10511905195028600, -10511905195028518⟩⟩, ⟨⟨223443922140, 223443922213⟩, ⟨-406147370500, -406147370428⟩⟩, ⟨⟨97962291209, 97962291261⟩, ⟨165170067745, 165170067797⟩⟩, ⟨⟨-102165112, -102165082⟩, ⟨224826872, 224826904⟩⟩, ⟨⟨-58755050, -58755030⟩, ⟨-83749272, -83749254⟩⟩, ⟨⟨1858651, 1858662⟩, ⟨-3355936, -3355926⟩⟩, ⟨⟨806842, 806846⟩, ⟨1369189, 1369193⟩⟩, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨-210334489930297580, -210334489930297569⟩, ⟨356931255639292850, 356931255639292857⟩⟩, ⟨⟨-88496915417172957, -88496915417172919⟩, ⟨-150149907190142640, -150149907190142608⟩⟩, ⟨⟨72207148472176619, 72207148472176683⟩, ⟨-5610998135695, -5610998135629⟩⟩, ⟨⟨-14272110550115330, -14272110550115247⟩, ⟨25774168356737681, 25774168356737765⟩⟩, ⟨⟨-6197689181841648, -6197689181841565⟩, ⟨-10515358893967534, -10515358893967451⟩⟩, ⟨⟨223545585095, 223545585163⟩, ⟨-406332340152, -406332340080⟩⟩, ⟨⟨98013365715, 98013365765⟩, ⟨165256111869, 165256111919⟩⟩, ⟨⟨-102230583, -102230550⟩, ⟨224973683, 224973716⟩⟩, ⟨⟨-58797542, -58797521⟩, ⟨-83809024, -83809002⟩⟩, ⟨⟨1860211, 1860223⟩, ⟨-3358756, -3358744⟩⟩, ⟨⟨807573, 807577⟩, ⟨1370428, 1370433⟩⟩],
  [⟨⟨0, 1⟩, ⟨0, 0⟩⟩, ⟨⟨-10, 2⟩, ⟨-3, 4⟩⟩, ⟨⟨-25, 49⟩, ⟨-35, 29⟩⟩, ⟨⟨-168, 119⟩, ⟨-127, 150⟩⟩, ⟨⟨-370, 442⟩, ⟨-429, 375⟩⟩, ⟨⟨-924, 838⟩, ⟨-832, 920⟩⟩, ⟨⟨-1187, 1903⟩, ⟨-1596, 1481⟩⟩, ⟨⟨-27506, -22845⟩, ⟨-1990, 2653⟩⟩, ⟨⟨1556045, 1562427⟩, ⟨-24728, -18364⟩⟩, ⟨⟨-78283454, -78275202⟩, ⟨1330539, 1338768⟩⟩, ⟨⟨3194467019, 3194477258⟩, ⟨-67125268, -67115055⟩⟩, ⟨⟨-105850185580, -105850173381⟩, ⟨2744869023, 2744881195⟩⟩, ⟨⟨2832288197964, 2832288211988⟩, ⟨-91191032229, -91191018234⟩⟩, ⟨⟨-60559467191916, -60559467176078⟩, ⟨2448169286810, 2448169302625⟩⟩, ⟨⟨1017523036177319, 1017523036195167⟩, ⟨-52574448020014, -52574448002196⟩⟩, ⟨⟨-13097703417172458, -13097703417152537⟩, ⟨888595711249015, 888595711268894⟩⟩, ⟨⟨124323024908760551, 124323024908782272⟩, ⟨-11535117605496236, -11535117605474560⟩⟩, ⟨⟨-820973098368518714, -820973098368495459⟩, ⟨110910463513585938, 110910463513609153⟩⟩, ⟨⟨3449846580166252872, 3449846580166277889⟩, ⟨-748305625052019416, -748305625051994412⟩⟩, ⟨⟨-8201540802490652202, -8201540802490624876⟩, ⟨3273699369762257517, 3273699369762284868⟩⟩, ⟨⟨11161145740035857996, 11161145740035887483⟩, ⟨-8467053897253658365, -8467053897253628864⟩⟩, ⟨⟨-7015514024208687508, -7015514024208657860⟩, ⟨13359178359311303175, 13359178359311332810⟩⟩, ⟨⟨-3272700934877355344, -3272700934877329230⟩, ⟨-12076514560524262668, -12076514560524236566⟩⟩, ⟨⟨11190768858808225467, 11190768858808244660⟩, ⟨2748041986909937531, 2748041986909956722⟩⟩, ⟨⟨-10440894852523286958, -10440894852523275591⟩, ⟨8250051167676942870, 8250051167676954243⟩⟩, ⟨⟨4192458869646427968, 4192458869646433242⟩, ⟨-12647880950360142294, -12647880950360137020⟩⟩, ⟨⟨467625086399023452, 467625086399025293⟩, ⟨9352303924952154017, 9352303924952155860⟩⟩, ⟨⟨-1221380942405683077, -1221380942405682627⟩, ⟨-3884193390868141466, -3884193390868141017⟩⟩, ⟨⟨398974505201932670, 398974505201932733⟩, ⟨740459888616843365, 740459888616843428⟩⟩],
  [o],
  [⟨⟨-5, 5⟩, ⟨-5, 5⟩⟩, ⟨⟨-68, 68⟩, ⟨-68, 68⟩⟩, ⟨⟨-379, 379⟩, ⟨-379, 379⟩⟩, ⟨⟨-1346, 1346⟩, ⟨-1346, 1346⟩⟩, ⟨⟨-3465, 3465⟩, ⟨-3465, 3465⟩⟩, ⟨⟨-6939, 6947⟩, ⟨-6944, 6942⟩⟩, ⟨⟨-11709, 11182⟩, ⟨-11638, 11253⟩⟩, ⟨⟨-18689, 13899⟩, ⟨8450, 41039⟩⟩, ⟨⟨1369529, 1411034⟩, ⟨-672934, -631432⟩⟩, ⟨⟨-63573283, -63524956⟩, ⟨-43187588, -43139262⟩⟩, ⟨⟨-188686354, -188633840⟩, ⟨3115845273, 3115897778⟩⟩, ⟨⟨91426099773, 91426154896⟩, ⟨-47197106224, -47197051098⟩⟩, ⟨⟨-2322810026832, -2322809968606⟩, ⟨-1443469490362, -1443469432114⟩⟩, ⟨⟨-932246020668, -932245957646⟩, ⟨57963370486368, 57963370549387⟩⟩, ⟨⟨832368982073686, 832368982142772⟩, ⟨-483788456629022, -483788456559953⟩⟩, ⟨⟨-10713227747924166, -10713227747848522⟩, ⟨-5817487584999418, -5817487584923766⟩⟩, ⟨⟨6414481431592575, 6414481431675247⟩, ⟨112719777277123841, 112719777277206526⟩⟩, ⟨⟨580581009101050463, 580581009101140782⟩, ⟨-419606496298688636, -419606496298598323⟩⟩, ⟨⟨-2638948703418682657, -2638948703418584921⟩, ⟨-942486531701526918, -942486531701429198⟩⟩, ⟨⟨1933703388394992024, 1933703388395094291⟩, ⟨5498406149349970345, 5498406149350072604⟩⟩, ⟨⟨3466400587942127239, 3466400587942226734⟩, ⟨-5951996328202882560, -5951996328202783043⟩⟩, ⟨⟨-4576070813002170210, -4576070813002084558⟩, ⟨802009177256866935, 802009177256952581⟩⟩, ⟨⟨1107494124368692943, 1107494124368754845⟩, ⟨909328061668814029, 909328061668875923⟩⟩, ⟨⟨-539232051568328958, -539232051568293167⟩, ⟨526153772644938522, 526153772644974325⟩⟩, ⟨⟨2725689876387513310, 2725689876387529175⟩, ⟨623165686377772613, 623165686377788481⟩⟩, ⟨⟨-1966201393022293359, -1966201393022288163⟩, ⟨-4701308412045008898, -4701308412045003708⟩⟩, ⟨⟨-2476581093076583885, -2476581093076582646⟩, ⟨4834742800370765596, 4834742800370766838⟩⟩, ⟨⟨3105697880066098901, 3105697880066099134⟩, ⟨-850947499644466401, -850947499644466169⟩⟩, ⟨⟨-719063270957888343, -719063270957888307⟩, ⟨-433935356788520044, -433935356788520009⟩⟩],
  [o],
  [⟨⟨-5, 5⟩, ⟨-5, 5⟩⟩, ⟨⟨-68, 68⟩, ⟨-68, 68⟩⟩, ⟨⟨-374, 374⟩, ⟨-374, 374⟩⟩, ⟨⟨-1318, 1318⟩, ⟨-1318, 1318⟩⟩, ⟨⟨-3373, 3373⟩, ⟨-3373, 3373⟩⟩, ⟨⟨-6756, 6758⟩, ⟨-6761, 6753⟩⟩, ⟨⟨-11391, 11004⟩, ⟨-11456, 10938⟩⟩, ⟨⟨-40607, -8531⟩, ⟨-13394, 18682⟩⟩, ⟨⟨-649426, -608412⟩, ⟨1367945, 1408957⟩⟩, ⟨⟨43773254, 43821076⟩, ⟨62235244, 62283073⟩⟩, ⟨⟨3076671219, 3076723225⟩, ⟨-248663053, -248611048⟩⟩, ⟨⟨44301555515, 44301610186⟩, ⟨-91303317739, -91303263077⟩⟩, ⟨⟨-1488571981215, -1488571923340⟩, ⟨-2239194168385, -2239194110513⟩⟩, ⟨⟨-56678674105717, -56678674042953⟩, ⟨3086004019692, 3086004082461⟩⟩, ⟨⟨-431106755727810, -431106755658954⟩, ⟨832487065751406, 832487065820270⟩⟩, ⟨⟨6265570722866105, 6265570722941465⟩, ⟨9974216948777548, 9974216948852898⟩⟩, ⟨⟨107769534359211385, 107769534359293642⟩, ⟨-3131107895405322, -3131107895323078⟩⟩, ⟨⟨322966933525762571, 322966933525852339⟩, ⟨-588042882075046223, -588042882074956449⟩⟩, ⟨⟨-1297555932632722912, -1297555932632625843⟩, ⟨-2171177866318462204, -2171177866318365112⟩⟩, ⟨⟨-4863188581306240654, -4863188581306139160⟩, ⟨65011551830884532, 65011551830986028⟩⟩, ⟨⟨-2736612694970426298, -2736612694970327648⟩, ⟨4946158198420729370, 4946158198420827995⟩⟩, ⟨⟨2102258541656339700, 2102258541656424497⟩, ⟨3336013644545587316, 3336013644545672116⟩⟩, ⟨⟨1357033348038861272, 1357033348038922457⟩, ⟨-198965482951398416, -198965482951337222⟩⟩, ⟨⟨-502631754169744748, -502631754169709464⟩, ⟨485708666290407811, 485708666290443092⟩⟩, ⟨⟨1165522604895638511, 1165522604895654064⟩, ⟨2268058278496364525, 2268058278496380077⟩⟩, ⟨⟨4270653062562841729, 4270653062562846748⟩, ⟨41596671771704128, 41596671771709147⟩⟩, ⟨⟨2215306047020592210, 2215306047020593359⟩, ⟨-3839521312481800535, -3839521312481799385⟩⟩, ⟨⟨-1364495616043809392, -1364495616043809193⟩, ⟨-2348057018334378494, -2348057018334378295⟩⟩, ⟨⟨-839258791840262183, -839258791840262154⟩, ⟨-43109153447850, -43109153447821⟩⟩],
  [o],
  [⟨⟨103908124649, 103908124660⟩, ⟨-3, 4⟩⟩, ⟨⟨-5498139129358, -5498139129262⟩, ⟨90217516607, 90217516675⟩⟩, ⟨⟨139557237940186, 139557237940566⟩, ⟨-4728961170676, -4728961170403⟩⟩, ⟨⟨-2262214779717526, -2262214779716515⟩, ⟨118823393000515, 118823393001240⟩⟩, ⟨⟨26302701157880511, 26302701157882662⟩, ⟨-1905199556447253, -1905199556445705⟩⟩, ⟨⟨-233568798876536513, -233568798876532425⟩, ⟨21891896214385009, 21891896214387948⟩⟩, ⟨⟨1646949429894165826, 1646949429894173264⟩, ⟨-191933085692377067, -191933085692371769⟩⟩, ⟨⟨-9465373862545141839, -9465373862545128286⟩, ⟨1334727070560429833, 1334727070560439364⟩⟩, ⟨⟨45161901681351561016, 45161901681351586169⟩, ⟨-7556035872014944862, -7556035872014927308⟩⟩, ⟨⟨-181286549218209278969, -181286549218209231505⟩, ⟨35462667804404926816, 35462667804404959964⟩⟩, ⟨⟨618236767262388269574, 618236767262388359933⟩, ⟨-139806392762339917150, -139806392762339853518⟩⟩, ⟨⟨-1803973118942668978051, -1803973118942668806891⟩, ⟨467416438104158110003, 467416438104158232624⟩⟩, ⟨⟨4526726332988356417292, 4526726332988356732310⟩, ⟨-1334383793727313948795, -1334383793727313716740⟩⟩, ⟨⟨-9801023905718923938032, -9801023905718923391260⟩, ⟨3268259336110907642477, 3268259336110908060393⟩⟩, ⟨⟨18344430410296186917727, 18344430410296187788185⟩, ⟨-6888161074645461579014, -6888161074645460885399⟩⟩, ⟨⟨-29696584913416095556532, -29696584913416094311978⟩, ⟨12509940977113576632480, 12509940977113577666939⟩⟩, ⟨⟨41546102273097936860332, 41546102273097938435050⟩, ⟨-19577187360298419352704, -19577187360298417990397⟩⟩, ⟨⟨-50123177751729181744926, -50123177751729180000578⟩, ⟨26359113427667405615032, 26359113427667407179860⟩⟩, ⟨⟨51957958367196590837085, 51957958367196592513446⟩, ⟨-30441322792393860906904, -30441322792393859354395⟩⟩, ⟨⟨-46031042384923108279675, -46031042384923106894502⟩, ⟨30009015458710625545306, 30009015458710626863396⟩⟩, ⟨⟨34595113374334884917409, 34595113374334885891557⟩, ⟨-25077495804731294555023, -25077495804731293607111⟩⟩, ⟨⟨-21835950202715271065658, -21835950202715270489799⟩, ⟨17595047793077084330592, 17595047793077084900929⟩⟩, ⟨⟨11418217734650825387106, 11418217734650825668710⟩, ⟨-10229325682883711814570, -10229325682883711531970⟩⟩, ⟨⟨-4854612857913085591340, -4854612857913085479808⟩, ⟨4838622458982238250649, 4838622458982238363575⟩⟩, ⟨⟨1634291175665296047327, 1634291175665296082071⟩, ⟨-1814355311643277735118, -1814355311643277699766⟩⟩, ⟨⟨-418819094472006827466, -418819094472006819313⟩, ⟨518789787385134966651, 518789787385134974961⟩⟩, ⟨⟨76693404090268159525, 76693404090268160875⟩, ⟨-106244992222467517445, -106244992222467516072⟩⟩, ⟨⟨-8929282571754387404, -8929282571754387259⟩, ⟨13876244500570177768, 13876244500570177916⟩⟩, ⟨⟨496138938356833817, 496138938356833829⟩, ⟨-868243142124459199, -868243142124459187⟩⟩],
  [o],
  [⟨⟨-76298736366, -76298736258⟩, ⟨-70537216009, -70537215902⟩⟩, ⟨⟨-1108268378078, -1108268377109⟩, ⟨5347290108788, 5347290109755⟩⟩, ⟨⟨129899260686201, 129899260690725⟩, ⟨-45644622913695, -45644622909175⟩⟩, ⟨⟨-1709870829444825, -1709870829429658⟩, ⟨-1411609122651376, -1411609122636212⟩⟩, ⟨⟨-3749201712611795, -3749201712569373⟩, ⟨25341776238769641, 25341776238812063⟩⟩, ⟨⟨208549656999644288, 208549656999752154⟩, ⟨-87413051440285251, -87413051440177388⟩⟩, ⟨⟨-1281715665519350477, -1281715665519091063⟩, ⟨-933654030234446419, -933654030234187001⟩⟩, ⟨⟨-766810126588716595, -766810126588121316⟩, ⟨9036554507968722985, 9036554507969318266⟩⟩, ⟨⟨38598923191494648173, 38598923191495944061⟩, ⟨-19164505055349737867, -19164505055348441977⟩⟩, ⟨⟨-145767017635021526000, -145767017635018878374⟩, ⟨-92169318426501678526, -92169318426499030924⟩⟩, ⟨⟨-10033123379893909559, -10033123379888895589⟩, ⟨587026303018709030550, 587026303018714044517⟩⟩, ⟨⟨1477629509155051533207, 1477629509155060224501⟩, ⟨-866371008335528090236, -866371008335519398583⟩⟩, ⟨⟨-3794312259105421325446, -3794312259105407690246⟩, ⟨-2035739673638479616270, -2035739673638465982043⟩⟩, ⟨⟨526703435844521379916, 526703435844540556736⟩, ⟨9347166626208707365036, 9347166626208726541841⟩⟩, ⟨⟨14506966261706045494980, 14506966261706069486479⟩, ⟨-10046634673400591273953, -10046634673400567277447⟩⟩, ⟨⟨-26414629478391538371935, -26414629478391511843067⟩, ⟨-11637665655105726169147, -11637665655105699649744⟩⟩, ⟨⟨5547029371358615722546, 5547029371358641470137⟩, ⟨40588632306343931711226, 40588632306343957459748⟩⟩, ⟨⟨38930935442753248752731, 38930935442753270550099⟩, ⟨-31958717696272322716822, -31958717696272300901901⟩⟩, ⟨⟨-50585441308477342879763, -50585441308477326880972⟩, ⟨-17391818888461120818485, -17391818888461104844207⟩⟩, ⟨⟨10750073896770496045618, 10750073896770506102907⟩, ⟨47643916589420642813126, 47643916589420652874008⟩⟩, ⟨⟨27187093483516146711763, 27187093483516152077416⟩, ⟨-26670894581434698102861, -26670894581434692722271⟩⟩, ⟨⟨-24403675735201510238624, -24403675735201507829905⟩, ⟨-5977114341961269912077, -5977114341961267518823⟩⟩, ⟨⟨4295630973082053004044, 4295630973082053884912⟩, ⟨13158549182144522136241, 13158549182144523019247⟩⟩, ⟨⟨4021489264112226514304, 4021489264112226772006⟩, ⟨-4789312637089681870538, -4789312637089681610301⟩⟩, ⟨⟨-2235348730955955183375, -2235348730955955124116⟩, ⟨-316320273887285709763, -316320273887285652277⟩⟩, ⟨⟨254543796463340662686, 254543796463340672313⟩, ⟨572280111082076427091, 572280111082076436879⟩⟩, ⟨⟨69968439946651385372, 69968439946651386437⟩, ⟨-104059394461343080677, -104059394461343079563⟩⟩, ⟨⟨-16117530568036116147, -16117530568036116073⟩, ⟨-489386375861549219, -489386375861549159⟩⟩, ⟨⟨507692307692307691, 507692307692307693⟩, ⟨861538461538461537, 861538461538461539⟩⟩],
  [o],
  [⟨⟨-70537216004, -70537215903⟩, ⟨-76298736363, -76298736261⟩⟩, ⟨⟨-5322043348179, -5322043347300⟩, ⟨1156771350103, 1156771350981⟩⟩, ⟨⟨-42830997076714, -42830997072663⟩, ⟨130074121841242, 130074121845290⟩⟩, ⟨⟨1451189492252350, 1451189492265868⟩, ⟨1652577269926372, 1652577269939894⟩⟩, ⟨⟨24891130447273701, 24891130447311599⟩, ⟨-4749556040503958, -4749556040466055⟩⟩, ⟨⟨75118739473846092, 75118739473942864⟩, ⟨-210035453940316118, -210035453940219352⟩⟩, ⟨⟨-999387271572339730, -999387271572106568⟩, ⟨-1197777649412385088, -1197777649412151924⟩⟩, ⟨⟨-8778957429965886989, -8778957429965352664⟩, ⟨1447556083323397277, 1447556083323931589⟩⟩, ⟨⟨-15187811013026785233, -15187811013025626167⟩, ⟨39337155132882881192, 39337155132884040298⟩⟩, ⟨⟨104588504325508179814, 104588504325510536364⟩, ⟨131875468288604702731, 131875468288607059314⟩⟩, ⟨⟨566078753470595088145, 566078753470599524189⟩, ⟨-79047583518631974915, -79047583518627539602⟩⟩, ⟨⟨637046589763529375940, 637046589763537008984⟩, ⟨-1536825343705029214649, -1536825343705021580158⟩⟩, ⟨⟨-2512758693789152661623, -2512758693789140783777⟩, ⟨-3331608723302118082819, -3331608723302106204443⟩⟩, ⟨⟨-8995461571468599396230, -8995461571468582836637⟩, ⟨1035630099590510233934, 1035630099590526784311⟩⟩, ⟨⟨-6898646627992897874112, -6898646627992877367711⟩, ⟨15578415329626637810667, 15578415329626658329216⟩⟩, ⟨⟨16225617767037497614008, 16225617767037520057377⟩, ⟨22608773120326230174745, 22608773120326252620447⟩⟩, ⟨⟨39287312845496884881789, 39287312845496906448230⟩, ⟨-3589942714772717704109, -3589942714772696166309⟩⟩, ⟨⟨20652754269567454947600, 20652754269567472980006⟩, ⟨-43849450380861436518392, -43849450380861418460108⟩⟩, ⟨⟨-29030010786098784699211, -29030010786098771629259⟩, ⟨-42488988209915728758534, -42488988209915715686736⟩⟩, ⟨⟨-46885147194874292549296, -46885147194874284419499⟩, ⟨3202606636393488549371, 3202606636393496658463⟩⟩, ⟨⟨-16376908696777261176691, -16376908696777256905808⟩, ⟨32811713735799173367362, 32811713735799177650519⟩⟩, ⟨⟨13210085022229659002395, 13210085022229660883794⟩, ⟨20306978927391598917370, 20306978927391600798811⟩⟩, ⟨⟨13360322983999748652098, 13360322983999749331667⟩, ⟨-610184035941705428385, -610184035941704751473⟩⟩, ⟨⟨2827707418490869986650, 2827707418490870180290⟩, ⟨-5359820595640407602047, -5359820595640407407532⟩⟩, ⟨⟨-1155723252681602998950, -1155723252681602956611⟩, ⟨-1867342982020680418767, -1867342982020680376448⟩⟩, ⟨⟨-612089236935708504394, -612089236935708497708⟩, ⟨14112112139524800358, 14112112139524807019⟩⟩, ⟨⟨-60008321092914647583, -60008321092914646937⟩, ⟨107745520736358670316, 107745520736358670965⟩⟩, ⟨⟨8096679166052901317, 8096679166052901344⟩, ⟨13775876329332175051, 13775876329332175078⟩⟩, o],
  [o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨5934159345380992, 5934159345381008⟩, ⟨10714534900111460, 10714534900111475⟩⟩, ⟨⟨-32, 33⟩, ⟨-33, 33⟩⟩, ⟨⟨5516989512557550, 5516989512557722⟩, ⟨-12157561633958382, -12157561633958211⟩⟩, ⟨⟨-156, 154⟩, ⟨-155, 156⟩⟩, ⟨⟨-9640050023035732, -9640050023035317⟩, ⟨7692045864472970, 7692045864473384⟩⟩, ⟨⟨-206, 208⟩, ⟨-206, 208⟩⟩, ⟨⟨-478984973596245529, -478984973596245224⟩, ⟨-880719782702459799, -880719782702459491⟩⟩, ⟨⟨-79, 77⟩, ⟨-80, 79⟩⟩, ⟨⟨-522555237238514220, -522555237238514166⟩, ⟨874630374021264298, 874630374021264348⟩⟩, ⟨⟨-5, 5⟩, ⟨-3, 3⟩⟩, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨5872932610273451, 5872932610273467⟩, ⟨10603985797543083, 10603985797543098⟩⟩, ⟨⟨-33, 35⟩, ⟨-36, 35⟩⟩, ⟨⟨5458591166376361, 5458591166376536⟩, ⟨-12038856329930970, -12038856329930797⟩⟩, ⟨⟨-156, 156⟩, ⟨-157, 156⟩⟩, ⟨⟨-9525140479760868, -9525140479760448⟩, ⟨7659088363025923, 7659088363026344⟩⟩, ⟨⟨-213, 211⟩, ⟨-210, 211⟩⟩, ⟨⟨-478828921389528958, -478828921389528649⟩, ⟨-880372920939302043, -880372920939301731⟩⟩, ⟨⟨-78, 78⟩, ⟨-78, 80⟩⟩, ⟨⟨-522435694768931651, -522435694768931597⟩, ⟨874467878830795346, 874467878830795395⟩⟩, ⟨⟨-5, 5⟩, ⟨-3, 3⟩⟩, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨5812398198707592, 5812398198707608⟩, ⟨10494686732986455, 10494686732986470⟩⟩, ⟨⟨-32, 32⟩, ⟨-33, 33⟩⟩, ⟨⟨5400861131946917, 5400861131947087⟩, ⟨-11921441788148260, -11921441788148091⟩⟩, ⟨⟨-155, 157⟩, ⟨-155, 153⟩⟩, ⟨⟨-9411555312171937, -9411555312171516⟩, ⟨7626315000706368, 7626315000706789⟩⟩, ⟨⟨-212, 213⟩, ⟨-214, 211⟩⟩, ⟨⟨-478672793811868891, -478672793811868581⟩, ⟨-880026278621166836, -880026278621166525⟩⟩, ⟨⟨-79, 80⟩, ⟨-78, 78⟩⟩, ⟨⟨-522316273923868649, -522316273923868595⟩, ⟨874305413832668563, 874305413832668611⟩⟩, ⟨⟨-5, 5⟩, ⟨-3, 3⟩⟩, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨5752547690316999, 5752547690317014⟩, ⟨10386622502887953, 10386622502887968⟩⟩, ⟨⟨-29, 31⟩, ⟨-31, 32⟩⟩, ⟨⟨5343791240404496, 5343791240404652⟩, ⟨-11805302770222266, -11805302770222110⟩⟩, ⟨⟨-145, 145⟩, ⟨-145, 145⟩⟩, ⟨⟨-9299278578787348, -9299278578786939⟩, ⟨7593724546325657, 7593724546326064⟩⟩, ⟨⟨-214, 213⟩, ⟨-211, 212⟩⟩, ⟨⟨-478516591853319178, -478516591853318861⟩, ⟨-879679855197624893, -879679855197624577⟩⟩, ⟨⟨-81, 80⟩, ⟨-81, 81⟩⟩, ⟨⟨-522196974179657640, -522196974179657585⟩, ⟨874142979022675374, 874142979022675423⟩⟩, ⟨⟨-5, 5⟩, ⟨-3, 3⟩⟩, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨5693372773136339, 5693372773136355⟩, ⟨10279778099419601, 10279778099419618⟩⟩, ⟨⟨-35, 35⟩, ⟨-35, 36⟩⟩, ⟨⟨5287373428136606, 5287373428136778⟩, ⟨-11690424229265846, -11690424229265675⟩⟩, ⟨⟨-148, 148⟩, ⟨-150, 149⟩⟩, ⟨⟨-9188294539453326, -9188294539452932⟩, ⟨7561315777960407, 7561315777960801⟩⟩, ⟨⟨-199, 201⟩, ⟨-199, 199⟩⟩, ⟨⟨-478360316495854792, -478360316495854492⟩, ⟨-879333650120988460, -879333650120988160⟩⟩, ⟨⟨-77, 78⟩, ⟨-79, 79⟩⟩, ⟨⟨-522077795015344244, -522077795015344191⟩, ⟨873980574396607199, 873980574396607249⟩⟩, ⟨⟨-5, 5⟩, ⟨-3, 3⟩⟩, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨5634865242145736, 5634865242145754⟩, ⟨10174138707850832, 10174138707850849⟩⟩, ⟨⟨-35, 36⟩, ⟨-37, 36⟩⟩, ⟨⟨5231599735372447, 5231599735372623⟩, ⟨-11576791307373825, -11576791307373648⟩⟩, ⟨⟨-157, 153⟩, ⟨-155, 154⟩⟩, ⟨⟨-9078587652700355, -9078587652699943⟩, ⟨7529087482877818, 7529087482878227⟩⟩, ⟨⟨-208, 208⟩, ⟨-207, 209⟩⟩, ⟨⟨-478203968713440560, -478203968713440251⟩, ⟨-878987662846298003, -878987662846297691⟩⟩, ⟨⟨-81, 81⟩, ⟨-80, 81⟩⟩, ⟨⟨-521958735912674661, -521958735912674606⟩, ⟨873818199950255463, 873818199950255513⟩⟩, ⟨⟨-5, 5⟩, ⟨-3, 3⟩⟩, o]
]

private def st9_8 : List (List CFpIv) := [
  [o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-5325670316499980, -5325670316499936⟩, ⟨-21, 21⟩⟩, ⟨⟨-43, 43⟩, ⟨-46, 46⟩⟩, ⟨⟨909469663377507, 909469663377633⟩, ⟨-64, 63⟩⟩, ⟨⟨-68, 67⟩, ⟨-68, 68⟩⟩, ⟨⟨-5022864098155878, -5022864098155760⟩, ⟨-57, 60⟩⟩, ⟨⟨-44, 44⟩, ⟨-44, 42⟩⟩, ⟨⟨78710061730, 78710061788⟩, ⟨-30, 30⟩⟩, ⟨⟨-20, 20⟩, ⟨-19, 18⟩⟩, ⟨⟨-39889490, -39889466⟩, ⟨-11, 11⟩⟩, ⟨⟨-5, 5⟩, ⟨-6, 7⟩⟩, ⟨⟨648223, 648228⟩, ⟨-2, 1⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-5326370581746254, -5326370581746210⟩, ⟨-19, 21⟩⟩, ⟨⟨-41, 43⟩, ⟨-46, 44⟩⟩, ⟨⟨909708529822681, 909708529822806⟩, ⟨-64, 63⟩⟩, ⟨⟨-68, 69⟩, ⟨-68, 69⟩⟩, ⟨⟨-5024843014264599, -5024843014264477⟩, ⟨-60, 61⟩⟩, ⟨⟨-45, 45⟩, ⟨-45, 45⟩⟩, ⟨⟨78756196130, 78756196191⟩, ⟨-29, 31⟩⟩, ⟨⟨-20, 20⟩, ⟨-19, 20⟩⟩, ⟨⟨-39920543, -39920519⟩, ⟨-13, 12⟩⟩, ⟨⟨-7, 6⟩, ⟨-7, 6⟩⟩, ⟨⟨648852, 648857⟩, ⟨-2, 2⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-5327070971811364, -5327070971811319⟩, ⟨-20, 20⟩⟩, ⟨⟨-42, 43⟩, ⟨-44, 45⟩⟩, ⟨⟨909947470106223, 909947470106344⟩, ⟨-61, 60⟩⟩, ⟨⟨-66, 65⟩, ⟨-66, 65⟩⟩, ⟨⟨-5026822802009371, -5026822802009254⟩, ⟨-57, 58⟩⟩, ⟨⟨-46, 45⟩, ⟨-45, 45⟩⟩, ⟨⟨78802360467, 78802360530⟩, ⟨-31, 32⟩⟩, ⟨⟨-21, 21⟩, ⟨-20, 19⟩⟩, ⟨⟨-39951623, -39951597⟩, ⟨-12, 12⟩⟩, ⟨⟨-6, 6⟩, ⟨-7, 6⟩⟩, ⟨⟨649483, 649486⟩, ⟨-2, 2⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-5327771486721941, -5327771486721894⟩, ⟨-21, 21⟩⟩, ⟨⟨-45, 45⟩, ⟨-45, 46⟩⟩, ⟨⟨910186484253866, 910186484253991⟩, ⟨-63, 63⟩⟩, ⟨⟨-68, 69⟩, ⟨-67, 68⟩⟩, ⟨⟨-5028803461810378, -5028803461810254⟩, ⟨-63, 63⟩⟩, ⟨⟨-48, 49⟩, ⟨-49, 48⟩⟩, ⟨⟨78848554760, 78848554825⟩, ⟨-31, 30⟩⟩, ⟨⟨-21, 20⟩, ⟨-21, 20⟩⟩, ⟨⟨-39982730, -39982704⟩, ⟨-13, 13⟩⟩, ⟨⟨-6, 7⟩, ⟨-7, 7⟩⟩, ⟨⟨650112, 650117⟩, ⟨-2, 2⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-5328472126504615, -5328472126504570⟩, ⟨-21, 21⟩⟩, ⟨⟨-44, 44⟩, ⟨-44, 45⟩⟩, ⟨⟨910425572291372, 910425572291493⟩, ⟨-61, 62⟩⟩, ⟨⟨-64, 66⟩, ⟨-65, 65⟩⟩, ⟨⟨-5030784994088001, -5030784994087887⟩, ⟨-59, 58⟩⟩, ⟨⟨-43, 43⟩, ⟨-43, 42⟩⟩, ⟨⟨78894779035, 78894779091⟩, ⟨-28, 29⟩⟩, ⟨⟨-18, 19⟩, ⟨-20, 17⟩⟩, ⟨⟨-40013862, -40013837⟩, ⟨-12, 11⟩⟩, ⟨⟨-6, 7⟩, ⟨-6, 6⟩⟩, ⟨⟨650744, 650748⟩, ⟨-2, 2⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-5329172891186024, -5329172891185980⟩, ⟨-21, 19⟩⟩, ⟨⟨-41, 42⟩, ⟨-44, 44⟩⟩, ⟨⟨910664734244496, 910664734244616⟩, ⟨-59, 62⟩⟩, ⟨⟨-64, 65⟩, ⟨-63, 67⟩⟩, ⟨⟨-5032767399262864, -5032767399262749⟩, ⟨-59, 57⟩⟩, ⟨⟨-44, 44⟩, ⟨-46, 45⟩⟩, ⟨⟨78941033301, 78941033365⟩, ⟨-29, 29⟩⟩, ⟨⟨-21, 21⟩, ⟨-20, 20⟩⟩, ⟨⟨-40045022, -40044995⟩, ⟨-11, 12⟩⟩, ⟨⟨-6, 6⟩, ⟨-6, 6⟩⟩, ⟨⟨651376, 651379⟩, ⟨-2, 2⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-5329873780792813, -5329873780792767⟩, ⟨-21, 21⟩⟩, ⟨⟨-44, 43⟩, ⟨-45, 43⟩⟩, ⟨⟨910903970139011, 910903970139133⟩, ⟨-59, 60⟩⟩, ⟨⟨-66, 67⟩, ⟨-64, 67⟩⟩, ⟨⟨-5034750677755789, -5034750677755672⟩, ⟨-59, 57⟩⟩, ⟨⟨-43, 45⟩, ⟨-42, 44⟩⟩, ⟨⟨78987317593, 78987317653⟩, ⟨-30, 31⟩⟩, ⟨⟨-21, 21⟩, ⟨-20, 20⟩⟩, ⟨⟨-40076207, -40076180⟩, ⟨-13, 12⟩⟩, ⟨⟨-5, 7⟩, ⟨-7, 7⟩⟩, ⟨⟨652008, 652013⟩, ⟨-2, 2⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-5330574795351633, -5330574795351587⟩, ⟨-19, 21⟩⟩, ⟨⟨-45, 44⟩, ⟨-47, 46⟩⟩, ⟨⟨911143280000694, 911143280000829⟩, ⟨-66, 65⟩⟩, ⟨⟨-73, 73⟩, ⟨-73, 74⟩⟩, ⟨⟨-5036734829987826, -5036734829987702⟩, ⟨-62, 62⟩⟩, ⟨⟨-45, 46⟩, ⟨-45, 44⟩⟩, ⟨⟨79033631923, 79033631983⟩, ⟨-31, 31⟩⟩, ⟨⟨-21, 19⟩, ⟨-20, 19⟩⟩, ⟨⟨-40107417, -40107394⟩, ⟨-11, 12⟩⟩, ⟨⟨-5, 6⟩, ⟨-7, 6⟩⟩, ⟨⟨652641, 652645⟩, ⟨-2, 2⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-5331275934889141, -5331275934889095⟩, ⟨-21, 21⟩⟩, ⟨⟨-47, 45⟩, ⟨-47, 47⟩⟩, ⟨⟨911382663855353, 911382663855484⟩, ⟨-66, 68⟩⟩, ⟨⟨-73, 72⟩, ⟨-73, 72⟩⟩, ⟨⟨-5038719856380235, -5038719856380106⟩, ⟨-64, 64⟩⟩, ⟨⟨-48, 49⟩, ⟨-49, 49⟩⟩, ⟨⟨79079976314, 79079976378⟩, ⟨-32, 32⟩⟩, ⟨⟨-21, 21⟩, ⟨-19, 20⟩⟩, ⟨⟨-40138656, -40138631⟩, ⟨-13, 12⟩⟩, ⟨⟨-6, 7⟩, ⟨-7, 6⟩⟩, ⟨⟨653275, 653279⟩, ⟨-2, 2⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-5331977199432000, -5331977199431954⟩, ⟨-21, 21⟩⟩, ⟨⟨-45, 44⟩, ⟨-47, 46⟩⟩, ⟨⟨911622121728782, 911622121728909⟩, ⟨-62, 65⟩⟩, ⟨⟨-69, 67⟩, ⟨-69, 67⟩⟩, ⟨⟨-5040705757354495, -5040705757354376⟩, ⟨-59, 59⟩⟩, ⟨⟨-44, 44⟩, ⟨-43, 42⟩⟩, ⟨⟨79126350797, 79126350851⟩, ⟨-28, 29⟩⟩, ⟨⟨-18, 17⟩, ⟨-19, 18⟩⟩, ⟨⟨-40169921, -40169896⟩, ⟨-11, 13⟩⟩, ⟨⟨-6, 7⟩, ⟨-7, 7⟩⟩, ⟨⟨653909, 653914⟩, ⟨-3, 2⟩⟩, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-5332678589006877, -5332678589006832⟩, ⟨-21, 19⟩⟩, ⟨⟨-42, 43⟩, ⟨-45, 44⟩⟩, ⟨⟨911861653646783, 911861653646907⟩, ⟨-62, 61⟩⟩, ⟨⟨-68, 67⟩, ⟨-67, 68⟩⟩, ⟨⟨-5042692533332320, -5042692533332201⟩, ⟨-61, 61⟩⟩, ⟨⟨-45, 46⟩, ⟨-46, 45⟩⟩, ⟨⟨79172755378, 79172755437⟩, ⟨-31, 31⟩⟩, ⟨⟨-21, 18⟩, ⟨-19, 18⟩⟩, ⟨⟨-40201212, -40201189⟩, ⟨-11, 11⟩⟩, ⟨⟨-5, 6⟩, ⟨-7, 5⟩⟩, ⟨⟨654544, 654548⟩, ⟨-3, 2⟩⟩, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-5333380103640452, -5333380103640407⟩, ⟨-21, 21⟩⟩, ⟨⟨-44, 43⟩, ⟨-47, 46⟩⟩, ⟨⟨912101259635187, 912101259635314⟩, ⟨-65, 64⟩⟩, ⟨⟨-68, 71⟩, ⟨-69, 71⟩⟩, ⟨⟨-5044680184735630, -5044680184735506⟩, ⟨-61, 62⟩⟩, ⟨⟨-46, 46⟩, ⟨-46, 47⟩⟩, ⟨⟨79219190087, 79219190149⟩, ⟨-32, 31⟩⟩, ⟨⟨-21, 20⟩, ⟨-19, 19⟩⟩, ⟨⟨-40232531, -40232507⟩, ⟨-11, 12⟩⟩, ⟨⟨-7, 7⟩, ⟨-6, 7⟩⟩, ⟨⟨655180, 655184⟩, ⟨-3, 2⟩⟩, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-5334081743359409, -5334081743359364⟩, ⟨-20, 20⟩⟩, ⟨⟨-45, 44⟩, ⟨-43, 44⟩⟩, ⟨⟨912340939719819, 912340939719946⟩, ⟨-61, 64⟩⟩, ⟨⟨-69, 69⟩, ⟨-69, 70⟩⟩, ⟨⟨-5046668711986554, -5046668711986433⟩, ⟨-62, 63⟩⟩, ⟨⟨-45, 48⟩, ⟨-45, 47⟩⟩, ⟨⟨79265654945, 79265655006⟩, ⟨-32, 31⟩⟩, ⟨⟨-20, 21⟩, ⟨-20, 21⟩⟩, ⟨⟨-40263876, -40263852⟩, ⟨-12, 13⟩⟩, ⟨⟨-6, 6⟩, ⟨-7, 7⟩⟩, ⟨⟨655816, 655821⟩, ⟨-2, 2⟩⟩, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-5334783508190433, -5334783508190388⟩, ⟨-21, 21⟩⟩, ⟨⟨-44, 44⟩, ⟨-44, 44⟩⟩, ⟨⟨912580693926529, 912580693926651⟩, ⟨-61, 59⟩⟩, ⟨⟨-67, 64⟩, ⟨-66, 64⟩⟩, ⟨⟨-5048658115507459, -5048658115507343⟩, ⟨-57, 59⟩⟩, ⟨⟨-41, 43⟩, ⟨-44, 43⟩⟩, ⟨⟨79312149976, 79312150033⟩, ⟨-28, 28⟩⟩, ⟨⟨-18, 19⟩, ⟨-18, 17⟩⟩, ⟨⟨-40295245, -40295223⟩, ⟨-11, 11⟩⟩, ⟨⟨-5, 5⟩, ⟨-7, 5⟩⟩, ⟨⟨656454, 656457⟩, ⟨-2, 2⟩⟩, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-5335485398160216, -5335485398160172⟩, ⟨-21, 21⟩⟩, ⟨⟨-44, 43⟩, ⟨-45, 44⟩⟩, ⟨⟨912820522281160, 912820522281283⟩, ⟨-59, 62⟩⟩, ⟨⟨-66, 68⟩, ⟨-67, 68⟩⟩, ⟨⟨-5050648395720927, -5050648395720804⟩, ⟨-61, 60⟩⟩, ⟨⟨-47, 49⟩, ⟨-47, 50⟩⟩, ⟨⟨79358675188, 79358675256⟩, ⟨-34, 34⟩⟩, ⟨⟨-20, 22⟩, ⟨-21, 22⟩⟩, ⟨⟨-40326646, -40326621⟩, ⟨-13, 12⟩⟩, ⟨⟨-6, 7⟩, ⟨-7, 7⟩⟩, ⟨⟨657091, 657096⟩, ⟨-3, 2⟩⟩, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-5336187413295465, -5336187413295420⟩, ⟨-20, 20⟩⟩, ⟨⟨-44, 43⟩, ⟨-44, 45⟩⟩, ⟨⟨913060424809572, 913060424809694⟩, ⟨-62, 61⟩⟩, ⟨⟨-66, 66⟩, ⟨-69, 63⟩⟩, ⟨⟨-5052639553049744, -5052639553049622⟩, ⟨-57, 58⟩⟩, ⟨⟨-47, 47⟩, ⟨-47, 48⟩⟩, ⟨⟨79405230622, 79405230687⟩, ⟨-35, 32⟩⟩, ⟨⟨-23, 22⟩, ⟨-20, 21⟩⟩, ⟨⟨-40358070, -40358044⟩, ⟨-13, 13⟩⟩, ⟨⟨-6, 6⟩, ⟨-6, 7⟩⟩, ⟨⟨657729, 657734⟩, ⟨-2, 3⟩⟩, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-5336889553622881, -5336889553622837⟩, ⟨-21, 19⟩⟩, ⟨⟨-42, 43⟩, ⟨-44, 45⟩⟩, ⟨⟨913300401537640, 913300401537760⟩, ⟨-62, 60⟩⟩, ⟨⟨-68, 67⟩, ⟨-66, 65⟩⟩, ⟨⟨-5054631587916935, -5054631587916812⟩, ⟨-60, 62⟩⟩, ⟨⟨-47, 47⟩, ⟨-48, 48⟩⟩, ⟨⟨79451816291, 79451816351⟩, ⟨-32, 32⟩⟩, ⟨⟨-20, 20⟩, ⟨-19, 18⟩⟩, ⟨⟨-40389520, -40389497⟩, ⟨-12, 11⟩⟩, ⟨⟨-6, 6⟩, ⟨-5, 6⟩⟩, ⟨⟨658369, 658373⟩, ⟨-2, 2⟩⟩, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-5337591819169186, -5337591819169141⟩, ⟨-20, 20⟩⟩, ⟨⟨-42, 43⟩, ⟨-44, 44⟩⟩, ⟨⟨913540452491240, 913540452491363⟩, ⟨-62, 61⟩⟩, ⟨⟨-66, 66⟩, ⟨-65, 67⟩⟩, ⟨⟨-5056624500745730, -5056624500745613⟩, ⟨-61, 61⟩⟩, ⟨⟨-46, 46⟩, ⟨-45, 47⟩⟩, ⟨⟨79498432212, 79498432275⟩, ⟨-32, 31⟩⟩, ⟨⟨-21, 20⟩, ⟨-22, 21⟩⟩, ⟨⟨-40421002, -40420975⟩, ⟨-13, 14⟩⟩, ⟨⟨-6, 7⟩, ⟨-7, 7⟩⟩, ⟨⟨659008, 659013⟩, ⟨-2, 2⟩⟩, z, z, z],
  [⟨⟨0, 1⟩, ⟨0, 0⟩⟩, ⟨⟨-13, 3⟩, ⟨-4, 4⟩⟩, ⟨⟨-39, 71⟩, ⟨-45, 46⟩⟩, ⟨⟨-297, 218⟩, ⟨-249, 246⟩⟩, ⟨⟨-820, 967⟩, ⟨-887, 885⟩⟩, ⟨⟨-2511, 2279⟩, ⟨-2384, 2390⟩⟩, ⟨⟨-4676, 5624⟩, ⟨-5142, 5136⟩⟩, ⟨⟨-34898, -16380⟩, ⟨-9240, 9245⟩⟩, ⟨⟨1569799, 1598791⟩, ⟨-14485, 14471⟩⟩, ⟨⟨-79847745, -79806649⟩, ⟨-20516, 20537⟩⟩, ⟨⟨3272380565, 3272434977⟩, ⟨-27189, 27171⟩⟩, ⟨⟨-109042317066, -109042248478⟩, ⟨-34259, 34274⟩⟩, ⟨⟨2938543802098, 2938543885128⟩, ⟨-41492, 41480⟩⟩, ⟨⟨-63419262556514, -63419262459351⟩, ⟨-48553, 48560⟩⟩, ⟨⟨1079144382075584, 1079144382186698⟩, ⟨-55531, 55532⟩⟩, ⟨⟨-14144116639776821, -14144116639651325⟩, ⟨-62717, 62708⟩⟩, ⟨⟨138001434664283212, 138001434664423447⟩, ⟨-70064, 70082⟩⟩, ⟨⟨-953949762168079041, -953949762167924731⟩, ⟨-77122, 77100⟩⟩, ⟨⟨4364554252843261862, 4364554252843429152⟩, ⟨-83608, 83627⟩⟩, ⟨⟨-12360568785061264538, -12360568785061084000⟩, ⟨-90278, 90263⟩⟩, ⟨⟨22894308312782530646, 22894308312782726122⟩, ⟨-97740, 97751⟩⟩, ⟨⟨-29102437270525045321, -29102437270524835719⟩, ⟨-104781, 104776⟩⟩, ⟨⟨25774052323033351011, 25774052323033565678⟩, ⟨-107289, 107287⟩⟩, ⟨⟨-14960480078712722670, -14960480078712521742⟩, ⟨-100425, 100433⟩⟩, ⟨⟨2190637082312197670, 2190637082312363123⟩, ⟨-82722, 82711⟩⟩, ⟨⟨9784078695289316267, 9784078695289432812⟩, ⟨-58265, 58276⟩⟩, ⟨⟨-19588055084097536244, -19588055084097467445⟩, ⟨-34393, 34381⟩⟩, ⟨⟨23715013608072949385, 23715013608072982813⟩, ⟨-16687, 16694⟩⟩, ⟨⟨-19907997726763921364, -19907997726763908268⟩, ⟨-6523, 6523⟩⟩, ⟨⟨11491547162728462213, 11491547162728466228⟩, ⟨-1993, 1985⟩⟩, ⟨⟨-4316859215582476049, -4316859215582475135⟩, ⟨-444, 452⟩⟩, ⟨⟨940689288874811994, 940689288874812134⟩, ⟨-69, 66⟩⟩, ⟨⟨-89408678866661368, -89408678866661356⟩, ⟨-5, 6⟩⟩],
  [o],
  [⟨⟨-5, 5⟩, ⟨-5, 5⟩⟩, ⟨⟨-91, 91⟩, ⟨-91, 91⟩⟩, ⟨⟨-631, 631⟩, ⟨-631, 631⟩⟩, ⟨⟨-2873, 2873⟩, ⟨-2873, 2873⟩⟩, ⟨⟨-9494, 9494⟩, ⟨-9494, 9494⟩⟩, ⟨⟨-24295, 24303⟩, ⟨-24300, 24298⟩⟩, ⟨⟨-50700, 50166⟩, ⟨-50632, 50234⟩⟩, ⟨⟨-90783, 85322⟩, ⟨-62704, 113404⟩⟩, ⟨⟨1309715, 1576707⟩, ⟨-787211, -520222⟩⟩, ⟨⟨-65480669, -65119720⟩, ⟨-46116583, -45755632⟩⟩, ⟨⟨-263846833, -263402319⟩, ⟨3262154220, 3262598724⟩⟩, ⟨⟨98125869826, 98126378275⟩, ⟨-47613377584, -47612869123⟩⟩, ⟨⟨-2447891088395, -2447890535287⟩, ⟨-1627263058059, -1627262504934⟩⟩, ⟨⟨-3447844524226, -3447843935197⟩, ⟨63349822239800, 63349822828808⟩⟩, ⟨⟨958744044587023, 958744045216550⟩, ⟨-496535882332989, -496535881703470⟩⟩, ⟨⟨-11985981500894840, -11985981500213261⟩, ⟨-7528104850337839, -7528104849656238⟩⟩, ⟨⟨-3990697836629585, -3990697835885370⟩, ⟨138083647311066724, 138083647311810942⟩⟩, ⟨⟨837289823005792080, 837289823006606166⟩, ⟨-460272212526820324, -460272212526006250⟩⟩, ⟨⟨-3759459605089303481, -3759459605088414496⟩, ⟨-2240764965340468350, -2240764965339579376⟩⟩, ⟨⟨-107683449355535437, -107683449354571714⟩, ⟨12427571789574169860, 12427571789575133589⟩⟩, ⟨⟨20112766941252818808, 20112766941253841048⟩, ⟨-11452724735155668498, -11452724735154646233⟩⟩, ⟨⟨-25606946926160028817, -25606946926158994371⟩, ⟨-15027444200309998266, -15027444200308963849⟩⟩, ⟨⟨-430688945777249131, -430688945776282833⟩, ⟨26644006500718906049, 26644006500719872353⟩⟩, ⟨⟨13984644955510141620, 13984644955510946491⟩, ⟨-7191160346330321990, -7191160346329517103⟩⟩, ⟨⟨-1527315153482582399, -1527315153482003416⟩, ⟨-2026952153647705861, -2026952153647126887⟩⟩, ⟨⟨-948781996057355657, -948781996057005817⟩, ⟨-10306316977130220978, -10306316977129871143⟩⟩, ⟨⟨-17278529163382186483, -17278529163382013089⟩, ⟨10811007304621393469, 10811007304621566871⟩⟩, ⟨⟨21299434682190264616, 21299434682190333734⟩, ⟨11717887981463836748, 11717887981463905859⟩⟩, ⟨⟨-345288560601572456, -345288560601550597⟩, ⟨-20177651970854693770, -20177651970854671909⟩⟩, ⟨⟨-9907912724899472145, -9907912724899466661⟩, ⟨5967924258786172660, 5967924258786178141⟩⟩, ⟨⟨3796219289090727001, 3796219289090728112⟩, ⟨2078265548891243412, 2078265548891244524⟩⟩, ⟨⟨-26938548726356056, -26938548726355877⟩, ⟨-940934175122743280, -940934175122743100⟩⟩, ⟨⟨-75786884293637590, -75786884293637571⟩, ⟨47437667617206995, 47437667617207015⟩⟩],
  [o],
  [⟨⟨-5, 5⟩, ⟨-5, 5⟩⟩, ⟨⟨-91, 91⟩, ⟨-91, 91⟩⟩, ⟨⟨-627, 627⟩, ⟨-627, 627⟩⟩, ⟨⟨-2836, 2836⟩, ⟨-2836, 2836⟩⟩, ⟨⟨-9320, 9320⟩, ⟨-9320, 9320⟩⟩, ⟨⟨-23787, 23789⟩, ⟨-23792, 23784⟩⟩, ⟨⟨-49585, 49184⟩, ⟨-49651, 49118⟩⟩, ⟨⟨-111848, 61147⟩, ⟨-83767, 89229⟩⟩, ⟨⟨-785463, -521975⟩, ⟨1311467, 1574952⟩⟩, ⟨⟨45757236, 46114967⟩, ⟨65121323, 65479063⟩⟩, ⟨⟨3262155538, 3262597384⟩, ⟨-263845486, -263403649⟩⟩, ⟨⟨47612870209, 47613376499⟩, ⟨-98126377179, -98125870896⟩⟩, ⟨⟨-1627263057234, -1627262505745⟩, ⟨-2447891087584, -2447890536092⟩⟩, ⟨⟨-63349822828403, -63349822240197⟩, ⟨3447843935601, 3447844523814⟩⟩, ⟨⟨-496535882333127, -496535881703331⟩, ⟨958744044586882, 958744045216677⟩⟩, ⟨⟨7528104849655616, 7528104850338457⟩, ⟨11985981500212626, 11985981500895457⟩⟩, ⟨⟨138083647311065902, 138083647311811750⟩, ⟨-3990697836630405, -3990697835884559⟩⟩, ⟨⟨460272212526005586, 460272212526820972⟩, ⟨-837289823006606815, -837289823005791415⟩⟩, ⟨⟨-2240764965340468658, -2240764965339579062⟩, ⟨-3759459605089303773, -3759459605088414163⟩⟩, ⟨⟨-12427571789575133522, -12427571789574169889⟩, ⟨107683449354571781, 107683449355535397⟩⟩, ⟨⟨-11452724735155668070, -11452724735154646639⟩, ⟨20112766941252819225, 20112766941253840632⟩⟩, ⟨⟨15027444200308964657, 15027444200309997469⟩, ⟨25606946926158995186, 25606946926160028023⟩⟩, ⟨⟨26644006500718907197, 26644006500719871254⟩, ⟨-430688945777248007, -430688945776283950⟩⟩, ⟨⟨7191160346329518383, 7191160346330320732⟩, ⟨-13984644955510945250, -13984644955510142908⟩⟩, ⟨⟨-2026952153647704637, -2026952153647128134⟩, ⟨-1527315153482581180, -1527315153482004672⟩⟩, ⟨⟨10306316977129872210, 10306316977130219879⟩, ⟨948781996057006899, 948781996057354567⟩⟩, ⟨⟨10811007304621394327, 10811007304621566004⟩, ⟨-17278529163382185622, -17278529163382013943⟩⟩, ⟨⟨-11717887981463905248, -11717887981463837356⟩, ⟨-21299434682190333129, -21299434682190265236⟩⟩, ⟨⟨-20177651970854693410, -20177651970854672287⟩, ⟨-345288560601572094, -345288560601550973⟩⟩, ⟨⟨-5967924258786177972, -5967924258786172840⟩, ⟨9907912724899466840, 9907912724899471973⟩⟩, ⟨⟨2078265548891243474, 2078265548891244465⟩, ⟨3796219289090727065, 3796219289090728055⟩⟩, ⟨⟨940934175122743114, 940934175122743268⟩, ⟨26938548726355889, 26938548726356041⟩⟩, ⟨⟨47437667617206997, 47437667617207013⟩, ⟨-75786884293637590, -75786884293637573⟩⟩],
  [o],
  [⟨⟨103908124649, 103908124660⟩, ⟨-3, 4⟩⟩, ⟨⟨-5861358456474, -5861358456329⟩, ⟨-55, 49⟩⟩, ⟨⟨159321000996782, 159321000997636⟩, ⟨-323, 340⟩⟩, ⟨⟨-2779318070228110, -2779318070224862⟩, ⟨-1329, 1298⟩⟩, ⟨⟨34966099352417780, 34966099352426960⟩, ⟨-3789, 3837⟩⟩, ⟨⟨-337988513557502131, -337988513557480970⟩, ⟨-8999, 8911⟩⟩, ⟨⟨2611407728025356846, 2611407728025399659⟩, ⟨-18205, 18388⟩⟩, ⟨⟨-16565714041620419882, -16565714041620339191⟩, ⟨-34695, 34360⟩⟩, ⟨⟨87950155399395398074, 87950155399395546363⟩, ⟨-62952, 63453⟩⟩, ⟨⟨-396392500995769844994, -396392500995769571523⟩, ⟨-116349, 115720⟩⟩, ⟨⟨1533051103267363608249, 1533051103267364120092⟩, ⟨-216404, 217087⟩⟩, ⟨⟨-5130104370630484249037, -5130104370630483278980⟩, ⟨-411876, 411215⟩⟩, ⟨⟨14948829554932720935480, 14948829554932722775529⟩, ⟨-785684, 786285⟩⟩, ⟨⟨-38117308707687384614037, -38117308707687381186269⟩, ⟨-1482733, 1482169⟩⟩, ⟨⟨85360907018384531125015, 85360907018384537251970⟩, ⟨-2694561, 2695126⟩⟩, ⟨⟨-168324333274558417230036, -168324333274558406960593⟩, ⟨-4602769, 4602231⟩⟩, ⟨⟨292755477970402770223007, 292755477970402786057293⟩, ⟨-7226114, 7226500⟩⟩, ⟨⟨-449436397234142089594751, -449436397234142067455203⟩, ⟨-10263427, 10263331⟩⟩, ⟨⟨608966960414204381021278, 608966960414204408801865⟩, ⟨-13037677, 13037448⟩⟩, ⟨⟨-727527645030371853935067, -727527645030371822897131⟩, ⟨-14691544, 14691987⟩⟩, ⟨⟨764862867792694980522601, 764862867792695011193964⟩, ⟨-14590033, 14589570⟩⟩, ⟨⟨-705457556349732576695116, -705457556349732550058108⟩, ⟨-12689169, 12689447⟩⟩, ⟨⟨568370840602977261980239, 568370840602977282172005⟩, ⟨-9602455, 9602511⟩⟩, ⟨⟨-397659902917992815519960, -397659902917992802265298⟩, ⟨-6274573, 6274178⟩⟩, ⟨⟨239720260454247938172048, 239720260454247945635318⟩, ⟨-3506830, 3507397⟩⟩, ⟨⟨-123221880585684240881560, -123221880585684237319473⟩, ⟨-1657622, 1657118⟩⟩, ⟨⟨53261266729403437332508, 53261266729403438751909⟩, ⟨-652049, 652349⟩⟩, ⟨⟨-18994683746527998775588, -18994683746527998312738⟩, ⟨-209489, 209377⟩⟩, ⟨⟨5441914240537593836985, 5441914240537593957178⟩, ⟨-53372, 53389⟩⟩, ⟨⟨-1203949186171599782892, -1203949186171599758952⟩, ⟨-10391, 10401⟩⟩, ⟨⟨193052063966183680175, 193052063966183683662⟩, ⟨-1483, 1470⟩⟩, ⟨⟨-19963684182849182437, -19963684182849182080⟩, ⟨-144, 152⟩⟩, ⟨⟨999442741730015983, 999442741730016008⟩, ⟨-11, 9⟩⟩],
  [o],
  [⟨⟨-76298736366, -76298736258⟩, ⟨-70537216009, -70537215902⟩⟩, ⟨⟨-1244896042465, -1244896040941⟩, ⟨5728168741652, 5728168743177⟩⟩, ⟨⟨151352821616132, 151352821626665⟩, ⟨-49846845095303, -49846845084773⟩⟩, ⟨⟨-2089149672567816, -2089149672519231⟩, ⟨-1834225192760592, -1834225192712004⟩⟩, ⟨⟨-6551691308569585, -6551691308397487⟩, ⟨34360501546062769, 34360501546234871⟩⟩, ⟨⟨318384009036766823, 318384009037278426⟩, ⟨-113935497299082707, -113935497298571111⟩⟩, ⟨⟨-2006759927765076071, -2006759927763717263⟩, ⟨-1673544809948307594, -1673544809946948779⟩⟩, ⟨⟨-2691954613579012687, -2691954613575656852⟩, ⟨16357940591781002988, 16357940591784358814⟩⟩, ⟨⟨82105921855340943881, 82105921855348795851⟩, ⟨-31738108091059850484, -31738108091051998520⟩⟩, ⟨⟨-311009339710173176657, -311009339710155718239⟩, ⟨-246406410568258460763, -246406410568241002342⟩⟩, ⟨⟨-211339405653814695538, -211339405653778011081⟩, ⟨1520184038846226520234, 1520184038846263204766⟩⟩, ⟨⟨4743722171795206944354, 4743722171795279144704⟩, ⟨-1970460945088222200606, -1970460945088150000550⟩⟩, ⟨⟨-11959811086306614236756, -11959811086306482410585⟩, ⟨-9003769315354748747692, -9003769315354616921983⟩⟩, ⟨⟨-4326665894552530842225, -4326665894552309568294⟩, ⟨37930946813064242078565, 37930946813064463355893⟩⟩, ⟨⟨78140079233111166203670, 78140079233111504952857⟩, ⟨-34718326212107284714052, -34718326212106945971808⟩⟩, ⟨⟨-137142199994714717851996, -137142199994714247976452⟩, ⟨-98124386208674169902013, -98124386208673700031398⟩⟩, ⟨⟨-26206469230094741176908, -26206469230094153934687⟩, ⟨292148304815408414148286, 292148304815409001424759⟩⟩, ⟨⟨407054242245427001819400, 407054242245427659810508⟩, ⟨-192665153697756464013904, -192665153697755806071523⟩⟩, ⟨⟨-504609150915665938401563, -504609150915665280373564⟩, ⟨-343176502611432570812280, -343176502611431912789932⟩⟩, ⟨⟨-47931163609859759379953, -47931163609859174720365⟩, ⟨727513149357511871983962, 727513149357512456734067⟩⟩, ⟨⟨684918475620801447954903, 684918475620801907003252⟩, ⟨-344147790021878446728076, -344147790021877987782697⟩⟩, ⟨⟨-593745167786318430487792, -593745167786318113816321⟩, ⟨-383767186344207667812602, -383767186344207351119332⟩⟩, ⟨⟨-24174883408791858565553, -24174883408791667844434⟩, ⟨569047762981649859125242, 569047762981650049901801⟩⟩, ⟨⟨351781975445118921342429, 351781975445119020702868⟩, ⟨-187127134376131813386211, -187127134376131714082566⟩⟩, ⟨⟨-204674114973157917696498, -204674114973157873385863⟩, ⟨-125656454727868394677975, -125656454727868350348578⟩⟩, ⟨⟨-2379546431464820854680, -2379546431464804123973⟩, ⟨123408836515862800805408, 123408836515862817540583⟩⟩, ⟨⟨46499717214137835649233, 46499717214137840892943⟩, ⟨-26135613573455284839691, -26135613573455279602031⟩⟩, ⟨⟨-16434705688956873855706, -16434705688956872523686⟩, ⟨-9571749624568572302780, -9571749624568570968729⟩⟩, ⟨⟨21793418948407426946, 21793418948407695370⟩, ⟨5447447558585146925164, 5447447558585147193389⟩⟩, ⟨⟨1036248026057225872631, 1036248026057225913997⟩, ⟨-614733578293315791839, -614733578293315750523⟩⟩, ⟨⟨-169141610794869864603, -169141610794869860066⟩, ⟨-93259916432145756573, -93259916432145752021⟩⟩, ⟨⟨551703357110032065, 551703357110032396⟩, ⟨19960878199859934060, 19960878199859934388⟩⟩, ⟨⟨847196772597002365, 847196772597002386⟩, ⟨-530229594136384007, -530229594136383985⟩⟩],
  [o],
  [⟨⟨-70537216004, -70537215903⟩, ⟨-76298736363, -76298736261⟩⟩, ⟨⟨-5728168743135, -5728168741692⟩, ⟨1244896040973, 1244896042414⟩⟩, ⟨⟨-49846845095070, -49846845085044⟩, ⟨151352821616390, 151352821626416⟩⟩, ⟨⟨1834225192713047, 1834225192759700⟩, ⟨2089149672520228, 2089149672566888⟩⟩, ⟨⟨34360501546065530, 34360501546232425⟩, ⟨-6551691308567251, -6551691308400360⟩⟩, ⟨⟨113935497298575904, 113935497299076962⟩, ⟨-318384009037273676, -318384009036772628⟩⟩, ⟨⟨-1673544809948300404, -1673544809946958070⟩, ⟨-2006759927765067429, -2006759927763725082⟩⟩, ⟨⟨-16357940591784348891, -16357940591781012942⟩, ⟨2691954613575668089, 2691954613579004017⟩⟩, ⟨⟨-31738108091059840465, -31738108091052006859⟩, ⟨82105921855340953393, 82105921855348787062⟩⟩, ⟨⟨246406410568241008372, 246406410568258454568⟩, ⟨311009339710155724224, 311009339710173170386⟩⟩, ⟨⟨1520184038846226521553, 1520184038846263202395⟩, ⟨-211339405653814692227, -211339405653778012129⟩⟩, ⟨⟨1970460945088149999227, 1970460945088222203627⟩, ⟨-4743722171795279144947, -4743722171795206938049⟩⟩, ⟨⟨-9003769315354748751317, -9003769315354616904805⟩, ⟨-11959811086306614241733, -11959811086306482397293⟩⟩, ⟨⟨-37930946813064463363122, -37930946813064242036677⟩, ⟨4326665894552309539210, 4326665894552530856907⟩⟩, ⟨⟨-34718326212107284750582, -34718326212106945925630⟩, ⟨78140079233111166115290, 78140079233111504965562⟩⟩, ⟨⟨98124386208673699893525, 98124386208674169930734⟩, ⟨137142199994714247869273, 137142199994714717884630⟩⟩, ⟨⟨292148304815408413951231, 292148304815409001453768⟩, ⟨-26206469230094741246798, -26206469230094153765437⟩⟩, ⟨⟨192665153697755805935318, 192665153697756464184862⟩, ⟨-407054242245427659851034, -407054242245427001535627⟩⟩, ⟨⟨-343176502611432570865649, -343176502611431912475560⟩, ⟨-504609150915665938531539, -504609150915665280197960⟩⟩, ⟨⟨-727513149357512456801293, -727513149357511871827391⟩, ⟨47931163609859174443472, 47931163609859759418607⟩⟩, ⟨⟨-344147790021878446936211, -344147790021877987800267⟩, ⟨684918475620801447844027, 684918475620801907017900⟩⟩, ⟨⟨383767186344207351057408, 383767186344207667759552⟩, ⟨593745167786318113933961, 593745167786318430603304⟩⟩, ⟨⟨569047762981649859319304, 569047762981650049920996⟩, ⟨-24174883408791858428177, -24174883408791667816289⟩⟩, ⟨⟨187127134376131714259720, 187127134376131813412443⟩, ⟨-351781975445119020667516, -351781975445118921512626⟩⟩, ⟨⟨-125656454727868394614918, -125656454727868350446006⟩, ⟨-204674114973157917714709, -204674114973157873548865⟩⟩, ⟨⟨-123408836515862817533322, -123408836515862800924140⟩, ⟨2379546431464804169782, 2379546431464820780097⟩⟩, ⟨⟨-26135613573455284824678, -26135613573455279655700⟩, ⟨46499717214137835708804, 46499717214137840877607⟩⟩, ⟨⟨9571749624568570987154, 9571749624568572293112⟩, ⟨16434705688956872547966, 16434705688956873853923⟩⟩, ⟨⟨5447447558585146933751, 5447447558585147192555⟩, ⟨21793418948407432219, 21793418948407691029⟩⟩, ⟨⟨614733578293315752574, 614733578293315790897⟩, ⟨-1036248026057225913258, -1036248026057225874937⟩⟩, ⟨⟨-93259916432145756385, -93259916432145752357⟩, ⟨-169141610794869864502, -169141610794869860474⟩⟩, ⟨⟨-19960878199859934381, -19960878199859934108⟩, ⟨-551703357110032370, -551703357110032095⟩⟩, ⟨⟨-530229594136384005, -530229594136383988⟩, ⟨847196772597002370, 847196772597002385⟩⟩],
  [o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨12245806159537188, 12245806159537223⟩, ⟨-18, 17⟩⟩, ⟨⟨-86, 85⟩, ⟨-86, 87⟩⟩, ⟨⟨-2026744840230252, -2026744840229726⟩, ⟨-260, 264⟩⟩, ⟨⟨-562, 563⟩, ⟨-562, 565⟩⟩, ⟨⟨7574978482211383, 7574978482213191⟩, ⟨-901, 903⟩⟩, ⟨⟨-1112, 1114⟩, ⟨-1114, 1115⟩⟩, ⟨⟨-1011968010509735843, -1011968010509733709⟩, ⟨-1066, 1067⟩⟩, ⟨⟨-779, 780⟩, ⟨-777, 781⟩⟩, ⟨⟨32863888108908604, 32863888108909450⟩, ⟨-424, 422⟩⟩, ⟨⟨-162, 160⟩, ⟨-164, 163⟩⟩, ⟨⟨-38148209202386509, -38148209202386428⟩, ⟨-40, 40⟩⟩, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, o, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨12117206254809812, 12117206254809846⟩, ⟨-16, 17⟩⟩, ⟨⟨-89, 91⟩, ⟨-91, 89⟩⟩, ⟨⟨-2010971878914075, -2010971878913535⟩, ⟨-269, 269⟩⟩, ⟨⟨-568, 569⟩, ⟨-572, 570⟩⟩, ⟨⟨7543030160369149, 7543030160370975⟩, ⟨-911, 911⟩⟩, ⟨⟨-1132, 1131⟩, ⟨-1131, 1131⟩⟩, ⟨⟨-1011287982978095292, -1011287982978093124⟩, ⟨-1087, 1084⟩⟩, ⟨⟨-790, 789⟩, ⟨-786, 787⟩⟩, ⟨⟨32840644941821201, 32840644941822045⟩, ⟨-423, 423⟩⟩, ⟨⟨-160, 160⟩, ⟨-161, 163⟩⟩, ⟨⟨-38118663392676761, -38118663392676680⟩, ⟨-40, 39⟩⟩, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, o, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨11990081868672636, 11990081868672669⟩, ⟨-17, 17⟩⟩, ⟨⟨-85, 85⟩, ⟨-86, 85⟩⟩, ⟨⟨-1995339836211910, -1995339836211391⟩, ⟨-257, 258⟩⟩, ⟨⟨-558, 557⟩, ⟨-560, 557⟩⟩, ⟨⟨7511259946396998, 7511259946398810⟩, ⟨-907, 908⟩⟩, ⟨⟨-1135, 1134⟩, ⟨-1134, 1130⟩⟩, ⟨⟨-1010609610576867082, -1010609610576864905⟩, ⟨-1088, 1089⟩⟩, ⟨⟨-790, 792⟩, ⟨-792, 788⟩⟩, ⟨⟨32817493604918820, 32817493604919666⟩, ⟨-424, 425⟩⟩, ⟨⟨-161, 162⟩, ⟨-161, 161⟩⟩, ⟨⟨-38089222485699670, -38089222485699588⟩, ⟨-40, 39⟩⟩, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨11864414825292533, 11864414825292565⟩, ⟨-18, 15⟩⟩, ⟨⟨-81, 82⟩, ⟨-82, 80⟩⟩, ⟨⟨-1979847310327351, -1979847310326869⟩, ⟨-240, 240⟩⟩, ⟨⟨-516, 519⟩, ⟨-519, 520⟩⟩, ⟨⟨7479666583530275, 7479666583531995⟩, ⟨-861, 860⟩⟩, ⟨⟨-1106, 1105⟩, ⟨-1104, 1105⟩⟩, ⟨⟨-1009932877232079140, -1009932877232076966⟩, ⟨-1088, 1087⟩⟩, ⟨⟨-803, 803⟩, ⟨-800, 802⟩⟩, ⟨⟨32794433364924785, 32794433364925652⟩, ⟨-432, 431⟩⟩, ⟨⟨-163, 162⟩, ⟨-165, 165⟩⟩, ⟨⟨-38059885960118545, -38059885960118464⟩, ⟨-40, 40⟩⟩, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨11740187185572323, 11740187185572359⟩, ⟨-18, 18⟩⟩, ⟨⟨-92, 94⟩, ⟨-92, 91⟩⟩, ⟨⟨-1964492914612175, -1964492914611638⟩, ⟨-271, 268⟩⟩, ⟨⟨-553, 551⟩, ⟨-553, 554⟩⟩, ⟨⟨7448248825866254, 7448248825867986⟩, ⟨-864, 865⟩⟩, ⟨⟨-1064, 1065⟩, ⟨-1067, 1063⟩⟩, ⟨⟨-1009257767069613488, -1009257767069611431⟩, ⟨-1028, 1031⟩⟩, ⟨⟨-761, 764⟩, ⟨-762, 762⟩⟩, ⟨⟨32771463495137220, 32771463495138057⟩, ⟨-417, 418⟩⟩, ⟨⟨-160, 161⟩, ⟨-161, 162⟩⟩, ⟨⟨-38030653297309900, -38030653297309820⟩, ⟨-40, 41⟩⟩, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨11617381243936000, 11617381243936038⟩, ⟨-19, 19⟩⟩, ⟨⟨-95, 94⟩, ⟨-95, 94⟩⟩, ⟨⟨-1949275277392071, -1949275277391519⟩, ⟨-276, 275⟩⟩, ⟨⟨-572, 570⟩, ⟨-570, 571⟩⟩, ⟨⟨7417005438253204, 7417005438255002⟩, ⟨-900, 901⟩⟩, ⟨⟨-1110, 1110⟩, ⟨-1110, 1110⟩⟩, ⟨⟨-1008584264412585912, -1008584264412583771⟩, ⟨-1070, 1070⟩⟩, ⟨⟨-789, 790⟩, ⟨-787, 790⟩⟩, ⟨⟨32748583275367666, 32748583275368524⟩, ⟨-433, 430⟩⟩, ⟨⟨-164, 164⟩, ⟨-165, 166⟩⟩, ⟨⟨-38001523981350815, -38001523981350733⟩, ⟨-40, 40⟩⟩, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, o]
]

private def st9_9 : List (List CFpIv) := [
  [o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-5325670316499980, -5325670316499936⟩, ⟨-21, 21⟩⟩, ⟨⟨-43, 43⟩, ⟨-46, 46⟩⟩, ⟨⟨909469663377507, 909469663377633⟩, ⟨-64, 63⟩⟩, ⟨⟨-68, 67⟩, ⟨-68, 68⟩⟩, ⟨⟨-5022864098155878, -5022864098155760⟩, ⟨-57, 60⟩⟩, ⟨⟨-44, 44⟩, ⟨-44, 42⟩⟩, ⟨⟨78710061730, 78710061788⟩, ⟨-30, 30⟩⟩, ⟨⟨-20, 20⟩, ⟨-19, 18⟩⟩, ⟨⟨-39889490, -39889466⟩, ⟨-11, 11⟩⟩, ⟨⟨-5, 5⟩, ⟨-6, 7⟩⟩, ⟨⟨648223, 648228⟩, ⟨-2, 1⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-5326370581746254, -5326370581746210⟩, ⟨-19, 21⟩⟩, ⟨⟨-41, 43⟩, ⟨-46, 44⟩⟩, ⟨⟨909708529822681, 909708529822806⟩, ⟨-64, 63⟩⟩, ⟨⟨-68, 69⟩, ⟨-68, 69⟩⟩, ⟨⟨-5024843014264599, -5024843014264477⟩, ⟨-60, 61⟩⟩, ⟨⟨-45, 45⟩, ⟨-45, 45⟩⟩, ⟨⟨78756196130, 78756196191⟩, ⟨-29, 31⟩⟩, ⟨⟨-20, 20⟩, ⟨-19, 20⟩⟩, ⟨⟨-39920543, -39920519⟩, ⟨-13, 12⟩⟩, ⟨⟨-7, 6⟩, ⟨-7, 6⟩⟩, ⟨⟨648852, 648857⟩, ⟨-2, 2⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-5327070971811364, -5327070971811319⟩, ⟨-20, 20⟩⟩, ⟨⟨-42, 43⟩, ⟨-44, 45⟩⟩, ⟨⟨909947470106223, 909947470106344⟩, ⟨-61, 60⟩⟩, ⟨⟨-66, 65⟩, ⟨-66, 65⟩⟩, ⟨⟨-5026822802009371, -5026822802009254⟩, ⟨-57, 58⟩⟩, ⟨⟨-46, 45⟩, ⟨-45, 45⟩⟩, ⟨⟨78802360467, 78802360530⟩, ⟨-31, 32⟩⟩, ⟨⟨-21, 21⟩, ⟨-20, 19⟩⟩, ⟨⟨-39951623, -39951597⟩, ⟨-12, 12⟩⟩, ⟨⟨-6, 6⟩, ⟨-7, 6⟩⟩, ⟨⟨649483, 649486⟩, ⟨-2, 2⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-5327771486721941, -5327771486721894⟩, ⟨-21, 21⟩⟩, ⟨⟨-45, 45⟩, ⟨-45, 46⟩⟩, ⟨⟨910186484253866, 910186484253991⟩, ⟨-63, 63⟩⟩, ⟨⟨-68, 69⟩, ⟨-67, 68⟩⟩, ⟨⟨-5028803461810378, -5028803461810254⟩, ⟨-63, 63⟩⟩, ⟨⟨-48, 49⟩, ⟨-49, 48⟩⟩, ⟨⟨78848554760, 78848554825⟩, ⟨-31, 30⟩⟩, ⟨⟨-21, 20⟩, ⟨-21, 20⟩⟩, ⟨⟨-39982730, -39982704⟩, ⟨-13, 13⟩⟩, ⟨⟨-6, 7⟩, ⟨-7, 7⟩⟩, ⟨⟨650112, 650117⟩, ⟨-2, 2⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-5328472126504615, -5328472126504570⟩, ⟨-21, 21⟩⟩, ⟨⟨-44, 44⟩, ⟨-44, 45⟩⟩, ⟨⟨910425572291372, 910425572291493⟩, ⟨-61, 62⟩⟩, ⟨⟨-64, 66⟩, ⟨-65, 65⟩⟩, ⟨⟨-5030784994088001, -5030784994087887⟩, ⟨-59, 58⟩⟩, ⟨⟨-43, 43⟩, ⟨-43, 42⟩⟩, ⟨⟨78894779035, 78894779091⟩, ⟨-28, 29⟩⟩, ⟨⟨-18, 19⟩, ⟨-20, 17⟩⟩, ⟨⟨-40013862, -40013837⟩, ⟨-12, 11⟩⟩, ⟨⟨-6, 7⟩, ⟨-6, 6⟩⟩, ⟨⟨650744, 650748⟩, ⟨-2, 2⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-5329172891186024, -5329172891185980⟩, ⟨-21, 19⟩⟩, ⟨⟨-41, 42⟩, ⟨-44, 44⟩⟩, ⟨⟨910664734244496, 910664734244616⟩, ⟨-59, 62⟩⟩, ⟨⟨-64, 65⟩, ⟨-63, 67⟩⟩, ⟨⟨-5032767399262864, -5032767399262749⟩, ⟨-59, 57⟩⟩, ⟨⟨-44, 44⟩, ⟨-46, 45⟩⟩, ⟨⟨78941033301, 78941033365⟩, ⟨-29, 29⟩⟩, ⟨⟨-21, 21⟩, ⟨-20, 20⟩⟩, ⟨⟨-40045022, -40044995⟩, ⟨-11, 12⟩⟩, ⟨⟨-6, 6⟩, ⟨-6, 6⟩⟩, ⟨⟨651376, 651379⟩, ⟨-2, 2⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-5329873780792813, -5329873780792767⟩, ⟨-21, 21⟩⟩, ⟨⟨-44, 43⟩, ⟨-45, 43⟩⟩, ⟨⟨910903970139011, 910903970139133⟩, ⟨-59, 60⟩⟩, ⟨⟨-66, 67⟩, ⟨-64, 67⟩⟩, ⟨⟨-5034750677755789, -5034750677755672⟩, ⟨-59, 57⟩⟩, ⟨⟨-43, 45⟩, ⟨-42, 44⟩⟩, ⟨⟨78987317593, 78987317653⟩, ⟨-30, 31⟩⟩, ⟨⟨-21, 21⟩, ⟨-20, 20⟩⟩, ⟨⟨-40076207, -40076180⟩, ⟨-13, 12⟩⟩, ⟨⟨-5, 7⟩, ⟨-7, 7⟩⟩, ⟨⟨652008, 652013⟩, ⟨-2, 2⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-5330574795351633, -5330574795351587⟩, ⟨-19, 21⟩⟩, ⟨⟨-45, 44⟩, ⟨-47, 46⟩⟩, ⟨⟨911143280000694, 911143280000829⟩, ⟨-66, 65⟩⟩, ⟨⟨-73, 73⟩, ⟨-73, 74⟩⟩, ⟨⟨-5036734829987826, -5036734829987702⟩, ⟨-62, 62⟩⟩, ⟨⟨-45, 46⟩, ⟨-45, 44⟩⟩, ⟨⟨79033631923, 79033631983⟩, ⟨-31, 31⟩⟩, ⟨⟨-21, 19⟩, ⟨-20, 19⟩⟩, ⟨⟨-40107417, -40107394⟩, ⟨-11, 12⟩⟩, ⟨⟨-5, 6⟩, ⟨-7, 6⟩⟩, ⟨⟨652641, 652645⟩, ⟨-2, 2⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-5331275934889141, -5331275934889095⟩, ⟨-21, 21⟩⟩, ⟨⟨-47, 45⟩, ⟨-47, 47⟩⟩, ⟨⟨911382663855353, 911382663855484⟩, ⟨-66, 68⟩⟩, ⟨⟨-73, 72⟩, ⟨-73, 72⟩⟩, ⟨⟨-5038719856380235, -5038719856380106⟩, ⟨-64, 64⟩⟩, ⟨⟨-48, 49⟩, ⟨-49, 49⟩⟩, ⟨⟨79079976314, 79079976378⟩, ⟨-32, 32⟩⟩, ⟨⟨-21, 21⟩, ⟨-19, 20⟩⟩, ⟨⟨-40138656, -40138631⟩, ⟨-13, 12⟩⟩, ⟨⟨-6, 7⟩, ⟨-7, 6⟩⟩, ⟨⟨653275, 653279⟩, ⟨-2, 2⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-5331977199432000, -5331977199431954⟩, ⟨-21, 21⟩⟩, ⟨⟨-45, 44⟩, ⟨-47, 46⟩⟩, ⟨⟨911622121728782, 911622121728909⟩, ⟨-62, 65⟩⟩, ⟨⟨-69, 67⟩, ⟨-69, 67⟩⟩, ⟨⟨-5040705757354495, -5040705757354376⟩, ⟨-59, 59⟩⟩, ⟨⟨-44, 44⟩, ⟨-43, 42⟩⟩, ⟨⟨79126350797, 79126350851⟩, ⟨-28, 29⟩⟩, ⟨⟨-18, 17⟩, ⟨-19, 18⟩⟩, ⟨⟨-40169921, -40169896⟩, ⟨-11, 13⟩⟩, ⟨⟨-6, 7⟩, ⟨-7, 7⟩⟩, ⟨⟨653909, 653914⟩, ⟨-3, 2⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-5332678589006877, -5332678589006832⟩, ⟨-21, 19⟩⟩, ⟨⟨-42, 43⟩, ⟨-45, 44⟩⟩, ⟨⟨911861653646783, 911861653646907⟩, ⟨-62, 61⟩⟩, ⟨⟨-68, 67⟩, ⟨-67, 68⟩⟩, ⟨⟨-5042692533332320, -5042692533332201⟩, ⟨-61, 61⟩⟩, ⟨⟨-45, 46⟩, ⟨-46, 45⟩⟩, ⟨⟨79172755378, 79172755437⟩, ⟨-31, 31⟩⟩, ⟨⟨-21, 18⟩, ⟨-19, 18⟩⟩, ⟨⟨-40201212, -40201189⟩, ⟨-11, 11⟩⟩, ⟨⟨-5, 6⟩, ⟨-7, 5⟩⟩, ⟨⟨654544, 654548⟩, ⟨-3, 2⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-5333380103640452, -5333380103640407⟩, ⟨-21, 21⟩⟩, ⟨⟨-44, 43⟩, ⟨-47, 46⟩⟩, ⟨⟨912101259635187, 912101259635314⟩, ⟨-65, 64⟩⟩, ⟨⟨-68, 71⟩, ⟨-69, 71⟩⟩, ⟨⟨-5044680184735630, -5044680184735506⟩, ⟨-61, 62⟩⟩, ⟨⟨-46, 46⟩, ⟨-46, 47⟩⟩, ⟨⟨79219190087, 79219190149⟩, ⟨-32, 31⟩⟩, ⟨⟨-21, 20⟩, ⟨-19, 19⟩⟩, ⟨⟨-40232531, -40232507⟩, ⟨-11, 12⟩⟩, ⟨⟨-7, 7⟩, ⟨-6, 7⟩⟩, ⟨⟨655180, 655184⟩, ⟨-3, 2⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-5334081743359409, -5334081743359364⟩, ⟨-20, 20⟩⟩, ⟨⟨-45, 44⟩, ⟨-43, 44⟩⟩, ⟨⟨912340939719819, 912340939719946⟩, ⟨-61, 64⟩⟩, ⟨⟨-69, 69⟩, ⟨-69, 70⟩⟩, ⟨⟨-5046668711986554, -5046668711986433⟩, ⟨-62, 63⟩⟩, ⟨⟨-45, 48⟩, ⟨-45, 47⟩⟩, ⟨⟨79265654945, 79265655006⟩, ⟨-32, 31⟩⟩, ⟨⟨-20, 21⟩, ⟨-20, 21⟩⟩, ⟨⟨-40263876, -40263852⟩, ⟨-12, 13⟩⟩, ⟨⟨-6, 6⟩, ⟨-7, 7⟩⟩, ⟨⟨655816, 655821⟩, ⟨-2, 2⟩⟩, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-5334783508190433, -5334783508190388⟩, ⟨-21, 21⟩⟩, ⟨⟨-44, 44⟩, ⟨-44, 44⟩⟩, ⟨⟨912580693926529, 912580693926651⟩, ⟨-61, 59⟩⟩, ⟨⟨-67, 64⟩, ⟨-66, 64⟩⟩, ⟨⟨-5048658115507459, -5048658115507343⟩, ⟨-57, 59⟩⟩, ⟨⟨-41, 43⟩, ⟨-44, 43⟩⟩, ⟨⟨79312149976, 79312150033⟩, ⟨-28, 28⟩⟩, ⟨⟨-18, 19⟩, ⟨-18, 17⟩⟩, ⟨⟨-40295245, -40295223⟩, ⟨-11, 11⟩⟩, ⟨⟨-5, 5⟩, ⟨-7, 5⟩⟩, ⟨⟨656454, 656457⟩, ⟨-2, 2⟩⟩, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-5335485398160216, -5335485398160172⟩, ⟨-21, 21⟩⟩, ⟨⟨-44, 43⟩, ⟨-45, 44⟩⟩, ⟨⟨912820522281160, 912820522281283⟩, ⟨-59, 62⟩⟩, ⟨⟨-66, 68⟩, ⟨-67, 68⟩⟩, ⟨⟨-5050648395720927, -5050648395720804⟩, ⟨-61, 60⟩⟩, ⟨⟨-47, 49⟩, ⟨-47, 50⟩⟩, ⟨⟨79358675188, 79358675256⟩, ⟨-34, 34⟩⟩, ⟨⟨-20, 22⟩, ⟨-21, 22⟩⟩, ⟨⟨-40326646, -40326621⟩, ⟨-13, 12⟩⟩, ⟨⟨-6, 7⟩, ⟨-7, 7⟩⟩, ⟨⟨657091, 657096⟩, ⟨-3, 2⟩⟩, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-5336187413295465, -5336187413295420⟩, ⟨-20, 20⟩⟩, ⟨⟨-44, 43⟩, ⟨-44, 45⟩⟩, ⟨⟨913060424809572, 913060424809694⟩, ⟨-62, 61⟩⟩, ⟨⟨-66, 66⟩, ⟨-69, 63⟩⟩, ⟨⟨-5052639553049744, -5052639553049622⟩, ⟨-57, 58⟩⟩, ⟨⟨-47, 47⟩, ⟨-47, 48⟩⟩, ⟨⟨79405230622, 79405230687⟩, ⟨-35, 32⟩⟩, ⟨⟨-23, 22⟩, ⟨-20, 21⟩⟩, ⟨⟨-40358070, -40358044⟩, ⟨-13, 13⟩⟩, ⟨⟨-6, 6⟩, ⟨-6, 7⟩⟩, ⟨⟨657729, 657734⟩, ⟨-2, 3⟩⟩, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-5336889553622881, -5336889553622837⟩, ⟨-21, 19⟩⟩, ⟨⟨-42, 43⟩, ⟨-44, 45⟩⟩, ⟨⟨913300401537640, 913300401537760⟩, ⟨-62, 60⟩⟩, ⟨⟨-68, 67⟩, ⟨-66, 65⟩⟩, ⟨⟨-5054631587916935, -5054631587916812⟩, ⟨-60, 62⟩⟩, ⟨⟨-47, 47⟩, ⟨-48, 48⟩⟩, ⟨⟨79451816291, 79451816351⟩, ⟨-32, 32⟩⟩, ⟨⟨-20, 20⟩, ⟨-19, 18⟩⟩, ⟨⟨-40389520, -40389497⟩, ⟨-12, 11⟩⟩, ⟨⟨-6, 6⟩, ⟨-5, 6⟩⟩, ⟨⟨658369, 658373⟩, ⟨-2, 2⟩⟩, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-5337591819169186, -5337591819169141⟩, ⟨-20, 20⟩⟩, ⟨⟨-42, 43⟩, ⟨-44, 44⟩⟩, ⟨⟨913540452491240, 913540452491363⟩, ⟨-62, 61⟩⟩, ⟨⟨-66, 66⟩, ⟨-65, 67⟩⟩, ⟨⟨-5056624500745730, -5056624500745613⟩, ⟨-61, 61⟩⟩, ⟨⟨-46, 46⟩, ⟨-45, 47⟩⟩, ⟨⟨79498432212, 79498432275⟩, ⟨-32, 31⟩⟩, ⟨⟨-21, 20⟩, ⟨-22, 21⟩⟩, ⟨⟨-40421002, -40420975⟩, ⟨-13, 14⟩⟩, ⟨⟨-6, 7⟩, ⟨-7, 7⟩⟩, ⟨⟨659008, 659013⟩, ⟨-2, 2⟩⟩, z, z, z, z, z, z],
  [⟨⟨0, 1⟩, ⟨0, 0⟩⟩, ⟨⟨-16, 3⟩, ⟨-4, 4⟩⟩, ⟨⟨-45, 93⟩, ⟨-51, 52⟩⟩, ⟨⟨-410, 278⟩, ⟨-318, 315⟩⟩, ⟨⟨-1162, 1443⟩, ⟨-1272, 1274⟩⟩, ⟨⟨-4106, 3608⟩, ⟨-3826, 3834⟩⟩, ⟨⟨-8522, 9910⟩, ⟨-9196, 9179⟩⟩, ⟨⟨-44765, -8044⟩, ⟨-18313, 18332⟩⟩, ⟨⟨1589797, 1652838⟩, ⟨-31484, 31458⟩⟩, ⟨⟨-82159850, -82063510⟩, ⟨-48087, 48133⟩⟩, ⟨⟨3387647313, 3387782329⟩, ⟨-67466, 67407⟩⟩, ⟨⟨-113779441694, -113779264051⟩, ⟨-88711, 88768⟩⟩, ⟨⟨3096811992599, 3096812215369⟩, ⟨-111320, 111272⟩⟩, ⟨⟨-67698735574721, -67698735306035⟩, ⟨-134238, 134273⟩⟩, ⟨⟨1171906953355533, 1171906953669786⟩, ⟨-157052, 157035⟩⟩, ⟨⟨-15731841945309506, -15731841944949695⟩, ⟨-179816, 179811⟩⟩, ⟨⟨158983315037456072, 158983315037862256⟩, ⟨-202961, 202992⟩⟩, ⟨⟨-1161183106652610832, -1161183106652158156⟩, ⟨-226231, 226177⟩⟩, ⟨⟨5825257231917803437, 5825257231918300856⟩, ⟨-248552, 248615⟩⟩, ⟨⟨-19271732697803117504, -19271732697802577045⟩, ⟨-270178, 270119⟩⟩, ⟨⟨43662969459633204363, 43662969459633789136⟩, ⟨-292323, 292370⟩⟩, ⟨⟨-70770708993229113456, -70770708993228482676⟩, ⟨-315338, 315306⟩⟩, ⟨⟨84381966212616855311, 84381966212617523055⟩, ⟨-333711, 333725⟩⟩, ⟨⟨-74185691489989527793, -74185691489988855264⟩, ⟨-336059, 336064⟩⟩, ⟨⟨44345016928424718044, 44345016928425340390⟩, ⟨-311022, 311000⟩⟩, ⟨⟨-6357118531846299811, -6357118531845786032⟩, ⟨-256795, 256827⟩⟩, ⟨⟨-30469575728028060868, -30469575728027690551⟩, ⟨-185134, 185098⟩⟩, ⟨⟨58182798544798141846, 58182798544798371299⟩, ⟨-114623, 114656⟩⟩, ⟨⟨-68271183270232116807, -68271183270231996143⟩, ⟨-60208, 60189⟩⟩, ⟨⟨58287647932989444844, 58287647932989498022⟩, ⟨-26448, 26446⟩⟩, ⟨⟨-36919653018860942876, -36919653018860923540⟩, ⟨-9550, 9569⟩⟩, ⟨⟨17120320538594357729, 17120320538594363403⟩, ⟨-2786, 2767⟩⟩, ⟨⟨-5628422832221595061, -5628422832221593761⟩, ⟨-621, 631⟩⟩, ⟨⟨1238319815929758896, 1238319815929759118⟩, ⟨-106, 103⟩⟩, ⟨⟨-163086812048925410, -163086812048925383⟩, ⟨-12, 13⟩⟩, ⟨⟨9701148354483062, 9701148354483065⟩, ⟨-1, 1⟩⟩],
  [o],
  [⟨⟨-5, 5⟩, ⟨-5, 5⟩⟩, ⟨⟨-106, 106⟩, ⟨-106, 106⟩⟩, ⟨⟨-823, 823⟩, ⟨-823, 823⟩⟩, ⟨⟨-4234, 4234⟩, ⟨-4234, 4234⟩⟩, ⟨⟨-15961, 15961⟩, ⟨-15961, 15961⟩⟩, ⟨⟨-46751, 46759⟩, ⟨-46756, 46754⟩⟩, ⟨⟨-111262, 110720⟩, ⟨-111195, 110788⟩⟩, ⟨⟨-223383, 217818⟩, ⟨-194776, 246428⟩⟩, ⟨⟨1099340, 1853965⟩, ⟨-1046170, -291549⟩⟩, ⟨⟨-67737479, -66600011⟩, ⟨-47819116, -46681643⟩⟩, ⟨⟨-273673890, -272131527⟩, ⟨3376555214, 3378097565⟩⟩, ⟨⟨102387564062, 102389479599⟩, ⟨-49682908371, -49680992816⟩⟩, ⟨⟨-2579738424868, -2579736206297⟩, ⟨-1714882093995, -1714879875414⟩⟩, ⟨⟨-3679643355344, -3679640908259⟩, ⟨67624275996296, 67624278443353⟩⟩, ⟨⟨1041135076032103, 1041135078664970⟩, ⟨-539234587441997, -539234584809126⟩⟩, ⟨⟨-13331516777302960, -13331516774480302⟩, ⟨-8372471514913771, -8372471512091091⟩⟩, ⟨⟨-4584614191508741, -4584614188459606⟩, ⟨159071665477636259, 159071665480685384⟩⟩, ⟨⟨1018972641966559403, 1018972641969879001⟩, ⟨-560386284260846721, -560386284257527133⟩⟩, ⟨⟨-5017550417219269350, -5017550417215643345⟩, ⟨-2987399281886713148, -2987399281883087146⟩⟩, ⟨⟨-141052180951930541, -141052180947976200⟩, ⟨19356926159598872230, 19356926159602826579⟩⟩, ⟨⟨38181518372969727397, 38181518372974002028⟩, ⟨-21903842481338569647, -21903842481334294993⟩⟩, ⟨⟨-62134386573187886194, -62134386573183368096⟩, ⟨-35907486839828477019, -35907486839823958962⟩⟩, ⟨⟨-142344909223643057, -142344909219073461⟩, ⟨86270677140874448109, 86270677140879017728⟩⟩, ⟨⟨66730190276226043317, 66730190276230349889⟩, ⟨-37635143585872892434, -37635143585868585852⟩⟩, ⟨⟨-39136972850930358700, -39136972850926678080⟩, ⟨-24665462461107559244, -24665462461103878641⟩⟩, ⟨⟨-2638321049367892196, -2638321049365108914⟩, ⟨6667058049281997664, 6667058049284780943⟩⟩, ⟨⟨-26083330973548374861, -26083330973546551023⟩, ⟨18405471513249851817, 18405471513251675666⟩⟩, ⟨⟨53473966589403331522, 53473966589404349379⟩, ⟨27790468897542177015, 27790468897543194861⟩⟩, ⟨⟨-2246813146264141917, -2246813146263665134⟩, ⟨-69952564109343068434, -69952564109342591644⟩⟩, ⟨⟨-50412580295416272376, -50412580295416087137⟩, ⟨31115871049876928445, 31115871049877113679⟩⟩, ⟨⟨32855627215053321396, 32855627215053380635⟩, ⟨17631878754190264144, 17631878754190323385⟩⟩, ⟨⟨-605497926679571154, -605497926679555589⟩, ⟨-17206611017354324690, -17206611017354309122⟩⟩, ⟨⟨-4769527910275834882, -4769527910275831515⟩, ⟨3019442565936261758, 3019442565936265125⟩⟩, ⟨⟨1101978057434071598, 1101978057434072198⟩, ⟨568423028512608234, 568423028512608832⟩⟩, ⟨⟨-8911059029829344, -8911059029829258⟩, ⟨-162911896344143963, -162911896344143877⟩⟩, ⟨⟨-8082707759307049, -8082707759307039⟩, ⟨5364975830628096, 5364975830628106⟩⟩],
  [o],
  [⟨⟨-5, 5⟩, ⟨-5, 5⟩⟩, ⟨⟨-106, 106⟩, ⟨-106, 106⟩⟩, ⟨⟨-819, 819⟩, ⟨-819, 819⟩⟩, ⟨⟨-4189, 4189⟩, ⟨-4189, 4189⟩⟩, ⟨⟨-15710, 15710⟩, ⟨-15710, 15710⟩⟩, ⟨⟨-45856, 45858⟩, ⟨-45861, 45853⟩⟩, ⟨⟨-108915, 108507⟩, ⟨-108981, 108439⟩⟩, ⟨⟨-242117, 190462⟩, ⟨-213505, 219074⟩⟩, ⟨⟨-1039889, -297831⟩, ⟨1105625, 1847679⟩⟩, ⟨⟨46688960, 47811779⟩, ⟨66607328, 67730160⟩⟩, ⟨⟨3376562347, 3378090396⟩, ⟨-273666710, -272138675⟩⟩, ⟨⟨49680999067, 49682902129⟩, ⟨-102389473324, -102387570262⟩⟩, ⟨⟨-1714882088866, -1714879880477⟩, ⟨-2579738419765, -2579736211371⟩⟩, ⟨⟨-67624278439581, -67624276000025⟩, ⟨3679640912006, 3679643351567⟩⟩, ⟨⟨-539234587440000, -539234584811126⟩, ⟨1041135076034079, 1041135078662951⟩⟩, ⟨⟨8372471512090935, 8372471514913899⟩, ⟨13331516774480136, 13331516777303093⟩⟩, ⟨⟨159071665477634137, 159071665480687460⟩, ⟨-4584614191510842, -4584614188457517⟩⟩, ⟨⟨560386284257524022, 560386284260849784⟩, ⟨-1018972641969882072, -1018972641966556296⟩⟩, ⟨⟨-2987399281886715955, -2987399281883084324⟩, ⟨-5017550417219272123, -5017550417215640485⟩⟩, ⟨⟨-19356926159602828157, -19356926159598870544⟩, ⟨141052180947974603, 141052180951932194⟩⟩, ⟨⟨-21903842481338569657, -21903842481334294874⟩, ⟨38181518372969727306, 38181518372974002074⟩⟩, ⟨⟨35907486839823960573, 35907486839828475438⟩, ⟨62134386573183369673, 62134386573187884573⟩⟩, ⟨⟨86270677140874451391, 86270677140879014518⟩, ⟨-142344909223639818, -142344909219076706⟩⟩, ⟨⟨37635143585868590499, 37635143585872887860⟩, ⟨-66730190276230345338, -66730190276226047983⟩⟩, ⟨⟨-24665462461107553908, -24665462461103884057⟩, ⟨-39136972850930353387, -39136972850926683527⟩⟩, ⟨⟨-6667058049284775574, -6667058049282003171⟩, ⟨2638321049365114354, 2638321049367886751⟩⟩, ⟨⟨18405471513249856708, 18405471513251670713⟩, ⟨-26083330973548369910, -26083330973546555904⟩⟩, ⟨⟨-27790468897543190830, -27790468897542181034⟩, ⟨-53473966589404345335, -53473966589403335539⟩⟩, ⟨⟨-69952564109343065476, -69952564109342594625⟩, ⟨-2246813146264138963, -2246813146263668114⟩⟩, ⟨⟨-31115871049877111787, -31115871049876930389⟩, ⟨50412580295416089067, 50412580295416270466⟩⟩, ⟨⟨17631878754190265190, 17631878754190322341⟩, ⟨32855627215053322463, 32855627215053379611⟩⟩, ⟨⟨17206611017354309592, 17206611017354324241⟩, ⟨605497926679556048, 605497926679570697⟩⟩, ⟨⟨3019442565936261915, 3019442565936264972⟩, ⟨-4769527910275834734, -4769527910275831673⟩⟩, ⟨⟨-568423028512608798, -568423028512608273⟩, ⟨-1101978057434072161, -1101978057434071637⟩⟩, ⟨⟨-162911896344143958, -162911896344143885⟩, ⟨-8911059029829338, -8911059029829263⟩⟩, ⟨⟨-5364975830628106, -5364975830628097⟩, ⟨8082707759307040, 8082707759307049⟩⟩],
  [o],
  [⟨⟨103908124649, 103908124660⟩, ⟨-3, 4⟩⟩, ⟨⟨-6172938065478, -6172938065297⟩, ⟨-67, 58⟩⟩, ⟨⟨177208345221437, 177208345222765⟩, ⟨-479, 517⟩⟩, ⟨⟨-3274730617357054, -3274730617350792⟩, ⟨-2518, 2417⟩⟩, ⟨⟨43783553780646686, 43783553780668319⟩, ⟨-8700, 8898⟩⟩, ⟨⟨-451327407605130012, -451327407605070728⟩, ⟨-24831, 24489⟩⟩, ⟨⟨3732478720934250363, 3732478720934387396⟩, ⟨-57582, 58203⟩⟩, ⟨⟨-25444240398896135956, -25444240398895854277⟩, ⟨-120641, 119445⟩⟩, ⟨⟨145788684401849830178, 145788684401850369953⟩, ⟨-229451, 231594⟩⟩, ⟨⟨-712379200001380469755, -712379200001379466643⟩, ⟨-428975, 425656⟩⟩, ⟨⟨3001824454505582203558, 3001824454505584062240⟩, ⟨-786400, 790805⟩⟩, ⟨⟨-11003022756847310972052, -11003022756847307492196⟩, ⟨-1474926, 1469832⟩⟩, ⟨⟨35322718485529636149756, 35322718485529642731598⟩, ⟨-2782928, 2788185⟩⟩, ⟨⟨-99849908716307189606522, -99849908716307177162358⟩, ⟨-5291760, 5286733⟩⟩, ⟨⟨249587533154354498416837, 249587533154354521525432⟩, ⟨-9904513, 9909229⟩⟩, ⟨⟨-553461881985881776350523, -553461881985881735068021⟩, ⟨-17913655, 17909131⟩⟩, ⟨⟨1091403121605528127042164, 1091403121605528196588415⟩, ⟨-30582680, 30586936⟩⟩, ⟨⟨-1917041088031201052504143, -1917041088031200943842057⟩, ⟨-48419720, 48416290⟩⟩, ⟨⟨3002190813453265629352108, 3002190813453265784842924⟩, ⟨-70067409, 70069162⟩⟩, ⟨⟨-4192985077351870737748805, -4192985077351870535838882⟩, ⟨-91763854, 91764310⟩⟩, ⟨⟨5220447181031766787631562, 5220447181031767023928329⟩, ⟨-107971277, 107968897⟩⟩, ⟨⟨-5787655700768143340120192, -5787655700768143092259645⟩, ⟨-113490554, 113493776⟩⟩, ⟨⟨5702733056745046243367207, 5702733056745046475240227⟩, ⟨-106054103, 106051496⟩⟩, ⟨⟨-4980185747275239118739229, -4980185747275238926243572⟩, ⟨-87670143, 87670875⟩⟩, ⟨⟨3840150284890299795021740, 3840150284890299936065529⟩, ⟨-63773017, 63774659⟩⟩, ⟨⟨-2601499953120535714799881, -2601499953120535624160124⟩, ⟨-40570308, 40566864⟩⟩, ⟨⟨1538354348869943414817571, 1538354348869943465522692⟩, ⟨-22397260, 22401164⟩⟩, ⟨⟨-787413089581319779154811, -787413089581319754689248⟩, ⟨-10636391, 10633303⟩⟩, ⟨⟨345085215167939124398680, 345085215167939134463887⟩, ⟨-4290356, 4292111⟩⟩, ⟨⟨-127640343774095837315232, -127640343774095833836313⟩, ⟨-1449811, 1449136⟩⟩, ⟨⟨39082037550095938465507, 39082037550095939456415⟩, ⟨-401730, 401849⟩⟩, ⟨⟨-9641680584339239168414, -9641680584339238941706⟩, ⟨-89015, 89075⟩⟩, ⟨⟨1841753686619929501817, 1841753686619929542103⟩, ⟨-15302, 15227⟩⟩, ⟨⟨-255615600936450399517, -255615600936450394183⟩, ⟨-1929, 1971⟩⟩, ⟨⟨22931427498848255319, 22931427498848255822⟩, ⟨-185, 171⟩⟩, ⟨⟨-998050954316961128, -998050954316961097⟩, ⟨-9, 11⟩⟩],
  [o],
  [⟨⟨-76298736366, -76298736258⟩, ⟨-70537216009, -70537215902⟩⟩, ⟨⟨-1310968073552, -1310968071583⟩, ⟨6032663761604, 6032663763579⟩⟩, ⟨⟨168341992088756, 168341992106168⟩, ⟨-55448772696446, -55448772679041⟩⟩, ⟨⟨-2461628906053772, -2461628905953090⟩, ⟨-2160997568418649, -2160997568317959⟩⟩, ⟨⟨-8199978479557367, -8199978479122678⟩, ⟨43024985320161870, 43024985320596559⟩⟩, ⟨⟨425118273656660443, 425118273658178684⟩, ⟨-152187013707248023, -152187013705729794⟩⟩, ⟨⟨-2868512424161545848, -2868512424156994901⟩, ⟨-2391460673205017704, -2391460673200466740⟩⟩, ⟨⟨-4129615227747698745, -4129615227735447955⟩, ⟨25124698172125537117, 25124698172137787888⟩⟩, ⟨⟨136080246357718484234, 136080246357749061455⟩, ⟨-52640116649750522946, -52640116649719945719⟩⟩, ⟨⟨-559025968170435573852, -559025968170363536250⟩, ⟨-442632234579291568666, -442632234579219531057⟩⟩, ⟨⟨-412703108239991598156, -412703108239830506639⟩, ⟨2976538195378274007185, 2976538195378435098774⟩⟩, ⟨⟨10171533731817917642804, 10171533731818258700854⟩, ⟨-4230269745022803447844, -4230269745022462390165⟩⟩, ⟨⟨-28268005782053985973317, -28268005782053306783697⟩, ⟨-21258323833291299169859, -21258323833290619980361⟩⟩, ⟨⟨-11272426205064786809042, -11272426205063524423148⟩, ⟨99357482020352394864005, 99357482020353657253673⟩⟩, ⟨⟨228375802426734498865800, 228375802426736672249652⟩, ⟨-101662410489227703264456, -101662410489225529891312⟩⟩, ⟨⟨-451141006110157580950028, -451141006110154138205536⟩, ⟨-322232873915669465207222, -322232873915666022458997⟩⟩, ⟨⟨-96669658689465643572282, -96669658689460654711571⟩, ⟨1089099796099429443631156, 1089099796099434432528593⟩⟩, ⟨⟨1735194093183937960936427, 1735194093183944541691051⟩, ⟨-823551075485465842745153, -823551075485459262077139⟩⟩, ⟨⟨-2489490429923456356917471, -2489490429923448487861072⟩, ⟨-1688705917400437647428741, -1688705917400429778313222⟩⟩, ⟨⟨-270607814560585004279741, -270607814560576506857074⟩, ⟨4192955510971914451665650, 4192955510971922949165031⟩⟩, ⟨⟨4671111397150052000627749, 4671111397150060254814940⟩, ⟨-2355767189116929141294247, -2355767189116920887306034⟩⟩, ⟨⟨-4876296155373164217007917, -4876296155373157031002766⟩, ⟨-3140516045727954009696950, -3140516045727946823526523⟩⟩, ⟨⟨-232408760878152419388076, -232408760878146836234749⟩, ⟨5710260466348179601159361, 5710260466348185184302349⟩⟩, ⟨⟨4401629081641618708139426, 4401629081641622558970921⟩, ⟨-2352271905739203458068448, -2352271905739199607339835⟩⟩, ⟨⟨-3283492064540644437045476, -3283492064540642091136059⟩, ⟨-2006559129819418865875185, -2006559129819416519866903⟩⟩, ⟨⟨-44566332103253303672987, -44566332103252050020790⟩, ⟨2606246931638386925188051, 2606246931638388178801041⟩⟩, ⟨⟨1341793192018327422604437, 1341793192018328004851628⟩, ⟨-758218635297406494786918, -758218635297405912540963⟩⟩, ⟨⟨-682527057878564560601525, -682527057878564327600259⟩, ⟨-395334762360385439916306, -395334762360385206905745⟩⟩, ⟨⟨2232196338141645795820, 2232196338141725111015⟩, ⟨345605491720974225811533, 345605491720974305121903⟩⟩, ⟨⟨109759385530906128635550, 109759385530906151172675⟩, ⟨-65485682107684867053505, -65485682107684844515186⟩⟩, ⟨⟨-34310638151027817440885, -34310638151027812190902⟩, ⟨-18804394141653448993517, -18804394141653443743633⟩⟩, ⟨⟨291204794605481817763, 291204794605482797244⟩, ⟨9645901043629515240304, 9645901043629516219755⟩⟩, ⟨⟨1559751474493261529638, 1559751474493261670841⟩, ⟨-981697190910427109542, -981697190910426968325⟩⟩, ⟨⟨-227130520164741235500, -227130520164741220690⟩, ⟨-117505799838312933051, -117505799838312918244⟩⟩, ⟨⟨1243188262460376823, 1243188262460377919⟩, ⟨22902520205611408948, 22902520205611410043⟩⟩, ⟨⟨831570908232194393, 831570908232194462⟩, ⟨-551901741250088924, -551901741250088854⟩⟩],
  [o],
  [⟨⟨-70537216004, -70537215903⟩, ⟨-76298736363, -76298736261⟩⟩, ⟨⟨-6032663763520, -6032663761654⟩, ⟨1310968071622, 1310968073485⟩⟩, ⟨⟨-55448772696052, -55448772679522⟩, ⟨168341992089178, 168341992105710⟩⟩, ⟨⟨2160997568320235, 2160997568416434⟩, ⟨2461628905955432, 2461628906051636⟩⟩, ⟨⟨43024985320170361, 43024985320588871⟩, ⟨-8199978479549632, -8199978479131133⟩⟩, ⟨⟨152187013705750889, 152187013707225061⟩, ⟨-425118273658158244, -425118273656684078⟩⟩, ⟨⟨-2391460673204974852, -2391460673200517888⟩, ⟨-2868512424161498085, -2868512424157041099⟩⟩, ⟨⟨-25124698172137709243, -25124698172125618575⟩, ⟨4129615227735534940, 4129615227747625568⟩⟩, ⟨⟨-52640116649750405924, -52640116649720048343⟩, ⟨136080246357718599061, 136080246357748956734⟩⟩, ⟨⟨442632234579219658361, 442632234579291454522⟩, ⟨559025968170363653056, 559025968170435449105⟩⟩, ⟨⟨2976538195378274109921, 2976538195378434993547⟩, ⟨-412703108239991496750, -412703108239830613808⟩⟩, ⟨⟨4230269745022462456199, 4230269745022803385582⟩, ⟨-10171533731818258632003, -10171533731817917699346⟩⟩, ⟨⟨-21258323833291299145386, -21258323833290619965420⟩, ⟨-28268005782053985959530, -28268005782053306784566⟩⟩, ⟨⟨-99357482020353657281938, -99357482020352394744431⟩, ⟨11272426205063524324010, 11272426205064786855939⟩⟩, ⟨⟨-101662410489227703448964, -101662410489225529681010⟩, ⟨228375802426734498536470, 228375802426736672338136⟩⟩, ⟨⟨322232873915666021830497, 322232873915669465444362⟩, ⟨451141006110154137650153, 451141006110157581212110⟩⟩, ⟨⟨1089099796099429442507682, 1089099796099434432877860⟩, ⟨-96669658689465644150012, -96669658689460653767934⟩⟩, ⟨⟨823551075485459260885152, 823551075485465843924157⟩, ⟨-1735194093183944542223561, -1735194093183937959105548⟩⟩, ⟨⟨-1688705917400437648336754, -1688705917400429775851369⟩, ⟨-2489490429923456358215375, -2489490429923448485863364⟩⟩, ⟨⟨-4192955510971922950454167, -4192955510971914449014236⟩, ⟨270607814560576504113962, 270607814560585005640739⟩⟩, ⟨⟨-2355767189116929143820421, -2355767189116920885772601⟩, ⟨4671111397150051997849149, 4671111397150060255909469⟩⟩, ⟨⟨3140516045727946821174568, 3140516045727954010328010⟩, ⟨4876296155373157029828129, 4876296155373164218911488⟩⟩, ⟨⟨5710260466348179600756217, 5710260466348185185325953⟩, ⟨-232408760878152419233643, -232408760878146834604731⟩⟩, ⟨⟨2352271905739199608455472, 2352271905739203458909477⟩, ⟨-4401629081641622558955270, -4401629081641618708523902⟩⟩, ⟨⟨-2006559129819418864927400, -2006559129819416520642490⟩, ⟨-3283492064540644437203733, -3283492064540642092918915⟩⟩, ⟨⟨-2606246931638388178496535, -2606246931638386926981874⟩, ⟨44566332103252050725070, 44566332103253302244480⟩⟩, ⟨⟨-758218635297406494299058, -758218635297405913943360⟩, ⟨1341793192018327423936924, 1341793192018328004290000⟩⟩, ⟨⟨395334762360385207700984, 395334762360385439301160⟩, ⟨682527057878564328653218, 682527057878564560254138⟩⟩, ⟨⟨345605491720974226411171, 345605491720974304884093⟩, ⟨2232196338141646257699, 2232196338141724730511⟩⟩, ⟨⟨65485682107684844755309, 65485682107684866914740⟩, ⟨-109759385530906151043294, -109759385530906128883861⟩⟩, ⟨⟨-18804394141653448935369, -18804394141653443821241⟩, ⟨-34310638151027817397925, -34310638151027812283792⟩⟩, ⟨⟨-9645901043629516205239, -9645901043629515269311⟩, ⟨-291204794605482776399, -291204794605481840471⟩⟩, ⟨⟨-981697190910427105008, -981697190910426974673⟩, ⟨1559751474493261536309, 1559751474493261666641⟩⟩, ⟨⟨117505799838312919174, 117505799838312932319⟩, ⟨227130520164741221736, 227130520164741234885⟩⟩, ⟨⟨22902520205611409060, 22902520205611409981⟩, ⟨1243188262460376912, 1243188262460377833⟩⟩, ⟨⟨551901741250088861, 551901741250088917⟩, ⟨-831570908232194457, -831570908232194401⟩⟩],
  [o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨12245806159537188, 12245806159537223⟩, ⟨-18, 17⟩⟩, ⟨⟨-86, 85⟩, ⟨-86, 87⟩⟩, ⟨⟨-2026744840230252, -2026744840229726⟩, ⟨-260, 264⟩⟩, ⟨⟨-562, 563⟩, ⟨-562, 565⟩⟩, ⟨⟨7574978482211383, 7574978482213191⟩, ⟨-901, 903⟩⟩, ⟨⟨-1112, 1114⟩, ⟨-1114, 1115⟩⟩, ⟨⟨-1011968010509735843, -1011968010509733709⟩, ⟨-1066, 1067⟩⟩, ⟨⟨-779, 780⟩, ⟨-777, 781⟩⟩, ⟨⟨32863888108908604, 32863888108909450⟩, ⟨-424, 422⟩⟩, ⟨⟨-162, 160⟩, ⟨-164, 163⟩⟩, ⟨⟨-38148209202386509, -38148209202386428⟩, ⟨-40, 40⟩⟩, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, o, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨12117206254809812, 12117206254809846⟩, ⟨-16, 17⟩⟩, ⟨⟨-89, 91⟩, ⟨-91, 89⟩⟩, ⟨⟨-2010971878914075, -2010971878913535⟩, ⟨-269, 269⟩⟩, ⟨⟨-568, 569⟩, ⟨-572, 570⟩⟩, ⟨⟨7543030160369149, 7543030160370975⟩, ⟨-911, 911⟩⟩, ⟨⟨-1132, 1131⟩, ⟨-1131, 1131⟩⟩, ⟨⟨-1011287982978095292, -1011287982978093124⟩, ⟨-1087, 1084⟩⟩, ⟨⟨-790, 789⟩, ⟨-786, 787⟩⟩, ⟨⟨32840644941821201, 32840644941822045⟩, ⟨-423, 423⟩⟩, ⟨⟨-160, 160⟩, ⟨-161, 163⟩⟩, ⟨⟨-38118663392676761, -38118663392676680⟩, ⟨-40, 39⟩⟩, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, o, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨11990081868672636, 11990081868672669⟩, ⟨-17, 17⟩⟩, ⟨⟨-85, 85⟩, ⟨-86, 85⟩⟩, ⟨⟨-1995339836211910, -1995339836211391⟩, ⟨-257, 258⟩⟩, ⟨⟨-558, 557⟩, ⟨-560, 557⟩⟩, ⟨⟨7511259946396998, 7511259946398810⟩, ⟨-907, 908⟩⟩, ⟨⟨-1135, 1134⟩, ⟨-1134, 1130⟩⟩, ⟨⟨-1010609610576867082, -1010609610576864905⟩, ⟨-1088, 1089⟩⟩, ⟨⟨-790, 792⟩, ⟨-792, 788⟩⟩, ⟨⟨32817493604918820, 32817493604919666⟩, ⟨-424, 425⟩⟩, ⟨⟨-161, 162⟩, ⟨-161, 161⟩⟩, ⟨⟨-38089222485699670, -38089222485699588⟩, ⟨-40, 39⟩⟩, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, o, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨11864414825292533, 11864414825292565⟩, ⟨-18, 15⟩⟩, ⟨⟨-81, 82⟩, ⟨-82, 80⟩⟩, ⟨⟨-1979847310327351, -1979847310326869⟩, ⟨-240, 240⟩⟩, ⟨⟨-516, 519⟩, ⟨-519, 520⟩⟩, ⟨⟨7479666583530275, 7479666583531995⟩, ⟨-861, 860⟩⟩, ⟨⟨-1106, 1105⟩, ⟨-1104, 1105⟩⟩, ⟨⟨-1009932877232079140, -1009932877232076966⟩, ⟨-1088, 1087⟩⟩, ⟨⟨-803, 803⟩, ⟨-800, 802⟩⟩, ⟨⟨32794433364924785, 32794433364925652⟩, ⟨-432, 431⟩⟩, ⟨⟨-163, 162⟩, ⟨-165, 165⟩⟩, ⟨⟨-38059885960118545, -38059885960118464⟩, ⟨-40, 40⟩⟩, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, o, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨11740187185572323, 11740187185572359⟩, ⟨-18, 18⟩⟩, ⟨⟨-92, 94⟩, ⟨-92, 91⟩⟩, ⟨⟨-1964492914612175, -1964492914611638⟩, ⟨-271, 268⟩⟩, ⟨⟨-553, 551⟩, ⟨-553, 554⟩⟩, ⟨⟨7448248825866254, 7448248825867986⟩, ⟨-864, 865⟩⟩, ⟨⟨-1064, 1065⟩, ⟨-1067, 1063⟩⟩, ⟨⟨-1009257767069613488, -1009257767069611431⟩, ⟨-1028, 1031⟩⟩, ⟨⟨-761, 764⟩, ⟨-762, 762⟩⟩, ⟨⟨32771463495137220, 32771463495138057⟩, ⟨-417, 418⟩⟩, ⟨⟨-160, 161⟩, ⟨-161, 162⟩⟩, ⟨⟨-38030653297309900, -38030653297309820⟩, ⟨-40, 41⟩⟩, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, o, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨11617381243936000, 11617381243936038⟩, ⟨-19, 19⟩⟩, ⟨⟨-95, 94⟩, ⟨-95, 94⟩⟩, ⟨⟨-1949275277392071, -1949275277391519⟩, ⟨-276, 275⟩⟩, ⟨⟨-572, 570⟩, ⟨-570, 571⟩⟩, ⟨⟨7417005438253204, 7417005438255002⟩, ⟨-900, 901⟩⟩, ⟨⟨-1110, 1110⟩, ⟨-1110, 1110⟩⟩, ⟨⟨-1008584264412585912, -1008584264412583771⟩, ⟨-1070, 1070⟩⟩, ⟨⟨-789, 790⟩, ⟨-787, 790⟩⟩, ⟨⟨32748583275367666, 32748583275368524⟩, ⟨-433, 430⟩⟩, ⟨⟨-164, 164⟩, ⟨-165, 166⟩⟩, ⟨⟨-38001523981350815, -38001523981350733⟩, ⟨-40, 40⟩⟩, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, o]
]

private def m18ELit9 : List (List CFpIv) := [
  [o, ⟨⟨-5325670316499980, -5325670316499936⟩, ⟨-21, 21⟩⟩, ⟨⟨909469663377507, 909469663377633⟩, ⟨-64, 63⟩⟩, ⟨⟨-5022864098155878, -5022864098155760⟩, ⟨-57, 60⟩⟩, ⟨⟨78710061730, 78710061788⟩, ⟨-30, 30⟩⟩, ⟨⟨-39889490, -39889466⟩, ⟨-11, 11⟩⟩, ⟨⟨648223, 648228⟩, ⟨-2, 1⟩⟩, z, z, z, z, z, z, z, z, z, z, z],
  [z, o, ⟨⟨-5327070971811364, -5327070971811319⟩, ⟨-20, 20⟩⟩, ⟨⟨909947470106223, 909947470106344⟩, ⟨-61, 60⟩⟩, ⟨⟨-5026822802009371, -5026822802009254⟩, ⟨-57, 58⟩⟩, ⟨⟨78802360467, 78802360530⟩, ⟨-31, 32⟩⟩, ⟨⟨-39951623, -39951597⟩, ⟨-12, 12⟩⟩, ⟨⟨649483, 649486⟩, ⟨-2, 2⟩⟩, z, z, z, z, z, z, z, z, z, z],
  [z, z, o, ⟨⟨-5328472126504615, -5328472126504570⟩, ⟨-21, 21⟩⟩, ⟨⟨910425572291372, 910425572291493⟩, ⟨-61, 62⟩⟩, ⟨⟨-5030784994088001, -5030784994087887⟩, ⟨-59, 58⟩⟩, ⟨⟨78894779035, 78894779091⟩, ⟨-28, 29⟩⟩, ⟨⟨-40013862, -40013837⟩, ⟨-12, 11⟩⟩, ⟨⟨650744, 650748⟩, ⟨-2, 2⟩⟩, z, z, z, z, z, z, z, z, z],
  [z, z, z, o, ⟨⟨-5329873780792813, -5329873780792767⟩, ⟨-21, 21⟩⟩, ⟨⟨910903970139011, 910903970139133⟩, ⟨-59, 60⟩⟩, ⟨⟨-5034750677755789, -5034750677755672⟩, ⟨-59, 57⟩⟩, ⟨⟨78987317593, 78987317653⟩, ⟨-30, 31⟩⟩, ⟨⟨-40076207, -40076180⟩, ⟨-13, 12⟩⟩, ⟨⟨652008, 652013⟩, ⟨-2, 2⟩⟩, z, z, z, z, z, z, z, z],
  [z, z, z, z, o, ⟨⟨-5331275934889141, -5331275934889095⟩, ⟨-21, 21⟩⟩, ⟨⟨911382663855353, 911382663855484⟩, ⟨-66, 68⟩⟩, ⟨⟨-5038719856380235, -5038719856380106⟩, ⟨-64, 64⟩⟩, ⟨⟨79079976314, 79079976378⟩, ⟨-32, 32⟩⟩, ⟨⟨-40138656, -40138631⟩, ⟨-13, 12⟩⟩, ⟨⟨653275, 653279⟩, ⟨-2, 2⟩⟩, z, z, z, z, z, z, z],
  [z, z, z, z, z, o, ⟨⟨-5332678589006877, -5332678589006832⟩, ⟨-21, 19⟩⟩, ⟨⟨911861653646783, 911861653646907⟩, ⟨-62, 61⟩⟩, ⟨⟨-5042692533332320, -5042692533332201⟩, ⟨-61, 61⟩⟩, ⟨⟨79172755378, 79172755437⟩, ⟨-31, 31⟩⟩, ⟨⟨-40201212, -40201189⟩, ⟨-11, 11⟩⟩, ⟨⟨654544, 654548⟩, ⟨-3, 2⟩⟩, z, z, z, z, z, z],
  [z, z, z, z, z, z, o, ⟨⟨-5334081743359409, -5334081743359364⟩, ⟨-20, 20⟩⟩, ⟨⟨912340939719819, 912340939719946⟩, ⟨-61, 64⟩⟩, ⟨⟨-5046668711986554, -5046668711986433⟩, ⟨-62, 63⟩⟩, ⟨⟨79265654945, 79265655006⟩, ⟨-32, 31⟩⟩, ⟨⟨-40263876, -40263852⟩, ⟨-12, 13⟩⟩, ⟨⟨655816, 655821⟩, ⟨-2, 2⟩⟩, z, z, z, z, z],
  [z, z, z, z, z, z, z, o, ⟨⟨-5335485398160216, -5335485398160172⟩, ⟨-21, 21⟩⟩, ⟨⟨912820522281160, 912820522281283⟩, ⟨-59, 62⟩⟩, ⟨⟨-5050648395720927, -5050648395720804⟩, ⟨-61, 60⟩⟩, ⟨⟨79358675188, 79358675256⟩, ⟨-34, 34⟩⟩, ⟨⟨-40326646, -40326621⟩, ⟨-13, 12⟩⟩, ⟨⟨657091, 657096⟩, ⟨-3, 2⟩⟩, z, z, z, z],
  [z, z, z, z, z, z, z, z, o, ⟨⟨-5336889553622881, -5336889553622837⟩, ⟨-21, 19⟩⟩, ⟨⟨913300401537640, 913300401537760⟩, ⟨-62, 60⟩⟩, ⟨⟨-5054631587916935, -5054631587916812⟩, ⟨-60, 62⟩⟩, ⟨⟨79451816291, 79451816351⟩, ⟨-32, 32⟩⟩, ⟨⟨-40389520, -40389497⟩, ⟨-12, 11⟩⟩, ⟨⟨658369, 658373⟩, ⟨-2, 2⟩⟩, z, z, z],
  [⟨⟨0, 1⟩, ⟨0, 0⟩⟩, ⟨⟨-45, 93⟩, ⟨-51, 52⟩⟩, ⟨⟨-1162, 1443⟩, ⟨-1272, 1274⟩⟩, ⟨⟨-8522, 9910⟩, ⟨-9196, 9179⟩⟩, ⟨⟨1589797, 1652838⟩, ⟨-31484, 31458⟩⟩, ⟨⟨3387647313, 3387782329⟩, ⟨-67466, 67407⟩⟩, ⟨⟨3096811992599, 3096812215369⟩, ⟨-111320, 111272⟩⟩, ⟨⟨1171906953355533, 1171906953669786⟩, ⟨-157052, 157035⟩⟩, ⟨⟨158983315037456072, 158983315037862256⟩, ⟨-202961, 202992⟩⟩, ⟨⟨5825257231917803437, 5825257231918300856⟩, ⟨-248552, 248615⟩⟩, ⟨⟨43662969459633204363, 43662969459633789136⟩, ⟨-292323, 292370⟩⟩, ⟨⟨84381966212616855311, 84381966212617523055⟩, ⟨-333711, 333725⟩⟩, ⟨⟨44345016928424718044, 44345016928425340390⟩, ⟨-311022, 311000⟩⟩, ⟨⟨-30469575728028060868, -30469575728027690551⟩, ⟨-185134, 185098⟩⟩, ⟨⟨-68271183270232116807, -68271183270231996143⟩, ⟨-60208, 60189⟩⟩, ⟨⟨-36919653018860942876, -36919653018860923540⟩, ⟨-9550, 9569⟩⟩, ⟨⟨-5628422832221595061, -5628422832221593761⟩, ⟨-621, 631⟩⟩, ⟨⟨-163086812048925410, -163086812048925383⟩, ⟨-12, 13⟩⟩],
  [⟨⟨-5, 5⟩, ⟨-5, 5⟩⟩, ⟨⟨-823, 823⟩, ⟨-823, 823⟩⟩, ⟨⟨-15961, 15961⟩, ⟨-15961, 15961⟩⟩, ⟨⟨-111262, 110720⟩, ⟨-111195, 110788⟩⟩, ⟨⟨1099340, 1853965⟩, ⟨-1046170, -291549⟩⟩, ⟨⟨-273673890, -272131527⟩, ⟨3376555214, 3378097565⟩⟩, ⟨⟨-2579738424868, -2579736206297⟩, ⟨-1714882093995, -1714879875414⟩⟩, ⟨⟨1041135076032103, 1041135078664970⟩, ⟨-539234587441997, -539234584809126⟩⟩, ⟨⟨-4584614191508741, -4584614188459606⟩, ⟨159071665477636259, 159071665480685384⟩⟩, ⟨⟨-5017550417219269350, -5017550417215643345⟩, ⟨-2987399281886713148, -2987399281883087146⟩⟩, ⟨⟨38181518372969727397, 38181518372974002028⟩, ⟨-21903842481338569647, -21903842481334294993⟩⟩, ⟨⟨-142344909223643057, -142344909219073461⟩, ⟨86270677140874448109, 86270677140879017728⟩⟩, ⟨⟨-39136972850930358700, -39136972850926678080⟩, ⟨-24665462461107559244, -24665462461103878641⟩⟩, ⟨⟨-26083330973548374861, -26083330973546551023⟩, ⟨18405471513249851817, 18405471513251675666⟩⟩, ⟨⟨-2246813146264141917, -2246813146263665134⟩, ⟨-69952564109343068434, -69952564109342591644⟩⟩, ⟨⟨32855627215053321396, 32855627215053380635⟩, ⟨17631878754190264144, 17631878754190323385⟩⟩, ⟨⟨-4769527910275834882, -4769527910275831515⟩, ⟨3019442565936261758, 3019442565936265125⟩⟩, ⟨⟨-8911059029829344, -8911059029829258⟩, ⟨-162911896344143963, -162911896344143877⟩⟩],
  [⟨⟨-5, 5⟩, ⟨-5, 5⟩⟩, ⟨⟨-819, 819⟩, ⟨-819, 819⟩⟩, ⟨⟨-15710, 15710⟩, ⟨-15710, 15710⟩⟩, ⟨⟨-108915, 108507⟩, ⟨-108981, 108439⟩⟩, ⟨⟨-1039889, -297831⟩, ⟨1105625, 1847679⟩⟩, ⟨⟨3376562347, 3378090396⟩, ⟨-273666710, -272138675⟩⟩, ⟨⟨-1714882088866, -1714879880477⟩, ⟨-2579738419765, -2579736211371⟩⟩, ⟨⟨-539234587440000, -539234584811126⟩, ⟨1041135076034079, 1041135078662951⟩⟩, ⟨⟨159071665477634137, 159071665480687460⟩, ⟨-4584614191510842, -4584614188457517⟩⟩, ⟨⟨-2987399281886715955, -2987399281883084324⟩, ⟨-5017550417219272123, -5017550417215640485⟩⟩, ⟨⟨-21903842481338569657, -21903842481334294874⟩, ⟨38181518372969727306, 38181518372974002074⟩⟩, ⟨⟨86270677140874451391, 86270677140879014518⟩, ⟨-142344909223639818, -142344909219076706⟩⟩, ⟨⟨-24665462461107553908, -24665462461103884057⟩, ⟨-39136972850930353387, -39136972850926683527⟩⟩, ⟨⟨18405471513249856708, 18405471513251670713⟩, ⟨-26083330973548369910, -26083330973546555904⟩⟩, ⟨⟨-69952564109343065476, -69952564109342594625⟩, ⟨-2246813146264138963, -2246813146263668114⟩⟩, ⟨⟨17631878754190265190, 17631878754190322341⟩, ⟨32855627215053322463, 32855627215053379611⟩⟩, ⟨⟨3019442565936261915, 3019442565936264972⟩, ⟨-4769527910275834734, -4769527910275831673⟩⟩, ⟨⟨-162911896344143958, -162911896344143885⟩, ⟨-8911059029829338, -8911059029829263⟩⟩],
  [⟨⟨103908124649, 103908124660⟩, ⟨-3, 4⟩⟩, ⟨⟨177208345221437, 177208345222765⟩, ⟨-479, 517⟩⟩, ⟨⟨43783553780646686, 43783553780668319⟩, ⟨-8700, 8898⟩⟩, ⟨⟨3732478720934250363, 3732478720934387396⟩, ⟨-57582, 58203⟩⟩, ⟨⟨145788684401849830178, 145788684401850369953⟩, ⟨-229451, 231594⟩⟩, ⟨⟨3001824454505582203558, 3001824454505584062240⟩, ⟨-786400, 790805⟩⟩, ⟨⟨35322718485529636149756, 35322718485529642731598⟩, ⟨-2782928, 2788185⟩⟩, ⟨⟨249587533154354498416837, 249587533154354521525432⟩, ⟨-9904513, 9909229⟩⟩, ⟨⟨1091403121605528127042164, 1091403121605528196588415⟩, ⟨-30582680, 30586936⟩⟩, ⟨⟨3002190813453265629352108, 3002190813453265784842924⟩, ⟨-70067409, 70069162⟩⟩, ⟨⟨5220447181031766787631562, 5220447181031767023928329⟩, ⟨-107971277, 107968897⟩⟩, ⟨⟨5702733056745046243367207, 5702733056745046475240227⟩, ⟨-106054103, 106051496⟩⟩, ⟨⟨3840150284890299795021740, 3840150284890299936065529⟩, ⟨-63773017, 63774659⟩⟩, ⟨⟨1538354348869943414817571, 1538354348869943465522692⟩, ⟨-22397260, 22401164⟩⟩, ⟨⟨345085215167939124398680, 345085215167939134463887⟩, ⟨-4290356, 4292111⟩⟩, ⟨⟨39082037550095938465507, 39082037550095939456415⟩, ⟨-401730, 401849⟩⟩, ⟨⟨1841753686619929501817, 1841753686619929542103⟩, ⟨-15302, 15227⟩⟩, ⟨⟨22931427498848255319, 22931427498848255822⟩, ⟨-185, 171⟩⟩],
  [⟨⟨-76298736366, -76298736258⟩, ⟨-70537216009, -70537215902⟩⟩, ⟨⟨168341992088756, 168341992106168⟩, ⟨-55448772696446, -55448772679041⟩⟩, ⟨⟨-8199978479557367, -8199978479122678⟩, ⟨43024985320161870, 43024985320596559⟩⟩, ⟨⟨-2868512424161545848, -2868512424156994901⟩, ⟨-2391460673205017704, -2391460673200466740⟩⟩, ⟨⟨136080246357718484234, 136080246357749061455⟩, ⟨-52640116649750522946, -52640116649719945719⟩⟩, ⟨⟨-412703108239991598156, -412703108239830506639⟩, ⟨2976538195378274007185, 2976538195378435098774⟩⟩, ⟨⟨-28268005782053985973317, -28268005782053306783697⟩, ⟨-21258323833291299169859, -21258323833290619980361⟩⟩, ⟨⟨228375802426734498865800, 228375802426736672249652⟩, ⟨-101662410489227703264456, -101662410489225529891312⟩⟩, ⟨⟨-96669658689465643572282, -96669658689460654711571⟩, ⟨1089099796099429443631156, 1089099796099434432528593⟩⟩, ⟨⟨-2489490429923456356917471, -2489490429923448487861072⟩, ⟨-1688705917400437647428741, -1688705917400429778313222⟩⟩, ⟨⟨4671111397150052000627749, 4671111397150060254814940⟩, ⟨-2355767189116929141294247, -2355767189116920887306034⟩⟩, ⟨⟨-232408760878152419388076, -232408760878146836234749⟩, ⟨5710260466348179601159361, 5710260466348185184302349⟩⟩, ⟨⟨-3283492064540644437045476, -3283492064540642091136059⟩, ⟨-2006559129819418865875185, -2006559129819416519866903⟩⟩, ⟨⟨1341793192018327422604437, 1341793192018328004851628⟩, ⟨-758218635297406494786918, -758218635297405912540963⟩⟩, ⟨⟨2232196338141645795820, 2232196338141725111015⟩, ⟨345605491720974225811533, 345605491720974305121903⟩⟩, ⟨⟨-34310638151027817440885, -34310638151027812190902⟩, ⟨-18804394141653448993517, -18804394141653443743633⟩⟩, ⟨⟨1559751474493261529638, 1559751474493261670841⟩, ⟨-981697190910427109542, -981697190910426968325⟩⟩, ⟨⟨1243188262460376823, 1243188262460377919⟩, ⟨22902520205611408948, 22902520205611410043⟩⟩],
  [⟨⟨-70537216004, -70537215903⟩, ⟨-76298736363, -76298736261⟩⟩, ⟨⟨-55448772696052, -55448772679522⟩, ⟨168341992089178, 168341992105710⟩⟩, ⟨⟨43024985320170361, 43024985320588871⟩, ⟨-8199978479549632, -8199978479131133⟩⟩, ⟨⟨-2391460673204974852, -2391460673200517888⟩, ⟨-2868512424161498085, -2868512424157041099⟩⟩, ⟨⟨-52640116649750405924, -52640116649720048343⟩, ⟨136080246357718599061, 136080246357748956734⟩⟩, ⟨⟨2976538195378274109921, 2976538195378434993547⟩, ⟨-412703108239991496750, -412703108239830613808⟩⟩, ⟨⟨-21258323833291299145386, -21258323833290619965420⟩, ⟨-28268005782053985959530, -28268005782053306784566⟩⟩, ⟨⟨-101662410489227703448964, -101662410489225529681010⟩, ⟨228375802426734498536470, 228375802426736672338136⟩⟩, ⟨⟨1089099796099429442507682, 1089099796099434432877860⟩, ⟨-96669658689465644150012, -96669658689460653767934⟩⟩, ⟨⟨-1688705917400437648336754, -1688705917400429775851369⟩, ⟨-2489490429923456358215375, -2489490429923448485863364⟩⟩, ⟨⟨-2355767189116929143820421, -2355767189116920885772601⟩, ⟨4671111397150051997849149, 4671111397150060255909469⟩⟩, ⟨⟨5710260466348179600756217, 5710260466348185185325953⟩, ⟨-232408760878152419233643, -232408760878146834604731⟩⟩, ⟨⟨-2006559129819418864927400, -2006559129819416520642490⟩, ⟨-3283492064540644437203733, -3283492064540642092918915⟩⟩, ⟨⟨-758218635297406494299058, -758218635297405913943360⟩, ⟨1341793192018327423936924, 1341793192018328004290000⟩⟩, ⟨⟨345605491720974226411171, 345605491720974304884093⟩, ⟨2232196338141646257699, 2232196338141724730511⟩⟩, ⟨⟨-18804394141653448935369, -18804394141653443821241⟩, ⟨-34310638151027817397925, -34310638151027812283792⟩⟩, ⟨⟨-981697190910427105008, -981697190910426974673⟩, ⟨1559751474493261536309, 1559751474493261666641⟩⟩, ⟨⟨22902520205611409060, 22902520205611409981⟩, ⟨1243188262460376912, 1243188262460377833⟩⟩],
  [z, z, z, z, z, z, z, z, z, ⟨⟨12245806159537188, 12245806159537223⟩, ⟨-18, 17⟩⟩, ⟨⟨-2026744840230252, -2026744840229726⟩, ⟨-260, 264⟩⟩, ⟨⟨7574978482211383, 7574978482213191⟩, ⟨-901, 903⟩⟩, ⟨⟨-1011968010509735843, -1011968010509733709⟩, ⟨-1066, 1067⟩⟩, ⟨⟨32863888108908604, 32863888108909450⟩, ⟨-424, 422⟩⟩, ⟨⟨-38148209202386509, -38148209202386428⟩, ⟨-40, 40⟩⟩, o, z, z],
  [z, z, z, z, z, z, z, z, z, z, ⟨⟨11990081868672636, 11990081868672669⟩, ⟨-17, 17⟩⟩, ⟨⟨-1995339836211910, -1995339836211391⟩, ⟨-257, 258⟩⟩, ⟨⟨7511259946396998, 7511259946398810⟩, ⟨-907, 908⟩⟩, ⟨⟨-1010609610576867082, -1010609610576864905⟩, ⟨-1088, 1089⟩⟩, ⟨⟨32817493604918820, 32817493604919666⟩, ⟨-424, 425⟩⟩, ⟨⟨-38089222485699670, -38089222485699588⟩, ⟨-40, 39⟩⟩, o, z],
  [z, z, z, z, z, z, z, z, z, z, z, ⟨⟨11740187185572323, 11740187185572359⟩, ⟨-18, 18⟩⟩, ⟨⟨-1964492914612175, -1964492914611638⟩, ⟨-271, 268⟩⟩, ⟨⟨7448248825866254, 7448248825867986⟩, ⟨-864, 865⟩⟩, ⟨⟨-1009257767069613488, -1009257767069611431⟩, ⟨-1028, 1031⟩⟩, ⟨⟨32771463495137220, 32771463495138057⟩, ⟨-417, 418⟩⟩, ⟨⟨-38030653297309900, -38030653297309820⟩, ⟨-40, 41⟩⟩, o]
]

private def m18OLit9 : List (List CFpIv) := [
  [o, ⟨⟨-5326370581746254, -5326370581746210⟩, ⟨-19, 21⟩⟩, ⟨⟨909708529822681, 909708529822806⟩, ⟨-64, 63⟩⟩, ⟨⟨-5024843014264599, -5024843014264477⟩, ⟨-60, 61⟩⟩, ⟨⟨78756196130, 78756196191⟩, ⟨-29, 31⟩⟩, ⟨⟨-39920543, -39920519⟩, ⟨-13, 12⟩⟩, ⟨⟨648852, 648857⟩, ⟨-2, 2⟩⟩, z, z, z, z, z, z, z, z, z, z, z],
  [z, o, ⟨⟨-5327771486721941, -5327771486721894⟩, ⟨-21, 21⟩⟩, ⟨⟨910186484253866, 910186484253991⟩, ⟨-63, 63⟩⟩, ⟨⟨-5028803461810378, -5028803461810254⟩, ⟨-63, 63⟩⟩, ⟨⟨78848554760, 78848554825⟩, ⟨-31, 30⟩⟩, ⟨⟨-39982730, -39982704⟩, ⟨-13, 13⟩⟩, ⟨⟨650112, 650117⟩, ⟨-2, 2⟩⟩, z, z, z, z, z, z, z, z, z, z],
  [z, z, o, ⟨⟨-5329172891186024, -5329172891185980⟩, ⟨-21, 19⟩⟩, ⟨⟨910664734244496, 910664734244616⟩, ⟨-59, 62⟩⟩, ⟨⟨-5032767399262864, -5032767399262749⟩, ⟨-59, 57⟩⟩, ⟨⟨78941033301, 78941033365⟩, ⟨-29, 29⟩⟩, ⟨⟨-40045022, -40044995⟩, ⟨-11, 12⟩⟩, ⟨⟨651376, 651379⟩, ⟨-2, 2⟩⟩, z, z, z, z, z, z, z, z, z],
  [z, z, z, o, ⟨⟨-5330574795351633, -5330574795351587⟩, ⟨-19, 21⟩⟩, ⟨⟨911143280000694, 911143280000829⟩, ⟨-66, 65⟩⟩, ⟨⟨-5036734829987826, -5036734829987702⟩, ⟨-62, 62⟩⟩, ⟨⟨79033631923, 79033631983⟩, ⟨-31, 31⟩⟩, ⟨⟨-40107417, -40107394⟩, ⟨-11, 12⟩⟩, ⟨⟨652641, 652645⟩, ⟨-2, 2⟩⟩, z, z, z, z, z, z, z, z],
  [z, z, z, z, o, ⟨⟨-5331977199432000, -5331977199431954⟩, ⟨-21, 21⟩⟩, ⟨⟨911622121728782, 911622121728909⟩, ⟨-62, 65⟩⟩, ⟨⟨-5040705757354495, -5040705757354376⟩, ⟨-59, 59⟩⟩, ⟨⟨79126350797, 79126350851⟩, ⟨-28, 29⟩⟩, ⟨⟨-40169921, -40169896⟩, ⟨-11, 13⟩⟩, ⟨⟨653909, 653914⟩, ⟨-3, 2⟩⟩, z, z, z, z, z, z, z],
  [z, z, z, z, z, o, ⟨⟨-5333380103640452, -5333380103640407⟩, ⟨-21, 21⟩⟩, ⟨⟨912101259635187, 912101259635314⟩, ⟨-65, 64⟩⟩, ⟨⟨-5044680184735630, -5044680184735506⟩, ⟨-61, 62⟩⟩, ⟨⟨79219190087, 79219190149⟩, ⟨-32, 31⟩⟩, ⟨⟨-40232531, -40232507⟩, ⟨-11, 12⟩⟩, ⟨⟨655180, 655184⟩, ⟨-3, 2⟩⟩, z, z, z, z, z, z],
  [z, z, z, z, z, z, o, ⟨⟨-5334783508190433, -5334783508190388⟩, ⟨-21, 21⟩⟩, ⟨⟨912580693926529, 912580693926651⟩, ⟨-61, 59⟩⟩, ⟨⟨-5048658115507459, -5048658115507343⟩, ⟨-57, 59⟩⟩, ⟨⟨79312149976, 79312150033⟩, ⟨-28, 28⟩⟩, ⟨⟨-40295245, -40295223⟩, ⟨-11, 11⟩⟩, ⟨⟨656454, 656457⟩, ⟨-2, 2⟩⟩, z, z, z, z, z],
  [z, z, z, z, z, z, z, o, ⟨⟨-5336187413295465, -5336187413295420⟩, ⟨-20, 20⟩⟩, ⟨⟨913060424809572, 913060424809694⟩, ⟨-62, 61⟩⟩, ⟨⟨-5052639553049744, -5052639553049622⟩, ⟨-57, 58⟩⟩, ⟨⟨79405230622, 79405230687⟩, ⟨-35, 32⟩⟩, ⟨⟨-40358070, -40358044⟩, ⟨-13, 13⟩⟩, ⟨⟨657729, 657734⟩, ⟨-2, 3⟩⟩, z, z, z, z],
  [z, z, z, z, z, z, z, z, o, ⟨⟨-5337591819169186, -5337591819169141⟩, ⟨-20, 20⟩⟩, ⟨⟨913540452491240, 913540452491363⟩, ⟨-62, 61⟩⟩, ⟨⟨-5056624500745730, -5056624500745613⟩, ⟨-61, 61⟩⟩, ⟨⟨79498432212, 79498432275⟩, ⟨-32, 31⟩⟩, ⟨⟨-40421002, -40420975⟩, ⟨-13, 14⟩⟩, ⟨⟨659008, 659013⟩, ⟨-2, 2⟩⟩, z, z, z],
  [⟨⟨-16, 3⟩, ⟨-4, 4⟩⟩, ⟨⟨-410, 278⟩, ⟨-318, 315⟩⟩, ⟨⟨-4106, 3608⟩, ⟨-3826, 3834⟩⟩, ⟨⟨-44765, -8044⟩, ⟨-18313, 18332⟩⟩, ⟨⟨-82159850, -82063510⟩, ⟨-48087, 48133⟩⟩, ⟨⟨-113779441694, -113779264051⟩, ⟨-88711, 88768⟩⟩, ⟨⟨-67698735574721, -67698735306035⟩, ⟨-134238, 134273⟩⟩, ⟨⟨-15731841945309506, -15731841944949695⟩, ⟨-179816, 179811⟩⟩, ⟨⟨-1161183106652610832, -1161183106652158156⟩, ⟨-226231, 226177⟩⟩, ⟨⟨-19271732697803117504, -19271732697802577045⟩, ⟨-270178, 270119⟩⟩, ⟨⟨-70770708993229113456, -70770708993228482676⟩, ⟨-315338, 315306⟩⟩, ⟨⟨-74185691489989527793, -74185691489988855264⟩, ⟨-336059, 336064⟩⟩, ⟨⟨-6357118531846299811, -6357118531845786032⟩, ⟨-256795, 256827⟩⟩, ⟨⟨58182798544798141846, 58182798544798371299⟩, ⟨-114623, 114656⟩⟩, ⟨⟨58287647932989444844, 58287647932989498022⟩, ⟨-26448, 26446⟩⟩, ⟨⟨17120320538594357729, 17120320538594363403⟩, ⟨-2786, 2767⟩⟩, ⟨⟨1238319815929758896, 1238319815929759118⟩, ⟨-106, 103⟩⟩, ⟨⟨9701148354483062, 9701148354483065⟩, ⟨-1, 1⟩⟩],
  [⟨⟨-106, 106⟩, ⟨-106, 106⟩⟩, ⟨⟨-4234, 4234⟩, ⟨-4234, 4234⟩⟩, ⟨⟨-46751, 46759⟩, ⟨-46756, 46754⟩⟩, ⟨⟨-223383, 217818⟩, ⟨-194776, 246428⟩⟩, ⟨⟨-67737479, -66600011⟩, ⟨-47819116, -46681643⟩⟩, ⟨⟨102387564062, 102389479599⟩, ⟨-49682908371, -49680992816⟩⟩, ⟨⟨-3679643355344, -3679640908259⟩, ⟨67624275996296, 67624278443353⟩⟩, ⟨⟨-13331516777302960, -13331516774480302⟩, ⟨-8372471514913771, -8372471512091091⟩⟩, ⟨⟨1018972641966559403, 1018972641969879001⟩, ⟨-560386284260846721, -560386284257527133⟩⟩, ⟨⟨-141052180951930541, -141052180947976200⟩, ⟨19356926159598872230, 19356926159602826579⟩⟩, ⟨⟨-62134386573187886194, -62134386573183368096⟩, ⟨-35907486839828477019, -35907486839823958962⟩⟩, ⟨⟨66730190276226043317, 66730190276230349889⟩, ⟨-37635143585872892434, -37635143585868585852⟩⟩, ⟨⟨-2638321049367892196, -2638321049365108914⟩, ⟨6667058049281997664, 6667058049284780943⟩⟩, ⟨⟨53473966589403331522, 53473966589404349379⟩, ⟨27790468897542177015, 27790468897543194861⟩⟩, ⟨⟨-50412580295416272376, -50412580295416087137⟩, ⟨31115871049876928445, 31115871049877113679⟩⟩, ⟨⟨-605497926679571154, -605497926679555589⟩, ⟨-17206611017354324690, -17206611017354309122⟩⟩, ⟨⟨1101978057434071598, 1101978057434072198⟩, ⟨568423028512608234, 568423028512608832⟩⟩, ⟨⟨-8082707759307049, -8082707759307039⟩, ⟨5364975830628096, 5364975830628106⟩⟩],
  [⟨⟨-106, 106⟩, ⟨-106, 106⟩⟩, ⟨⟨-4189, 4189⟩, ⟨-4189, 4189⟩⟩, ⟨⟨-45856, 45858⟩, ⟨-45861, 45853⟩⟩, ⟨⟨-242117, 190462⟩, ⟨-213505, 219074⟩⟩, ⟨⟨46688960, 47811779⟩, ⟨66607328, 67730160⟩⟩, ⟨⟨49680999067, 49682902129⟩, ⟨-102389473324, -102387570262⟩⟩, ⟨⟨-67624278439581, -67624276000025⟩, ⟨3679640912006, 3679643351567⟩⟩, ⟨⟨8372471512090935, 8372471514913899⟩, ⟨13331516774480136, 13331516777303093⟩⟩, ⟨⟨560386284257524022, 560386284260849784⟩, ⟨-1018972641969882072, -1018972641966556296⟩⟩, ⟨⟨-19356926159602828157, -19356926159598870544⟩, ⟨141052180947974603, 141052180951932194⟩⟩, ⟨⟨35907486839823960573, 35907486839828475438⟩, ⟨62134386573183369673, 62134386573187884573⟩⟩, ⟨⟨37635143585868590499, 37635143585872887860⟩, ⟨-66730190276230345338, -66730190276226047983⟩⟩, ⟨⟨-6667058049284775574, -6667058049282003171⟩, ⟨2638321049365114354, 2638321049367886751⟩⟩, ⟨⟨-27790468897543190830, -27790468897542181034⟩, ⟨-53473966589404345335, -53473966589403335539⟩⟩, ⟨⟨-31115871049877111787, -31115871049876930389⟩, ⟨50412580295416089067, 50412580295416270466⟩⟩, ⟨⟨17206611017354309592, 17206611017354324241⟩, ⟨605497926679556048, 605497926679570697⟩⟩, ⟨⟨-568423028512608798, -568423028512608273⟩, ⟨-1101978057434072161, -1101978057434071637⟩⟩, ⟨⟨-5364975830628106, -5364975830628097⟩, ⟨8082707759307040, 8082707759307049⟩⟩],
  [⟨⟨-6172938065478, -6172938065297⟩, ⟨-67, 58⟩⟩, ⟨⟨-3274730617357054, -3274730617350792⟩, ⟨-2518, 2417⟩⟩, ⟨⟨-451327407605130012, -451327407605070728⟩, ⟨-24831, 24489⟩⟩, ⟨⟨-25444240398896135956, -25444240398895854277⟩, ⟨-120641, 119445⟩⟩, ⟨⟨-712379200001380469755, -712379200001379466643⟩, ⟨-428975, 425656⟩⟩, ⟨⟨-11003022756847310972052, -11003022756847307492196⟩, ⟨-1474926, 1469832⟩⟩, ⟨⟨-99849908716307189606522, -99849908716307177162358⟩, ⟨-5291760, 5286733⟩⟩, ⟨⟨-553461881985881776350523, -553461881985881735068021⟩, ⟨-17913655, 17909131⟩⟩, ⟨⟨-1917041088031201052504143, -1917041088031200943842057⟩, ⟨-48419720, 48416290⟩⟩, ⟨⟨-4192985077351870737748805, -4192985077351870535838882⟩, ⟨-91763854, 91764310⟩⟩, ⟨⟨-5787655700768143340120192, -5787655700768143092259645⟩, ⟨-113490554, 113493776⟩⟩, ⟨⟨-4980185747275239118739229, -4980185747275238926243572⟩, ⟨-87670143, 87670875⟩⟩, ⟨⟨-2601499953120535714799881, -2601499953120535624160124⟩, ⟨-40570308, 40566864⟩⟩, ⟨⟨-787413089581319779154811, -787413089581319754689248⟩, ⟨-10636391, 10633303⟩⟩, ⟨⟨-127640343774095837315232, -127640343774095833836313⟩, ⟨-1449811, 1449136⟩⟩, ⟨⟨-9641680584339239168414, -9641680584339238941706⟩, ⟨-89015, 89075⟩⟩, ⟨⟨-255615600936450399517, -255615600936450394183⟩, ⟨-1929, 1971⟩⟩, ⟨⟨-998050954316961128, -998050954316961097⟩, ⟨-9, 11⟩⟩],
  [⟨⟨-1310968073552, -1310968071583⟩, ⟨6032663761604, 6032663763579⟩⟩, ⟨⟨-2461628906053772, -2461628905953090⟩, ⟨-2160997568418649, -2160997568317959⟩⟩, ⟨⟨425118273656660443, 425118273658178684⟩, ⟨-152187013707248023, -152187013705729794⟩⟩, ⟨⟨-4129615227747698745, -4129615227735447955⟩, ⟨25124698172125537117, 25124698172137787888⟩⟩, ⟨⟨-559025968170435573852, -559025968170363536250⟩, ⟨-442632234579291568666, -442632234579219531057⟩⟩, ⟨⟨10171533731817917642804, 10171533731818258700854⟩, ⟨-4230269745022803447844, -4230269745022462390165⟩⟩, ⟨⟨-11272426205064786809042, -11272426205063524423148⟩, ⟨99357482020352394864005, 99357482020353657253673⟩⟩, ⟨⟨-451141006110157580950028, -451141006110154138205536⟩, ⟨-322232873915669465207222, -322232873915666022458997⟩⟩, ⟨⟨1735194093183937960936427, 1735194093183944541691051⟩, ⟨-823551075485465842745153, -823551075485459262077139⟩⟩, ⟨⟨-270607814560585004279741, -270607814560576506857074⟩, ⟨4192955510971914451665650, 4192955510971922949165031⟩⟩, ⟨⟨-4876296155373164217007917, -4876296155373157031002766⟩, ⟨-3140516045727954009696950, -3140516045727946823526523⟩⟩, ⟨⟨4401629081641618708139426, 4401629081641622558970921⟩, ⟨-2352271905739203458068448, -2352271905739199607339835⟩⟩, ⟨⟨-44566332103253303672987, -44566332103252050020790⟩, ⟨2606246931638386925188051, 2606246931638388178801041⟩⟩, ⟨⟨-682527057878564560601525, -682527057878564327600259⟩, ⟨-395334762360385439916306, -395334762360385206905745⟩⟩, ⟨⟨109759385530906128635550, 109759385530906151172675⟩, ⟨-65485682107684867053505, -65485682107684844515186⟩⟩, ⟨⟨291204794605481817763, 291204794605482797244⟩, ⟨9645901043629515240304, 9645901043629516219755⟩⟩, ⟨⟨-227130520164741235500, -227130520164741220690⟩, ⟨-117505799838312933051, -117505799838312918244⟩⟩, ⟨⟨831570908232194393, 831570908232194462⟩, ⟨-551901741250088924, -551901741250088854⟩⟩],
  [⟨⟨-6032663763520, -6032663761654⟩, ⟨1310968071622, 1310968073485⟩⟩, ⟨⟨2160997568320235, 2160997568416434⟩, ⟨2461628905955432, 2461628906051636⟩⟩, ⟨⟨152187013705750889, 152187013707225061⟩, ⟨-425118273658158244, -425118273656684078⟩⟩, ⟨⟨-25124698172137709243, -25124698172125618575⟩, ⟨4129615227735534940, 4129615227747625568⟩⟩, ⟨⟨442632234579219658361, 442632234579291454522⟩, ⟨559025968170363653056, 559025968170435449105⟩⟩, ⟨⟨4230269745022462456199, 4230269745022803385582⟩, ⟨-10171533731818258632003, -10171533731817917699346⟩⟩, ⟨⟨-99357482020353657281938, -99357482020352394744431⟩, ⟨11272426205063524324010, 11272426205064786855939⟩⟩, ⟨⟨322232873915666021830497, 322232873915669465444362⟩, ⟨451141006110154137650153, 451141006110157581212110⟩⟩, ⟨⟨823551075485459260885152, 823551075485465843924157⟩, ⟨-1735194093183944542223561, -1735194093183937959105548⟩⟩, ⟨⟨-4192955510971922950454167, -4192955510971914449014236⟩, ⟨270607814560576504113962, 270607814560585005640739⟩⟩, ⟨⟨3140516045727946821174568, 3140516045727954010328010⟩, ⟨4876296155373157029828129, 4876296155373164218911488⟩⟩, ⟨⟨2352271905739199608455472, 2352271905739203458909477⟩, ⟨-4401629081641622558955270, -4401629081641618708523902⟩⟩, ⟨⟨-2606246931638388178496535, -2606246931638386926981874⟩, ⟨44566332103252050725070, 44566332103253302244480⟩⟩, ⟨⟨395334762360385207700984, 395334762360385439301160⟩, ⟨682527057878564328653218, 682527057878564560254138⟩⟩, ⟨⟨65485682107684844755309, 65485682107684866914740⟩, ⟨-109759385530906151043294, -109759385530906128883861⟩⟩, ⟨⟨-9645901043629516205239, -9645901043629515269311⟩, ⟨-291204794605482776399, -291204794605481840471⟩⟩, ⟨⟨117505799838312919174, 117505799838312932319⟩, ⟨227130520164741221736, 227130520164741234885⟩⟩, ⟨⟨551901741250088861, 551901741250088917⟩, ⟨-831570908232194457, -831570908232194401⟩⟩],
  [z, z, z, z, z, z, z, z, z, ⟨⟨12117206254809812, 12117206254809846⟩, ⟨-16, 17⟩⟩, ⟨⟨-2010971878914075, -2010971878913535⟩, ⟨-269, 269⟩⟩, ⟨⟨7543030160369149, 7543030160370975⟩, ⟨-911, 911⟩⟩, ⟨⟨-1011287982978095292, -1011287982978093124⟩, ⟨-1087, 1084⟩⟩, ⟨⟨32840644941821201, 32840644941822045⟩, ⟨-423, 423⟩⟩, ⟨⟨-38118663392676761, -38118663392676680⟩, ⟨-40, 39⟩⟩, o, z, z],
  [z, z, z, z, z, z, z, z, z, z, ⟨⟨11864414825292533, 11864414825292565⟩, ⟨-18, 15⟩⟩, ⟨⟨-1979847310327351, -1979847310326869⟩, ⟨-240, 240⟩⟩, ⟨⟨7479666583530275, 7479666583531995⟩, ⟨-861, 860⟩⟩, ⟨⟨-1009932877232079140, -1009932877232076966⟩, ⟨-1088, 1087⟩⟩, ⟨⟨32794433364924785, 32794433364925652⟩, ⟨-432, 431⟩⟩, ⟨⟨-38059885960118545, -38059885960118464⟩, ⟨-40, 40⟩⟩, o, z],
  [z, z, z, z, z, z, z, z, z, z, z, ⟨⟨11617381243936000, 11617381243936038⟩, ⟨-19, 19⟩⟩, ⟨⟨-1949275277392071, -1949275277391519⟩, ⟨-276, 275⟩⟩, ⟨⟨7417005438253204, 7417005438255002⟩, ⟨-900, 901⟩⟩, ⟨⟨-1008584264412585912, -1008584264412583771⟩, ⟨-1070, 1070⟩⟩, ⟨⟨32748583275367666, 32748583275368524⟩, ⟨-433, 430⟩⟩, ⟨⟨-38001523981350815, -38001523981350733⟩, ⟨-40, 40⟩⟩, o]
]

private def w10Lit : List (List CFpIv) := [
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨24974800790525099, 24974800790525100⟩, ⟨0, 0⟩⟩, ⟨⟨-24974800790525100, -24974800790525099⟩, ⟨0, 0⟩⟩, ⟨⟨12679514247497358, 12679514247497359⟩, ⟨21516751450298547, 21516751450298548⟩⟩, ⟨⟨-12679514247497359, -12679514247497358⟩, ⟨-21516751450298548, -21516751450298547⟩⟩, ⟨⟨-12679514247497359, -12679514247497358⟩, ⟨21516751450298547, 21516751450298548⟩⟩, ⟨⟨12679514247497358, 12679514247497359⟩, ⟨-21516751450298548, -21516751450298547⟩⟩, ⟨⟨444975186414953246, 444975186414953247⟩, ⟨0, 0⟩⟩, ⟨⟨-444975186414953247, -444975186414953246⟩, ⟨0, 0⟩⟩, ⟨⟨225910479256822417, 225910479256822418⟩, ⟨383363237526728951, 383363237526728952⟩⟩, ⟨⟨-225910479256822418, -225910479256822417⟩, ⟨-383363237526728952, -383363237526728951⟩⟩, ⟨⟨-225910479256822418, -225910479256822417⟩, ⟨383363237526728951, 383363237526728952⟩⟩, ⟨⟨225910479256822417, 225910479256822418⟩, ⟨-383363237526728952, -383363237526728951⟩⟩, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨24977198527728892, 24977198527728893⟩, ⟨0, 0⟩⟩, ⟨⟨-24977198527728893, -24977198527728892⟩, ⟨0, 0⟩⟩, ⟨⟨12680731560231591, 12680731560231592⟩, ⟨21518817193120276, 21518817193120277⟩⟩, ⟨⟨-12680731560231592, -12680731560231591⟩, ⟨-21518817193120277, -21518817193120276⟩⟩, ⟨⟨-12680731560231592, -12680731560231591⟩, ⟨21518817193120276, 21518817193120277⟩⟩, ⟨⟨12680731560231591, 12680731560231592⟩, ⟨-21518817193120277, -21518817193120276⟩⟩, ⟨⟨445002826224423231, 445002826224423232⟩, ⟨0, 0⟩⟩, ⟨⟨-445002826224423232, -445002826224423231⟩, ⟨0, 0⟩⟩, ⟨⟨225924511775476409, 225924511775476410⟩, ⟨383387050285656937, 383387050285656938⟩⟩, ⟨⟨-225924511775476410, -225924511775476409⟩, ⟨-383387050285656938, -383387050285656937⟩⟩, ⟨⟨-225924511775476410, -225924511775476409⟩, ⟨383387050285656937, 383387050285656938⟩⟩, ⟨⟨225924511775476409, 225924511775476410⟩, ⟨-383387050285656938, -383387050285656937⟩⟩, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨24979596725085324, 24979596725085325⟩, ⟨0, 0⟩⟩, ⟨⟨-24979596725085325, -24979596725085324⟩, ⟨0, 0⟩⟩, ⟨⟨12681949106581780, 12681949106581781⟩, ⟨21520883332381202, 21520883332381203⟩⟩, ⟨⟨-12681949106581781, -12681949106581780⟩, ⟨-21520883332381203, -21520883332381202⟩⟩, ⟨⟨-12681949106581781, -12681949106581780⟩, ⟨21520883332381202, 21520883332381203⟩⟩, ⟨⟨12681949106581780, 12681949106581781⟩, ⟨-21520883332381203, -21520883332381202⟩⟩, ⟨⟨445030468900153049, 445030468900153050⟩, ⟨0, 0⟩⟩, ⟨⟨-445030468900153050, -445030468900153049⟩, ⟨0, 0⟩⟩, ⟨⟨225938545749308471, 225938545749308472⟩, ⟨383410865513978011, 383410865513978012⟩⟩, ⟨⟨-225938545749308472, -225938545749308471⟩, ⟨-383410865513978012, -383410865513978011⟩⟩, ⟨⟨-225938545749308472, -225938545749308471⟩, ⟨383410865513978011, 383410865513978012⟩⟩, ⟨⟨225938545749308471, 225938545749308472⟩, ⟨-383410865513978012, -383410865513978011⟩⟩, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨24981995382726788, 24981995382726789⟩, ⟨0, 0⟩⟩, ⟨⟨-24981995382726789, -24981995382726788⟩, ⟨0, 0⟩⟩, ⟨⟨12683166886615138, 12683166886615139⟩, ⟨21522949868195387, 21522949868195388⟩⟩, ⟨⟨-12683166886615139, -12683166886615138⟩, ⟨-21522949868195388, -21522949868195387⟩⟩, ⟨⟨-12683166886615139, -12683166886615138⟩, ⟨21522949868195387, 21522949868195388⟩⟩, ⟨⟨12683166886615138, 12683166886615139⟩, ⟨-21522949868195388, -21522949868195387⟩⟩, ⟨⟨445058114442500261, 445058114442500262⟩, ⟨0, 0⟩⟩, ⟨⟨-445058114442500262, -445058114442500261⟩, ⟨0, 0⟩⟩, ⟨⟨225952581178500132, 225952581178500133⟩, ⟨383434683212000225, 383434683212000226⟩⟩, ⟨⟨-225952581178500133, -225952581178500132⟩, ⟨-383434683212000226, -383434683212000225⟩⟩, ⟨⟨-225952581178500133, -225952581178500132⟩, ⟨383434683212000225, 383434683212000226⟩⟩, ⟨⟨225952581178500132, 225952581178500133⟩, ⟨-383434683212000226, -383434683212000225⟩⟩, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨24984394500785727, 24984394500785728⟩, ⟨0, 0⟩⟩, ⟨⟨-24984394500785728, -24984394500785727⟩, ⟨0, 0⟩⟩, ⟨⟨12684384900398907, 12684384900398908⟩, ⟨21525016800676934, 21525016800676935⟩⟩, ⟨⟨-12684384900398908, -12684384900398907⟩, ⟨-21525016800676935, -21525016800676934⟩⟩, ⟨⟨-12684384900398908, -12684384900398907⟩, ⟨21525016800676934, 21525016800676935⟩⟩, ⟨⟨12684384900398907, 12684384900398908⟩, ⟨-21525016800676935, -21525016800676934⟩⟩, ⟨⟨445085762851822468, 445085762851822469⟩, ⟨0, 0⟩⟩, ⟨⟨-445085762851822469, -445085762851822468⟩, ⟨0, 0⟩⟩, ⟨⟨225966618063232945, 225966618063232946⟩, ⟨383458503380031665, 383458503380031666⟩⟩, ⟨⟨-225966618063232946, -225966618063232945⟩, ⟨-383458503380031666, -383458503380031665⟩⟩, ⟨⟨-225966618063232946, -225966618063232945⟩, ⟨383458503380031665, 383458503380031666⟩⟩, ⟨⟨225966618063232945, 225966618063232946⟩, ⟨-383458503380031666, -383458503380031665⟩⟩, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨24986794079394636, 24986794079394637⟩, ⟨0, 0⟩⟩, ⟨⟨-24986794079394637, -24986794079394636⟩, ⟨0, 0⟩⟩, ⟨⟨12685603148000353, 12685603148000354⟩, ⟨21527084129939994, 21527084129939995⟩⟩, ⟨⟨-12685603148000354, -12685603148000353⟩, ⟨-21527084129939995, -21527084129939994⟩⟩, ⟨⟨-12685603148000354, -12685603148000353⟩, ⟨21527084129939994, 21527084129939995⟩⟩, ⟨⟨12685603148000353, 12685603148000354⟩, ⟨-21527084129939995, -21527084129939994⟩⟩, ⟨⟨445113414128477313, 445113414128477314⟩, ⟨0, 0⟩⟩, ⟨⟨-445113414128477314, -445113414128477313⟩, ⟨0, 0⟩⟩, ⟨⟨225980656403688482, 225980656403688483⟩, ⟨383482326018380454, 383482326018380455⟩⟩, ⟨⟨-225980656403688483, -225980656403688482⟩, ⟨-383482326018380455, -383482326018380454⟩⟩, ⟨⟨-225980656403688483, -225980656403688482⟩, ⟨383482326018380454, 383482326018380455⟩⟩, ⟨⟨225980656403688482, 225980656403688483⟩, ⟨-383482326018380455, -383482326018380454⟩⟩, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨24989194118686059, 24989194118686060⟩, ⟨0, 0⟩⟩, ⟨⟨-24989194118686060, -24989194118686059⟩, ⟨0, 0⟩⟩, ⟨⟨12686821629486768, 12686821629486769⟩, ⟨21529151856098758, 21529151856098759⟩⟩, ⟨⟨-12686821629486769, -12686821629486768⟩, ⟨-21529151856098759, -21529151856098758⟩⟩, ⟨⟨-12686821629486769, -12686821629486768⟩, ⟨21529151856098758, 21529151856098759⟩⟩, ⟨⟨12686821629486768, 12686821629486769⟩, ⟨-21529151856098759, -21529151856098758⟩⟩, ⟨⟨445141068272822480, 445141068272822481⟩, ⟨0, 0⟩⟩, ⟨⟨-445141068272822481, -445141068272822480⟩, ⟨0, 0⟩⟩, ⟨⟨225994696200048336, 225994696200048337⟩, ⟨383506151127354752, 383506151127354753⟩⟩, ⟨⟨-225994696200048337, -225994696200048336⟩, ⟨-383506151127354753, -383506151127354752⟩⟩, ⟨⟨-225994696200048337, -225994696200048336⟩, ⟨383506151127354752, 383506151127354753⟩⟩, ⟨⟨225994696200048336, 225994696200048337⟩, ⟨-383506151127354753, -383506151127354752⟩⟩, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨24991594618792592, 24991594618792593⟩, ⟨0, 0⟩⟩, ⟨⟨-24991594618792593, -24991594618792592⟩, ⟨0, 0⟩⟩, ⟨⟨12688040344925470, 12688040344925471⟩, ⟨21531219979267464, 21531219979267465⟩⟩, ⟨⟨-12688040344925471, -12688040344925470⟩, ⟨-21531219979267465, -21531219979267464⟩⟩, ⟨⟨-12688040344925471, -12688040344925470⟩, ⟨21531219979267464, 21531219979267465⟩⟩, ⟨⟨12688040344925470, 12688040344925471⟩, ⟨-21531219979267465, -21531219979267464⟩⟩, ⟨⟨445168725285215694, 445168725285215695⟩, ⟨0, 0⟩⟩, ⟨⟨-445168725285215695, -445168725285215694⟩, ⟨0, 0⟩⟩, ⟨⟨226008737452494121, 226008737452494122⟩, ⟨383529978707262751, 383529978707262752⟩⟩, ⟨⟨-226008737452494122, -226008737452494121⟩, ⟨-383529978707262752, -383529978707262751⟩⟩, ⟨⟨-226008737452494122, -226008737452494121⟩, ⟨383529978707262751, 383529978707262752⟩⟩, ⟨⟨226008737452494121, 226008737452494122⟩, ⟨-383529978707262752, -383529978707262751⟩⟩, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨24993995579846882, 24993995579846883⟩, ⟨0, 0⟩⟩, ⟨⟨-24993995579846883, -24993995579846882⟩, ⟨0, 0⟩⟩, ⟨⟨12689259294383802, 12689259294383803⟩, ⟨21533288499560391, 21533288499560392⟩⟩, ⟨⟨-12689259294383803, -12689259294383802⟩, ⟨-21533288499560392, -21533288499560391⟩⟩, ⟨⟨-12689259294383803, -12689259294383802⟩, ⟨21533288499560391, 21533288499560392⟩⟩, ⟨⟨12689259294383802, 12689259294383803⟩, ⟨-21533288499560392, -21533288499560391⟩⟩, ⟨⟨445196385166014720, 445196385166014721⟩, ⟨0, 0⟩⟩, ⟨⟨-445196385166014721, -445196385166014720⟩, ⟨0, 0⟩⟩, ⟨⟨226022780161207473, 226022780161207474⟩, ⟨383553808758412682, 383553808758412683⟩⟩, ⟨⟨-226022780161207474, -226022780161207473⟩, ⟨-383553808758412683, -383553808758412682⟩⟩, ⟨⟨-226022780161207474, -226022780161207473⟩, ⟨383553808758412682, 383553808758412683⟩⟩, ⟨⟨226022780161207473, 226022780161207474⟩, ⟨-383553808758412683, -383553808758412682⟩⟩, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨24996397001981628, 24996397001981629⟩, ⟨0, 0⟩⟩, ⟨⟨-24996397001981629, -24996397001981628⟩, ⟨0, 0⟩⟩, ⟨⟨12690478477929134, 12690478477929135⟩, ⟨21535357417091864, 21535357417091865⟩⟩, ⟨⟨-12690478477929135, -12690478477929134⟩, ⟨-21535357417091865, -21535357417091864⟩⟩, ⟨⟨-12690478477929135, -12690478477929134⟩, ⟨21535357417091864, 21535357417091865⟩⟩, ⟨⟨12690478477929134, 12690478477929135⟩, ⟨-21535357417091865, -21535357417091864⟩⟩, ⟨⟨445224047915577366, 445224047915577367⟩, ⟨0, 0⟩⟩, ⟨⟨-445224047915577367, -445224047915577366⟩, ⟨0, 0⟩⟩, ⟨⟨226036824326370047, 226036824326370048⟩, ⟨383577641281112808, 383577641281112809⟩⟩, ⟨⟨-226036824326370048, -226036824326370047⟩, ⟨-383577641281112809, -383577641281112808⟩⟩, ⟨⟨-226036824326370048, -226036824326370047⟩, ⟨383577641281112808, 383577641281112809⟩⟩, ⟨⟨226036824326370047, 226036824326370048⟩, ⟨-383577641281112809, -383577641281112808⟩⟩, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨24998798885329576, 24998798885329577⟩, ⟨0, 0⟩⟩, ⟨⟨-24998798885329577, -24998798885329576⟩, ⟨0, 0⟩⟩, ⟨⟨12691697895628861, 12691697895628862⟩, ⟨21537426731976250, 21537426731976251⟩⟩, ⟨⟨-12691697895628862, -12691697895628861⟩, ⟨-21537426731976251, -21537426731976250⟩⟩, ⟨⟨-12691697895628862, -12691697895628861⟩, ⟨21537426731976250, 21537426731976251⟩⟩, ⟨⟨12691697895628861, 12691697895628862⟩, ⟨-21537426731976251, -21537426731976250⟩⟩, ⟨⟨445251713534261481, 445251713534261482⟩, ⟨0, 0⟩⟩, ⟨⟨-445251713534261482, -445251713534261481⟩, ⟨0, 0⟩⟩, ⟨⟨226050869948163521, 226050869948163522⟩, ⟨383601476275671429, 383601476275671430⟩⟩, ⟨⟨-226050869948163522, -226050869948163521⟩, ⟨-383601476275671430, -383601476275671429⟩⟩, ⟨⟨-226050869948163522, -226050869948163521⟩, ⟨383601476275671429, 383601476275671430⟩⟩, ⟨⟨226050869948163521, 226050869948163522⟩, ⟨-383601476275671430, -383601476275671429⟩⟩, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨25001201230023527, 25001201230023528⟩, ⟨0, 0⟩⟩, ⟨⟨-25001201230023528, -25001201230023527⟩, ⟨0, 0⟩⟩, ⟨⟨12692917547550406, 12692917547550407⟩, ⟨21539496444327962, 21539496444327963⟩⟩, ⟨⟨-12692917547550407, -12692917547550406⟩, ⟨-21539496444327963, -21539496444327962⟩⟩, ⟨⟨-12692917547550407, -12692917547550406⟩, ⟨21539496444327962, 21539496444327963⟩⟩, ⟨⟨12692917547550406, 12692917547550407⟩, ⟨-21539496444327963, -21539496444327962⟩⟩, ⟨⟨445279382022424953, 445279382022424954⟩, ⟨0, 0⟩⟩, ⟨⟨-445279382022424954, -445279382022424953⟩, ⟨0, 0⟩⟩, ⟨⟨226064917026769591, 226064917026769592⟩, ⟨383625313742396883, 383625313742396884⟩⟩, ⟨⟨-226064917026769592, -226064917026769591⟩, ⟨-383625313742396884, -383625313742396883⟩⟩, ⟨⟨-226064917026769592, -226064917026769591⟩, ⟨383625313742396883, 383625313742396884⟩⟩, ⟨⟨226064917026769591, 226064917026769592⟩, ⟨-383625313742396884, -383625313742396883⟩⟩, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨25003604036196332, 25003604036196333⟩, ⟨0, 0⟩⟩, ⟨⟨-25003604036196333, -25003604036196332⟩, ⟨0, 0⟩⟩, ⟨⟨12694137433761214, 12694137433761215⟩, ⟨21541566554261455, 21541566554261456⟩⟩, ⟨⟨-12694137433761215, -12694137433761214⟩, ⟨-21541566554261456, -21541566554261455⟩⟩, ⟨⟨-12694137433761215, -12694137433761214⟩, ⟨21541566554261455, 21541566554261456⟩⟩, ⟨⟨12694137433761214, 12694137433761215⟩, ⟨-21541566554261456, -21541566554261455⟩⟩, ⟨⟨445307053380425714, 445307053380425715⟩, ⟨0, 0⟩⟩, ⟨⟨-445307053380425715, -445307053380425714⟩, ⟨0, 0⟩⟩, ⟨⟨226078965562369978, 226078965562369979⟩, ⟨383649153681597538, 383649153681597539⟩⟩, ⟨⟨-226078965562369979, -226078965562369978⟩, ⟨-383649153681597539, -383649153681597538⟩⟩, ⟨⟨-226078965562369979, -226078965562369978⟩, ⟨383649153681597538, 383649153681597539⟩⟩, ⟨⟨226078965562369978, 226078965562369979⟩, ⟨-383649153681597539, -383649153681597538⟩⟩, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨25006007303980891, 25006007303980892⟩, ⟨0, 0⟩⟩, ⟨⟨-25006007303980892, -25006007303980891⟩, ⟨0, 0⟩⟩, ⟨⟨12695357554328760, 12695357554328761⟩, ⟨21543637061891229, 21543637061891230⟩⟩, ⟨⟨-12695357554328761, -12695357554328760⟩, ⟨-21543637061891230, -21543637061891229⟩⟩, ⟨⟨-12695357554328761, -12695357554328760⟩, ⟨21543637061891229, 21543637061891230⟩⟩, ⟨⟨12695357554328760, 12695357554328761⟩, ⟨-21543637061891230, -21543637061891229⟩⟩, ⟨⟨445334727608621736, 445334727608621737⟩, ⟨0, 0⟩⟩, ⟨⟨-445334727608621737, -445334727608621736⟩, ⟨0, 0⟩⟩, ⟨⟨226093015555146420, 226093015555146421⟩, ⟨383672996093581803, 383672996093581804⟩⟩, ⟨⟨-226093015555146421, -226093015555146420⟩, ⟨-383672996093581804, -383672996093581803⟩⟩, ⟨⟨-226093015555146421, -226093015555146420⟩, ⟨383672996093581803, 383672996093581804⟩⟩, ⟨⟨226093015555146420, 226093015555146421⟩, ⟨-383672996093581804, -383672996093581803⟩⟩, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨25008411033510158, 25008411033510159⟩, ⟨0, 0⟩⟩, ⟨⟨-25008411033510159, -25008411033510158⟩, ⟨0, 0⟩⟩, ⟨⟨12696577909320541, 12696577909320542⟩, ⟨21545707967331828, 21545707967331829⟩⟩, ⟨⟨-12696577909320542, -12696577909320541⟩, ⟨-21545707967331829, -21545707967331828⟩⟩, ⟨⟨-12696577909320542, -12696577909320541⟩, ⟨21545707967331828, 21545707967331829⟩⟩, ⟨⟨12696577909320541, 12696577909320542⟩, ⟨-21545707967331829, -21545707967331828⟩⟩, ⟨⟨445362404707371031, 445362404707371032⟩, ⟨0, 0⟩⟩, ⟨⟨-445362404707371032, -445362404707371031⟩, ⟨0, 0⟩⟩, ⟨⟨226107067005280677, 226107067005280678⟩, ⟨383696840978658119, 383696840978658120⟩⟩, ⟨⟨-226107067005280678, -226107067005280677⟩, ⟨-383696840978658120, -383696840978658119⟩⟩, ⟨⟨-226107067005280678, -226107067005280677⟩, ⟨383696840978658119, 383696840978658120⟩⟩, ⟨⟨226107067005280677, 226107067005280678⟩, ⟨-383696840978658120, -383696840978658119⟩⟩, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨25010815224917134, 25010815224917135⟩, ⟨0, 0⟩⟩, ⟨⟨-25010815224917135, -25010815224917134⟩, ⟨0, 0⟩⟩, ⟨⟨12697798498804083, 12697798498804084⟩, ⟨21547779270697839, 21547779270697840⟩⟩, ⟨⟨-12697798498804084, -12697798498804083⟩, ⟨-21547779270697840, -21547779270697839⟩⟩, ⟨⟨-12697798498804084, -12697798498804083⟩, ⟨21547779270697839, 21547779270697840⟩⟩, ⟨⟨12697798498804083, 12697798498804084⟩, ⟨-21547779270697840, -21547779270697839⟩⟩, ⟨⟨445390084677031654, 445390084677031655⟩, ⟨0, 0⟩⟩, ⟨⟨-445390084677031655, -445390084677031654⟩, ⟨0, 0⟩⟩, ⟨⟨226121119912954532, 226121119912954533⟩, ⟨383720688337134964, 383720688337134965⟩⟩, ⟨⟨-226121119912954533, -226121119912954532⟩, ⟨-383720688337134965, -383720688337134964⟩⟩, ⟨⟨-226121119912954533, -226121119912954532⟩, ⟨383720688337134964, 383720688337134965⟩⟩, ⟨⟨226121119912954532, 226121119912954533⟩, ⟨-383720688337134965, -383720688337134964⟩⟩, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨25013219878334876, 25013219878334877⟩, ⟨0, 0⟩⟩, ⟨⟨-25013219878334877, -25013219878334876⟩, ⟨0, 0⟩⟩, ⟨⟨12699019322846937, 12699019322846938⟩, ⟨21549850972103893, 21549850972103894⟩⟩, ⟨⟨-12699019322846938, -12699019322846937⟩, ⟨-21549850972103894, -21549850972103893⟩⟩, ⟨⟨-12699019322846938, -12699019322846937⟩, ⟨21549850972103893, 21549850972103894⟩⟩, ⟨⟨12699019322846937, 12699019322846938⟩, ⟨-21549850972103894, -21549850972103893⟩⟩, ⟨⟨445417767517961701, 445417767517961702⟩, ⟨0, 0⟩⟩, ⟨⟨-445417767517961702, -445417767517961701⟩, ⟨0, 0⟩⟩, ⟨⟨226135174278349786, 226135174278349787⟩, ⟨383744538169320850, 383744538169320851⟩⟩, ⟨⟨-226135174278349787, -226135174278349786⟩, ⟨-383744538169320851, -383744538169320850⟩⟩, ⟨⟨-226135174278349787, -226135174278349786⟩, ⟨383744538169320850, 383744538169320851⟩⟩, ⟨⟨226135174278349786, 226135174278349787⟩, ⟨-383744538169320851, -383744538169320850⟩⟩, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨25015624993896489, 25015624993896490⟩, ⟨0, 0⟩⟩, ⟨⟨-25015624993896490, -25015624993896489⟩, ⟨0, 0⟩⟩, ⟨⟨12700240381516679, 12700240381516680⟩, ⟨21551923071664667, 21551923071664668⟩⟩, ⟨⟨-12700240381516680, -12700240381516679⟩, ⟨-21551923071664668, -21551923071664667⟩⟩, ⟨⟨-12700240381516680, -12700240381516679⟩, ⟨21551923071664667, 21551923071664668⟩⟩, ⟨⟨12700240381516679, 12700240381516680⟩, ⟨-21551923071664668, -21551923071664667⟩⟩, ⟨⟨445445453230519307, 445445453230519308⟩, ⟨0, 0⟩⟩, ⟨⟨-445445453230519308, -445445453230519307⟩, ⟨0, 0⟩⟩, ⟨⟨226149230101648263, 226149230101648264⟩, ⟨383768390475524326, 383768390475524327⟩⟩, ⟨⟨-226149230101648264, -226149230101648263⟩, ⟨-383768390475524327, -383768390475524326⟩⟩, ⟨⟨-226149230101648264, -226149230101648263⟩, ⟨383768390475524326, 383768390475524327⟩⟩, ⟨⟨226149230101648263, 226149230101648264⟩, ⟨-383768390475524327, -383768390475524326⟩⟩, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨-1000000000000000000, -999999999999999999⟩, ⟨0, 0⟩⟩, ⟨⟨-496138938356833825, -496138938356833824⟩, ⟨868243142124459193, 868243142124459194⟩⟩, ⟨⟨-868243142124459194, -868243142124459193⟩, ⟨-496138938356833825, -496138938356833824⟩⟩, ⟨⟨-868243142124459194, -868243142124459193⟩, ⟨496138938356833824, 496138938356833825⟩⟩, ⟨⟨-496138938356833825, -496138938356833824⟩, ⟨-868243142124459194, -868243142124459193⟩⟩, ⟨⟨967841943086869042, 967841943086869043⟩, ⟨0, 0⟩⟩, ⟨⟨-970480989484477286, -970480989484477285⟩, ⟨0, 0⟩⟩, ⟨⟨459429578403254070, 459429578403254071⟩, ⟨852658929370880753, 852658929370880754⟩⟩, ⟨⟨-522680012526473889, -522680012526473888⟩, ⟨-817004679774391225, -817004679774391224⟩⟩, ⟨⟨-522680012526473889, -522680012526473888⟩, ⟨817004679774391224, 817004679774391225⟩⟩, ⟨⟨459429578403254070, 459429578403254071⟩, ⟨-852658929370880754, -852658929370880753⟩⟩, ⟨⟨-511754451256178258, -511754451256178257⟩, ⟨0, 0⟩⟩, ⟨⟨-510957208009567794, -510957208009567793⟩, ⟨0, 0⟩⟩, ⟨⟨-510161932703562558, -510161932703562557⟩, ⟨0, 0⟩⟩, ⟨⟨-509368619952427297, -509368619952427296⟩, ⟨0, 0⟩⟩, ⟨⟨-508577264380740453, -508577264380740452⟩, ⟨0, 0⟩⟩, ⟨⟨-507787860623432186, -507787860623432185⟩, ⟨0, 0⟩⟩],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨868243142124459193, 868243142124459194⟩, ⟨496138938356833824, 496138938356833825⟩⟩, ⟨⟨496138938356833824, 496138938356833825⟩, ⟨-868243142124459194, -868243142124459193⟩⟩, ⟨⟨496138938356833824, 496138938356833825⟩, ⟨868243142124459193, 868243142124459194⟩⟩, ⟨⟨868243142124459193, 868243142124459194⟩, ⟨-496138938356833825, -496138938356833824⟩⟩, ⟨⟨970480989484477285, 970480989484477286⟩, ⟨0, 0⟩⟩, ⟨⟨-967841943086869043, -967841943086869042⟩, ⟨0, 0⟩⟩, ⟨⟨522680012526473888, 522680012526473889⟩, ⟨817004679774391224, 817004679774391225⟩⟩, ⟨⟨-459429578403254071, -459429578403254070⟩, ⟨-852658929370880754, -852658929370880753⟩⟩, ⟨⟨-459429578403254071, -459429578403254070⟩, ⟨852658929370880753, 852658929370880754⟩⟩, ⟨⟨522680012526473888, 522680012526473889⟩, ⟨-817004679774391225, -817004679774391224⟩⟩, ⟨⟨511754451256178257, 511754451256178258⟩, ⟨0, 0⟩⟩, ⟨⟨510957208009567793, 510957208009567794⟩, ⟨0, 0⟩⟩, ⟨⟨510161932703562557, 510161932703562558⟩, ⟨0, 0⟩⟩, ⟨⟨509368619952427296, 509368619952427297⟩, ⟨0, 0⟩⟩, ⟨⟨508577264380740452, 508577264380740453⟩, ⟨0, 0⟩⟩, ⟨⟨507787860623432185, 507787860623432186⟩, ⟨0, 0⟩⟩],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨-507692307692307693, -507692307692307692⟩, ⟨-861538461538461539, -861538461538461538⟩⟩, ⟨⟨-1000000000000000000, -999999999999999999⟩, ⟨0, 0⟩⟩, ⟨⟨0, 0⟩, ⟨-1000000000000000000, -999999999999999999⟩⟩, ⟨⟨967847325108872408, 967847325108872409⟩, ⟨-37072127363951338, -37072127363951337⟩⟩, ⟨⟨-969241576626762261, -969241576626762260⟩, ⟨-35521942598886575, -35521942598886574⟩⟩, ⟨⟨491365909567179667, 491365909567179668⟩, ⟨833833058659456405, 833833058659456406⟩⟩, ⟨⟨-492705733122888468, -492705733122888467⟩, ⟨-836106698632780431, -836106698632780430⟩⟩, ⟨⟨-523772171280983255, -523772171280983254⟩, ⟨814756710881529506, 814756710881529507⟩⟩, ⟨⟨460947641266757000, 460947641266757001⟩, ⟨-853324559039285687, -853324559039285686⟩⟩, ⟨⟨-259813798330059731, -259813798330059730⟩, ⟨-440896142620707423, -440896142620707422⟩⟩, ⟨⟨-259409044066395957, -259409044066395956⟩, ⟨-440209286900550715, -440209286900550714⟩⟩, ⟨⟨-259005288911039453, -259005288911039452⟩, ⟨-439524126636915435, -439524126636915434⟩⟩, ⟨⟨-258602530129693859, -258602530129693858⟩, ⟨-438840657189783517, -438840657189783516⟩⟩, ⟨⟨-258200764993298999, -258200764993298998⟩, ⟨-438158873928022544, -438158873928022543⟩⟩, ⟨⟨-257799990778050187, -257799990778050186⟩, ⟨-437478772229418499, -437478772229418498⟩⟩],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨0, 0⟩, ⟨999999999999999999, 1000000000000000000⟩⟩, ⟨⟨999999999999999999, 1000000000000000000⟩, ⟨0, 0⟩⟩, ⟨⟨969241576626762260, 969241576626762261⟩, ⟨35521942598886574, 35521942598886575⟩⟩, ⟨⟨-967847325108872409, -967847325108872408⟩, ⟨37072127363951337, 37072127363951338⟩⟩, ⟨⟨492705733122888467, 492705733122888468⟩, ⟨836106698632780430, 836106698632780431⟩⟩, ⟨⟨-491365909567179668, -491365909567179667⟩, ⟨-833833058659456406, -833833058659456405⟩⟩, ⟨⟨-460947641266757001, -460947641266757000⟩, ⟨853324559039285686, 853324559039285687⟩⟩, ⟨⟨523772171280983254, 523772171280983255⟩, ⟨-814756710881529507, -814756710881529506⟩⟩, ⟨⟨259813798330059730, 259813798330059731⟩, ⟨440896142620707422, 440896142620707423⟩⟩, ⟨⟨259409044066395956, 259409044066395957⟩, ⟨440209286900550714, 440209286900550715⟩⟩, ⟨⟨259005288911039452, 259005288911039453⟩, ⟨439524126636915434, 439524126636915435⟩⟩, ⟨⟨258602530129693858, 258602530129693859⟩, ⟨438840657189783516, 438840657189783517⟩⟩, ⟨⟨258200764993298998, 258200764993298999⟩, ⟨438158873928022543, 438158873928022544⟩⟩, ⟨⟨257799990778050186, 257799990778050187⟩, ⟨437478772229418498, 437478772229418499⟩⟩],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨507692307692307692, 507692307692307693⟩, ⟨-861538461538461539, -861538461538461538⟩⟩, ⟨⟨969241576626762260, 969241576626762261⟩, ⟨-35521942598886575, -35521942598886574⟩⟩, ⟨⟨-967847325108872409, -967847325108872408⟩, ⟨-37072127363951338, -37072127363951337⟩⟩, ⟨⟨523772171280983254, 523772171280983255⟩, ⟨814756710881529506, 814756710881529507⟩⟩, ⟨⟨-460947641266757001, -460947641266757000⟩, ⟨-853324559039285687, -853324559039285686⟩⟩, ⟨⟨-491365909567179668, -491365909567179667⟩, ⟨833833058659456405, 833833058659456406⟩⟩, ⟨⟨492705733122888467, 492705733122888468⟩, ⟨-836106698632780431, -836106698632780430⟩⟩, ⟨⟨259813798330059730, 259813798330059731⟩, ⟨-440896142620707423, -440896142620707422⟩⟩, ⟨⟨259409044066395956, 259409044066395957⟩, ⟨-440209286900550715, -440209286900550714⟩⟩, ⟨⟨259005288911039452, 259005288911039453⟩, ⟨-439524126636915435, -439524126636915434⟩⟩, ⟨⟨258602530129693858, 258602530129693859⟩, ⟨-438840657189783517, -438840657189783516⟩⟩, ⟨⟨258200764993298998, 258200764993298999⟩, ⟨-438158873928022544, -438158873928022543⟩⟩, ⟨⟨257799990778050186, 257799990778050187⟩, ⟨-437478772229418499, -437478772229418498⟩⟩],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨967847325108872408, 967847325108872409⟩, ⟨37072127363951337, 37072127363951338⟩⟩, ⟨⟨-969241576626762261, -969241576626762260⟩, ⟨35521942598886574, 35521942598886575⟩⟩, ⟨⟨460947641266757000, 460947641266757001⟩, ⟨853324559039285686, 853324559039285687⟩⟩, ⟨⟨-523772171280983255, -523772171280983254⟩, ⟨-814756710881529507, -814756710881529506⟩⟩, ⟨⟨-492705733122888468, -492705733122888467⟩, ⟨836106698632780430, 836106698632780431⟩⟩, ⟨⟨491365909567179667, 491365909567179668⟩, ⟨-833833058659456406, -833833058659456405⟩⟩, ⟨⟨-259813798330059731, -259813798330059730⟩, ⟨440896142620707422, 440896142620707423⟩⟩, ⟨⟨-259409044066395957, -259409044066395956⟩, ⟨440209286900550714, 440209286900550715⟩⟩, ⟨⟨-259005288911039453, -259005288911039452⟩, ⟨439524126636915434, 439524126636915435⟩⟩, ⟨⟨-258602530129693859, -258602530129693858⟩, ⟨438840657189783516, 438840657189783517⟩⟩, ⟨⟨-258200764993298999, -258200764993298998⟩, ⟨438158873928022543, 438158873928022544⟩⟩, ⟨⟨-257799990778050187, -257799990778050186⟩, ⟨437478772229418498, 437478772229418499⟩⟩],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨-1000000000000000000, -999999999999999999⟩, ⟨0, 0⟩⟩, ⟨⟨-496138938356833825, -496138938356833824⟩, ⟨868243142124459193, 868243142124459194⟩⟩, ⟨⟨-868243142124459194, -868243142124459193⟩, ⟨-496138938356833825, -496138938356833824⟩⟩, ⟨⟨-868243142124459194, -868243142124459193⟩, ⟨496138938356833824, 496138938356833825⟩⟩, ⟨⟨-496138938356833825, -496138938356833824⟩, ⟨-868243142124459194, -868243142124459193⟩⟩, ⟨⟨-999916391455352843, -999916391455352842⟩, ⟨0, 0⟩⟩, ⟨⟨-999832789901678855, -999832789901678854⟩, ⟨0, 0⟩⟩, ⟨⟨-999749195338977817, -999749195338977816⟩, ⟨0, 0⟩⟩, ⟨⟨-999665607767249362, -999665607767249361⟩, ⟨0, 0⟩⟩, ⟨⟨-999582027186492978, -999582027186492977⟩, ⟨0, 0⟩⟩, ⟨⟨-999498453596708003, -999498453596708002⟩, ⟨0, 0⟩⟩],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨868243142124459193, 868243142124459194⟩, ⟨496138938356833824, 496138938356833825⟩⟩, ⟨⟨496138938356833824, 496138938356833825⟩, ⟨-868243142124459194, -868243142124459193⟩⟩, ⟨⟨496138938356833824, 496138938356833825⟩, ⟨868243142124459193, 868243142124459194⟩⟩, ⟨⟨868243142124459193, 868243142124459194⟩, ⟨-496138938356833825, -496138938356833824⟩⟩, ⟨⟨999916391455352842, 999916391455352843⟩, ⟨0, 0⟩⟩, ⟨⟨999832789901678854, 999832789901678855⟩, ⟨0, 0⟩⟩, ⟨⟨999749195338977816, 999749195338977817⟩, ⟨0, 0⟩⟩, ⟨⟨999665607767249361, 999665607767249362⟩, ⟨0, 0⟩⟩, ⟨⟨999582027186492977, 999582027186492978⟩, ⟨0, 0⟩⟩, ⟨⟨999498453596708002, 999498453596708003⟩, ⟨0, 0⟩⟩],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨-507692307692307693, -507692307692307692⟩, ⟨-861538461538461539, -861538461538461538⟩⟩, ⟨⟨-1000000000000000000, -999999999999999999⟩, ⟨0, 0⟩⟩, ⟨⟨0, 0⟩, ⟨-1000000000000000000, -999999999999999999⟩⟩, ⟨⟨-507649860277332982, -507649860277332981⟩, ⟨-861466429561534757, -861466429561534756⟩⟩, ⟨⟨-507607416411621573, -507607416411621572⟩, ⟨-861394403607600244, -861394403607600243⟩⟩, ⟨⟨-507564976095173353, -507564976095173352⟩, ⟨-861322383676657812, -861322383676657811⟩⟩, ⟨⟨-507522539327988138, -507522539327988137⟩, ⟨-861250369768707143, -861250369768707142⟩⟩, ⟨⟨-507480106110065666, -507480106110065665⟩, ⟨-861178361883747796, -861178361883747795⟩⟩, ⟨⟨-507437676441405602, -507437676441405601⟩, ⟨-861106360021779203, -861106360021779202⟩⟩],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨0, 0⟩, ⟨999999999999999999, 1000000000000000000⟩⟩, ⟨⟨999999999999999999, 1000000000000000000⟩, ⟨0, 0⟩⟩, ⟨⟨507649860277332981, 507649860277332982⟩, ⟨861466429561534756, 861466429561534757⟩⟩, ⟨⟨507607416411621572, 507607416411621573⟩, ⟨861394403607600243, 861394403607600244⟩⟩, ⟨⟨507564976095173352, 507564976095173353⟩, ⟨861322383676657811, 861322383676657812⟩⟩, ⟨⟨507522539327988137, 507522539327988138⟩, ⟨861250369768707142, 861250369768707143⟩⟩, ⟨⟨507480106110065665, 507480106110065666⟩, ⟨861178361883747795, 861178361883747796⟩⟩, ⟨⟨507437676441405601, 507437676441405602⟩, ⟨861106360021779202, 861106360021779203⟩⟩],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨507692307692307692, 507692307692307693⟩, ⟨-861538461538461539, -861538461538461538⟩⟩, ⟨⟨507649860277332981, 507649860277332982⟩, ⟨-861466429561534757, -861466429561534756⟩⟩, ⟨⟨507607416411621572, 507607416411621573⟩, ⟨-861394403607600244, -861394403607600243⟩⟩, ⟨⟨507564976095173352, 507564976095173353⟩, ⟨-861322383676657812, -861322383676657811⟩⟩, ⟨⟨507522539327988137, 507522539327988138⟩, ⟨-861250369768707143, -861250369768707142⟩⟩, ⟨⟨507480106110065665, 507480106110065666⟩, ⟨-861178361883747796, -861178361883747795⟩⟩, ⟨⟨507437676441405601, 507437676441405602⟩, ⟨-861106360021779203, -861106360021779202⟩⟩],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨-507649860277332982, -507649860277332981⟩, ⟨861466429561534756, 861466429561534757⟩⟩, ⟨⟨-507607416411621573, -507607416411621572⟩, ⟨861394403607600243, 861394403607600244⟩⟩, ⟨⟨-507564976095173353, -507564976095173352⟩, ⟨861322383676657811, 861322383676657812⟩⟩, ⟨⟨-507522539327988138, -507522539327988137⟩, ⟨861250369768707142, 861250369768707143⟩⟩, ⟨⟨-507480106110065666, -507480106110065665⟩, ⟨861178361883747795, 861178361883747796⟩⟩, ⟨⟨-507437676441405602, -507437676441405601⟩, ⟨861106360021779202, 861106360021779203⟩⟩],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z]
]

private def fac10Lit : List (List (CFpIv × CFpIv)) := [
  [(o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, ⟨⟨24974800790525099, 24974800790525100⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-24974800790525100, -24974800790525099⟩, ⟨0, 0⟩⟩), (o, ⟨⟨12679514247497358, 12679514247497359⟩, ⟨21516751450298547, 21516751450298548⟩⟩), (o, ⟨⟨-12679514247497359, -12679514247497358⟩, ⟨-21516751450298548, -21516751450298547⟩⟩), (o, ⟨⟨-12679514247497359, -12679514247497358⟩, ⟨21516751450298547, 21516751450298548⟩⟩), (o, ⟨⟨12679514247497358, 12679514247497359⟩, ⟨-21516751450298548, -21516751450298547⟩⟩), (o, ⟨⟨444975186414953246, 444975186414953247⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-444975186414953247, -444975186414953246⟩, ⟨0, 0⟩⟩), (o, ⟨⟨225910479256822417, 225910479256822418⟩, ⟨383363237526728951, 383363237526728952⟩⟩), (o, ⟨⟨-225910479256822418, -225910479256822417⟩, ⟨-383363237526728952, -383363237526728951⟩⟩), (o, ⟨⟨-225910479256822418, -225910479256822417⟩, ⟨383363237526728951, 383363237526728952⟩⟩), (o, ⟨⟨225910479256822417, 225910479256822418⟩, ⟨-383363237526728952, -383363237526728951⟩⟩), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z)],
  [(z, o), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, ⟨⟨24977198527728892, 24977198527728893⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-24977198527728893, -24977198527728892⟩, ⟨0, 0⟩⟩), (o, ⟨⟨12680731560231591, 12680731560231592⟩, ⟨21518817193120276, 21518817193120277⟩⟩), (o, ⟨⟨-12680731560231592, -12680731560231591⟩, ⟨-21518817193120277, -21518817193120276⟩⟩), (o, ⟨⟨-12680731560231592, -12680731560231591⟩, ⟨21518817193120276, 21518817193120277⟩⟩), (o, ⟨⟨12680731560231591, 12680731560231592⟩, ⟨-21518817193120277, -21518817193120276⟩⟩), (o, ⟨⟨445002826224423231, 445002826224423232⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-445002826224423232, -445002826224423231⟩, ⟨0, 0⟩⟩), (o, ⟨⟨225924511775476409, 225924511775476410⟩, ⟨383387050285656937, 383387050285656938⟩⟩), (o, ⟨⟨-225924511775476410, -225924511775476409⟩, ⟨-383387050285656938, -383387050285656937⟩⟩), (o, ⟨⟨-225924511775476410, -225924511775476409⟩, ⟨383387050285656937, 383387050285656938⟩⟩), (o, ⟨⟨225924511775476409, 225924511775476410⟩, ⟨-383387050285656938, -383387050285656937⟩⟩), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z)],
  [(z, o), (z, o), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, ⟨⟨24979596725085324, 24979596725085325⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-24979596725085325, -24979596725085324⟩, ⟨0, 0⟩⟩), (o, ⟨⟨12681949106581780, 12681949106581781⟩, ⟨21520883332381202, 21520883332381203⟩⟩), (o, ⟨⟨-12681949106581781, -12681949106581780⟩, ⟨-21520883332381203, -21520883332381202⟩⟩), (o, ⟨⟨-12681949106581781, -12681949106581780⟩, ⟨21520883332381202, 21520883332381203⟩⟩), (o, ⟨⟨12681949106581780, 12681949106581781⟩, ⟨-21520883332381203, -21520883332381202⟩⟩), (o, ⟨⟨445030468900153049, 445030468900153050⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-445030468900153050, -445030468900153049⟩, ⟨0, 0⟩⟩), (o, ⟨⟨225938545749308471, 225938545749308472⟩, ⟨383410865513978011, 383410865513978012⟩⟩), (o, ⟨⟨-225938545749308472, -225938545749308471⟩, ⟨-383410865513978012, -383410865513978011⟩⟩), (o, ⟨⟨-225938545749308472, -225938545749308471⟩, ⟨383410865513978011, 383410865513978012⟩⟩), (o, ⟨⟨225938545749308471, 225938545749308472⟩, ⟨-383410865513978012, -383410865513978011⟩⟩), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z)],
  [(z, o), (z, o), (z, o), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, ⟨⟨24981995382726788, 24981995382726789⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-24981995382726789, -24981995382726788⟩, ⟨0, 0⟩⟩), (o, ⟨⟨12683166886615138, 12683166886615139⟩, ⟨21522949868195387, 21522949868195388⟩⟩), (o, ⟨⟨-12683166886615139, -12683166886615138⟩, ⟨-21522949868195388, -21522949868195387⟩⟩), (o, ⟨⟨-12683166886615139, -12683166886615138⟩, ⟨21522949868195387, 21522949868195388⟩⟩), (o, ⟨⟨12683166886615138, 12683166886615139⟩, ⟨-21522949868195388, -21522949868195387⟩⟩), (o, ⟨⟨445058114442500261, 445058114442500262⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-445058114442500262, -445058114442500261⟩, ⟨0, 0⟩⟩), (o, ⟨⟨225952581178500132, 225952581178500133⟩, ⟨383434683212000225, 383434683212000226⟩⟩), (o, ⟨⟨-225952581178500133, -225952581178500132⟩, ⟨-383434683212000226, -383434683212000225⟩⟩), (o, ⟨⟨-225952581178500133, -225952581178500132⟩, ⟨383434683212000225, 383434683212000226⟩⟩), (o, ⟨⟨225952581178500132, 225952581178500133⟩, ⟨-383434683212000226, -383434683212000225⟩⟩), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z)],
  [(z, o), (z, o), (z, o), (z, o), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, ⟨⟨24984394500785727, 24984394500785728⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-24984394500785728, -24984394500785727⟩, ⟨0, 0⟩⟩), (o, ⟨⟨12684384900398907, 12684384900398908⟩, ⟨21525016800676934, 21525016800676935⟩⟩), (o, ⟨⟨-12684384900398908, -12684384900398907⟩, ⟨-21525016800676935, -21525016800676934⟩⟩), (o, ⟨⟨-12684384900398908, -12684384900398907⟩, ⟨21525016800676934, 21525016800676935⟩⟩), (o, ⟨⟨12684384900398907, 12684384900398908⟩, ⟨-21525016800676935, -21525016800676934⟩⟩), (o, ⟨⟨445085762851822468, 445085762851822469⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-445085762851822469, -445085762851822468⟩, ⟨0, 0⟩⟩), (o, ⟨⟨225966618063232945, 225966618063232946⟩, ⟨383458503380031665, 383458503380031666⟩⟩), (o, ⟨⟨-225966618063232946, -225966618063232945⟩, ⟨-383458503380031666, -383458503380031665⟩⟩), (o, ⟨⟨-225966618063232946, -225966618063232945⟩, ⟨383458503380031665, 383458503380031666⟩⟩), (o, ⟨⟨225966618063232945, 225966618063232946⟩, ⟨-383458503380031666, -383458503380031665⟩⟩), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z)],
  [(z, o), (z, o), (z, o), (z, o), (z, o), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, ⟨⟨24986794079394636, 24986794079394637⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-24986794079394637, -24986794079394636⟩, ⟨0, 0⟩⟩), (o, ⟨⟨12685603148000353, 12685603148000354⟩, ⟨21527084129939994, 21527084129939995⟩⟩), (o, ⟨⟨-12685603148000354, -12685603148000353⟩, ⟨-21527084129939995, -21527084129939994⟩⟩), (o, ⟨⟨-12685603148000354, -12685603148000353⟩, ⟨21527084129939994, 21527084129939995⟩⟩), (o, ⟨⟨12685603148000353, 12685603148000354⟩, ⟨-21527084129939995, -21527084129939994⟩⟩), (o, ⟨⟨445113414128477313, 445113414128477314⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-445113414128477314, -445113414128477313⟩, ⟨0, 0⟩⟩), (o, ⟨⟨225980656403688482, 225980656403688483⟩, ⟨383482326018380454, 383482326018380455⟩⟩), (o, ⟨⟨-225980656403688483, -225980656403688482⟩, ⟨-383482326018380455, -383482326018380454⟩⟩), (o, ⟨⟨-225980656403688483, -225980656403688482⟩, ⟨383482326018380454, 383482326018380455⟩⟩), (o, ⟨⟨225980656403688482, 225980656403688483⟩, ⟨-383482326018380455, -383482326018380454⟩⟩), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z)],
  [(z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, ⟨⟨24989194118686059, 24989194118686060⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-24989194118686060, -24989194118686059⟩, ⟨0, 0⟩⟩), (o, ⟨⟨12686821629486768, 12686821629486769⟩, ⟨21529151856098758, 21529151856098759⟩⟩), (o, ⟨⟨-12686821629486769, -12686821629486768⟩, ⟨-21529151856098759, -21529151856098758⟩⟩), (o, ⟨⟨-12686821629486769, -12686821629486768⟩, ⟨21529151856098758, 21529151856098759⟩⟩), (o, ⟨⟨12686821629486768, 12686821629486769⟩, ⟨-21529151856098759, -21529151856098758⟩⟩), (o, ⟨⟨445141068272822480, 445141068272822481⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-445141068272822481, -445141068272822480⟩, ⟨0, 0⟩⟩), (o, ⟨⟨225994696200048336, 225994696200048337⟩, ⟨383506151127354752, 383506151127354753⟩⟩), (o, ⟨⟨-225994696200048337, -225994696200048336⟩, ⟨-383506151127354753, -383506151127354752⟩⟩), (o, ⟨⟨-225994696200048337, -225994696200048336⟩, ⟨383506151127354752, 383506151127354753⟩⟩), (o, ⟨⟨225994696200048336, 225994696200048337⟩, ⟨-383506151127354753, -383506151127354752⟩⟩), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z)],
  [(z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, ⟨⟨24991594618792592, 24991594618792593⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-24991594618792593, -24991594618792592⟩, ⟨0, 0⟩⟩), (o, ⟨⟨12688040344925470, 12688040344925471⟩, ⟨21531219979267464, 21531219979267465⟩⟩), (o, ⟨⟨-12688040344925471, -12688040344925470⟩, ⟨-21531219979267465, -21531219979267464⟩⟩), (o, ⟨⟨-12688040344925471, -12688040344925470⟩, ⟨21531219979267464, 21531219979267465⟩⟩), (o, ⟨⟨12688040344925470, 12688040344925471⟩, ⟨-21531219979267465, -21531219979267464⟩⟩), (o, ⟨⟨445168725285215694, 445168725285215695⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-445168725285215695, -445168725285215694⟩, ⟨0, 0⟩⟩), (o, ⟨⟨226008737452494121, 226008737452494122⟩, ⟨383529978707262751, 383529978707262752⟩⟩), (o, ⟨⟨-226008737452494122, -226008737452494121⟩, ⟨-383529978707262752, -383529978707262751⟩⟩), (o, ⟨⟨-226008737452494122, -226008737452494121⟩, ⟨383529978707262751, 383529978707262752⟩⟩), (o, ⟨⟨226008737452494121, 226008737452494122⟩, ⟨-383529978707262752, -383529978707262751⟩⟩), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z)],
  [(z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, ⟨⟨24993995579846882, 24993995579846883⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-24993995579846883, -24993995579846882⟩, ⟨0, 0⟩⟩), (o, ⟨⟨12689259294383802, 12689259294383803⟩, ⟨21533288499560391, 21533288499560392⟩⟩), (o, ⟨⟨-12689259294383803, -12689259294383802⟩, ⟨-21533288499560392, -21533288499560391⟩⟩), (o, ⟨⟨-12689259294383803, -12689259294383802⟩, ⟨21533288499560391, 21533288499560392⟩⟩), (o, ⟨⟨12689259294383802, 12689259294383803⟩, ⟨-21533288499560392, -21533288499560391⟩⟩), (o, ⟨⟨445196385166014720, 445196385166014721⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-445196385166014721, -445196385166014720⟩, ⟨0, 0⟩⟩), (o, ⟨⟨226022780161207473, 226022780161207474⟩, ⟨383553808758412682, 383553808758412683⟩⟩), (o, ⟨⟨-226022780161207474, -226022780161207473⟩, ⟨-383553808758412683, -383553808758412682⟩⟩), (o, ⟨⟨-226022780161207474, -226022780161207473⟩, ⟨383553808758412682, 383553808758412683⟩⟩), (o, ⟨⟨226022780161207473, 226022780161207474⟩, ⟨-383553808758412683, -383553808758412682⟩⟩), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z)],
  [(z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, ⟨⟨24996397001981628, 24996397001981629⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-24996397001981629, -24996397001981628⟩, ⟨0, 0⟩⟩), (o, ⟨⟨12690478477929134, 12690478477929135⟩, ⟨21535357417091864, 21535357417091865⟩⟩), (o, ⟨⟨-12690478477929135, -12690478477929134⟩, ⟨-21535357417091865, -21535357417091864⟩⟩), (o, ⟨⟨-12690478477929135, -12690478477929134⟩, ⟨21535357417091864, 21535357417091865⟩⟩), (o, ⟨⟨12690478477929134, 12690478477929135⟩, ⟨-21535357417091865, -21535357417091864⟩⟩), (o, ⟨⟨445224047915577366, 445224047915577367⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-445224047915577367, -445224047915577366⟩, ⟨0, 0⟩⟩), (o, ⟨⟨226036824326370047, 226036824326370048⟩, ⟨383577641281112808, 383577641281112809⟩⟩), (o, ⟨⟨-226036824326370048, -226036824326370047⟩, ⟨-383577641281112809, -383577641281112808⟩⟩), (o, ⟨⟨-226036824326370048, -226036824326370047⟩, ⟨383577641281112808, 383577641281112809⟩⟩), (o, ⟨⟨226036824326370047, 226036824326370048⟩, ⟨-383577641281112809, -383577641281112808⟩⟩), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z)],
  [(z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, ⟨⟨24998798885329576, 24998798885329577⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-24998798885329577, -24998798885329576⟩, ⟨0, 0⟩⟩), (o, ⟨⟨12691697895628861, 12691697895628862⟩, ⟨21537426731976250, 21537426731976251⟩⟩), (o, ⟨⟨-12691697895628862, -12691697895628861⟩, ⟨-21537426731976251, -21537426731976250⟩⟩), (o, ⟨⟨-12691697895628862, -12691697895628861⟩, ⟨21537426731976250, 21537426731976251⟩⟩), (o, ⟨⟨12691697895628861, 12691697895628862⟩, ⟨-21537426731976251, -21537426731976250⟩⟩), (o, ⟨⟨445251713534261481, 445251713534261482⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-445251713534261482, -445251713534261481⟩, ⟨0, 0⟩⟩), (o, ⟨⟨226050869948163521, 226050869948163522⟩, ⟨383601476275671429, 383601476275671430⟩⟩), (o, ⟨⟨-226050869948163522, -226050869948163521⟩, ⟨-383601476275671430, -383601476275671429⟩⟩), (o, ⟨⟨-226050869948163522, -226050869948163521⟩, ⟨383601476275671429, 383601476275671430⟩⟩), (o, ⟨⟨226050869948163521, 226050869948163522⟩, ⟨-383601476275671430, -383601476275671429⟩⟩), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z)],
  [(z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z), (o, ⟨⟨25001201230023527, 25001201230023528⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-25001201230023528, -25001201230023527⟩, ⟨0, 0⟩⟩), (o, ⟨⟨12692917547550406, 12692917547550407⟩, ⟨21539496444327962, 21539496444327963⟩⟩), (o, ⟨⟨-12692917547550407, -12692917547550406⟩, ⟨-21539496444327963, -21539496444327962⟩⟩), (o, ⟨⟨-12692917547550407, -12692917547550406⟩, ⟨21539496444327962, 21539496444327963⟩⟩), (o, ⟨⟨12692917547550406, 12692917547550407⟩, ⟨-21539496444327963, -21539496444327962⟩⟩), (o, ⟨⟨445279382022424953, 445279382022424954⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-445279382022424954, -445279382022424953⟩, ⟨0, 0⟩⟩), (o, ⟨⟨226064917026769591, 226064917026769592⟩, ⟨383625313742396883, 383625313742396884⟩⟩), (o, ⟨⟨-226064917026769592, -226064917026769591⟩, ⟨-383625313742396884, -383625313742396883⟩⟩), (o, ⟨⟨-226064917026769592, -226064917026769591⟩, ⟨383625313742396883, 383625313742396884⟩⟩), (o, ⟨⟨226064917026769591, 226064917026769592⟩, ⟨-383625313742396884, -383625313742396883⟩⟩), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z)],
  [(z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (o, z), (o, z), (o, z), (o, z), (o, z), (o, ⟨⟨25003604036196332, 25003604036196333⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-25003604036196333, -25003604036196332⟩, ⟨0, 0⟩⟩), (o, ⟨⟨12694137433761214, 12694137433761215⟩, ⟨21541566554261455, 21541566554261456⟩⟩), (o, ⟨⟨-12694137433761215, -12694137433761214⟩, ⟨-21541566554261456, -21541566554261455⟩⟩), (o, ⟨⟨-12694137433761215, -12694137433761214⟩, ⟨21541566554261455, 21541566554261456⟩⟩), (o, ⟨⟨12694137433761214, 12694137433761215⟩, ⟨-21541566554261456, -21541566554261455⟩⟩), (o, ⟨⟨445307053380425714, 445307053380425715⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-445307053380425715, -445307053380425714⟩, ⟨0, 0⟩⟩), (o, ⟨⟨226078965562369978, 226078965562369979⟩, ⟨383649153681597538, 383649153681597539⟩⟩), (o, ⟨⟨-226078965562369979, -226078965562369978⟩, ⟨-383649153681597539, -383649153681597538⟩⟩), (o, ⟨⟨-226078965562369979, -226078965562369978⟩, ⟨383649153681597538, 383649153681597539⟩⟩), (o, ⟨⟨226078965562369978, 226078965562369979⟩, ⟨-383649153681597539, -383649153681597538⟩⟩), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z)],
  [(z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (o, z), (o, z), (o, z), (o, z), (o, ⟨⟨25006007303980891, 25006007303980892⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-25006007303980892, -25006007303980891⟩, ⟨0, 0⟩⟩), (o, ⟨⟨12695357554328760, 12695357554328761⟩, ⟨21543637061891229, 21543637061891230⟩⟩), (o, ⟨⟨-12695357554328761, -12695357554328760⟩, ⟨-21543637061891230, -21543637061891229⟩⟩), (o, ⟨⟨-12695357554328761, -12695357554328760⟩, ⟨21543637061891229, 21543637061891230⟩⟩), (o, ⟨⟨12695357554328760, 12695357554328761⟩, ⟨-21543637061891230, -21543637061891229⟩⟩), (o, ⟨⟨445334727608621736, 445334727608621737⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-445334727608621737, -445334727608621736⟩, ⟨0, 0⟩⟩), (o, ⟨⟨226093015555146420, 226093015555146421⟩, ⟨383672996093581803, 383672996093581804⟩⟩), (o, ⟨⟨-226093015555146421, -226093015555146420⟩, ⟨-383672996093581804, -383672996093581803⟩⟩), (o, ⟨⟨-226093015555146421, -226093015555146420⟩, ⟨383672996093581803, 383672996093581804⟩⟩), (o, ⟨⟨226093015555146420, 226093015555146421⟩, ⟨-383672996093581804, -383672996093581803⟩⟩), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z)],
  [(z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (o, z), (o, z), (o, z), (o, ⟨⟨25008411033510158, 25008411033510159⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-25008411033510159, -25008411033510158⟩, ⟨0, 0⟩⟩), (o, ⟨⟨12696577909320541, 12696577909320542⟩, ⟨21545707967331828, 21545707967331829⟩⟩), (o, ⟨⟨-12696577909320542, -12696577909320541⟩, ⟨-21545707967331829, -21545707967331828⟩⟩), (o, ⟨⟨-12696577909320542, -12696577909320541⟩, ⟨21545707967331828, 21545707967331829⟩⟩), (o, ⟨⟨12696577909320541, 12696577909320542⟩, ⟨-21545707967331829, -21545707967331828⟩⟩), (o, ⟨⟨445362404707371031, 445362404707371032⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-445362404707371032, -445362404707371031⟩, ⟨0, 0⟩⟩), (o, ⟨⟨226107067005280677, 226107067005280678⟩, ⟨383696840978658119, 383696840978658120⟩⟩), (o, ⟨⟨-226107067005280678, -226107067005280677⟩, ⟨-383696840978658120, -383696840978658119⟩⟩), (o, ⟨⟨-226107067005280678, -226107067005280677⟩, ⟨383696840978658119, 383696840978658120⟩⟩), (o, ⟨⟨226107067005280677, 226107067005280678⟩, ⟨-383696840978658120, -383696840978658119⟩⟩), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z)],
  [(z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (o, z), (o, z), (o, ⟨⟨25010815224917134, 25010815224917135⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-25010815224917135, -25010815224917134⟩, ⟨0, 0⟩⟩), (o, ⟨⟨12697798498804083, 12697798498804084⟩, ⟨21547779270697839, 21547779270697840⟩⟩), (o, ⟨⟨-12697798498804084, -12697798498804083⟩, ⟨-21547779270697840, -21547779270697839⟩⟩), (o, ⟨⟨-12697798498804084, -12697798498804083⟩, ⟨21547779270697839, 21547779270697840⟩⟩), (o, ⟨⟨12697798498804083, 12697798498804084⟩, ⟨-21547779270697840, -21547779270697839⟩⟩), (o, ⟨⟨445390084677031654, 445390084677031655⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-445390084677031655, -445390084677031654⟩, ⟨0, 0⟩⟩), (o, ⟨⟨226121119912954532, 226121119912954533⟩, ⟨383720688337134964, 383720688337134965⟩⟩), (o, ⟨⟨-226121119912954533, -226121119912954532⟩, ⟨-383720688337134965, -383720688337134964⟩⟩), (o, ⟨⟨-226121119912954533, -226121119912954532⟩, ⟨383720688337134964, 383720688337134965⟩⟩), (o, ⟨⟨226121119912954532, 226121119912954533⟩, ⟨-383720688337134965, -383720688337134964⟩⟩), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z)],
  [(z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (o, z), (o, ⟨⟨25013219878334876, 25013219878334877⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-25013219878334877, -25013219878334876⟩, ⟨0, 0⟩⟩), (o, ⟨⟨12699019322846937, 12699019322846938⟩, ⟨21549850972103893, 21549850972103894⟩⟩), (o, ⟨⟨-12699019322846938, -12699019322846937⟩, ⟨-21549850972103894, -21549850972103893⟩⟩), (o, ⟨⟨-12699019322846938, -12699019322846937⟩, ⟨21549850972103893, 21549850972103894⟩⟩), (o, ⟨⟨12699019322846937, 12699019322846938⟩, ⟨-21549850972103894, -21549850972103893⟩⟩), (o, ⟨⟨445417767517961701, 445417767517961702⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-445417767517961702, -445417767517961701⟩, ⟨0, 0⟩⟩), (o, ⟨⟨226135174278349786, 226135174278349787⟩, ⟨383744538169320850, 383744538169320851⟩⟩), (o, ⟨⟨-226135174278349787, -226135174278349786⟩, ⟨-383744538169320851, -383744538169320850⟩⟩), (o, ⟨⟨-226135174278349787, -226135174278349786⟩, ⟨383744538169320850, 383744538169320851⟩⟩), (o, ⟨⟨226135174278349786, 226135174278349787⟩, ⟨-383744538169320851, -383744538169320850⟩⟩), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z)],
  [(z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (o, ⟨⟨25015624993896489, 25015624993896490⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-25015624993896490, -25015624993896489⟩, ⟨0, 0⟩⟩), (o, ⟨⟨12700240381516679, 12700240381516680⟩, ⟨21551923071664667, 21551923071664668⟩⟩), (o, ⟨⟨-12700240381516680, -12700240381516679⟩, ⟨-21551923071664668, -21551923071664667⟩⟩), (o, ⟨⟨-12700240381516680, -12700240381516679⟩, ⟨21551923071664667, 21551923071664668⟩⟩), (o, ⟨⟨12700240381516679, 12700240381516680⟩, ⟨-21551923071664668, -21551923071664667⟩⟩), (o, ⟨⟨445445453230519307, 445445453230519308⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-445445453230519308, -445445453230519307⟩, ⟨0, 0⟩⟩), (o, ⟨⟨226149230101648263, 226149230101648264⟩, ⟨383768390475524326, 383768390475524327⟩⟩), (o, ⟨⟨-226149230101648264, -226149230101648263⟩, ⟨-383768390475524327, -383768390475524326⟩⟩), (o, ⟨⟨-226149230101648264, -226149230101648263⟩, ⟨383768390475524326, 383768390475524327⟩⟩), (o, ⟨⟨226149230101648263, 226149230101648264⟩, ⟨-383768390475524327, -383768390475524326⟩⟩), (o, z), (o, z), (o, z), (o, z), (o, z), (o, z)],
  [(⟨⟨-24974800790525100, -24974800790525099⟩, ⟨0, 0⟩⟩, o), (⟨⟨-24977198527728893, -24977198527728892⟩, ⟨0, 0⟩⟩, o), (⟨⟨-24979596725085325, -24979596725085324⟩, ⟨0, 0⟩⟩, o), (⟨⟨-24981995382726789, -24981995382726788⟩, ⟨0, 0⟩⟩, o), (⟨⟨-24984394500785728, -24984394500785727⟩, ⟨0, 0⟩⟩, o), (⟨⟨-24986794079394637, -24986794079394636⟩, ⟨0, 0⟩⟩, o), (⟨⟨-24989194118686060, -24989194118686059⟩, ⟨0, 0⟩⟩, o), (⟨⟨-24991594618792593, -24991594618792592⟩, ⟨0, 0⟩⟩, o), (⟨⟨-24993995579846883, -24993995579846882⟩, ⟨0, 0⟩⟩, o), (⟨⟨-24996397001981629, -24996397001981628⟩, ⟨0, 0⟩⟩, o), (⟨⟨-24998798885329577, -24998798885329576⟩, ⟨0, 0⟩⟩, o), (⟨⟨-25001201230023528, -25001201230023527⟩, ⟨0, 0⟩⟩, o), (⟨⟨-25003604036196333, -25003604036196332⟩, ⟨0, 0⟩⟩, o), (⟨⟨-25006007303980892, -25006007303980891⟩, ⟨0, 0⟩⟩, o), (⟨⟨-25008411033510159, -25008411033510158⟩, ⟨0, 0⟩⟩, o), (⟨⟨-25010815224917135, -25010815224917134⟩, ⟨0, 0⟩⟩, o), (⟨⟨-25013219878334877, -25013219878334876⟩, ⟨0, 0⟩⟩, o), (⟨⟨-25015624993896490, -25015624993896489⟩, ⟨0, 0⟩⟩, o), (o, ⟨⟨-1000000000000000000, -999999999999999999⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-496138938356833825, -496138938356833824⟩, ⟨868243142124459193, 868243142124459194⟩⟩), (o, ⟨⟨-868243142124459194, -868243142124459193⟩, ⟨-496138938356833825, -496138938356833824⟩⟩), (o, ⟨⟨-868243142124459194, -868243142124459193⟩, ⟨496138938356833824, 496138938356833825⟩⟩), (o, ⟨⟨-496138938356833825, -496138938356833824⟩, ⟨-868243142124459194, -868243142124459193⟩⟩), (o, ⟨⟨967841943086869042, 967841943086869043⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-970480989484477286, -970480989484477285⟩, ⟨0, 0⟩⟩), (o, ⟨⟨459429578403254070, 459429578403254071⟩, ⟨852658929370880753, 852658929370880754⟩⟩), (o, ⟨⟨-522680012526473889, -522680012526473888⟩, ⟨-817004679774391225, -817004679774391224⟩⟩), (o, ⟨⟨-522680012526473889, -522680012526473888⟩, ⟨817004679774391224, 817004679774391225⟩⟩), (o, ⟨⟨459429578403254070, 459429578403254071⟩, ⟨-852658929370880754, -852658929370880753⟩⟩), (o, ⟨⟨-511754451256178258, -511754451256178257⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-510957208009567794, -510957208009567793⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-510161932703562558, -510161932703562557⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-509368619952427297, -509368619952427296⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-508577264380740453, -508577264380740452⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-507787860623432186, -507787860623432185⟩, ⟨0, 0⟩⟩)],
  [],
  [(⟨⟨-12679514247497359, -12679514247497358⟩, ⟨21516751450298547, 21516751450298548⟩⟩, o), (⟨⟨-12680731560231592, -12680731560231591⟩, ⟨21518817193120276, 21518817193120277⟩⟩, o), (⟨⟨-12681949106581781, -12681949106581780⟩, ⟨21520883332381202, 21520883332381203⟩⟩, o), (⟨⟨-12683166886615139, -12683166886615138⟩, ⟨21522949868195387, 21522949868195388⟩⟩, o), (⟨⟨-12684384900398908, -12684384900398907⟩, ⟨21525016800676934, 21525016800676935⟩⟩, o), (⟨⟨-12685603148000354, -12685603148000353⟩, ⟨21527084129939994, 21527084129939995⟩⟩, o), (⟨⟨-12686821629486769, -12686821629486768⟩, ⟨21529151856098758, 21529151856098759⟩⟩, o), (⟨⟨-12688040344925471, -12688040344925470⟩, ⟨21531219979267464, 21531219979267465⟩⟩, o), (⟨⟨-12689259294383803, -12689259294383802⟩, ⟨21533288499560391, 21533288499560392⟩⟩, o), (⟨⟨-12690478477929135, -12690478477929134⟩, ⟨21535357417091864, 21535357417091865⟩⟩, o), (⟨⟨-12691697895628862, -12691697895628861⟩, ⟨21537426731976250, 21537426731976251⟩⟩, o), (⟨⟨-12692917547550407, -12692917547550406⟩, ⟨21539496444327962, 21539496444327963⟩⟩, o), (⟨⟨-12694137433761215, -12694137433761214⟩, ⟨21541566554261455, 21541566554261456⟩⟩, o), (⟨⟨-12695357554328761, -12695357554328760⟩, ⟨21543637061891229, 21543637061891230⟩⟩, o), (⟨⟨-12696577909320542, -12696577909320541⟩, ⟨21545707967331828, 21545707967331829⟩⟩, o), (⟨⟨-12697798498804084, -12697798498804083⟩, ⟨21547779270697839, 21547779270697840⟩⟩, o), (⟨⟨-12699019322846938, -12699019322846937⟩, ⟨21549850972103893, 21549850972103894⟩⟩, o), (⟨⟨-12700240381516680, -12700240381516679⟩, ⟨21551923071664667, 21551923071664668⟩⟩, o), (⟨⟨496138938356833824, 496138938356833825⟩, ⟨868243142124459193, 868243142124459194⟩⟩, o), (⟨⟨-868243142124459194, -868243142124459193⟩, ⟨496138938356833824, 496138938356833825⟩⟩, o), (o, ⟨⟨-507692307692307693, -507692307692307692⟩, ⟨-861538461538461539, -861538461538461538⟩⟩), (o, ⟨⟨-1000000000000000000, -999999999999999999⟩, ⟨0, 0⟩⟩), (o, ⟨⟨0, 0⟩, ⟨-1000000000000000000, -999999999999999999⟩⟩), (o, ⟨⟨967847325108872408, 967847325108872409⟩, ⟨-37072127363951338, -37072127363951337⟩⟩), (o, ⟨⟨-969241576626762261, -969241576626762260⟩, ⟨-35521942598886575, -35521942598886574⟩⟩), (o, ⟨⟨491365909567179667, 491365909567179668⟩, ⟨833833058659456405, 833833058659456406⟩⟩), (o, ⟨⟨-492705733122888468, -492705733122888467⟩, ⟨-836106698632780431, -836106698632780430⟩⟩), (o, ⟨⟨-523772171280983255, -523772171280983254⟩, ⟨814756710881529506, 814756710881529507⟩⟩), (o, ⟨⟨460947641266757000, 460947641266757001⟩, ⟨-853324559039285687, -853324559039285686⟩⟩), (o, ⟨⟨-259813798330059731, -259813798330059730⟩, ⟨-440896142620707423, -440896142620707422⟩⟩), (o, ⟨⟨-259409044066395957, -259409044066395956⟩, ⟨-440209286900550715, -440209286900550714⟩⟩), (o, ⟨⟨-259005288911039453, -259005288911039452⟩, ⟨-439524126636915435, -439524126636915434⟩⟩), (o, ⟨⟨-258602530129693859, -258602530129693858⟩, ⟨-438840657189783517, -438840657189783516⟩⟩), (o, ⟨⟨-258200764993298999, -258200764993298998⟩, ⟨-438158873928022544, -438158873928022543⟩⟩), (o, ⟨⟨-257799990778050187, -257799990778050186⟩, ⟨-437478772229418499, -437478772229418498⟩⟩)],
  [],
  [(⟨⟨12679514247497358, 12679514247497359⟩, ⟨21516751450298547, 21516751450298548⟩⟩, o), (⟨⟨12680731560231591, 12680731560231592⟩, ⟨21518817193120276, 21518817193120277⟩⟩, o), (⟨⟨12681949106581780, 12681949106581781⟩, ⟨21520883332381202, 21520883332381203⟩⟩, o), (⟨⟨12683166886615138, 12683166886615139⟩, ⟨21522949868195387, 21522949868195388⟩⟩, o), (⟨⟨12684384900398907, 12684384900398908⟩, ⟨21525016800676934, 21525016800676935⟩⟩, o), (⟨⟨12685603148000353, 12685603148000354⟩, ⟨21527084129939994, 21527084129939995⟩⟩, o), (⟨⟨12686821629486768, 12686821629486769⟩, ⟨21529151856098758, 21529151856098759⟩⟩, o), (⟨⟨12688040344925470, 12688040344925471⟩, ⟨21531219979267464, 21531219979267465⟩⟩, o), (⟨⟨12689259294383802, 12689259294383803⟩, ⟨21533288499560391, 21533288499560392⟩⟩, o), (⟨⟨12690478477929134, 12690478477929135⟩, ⟨21535357417091864, 21535357417091865⟩⟩, o), (⟨⟨12691697895628861, 12691697895628862⟩, ⟨21537426731976250, 21537426731976251⟩⟩, o), (⟨⟨12692917547550406, 12692917547550407⟩, ⟨21539496444327962, 21539496444327963⟩⟩, o), (⟨⟨12694137433761214, 12694137433761215⟩, ⟨21541566554261455, 21541566554261456⟩⟩, o), (⟨⟨12695357554328760, 12695357554328761⟩, ⟨21543637061891229, 21543637061891230⟩⟩, o), (⟨⟨12696577909320541, 12696577909320542⟩, ⟨21545707967331828, 21545707967331829⟩⟩, o), (⟨⟨12697798498804083, 12697798498804084⟩, ⟨21547779270697839, 21547779270697840⟩⟩, o), (⟨⟨12699019322846937, 12699019322846938⟩, ⟨21549850972103893, 21549850972103894⟩⟩, o), (⟨⟨12700240381516679, 12700240381516680⟩, ⟨21551923071664667, 21551923071664668⟩⟩, o), (⟨⟨868243142124459193, 868243142124459194⟩, ⟨496138938356833824, 496138938356833825⟩⟩, o), (⟨⟨-496138938356833825, -496138938356833824⟩, ⟨868243142124459193, 868243142124459194⟩⟩, o), (⟨⟨999999999999999999, 1000000000000000000⟩, ⟨0, 0⟩⟩, o), (⟨⟨0, 0⟩, ⟨999999999999999999, 1000000000000000000⟩⟩, o), (o, ⟨⟨507692307692307692, 507692307692307693⟩, ⟨-861538461538461539, -861538461538461538⟩⟩), (o, ⟨⟨969241576626762260, 969241576626762261⟩, ⟨-35521942598886575, -35521942598886574⟩⟩), (o, ⟨⟨-967847325108872409, -967847325108872408⟩, ⟨-37072127363951338, -37072127363951337⟩⟩), (o, ⟨⟨523772171280983254, 523772171280983255⟩, ⟨814756710881529506, 814756710881529507⟩⟩), (o, ⟨⟨-460947641266757001, -460947641266757000⟩, ⟨-853324559039285687, -853324559039285686⟩⟩), (o, ⟨⟨-491365909567179668, -491365909567179667⟩, ⟨833833058659456405, 833833058659456406⟩⟩), (o, ⟨⟨492705733122888467, 492705733122888468⟩, ⟨-836106698632780431, -836106698632780430⟩⟩), (o, ⟨⟨259813798330059730, 259813798330059731⟩, ⟨-440896142620707423, -440896142620707422⟩⟩), (o, ⟨⟨259409044066395956, 259409044066395957⟩, ⟨-440209286900550715, -440209286900550714⟩⟩), (o, ⟨⟨259005288911039452, 259005288911039453⟩, ⟨-439524126636915435, -439524126636915434⟩⟩), (o, ⟨⟨258602530129693858, 258602530129693859⟩, ⟨-438840657189783517, -438840657189783516⟩⟩), (o, ⟨⟨258200764993298998, 258200764993298999⟩, ⟨-438158873928022544, -438158873928022543⟩⟩), (o, ⟨⟨257799990778050186, 257799990778050187⟩, ⟨-437478772229418499, -437478772229418498⟩⟩)],
  [],
  [(⟨⟨-444975186414953247, -444975186414953246⟩, ⟨0, 0⟩⟩, o), (⟨⟨-445002826224423232, -445002826224423231⟩, ⟨0, 0⟩⟩, o), (⟨⟨-445030468900153050, -445030468900153049⟩, ⟨0, 0⟩⟩, o), (⟨⟨-445058114442500262, -445058114442500261⟩, ⟨0, 0⟩⟩, o), (⟨⟨-445085762851822469, -445085762851822468⟩, ⟨0, 0⟩⟩, o), (⟨⟨-445113414128477314, -445113414128477313⟩, ⟨0, 0⟩⟩, o), (⟨⟨-445141068272822481, -445141068272822480⟩, ⟨0, 0⟩⟩, o), (⟨⟨-445168725285215695, -445168725285215694⟩, ⟨0, 0⟩⟩, o), (⟨⟨-445196385166014721, -445196385166014720⟩, ⟨0, 0⟩⟩, o), (⟨⟨-445224047915577367, -445224047915577366⟩, ⟨0, 0⟩⟩, o), (⟨⟨-445251713534261482, -445251713534261481⟩, ⟨0, 0⟩⟩, o), (⟨⟨-445279382022424954, -445279382022424953⟩, ⟨0, 0⟩⟩, o), (⟨⟨-445307053380425715, -445307053380425714⟩, ⟨0, 0⟩⟩, o), (⟨⟨-445334727608621737, -445334727608621736⟩, ⟨0, 0⟩⟩, o), (⟨⟨-445362404707371032, -445362404707371031⟩, ⟨0, 0⟩⟩, o), (⟨⟨-445390084677031655, -445390084677031654⟩, ⟨0, 0⟩⟩, o), (⟨⟨-445417767517961702, -445417767517961701⟩, ⟨0, 0⟩⟩, o), (⟨⟨-445445453230519308, -445445453230519307⟩, ⟨0, 0⟩⟩, o), (⟨⟨-967841943086869043, -967841943086869042⟩, ⟨0, 0⟩⟩, o), (⟨⟨-970480989484477286, -970480989484477285⟩, ⟨0, 0⟩⟩, o), (⟨⟨-967847325108872409, -967847325108872408⟩, ⟨-37072127363951338, -37072127363951337⟩⟩, o), (⟨⟨-969241576626762261, -969241576626762260⟩, ⟨35521942598886574, 35521942598886575⟩⟩, o), (⟨⟨-969241576626762261, -969241576626762260⟩, ⟨-35521942598886575, -35521942598886574⟩⟩, o), (⟨⟨-967847325108872409, -967847325108872408⟩, ⟨37072127363951337, 37072127363951338⟩⟩, o), (o, ⟨⟨-1000000000000000000, -999999999999999999⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-496138938356833825, -496138938356833824⟩, ⟨868243142124459193, 868243142124459194⟩⟩), (o, ⟨⟨-868243142124459194, -868243142124459193⟩, ⟨-496138938356833825, -496138938356833824⟩⟩), (o, ⟨⟨-868243142124459194, -868243142124459193⟩, ⟨496138938356833824, 496138938356833825⟩⟩), (o, ⟨⟨-496138938356833825, -496138938356833824⟩, ⟨-868243142124459194, -868243142124459193⟩⟩), (o, ⟨⟨-999916391455352843, -999916391455352842⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-999832789901678855, -999832789901678854⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-999749195338977817, -999749195338977816⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-999665607767249362, -999665607767249361⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-999582027186492978, -999582027186492977⟩, ⟨0, 0⟩⟩), (o, ⟨⟨-999498453596708003, -999498453596708002⟩, ⟨0, 0⟩⟩)],
  [],
  [(⟨⟨-225910479256822418, -225910479256822417⟩, ⟨383363237526728951, 383363237526728952⟩⟩, o), (⟨⟨-225924511775476410, -225924511775476409⟩, ⟨383387050285656937, 383387050285656938⟩⟩, o), (⟨⟨-225938545749308472, -225938545749308471⟩, ⟨383410865513978011, 383410865513978012⟩⟩, o), (⟨⟨-225952581178500133, -225952581178500132⟩, ⟨383434683212000225, 383434683212000226⟩⟩, o), (⟨⟨-225966618063232946, -225966618063232945⟩, ⟨383458503380031665, 383458503380031666⟩⟩, o), (⟨⟨-225980656403688483, -225980656403688482⟩, ⟨383482326018380454, 383482326018380455⟩⟩, o), (⟨⟨-225994696200048337, -225994696200048336⟩, ⟨383506151127354752, 383506151127354753⟩⟩, o), (⟨⟨-226008737452494122, -226008737452494121⟩, ⟨383529978707262751, 383529978707262752⟩⟩, o), (⟨⟨-226022780161207474, -226022780161207473⟩, ⟨383553808758412682, 383553808758412683⟩⟩, o), (⟨⟨-226036824326370048, -226036824326370047⟩, ⟨383577641281112808, 383577641281112809⟩⟩, o), (⟨⟨-226050869948163522, -226050869948163521⟩, ⟨383601476275671429, 383601476275671430⟩⟩, o), (⟨⟨-226064917026769592, -226064917026769591⟩, ⟨383625313742396883, 383625313742396884⟩⟩, o), (⟨⟨-226078965562369979, -226078965562369978⟩, ⟨383649153681597538, 383649153681597539⟩⟩, o), (⟨⟨-226093015555146421, -226093015555146420⟩, ⟨383672996093581803, 383672996093581804⟩⟩, o), (⟨⟨-226107067005280678, -226107067005280677⟩, ⟨383696840978658119, 383696840978658120⟩⟩, o), (⟨⟨-226121119912954533, -226121119912954532⟩, ⟨383720688337134964, 383720688337134965⟩⟩, o), (⟨⟨-226135174278349787, -226135174278349786⟩, ⟨383744538169320850, 383744538169320851⟩⟩, o), (⟨⟨-226149230101648264, -226149230101648263⟩, ⟨383768390475524326, 383768390475524327⟩⟩, o), (⟨⟨-459429578403254071, -459429578403254070⟩, ⟨852658929370880753, 852658929370880754⟩⟩, o), (⟨⟨-522680012526473889, -522680012526473888⟩, ⟨817004679774391224, 817004679774391225⟩⟩, o), (⟨⟨-491365909567179668, -491365909567179667⟩, ⟨833833058659456405, 833833058659456406⟩⟩, o), (⟨⟨-492705733122888468, -492705733122888467⟩, ⟨836106698632780430, 836106698632780431⟩⟩, o), (⟨⟨-523772171280983255, -523772171280983254⟩, ⟨814756710881529506, 814756710881529507⟩⟩, o), (⟨⟨-460947641266757001, -460947641266757000⟩, ⟨853324559039285686, 853324559039285687⟩⟩, o), (⟨⟨496138938356833824, 496138938356833825⟩, ⟨868243142124459193, 868243142124459194⟩⟩, o), (⟨⟨-868243142124459194, -868243142124459193⟩, ⟨496138938356833824, 496138938356833825⟩⟩, o), (o, ⟨⟨-507692307692307693, -507692307692307692⟩, ⟨-861538461538461539, -861538461538461538⟩⟩), (o, ⟨⟨-1000000000000000000, -999999999999999999⟩, ⟨0, 0⟩⟩), (o, ⟨⟨0, 0⟩, ⟨-1000000000000000000, -999999999999999999⟩⟩), (o, ⟨⟨-507649860277332982, -507649860277332981⟩, ⟨-861466429561534757, -861466429561534756⟩⟩), (o, ⟨⟨-507607416411621573, -507607416411621572⟩, ⟨-861394403607600244, -861394403607600243⟩⟩), (o, ⟨⟨-507564976095173353, -507564976095173352⟩, ⟨-861322383676657812, -861322383676657811⟩⟩), (o, ⟨⟨-507522539327988138, -507522539327988137⟩, ⟨-861250369768707143, -861250369768707142⟩⟩), (o, ⟨⟨-507480106110065666, -507480106110065665⟩, ⟨-861178361883747796, -861178361883747795⟩⟩), (o, ⟨⟨-507437676441405602, -507437676441405601⟩, ⟨-861106360021779203, -861106360021779202⟩⟩)],
  [],
  [(⟨⟨225910479256822417, 225910479256822418⟩, ⟨383363237526728951, 383363237526728952⟩⟩, o), (⟨⟨225924511775476409, 225924511775476410⟩, ⟨383387050285656937, 383387050285656938⟩⟩, o), (⟨⟨225938545749308471, 225938545749308472⟩, ⟨383410865513978011, 383410865513978012⟩⟩, o), (⟨⟨225952581178500132, 225952581178500133⟩, ⟨383434683212000225, 383434683212000226⟩⟩, o), (⟨⟨225966618063232945, 225966618063232946⟩, ⟨383458503380031665, 383458503380031666⟩⟩, o), (⟨⟨225980656403688482, 225980656403688483⟩, ⟨383482326018380454, 383482326018380455⟩⟩, o), (⟨⟨225994696200048336, 225994696200048337⟩, ⟨383506151127354752, 383506151127354753⟩⟩, o), (⟨⟨226008737452494121, 226008737452494122⟩, ⟨383529978707262751, 383529978707262752⟩⟩, o), (⟨⟨226022780161207473, 226022780161207474⟩, ⟨383553808758412682, 383553808758412683⟩⟩, o), (⟨⟨226036824326370047, 226036824326370048⟩, ⟨383577641281112808, 383577641281112809⟩⟩, o), (⟨⟨226050869948163521, 226050869948163522⟩, ⟨383601476275671429, 383601476275671430⟩⟩, o), (⟨⟨226064917026769591, 226064917026769592⟩, ⟨383625313742396883, 383625313742396884⟩⟩, o), (⟨⟨226078965562369978, 226078965562369979⟩, ⟨383649153681597538, 383649153681597539⟩⟩, o), (⟨⟨226093015555146420, 226093015555146421⟩, ⟨383672996093581803, 383672996093581804⟩⟩, o), (⟨⟨226107067005280677, 226107067005280678⟩, ⟨383696840978658119, 383696840978658120⟩⟩, o), (⟨⟨226121119912954532, 226121119912954533⟩, ⟨383720688337134964, 383720688337134965⟩⟩, o), (⟨⟨226135174278349786, 226135174278349787⟩, ⟨383744538169320850, 383744538169320851⟩⟩, o), (⟨⟨226149230101648263, 226149230101648264⟩, ⟨383768390475524326, 383768390475524327⟩⟩, o), (⟨⟨522680012526473888, 522680012526473889⟩, ⟨817004679774391224, 817004679774391225⟩⟩, o), (⟨⟨459429578403254070, 459429578403254071⟩, ⟨852658929370880753, 852658929370880754⟩⟩, o), (⟨⟨523772171280983254, 523772171280983255⟩, ⟨814756710881529506, 814756710881529507⟩⟩, o), (⟨⟨460947641266757000, 460947641266757001⟩, ⟨853324559039285686, 853324559039285687⟩⟩, o), (⟨⟨491365909567179667, 491365909567179668⟩, ⟨833833058659456405, 833833058659456406⟩⟩, o), (⟨⟨492705733122888467, 492705733122888468⟩, ⟨836106698632780430, 836106698632780431⟩⟩, o), (⟨⟨868243142124459193, 868243142124459194⟩, ⟨496138938356833824, 496138938356833825⟩⟩, o), (⟨⟨-496138938356833825, -496138938356833824⟩, ⟨868243142124459193, 868243142124459194⟩⟩, o), (⟨⟨999999999999999999, 1000000000000000000⟩, ⟨0, 0⟩⟩, o), (⟨⟨0, 0⟩, ⟨999999999999999999, 1000000000000000000⟩⟩, o), (o, ⟨⟨507692307692307692, 507692307692307693⟩, ⟨-861538461538461539, -861538461538461538⟩⟩), (o, ⟨⟨507649860277332981, 507649860277332982⟩, ⟨-861466429561534757, -861466429561534756⟩⟩), (o, ⟨⟨507607416411621572, 507607416411621573⟩, ⟨-861394403607600244, -861394403607600243⟩⟩), (o, ⟨⟨507564976095173352, 507564976095173353⟩, ⟨-861322383676657812, -861322383676657811⟩⟩), (o, ⟨⟨507522539327988137, 507522539327988138⟩, ⟨-861250369768707143, -861250369768707142⟩⟩), (o, ⟨⟨507480106110065665, 507480106110065666⟩, ⟨-861178361883747796, -861178361883747795⟩⟩), (o, ⟨⟨507437676441405601, 507437676441405602⟩, ⟨-861106360021779203, -861106360021779202⟩⟩)],
  [],
  [(z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (⟨⟨511754451256178257, 511754451256178258⟩, ⟨0, 0⟩⟩, o), (⟨⟨-511754451256178258, -511754451256178257⟩, ⟨0, 0⟩⟩, o), (⟨⟨259813798330059730, 259813798330059731⟩, ⟨-440896142620707423, -440896142620707422⟩⟩, o), (⟨⟨-259813798330059731, -259813798330059730⟩, ⟨440896142620707422, 440896142620707423⟩⟩, o), (⟨⟨-259813798330059731, -259813798330059730⟩, ⟨-440896142620707423, -440896142620707422⟩⟩, o), (⟨⟨259813798330059730, 259813798330059731⟩, ⟨440896142620707422, 440896142620707423⟩⟩, o), (⟨⟨999916391455352842, 999916391455352843⟩, ⟨0, 0⟩⟩, o), (⟨⟨-999916391455352843, -999916391455352842⟩, ⟨0, 0⟩⟩, o), (⟨⟨507649860277332981, 507649860277332982⟩, ⟨-861466429561534757, -861466429561534756⟩⟩, o), (⟨⟨-507649860277332982, -507649860277332981⟩, ⟨861466429561534756, 861466429561534757⟩⟩, o), (⟨⟨-507649860277332982, -507649860277332981⟩, ⟨-861466429561534757, -861466429561534756⟩⟩, o), (⟨⟨507649860277332981, 507649860277332982⟩, ⟨861466429561534756, 861466429561534757⟩⟩, o), (o, z), (o, z), (o, z), (o, z), (o, z)],
  [(z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (⟨⟨510957208009567793, 510957208009567794⟩, ⟨0, 0⟩⟩, o), (⟨⟨-510957208009567794, -510957208009567793⟩, ⟨0, 0⟩⟩, o), (⟨⟨259409044066395956, 259409044066395957⟩, ⟨-440209286900550715, -440209286900550714⟩⟩, o), (⟨⟨-259409044066395957, -259409044066395956⟩, ⟨440209286900550714, 440209286900550715⟩⟩, o), (⟨⟨-259409044066395957, -259409044066395956⟩, ⟨-440209286900550715, -440209286900550714⟩⟩, o), (⟨⟨259409044066395956, 259409044066395957⟩, ⟨440209286900550714, 440209286900550715⟩⟩, o), (⟨⟨999832789901678854, 999832789901678855⟩, ⟨0, 0⟩⟩, o), (⟨⟨-999832789901678855, -999832789901678854⟩, ⟨0, 0⟩⟩, o), (⟨⟨507607416411621572, 507607416411621573⟩, ⟨-861394403607600244, -861394403607600243⟩⟩, o), (⟨⟨-507607416411621573, -507607416411621572⟩, ⟨861394403607600243, 861394403607600244⟩⟩, o), (⟨⟨-507607416411621573, -507607416411621572⟩, ⟨-861394403607600244, -861394403607600243⟩⟩, o), (⟨⟨507607416411621572, 507607416411621573⟩, ⟨861394403607600243, 861394403607600244⟩⟩, o), (z, o), (o, z), (o, z), (o, z), (o, z)],
  [(z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (⟨⟨510161932703562557, 510161932703562558⟩, ⟨0, 0⟩⟩, o), (⟨⟨-510161932703562558, -510161932703562557⟩, ⟨0, 0⟩⟩, o), (⟨⟨259005288911039452, 259005288911039453⟩, ⟨-439524126636915435, -439524126636915434⟩⟩, o), (⟨⟨-259005288911039453, -259005288911039452⟩, ⟨439524126636915434, 439524126636915435⟩⟩, o), (⟨⟨-259005288911039453, -259005288911039452⟩, ⟨-439524126636915435, -439524126636915434⟩⟩, o), (⟨⟨259005288911039452, 259005288911039453⟩, ⟨439524126636915434, 439524126636915435⟩⟩, o), (⟨⟨999749195338977816, 999749195338977817⟩, ⟨0, 0⟩⟩, o), (⟨⟨-999749195338977817, -999749195338977816⟩, ⟨0, 0⟩⟩, o), (⟨⟨507564976095173352, 507564976095173353⟩, ⟨-861322383676657812, -861322383676657811⟩⟩, o), (⟨⟨-507564976095173353, -507564976095173352⟩, ⟨861322383676657811, 861322383676657812⟩⟩, o), (⟨⟨-507564976095173353, -507564976095173352⟩, ⟨-861322383676657812, -861322383676657811⟩⟩, o), (⟨⟨507564976095173352, 507564976095173353⟩, ⟨861322383676657811, 861322383676657812⟩⟩, o), (z, o), (z, o), (o, z), (o, z), (o, z)],
  [(z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (⟨⟨509368619952427296, 509368619952427297⟩, ⟨0, 0⟩⟩, o), (⟨⟨-509368619952427297, -509368619952427296⟩, ⟨0, 0⟩⟩, o), (⟨⟨258602530129693858, 258602530129693859⟩, ⟨-438840657189783517, -438840657189783516⟩⟩, o), (⟨⟨-258602530129693859, -258602530129693858⟩, ⟨438840657189783516, 438840657189783517⟩⟩, o), (⟨⟨-258602530129693859, -258602530129693858⟩, ⟨-438840657189783517, -438840657189783516⟩⟩, o), (⟨⟨258602530129693858, 258602530129693859⟩, ⟨438840657189783516, 438840657189783517⟩⟩, o), (⟨⟨999665607767249361, 999665607767249362⟩, ⟨0, 0⟩⟩, o), (⟨⟨-999665607767249362, -999665607767249361⟩, ⟨0, 0⟩⟩, o), (⟨⟨507522539327988137, 507522539327988138⟩, ⟨-861250369768707143, -861250369768707142⟩⟩, o), (⟨⟨-507522539327988138, -507522539327988137⟩, ⟨861250369768707142, 861250369768707143⟩⟩, o), (⟨⟨-507522539327988138, -507522539327988137⟩, ⟨-861250369768707143, -861250369768707142⟩⟩, o), (⟨⟨507522539327988137, 507522539327988138⟩, ⟨861250369768707142, 861250369768707143⟩⟩, o), (z, o), (z, o), (z, o), (o, z), (o, z)],
  [(z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (⟨⟨508577264380740452, 508577264380740453⟩, ⟨0, 0⟩⟩, o), (⟨⟨-508577264380740453, -508577264380740452⟩, ⟨0, 0⟩⟩, o), (⟨⟨258200764993298998, 258200764993298999⟩, ⟨-438158873928022544, -438158873928022543⟩⟩, o), (⟨⟨-258200764993298999, -258200764993298998⟩, ⟨438158873928022543, 438158873928022544⟩⟩, o), (⟨⟨-258200764993298999, -258200764993298998⟩, ⟨-438158873928022544, -438158873928022543⟩⟩, o), (⟨⟨258200764993298998, 258200764993298999⟩, ⟨438158873928022543, 438158873928022544⟩⟩, o), (⟨⟨999582027186492977, 999582027186492978⟩, ⟨0, 0⟩⟩, o), (⟨⟨-999582027186492978, -999582027186492977⟩, ⟨0, 0⟩⟩, o), (⟨⟨507480106110065665, 507480106110065666⟩, ⟨-861178361883747796, -861178361883747795⟩⟩, o), (⟨⟨-507480106110065666, -507480106110065665⟩, ⟨861178361883747795, 861178361883747796⟩⟩, o), (⟨⟨-507480106110065666, -507480106110065665⟩, ⟨-861178361883747796, -861178361883747795⟩⟩, o), (⟨⟨507480106110065665, 507480106110065666⟩, ⟨861178361883747795, 861178361883747796⟩⟩, o), (z, o), (z, o), (z, o), (z, o), (o, z)],
  [(z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (z, o), (⟨⟨507787860623432185, 507787860623432186⟩, ⟨0, 0⟩⟩, o), (⟨⟨-507787860623432186, -507787860623432185⟩, ⟨0, 0⟩⟩, o), (⟨⟨257799990778050186, 257799990778050187⟩, ⟨-437478772229418499, -437478772229418498⟩⟩, o), (⟨⟨-257799990778050187, -257799990778050186⟩, ⟨437478772229418498, 437478772229418499⟩⟩, o), (⟨⟨-257799990778050187, -257799990778050186⟩, ⟨-437478772229418499, -437478772229418498⟩⟩, o), (⟨⟨257799990778050186, 257799990778050187⟩, ⟨437478772229418498, 437478772229418499⟩⟩, o), (⟨⟨999498453596708002, 999498453596708003⟩, ⟨0, 0⟩⟩, o), (⟨⟨-999498453596708003, -999498453596708002⟩, ⟨0, 0⟩⟩, o), (⟨⟨507437676441405601, 507437676441405602⟩, ⟨-861106360021779203, -861106360021779202⟩⟩, o), (⟨⟨-507437676441405602, -507437676441405601⟩, ⟨861106360021779202, 861106360021779203⟩⟩, o), (⟨⟨-507437676441405602, -507437676441405601⟩, ⟨-861106360021779203, -861106360021779202⟩⟩, o), (⟨⟨507437676441405601, 507437676441405602⟩, ⟨861106360021779202, 861106360021779203⟩⟩, o), (z, o), (z, o), (z, o), (z, o), (z, o)]
]

private def st10_1 : List (List CFpIv) := [
  [o, z, z, z, z],
  [z, o, z, z, z],
  [z, z, o, z, z],
  [z, z, z, o, z],
  [z, z, z, z, o],
  [z, z, z, z, o],
  [z, z, z, z, o],
  [z, z, z, z, o],
  [z, z, z, z, o],
  [z, z, z, z, o],
  [z, z, z, z, o],
  [z, z, z, z, o],
  [z, z, z, z, o],
  [z, z, z, z, o],
  [z, z, z, z, o],
  [z, z, z, z, o],
  [z, z, z, z, o],
  [z, z, z, z, o],
  [⟨⟨389276606000, 389276606001⟩, ⟨0, 0⟩⟩, ⟨⟨-62338123161036, -62338123161034⟩, ⟨0, 0⟩⟩, ⟨⟨3743522142492197, 3743522142492200⟩, ⟨0, 0⟩⟩, ⟨⟨-99913591426066107, -99913591426066103⟩, ⟨0, 0⟩⟩, o],
  [o],
  [⟨⟨-206521062377, -206521062375⟩, ⟨329977767090, 329977767092⟩⟩, ⟨⟨62315877786176, 62315877786181⟩, ⟨1665225203491, 1665225203496⟩⟩, ⟨⟨-1813725402528178, -1813725402528171⟩, ⟨-3274806589029866, -3274806589029860⟩⟩, ⟨⟨-50725361800925871, -50725361800925867⟩, ⟨86079401843995412, 86079401843995416⟩⟩, o],
  [o],
  [⟨⟨-206521062377, -206521062375⟩, ⟨-329977767092, -329977767090⟩⟩, ⟨⟨-62315877786181, -62315877786176⟩, ⟨1665225203491, 1665225203496⟩⟩, ⟨⟨-1813725402528178, -1813725402528171⟩, ⟨3274806589029860, 3274806589029866⟩⟩, ⟨⟨50725361800925867, 50725361800925871⟩, ⟨86079401843995412, 86079401843995416⟩⟩, o],
  [o],
  [⟨⟨39219769088893091, 39219769088893093⟩, ⟨0, 0⟩⟩, ⟨⟨-352524062788007237, -352524062788007231⟩, ⟨0, 0⟩⟩, ⟨⟨1188238905388850250, 1188238905388850259⟩, ⟨0, 0⟩⟩, ⟨⟨-1780066595982029791, -1780066595982029787⟩, ⟨0, 0⟩⟩, o],
  [o],
  [⟨⟨-20807077161949177, -20807077161949172⟩, ⟨33245388061546026, 33245388061546031⟩⟩, ⟨⟨352398264487949970, 352398264487949981⟩, ⟨9416901318571942, 9416901318571953⟩⟩, ⟨⟨-575698234161177869, -575698234161177856⟩, ⟨-1039462957234838004, -1039462957234837991⟩⟩, ⟨⟨-903726117960107433, -903726117960107429⟩, ⟨1533595836538364124, 1533595836538364128⟩⟩, o],
  [o],
  [⟨⟨-20807077161949177, -20807077161949172⟩, ⟨-33245388061546031, -33245388061546026⟩⟩, ⟨⟨-352398264487949981, -352398264487949970⟩, ⟨9416901318571942, 9416901318571953⟩⟩, ⟨⟨-575698234161177869, -575698234161177856⟩, ⟨1039462957234837991, 1039462957234838004⟩⟩, ⟨⟨903726117960107429, 903726117960107433⟩, ⟨1533595836538364124, 1533595836538364128⟩⟩, o],
  [o],
  [z, z, z, z, o],
  [z, z, z, z, o],
  [z, z, z, z, o],
  [z, z, z, z, o],
  [z, z, z, z, o],
  [z, z, z, z, o]
]

private def st10_2 : List (List CFpIv) := [
  [o, z, z, z, z, z, z, z, z],
  [z, o, z, z, z, z, z, z, z],
  [z, z, o, z, z, z, z, z, z],
  [z, z, z, o, z, z, z, z, z],
  [z, z, z, z, o, z, z, z, z],
  [z, z, z, z, z, o, z, z, z],
  [z, z, z, z, z, z, o, z, z],
  [z, z, z, z, z, z, z, o, z],
  [z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, o],
  [⟨⟨151769, 151770⟩, ⟨0, 0⟩⟩, ⟨⟨-48598841, -48598839⟩, ⟨0, 0⟩⟩, ⟨⟨6808414167, 6808414170⟩, ⟨0, 0⟩⟩, ⟨⟨-545039504063, -545039504059⟩, ⟨0, 0⟩⟩, ⟨⟨27270305864332, 27270305864337⟩, ⟨0, 0⟩⟩, ⟨⟨-873236757336620, -873236757336613⟩, ⟨0, 0⟩⟩, ⟨⟨17476482315676914, 17476482315676925⟩, ⟨0, 0⟩⟩, ⟨⟨-199865568743725125, -199865568743725117⟩, ⟨0, 0⟩⟩, o],
  [o],
  [⟨⟨-66337, -66335⟩, ⟨-136505, -136503⟩⟩, ⟨⟨-26874165, -26874161⟩, ⟨40492301, 40492306⟩⟩, ⟨⟨6798697563, 6798697570⟩, ⟨363613672, 363613679⟩⟩, ⟨⟨-251239223843, -251239223834⟩, ⟨-483680590262, -483680590254⟩⟩, ⟨⟨-14467585392035, -14467585392023⟩, ⟨23116196807835, 23116196807845⟩⟩, ⟨⟨872925142581147, 872925142581161⟩, ⟨23326590266070, 23326590266083⟩⟩, ⟨⟨-8467303976376497, -8467303976376481⟩, ⟨-15288302636388622, -15288302636388608⟩⟩, ⟨⟨-101470211823737373, -101470211823737365⟩, ⟨172191874609978562, 172191874609978570⟩⟩, o],
  [o],
  [⟨⟨-66337, -66335⟩, ⟨136503, 136505⟩⟩, ⟨⟨26874161, 26874165⟩, ⟨40492301, 40492306⟩⟩, ⟨⟨6798697563, 6798697570⟩, ⟨-363613679, -363613672⟩⟩, ⟨⟨251239223834, 251239223843⟩, ⟨-483680590262, -483680590254⟩⟩, ⟨⟨-14467585392035, -14467585392023⟩, ⟨-23116196807845, -23116196807835⟩⟩, ⟨⟨-872925142581161, -872925142581147⟩, ⟨23326590266070, 23326590266083⟩⟩, ⟨⟨-8467303976376497, -8467303976376481⟩, ⟨15288302636388608, 15288302636388622⟩⟩, ⟨⟨101470211823737365, 101470211823737373⟩, ⟨172191874609978562, 172191874609978570⟩⟩, o],
  [o],
  [⟨⟨1539719915419988, 1539719915419990⟩, ⟨0, 0⟩⟩, ⟨⟨-27675884064902032, -27675884064902027⟩, ⟨0, 0⟩⟩, ⟨⟨217640309213175594, 217640309213175606⟩, ⟨0, 0⟩⟩, ⟨⟨-978000588036085790, -978000588036085763⟩, ⟨0, 0⟩⟩, ⟨⟨2746748611529397006, 2746748611529397049⟩, ⟨0, 0⟩⟩, ⟨⟨-4937176851888925444, -4937176851888925395⟩, ⟨0, 0⟩⟩, ⟨⟨5546493018591427893, 5546493018591427924⟩, ⟨0, 0⟩⟩, ⟨⟨-3560575566520367750, -3560575566520367742⟩, ⟨0, 0⟩⟩, o],
  [o],
  [⟨⟨-672989946266097, -672989946266092⟩, ⟨-1384854487000603, -1384854487000598⟩⟩, ⟨⟨-15304197185511824, -15304197185511807⟩, ⟨23059403879564404, 23059403879564422⟩⟩, ⟨⟨217329704647415744, 217329704647415787⟩, ⟨11623410526765282, 11623410526765323⟩⟩, ⟨⟨-450815228659572347, -450815228659572270⟩, ⟨-867900213047299101, -867900213047299023⟩⟩, ⟨⟨-1457219449075087138, -1457219449075087035⟩, ⟨2328334042223316772, 2328334042223316874⟩⟩, ⟨⟨4935415019093349168, 4935415019093349260⟩, ⟨131885769268847134, 131885769268847229⟩⟩, ⟨⟨-2687259457764888291, -2687259457764888241⟩, ⟨-4852032709281400626, -4852032709281400579⟩⟩, ⟨⟨-1807676826079571321, -1807676826079571313⟩, ⟨3067572795771393746, 3067572795771393754⟩⟩, o],
  [o],
  [⟨⟨-672989946266097, -672989946266092⟩, ⟨1384854487000598, 1384854487000603⟩⟩, ⟨⟨15304197185511807, 15304197185511824⟩, ⟨23059403879564404, 23059403879564422⟩⟩, ⟨⟨217329704647415744, 217329704647415787⟩, ⟨-11623410526765323, -11623410526765282⟩⟩, ⟨⟨450815228659572270, 450815228659572347⟩, ⟨-867900213047299101, -867900213047299023⟩⟩, ⟨⟨-1457219449075087138, -1457219449075087035⟩, ⟨-2328334042223316874, -2328334042223316772⟩⟩, ⟨⟨-4935415019093349260, -4935415019093349168⟩, ⟨131885769268847134, 131885769268847229⟩⟩, ⟨⟨-2687259457764888291, -2687259457764888241⟩, ⟨4852032709281400579, 4852032709281400626⟩⟩, ⟨⟨1807676826079571313, 1807676826079571321⟩, ⟨3067572795771393746, 3067572795771393754⟩⟩, o],
  [o],
  [z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, o]
]

private def st10_3 : List (List CFpIv) := [
  [o, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, o, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, o, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, o, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, o, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, o, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, o, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, o, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, o, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, o, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, o, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, o, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, o],
  [⟨⟨0, 1⟩, ⟨0, 0⟩⟩, ⟨⟨-30, -28⟩, ⟨0, 0⟩⟩, ⟨⟨6262, 6265⟩, ⟨0, 0⟩⟩, ⟨⟨-835616, -835612⟩, ⟨0, 0⟩⟩, ⟨⟨75241352, 75241359⟩, ⟨0, 0⟩⟩, ⟨⟨-4817760213, -4817760207⟩, ⟨0, 0⟩⟩, ⟨⟨224936821852, 224936821859⟩, ⟨0, 0⟩⟩, ⟨⟨-7715824579370, -7715824579360⟩, ⟨0, 0⟩⟩, ⟨⟨192988281375144, 192988281375153⟩, ⟨0, 0⟩⟩, ⟨⟨-3432550948509349, -3432550948509335⟩, ⟨0, 0⟩⟩, ⟨⟨41210398493486145, 41210398493486163⟩, ⟨0, 0⟩⟩, ⟨⟨-299855961440906742, -299855961440906730⟩, ⟨0, 0⟩⟩, o],
  [o],
  [⟨⟨0, 2⟩, ⟨-1, 1⟩⟩, ⟨⟨-14, -10⟩, ⟨-28, -23⟩⟩, ⟨⟨-3605, -3599⟩, ⟨5122, 5128⟩⟩, ⟨⟨832928, 832936⟩, ⟨66896, 66906⟩⟩, ⟨⟨-32886945, -32886933⟩, ⟨-67673566, -67673555⟩⟩, ⟨⟨-2664122752, -2664122738⟩, ⟨4014132955, 4014132970⟩⟩, ⟨⟨224615804091, 224615804108⟩, ⟨12013091832, 12013091849⟩⟩, ⟨⟨-3556655552772, -3556655552753⟩, ⟨-6847200173695, -6847200173678⟩⟩, ⟨⟨-102385153079913, -102385153079891⟩, ⟨163590211128098, 163590211128118⟩⟩, ⟨⟨3431326041844045, 3431326041844070⟩, ⟨91693013229899, 91693013229923⟩⟩, ⟨⟨-19966316145838160, -19966316145838134⟩, ⟨-36050563983887545, -36050563983887522⟩⟩, ⟨⟨-152234565039229580, -152234565039229568⟩, ⟨258337443702935029, 258337443702935041⟩⟩, o],
  [o],
  [⟨⟨0, 2⟩, ⟨-1, 1⟩⟩, ⟨⟨10, 14⟩, ⟨-28, -23⟩⟩, ⟨⟨-3605, -3599⟩, ⟨-5128, -5122⟩⟩, ⟨⟨-832936, -832928⟩, ⟨66896, 66906⟩⟩, ⟨⟨-32886945, -32886933⟩, ⟨67673555, 67673566⟩⟩, ⟨⟨2664122738, 2664122752⟩, ⟨4014132955, 4014132970⟩⟩, ⟨⟨224615804091, 224615804108⟩, ⟨-12013091849, -12013091832⟩⟩, ⟨⟨3556655552753, 3556655552772⟩, ⟨-6847200173695, -6847200173678⟩⟩, ⟨⟨-102385153079913, -102385153079891⟩, ⟨-163590211128118, -163590211128098⟩⟩, ⟨⟨-3431326041844070, -3431326041844045⟩, ⟨91693013229899, 91693013229923⟩⟩, ⟨⟨-19966316145838160, -19966316145838134⟩, ⟨36050563983887522, 36050563983887545⟩⟩, ⟨⟨152234565039229568, 152234565039229580⟩, ⟨258337443702935029, 258337443702935041⟩⟩, o],
  [o],
  [⟨⟨60507631896486, 60507631896488⟩, ⟨0, 0⟩⟩, ⟨⟨-1631200074178587, -1631200074178582⟩, ⟨0, 0⟩⟩, ⟨⟨20155136813767931, 20155136813767943⟩, ⟨0, 0⟩⟩, ⟨⟨-150931650916928969, -150931650916928944⟩, ⟨0, 0⟩⟩, ⟨⟨762919412084814602, 762919412084814650⟩, ⟨0, 0⟩⟩, ⟨⟨-2742296889974226964, -2742296889974226867⟩, ⟨0, 0⟩⟩, ⟨⟨7187487162167073355, 7187487162167073524⟩, ⟨0, 0⟩⟩, ⟨⟨-13840319371381831735, -13840319371381831504⟩, ⟨0, 0⟩⟩, ⟨⟨19433093789896457386, 19433093789896457619⟩, ⟨0, 0⟩⟩, ⟨⟨-19403284179440770868, -19403284179440770705⟩, ⟨0, 0⟩⟩, ⟨⟨13077126144964148079, 13077126144964148147⟩, ⟨0, 0⟩⟩, ⟨⟨-5341527095158646274, -5341527095158646262⟩, ⟨0, 0⟩⟩, o],
  [o],
  [⟨⟨60162465397828, 60162465397833⟩, ⟨6453779898296, 6453779898300⟩⟩, ⟨⟨-673528982832668, -673528982832652⟩, ⟨-1485655542608934, -1485655542608918⟩⟩, ⟨⟨-11589992776463522, -11589992776463473⟩, ⟨16489439269521165, 16489439269521212⟩⟩, ⟨⟨150447141552209756, 150447141552209874⟩, ⟨12083908609346679, 12083908609346800⟩⟩, ⟨⟨-333461358135560576, -333461358135560322⟩, ⟨-686184779754132159, -686184779754131908⟩⟩, ⟨⟨-1516434027796970443, -1516434027796970000⟩, ⟨2284867626822563640, 2284867626822564082⟩⟩, ⟨⟨7177229566333928889, 7177229566333929514⟩, ⟨383858643850270716, 383858643850271339⟩⟩, ⟨⟨-6379778108989019929, -6379778108989019256⟩, ⟨-12282217698034491210, -12282217698034490531⟩⟩, ⟨⟨-10309746624599080755, -10309746624599080211⟩, ⟨16472833963331267658, 16472833963331268197⟩⟩, ⟨⟨19396360112623892357, 19396360112623892664⟩, ⟨518315858863459086, 518315858863459396⟩⟩, ⟨⟨-6335828927512807435, -6335828927512807331⟩, ⟨-11439777096281063108, -11439777096281063006⟩⟩, ⟨⟨-2711852217542081957, -2711852217542081945⟩, ⟨4601931035828987548, 4601931035828987560⟩⟩, o],
  [o],
  [⟨⟨60162465397828, 60162465397833⟩, ⟨-6453779898300, -6453779898296⟩⟩, ⟨⟨673528982832652, 673528982832668⟩, ⟨-1485655542608934, -1485655542608918⟩⟩, ⟨⟨-11589992776463522, -11589992776463473⟩, ⟨-16489439269521212, -16489439269521165⟩⟩, ⟨⟨-150447141552209874, -150447141552209756⟩, ⟨12083908609346679, 12083908609346800⟩⟩, ⟨⟨-333461358135560576, -333461358135560322⟩, ⟨686184779754131908, 686184779754132159⟩⟩, ⟨⟨1516434027796970000, 1516434027796970443⟩, ⟨2284867626822563640, 2284867626822564082⟩⟩, ⟨⟨7177229566333928889, 7177229566333929514⟩, ⟨-383858643850271339, -383858643850270716⟩⟩, ⟨⟨6379778108989019256, 6379778108989019929⟩, ⟨-12282217698034491210, -12282217698034490531⟩⟩, ⟨⟨-10309746624599080755, -10309746624599080211⟩, ⟨-16472833963331268197, -16472833963331267658⟩⟩, ⟨⟨-19396360112623892664, -19396360112623892357⟩, ⟨518315858863459086, 518315858863459396⟩⟩, ⟨⟨-6335828927512807435, -6335828927512807331⟩, ⟨11439777096281063006, 11439777096281063108⟩⟩, ⟨⟨2711852217542081945, 2711852217542081957⟩, ⟨4601931035828987548, 4601931035828987560⟩⟩, o],
  [o],
  [z, z, z, z, z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, o]
]

private def st10_4 : List (List CFpIv) := [
  [o, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, o, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, o, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, o, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, o, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, o, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, o, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, o, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, o, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, o, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, o, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, o, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, o, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, o, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, o, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, o, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, o],
  [⟨⟨0, 1⟩, ⟨0, 0⟩⟩, ⟨⟨-2, 0⟩, ⟨0, 0⟩⟩, ⟨⟨0, 3⟩, ⟨0, 0⟩⟩, ⟨⟨-4, 0⟩, ⟨0, 0⟩⟩, ⟨⟨106, 111⟩, ⟨0, 0⟩⟩, ⟨⟨-10385, -10379⟩, ⟨0, 0⟩⟩, ⟨⟨761501, 761509⟩, ⟨0, 0⟩⟩, ⟨⟨-43527135, -43527126⟩, ⟨0, 0⟩⟩, ⟨⟨1959285341, 1959285353⟩, ⟨0, 0⟩⟩, ⟨⟨-69683554389, -69683554379⟩, ⟨0, 0⟩⟩, ⟨⟨1951701770615, 1951701770628⟩, ⟨0, 0⟩⟩, ⟨⟨-42594854290223, -42594854290208⟩, ⟨0, 0⟩⟩, ⟨⟨710118791212934, 710118791212947⟩, ⟨0, 0⟩⟩, ⟨⟨-8742441771179186, -8742441771179165⟩, ⟨0, 0⟩⟩, ⟨⟨74956804880735229, 74956804880735253⟩, ⟨0, 0⟩⟩, ⟨⟨-399884799039511261, -399884799039511245⟩, ⟨0, 0⟩⟩, o],
  [o],
  [⟨⟨-2, 2⟩, ⟨-2, 2⟩⟩, ⟨⟨-4, 4⟩, ⟨-4, 4⟩⟩, ⟨⟨-6, 6⟩, ⟨-6, 6⟩⟩, ⟨⟨-8, 4⟩, ⟨-4, 8⟩⟩, ⟨⟨102, 115⟩, ⟨7, 18⟩⟩, ⟨⟨-4292, -4280⟩, ⟨-9462, -9449⟩⟩, ⟨⟨-437904, -437890⟩, ⟨622999, 623015⟩⟩, ⟨⟨43387395, 43387412⟩, ⟨3484864, 3484883⟩⟩, ⟨⟨-856376113, -856376092⟩, ⟨-1762219928, -1762219909⟩⟩, ⟨⟨-38533578719, -38533578693⟩, ⟨58059978146, 58059978173⟩⟩, ⟨⟨1948916406613, 1948916406643⟩, ⟨104233590665, 104233590692⟩⟩, ⟨⟨-19634353201299, -19634353201270⟩, ⟨-37799653257312, -37799653257283⟩⟩, ⟨⟨-376735937670342, -376735937670309⟩, ⟨601945787344153, 601945787344183⟩⟩, ⟨⟨8739322028644518, 8739322028644557⟩, ⟨233535012593046, 233535012593082⟩⟩, ⟨⟨-36316350199021334, -36316350199021294⟩, ⟨-65571680671999416, -65571680671999378⟩⟩, ⟨⟨-203018436435444182, -203018436435444166⟩, ⟨344516134557117380, 344516134557117396⟩⟩, o],
  [o],
  [⟨⟨-2, 2⟩, ⟨-2, 2⟩⟩, ⟨⟨-4, 4⟩, ⟨-4, 4⟩⟩, ⟨⟨-6, 6⟩, ⟨-6, 6⟩⟩, ⟨⟨-4, 8⟩, ⟨-4, 8⟩⟩, ⟨⟨102, 115⟩, ⟨-18, -7⟩⟩, ⟨⟨4280, 4292⟩, ⟨-9462, -9449⟩⟩, ⟨⟨-437904, -437890⟩, ⟨-623015, -622999⟩⟩, ⟨⟨-43387412, -43387395⟩, ⟨3484864, 3484883⟩⟩, ⟨⟨-856376113, -856376092⟩, ⟨1762219909, 1762219928⟩⟩, ⟨⟨38533578693, 38533578719⟩, ⟨58059978146, 58059978173⟩⟩, ⟨⟨1948916406613, 1948916406643⟩, ⟨-104233590692, -104233590665⟩⟩, ⟨⟨19634353201270, 19634353201299⟩, ⟨-37799653257312, -37799653257283⟩⟩, ⟨⟨-376735937670342, -376735937670309⟩, ⟨-601945787344183, -601945787344153⟩⟩, ⟨⟨-8739322028644557, -8739322028644518⟩, ⟨233535012593046, 233535012593082⟩⟩, ⟨⟨-36316350199021334, -36316350199021294⟩, ⟨65571680671999378, 65571680671999416⟩⟩, ⟨⟨203018436435444166, 203018436435444182⟩, ⟨344516134557117380, 344516134557117396⟩⟩, o],
  [o],
  [⟨⟨2380183231131, 2380183231133⟩, ⟨0, 0⟩⟩, ⟨⟨-85544529538491, -85544529538486⟩, ⟨0, 0⟩⟩, ⟨⟨1441170525936199, 1441170525936210⟩, ⟨0, 0⟩⟩, ⟨⟨-15107201300985892, -15107201300985870⟩, ⟨0, 0⟩⟩, ⟨⟨110288248162680209, 110288248162680253⟩, ⟨0, 0⟩⟩, ⟨⟨-594569105410688893, -594569105410688804⟩, ⟨0, 0⟩⟩, ⟨⟨2448531131749667502, 2448531131749667678⟩, ⟨0, 0⟩⟩, ⟨⟨-7857229604416069183, -7857229604416068840⟩, ⟨0, 0⟩⟩, ⟨⟨19855636726736345213, 19855636726736345825⟩, ⟨0, 0⟩⟩, ⟨⟨-39645431166521950321, -39645431166521949394⟩, ⟨0, 0⟩⟩, ⟨⟨62338024084266318637, 62338024084266319776⟩, ⟨0, 0⟩⟩, ⟨⟨-76378907532457690182, -76378907532457689093⟩, ⟨0, 0⟩⟩, ⟨⟨71486501379298333451, 71486501379298334229⟩, ⟨0, 0⟩⟩, ⟨⟨-49408596973834856285, -49408596973834855895⟩, ⟨0, 0⟩⟩, ⟨⟨23782503985354003562, 23782503985354003683⟩, ⟨0, 0⟩⟩, ⟨⟨-7122921365532096413, -7122921365532096397⟩, ⟨0, 0⟩⟩, o],
  [o],
  [⟨⟨-1470743161255, -1470743161250⟩, ⟨1871413040294, 1871413040298⟩⟩, ⟨⟨84782453666851, 84782453666869⟩, ⟨11393071762607, 11393071762625⟩⟩, ⟨⟨-559789966069855, -559789966069807⟩, ⟨-1328008915148855, -1328008915148806⟩⟩, ⟨⟨-9014291381989679, -9014291381989554⟩, ⟨12123121793873711, 12123121793873838⟩⟩, ⟨⟨109659107552344358, 109659107552344673⟩, ⟨11763409948491717, 11763409948492030⟩⟩, ⟨⟨-245499942729369777, -245499942729369062⟩, ⟨-541518420027189427, -541518420027188709⟩⟩, ⟨⟨-1408001264994608358, -1408001264994606920⟩, ⟨2003206714475790150, 2003206714475791582⟩⟩, ⟨⟨7832006920499469458, 7832006920499471925⟩, ⟨629066493910375641, 629066493910378112⟩⟩, ⟨⟨-8678619897022286204, -8678619897022282628⟩, ⟨-17858551635200716784, -17858551635200713211⟩⟩, ⟨⟨-21923111639513783020, -21923111639513778759⟩, ⟨33032368798208299511, 33032368798208303772⟩⟩, ⟨⟨62249058602775228062, 62249058602775232191⟩, ⟨3329256643580180628, 3329256643580184749⟩⟩, ⟨⟨-35207314888386101165, -35207314888386098061⟩, ⟨-67780399041328671581, -67780399041328668468⟩⟩, ⟨⟨-37925392851384237382, -37925392851384235622⟩, ⟨60596901377220567697, 60596901377220569451⟩⟩, ⟨⟨49390965503635726686, 49390965503635727407⟩, ⟨1319841483477660108, 1319841483477660833⟩⟩, ⟨⟨-11522552818466188352, -11522552818466188176⟩, ⟨-20804765616536898883, -20804765616536898707⟩⟩, ⟨⟨-3616252385577833568, -3616252385577833552⟩, ⟨6136670714919959972, 6136670714919959988⟩⟩, o],
  [o],
  [⟨⟨-1470743161255, -1470743161250⟩, ⟨-1871413040298, -1871413040294⟩⟩, ⟨⟨-84782453666869, -84782453666851⟩, ⟨11393071762607, 11393071762625⟩⟩, ⟨⟨-559789966069855, -559789966069807⟩, ⟨1328008915148806, 1328008915148855⟩⟩, ⟨⟨9014291381989554, 9014291381989679⟩, ⟨12123121793873711, 12123121793873838⟩⟩, ⟨⟨109659107552344358, 109659107552344673⟩, ⟨-11763409948492030, -11763409948491717⟩⟩, ⟨⟨245499942729369062, 245499942729369777⟩, ⟨-541518420027189427, -541518420027188709⟩⟩, ⟨⟨-1408001264994608358, -1408001264994606920⟩, ⟨-2003206714475791582, -2003206714475790150⟩⟩, ⟨⟨-7832006920499471925, -7832006920499469458⟩, ⟨629066493910375641, 629066493910378112⟩⟩, ⟨⟨-8678619897022286204, -8678619897022282628⟩, ⟨17858551635200713211, 17858551635200716784⟩⟩, ⟨⟨21923111639513778759, 21923111639513783020⟩, ⟨33032368798208299511, 33032368798208303772⟩⟩, ⟨⟨62249058602775228062, 62249058602775232191⟩, ⟨-3329256643580184749, -3329256643580180628⟩⟩, ⟨⟨35207314888386098061, 35207314888386101165⟩, ⟨-67780399041328671581, -67780399041328668468⟩⟩, ⟨⟨-37925392851384237382, -37925392851384235622⟩, ⟨-60596901377220569451, -60596901377220567697⟩⟩, ⟨⟨-49390965503635727407, -49390965503635726686⟩, ⟨1319841483477660108, 1319841483477660833⟩⟩, ⟨⟨-11522552818466188352, -11522552818466188176⟩, ⟨20804765616536898707, 20804765616536898883⟩⟩, ⟨⟨3616252385577833552, 3616252385577833568⟩, ⟨6136670714919959972, 6136670714919959988⟩⟩, o],
  [o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, o]
]

private def st10_5 : List (List CFpIv) := [
  [o, ⟨⟨12679514247497357, 12679514247497360⟩, ⟨21516751450298547, 21516751450298548⟩⟩, ⟨⟨-623740674526415, -623740674526412⟩, ⟨-1, 1⟩⟩, ⟨⟨-7908728769402, -7908728769401⟩, ⟨-13420873063227, -13420873063226⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, o, ⟨⟨12680731560231590, 12680731560231593⟩, ⟨21518817193120276, 21518817193120277⟩⟩, ⟨⟨-623860446293584, -623860446293581⟩, ⟨-1, 1⟩⟩, ⟨⟨-7911006850496, -7911006850495⟩, ⟨-13424738897811, -13424738897810⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, o, ⟨⟨12681949106581779, 12681949106581782⟩, ⟨21520883332381202, 21520883332381203⟩⟩, ⟨⟨-623980252547895, -623980252547892⟩, ⟨-1, 1⟩⟩, ⟨⟨-7913285806325, -7913285806324⟩, ⟨-13428606216793, -13428606216792⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, o, ⟨⟨12683166886615137, 12683166886615140⟩, ⟨21522949868195387, 21522949868195388⟩⟩, ⟨⟨-624100093302584, -624100093302581⟩, ⟨-1, 1⟩⟩, ⟨⟨-7915565637309, -7915565637308⟩, ⟨-13432475020888, -13432475020887⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, o, ⟨⟨12684384900398906, 12684384900398909⟩, ⟨21525016800676934, 21525016800676935⟩⟩, ⟨⟨-624219968570894, -624219968570891⟩, ⟨-1, 1⟩⟩, ⟨⟨-7917846343869, -7917846343868⟩, ⟨-13436345310807, -13436345310806⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, o, ⟨⟨12685603148000352, 12685603148000355⟩, ⟨21527084129939994, 21527084129939995⟩⟩, ⟨⟨-624339878366072, -624339878366069⟩, ⟨-1, 1⟩⟩, ⟨⟨-7920127926423, -7920127926422⟩, ⟨-13440217087263, -13440217087262⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, o, ⟨⟨12686821629486767, 12686821629486770⟩, ⟨21529151856098758, 21529151856098759⟩⟩, ⟨⟨-624459822701375, -624459822701372⟩, ⟨-1, 1⟩⟩, ⟨⟨-7922410385394, -7922410385393⟩, ⟨-13444090350971, -13444090350970⟩⟩, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, o, ⟨⟨12688040344925469, 12688040344925472⟩, ⟨21531219979267464, 21531219979267465⟩⟩, ⟨⟨-624579801590064, -624579801590061⟩, ⟨-1, 1⟩⟩, ⟨⟨-7924693721201, -7924693721200⟩, ⟨-13447965102643, -13447965102642⟩⟩, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, o, ⟨⟨12689259294383801, 12689259294383804⟩, ⟨21533288499560391, 21533288499560392⟩⟩, ⟨⟨-624699815045407, -624699815045404⟩, ⟨-1, 1⟩⟩, ⟨⟨-7926977934265, -7926977934264⟩, ⟨-13451841342995, -13451841342994⟩⟩, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, o, ⟨⟨12690478477929133, 12690478477929136⟩, ⟨21535357417091864, 21535357417091865⟩⟩, ⟨⟨-624819863080678, -624819863080675⟩, ⟨-1, 1⟩⟩, ⟨⟨-7929263025008, -7929263025007⟩, ⟨-13455719072741, -13455719072740⟩⟩, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, o, ⟨⟨12691697895628860, 12691697895628863⟩, ⟨21537426731976250, 21537426731976251⟩⟩, ⟨⟨-624939945709157, -624939945709154⟩, ⟨-1, 1⟩⟩, ⟨⟨-7931548993852, -7931548993851⟩, ⟨-13459598292597, -13459598292596⟩⟩, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨12692917547550405, 12692917547550408⟩, ⟨21539496444327962, 21539496444327963⟩⟩, ⟨⟨-625060062944131, -625060062944128⟩, ⟨-1, 1⟩⟩, ⟨⟨-7933835841217, -7933835841216⟩, ⟨-13463479003277, -13463479003276⟩⟩, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨12694137433761213, 12694137433761216⟩, ⟨21541566554261455, 21541566554261456⟩⟩, ⟨⟨-625180214798895, -625180214798892⟩, ⟨-1, 1⟩⟩, ⟨⟨-7936123567526, -7936123567525⟩, ⟨-13467361205498, -13467361205497⟩⟩, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨12695357554328759, 12695357554328762⟩, ⟨21543637061891229, 21543637061891230⟩⟩, ⟨⟨-625300401286747, -625300401286744⟩, ⟨-1, 1⟩⟩, ⟨⟨-7938412173201, -7938412173200⟩, ⟨-13471244899977, -13471244899976⟩⟩, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨12696577909320540, 12696577909320543⟩, ⟨21545707967331828, 21545707967331829⟩⟩, ⟨⟨-625420622420994, -625420622420991⟩, ⟨-1, 1⟩⟩, ⟨⟨-7940701658664, -7940701658663⟩, ⟨-13475130087430, -13475130087429⟩⟩, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨12697798498804082, 12697798498804085⟩, ⟨21547779270697839, 21547779270697840⟩⟩, ⟨⟨-625540878214948, -625540878214945⟩, ⟨-1, 1⟩⟩, ⟨⟨-7942992024339, -7942992024338⟩, ⟨-13479016768575, -13479016768574⟩⟩, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨12699019322846936, 12699019322846939⟩, ⟨21549850972103893, 21549850972103894⟩⟩, ⟨⟨-625661168681929, -625661168681925⟩, ⟨-1, 1⟩⟩, ⟨⟨-7945283270647, -7945283270646⟩, ⟨-13482904944128, -13482904944127⟩⟩, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨12700240381516678, 12700240381516681⟩, ⟨21551923071664667, 21551923071664668⟩⟩, ⟨⟨-625781493835260, -625781493835257⟩, ⟨-1, 1⟩⟩, ⟨⟨-7947575398013, -7947575398012⟩, ⟨-13486794614809, -13486794614808⟩⟩],
  [⟨⟨0, 1⟩, ⟨0, 0⟩⟩, ⟨⟨-4, 0⟩, ⟨0, 1⟩⟩, ⟨⟨0, 7⟩, ⟨-3, 0⟩⟩, ⟨⟨-10, 0⟩, ⟨0, 5⟩⟩, ⟨⟨0, 13⟩, ⟨-7, 0⟩⟩, ⟨⟨-27, -11⟩, ⟨0, 8⟩⟩, ⟨⟨1116, 1136⟩, ⟨-20, -9⟩⟩, ⟨⟨-77386, -77362⟩, ⟨964, 977⟩⟩, ⟨⟨4278896, 4278925⟩, ⟨-66705, -66690⟩⟩, ⟨⟨-191419524, -191419491⟩, ⟨3682035, 3682053⟩⟩, ⟨⟨6945771666, 6945771705⟩, ⟨-164371880, -164371859⟩⟩, ⟨⟨-204043609892, -204043609850⟩, ⟨5949067336, 5949067360⟩⟩, ⟨⟨4820534421890, 4820534421934⟩, ⟨-174207901019, -174207900994⟩⟩, ⟨⟨-90460884519451, -90460884519402⟩, ⟨4098964630128, 4098964630155⟩⟩, ⟨⟨1321705813411022, 1321705813411075⟩, ⟨-76508386654559, -76508386654529⟩⟩, ⟨⟨-14571114690329104, -14571114690329044⟩, ⟨1109603218669977, 1109603218670009⟩⟩, ⟨⟨115245677392238960, 115245677392239035⟩, ⟨-12100753040078944, -12100753040078906⟩⟩, ⟨⟨-599249152863713236, -599249152863713162⟩, ⟨94057614288676327, 94057614288676374⟩⟩, ⟨⟨1720558399626171319, 1720558399626171362⟩, ⟨-473628322500250285, -473628322500250243⟩⟩, ⟨⟨-1719358615999460385, -1719358615999460372⟩, ⟨1258877577999055655, 1258877577999055674⟩⟩, ⟨⟨496138938356833823, 496138938356833825⟩, ⟨-868243142124459194, -868243142124459192⟩⟩],
  [o],
  [⟨⟨-5, 5⟩, ⟨-5, 5⟩⟩, ⟨⟨-14, 14⟩, ⟨-14, 14⟩⟩, ⟨⟨-27, 27⟩, ⟨-27, 27⟩⟩, ⟨⟨-37, 37⟩, ⟨-37, 37⟩⟩, ⟨⟨-48, 48⟩, ⟨-48, 48⟩⟩, ⟨⟨-39, 68⟩, ⟨-59, 48⟩⟩, ⟨⟨-951, -845⟩, ⟨-731, -624⟩⟩, ⟨⟨-8707, -8605⟩, ⟨76698, 76800⟩⟩, ⟨⟨3900217, 3900324⟩, ⟨-1736707, -1736600⟩⟩, ⟨⟨-155265652, -155265534⟩, ⟨-111073529, -111073409⟩⟩, ⟨⟨-625043919, -625043789⟩, ⟨6894990140, 6894990276⟩⟩, ⟨⟨183917032221, 183917032379⟩, ⟨-86514497483, -86514497323⟩⟩, ⟨⟨-3955393817742, -3955393817555⟩, ⟨-2715830830426, -2715830830244⟩⟩, ⟨⟨-6583586503177, -6583586502982⟩, ⟨89711724569099, 89711724569297⟩⟩, ⟨⟨1180003576366211, 1180003576366421⟩, ⟨-575291152501986, -575291152501780⟩⟩, ⟨⟨-11985677109996090, -11985677109995862⟩, ⟨-8075771625012614, -8075771625012381⟩⟩, ⟨⟨-8391417274518930, -8391417274518677⟩, ⟨113819634278550796, 113819634278551044⟩⟩, ⟨⟨537641941178298597, 537641941178298806⟩, ⟨-249713698729131370, -249713698729131164⟩⟩, ⟨⟨-1351714454084291479, -1351714454084291378⟩, ⟨-1047195539211269329, -1047195539211269229⟩⟩, ⟨⟨-600521899907433170, -600521899907433150⟩, ⟨1751999989082178957, 1751999989082178977⟩⟩, o],
  [o],
  [⟨⟨-5, 5⟩, ⟨-5, 5⟩⟩, ⟨⟨-14, 14⟩, ⟨-14, 14⟩⟩, ⟨⟨-27, 27⟩, ⟨-27, 27⟩⟩, ⟨⟨-37, 37⟩, ⟨-37, 37⟩⟩, ⟨⟨-48, 48⟩, ⟨-48, 48⟩⟩, ⟨⟨-68, 39⟩, ⟨-59, 48⟩⟩, ⟨⟨-951, -846⟩, ⟨625, 730⟩⟩, ⟨⟨8606, 8708⟩, ⟨76697, 76800⟩⟩, ⟨⟨3900217, 3900325⟩, ⟨1736601, 1736707⟩⟩, ⟨⟨155265535, 155265653⟩, ⟨-111073528, -111073409⟩⟩, ⟨⟨-625043920, -625043788⟩, ⟨-6894990275, -6894990141⟩⟩, ⟨⟨-183917032379, -183917032220⟩, ⟨-86514497484, -86514497324⟩⟩, ⟨⟨-3955393817741, -3955393817556⟩, ⟨2715830830243, 2715830830426⟩⟩, ⟨⟨6583586502983, 6583586503176⟩, ⟨89711724569100, 89711724569299⟩⟩, ⟨⟨1180003576366210, 1180003576366420⟩, ⟨575291152501781, 575291152501986⟩⟩, ⟨⟨11985677109995862, 11985677109996091⟩, ⟨-8075771625012613, -8075771625012383⟩⟩, ⟨⟨-8391417274518930, -8391417274518677⟩, ⟨-113819634278551044, -113819634278550796⟩⟩, ⟨⟨-537641941178298806, -537641941178298596⟩, ⟨-249713698729131370, -249713698729131164⟩⟩, ⟨⟨-1351714454084291480, -1351714454084291378⟩, ⟨1047195539211269228, 1047195539211269330⟩⟩, ⟨⟨600521899907433150, 600521899907433170⟩, ⟨1751999989082178957, 1751999989082178977⟩⟩, o],
  [o],
  [⟨⟨443571801852, 443571801856⟩, ⟨0, 0⟩⟩, ⟨⟨-18849132702942, -18849132702930⟩, ⟨0, 0⟩⟩, ⟨⟨379874333418535, 379874333418560⟩, ⟨0, 0⟩⟩, ⟨⟨-4827322054565229, -4827322054565180⟩, ⟨0, 0⟩⟩, ⟨⟨43377033186281230, 43377033186281325⟩, ⟨0, 0⟩⟩, ⟨⟨-292940936307347248, -292940936307347067⟩, ⟨0, 0⟩⟩, ⟨⟨1542581552798221058, 1542581552798221415⟩, ⟨0, 0⟩⟩, ⟨⟨-6485029785231638912, -6485029785231638192⟩, ⟨0, 0⟩⟩, ⟨⟨22102846589148989433, 22102846589148990869⟩, ⟨0, 0⟩⟩, ⟨⟨-61667563632031128869, -61667563632031126129⟩, ⟨0, 0⟩⟩, ⟨⟨141591877704598236711, 141591877704598241470⟩, ⟨0, 0⟩⟩, ⟨⟨-267965555622966948070, -267965555622966940868⟩, ⟨0, 0⟩⟩, ⟨⟨417192052100693537643, 417192052100693546839⟩, ⟨0, 0⟩⟩, ⟨⟨-531313236169456207127, -531313236169456197455⟩, ⟨0, 0⟩⟩, ⟨⟨547975577204588572292, 547975577204588580478⟩, ⟨0, 0⟩⟩, ⟨⟨-450530640801069551934, -450530640801069546511⟩, ⟨0, 0⟩⟩, ⟨⟨288282602427321969002, 288282602427321971704⟩, ⟨0, 0⟩⟩, ⟨⟨-138318410889989654514, -138318410889989653565⟩, ⟨0, 0⟩⟩, ⟨⟨46799036620385005841, 46799036620385006048⟩, ⟨0, 0⟩⟩, ⟨⟨-9952107518851923752, -9952107518851923732⟩, ⟨0, 0⟩⟩, o],
  [o],
  [⟨⟨-150929236925, -150929236911⟩, ⟨-417166856093, -417166856078⟩⟩, ⟨⟨-12016586978915, -12016586978860⟩, ⟨14524413758135, 14524413758187⟩⟩, ⟨⟨375120248133266, 375120248133413⟩, ⟨60047470836071, 60047470836218⟩⟩, ⟨⟨-1762439399941756, -1762439399941372⟩, ⟨-4494187639345768, -4494187639345384⟩⟩, ⟨⟨-26752426630029977, -26752426630029006⟩, ⟨34143846579618969, 34143846579619939⟩⟩, ⟨⟨290369781267755951, 290369781267758320⟩, ⟨38600125761819954, 38600125761822326⟩⟩, ⟨⟨-601063967767403645, -601063967767398191⟩, ⟨-1420503183446438022, -1420503183446432569⟩⟩, ⟨⟨-3862230565026923774, -3862230565026912387⟩, ⟨5208428702946834183, 5208428702946845575⟩⟩, ⟨⟨21976005917795058146, 21976005917795079218⟩, ⟨2329765968994136347, 2329765968994157414⟩⟩, ⟨⟨-25523781811650396827, -25523781811650362850⟩, ⟨-56123949686851119076, -56123949686851085090⟩⟩, ⟨⟨-81273785509960577449, -81273785509960530278⟩, ⟨115903084160888444719, 115903084160888491878⟩⟩, ⟨⟨267057839826757281357, 267057839826757337042⟩, ⟨21173240742436114988, 21173240742436170682⟩⟩, ⟨⟨-182652653676046166385, -182652653676046111225⟩, ⟨-374951411318955075145, -374951411318955019990⟩⟩, ⟨⟨-293336325071878196771, -293336325071878151637⟩, ⟨442806654945079791278, 442806654945079836422⟩⟩, ⟨⟨547045942371050984094, 547045942371051014110⟩, ⟨28838065228314939454, 28838065228314969452⟩⟩, ⟨⟨-207875041777549623531, -207875041777549607891⟩, ⟨-399550003737166843539, -399550003737166827884⟩⟩, ⟨⟨-152761502967756076959, -152761502967756070776⟩, ⟨244380283238500785700, 244380283238500791876⟩⟩, ⟨⟨138234211167719630532, 138234211167719632284⟩, ⟨3634469184450602185, 3634469184450603940⟩⟩, ⟨⟨-22681487958710426341, -22681487958710426045⟩, ⟨-40924150288622887640, -40924150288622887342⟩⟩, ⟨⟨-5050646380887559579, -5050646380887559559⟩, ⟨8573847252710077125, 8573847252710077145⟩⟩, o],
  [o],
  [⟨⟨-150929236927, -150929236910⟩, ⟨417166856077, 417166856093⟩⟩, ⟨⟨12016586978859, 12016586978915⟩, ⟨14524413758133, 14524413758188⟩⟩, ⟨⟨375120248133264, 375120248133413⟩, ⟨-60047470836219, -60047470836071⟩⟩, ⟨⟨1762439399941372, 1762439399941756⟩, ⟨-4494187639345767, -4494187639345384⟩⟩, ⟨⟨-26752426630029977, -26752426630029006⟩, ⟨-34143846579619939, -34143846579618970⟩⟩, ⟨⟨-290369781267758321, -290369781267755952⟩, ⟨38600125761819954, 38600125761822325⟩⟩, ⟨⟨-601063967767403645, -601063967767398191⟩, ⟨1420503183446432571, 1420503183446438022⟩⟩, ⟨⟨3862230565026912388, 3862230565026923774⟩, ⟨5208428702946834184, 5208428702946845575⟩⟩, ⟨⟨21976005917795058146, 21976005917795079219⟩, ⟨-2329765968994157414, -2329765968994136349⟩⟩, ⟨⟨25523781811650362850, 25523781811650396826⟩, ⟨-56123949686851119075, -56123949686851085090⟩⟩, ⟨⟨-81273785509960577449, -81273785509960530277⟩, ⟨-115903084160888491878, -115903084160888444717⟩⟩, ⟨⟨-267057839826757337037, -267057839826757281360⟩, ⟨21173240742436114993, 21173240742436170678⟩⟩, ⟨⟨-182652653676046166385, -182652653676046111227⟩, ⟨374951411318955019991, 374951411318955075145⟩⟩, ⟨⟨293336325071878151635, 293336325071878196773⟩, ⟨442806654945079791276, 442806654945079836423⟩⟩, ⟨⟨547045942371050984099, 547045942371051014105⟩, ⟨-28838065228314969447, -28838065228314939457⟩⟩, ⟨⟨207875041777549607892, 207875041777549623530⟩, ⟨-399550003737166843539, -399550003737166827884⟩⟩, ⟨⟨-152761502967756076960, -152761502967756070773⟩, ⟨-244380283238500791875, -244380283238500785701⟩⟩, ⟨⟨-138234211167719632283, -138234211167719630532⟩, ⟨3634469184450602185, 3634469184450603940⟩⟩, ⟨⟨-22681487958710426341, -22681487958710426045⟩, ⟨40924150288622887342, 40924150288622887641⟩⟩, ⟨⟨5050646380887559559, 5050646380887559579⟩, ⟨8573847252710077125, 8573847252710077145⟩⟩, o],
  [o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨-261892618380512129, -261892618380512127⟩, ⟨0, 0⟩⟩, ⟨⟨-1, 1⟩, ⟨0, 0⟩⟩, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨-261077268416932731, -261077268416932729⟩, ⟨0, 0⟩⟩, ⟨⟨-1, 1⟩, ⟨0, 0⟩⟩, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨-260265197579834293, -260265197579834291⟩, ⟨0, 0⟩⟩, ⟨⟨-1, 1⟩, ⟨0, 0⟩⟩, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨-259456390992240316, -259456390992240314⟩, ⟨0, 0⟩⟩, ⟨⟨-1, 1⟩, ⟨0, 0⟩⟩, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨-258650833844997572, -258650833844997570⟩, ⟨0, 0⟩⟩, ⟨⟨-1, 1⟩, ⟨0, 0⟩⟩, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨-257848511396522192, -257848511396522190⟩, ⟨0, 0⟩⟩, ⟨⟨-1, 1⟩, ⟨0, 0⟩⟩, o]
]

private def st10_6 : List (List CFpIv) := [
  [o, ⟨⟨444975186414953243, 444975186414953250⟩, ⟨-2, 2⟩⟩, ⟨⟨-19339651683549, -19339651683534⟩, ⟨-6, 6⟩⟩, ⟨⟨-8605665113091, -8605665113077⟩, ⟨-7, 7⟩⟩, ⟨⟨12062927380, 12062927393⟩, ⟨-6, 7⟩⟩, ⟨⟨5367703358, 5367703367⟩, ⟨-4, 5⟩⟩, ⟨⟨-242667826, -242667822⟩, ⟨-2, 2⟩⟩, ⟨⟨-107981161, -107981159⟩, ⟨-1, 1⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, o, ⟨⟨445002826224423228, 445002826224423235⟩, ⟨-2, 2⟩⟩, ⟨⟨-19343365317040, -19343365317025⟩, ⟨-6, 6⟩⟩, ⟨⟨-8607852234779, -8607852234763⟩, ⟨-8, 7⟩⟩, ⟨⟨12067560512, 12067560527⟩, ⟨-7, 7⟩⟩, ⟨⟨5370098532, 5370098541⟩, ⟨-4, 5⟩⟩, ⟨⟨-242807646, -242807642⟩, ⟨-2, 2⟩⟩, ⟨⟨-108050089, -108050087⟩, ⟨-1, 1⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, o, ⟨⟨445030468900153046, 445030468900153053⟩, ⟨-2, 2⟩⟩, ⟨⟨-19347080019835, -19347080019820⟩, ⟨-6, 6⟩⟩, ⟨⟨-8610040093080, -8610040093066⟩, ⟨-9, 9⟩⟩, ⟨⟨12072195870, 12072195883⟩, ⟨-8, 7⟩⟩, ⟨⟨5372494986, 5372494997⟩, ⟨-5, 4⟩⟩, ⟨⟨-242947560, -242947554⟩, ⟨-2, 2⟩⟩, ⟨⟨-108119066, -108119064⟩, ⟨-1, 1⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, o, ⟨⟨445058114442500258, 445058114442500265⟩, ⟨-2, 2⟩⟩, ⟨⟨-19350795792348, -19350795792333⟩, ⟨-6, 6⟩⟩, ⟨⟨-8612228688308, -8612228688294⟩, ⟨-7, 7⟩⟩, ⟨⟨12076833452, 12076833465⟩, ⟨-6, 7⟩⟩, ⟨⟨5374892723, 5374892732⟩, ⟨-4, 5⟩⟩, ⟨⟨-243087567, -243087563⟩, ⟨-2, 2⟩⟩, ⟨⟨-108188094, -108188092⟩, ⟨-1, 1⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, o, ⟨⟨445085762851822465, 445085762851822472⟩, ⟨-2, 2⟩⟩, ⟨⟨-19354512634986, -19354512634971⟩, ⟨-6, 6⟩⟩, ⟨⟨-8614418020772, -8614418020758⟩, ⟨-7, 7⟩⟩, ⟨⟨12081473262, 12081473275⟩, ⟨-7, 6⟩⟩, ⟨⟨5377291742, 5377291751⟩, ⟨-5, 4⟩⟩, ⟨⟨-243227668, -243227664⟩, ⟨-2, 2⟩⟩, ⟨⟨-108257172, -108257170⟩, ⟨-1, 1⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, o, ⟨⟨445113414128477310, 445113414128477317⟩, ⟨-2, 2⟩⟩, ⟨⟨-19358230548162, -19358230548147⟩, ⟨-6, 6⟩⟩, ⟨⟨-8616608090782, -8616608090768⟩, ⟨-7, 7⟩⟩, ⟨⟨12086115298, 12086115312⟩, ⟨-8, 6⟩⟩, ⟨⟨5379692042, 5379692052⟩, ⟨-5, 4⟩⟩, ⟨⟨-243367864, -243367860⟩, ⟨-2, 2⟩⟩, ⟨⟨-108326301, -108326299⟩, ⟨-1, 1⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, o, ⟨⟨445141068272822477, 445141068272822484⟩, ⟨-2, 2⟩⟩, ⟨⟨-19361949532287, -19361949532272⟩, ⟨-6, 6⟩⟩, ⟨⟨-8618798898650, -8618798898636⟩, ⟨-7, 7⟩⟩, ⟨⟨12090759566, 12090759579⟩, ⟨-7, 7⟩⟩, ⟨⟨5382093628, 5382093637⟩, ⟨-6, 5⟩⟩, ⟨⟨-243508154, -243508150⟩, ⟨-4, 2⟩⟩, ⟨⟨-108395480, -108395478⟩, ⟨-1, 1⟩⟩, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, o, ⟨⟨445168725285215691, 445168725285215698⟩, ⟨-2, 2⟩⟩, ⟨⟨-19365669587770, -19365669587755⟩, ⟨-6, 7⟩⟩, ⟨⟨-8620990444686, -8620990444672⟩, ⟨-7, 7⟩⟩, ⟨⟨12095406062, 12095406075⟩, ⟨-7, 7⟩⟩, ⟨⟨5384496496, 5384496507⟩, ⟨-5, 5⟩⟩, ⟨⟨-243648539, -243648533⟩, ⟨-2, 2⟩⟩, ⟨⟨-108464709, -108464707⟩, ⟨-1, 1⟩⟩, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, o, ⟨⟨445196385166014717, 445196385166014724⟩, ⟨-2, 2⟩⟩, ⟨⟨-19369390715025, -19369390715010⟩, ⟨-6, 6⟩⟩, ⟨⟨-8623182729201, -8623182729187⟩, ⟨-9, 8⟩⟩, ⟨⟨12100054790, 12100054803⟩, ⟨-7, 8⟩⟩, ⟨⟨5386900651, 5386900660⟩, ⟨-4, 5⟩⟩, ⟨⟨-243789017, -243789013⟩, ⟨-2, 2⟩⟩, ⟨⟨-108533989, -108533987⟩, ⟨-1, 1⟩⟩, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, o, ⟨⟨445224047915577363, 445224047915577370⟩, ⟨-2, 2⟩⟩, ⟨⟨-19373112914462, -19373112914447⟩, ⟨-6, 6⟩⟩, ⟨⟨-8625375752506, -8625375752492⟩, ⟨-7, 7⟩⟩, ⟨⟨12104705752, 12104705765⟩, ⟨-7, 6⟩⟩, ⟨⟨5389306092, 5389306101⟩, ⟨-5, 4⟩⟩, ⟨⟨-243929590, -243929586⟩, ⟨-2, 2⟩⟩, ⟨⟨-108603320, -108603318⟩, ⟨-1, 1⟩⟩, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, o, ⟨⟨445251713534261478, 445251713534261485⟩, ⟨-2, 2⟩⟩, ⟨⟨-19376836186493, -19376836186478⟩, ⟨-6, 6⟩⟩, ⟨⟨-8627569514913, -8627569514897⟩, ⟨-8, 9⟩⟩, ⟨⟨12109358947, 12109358962⟩, ⟨-7, 8⟩⟩, ⟨⟨5391712820, 5391712830⟩, ⟨-4, 5⟩⟩, ⟨⟨-244070258, -244070253⟩, ⟨-2, 2⟩⟩, ⟨⟨-108672701, -108672699⟩, ⟨-1, 1⟩⟩, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨445279382022424950, 445279382022424957⟩, ⟨-2, 2⟩⟩, ⟨⟨-19380560531531, -19380560531515⟩, ⟨-7, 8⟩⟩, ⟨⟨-8629764016732, -8629764016718⟩, ⟨-7, 8⟩⟩, ⟨⟨12114014379, 12114014392⟩, ⟨-7, 6⟩⟩, ⟨⟨5394120835, 5394120844⟩, ⟨-5, 4⟩⟩, ⟨⟨-244211020, -244211016⟩, ⟨-2, 2⟩⟩, ⟨⟨-108742132, -108742130⟩, ⟨-1, 1⟩⟩, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨445307053380425711, 445307053380425718⟩, ⟨-2, 2⟩⟩, ⟨⟨-19384285949985, -19384285949970⟩, ⟨-6, 6⟩⟩, ⟨⟨-8631959258275, -8631959258260⟩, ⟨-8, 8⟩⟩, ⟨⟨12118672047, 12118672061⟩, ⟨-8, 7⟩⟩, ⟨⟨5396530139, 5396530149⟩, ⟨-5, 4⟩⟩, ⟨⟨-244351877, -244351872⟩, ⟨-2, 2⟩⟩, ⟨⟨-108811614, -108811612⟩, ⟨-1, 1⟩⟩, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨445334727608621733, 445334727608621740⟩, ⟨-2, 2⟩⟩, ⟨⟨-19388012442271, -19388012442256⟩, ⟨-6, 6⟩⟩, ⟨⟨-8634155239855, -8634155239841⟩, ⟨-8, 7⟩⟩, ⟨⟨12123331954, 12123331967⟩, ⟨-7, 7⟩⟩, ⟨⟨5398940732, 5398940741⟩, ⟨-5, 6⟩⟩, ⟨⟨-244492829, -244492825⟩, ⟨-3, 3⟩⟩, ⟨⟨-108881147, -108881146⟩, ⟨-1, 1⟩⟩, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨445362404707371028, 445362404707371035⟩, ⟨-2, 2⟩⟩, ⟨⟨-19391740008800, -19391740008785⟩, ⟨-6, 6⟩⟩, ⟨⟨-8636351961783, -8636351961769⟩, ⟨-7, 7⟩⟩, ⟨⟨12127994099, 12127994112⟩, ⟨-6, 7⟩⟩, ⟨⟨5401352615, 5401352624⟩, ⟨-4, 5⟩⟩, ⟨⟨-244633875, -244633871⟩, ⟨-2, 2⟩⟩, ⟨⟨-108950731, -108950729⟩, ⟨-1, 1⟩⟩, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨445390084677031651, 445390084677031658⟩, ⟨-2, 2⟩⟩, ⟨⟨-19395468649986, -19395468649971⟩, ⟨-6, 6⟩⟩, ⟨⟨-8638549424372, -8638549424358⟩, ⟨-7, 7⟩⟩, ⟨⟨12132658486, 12132658499⟩, ⟨-6, 7⟩⟩, ⟨⟨5403765789, 5403765798⟩, ⟨-5, 5⟩⟩, ⟨⟨-244775018, -244775014⟩, ⟨-3, 2⟩⟩, ⟨⟨-109020366, -109020364⟩, ⟨-1, 1⟩⟩, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨445417767517961698, 445417767517961705⟩, ⟨-2, 2⟩⟩, ⟨⟨-19399198366239, -19399198366223⟩, ⟨-6, 6⟩⟩, ⟨⟨-8640747627933, -8640747627918⟩, ⟨-7, 7⟩⟩, ⟨⟨12137325113, 12137325128⟩, ⟨-7, 6⟩⟩, ⟨⟨5406180254, 5406180264⟩, ⟨-5, 4⟩⟩, ⟨⟨-244916254, -244916250⟩, ⟨-2, 2⟩⟩, ⟨⟨-109090051, -109090049⟩, ⟨-1, 1⟩⟩, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨445445453230519304, 445445453230519311⟩, ⟨-2, 2⟩⟩, ⟨⟨-19402929157976, -19402929157961⟩, ⟨-6, 6⟩⟩, ⟨⟨-8642946572778, -8642946572764⟩, ⟨-7, 7⟩⟩, ⟨⟨12141993986, 12141994000⟩, ⟨-6, 7⟩⟩, ⟨⟨5408596013, 5408596022⟩, ⟨-4, 5⟩⟩, ⟨⟨-245057586, -245057581⟩, ⟨-2, 2⟩⟩, ⟨⟨-109159788, -109159785⟩, ⟨-1, 1⟩⟩],
  [⟨⟨0, 1⟩, ⟨0, 0⟩⟩, ⟨⟨-7, 1⟩, ⟨-2, 2⟩⟩, ⟨⟨-9, 23⟩, ⟨-11, 12⟩⟩, ⟨⟨-49, 29⟩, ⟨-33, 33⟩⟩, ⟨⟨-57, 82⟩, ⟨-64, 62⟩⟩, ⟨⟨-127, 79⟩, ⟨-95, 96⟩⟩, ⟨⟨1004, 1279⟩, ⟨-129, 130⟩⟩, ⟨⟨-78966, -78616⟩, ⟨-164, 163⟩⟩, ⟨⟨4377038, 4377468⟩, ⟨-201, 202⟩⟩, ⟨⟨-196865569, -196865053⟩, ⟨-242, 243⟩⟩, ⟨⟨7189734221, 7189734828⟩, ⟨-286, 284⟩⟩, ⟨⟨-212910724571, -212910723867⟩, ⟨-330, 331⟩⟩, ⟨⟨5081547310521, 5081547311320⟩, ⟨-377, 379⟩⟩, ⟨⟨-96642712610538, -96642712609651⟩, ⟨-420, 419⟩⟩, ⟨⟨1438078274204177, 1438078274205141⟩, ⟨-454, 455⟩⟩, ⟨⟨-16278376175920737, -16278376175919699⟩, ⟨-490, 490⟩⟩, ⟨⟨134170887828258705, 134170887828259848⟩, ⟨-534, 534⟩⟩, ⟨⟨-750078252865469035, -750078252865467753⟩, ⟨-601, 603⟩⟩, ⟨⟨2513349598838779969, 2513349598838781383⟩, ⟨-687, 688⟩⟩, ⟨⟨-4024600951322305185, -4024600951322303764⟩, ⟨-712, 714⟩⟩, ⟨⟨2661472725472655955, 2661472725472657137⟩, ⟨-594, 594⟩⟩, ⟨⟨1186032138413796050, 1186032138413796803⟩, ⟨-372, 371⟩⟩, ⟨⟨-3781871784501823895, -3781871784501823546⟩, ⟨-170, 169⟩⟩, ⟨⟨3044299646203542797, 3044299646203542910⟩, ⟨-54, 55⟩⟩, ⟨⟨-967841943086869052, -967841943086869031⟩, ⟨-9, 11⟩⟩],
  [o],
  [⟨⟨-5, 5⟩, ⟨-5, 5⟩⟩, ⟨⟨-38, 38⟩, ⟨-38, 38⟩⟩, ⟨⟨-130, 130⟩, ⟨-130, 130⟩⟩, ⟨⟨-291, 291⟩, ⟨-291, 291⟩⟩, ⟨⟨-492, 492⟩, ⟨-492, 492⟩⟩, ⟨⟨-679, 708⟩, ⟨-699, 688⟩⟩, ⟨⟨-1779, -53⟩, ⟨-1567, 162⟩⟩, ⟨⟨-10454, -8511⟩, ⟨77866, 79810⟩⟩, ⟨⟨4051781, 4053797⟩, ⟨-1761922, -1759905⟩⟩, ⟨⟨-160700253, -160698220⟩, ⟨-117693938, -117691904⟩⟩, ⟨⟨-758513089, -758510980⟩, ⟨7255471523, 7255473637⟩⟩, ⟨⟨197712351653, 197712353954⟩, ⟨-88931732117, -88931729814⟩⟩, ⟨⟨-4221952272790, -4221952270175⟩, ⟨-3032029902207, -3032029899605⟩⟩, ⟨⟨-9909765493204, -9909765490198⟩, ⟨98968143676839, 98968143679841⟩⟩, ⟨⟨1363293131906342, 1363293131909741⟩, ⟨-608292252551098, -608292252547693⟩⟩, ⟨⟨-13755900548065572, -13755900548061844⟩, ⟨-10187448067822740, -10187448067819011⟩⟩, ⟨⟨-19285934565812557, -19285934565808529⟩, ⟨142796295259028972, 142796295259033000⟩⟩, ⟨⟨787656220045555506, 787656220045559819⟩, ⟨-285650140752604026, -285650140752599722⟩⟩, ⟨⟨-2163322534232530391, -2163322534232526104⟩, ⟨-2180153536308112030, -2180153536308107743⟩⟩, ⟨⟨-2939012083387455420, -2939012083387451850⟩, ⟨5742544989382752507, 5742544989382756085⟩⟩, ⟨⟨8675567137024246289, 8675567137024248548⟩, ⟨2235078262419012673, 2235078262419014934⟩⟩, ⟨⟨868627274192171980, 868627274192172985⟩, ⟨-9121839996558058031, -9121839996558057031⟩⟩, ⟨⟨-7047141691644144377, -7047141691644144090⟩, ⟨460585964182158299, 460585964182158586⟩⟩, ⟨⟨1034301693318748433, 1034301693318748477⟩, ⟨3540645753931485808, 3540645753931485859⟩⟩, ⟨⟨815016461585945546, 815016461585945552⟩, ⟨-523307705553447147, -523307705553447140⟩⟩],
  [o],
  [⟨⟨-5, 5⟩, ⟨-5, 5⟩⟩, ⟨⟨-38, 38⟩, ⟨-38, 38⟩⟩, ⟨⟨-128, 128⟩, ⟨-128, 128⟩⟩, ⟨⟨-284, 284⟩, ⟨-284, 284⟩⟩, ⟨⟨-484, 484⟩, ⟨-484, 484⟩⟩, ⟨⟨-682, 693⟩, ⟨-702, 673⟩⟩, ⟨⟨-1550, 169⟩, ⟨-1804, -85⟩⟩, ⟨⟨-81149, -79216⟩, ⟨6711, 8644⟩⟩, ⟨⟨-1915881, -1913879⟩, ⟨4068235, 4070238⟩⟩, ⟨⟨114124954, 114126976⟩, ⟨168556322, 168558345⟩⟩, ⟨⟨7479460480, 7479462585⟩, ⟨-439568722, -439566619⟩⟩, ⟨⟨103192364231, 103192366526⟩, ⟨-198853418675, -198853416378⟩⟩, ⟨⟨-2845610323891, -2845610321290⟩, ⟨-4605376520915, -4605376518306⟩⟩, ⟨⟨-104640270301747, -104640270298743⟩, ⟨1362583232304, 1362583235306⟩⟩, ⟨⟨-805190597612707, -805190597609309⟩, ⟨1373853164464487, 1373853164467882⟩⟩, ⟨⟨8816059520692199, 8816059520695912⟩, ⟨16398698637049316, 16398698637053036⟩⟩, ⟨⟨161083694776379797, 161083694776383807⟩, ⟨9883244916355236, 9883244916359247⟩⟩, ⟨⟨578907203438977828, 578907203438982119⟩, ⟨-795884164069673445, -795884164069669151⟩⟩, ⟨⟨-1341469715125500516, -1341469715125496234⟩, ⟨-3685731576406084029, -3685731576406079747⟩⟩, ⟨⟨-9094185824155236671, -9094185824155233082⟩, ⟨-2697283355098740387, -2697283355098736810⟩⟩, ⟨⟨-11928225070291702641, -11928225070291700371⟩, ⟨8780466900498662400, 8780466900498664669⟩⟩, ⟨⟨-273867541465232058, -273867541465231060⟩, ⟨15516645497909759153, 15516645497909760154⟩⟩, ⟨⟨8430700190408407672, 8430700190408407951⟩, ⟨6794514150299401674, 6794514150299401953⟩⟩, ⟨⟨4563188683633352891, 4563188683633352933⟩, ⟨-992448988413870386, -992448988413870343⟩⟩, ⟨⟨461472972971469327, 461472972971469332⟩, ⟨-853073113797876057, -853073113797876052⟩⟩],
  [o],
  [⟨⟨391436540786, 391436540797⟩, ⟨-3, 4⟩⟩, ⟨⟨-18248027273500, -18248027273455⟩, ⟨-10, 8⟩⟩, ⟨⟨406322850705366, 406322850705479⟩, ⟨-13, 16⟩⟩, ⟨⟨-5750311883331528, -5750311883331286⟩, ⟨-21, 20⟩⟩, ⟨⟨58059783056871393, 58059783056871872⟩, ⟨-31, 34⟩⟩, ⟨⟨-445049613020071686, -445049613020070767⟩, ⟨-55, 55⟩⟩, ⟨⟨2690741933230086669, 2690741933230088431⟩, ⟨-101, 100⟩⟩, ⟨⟨-13159321361640318279, -13159321361640314830⟩, ⟨-199, 200⟩⟩, ⟨⟨52971241050981297160, 52971241050981304073⟩, ⟨-431, 432⟩⟩, ⟨⟨-177647335445030712406, -177647335445030698504⟩, ⟨-957, 954⟩⟩, ⟨⟨500512190717546342228, 500512190717546369287⟩, ⟨-2024, 2029⟩⟩, ⟨⟨-1191149774569881468607, -1191149774569881419548⟩, ⟨-3918, 3914⟩⟩, ⟨⟨2401720441111019475961, 2401720441111019556043⟩, ⟨-6662, 6665⟩⟩, ⟨⟨-4106350568449466680666, -4106350568449466565951⟩, ⟨-9785, 9784⟩⟩, ⟨⟨5946214187844758811572, 5946214187844758953128⟩, ⟨-12231, 12232⟩⟩, ⟨⟨-7267995223942499025099, -7267995223942498876795⟩, ⟨-12878, 12876⟩⟩, ⟨⟨7455356837078658369963, 7455356837078658500098⟩, ⟨-11284, 11287⟩⟩, ⟨⟨-6362486649044191244057, -6362486649044191149864⟩, ⟨-8122, 8121⟩⟩, ⟨⟨4461453818102233826463, 4461453818102233881616⟩, ⟨-4714, 4712⟩⟩, ⟨⟨-2525376430844802678709, -2525376430844802653279⟩, ⟨-2150, 2151⟩⟩, ⟨⟨1124785059090937021303, 1124785059090937030174⟩, ⟨-746, 744⟩⟩, ⟨⟨-379306952240530025495, -379306952240530023298⟩, ⟨-186, 187⟩⟩, ⟨⟨90986375966586346913, 90986375966586347256⟩, ⟨-32, 30⟩⟩, ⟨⟨-13826285322323193092, -13826285322323193068⟩, ⟨-2, 2⟩⟩, o],
  [o],
  [⟨⟨382536020159, 382536020216⟩, ⟨83006059373, 83006059431⟩⟩, ⟨⟨-5719906333819, -5719906333489⟩, ⟨-17328450096957, -17328450096629⟩⟩, ⟨⟨-267760701462244, -267760701461098⟩, ⟨305619232312372, 305619232313519⟩⟩, ⟨⟨5650106728498068, 5650106728501319⟩, ⟨1068850290876078, 1068850290879326⟩⟩, ⟨⟨-19665051786928939, -19665051786920453⟩, ⟨-54628043939998977, -54628043939990486⟩⟩, ⟨⟨-284234837546680892, -284234837546659549⟩, ⟨342460573299811276, 342460573299832616⟩⟩, ⟨⟨2656259684526612843, 2656259684526664373⟩, ⟨429353553374757689, 429353553374809218⟩⟩, ⟨⟨-4786193357353312917, -4786193357353195994⟩, ⟨-12258016641314836208, -12258016641314719286⟩⟩, ⟨⟨-32729735859935689320, -32729735859935446146⟩, ⟨41649647121996116307, 41649647121996359476⟩⟩, ⟨⟨176064763082250258885, 176064763082250713637⟩, ⟨23652679253165822587, 23652679253166277343⟩⟩, ⟨⟨-194428386241907932539, -194428386241907177767⟩, ⟨-461201714953486362790, -461201714953485608029⟩⟩, ⟨⟨-710706958384683108423, -710706958384682007162⟩, ⟨955883814335374307994, 955883814335375409274⟩⟩, ⟨⟨2388010000304474701125, 2388010000304476103223⟩, ⟨256088320063868870631, 256088320063870272703⟩⟩, ⟨⟨-1695629804342976380791, -1695629804342974835369⟩, ⟨-3739876343650699712512, -3739876343650698167060⟩⟩, ⟨⟨-3419136288670001498457, -3419136288670000035322⟩, ⟨4864806934598246457034, 4864806934598247920140⟩⟩, ⟨⟨7244612699848372224032, 7244612699848373404324⟩, ⟨581694616354188781552, 581694616354189961869⟩⟩, ⟨⟨-3258761829791348466889, -3258761829791347666607⟩, ⟨-6705353787544754721471, -6705353787544753921220⟩⟩, ⟨⟨-3518177938605551448338, -3518177938605550998664⟩, ⟨5301216526750234347431, 5301216526750234797148⟩⟩, ⟨⟨4455050160920365398773, 4455050160920365605322⟩, ⟨238184777439120548674, 238184777439120755181⟩⟩, ⟨⟨-1164113160796563974702, -1164113160796563900029⟩, ⟨-2241039024630183854240, -2241039024630183779542⟩⟩, ⟨⟨-596709701022726646085, -596709701022726625663⟩, ⟨953445927158431998134, 953445927158432018547⟩⟩, ⟨⟨379169194053144718947, 379169194053144722976⟩, ⟨10128476839525448385, 10128476839525452416⟩⟩, ⟨⟨-44082956291068197464, -44082956291068196983⟩, ⟨-79593542057011475314, -79593542057011474831⟩⟩, ⟨⟨-7019437836125367971, -7019437836125367947⟩, ⟨11911868279923129152, 11911868279923129176⟩⟩, o],
  [o],
  [⟨⟨382536020155, 382536020220⟩, ⟨-83006059434, -83006059368⟩⟩, ⟨⟨5719906333475, 5719906333839⟩, ⟨-17328450096972, -17328450096610⟩⟩, ⟨⟨-267760701462265, -267760701461065⟩, ⟨-305619232313541, -305619232312341⟩⟩, ⟨⟨-5650106728501326, -5650106728498032⟩, ⟨1068850290876055, 1068850290879350⟩⟩, ⟨⟨-19665051786928939, -19665051786920433⟩, ⟨54628043939990467, 54628043939998972⟩⟩, ⟨⟨284234837546659550, 284234837546680884⟩, ⟨342460573299811272, 342460573299832605⟩⟩, ⟨⟨2656259684526612856, 2656259684526664368⟩, ⟨-429353553374809206, -429353553374757697⟩⟩, ⟨⟨4786193357353196015, 4786193357353312914⟩, ⟨-12258016641314836207, -12258016641314719305⟩⟩, ⟨⟨-32729735859935689314, -32729735859935446165⟩, ⟨-41649647121996359475, -41649647121996116332⟩⟩, ⟨⟨-176064763082250713637, -176064763082250258905⟩, ⟨23652679253165822598, 23652679253166277341⟩⟩, ⟨⟨-194428386241907932525, -194428386241907177769⟩, ⟨461201714953485608046, 461201714953486362785⟩⟩, ⟨⟨710706958384682007186, 710706958384683108400⟩, ⟨955883814335374308006, 955883814335375409243⟩⟩, ⟨⟨2388010000304474701128, 2388010000304476103199⟩, ⟨-256088320063870272688, -256088320063868870645⟩⟩, ⟨⟨1695629804342974835413, 1695629804342976380741⟩, ⟨-3739876343650699712458, -3739876343650698167098⟩⟩, ⟨⟨-3419136288670001498385, -3419136288670000035387⟩, ⟨-4864806934598247920071, -4864806934598246457102⟩⟩, ⟨⟨-7244612699848373404319, -7244612699848372224039⟩, ⟨581694616354188781552, 581694616354189961857⟩⟩, ⟨⟨-3258761829791348466856, -3258761829791347666653⟩, ⟨6705353787544753921255, 6705353787544754721427⟩⟩, ⟨⟨3518177938605550998699, 3518177938605551448285⟩, ⟨5301216526750234347475, 5301216526750234797108⟩⟩, ⟨⟨4455050160920365398765, 4455050160920365605322⟩, ⟨-238184777439120755176, -238184777439120548670⟩⟩, ⟨⟨1164113160796563900031, 1164113160796563974699⟩, ⟨-2241039024630183854241, -2241039024630183779536⟩⟩, ⟨⟨-596709701022726646086, -596709701022726625663⟩, ⟨-953445927158432018541, -953445927158431998136⟩⟩, ⟨⟨-379169194053144722973, -379169194053144718948⟩, ⟨10128476839525448388, 10128476839525452415⟩⟩, ⟨⟨-44082956291068197464, -44082956291068196983⟩, ⟨79593542057011474831, 79593542057011475313⟩⟩, ⟨⟨7019437836125367947, 7019437836125367971⟩, ⟨11911868279923129152, 11911868279923129176⟩⟩, o],
  [o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨-17962623750315821, -17962623750315816⟩, ⟨-2, 3⟩⟩, ⟨⟨-7, 6⟩, ⟨-7, 6⟩⟩, ⟨⟨2126625895064670, 2126625895064691⟩, ⟨-12, 11⟩⟩, ⟨⟨-11, 12⟩, ⟨-14, 12⟩⟩, ⟨⟨-8120220830259673, -8120220830259655⟩, ⟨-8, 8⟩⟩, ⟨⟨-3, 3⟩, ⟨-2, 2⟩⟩, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨-17795376480780614, -17795376480780609⟩, ⟨-3, 3⟩⟩, ⟨⟨-7, 7⟩, ⟨-7, 7⟩⟩, ⟨⟨2113404864144409, 2113404864144431⟩, ⟨-12, 11⟩⟩, ⟨⟨-12, 11⟩, ⟨-12, 12⟩⟩, ⟨⟨-8094940156832714, -8094940156832698⟩, ⟨-8, 8⟩⟩, ⟨⟨-3, 3⟩, ⟨-2, 2⟩⟩, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨-17629836945051631, -17629836945051626⟩, ⟨-3, 2⟩⟩, ⟨⟨-7, 8⟩, ⟨-7, 7⟩⟩, ⟨⟨2100277981618070, 2100277981618093⟩, ⟨-12, 12⟩⟩, ⟨⟨-13, 12⟩, ⟨-12, 14⟩⟩, ⟨⟨-8069761155729782, -8069761155729764⟩, ⟨-8, 8⟩⟩, ⟨⟨-3, 3⟩, ⟨-2, 2⟩⟩, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨-17465986430971618, -17465986430971613⟩, ⟨-3, 2⟩⟩, ⟨⟨-8, 6⟩, ⟨-7, 7⟩⟩, ⟨⟨2087244512733740, 2087244512733762⟩, ⟨-12, 13⟩⟩, ⟨⟨-12, 12⟩, ⟨-13, 13⟩⟩, ⟨⟨-8044683365676573, -8044683365676556⟩, ⟨-8, 7⟩⟩, ⟨⟨-3, 3⟩, ⟨-2, 2⟩⟩, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨-17303806442411510, -17303806442411504⟩, ⟨-3, 2⟩⟩, ⟨⟨-8, 7⟩, ⟨-7, 8⟩⟩, ⟨⟨2074303728800307, 2074303728800331⟩, ⟨-12, 11⟩⟩, ⟨⟨-12, 11⟩, ⟨-13, 11⟩⟩, ⟨⟨-8019706327501709, -8019706327501691⟩, ⟨-8, 8⟩⟩, ⟨⟨-3, 3⟩, ⟨-2, 2⟩⟩, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨-17143278696686696, -17143278696686691⟩, ⟨-3, 3⟩⟩, ⟨⟨-8, 8⟩, ⟨-7, 7⟩⟩, ⟨⟨2061454907136490, 2061454907136513⟩, ⟨-12, 13⟩⟩, ⟨⟨-11, 11⟩, ⟨-12, 13⟩⟩, ⟨⟨-7994829584128861, -7994829584128845⟩, ⟨-8, 8⟩⟩, ⟨⟨-3, 3⟩, ⟨-2, 2⟩⟩, o]
]

private def st10_7 : List (List CFpIv) := [
  [o, ⟨⟨-225910479256822423, -225910479256822412⟩, ⟨383363237526728948, 383363237526728955⟩⟩, ⟨⟨-102090428927777944, -102090428927777905⟩, ⟨-173211545438220789, -173211545438220756⟩⟩, ⟨⟨89466236562813278, 89466236562813346⟩, ⟨-7414111482076, -7414111482007⟩⟩, ⟨⟨-18992795500621459, -18992795500621371⟩, ⟨34299741023530449, 34299741023530540⟩⟩, ⟨⟨-8858588231136853, -8858588231136760⟩, ⟨-15029810505812029, -15029810505811938⟩⟩, ⟨⟨365878515616, 365878515694⟩, ⟨-665369697615, -665369697537⟩⟩, ⟨⟨172422490566, 172422490620⟩, ⟨290578359537, 290578359593⟩⟩, ⟨⟨-204363317, -204363285⟩, ⟨455747730, 455747763⟩⟩, ⟨⟨-128549131, -128549109⟩, ⟨-181303579, -181303558⟩⟩, ⟨⟨4609416, 4609428⟩, ⟨-8322636, -8322624⟩⟩, ⟨⟨2149271, 2149276⟩, ⟨3647250, 3647254⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, o, ⟨⟨-225924511775476415, -225924511775476404⟩, ⟨383387050285656934, 383387050285656941⟩⟩, ⟨⟨-102103113407291809, -102103113407291771⟩, ⟨-173233064313654150, -173233064313654118⟩⟩, ⟨⟨89482909586455822, 89482909586455892⟩, ⟨-7415995771531, -7415995771460⟩⟩, ⟨⟨-18997514784835111, -18997514784835017⟩, ⟨34308264212553402, 34308264212553496⟩⟩, ⟨⟨-8861339964160627, -8861339964160528⟩, ⟨-15034478998201308, -15034478998201209⟩⟩, ⟨⟨366039588522, 366039588604⟩, ⟨-665662970700, -665662970619⟩⟩, ⟨⟨172509247440, 172509247496⟩, ⟨290724419772, 290724419828⟩⟩, ⟨⟨-204490930, -204490898⟩, ⟨456038912, 456038947⟩⟩, ⟨⟨-128639921, -128639900⟩, ⟨-181429552, -181429532⟩⟩, ⟨⟨4613219, 4613231⟩, ⟨-8329501, -8329489⟩⟩, ⟨⟨2151177, 2151183⟩, ⟨3650485, 3650490⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, o, ⟨⟨-225938545749308477, -225938545749308466⟩, ⟨383410865513978008, 383410865513978015⟩⟩, ⟨⟨-102115799990644561, -102115799990644523⟩, ⟨-173254586757423774, -173254586757423740⟩⟩, ⟨⟨89499586410843877, 89499586410843944⟩, ⟨-7417880695608, -7417880695533⟩⟩, ⟨⟨-19002235437961430, -19002235437961337⟩, ⟨34316789874101579, 34316789874101675⟩⟩, ⟨⟨-8864092666451702, -8864092666451603⟩, ⟨-15039149134908324, -15039149134908228⟩⟩, ⟨⟨366200742832, 366200742917⟩, ⟨-665956392229, -665956392146⟩⟩, ⟨⟨172596053396, 172596053456⟩, ⟨290870562530, 290870562591⟩⟩, ⟨⟨-204618634, -204618598⟩, ⟨456330303, 456330341⟩⟩, ⟨⟨-128730783, -128730760⟩, ⟨-181555620, -181555599⟩⟩, ⟨⟨4617023, 4617035⟩, ⟨-8336372, -8336361⟩⟩, ⟨⟨2153086, 2153091⟩, ⟨3653723, 3653727⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, o, ⟨⟨-225952581178500138, -225952581178500127⟩, ⟨383434683212000222, 383434683212000229⟩⟩, ⟨⟨-102128488678245744, -102128488678245707⟩, ⟨-173276112770223942, -173276112770223910⟩⟩, ⟨⟨89516267036966453, 89516267036966520⟩, ⟨-7419766254569, -7419766254501⟩⟩, ⟨⟨-19006957460444372, -19006957460444283⟩, ⟨34325318008976971, 34325318008977063⟩⟩, ⟨⟨-8866846338385970, -8866846338385877⟩, ⟨-15043820916570692, -15043820916570602⟩⟩, ⟨⟨366361978595, 366361978672⟩, ⟨-666249962282, -666249962205⟩⟩, ⟨⟨172682908467, 172682908522⟩, ⟨291016787870, 291016787923⟩⟩, ⟨⟨-204746423, -204746389⟩, ⟨456621906, 456621942⟩⟩, ⟨⟨-128821713, -128821693⟩, ⟨-181681786, -181681765⟩⟩, ⟨⟨4620832, 4620844⟩, ⟨-8343249, -8343238⟩⟩, ⟨⟨2154996, 2155001⟩, ⟨3656964, 3656969⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, o, ⟨⟨-225966618063232951, -225966618063232940⟩, ⟨383458503380031662, 383458503380031669⟩⟩, ⟨⟨-102141179470504984, -102141179470504946⟩, ⟨-173297642352749086, -173297642352749053⟩⟩, ⟨⟨89532951465812838, 89532951465812906⟩, ⟨-7421652448693, -7421652448625⟩⟩, ⟨⟨-19011680852728042, -19011680852727953⟩, ⟨34333848617981835, 34333848617981925⟩⟩, ⟨⟨-8869600980339479, -8869600980339389⟩, ⟨-15048494343826298, -15048494343826207⟩⟩, ⟨⟨366523295849, 366523295926⟩, ⟨-666543680950, -666543680875⟩⟩, ⟨⟨172769812681, 172769812734⟩, ⟨291163095836, 291163095890⟩⟩, ⟨⟨-204874303, -204874271⟩, ⟨456913717, 456913750⟩⟩, ⟨⟨-128912718, -128912696⟩, ⟨-181808047, -181808029⟩⟩, ⟨⟨4624644, 4624657⟩, ⟨-8350131, -8350121⟩⟩, ⟨⟨2156908, 2156912⟩, ⟨3660209, 3660214⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, o, ⟨⟨-225980656403688488, -225980656403688477⟩, ⟨383482326018380451, 383482326018380458⟩⟩, ⟨⟨-102153872367831999, -102153872367831960⟩, ⟨-173319175505693780, -173319175505693746⟩⟩, ⟨⟨89549639698372607, 89549639698372676⟩, ⟨-7423539278242, -7423539278171⟩⟩, ⟨⟨-19016405615256705, -19016405615256614⟩, ⟨34342381701918723, 34342381701918815⟩⟩, ⟨⟨-8872356592688437, -8872356592688341⟩, ⟨-15053169417313286, -15053169417313192⟩⟩, ⟨⟨366684694645, 366684694726⟩, ⟨-666837548321, -666837548241⟩⟩, ⟨⟨172856766067, 172856766121⟩, ⟨291309486481, 291309486538⟩⟩, ⟨⟨-205002272, -205002239⟩, ⟨457205735, 457205767⟩⟩, ⟨⟨-129003791, -129003771⟩, ⟨-181934407, -181934387⟩⟩, ⟨⟨4628460, 4628472⟩, ⟨-8357022, -8357011⟩⟩, ⟨⟨2158822, 2158826⟩, ⟨3663457, 3663461⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, o, ⟨⟨-225994696200048342, -225994696200048331⟩, ⟨383506151127354749, 383506151127354756⟩⟩, ⟨⟨-102166567370636583, -102166567370636543⟩, ⟨-173340712229752740, -173340712229752708⟩⟩, ⟨⟨89566331735635607, 89566331735635673⟩, ⟨-7425426743481, -7425426743411⟩⟩, ⟨⟨-19021131748474774, -19021131748474687⟩, ⟨34350917261590468, 34350917261590559⟩⟩, ⟨⟨-8875113175809195, -8875113175809101⟩, ⟨-15057846137670069, -15057846137669973⟩⟩, ⟨⟨366846175032, 366846175112⟩, ⟨-667131564477, -667131564391⟩⟩, ⟨⟨172943768655, 172943768714⟩, ⟨291455959859, 291455959917⟩⟩, ⟨⟨-205130331, -205130295⟩, ⟨457497962, 457497996⟩⟩, ⟨⟨-129094937, -129094916⟩, ⟨-182060864, -182060843⟩⟩, ⟨⟨4632278, 4632291⟩, ⟨-8363917, -8363905⟩⟩, ⟨⟨2160737, 2160742⟩, ⟨3666707, 3666711⟩⟩, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, o, ⟨⟨-226008737452494127, -226008737452494116⟩, ⟨383529978707262748, 383529978707262755⟩⟩, ⟨⟨-102179264479328621, -102179264479328582⟩, ⟨-173362252525620832, -173362252525620799⟩⟩, ⟨⟨89583027578591961, 89583027578592031⟩, ⟨-7427314844683, -7427314844612⟩⟩, ⟨⟨-19025859252826831, -19025859252826741⟩, ⟨34359455297800174, 34359455297800268⟩⟩, ⟨⟨-8877870730078279, -8877870730078182⟩, ⟨-15062524505535322, -15062524505535226⟩⟩, ⟨⟨367007737051, 367007737137⟩, ⟨-667425729496, -667425729412⟩⟩, ⟨⟨173030820480, 173030820541⟩, ⟨291602516019, 291602516081⟩⟩, ⟨⟨-205258478, -205258440⟩, ⟨457790397, 457790436⟩⟩, ⟨⟨-129186154, -129186132⟩, ⟨-182187416, -182187395⟩⟩, ⟨⟨4636102, 4636114⟩, ⟨-8370819, -8370808⟩⟩, ⟨⟨2162654, 2162659⟩, ⟨3669961, 3669966⟩⟩, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, o, ⟨⟨-226022780161207479, -226022780161207468⟩, ⟨383553808758412679, 383553808758412686⟩⟩, ⟨⟨-102191963694318081, -102191963694318044⟩, ⟨-173383796393993064, -173383796393993030⟩⟩, ⟨⟨89599727228232086, 89599727228232153⟩, ⟨-7429203582110, -7429203582040⟩⟩, ⟨⟨-19030588128757600, -19030588128757510⟩, ⟨34367995811351243, 34367995811351337⟩⟩, ⟨⟨-8880629255872355, -8880629255872257⟩, ⟨-15067204521547993, -15067204521547898⟩⟩, ⟨⟨367169380758, 367169380837⟩, ⟨-667720043469, -667720043389⟩⟩, ⟨⟨173117921576, 173117921631⟩, ⟨291749155023, 291749155077⟩⟩, ⟨⟨-205386713, -205386680⟩, ⟨458083045, 458083080⟩⟩, ⟨⟨-129277442, -129277421⟩, ⟨-182314068, -182314046⟩⟩, ⟨⟨4639927, 4639940⟩, ⟨-8377727, -8377715⟩⟩, ⟨⟨2164574, 2164578⟩, ⟨3673218, 3673223⟩⟩, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, o, ⟨⟨-226036824326370053, -226036824326370042⟩, ⟨383577641281112805, 383577641281112812⟩⟩, ⟨⟨-102204665016015022, -102204665016014982⟩, ⟨-173405343835564584, -173405343835564550⟩⟩, ⟨⟨89616430685546659, 89616430685546729⟩, ⟨-7431092956033, -7431092955964⟩⟩, ⟨⟨-19035318376711966, -19035318376711878⟩, ⟨34376538803047342, 34376538803047433⟩⟩, ⟨⟨-8883388753568256, -8883388753568164⟩, ⟨-15071886186347292, -15071886186347200⟩⟩, ⟨⟨367331106191, 367331106269⟩, ⟨-668014506481, -668014506403⟩⟩, ⟨⟨173205071966, 173205072021⟩, ⟨291895876910, 291895876964⟩⟩, ⟨⟨-205515038, -205515004⟩, ⟨458375898, 458375932⟩⟩, ⟨⟨-129368801, -129368779⟩, ⟨-182440814, -182440793⟩⟩, ⟨⟨4643757, 4643769⟩, ⟨-8384641, -8384631⟩⟩, ⟨⟨2166496, 2166500⟩, ⟨3676478, 3676482⟩⟩, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, o, ⟨⟨-226050869948163527, -226050869948163516⟩, ⟨383601476275671426, 383601476275671433⟩⟩, ⟨⟨-102217368444829581, -102217368444829543⟩, ⟨-173426894851030690, -173426894851030657⟩⟩, ⟨⟨89633137951526654, 89633137951526722⟩, ⟨-7432982966723, -7432982966652⟩⟩, ⟨⟨-19040049997134978, -19040049997134884⟩, ⟨34385084273692431, 34385084273692526⟩⟩, ⟨⟨-8886149223542978, -8886149223542877⟩, ⟨-15076569500572704, -15076569500572605⟩⟩, ⟨⟨367492913395, 367492913480⟩, ⟨-668309118623, -668309118541⟩⟩, ⟨⟨173292271685, 173292271742⟩, ⟨292042681735, 292042681793⟩⟩, ⟨⟨-205643453, -205643419⟩, ⟨458668964, 458669000⟩⟩, ⟨⟨-129460231, -129460210⟩, ⟨-182567659, -182567637⟩⟩, ⟨⟨4647590, 4647603⟩, ⟨-8391562, -8391550⟩⟩, ⟨⟨2168418, 2168423⟩, ⟨3679741, 3679745⟩⟩, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨-226064917026769597, -226064917026769586⟩, ⟨383625313742396880, 383625313742396887⟩⟩, ⟨⟨-102230073981171982, -102230073981171943⟩, ⟨-173448449441086825, -173448449441086789⟩⟩, ⟨⟨89649849027163309, 89649849027163383⟩, ⟨-7434873614445, -7434873614371⟩⟩, ⟨⟨-19044782990471825, -19044782990471731⟩, ⟨34393632224090750, 34393632224090845⟩⟩, ⟨⟨-8888910666173655, -8888910666173562⟩, ⟨-15081254464863962, -15081254464863867⟩⟩, ⟨⟨367654802429, 367654802507⟩, ⟨-668603879968, -668603879891⟩⟩, ⟨⟨173379520767, 173379520821⟩, ⟨292189569559, 292189569613⟩⟩, ⟨⟨-205771958, -205771925⟩, ⟨458962239, 458962274⟩⟩, ⟨⟨-129551734, -129551712⟩, ⟨-182694601, -182694579⟩⟩, ⟨⟨4651426, 4651439⟩, ⟨-8398489, -8398477⟩⟩, ⟨⟨2170342, 2170347⟩, ⟨3683007, 3683012⟩⟩, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨-226078965562369984, -226078965562369973⟩, ⟨383649153681597535, 383649153681597542⟩⟩, ⟨⟨-102242781625452538, -102242781625452499⟩, ⟨-173470007606428572, -173470007606428538⟩⟩, ⟨⟨89666563913448163, 89666563913448233⟩, ⟨-7436764899467, -7436764899396⟩⟩, ⟨⟨-19049517357167867, -19049517357167773⟩, ⟨34402182655046821, 34402182655046915⟩⟩, ⟨⟨-8891673081837602, -8891673081837503⟩, ⟨-15085941079861089, -15085941079860990⟩⟩, ⟨⟨367816773324, 367816773407⟩, ⟨-668898790614, -668898790532⟩⟩, ⟨⟨173466819234, 173466819293⟩, ⟨292336540421, 292336540479⟩⟩, ⟨⟨-205900552, -205900517⟩, ⟨459255723, 459255759⟩⟩, ⟨⟨-129643307, -129643286⟩, ⟨-182821639, -182821619⟩⟩, ⟨⟨4655266, 4655278⟩, ⟨-8405421, -8405410⟩⟩, ⟨⟨2172269, 2172274⟩, ⟨3686277, 3686281⟩⟩, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨-226093015555146426, -226093015555146415⟩, ⟨383672996093581800, 383672996093581807⟩⟩, ⟨⟨-102255491378081645, -102255491378081608⟩, ⟨-173491569347751662, -173491569347751628⟩⟩, ⟨⟨89683282611373009, 89683282611373077⟩, ⟨-7438656822058, -7438656821989⟩⟩, ⟨⟨-19054253097668609, -19054253097668519⟩, ⟨34410735567365447, 34410735567365540⟩⟩, ⟨⟨-8894436470912270, -8894436470912174⟩, ⟨-15090629346204355, -15090629346204258⟩⟩, ⟨⟨367978826139, 367978826220⟩, ⟨-669193850639, -669193850555⟩⟩, ⟨⟨173554167125, 173554167184⟩, ⟨292483594383, 292483594441⟩⟩, ⟨⟨-206029238, -206029200⟩, ⟨459549418, 459549454⟩⟩, ⟨⟨-129734953, -129734930⟩, ⟨-182948776, -182948755⟩⟩, ⟨⟨4659110, 4659121⟩, ⟨-8412361, -8412351⟩⟩, ⟨⟨2174199, 2174202⟩, ⟨3689550, 3689554⟩⟩, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨-226107067005280683, -226107067005280672⟩, ⟨383696840978658116, 383696840978658123⟩⟩, ⟨⟨-102268203239469784, -102268203239469745⟩, ⟨-173513134665751970, -173513134665751936⟩⟩, ⟨⟨89700005121929937, 89700005121930006⟩, ⟨-7440549382487, -7440549382419⟩⟩, ⟨⟨-19058990212419725, -19058990212419636⟩, ⟨34419290961851712, 34419290961851804⟩⟩, ⟨⟨-8897200833775279, -8897200833775188⟩, ⟨-15095319264534309, -15095319264534217⟩⟩, ⟨⟨368140960917, 368140960994⟩, ⟨-669489060125, -669489060050⟩⟩, ⟨⟨173641564472, 173641564525⟩, ⟨292630731495, 292630731549⟩⟩, ⟨⟨-206158008, -206157976⟩, ⟨459843326, 459843357⟩⟩, ⟨⟨-129826668, -129826648⟩, ⟨-183076009, -183075990⟩⟩, ⟨⟨4662956, 4662969⟩, ⟨-8419306, -8419297⟩⟩, ⟨⟨2176128, 2176132⟩, ⟨3692826, 3692829⟩⟩, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨-226121119912954538, -226121119912954527⟩, ⟨383720688337134961, 383720688337134968⟩⟩, ⟨⟨-102280917210027522, -102280917210027484⟩, ⟨-173534703561125514, -173534703561125482⟩⟩, ⟨⟨89716731446111313, 89716731446111379⟩, ⟨-7442442581025, -7442442580956⟩⟩, ⟨⟨-19063728701867032, -19063728701866945⟩, ⟨34427848839310984, 34427848839311074⟩⟩, ⟨⟨-8899966170804408, -8899966170804318⟩, ⟨-15100010835491765, -15100010835491673⟩⟩, ⟨⟨368303177702, 368303177779⟩, ⟨-669784419171, -669784419091⟩⟩, ⟨⟨173729011301, 173729011356⟩, ⟨292777951805, 292777951863⟩⟩, ⟨⟨-206286874, -206286838⟩, ⟨460137439, 460137474⟩⟩, ⟨⟨-129918458, -129918436⟩, ⟨-183203342, -183203320⟩⟩, ⟨⟨4666807, 4666819⟩, ⟨-8426260, -8426248⟩⟩, ⟨⟨2178061, 2178065⟩, ⟨3696104, 3696109⟩⟩, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨-226135174278349792, -226135174278349781⟩, ⟨383744538169320847, 383744538169320854⟩⟩, ⟨⟨-102293633290165513, -102293633290165473⟩, ⟨-173556276034568462, -173556276034568428⟩⟩, ⟨⟨89733461584909778, 89733461584909847⟩, ⟨-7444336417940, -7444336417870⟩⟩, ⟨⟨-19068468566456516, -19068468566456425⟩, ⟨34436409200548914, 34436409200549005⟩⟩, ⟨⟨-8902732482377592, -8902732482377496⟩, ⟨-15104704059717804, -15104704059717710⟩⟩, ⟨⟨368465476543, 368465476622⟩, ⟨-670079927850, -670079927770⟩⟩, ⟨⟨173816507645, 173816507701⟩, ⟨292925255371, 292925255426⟩⟩, ⟨⟨-206415826, -206415793⟩, ⟨460431765, 460431800⟩⟩, ⟨⟨-130010316, -130010296⟩, ⟨-183330770, -183330751⟩⟩, ⟨⟨4670661, 4670672⟩, ⟨-8433217, -8433207⟩⟩, ⟨⟨2179995, 2179999⟩, ⟨3699387, 3699391⟩⟩, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨-226149230101648269, -226149230101648258⟩, ⟨383768390475524323, 383768390475524330⟩⟩, ⟨⟨-102306351480294494, -102306351480294455⟩, ⟨-173577852086777118, -173577852086777085⟩⟩, ⟨⟨89750195539318264, 89750195539318333⟩, ⟨-7446230893499, -7446230893429⟩⟩, ⟨⟨-19073209806634304, -19073209806634215⟩, ⟨34444972046371437, 34444972046371528⟩⟩, ⟨⟨-8905499768872912, -8905499768872819⟩, ⟨-15109398937853769, -15109398937853676⟩⟩, ⟨⟨368627857488, 368627857567⟩, ⟨-670375586251, -670375586173⟩⟩, ⟨⟨173904053532, 173904053587⟩, ⟨293072642241, 293072642296⟩⟩, ⟨⟨-206544868, -206544834⟩, ⟨460726302, 460726338⟩⟩, ⟨⟨-130102250, -130102227⟩, ⟨-183458299, -183458277⟩⟩, ⟨⟨4674517, 4674530⟩, ⟨-8440182, -8440170⟩⟩, ⟨⟨2181930, 2181935⟩, ⟨3702671, 3702676⟩⟩],
  [⟨⟨0, 1⟩, ⟨0, 0⟩⟩, ⟨⟨-10, 2⟩, ⟨-3, 4⟩⟩, ⟨⟨-25, 49⟩, ⟨-35, 29⟩⟩, ⟨⟨-168, 119⟩, ⟨-127, 150⟩⟩, ⟨⟨-372, 442⟩, ⟨-431, 377⟩⟩, ⟨⟨-939, 834⟩, ⟨-837, 926⟩⟩, ⟨⟨-370, 2744⟩, ⟨-1617, 1486⟩⟩, ⟨⟨-82933, -78241⟩, ⟨-1296, 3380⟩⟩, ⟨⟨4497861, 4504250⟩, ⟨-72377, -66006⟩⟩, ⟨⟨-203763297, -203755118⟩, ⟨3865573, 3873733⟩⟩, ⟨⟨7500638014, 7500648111⟩, ⟨-175519975, -175509907⟩⟩, ⟨⟨-224303531851, -224303519704⟩, ⟨6476120980, 6476133097⟩⟩, ⟨⟨5420323677882, 5420323692205⟩, ⟨-194229735608, -194229721310⟩⟩, ⟨⟨-104770810797157, -104770810780556⟩, ⟨4710922264108, 4710922280677⟩⟩, ⟨⟨1593723397944683, 1593723397963561⟩, ⟨-91498104399464, -91498104380621⟩⟩, ⟨⟨-18616053560585134, -18616053560564109⟩, ⟨1400939421727004, 1400939421747991⟩⟩, ⟨⟨160985886291976727, 160985886291999747⟩, ⟨-16516777305979371, -16516777305956401⟩⟩, ⟨⟨-975635251669681949, -975635251669656893⟩, ⟨144854349483797797, 144854349483822799⟩⟩, ⟨⟨3818484640076521715, 3818484640076549187⟩, ⟨-898434481858388450, -898434481858360983⟩⟩, ⟨⟨-8703417566172008463, -8703417566171978062⟩, ⟨3668632400249935553, 3668632400249965989⟩⟩, ⟨⟨11466498999442684639, 11466498999442717627⟩, ⟨-9106524940803297897, -9106524940803264899⟩⟩, ⟨⟨-6820072608944706925, -6820072608944673797⟩, ⟨13960819674769042185, 13960819674769075294⟩⟩, ⟨⟨-3884222151424521043, -3884222151424492115⟩, ⟨-12229209306317466897, -12229209306317437981⟩⟩, ⟨⟨11799966291438068632, 11799966291438089562⟩, ⟨2306543774734289033, 2306543774734309964⟩⟩, ⟨⟨-10731442183407988668, -10731442183407976520⟩, ⟨9001652190675239259, 9001652190675251411⟩⟩, ⟨⟨4197066892960478781, 4197066892960484302⟩, ⟨-13285885273604816517, -13285885273604810997⟩⟩, ⟨⟨545646420879966982, 545646420879968876⟩, ⟨9682595233415913654, 9682595233415915549⟩⟩, ⟨⟨-1262673344745057797, -1262673344745057342⟩, ⟨-3983220352895064867, -3983220352895064411⟩⟩, ⟨⟨405935872926090984, 405935872926091046⟩, ⟨753379545142370609, 753379545142370672⟩⟩],
  [o],
  [⟨⟨-5, 5⟩, ⟨-5, 5⟩⟩, ⟨⟨-68, 68⟩, ⟨-68, 68⟩⟩, ⟨⟨-379, 379⟩, ⟨-379, 379⟩⟩, ⟨⟨-1352, 1352⟩, ⟨-1352, 1352⟩⟩, ⟨⟨-3484, 3484⟩, ⟨-3484, 3484⟩⟩, ⟨⟨-6966, 6995⟩, ⟨-6986, 6975⟩⟩, ⟨⟨-12421, 10556⟩, ⟨-12171, 10808⟩⟩, ⟨⟨-23815, 8690⟩, ⟨62892, 95402⟩⟩, ⟨⟨3983238, 4024130⟩, ⟨-1905756, -1864868⟩⟩, ⟨⟨-165293721, -165246859⟩, ⟨-111843934, -111797068⟩⟩, ⟨⟨-425843501, -425793333⟩, ⟨7298249499, 7298299674⟩⟩, ⟨⟨192864125599, 192864177581⟩, ⟨-100218454313, -100218402334⟩⟩, ⟨⟨-4437334042515, -4437333988238⟩, ⟨-2737342578716, -2737342524453⟩⟩, ⟨⟨-1201002988712, -1201002930093⟩, ⟨99814476651188, 99814476709801⟩⟩, ⟨⟨1292320941321588, 1292320941387081⟩, ⟨-759874661085317, -759874661019807⟩⟩, ⟨⟨-15168165379348938, -15168165379274624⟩, ⟨-8111611546076249, -8111611546001935⟩⟩, ⟨⟨9418321469577404, 9418321469661130⟩, ⟨144543160845758343, 144543160845842064⟩⟩, ⟨⟨676620823286403550, 676620823286496096⟩, ⟨-500136054157772028, -500136054157679486⟩⟩, ⟨⟨-2894845637791106765, -2894845637791006583⟩, ⟨-990662966863742855, -990662966863642676⟩⟩, ⟨⟨2089728515194735834, 2089728515194840902⟩, ⟨5761021264540789998, 5761021264540895083⟩⟩, ⟨⟨3524392932746199215, 3524392932746302129⟩, ⟨-6142488734811199091, -6142488734811096178⟩⟩, ⟨⟨-4620546011652167782, -4620546011652078773⟩, ⟨827090009066804409, 827090009066893409⟩⟩, ⟨⟨1091339599159163728, 1091339599159228006⟩, ⟨869614669252369263, 869614669252433540⟩⟩, ⟨⟨-639229228447320077, -639229228447283109⟩, ⟨630916067513886451, 630916067513923427⟩⟩, ⟨⟨3014679549488943410, 3014679549488959668⟩, ⟨669130524924733330, 669130524924749591⟩⟩, ⟨⟨-2146581298263838437, -2146581298263833159⟩, ⟨-5003068294797875157, -5003068294797869887⟩⟩, ⟨⟨-2553683495861470748, -2553683495861469502⟩, ⟨5071562748058743666, 5071562748058744915⟩⟩, ⟨⟨3194305957306261703, 3194305957306261937⟩, ⟨-887175301599498718, -887175301599498485⟩⟩, ⟨⟨-731718736137855766, -731718736137855730⟩, ⟨-441572589866602644, -441572589866602608⟩⟩],
  [o],
  [⟨⟨-5, 5⟩, ⟨-5, 5⟩⟩, ⟨⟨-68, 68⟩, ⟨-68, 68⟩⟩, ⟨⟨-377, 377⟩, ⟨-377, 377⟩⟩, ⟨⟨-1330, 1330⟩, ⟨-1330, 1330⟩⟩, ⟨⟨-3407, 3407⟩, ⟨-3407, 3407⟩⟩, ⟨⟨-6811, 6822⟩, ⟨-6831, 6802⟩⟩, ⟨⟨-11946, 10570⟩, ⟨-12177, 10338⟩⟩, ⟨⟨-94521, -62517⟩, ⟨-7552, 24454⟩⟩, ⟨⟨-1830945, -1790568⟩, ⟨3977733, 4018108⟩⟩, ⟨⟨113632304, 113678611⟩, ⟨161526648, 161572956⟩⟩, ⟨⟨7196664033, 7196713608⟩, ⟨-582011752, -581962181⟩⟩, ⟨⟨93431672228, 93431723616⟩, ⟨-192591746185, -192591694798⟩⟩, ⟨⟨-2833120849314, -2833120795597⟩, ⟨-4260942699304, -4260942645573⟩⟩, ⟨⟨-97380693626267, -97380693568153⟩, ⟨5312822789545, 5312822847650⟩⟩, ⟨⟨-669302628890634, -669302628825624⟩, ⟨1292903177643735, 1292903177708738⟩⟩, ⟨⟨8813407410985085, 8813407411058867⟩, ⟨14024263580251082, 14024263580324877⟩⟩, ⟨⟨137679303587847129, 137679303587930216⟩, ⟨-4036132024681064, -4036132024597977⟩⟩, ⟨⟨377085364931767886, 377085364931859624⟩, ⟨-687201191962385047, -687201191962293312⟩⟩, ⟨⟨-1409795268278415565, -1409795268278316336⟩, ⟨-2355865676474432501, -2355865676474333269⟩⟩, ⟨⟨-5110251099640051364, -5110251099639947243⟩, ⟨72010050489839908, 72010050489944015⟩⟩, ⟨⟨-2812534306467192208, -2812534306467090093⟩, ⟨5095474352070008023, 5095474352070110140⟩⟩, ⟨⟨2137118268892665441, 2137118268892753939⟩, ⟨3375373693424737366, 3375373693424825874⟩⟩, ⟨⟨1318542267054382629, 1318542267054446657⟩, ⟨-208921038794518810, -208921038794454786⟩⟩, ⟨⟨-575469070223328551, -575469070223291735⟩, ⟨599493875718625687, 599493875718662504⟩⟩, ⟨⟨1287715862428619454, 1287715862428635588⟩, ⟨2481876905501170106, 2481876905501186243⟩⟩, ⟨⟨4557555360923234633, 4557555360923239815⟩, ⟨39819238897180244, 39819238897185423⟩⟩, ⟨⟨2318313970529905685, 2318313970529906873⟩, ⟨-4021402729220918306, -4021402729220917116⟩⟩, ⟨⟨-1409595252343639762, -1409595252343639549⟩, ⟨-2425154598797177207, -2425154598797176995⟩⟩, ⟨⟨-854090007497015639, -854090007497015606⟩, ⟨-43870969895629, -43870969895595⟩⟩],
  [o],
  [⟨⟨391436540786, 391436540797⟩, ⟨-3, 4⟩⟩, ⟨⟨-19513394908339, -19513394908240⟩, ⟨339862092083, 339862092150⟩⟩, ⟨⟨466914489202223, 466914489202618⟩, ⟨-16773752491246, -16773752490974⟩⟩, ⟨⟨-7139434670699425, -7139434670698359⟩, ⟨397073191454960, 397073191455703⟩⟩, ⟨⟨78355155716578384, 78355155716580723⟩, ⟨-6001761719822099, -6001761719820465⟩⟩, ⟨⟨-657244881993021041, -657244881993016383⟩, ⟨65053618913069850, 65053618913073101⟩⟩, ⟨⟨4380885765847888985, 4380885765847897942⟩, ⟨-538372728063039726, -538372728063033495⟩⟩, ⟨⟨-23819326757781107169, -23819326757781090010⟩, ⟨3536566348886619502, 3536566348886631365⟩⟩, ⟨⟨107604822237005695060, 107604822237005728445⟩, ⟨-18926338833699965337, -18926338833699942390⟩⟩, ⟨⟨-409324628853420146144, -409324628853420079762⟩, ⟨84037055310868082818, 84037055310868128477⟩⟩, ⟨⟨1324012795839277972711, 1324012795839278105997⟩, ⟨-313699246500052970297, -313699246500052877417⟩⟩, ⟨⟨-3667853325469277607204, -3667853325469277344287⟩, ⟨993926618950609786139, 993926618950609974211⟩⟩, ⟨⟨8746556284222859900622, 8746556284222860393921⟩, ⟨-2691462798626339452545, -2691462798626339086703⟩⟩, ⟨⟨-18015158834289798158941, -18015158834289797303412⟩, ⟨6258798015444705344806, 6258798015444706006185⟩⟩, ⟨⟨32110213708070572089990, 32110213708070573432027⟩, ⟨-12536304709382389297232, -12536304709382388214225⟩⟩, ⟨⟨-49555406347749493560025, -49555406347749491684985⟩, ⟨21659723934752320816575, 21659723934752322393895⟩⟩, ⟨⟨66167872662953648129792, 66167872662953650437472⟩, ⟨-32279909278534270756216, -32279909278534268738882⟩⟩, ⟨⟨-76275798523679724699513, -76275798523679722219297⟩, ⟨41434481748867080128048, 41434481748867082372116⟩⟩, ⟨⟨75638176329434368078107, 75638176329434370387580⟩, ⟨-45668679192003348959266, -45668679192003346806115⟩⟩, ⟨⟨-64179908109426554102666, -64179908109426552255038⟩, ⟨43014317870352620798926, 43014317870352622565797⟩⟩, ⟨⟨46253886612381254676560, 46253886612381255934142⟩, ⟨-34382687075847435605476, -34382687075847434377520⟩⟩, ⟨⟨-28029966185209044276153, -28029966185209043556763⟩, ⟨23101029984136180702638, 23101029984136181416725⟩⟩, ⟨⟨14089721636359477498415, 14089721636359477838839⟩, ⟨-12875505423009530775680, -12875505423009530433613⟩⟩, ⟨⟨-5765713783101308972593, -5765713783101308842116⟩, ⟨5845264593832124537379, 5845264593832124669571⟩⟩, ⟨⟨1870541408919843243676, 1870541408919843283015⟩, ⟨-2105978081631523286179, -2105978081631523246143⟩⟩, ⟨⟨-462545171386657476023, -462545171386657467087⟩, ⟨579227020731052137958, 579227020731052147061⟩⟩, ⟨⟨81833968090087534870, 81833968090087536299⟩, ⟨-114224593846151993031, -114224593846151991581⟩⟩, ⟨⟨-9217435921131398408, -9217435921131398261⟩, ⟨14380512861979947024, 14380512861979947174⟩⟩, ⟨⟨496138938356833817, 496138938356833829⟩, ⟨-868243142124459199, -868243142124459187⟩⟩],
  [o],
  [⟨⟨-287427956521, -287427956409⟩, ⟨-265723507637, -265723507524⟩⟩, ⟨⟨-3920774860216, -3920774859170⟩, ⟨18972376598239, 18972376599286⟩⟩, ⟨⟨434089705237661, 434089705242754⟩, ⟨-153091468016116, -153091468011020⟩⟩, ⟨⟨-5398079174638235, -5398079174620321⟩, ⟨-4441011736224715, -4441011736206799⟩⟩, ⟨⟨-10984832074819562, -10984832074766957⟩, ⟨75420601380930578, 75420601380983180⟩⟩, ⟨⟨585331867335192523, 585331867335332881⟩, ⟨-247252423332119042, -247252423331978687⟩⟩, ⟨⟨-3412582569125448184, -3412582569125093438⟩, ⟨-2468785316964692045, -2468785316964337296⟩⟩, ⟨⟨-1841857708809289287, -1841857708808433650⟩, ⟨22716656478725097587, 22716656478725953224⟩⟩, ⟨⟨91671314596264454229, 91671314596266399959⟩, ⟨-45994966906448881811, -45994966906446936072⟩⟩, ⟨⟨-329817649310890871460, -329817649310886772829⟩, ⟨-206432647149058847628, -206432647149054749064⟩⟩, ⟨⟨-15266474953574517068, -15266474953566641587⟩, ⟨1256893413652983442331, 1256893413652991317798⟩⟩, ⟨⟨2996083840651559047157, 2996083840651572696254⟩, ⟨-1777873120685001141434, -1777873120684987491569⟩⟩, ⟨⟨-7361278998196151463709, -7361278998196130294604⟩, ⟨-3897543869395229112197, -3897543869395207945085⟩⟩, ⟨⟨1068030044383258668979, 1068030044383287873357⟩, ⟨17210849462886736646072, 17210849462886765850482⟩⟩, ⟨⟨25370063769446834237215, 25370063769446869895303⟩, ⟨-17788903246055422203234, -17788903246055386536151⟩⟩, ⟨⟨-44383463541917174030516, -44383463541917135671297⟩, ⟨-19243534761511439459720, -19243534761511401117079⟩⟩, ⟨⟨9265737140437754082222, 9265737140437790222630⟩, ⟨64950512278290682764575, 64950512278290718906886⟩⟩, ⟨⟨59364546325918471333881, 59364546325918500995076⟩, ⟨-49313471958341804747190, -49313471958341775058825⟩⟩, ⟨⟨-74380796014132466124063, -74380796014132445032093⟩, ⟨-25100747645832319253672, -25100747645832298198928⟩⟩, ⟨⟨15495258787684646001433, 15495258787684658836709⟩, ⟨66957774771624963166934, 66957774771624976007848⟩⟩, ⟨⟨36529330082288726167758, 36529330082288732795775⟩, ⟨-36213517158450512566879, -36213517158450505918671⟩⟩, ⟨⟨-31702110225763979367621, -31702110225763976485536⟩, ⟨-7599563085201019458515, -7599563085201016596962⟩⟩, ⟨⟨5433430250122920904998, 5433430250122921925927⟩, ⟨16392201732504156896424, 16392201732504157920169⟩⟩, ⟨⟨4804599446744562950525, 4804599446744563240348⟩, ⟨-5769143008889053200705, -5769143008889052907859⟩⟩, ⟨⟨-2585368074883313114841, -2585368074883313049992⟩, ⟨-356711521188381819666, -356711521188381756884⟩⟩, ⟨⟨285306437383014062111, 285306437383014072367⟩, ⟨636662610403673584787, 636662610403673595225⟩⟩, ⟨⟨74919230285892406650, 74919230285892407758⟩, ⟨-111900896126424159681, -111900896126424158520⟩⟩, ⟨⟨-16698321653832560370, -16698321653832560295⟩, ⟨-489386036010179942, -489386036010179882⟩⟩, ⟨⟨507692307692307691, 507692307692307693⟩, ⟨861538461538461537, 861538461538461539⟩⟩],
  [o],
  [⟨⟨-265723507642, -265723507515⟩, ⟨-287427956528, -287427956401⟩⟩, ⟨⟨-18877268535595, -18877268534480⟩, ⟨4103492307306, 4103492308420⟩⟩, ⟨⟨-143122165580834, -143122165575686⟩, ⟨434715277465272, 434715277470421⟩⟩, ⟨⟨4573239532614720, 4573239532631956⟩, ⟨5207163789883106, 5207163789900343⟩⟩, ⟨⟨74010710143092255, 74010710143141142⟩, ⟨-14129459060872180, -14129459060823296⟩⟩, ⟨⟨210865995452339521, 210865995452467589⟩, ⟨-589815977685167871, -589815977685039803⟩⟩, ⟨⟨-2653023078139376301, -2653023078139055189⟩, ⟨-3178720792319894998, -3178720792319573882⟩⟩, ⟨⟨-22043729417874270029, -22043729417873498953⟩, ⟨3638773699169223771, 3638773699169994817⟩⟩, ⟨⟨-36096620834003918957, -36096620834002173822⟩, ⟨93549072929243393001, 93549072929245138236⟩⟩, ⟨⟨235833814106619192827, 235833814106622847012⟩, ⟨297219844319346728996, 297219844319350383234⟩⟩, ⟨⟨1210913722234610980198, 1210913722234617951563⟩, ⟨-169415449372903558192, -169415449372896588347⟩⟩, ⟨⟨1293792989287419695942, 1293792989287431676435⟩, ⟨-3123717588543880586481, -3123717588543868603111⟩⟩, ⟨⟨-4859273612939533146566, -4859273612939514730107⟩, ⟨-6438612306234318244583, -6438612306234299827165⟩⟩, ⟨⟨-16558000486065587838367, -16558000486065562664785⟩, ⟨1911896652413761252806, 1911896652413786409975⟩⟩, ⟨⟨-12097736313438805938277, -12097736313438775527205⟩, ⟨27344903743882407294422, 27344903743882437726336⟩⟩, ⟨⟨27196839895359247421990, 27196839895359279794796⟩, ⟨37866904371038816486536, 37866904371038848862799⟩⟩, ⟨⟨62902554876745835480996, 62902554876745865678252⟩, ⟨-5771410084214628055189, -5771410084214597901862⟩⟩, ⟨⟨31616357618524246087646, 31616357618524270561486⟩, ⟨-67191987744565355187078, -67191987744565330674872⟩⟩, ⟨⟨-42628193782760669905673, -42628193782760652722767⟩, ⟨-62342704553889411233241, -62342704553889394048124⟩⟩, ⟨⟨-65985926941928070747050, -65985926941928060399005⟩, ⟨4530571911128470408341, 4530571911128480728740⟩⟩, ⟨⟨-22111490375974679188454, -22111490375974673927535⟩, ⟨44337554364448906160140, 44337554364448911436900⟩⟩, ⟨⟨17156218367459368430796, 17156218367459370674403⟩, ⟨26355892690654549466641, 26355892690654551710228⟩⟩, ⟨⟨16677616622840226814246, 16677616622840227599349⟩, ⟨-766074838368488913054, -766074838368488131093⟩⟩, ⟨⟨3395478526625941431123, 3395478526625941647942⟩, ⟨-6439462709322369153591, -6439462709322368935759⟩⟩, ⟨⟨-1337324501111458819111, -1337324501111458773096⟩, ⟨-2159910054561736857780, -2159910054561736811803⟩⟩, ⟨⟨-682235737715672783838, -682235737715672776769⟩, ⟨15818310548377301571, 15818310548377308615⟩⟩, ⟨⟨-64469580372390954978, -64469580372390954312⟩, ⟨115778678225348662189, 115778678225348662857⟩⟩, ⟨⟨8391542039892993314, 8391542039892993341⟩, ⟨14276250360404422168, 14276250360404422195⟩⟩, o],
  [o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨8699927901668692, 8699927901668709⟩, ⟨15708321213760380, 15708321213760397⟩⟩, ⟨⟨-35, 34⟩, ⟨-35, 36⟩⟩, ⟨⟨8228237942119543, 8228237942119725⟩, ⟨-17570683386650828, -17570683386650646⟩⟩, ⟨⟨-168, 167⟩, ⟨-167, 167⟩⟩, ⟨⟨-15125814987289297, -15125814987288843⟩, ⟨8961182327001291, 8961182327001742⟩⟩, ⟨⟨-227, 227⟩, ⟨-226, 228⟩⟩, ⟨⟨-478023105553576930, -478023105553576604⟩, ⟨-881602699197418838, -881602699197418505⟩⟩, ⟨⟨-81, 83⟩, ⟨-84, 82⟩⟩, ⟨⟨-523536982109451090, -523536982109451035⟩, ⟨874646625201052043, 874646625201052093⟩⟩, ⟨⟨-5, 5⟩, ⟨-3, 3⟩⟩, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨8616042089132154, 8616042089132171⟩, ⟨15556859580572768, 15556859580572784⟩⟩, ⟨⟨-36, 36⟩, ⟨-38, 37⟩⟩, ⟨⟨8147247930158890, 8147247930159082⟩, ⟨-17409618746135314, -17409618746135124⟩⟩, ⟨⟨-172, 172⟩, ⟨-173, 174⟩⟩, ⟨⟨-14965126592484946, -14965126592484490⟩, ⟨8924834381521039, 8924834381521494⟩⟩, ⟨⟨-220, 222⟩, ⟨-222, 220⟩⟩, ⟨⟨-477888096439062495, -477888096439062180⟩, ⟨-881286977522612887, -881286977522612569⟩⟩, ⟨⟨-80, 78⟩, ⟨-80, 80⟩⟩, ⟨⟨-523425518548995497, -523425518548995444⟩, ⟨874500375453367088, 874500375453367138⟩⟩, ⟨⟨-5, 5⟩, ⟨-3, 3⟩⟩, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨8533037967588219, 8533037967588236⟩, ⟨15406989901419674, 15406989901419690⟩⟩, ⟨⟨-35, 36⟩, ⟨-38, 36⟩⟩, ⟨⟨8067116935135053, 8067116935135245⟩, ⟨-17250186836101785, -17250186836101591⟩⟩, ⟨⟨-178, 180⟩, ⟨-177, 179⟩⟩, ⟨⟨-14806138913642278, -14806138913641797⟩, ⟨8888677101204060, 8888677101204537⟩⟩, ⟨⟨-235, 236⟩, ⟨-236, 235⟩⟩, ⟨⟨-477752990475954833, -477752990475954500⟩, ⟨-880971450126481342, -880971450126481004⟩⟩, ⟨⟨-83, 82⟩, ⟨-82, 83⟩⟩, ⟨⟨-523314171072717594, -523314171072717539⟩, ⟨874354150162161080, 874354150162161130⟩⟩, ⟨⟨-5, 5⟩, ⟨-3, 3⟩⟩, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨8450905626513710, 8450905626513726⟩, ⟨15258694282166433, 15258694282166448⟩⟩, ⟨⟨-35, 35⟩, ⟨-36, 37⟩⟩, ⟨⟨7987835272084935, 7987835272085125⟩, ⟨-17092369808514691, -17092369808514501⟩⟩, ⟨⟨-175, 177⟩, ⟨-177, 174⟩⟩, ⟨⟨-14648833111979611, -14648833111979138⟩, ⟨8852709301675801, 8852709301676271⟩⟩, ⟨⟨-230, 228⟩, ⟨-230, 230⟩⟩, ⟨⟨-477617788647040303, -477617788647039982⟩, ⟨-880656116528641245, -880656116528640917⟩⟩, ⟨⟨-79, 80⟩, ⟨-80, 80⟩⟩, ⟨⟨-523202939217535122, -523202939217535068⟩, ⟨874207949324365968, 874207949324366017⟩⟩, ⟨⟨-5, 5⟩, ⟨-3, 3⟩⟩, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨8369635272551787, 8369635272551805⟩, ⟨15111955040230299, 15111955040230315⟩⟩, ⟨⟨-37, 37⟩, ⟨-39, 38⟩⟩, ⟨⟨7909393370473265, 7909393370473465⟩, ⟨-16936150021562664, -16936150021562465⟩⟩, ⟨⟨-181, 179⟩, ⟨-179, 178⟩⟩, ⟨⟨-14493190566776188, -14493190566775717⟩, ⟨8816929806741111, 8816929806741579⟩⟩, ⟨⟨-226, 229⟩, ⟨-226, 227⟩⟩, ⟨⟨-477482491927797999, -477482491927797675⟩, ⟨-880340976250840914, -880340976250840588⟩⟩, ⟨⟨-82, 81⟩, ⟨-83, 81⟩⟩, ⟨⟨-523091822522468742, -523091822522468687⟩, ⟨874061772936913696, 874061772936913746⟩⟩, ⟨⟨-5, 5⟩, ⟨-3, 3⟩⟩, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨8289217228077532, 8289217228077549⟩, ⟨14966754701990508, 14966754701990526⟩⟩, ⟨⟨-38, 38⟩, ⟨-38, 38⟩⟩, ⟨⟨7831781772796260, 7831781772796463⟩, ⟨-16781510037183943, -16781510037183741⟩⟩, ⟨⟨-181, 182⟩, ⟨-182, 182⟩⟩, ⟨⟨-14339192872765191, -14339192872764719⟩, ⟨8781337448324719, 8781337448325189⟩⟩, ⟨⟨-225, 225⟩, ⟨-224, 224⟩⟩, ⟨⟨-477347101286455650, -477347101286455338⟩, ⟨-880026028816951323, -880026028816951004⟩⟩, ⟨⟨-78, 78⟩, ⟨-80, 81⟩⟩, ⟨⟨-522980820528634162, -522980820528634108⟩, ⟨873915620996736213, 873915620996736262⟩⟩, ⟨⟨-5, 5⟩, ⟨-3, 3⟩⟩, o]
]

private def st10_8 : List (List CFpIv) := [
  [o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-6158601678849939, -6158601678849892⟩, ⟨-21, 21⟩⟩, ⟨⟨-46, 45⟩, ⟨-47, 47⟩⟩, ⟨⟨1215722580806784, 1215722580806915⟩, ⟨-67, 68⟩⟩, ⟨⟨-76, 74⟩, ⟨-74, 73⟩⟩, ⟨⟨-7762758849240702, -7762758849240566⟩, ⟨-69, 68⟩⟩, ⟨⟨-52, 52⟩, ⟨-53, 52⟩⟩, ⟨⟨150144744828, 150144744895⟩, ⟨-33, 36⟩⟩, ⟨⟨-21, 22⟩, ⟨-21, 21⟩⟩, ⟨⟨-93936308, -93936280⟩, ⟨-13, 15⟩⟩, ⟨⟨-7, 7⟩, ⟨-7, 7⟩⟩, ⟨⟨1883763, 1883768⟩, ⟨-3, 2⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-6159368101542351, -6159368101542305⟩, ⟨-20, 21⟩⟩, ⟨⟨-47, 47⟩, ⟨-48, 47⟩⟩, ⟨⟨1216024678990239, 1216024678990379⟩, ⟨-70, 69⟩⟩, ⟨⟨-80, 79⟩, ⟨-79, 80⟩⟩, ⟨⟨-7765652421193045, -7765652421192900⟩, ⟨-72, 72⟩⟩, ⟨⟨-55, 52⟩, ⟨-54, 53⟩⟩, ⟨⟨150229554316, 150229554384⟩, ⟨-35, 35⟩⟩, ⟨⟨-22, 21⟩, ⟨-22, 20⟩⟩, ⟨⟨-94007434, -94007408⟩, ⟨-13, 13⟩⟩, ⟨⟨-7, 7⟩, ⟨-8, 7⟩⟩, ⟨⟨1885551, 1885556⟩, ⟨-2, 3⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-6160134651779189, -6160134651779143⟩, ⟨-21, 21⟩⟩, ⟨⟨-46, 44⟩, ⟨-50, 49⟩⟩, ⟨⟨1216326864811423, 1216326864811562⟩, ⟨-71, 70⟩⟩, ⟨⟨-80, 79⟩, ⟨-78, 77⟩⟩, ⟨⟨-7768547192111371, -7768547192111225⟩, ⟨-73, 72⟩⟩, ⟨⟨-57, 56⟩, ⟨-57, 57⟩⟩, ⟨⟨150314416804, 150314416878⟩, ⟨-38, 39⟩⟩, ⟨⟨-24, 24⟩, ⟨-22, 23⟩⟩, ⟨⟨-94078621, -94078594⟩, ⟨-13, 12⟩⟩, ⟨⟨-7, 7⟩, ⟨-7, 6⟩⟩, ⟨⟨1887342, 1887346⟩, ⟨-3, 2⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-6160901329585472, -6160901329585427⟩, ⟨-21, 20⟩⟩, ⟨⟨-46, 45⟩, ⟨-44, 47⟩⟩, ⟨⟨1216629138298757, 1216629138298890⟩, ⟨-66, 69⟩⟩, ⟨⟨-75, 75⟩, ⟨-74, 74⟩⟩, ⟨⟨-7771443162536195, -7771443162536060⟩, ⟨-68, 67⟩⟩, ⟨⟨-52, 51⟩, ⟨-52, 50⟩⟩, ⟨⟨150399332336, 150399332404⟩, ⟨-35, 36⟩⟩, ⟨⟨-21, 22⟩, ⟨-22, 22⟩⟩, ⟨⟨-94149866, -94149840⟩, ⟨-13, 12⟩⟩, ⟨⟨-8, 7⟩, ⟨-7, 6⟩⟩, ⟨⟨1889132, 1889138⟩, ⟨-3, 2⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-6161668134986226, -6161668134986180⟩, ⟨-21, 21⟩⟩, ⟨⟨-47, 45⟩, ⟨-47, 46⟩⟩, ⟨⟨1216931499480676, 1216931499480809⟩, ⟨-67, 66⟩⟩, ⟨⟨-74, 73⟩, ⟨-74, 73⟩⟩, ⟨⟨-7774340333008303, -7774340333008169⟩, ⟨-66, 67⟩⟩, ⟨⟨-50, 51⟩, ⟨-50, 52⟩⟩, ⟨⟨150484300939, 150484301006⟩, ⟨-34, 35⟩⟩, ⟨⟨-22, 21⟩, ⟨-19, 20⟩⟩, ⟨⟨-94221169, -94221142⟩, ⟨-12, 12⟩⟩, ⟨⟨-6, 7⟩, ⟨-7, 7⟩⟩, ⟨⟨1890927, 1890932⟩, ⟨-2, 3⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-6162435068006480, -6162435068006433⟩, ⟨-21, 21⟩⟩, ⟨⟨-47, 46⟩, ⟨-48, 48⟩⟩, ⟨⟨1217233948385626, 1217233948385763⟩, ⟨-69, 68⟩⟩, ⟨⟨-76, 77⟩, ⟨-76, 76⟩⟩, ⟨⟨-7777238704068729, -7777238704068589⟩, ⟨-70, 71⟩⟩, ⟨⟨-51, 54⟩, ⟨-53, 55⟩⟩, ⟨⟨150569322653, 150569322722⟩, ⟨-35, 33⟩⟩, ⟨⟨-21, 20⟩, ⟨-20, 22⟩⟩, ⟨⟨-94292532, -94292505⟩, ⟨-13, 11⟩⟩, ⟨⟨-7, 6⟩, ⟨-7, 7⟩⟩, ⟨⟨1892723, 1892726⟩, ⟨-2, 2⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-6163202128671266, -6163202128671218⟩, ⟨-20, 21⟩⟩, ⟨⟨-44, 45⟩, ⟨-47, 48⟩⟩, ⟨⟨1217536485042071, 1217536485042203⟩, ⟨-66, 68⟩⟩, ⟨⟨-73, 77⟩, ⟨-77, 75⟩⟩, ⟨⟨-7780138276258767, -7780138276258626⟩, ⟨-74, 72⟩⟩, ⟨⟨-56, 56⟩, ⟨-54, 55⟩⟩, ⟨⟨150654397513, 150654397587⟩, ⟨-35, 36⟩⟩, ⟨⟨-22, 22⟩, ⟨-23, 22⟩⟩, ⟨⟨-94363956, -94363928⟩, ⟨-13, 14⟩⟩, ⟨⟨-7, 7⟩, ⟨-7, 6⟩⟩, ⟨⟨1894519, 1894524⟩, ⟨-2, 3⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-6163969317005624, -6163969317005577⟩, ⟨-21, 21⟩⟩, ⟨⟨-46, 47⟩, ⟨-48, 48⟩⟩, ⟨⟨1217839109478465, 1217839109478600⟩, ⟨-69, 70⟩⟩, ⟨⟨-78, 78⟩, ⟨-78, 77⟩⟩, ⟨⟨-7783039050119980, -7783039050119833⟩, ⟨-72, 73⟩⟩, ⟨⟨-57, 57⟩, ⟨-58, 58⟩⟩, ⟨⟨150739525558, 150739525635⟩, ⟨-38, 40⟩⟩, ⟨⟨-23, 25⟩, ⟨-22, 24⟩⟩, ⟨⟨-94435434, -94435407⟩, ⟨-13, 12⟩⟩, ⟨⟨-8, 7⟩, ⟨-7, 7⟩⟩, ⟨⟨1896318, 1896322⟩, ⟨-2, 3⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-6164736633034599, -6164736633034554⟩, ⟨-21, 21⟩⟩, ⟨⟨-45, 46⟩, ⟨-47, 47⟩⟩, ⟨⟨1218141821723296, 1218141821723429⟩, ⟨-67, 70⟩⟩, ⟨⟨-77, 79⟩, ⟨-76, 77⟩⟩, ⟨⟨-7785941026194177, -7785941026194038⟩, ⟨-71, 70⟩⟩, ⟨⟨-53, 52⟩, ⟨-52, 52⟩⟩, ⟨⟨150824706828, 150824706895⟩, ⟨-34, 37⟩⟩, ⟨⟨-22, 22⟩, ⟨-22, 23⟩⟩, ⟨⟨-94506976, -94506948⟩, ⟨-13, 14⟩⟩, ⟨⟨-7, 7⟩, ⟨-7, 8⟩⟩, ⟨⟨1898119, 1898123⟩, ⟨-3, 3⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-6165504076783243, -6165504076783195⟩, ⟨-21, 21⟩⟩, ⟨⟨-47, 48⟩, ⟨-47, 47⟩⟩, ⟨⟨1218444621805046, 1218444621805178⟩, ⟨-68, 67⟩⟩, ⟨⟨-75, 74⟩, ⟨-74, 74⟩⟩, ⟨⟨-7788844205023450, -7788844205023314⟩, ⟨-67, 69⟩⟩, ⟨⟨-53, 52⟩, ⟨-51, 52⟩⟩, ⟨⟨150909941350, 150909941419⟩, ⟨-36, 33⟩⟩, ⟨⟨-23, 22⟩, ⟨-22, 22⟩⟩, ⟨⟨-94578574, -94578547⟩, ⟨-13, 12⟩⟩, ⟨⟨-5, 7⟩, ⟨-6, 6⟩⟩, ⟨⟨1899921, 1899926⟩, ⟨-2, 2⟩⟩, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-6166271648276612, -6166271648276566⟩, ⟨-21, 21⟩⟩, ⟨⟨-45, 46⟩, ⟨-47, 48⟩⟩, ⟨⟨1218747509752206, 1218747509752345⟩, ⟨-70, 69⟩⟩, ⟨⟨-80, 82⟩, ⟨-79, 79⟩⟩, ⟨⟨-7791748587150145, -7791748587149998⟩, ⟨-73, 71⟩⟩, ⟨⟨-56, 54⟩, ⟨-57, 54⟩⟩, ⟨⟨150995229165, 150995229236⟩, ⟨-36, 37⟩⟩, ⟨⟨-22, 23⟩, ⟨-22, 23⟩⟩, ⟨⟨-94650232, -94650205⟩, ⟨-14, 13⟩⟩, ⟨⟨-7, 8⟩, ⟨-7, 6⟩⟩, ⟨⟨1901726, 1901730⟩, ⟨-3, 2⟩⟩, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-6167039347539763, -6167039347539716⟩, ⟨-22, 23⟩⟩, ⟨⟨-50, 49⟩, ⟨-48, 51⟩⟩, ⟨⟨1219050485593291, 1219050485593432⟩, ⟨-72, 70⟩⟩, ⟨⟨-76, 76⟩, ⟨-77, 77⟩⟩, ⟨⟨-7794654173116848, -7794654173116710⟩, ⟨-69, 68⟩⟩, ⟨⟨-51, 53⟩, ⟨-51, 52⟩⟩, ⟨⟨151080570312, 151080570380⟩, ⟨-35, 35⟩⟩, ⟨⟨-23, 22⟩, ⟨-22, 22⟩⟩, ⟨⟨-94721950, -94721923⟩, ⟨-13, 14⟩⟩, ⟨⟨-7, 7⟩, ⟨-7, 7⟩⟩, ⟨⟨1903532, 1903537⟩, ⟨-3, 2⟩⟩, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-6167807174597767, -6167807174597720⟩, ⟨-21, 21⟩⟩, ⟨⟨-46, 48⟩, ⟨-49, 47⟩⟩, ⟨⟨1219353549356816, 1219353549356955⟩, ⟨-72, 68⟩⟩, ⟨⟨-79, 79⟩, ⟨-79, 79⟩⟩, ⟨⟨-7797560963466445, -7797560963466299⟩, ⟨-72, 72⟩⟩, ⟨⟨-55, 56⟩, ⟨-55, 55⟩⟩, ⟨⟨151165964821, 151165964894⟩, ⟨-37, 37⟩⟩, ⟨⟨-22, 23⟩, ⟨-22, 21⟩⟩, ⟨⟨-94793727, -94793700⟩, ⟨-13, 14⟩⟩, ⟨⟨-7, 7⟩, ⟨-6, 7⟩⟩, ⟨⟨1905341, 1905345⟩, ⟨-3, 2⟩⟩, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-6168575129475692, -6168575129475647⟩, ⟨-21, 21⟩⟩, ⟨⟨-47, 46⟩, ⟨-47, 46⟩⟩, ⟨⟨1219656701071310, 1219656701071443⟩, ⟨-68, 68⟩⟩, ⟨⟨-77, 77⟩, ⟨-77, 78⟩⟩, ⟨⟨-7800468958742046, -7800468958741904⟩, ⟨-72, 72⟩⟩, ⟨⟨-56, 56⟩, ⟨-54, 56⟩⟩, ⟨⟨151251412734, 151251412809⟩, ⟨-37, 37⟩⟩, ⟨⟨-23, 23⟩, ⟨-23, 23⟩⟩, ⟨⟨-94865563, -94865536⟩, ⟨-13, 13⟩⟩, ⟨⟨-5, 6⟩, ⟨-6, 7⟩⟩, ⟨⟨1907151, 1907155⟩, ⟨-2, 2⟩⟩, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-6169343212198617, -6169343212198570⟩, ⟨-21, 21⟩⟩, ⟨⟨-46, 46⟩, ⟨-47, 46⟩⟩, ⟨⟨1219959940765301, 1219959940765433⟩, ⟨-68, 69⟩⟩, ⟨⟨-75, 74⟩, ⟨-75, 74⟩⟩, ⟨⟨-7803378159487046, -7803378159486910⟩, ⟨-67, 66⟩⟩, ⟨⟨-51, 50⟩, ⟨-51, 51⟩⟩, ⟨⟨151336914091, 151336914158⟩, ⟨-32, 34⟩⟩, ⟨⟨-20, 21⟩, ⟨-20, 20⟩⟩, ⟨⟨-94937459, -94937432⟩, ⟨-12, 11⟩⟩, ⟨⟨-7, 6⟩, ⟨-6, 6⟩⟩, ⟨⟨1908962, 1908966⟩, ⟨-1, 2⟩⟩, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-6170111422791624, -6170111422791578⟩, ⟨-20, 21⟩⟩, ⟨⟨-45, 44⟩, ⟨-46, 47⟩⟩, ⟨⟨1220263268467341, 1220263268467471⟩, ⟨-67, 67⟩⟩, ⟨⟨-74, 73⟩, ⟨-74, 73⟩⟩, ⟨⟨-7806288566245098, -7806288566244963⟩, ⟨-70, 67⟩⟩, ⟨⟨-52, 52⟩, ⟨-54, 54⟩⟩, ⟨⟨151422468918, 151422468991⟩, ⟨-36, 36⟩⟩, ⟨⟨-23, 23⟩, ⟨-22, 23⟩⟩, ⟨⟨-95009414, -95009387⟩, ⟨-14, 14⟩⟩, ⟨⟨-7, 7⟩, ⟨-7, 7⟩⟩, ⟨⟨1910776, 1910781⟩, ⟨-2, 2⟩⟩, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-6170879761279801, -6170879761279753⟩, ⟨-21, 21⟩⟩, ⟨⟨-47, 46⟩, ⟨-48, 47⟩⟩, ⟨⟨1220566684205982, 1220566684206117⟩, ⟨-68, 68⟩⟩, ⟨⟨-77, 76⟩, ⟨-76, 76⟩⟩, ⟨⟨-7809200179560115, -7809200179559976⟩, ⟨-71, 70⟩⟩, ⟨⟨-52, 55⟩, ⟨-52, 53⟩⟩, ⟨⟨151508077262, 151508077331⟩, ⟨-36, 35⟩⟩, ⟨⟨-20, 22⟩, ⟨-20, 21⟩⟩, ⟨⟨-95081427, -95081402⟩, ⟨-13, 11⟩⟩, ⟨⟨-6, 6⟩, ⟨-5, 7⟩⟩, ⟨⟨1912592, 1912597⟩, ⟨-2, 2⟩⟩, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-6171648227688240, -6171648227688193⟩, ⟨-21, 20⟩⟩, ⟨⟨-47, 46⟩, ⟨-47, 47⟩⟩, ⟨⟨1220870188009799, 1220870188009933⟩, ⟨-67, 67⟩⟩, ⟨⟨-75, 75⟩, ⟨-74, 75⟩⟩, ⟨⟨-7812112999976266, -7812112999976129⟩, ⟨-68, 69⟩⟩, ⟨⟨-54, 51⟩, ⟨-52, 53⟩⟩, ⟨⟨151593739154, 151593739224⟩, ⟨-35, 37⟩⟩, ⟨⟨-22, 24⟩, ⟨-23, 22⟩⟩, ⟨⟨-95153504, -95153475⟩, ⟨-14, 14⟩⟩, ⟨⟨-8, 7⟩, ⟨-7, 8⟩⟩, ⟨⟨1914409, 1914414⟩, ⟨-2, 3⟩⟩, z, z, z],
  [⟨⟨0, 1⟩, ⟨0, 0⟩⟩, ⟨⟨-13, 3⟩, ⟨-4, 4⟩⟩, ⟨⟨-39, 73⟩, ⟨-48, 49⟩⟩, ⟨⟨-303, 221⟩, ⟨-253, 251⟩⟩, ⟨⟨-844, 993⟩, ⟨-911, 909⟩⟩, ⟨⟨-2610, 2355⟩, ⟨-2471, 2479⟩⟩, ⟨⟨-4063, 6703⟩, ⟨-5378, 5368⟩⟩, ⟨⟨-91731, -72246⟩, ⟨-9726, 9730⟩⟩, ⟨⟨4573339, 4603955⟩, ⟨-15290, 15289⟩⟩, ⟨⟨-208679017, -208635658⟩, ⟨-21661, 21659⟩⟩, ⟨⟨7723066408, 7723123581⟩, ⟨-28560, 28562⟩⟩, ⟨⟨-232524910450, -232524838533⟩, ⟨-35927, 35927⟩⟩, ⟨⟨5667400867483, 5667400955127⟩, ⟨-43794, 43793⟩⟩, ⟨⟨-110779424469225, -110779424364849⟩, ⟨-52159, 52162⟩⟩, ⟨⟨1710840891141318, 1710840891263249⟩, ⟨-60935, 60929⟩⟩, ⟨⟨-20418165055100079, -20418165054960278⟩, ⟨-69860, 69863⟩⟩, ⟨⟨182388283719262830, 182388283719420111⟩, ⟨-78594, 78595⟩⟩, ⟨⟨-1165523556686241511, -1165523556686067495⟩, ⟨-86955, 86953⟩⟩, ⟨⟨5020222015924723710, 5020222015924914383⟩, ⟨-95302, 95304⟩⟩, ⟨⟨-13808388791143293036, -13808388791143084133⟩, ⟨-104461, 104462⟩⟩, ⟨⟨25280925371838363953, 25280925371838593371⟩, ⟨-114727, 114720⟩⟩, ⟨⟨-32067915349264291213, -32067915349264042839⟩, ⟨-124155, 124165⟩⟩, ⟨⟨28496027223773498781, 28496027223773754406⟩, ⟨-127768, 127758⟩⟩, ⟨⟨-16612624945344099735, -16612624945343860208⟩, ⟨-119726, 119737⟩⟩, ⟨⟨2357833691986461722, 2357833691986658555⟩, ⟨-98414, 98405⟩⟩, ⟨⟨11092775836007998681, 11092775836008136711⟩, ⟨-69008, 69017⟩⟩, ⟨⟨-22059519444519503997, -22059519444519422978⟩, ⟨-40498, 40490⟩⟩, ⟨⟨26699954537864343898, 26699954537864383057⟩, ⟨-19553, 19555⟩⟩, ⟨⟨-22535731040242225096, -22535731040242209806⟩, ⟨-7616, 7622⟩⟩, ⟨⟨13156891965796681901, 13156891965796686587⟩, ⟨-2329, 2319⟩⟩, ⟨⟨-5033437053554728056, -5033437053554726984⟩, ⟨-522, 531⟩⟩, ⟨⟨1125505392989494991, 1125505392989495157⟩, ⟨-82, 78⟩⟩, ⟨⟨-110571477954275300, -110571477954275286⟩, ⟨-6, 7⟩⟩],
  [o],
  [⟨⟨-5, 5⟩, ⟨-5, 5⟩⟩, ⟨⟨-91, 91⟩, ⟨-91, 91⟩⟩, ⟨⟨-643, 643⟩, ⟨-643, 643⟩⟩, ⟨⟨-2956, 2956⟩, ⟨-2956, 2956⟩⟩, ⟨⟨-9870, 9870⟩, ⟨-9870, 9870⟩⟩, ⟨⟨-25473, 25502⟩, ⟨-25493, 25482⟩⟩, ⟨⟨-54240, 52342⟩, ⟨-54003, 52581⟩⟩, ⟨⟨-102277, 84735⟩, ⟨-12098, 174920⟩⟩, ⟨⟨4038474, 4322326⟩, ⟨-2035319, -1751475⟩⟩, ⟨⟨-170874913, -170492566⟩, ⟨-120271515, -119889160⟩⟩, ⟨⟨-622833468, -622366278⟩, ⟨7699328816, 7699796007⟩⟩, ⟨⟨209259540555, 209260069437⟩, ⟨-101520879862, -101520350992⟩⟩, ⟨⟨-4721025432563, -4721024863891⟩, ⟨-3138917222560, -3138916653898⟩⟩, ⟨⟨-6034379719865, -6034379121190⟩, ⟨110662984579613, 110662985178295⟩⟩, ⟨⟨1520166589057655, 1520166589693320⟩, ⟨-787044597237146, -787044596601463⟩⟩, ⟨⟨-17302468613758803, -17302468613066422⟩, ⟨-10871357385979571, -10871357385287205⟩⟩, ⟨⟨-5315748163006878, -5315748162235006⟩, ⟨182519742179415232, 182519742180187102⟩⟩, ⟨⟨1023356615040824196, 1023356615041691856⟩, ⟨-562159466843887863, -562159466843020203⟩⟩, ⟨⟨-4324489076676125052, -4324489076675156747⟩, ⟨-2579785653763476516, -2579785653762508211⟩⟩, ⟨⟨-125723673518393967, -125723673517332059⟩, ⟨13888227877883696665, 13888227877884758592⟩⟩, ⟨⟨22221228568276810871, 22221228568277943934⟩, ⟨-12643152696644983648, -12643152696643850605⟩⟩, ⟨⟨-28216194731509486007, -28216194731508332174⟩, ⟨-16570142520567045557, -16570142520565891726⟩⟩, ⟨⟨-482473849431512936, -482473849430425860⟩, ⟨29452725902001916445, 29452725902003003525⟩⟩, ⟨⟨15518758968506763350, 15518758968507677183⟩, ⟨-7980537717381060684, -7980537717380146845⟩⟩, ⟨⟨-1629026838598619289, -1629026838597956507⟩, ⟨-2210741329308956675, -2210741329308293895⟩⟩, ⟨⟨-1058301163214234276, -1058301163213831059⟩, ⟨-11671069717900027663, -11671069717899624455⟩⟩, ⟨⟨-19451628622905900958, -19451628622905699970⟩, ⟨12170773206345427624, 12170773206345628624⟩⟩, ⟨⟨23985474519545719307, 23985474519545799802⟩, ⟨13188711522423384901, 13188711522423465391⟩⟩, ⟨⟨-396581508238808355, -396581508238782810⟩, ⟨-22845949512126866848, -22845949512126841304⟩⟩, ⟨⟨-11344379277106563489, -11344379277106557071⟩, ⟨6836441047803936122, 6836441047803942541⟩⟩, ⟨⟨4427115057197801532, 4427115057197802836⟩, ⟨2422843814173002426, 2422843814173003729⟩⟩, ⟨⟨-32300992114036183, -32300992114035971⟩, ⟨-1125819538695340756, -1125819538695340544⟩⟩, ⟨⟨-93725398137987329, -93725398137987306⟩, ⟨58666012273755547, 58666012273755570⟩⟩],
  [o],
  [⟨⟨-5, 5⟩, ⟨-5, 5⟩⟩, ⟨⟨-91, 91⟩, ⟨-91, 91⟩⟩, ⟨⟨-641, 641⟩, ⟨-641, 641⟩⟩, ⟨⟨-2933, 2933⟩, ⟨-2933, 2933⟩⟩, ⟨⟨-9739, 9739⟩, ⟨-9739, 9739⟩⟩, ⟨⟨-25058, 25069⟩, ⟨-25078, 25049⟩⟩, ⟨⟨-53073, 51649⟩, ⟨-53309, 51410⟩⟩, ⟨⟨-173451, 10628⟩, ⟨-83270, 100813⟩⟩, ⟨⟨-2033562, -1753233⟩, ⟨4040236, 4320559⟩⟩, ⟨⟨119890924, 120269749⟩, ⟨170494324, 170873155⟩⟩, ⟨⟨7699330477, 7699794353⟩, ⟨-622831806, -622367936⟩⟩, ⟨⟨101520352615, 101520878264⟩, ⟨-209260067819, -209259542168⟩⟩, ⟨⟨-3138917220974, -3138916655457⟩, ⟨-4721025431003, -4721024865474⟩⟩, ⟨⟨-110662985176870, -110662984581029⟩, ⟨6034379122603, 6034379718424⟩⟩, ⟨⟨-787044597235989, -787044596602636⟩, ⟨1520166589058793, 1520166589692152⟩⟩, ⟨⟨10871357385288057, 10871357385978682⟩, ⟨17302468613067296, 17302468613757937⟩⟩, ⟨⟨182519742179415900, 182519742180186425⟩, ⟨-5315748163006185, -5315748162235674⟩⟩, ⟨⟨562159466843020906, 562159466843887149⟩, ⟨-1023356615041691139, -1023356615040824895⟩⟩, ⟨⟨-2579785653763475498, -2579785653762509241⟩, ⟨-4324489076676124018, -4324489076675157757⟩⟩, ⟨⟨-13888227877884757128, -13888227877883698125⟩, ⟨125723673517333540, 125723673518392528⟩⟩, ⟨⟨-12643152696644981981, -12643152696643852246⟩, ⟨22221228568276812540, 22221228568277942288⟩⟩, ⟨⟨16570142520565893029, 16570142520567044275⟩, ⟨28216194731508333469, 28216194731509484718⟩⟩, ⟨⟨29452725902001916869, 29452725902003003118⟩, ⟨-482473849431512525, -482473849430426284⟩⟩, ⟨⟨7980537717380146371, 7980537717381061154⟩, ⟨-15518758968507677675, -15518758968506762884⟩⟩, ⟨⟨-2210741329308957522, -2210741329308293072⟩, ⟨-1629026838598620132, -1629026838597955680⟩⟩, ⟨⟨11671069717899623840, 11671069717900028250⟩, ⟨1058301163213830473, 1058301163214234876⟩⟩, ⟨⟨12170773206345427487, 12170773206345628776⟩, ⟨-19451628622905901098, -19451628622905699803⟩⟩, ⟨⟨-13188711522423465246, -13188711522423385024⟩, ⟨-23985474519545799674, -23985474519545719456⟩⟩, ⟨⟨-22845949512126866674, -22845949512126841497⟩, ⟨-396581508238808185, -396581508238783004⟩⟩, ⟨⟨-6836441047803942441, -6836441047803936239⟩, ⟨11344379277106557182, 11344379277106563383⟩⟩, ⟨⟨2422843814173002459, 2422843814173003690⟩, ⟨4427115057197801575, 4427115057197802803⟩⟩, ⟨⟨1125819538695340551, 1125819538695340749⟩, ⟨32300992114035981, 32300992114036178⟩⟩, ⟨⟨58666012273755548, 58666012273755570⟩, ⟨-93725398137987329, -93725398137987306⟩⟩],
  [o],
  [⟨⟨391436540786, 391436540797⟩, ⟨-3, 4⟩⟩, ⟨⟨-20881715086830, -20881715086681⟩, ⟨-55, 47⟩⟩, ⟨⟨537177763773230, 537177763774112⟩, ⟨-312, 346⟩⟩, ⟨⟨-8875580662744562, -8875580662741193⟩, ⟨-1374, 1281⟩⟩, ⟨⟨105845209086625936, 105845209086635582⟩, ⟨-3842, 4021⟩⟩, ⟨⟨-970642050829988187, -970642050829965395⟩, ⟨-9606, 9344⟩⟩, ⟨⟨7121119476878065151, 7121119476878113008⟩, ⟨-19939, 20247⟩⟩, ⟨⟨-42933752451608344326, -42933752451608249786⟩, ⟨-39953, 39660⟩⟩, ⟨⟨216847283025136895702, 216847283025137078593⟩, ⟨-76754, 76966⟩⟩, ⟨⟨-930677540478003376826, -930677540478003021505⟩, ⟨-148801, 148702⟩⟩, ⟨⟨3431055127106184994151, 3431055127106185695348⟩, ⟨-293021, 293050⟩⟩, ⟨⟨-10955873782895451881999, -10955873782895450482555⟩, ⟨-587316, 587245⟩⟩, ⟨⟨30495806263123233214916, 30495806263123235987043⟩, ⟨-1176589, 1176822⟩⟩, ⟨⟨-74359639864057616927866, -74359639864057611617316⟩, ⟨-2293396, 2292951⟩⟩, ⟨⟨159415755398359733029758, 159415755398359742623972⟩, ⟨-4225908, 4226499⟩⟩, ⟨⟨-301268278766983243499870, -301268278766983227480395⟩, ⟨-7198522, 7197926⟩⟩, ⟨⟨502714797696355622252874, 502714797696355646610617⟩, ⟨-11142477, 11142969⟩⟩, ⟨⟨-741252297461466636575570, -741252297461466603202715⟩, ⟨-15494900, 15494521⟩⟩, ⟨⟨965684507540083507919987, 965684507540083548801842⟩, ⟨-19195693, 19196022⟩⟩, ⟨⟨-1110414653432087289647441, -1110414653432087245151868⟩, ⟨-21052358, 21052046⟩⟩, ⟨⟨1124730108624807946634968, 1124730108624807989417676⟩, ⟨-20324938, 20325191⟩⟩, ⟨⟨-1000417136556333414815169, -1000417136556333378686848⟩, ⟨-17178360, 17178238⟩⟩, ⟨⟨778006338677187398682219, 778006338677187425303287⟩, ⟨-12630808, 12630765⟩⟩, ⟨⟨-525869003661922546959753, -525869003661922529974883⟩, ⟨-8019470, 8019649⟩⟩, ⟨⟨306503445350889261688213, 306503445350889270983813⟩, ⟨-4356639, 4356396⟩⟩, ⟨⟨-152444323501233195872316, -152444323501233191559545⟩, ⟨-2001212, 2001446⟩⟩, ⟨⟨63802042536544006690109, 63802042536544008360921⟩, ⟨-765845, 765662⟩⟩, ⟨⟨-22046660033857103247479, -22046660033857102717715⟩, ⟨-239069, 239190⟩⟩, ⟨⟨6123814704497273943294, 6123814704497274077038⟩, ⟨-59298, 59232⟩⟩, ⟨⟨-1314308552146498315797, -1314308552146498289919⟩, ⟨-11198, 11229⟩⟩, ⟨⟨204565483378936927851, 204565483378936931510⟩, ⟨-1552, 1536⟩⟩, ⟨⟨-20545241641328832093, -20545241641328831728⟩, ⟨-146, 154⟩⟩, ⟨⟨999498453579180901, 999498453579180926⟩, ⟨-11, 9⟩⟩],
  [o],
  [⟨⟨-287427956521, -287427956409⟩, ⟨-265723507637, -265723507524⟩⟩, ⟨⟨-4435474908521, -4435474906893⟩, ⟨20407220725994, 20407220727621⟩⟩, ⟨⟨510322998606714, 510322998618267⟩, ⟨-168049243262412, -168049243250857⟩⟩, ⟨⟨-6671327456036590, -6671327455981521⟩, ⟨-5857962117157828, -5857962117102762⟩⟩, ⟨⟨-19841173662538205, -19841173662335649⟩, ⟨104012545237533124, 104012545237735676⟩⟩, ⟨⟨914397968687842905, 914397968688470644⟩, ⟨-327117964172266372, -327117964171638628⟩⟩, ⟨⟨-5471892938554064334, -5471892938552321184⟩, ⟨-4564451456570810519, -4564451456569067364⟩⟩, ⟨⟨-6983246431133761417, -6983246431129251723⟩, ⟨42395744866851706317, 42395744866856216001⟩⟩, ⟨⟨202459171182768564526, 202459171182779615953⟩, ⟨-78221444447290576636, -78221444447279525214⟩⟩, ⟨⟨-730129826880601072824, -730129826880575446654⟩, ⟨-578694774539990569366, -578694774539964943216⟩⟩, ⟨⟨-473738443210698831072, -473738443210643172785⟩, ⟨3402312635209460352487, 3402312635209516010978⟩⟩, ⟨⟨10132182375910577753175, 10132182375910689640527⟩, ⟨-4205941966208627758209, -4205941966208515871514⟩⟩, ⟨⟨-24394636633372806212009, -24394636633372600117371⟩, ⟨-18374904835468285615913, -18374904835468079522260⟩⟩, ⟨⟨-8461148346228207825911, -8461148346227862594160⟩, ⟨73997177287106774113387, 73997177287107119352082⟩⟩, ⟨⟨145955583233194906973415, 145955583233195429975100⟩, ⟨-64798680797351755920179, -64798680797351232932057⟩⟩, ⟨⟨-245414372791711177365752, -245414372791710463832835⟩, ⟨-175705084384713208392488, -175705084384712494867813⟩⟩, ⟨⟨-45160169004355608837151, -45160169004354735359404⟩, ⟨501674223938668628176759, 501674223938669501714283⟩⟩, ⟨⟨671469988840746893914894, 671469988840747849898135⟩, ⟨-317554086621591613744879, -317554086621590657844789⟩⟩, ⟨⟨-800033598556445528190954, -800033598556444596067312⟩, ⟨-544467391680855478684522, -544467391680854546565764⟩⟩, ⟨⟨-73512775595734820541759, -73512775595734014009263⟩, ⟨1110375982058986309041295, 1110375982058987115710261⟩⟩, ⟨⟨1007326855023741685442416, 1007326855023742301650562⟩, ⟨-505751575453146643594120, -505751575453146027539740⟩⟩, ⟨⟨-841821404193699017780068, -841821404193698604335756⟩, ⟨-544471174445829833667094, -544471174445829420187010⟩⟩, ⟨⟨-33312698533470486241404, -33312698533470244092495⟩, ⟨778906580658325823289114, 778906580658326065510419⟩⟩, ⟨⟨465251601319255533110249, 465251601319255655791427⟩, ⟨-247328637911418669658828, -247328637911418547052303⟩⟩, ⟨⟨-261646608887492599136136, -261646608887492545915482⟩, ⟨-160720048052860868112753, -160720048052860814867134⟩⟩, ⟨⟨-2976024191111325133886, -2976024191111305568986⟩, ⟨152669476089729333698704, 152669476089729353268370⟩⟩, ⟨⟨55705996832849291782899, 55705996832849297759858⟩, ⟨-31296822441484805196952, -31296822441484799227025⟩⟩, ⟨⟨-19073062567412651697900, -19073062567412650216248⟩, ⟨-11112169678184295705002, -11112169678184294220997⟩⟩, ⟨⟨23806686942349558599, 23806686942349850432⟩, ⟨6129869716155300534907, 6129869716155300826505⟩⟩, ⟨⟨1131267419656341697668, 1131267419656341741724⟩, ⟨-670971880813092865887, -670971880813092821883⟩⟩, ⟨⟨-179221067784924803845, -179221067784924799119⟩, ⟨-98830166045384400959, -98830166045384396217⟩⟩, ⟨⟨567239730794026380, 567239730794026711⟩, ⟨20542227803889270655, 20542227803889270986⟩⟩, ⟨⟨847243997812452157, 847243997812452177⟩, ⟨-530259150678182658, -530259150678182638⟩⟩],
  [o],
  [⟨⟨-265723507642, -265723507515⟩, ⟨-287427956528, -287427956401⟩⟩, ⟨⟨-20407220727709, -20407220725890⟩, ⟨4435474906785, 4435474908602⟩⟩, ⟨⟨-168049243263017, -168049243250317⟩, ⟨510322998606087, 510322998618792⟩⟩, ⟨⟨5857962117100474, 5857962117159780⟩, ⟨6671327455979387, 6671327456038691⟩⟩, ⟨⟨104012545237527532, 104012545237740641⟩, ⟨-19841173662543234, -19841173662330129⟩⟩, ⟨⟨327117964171629177, 327117964172275601⟩, ⟨-914397968688479188, -914397968687832759⟩⟩, ⟨⟨-4564451456570821709, -4564451456569054441⟩, ⟨-5471892938554075366, -5471892938552308097⟩⟩, ⟨⟨-42395744866856225522, -42395744866851693294⟩, ⟨6983246431129240392, 6983246431133772584⟩⟩, ⟨⟨-78221444447290582726, -78221444447279517380⟩, ⟨202459171182768555981, 202459171182779621472⟩⟩, ⟨⟨578694774539964940642, 578694774539990570202⟩, ⟨730129826880575443822, 730129826880601073272⟩⟩, ⟨⟨3402312635209460351848, 3402312635209516007826⟩, ⟨-473738443210698828475, -473738443210643174012⟩⟩, ⟨⟨4205941966208515872110, 4205941966208627755911⟩, ⟨-10132182375910689635868, -10132182375910577747016⟩⟩, ⟨⟨-18374904835468285613750, -18374904835468079501304⟩, ⟨-24394636633372806208966, -24394636633372600100782⟩⟩, ⟨⟨-73997177287107119350419, -73997177287106774049102⟩, ⟨8461148346227862554760, 8461148346228207840741⟩⟩, ⟨⟨-64798680797351755970076, -64798680797351232865225⟩, ⟨145955583233194906831915, 145955583233195429981022⟩⟩, ⟨⟨175705084384712494649090, 175705084384713208423146⟩, ⟨245414372791710463669841, 245414372791711177405407⟩⟩, ⟨⟨501674223938668627881892, 501674223938669501742693⟩, ⟨-45160169004355608929026, -45160169004354735098469⟩⟩, ⟨⟨317554086621590657661176, 317554086621591614000398⟩, ⟨-671469988840747849940165, -671469988840746893501763⟩⟩, ⟨⟨-544467391680855478740359, -544467391680854546120784⟩, ⟨-800033598556445528378127, -800033598556444595843915⟩⟩, ⟨⟨-1110375982058987115798132, -1110375982058986308867033⟩, ⟨73512775595734013627171, 73512775595734820564144⟩⟩, ⟨⟨-505751575453146643877322, -505751575453146027610098⟩, ⟨1007326855023741685340001, 1007326855023742301656363⟩⟩, ⟨⟨544471174445829420143198, 544471174445829833571471⟩, ⟨841821404193698604548262, 841821404193699017933545⟩⟩, ⟨⟨778906580658325823594700, 778906580658326065527264⟩, ⟨-33312698533470486027673, -33312698533470244081394⟩⟩, ⟨⟨247328637911418547309421, 247328637911418669678680⟩, ⟨-465251601319255655733830, -465251601319255533362366⟩⟩, ⟨⟨-160720048052860868023849, -160720048052860815005114⟩, ⟨-261646608887492599152602, -261646608887492546137449⟩⟩, ⟨⟨-152669476089729353255061, -152669476089729333852775⟩, ⟨2976024191111305632331, 2976024191111325035967⟩⟩, ⟨⟨-31296822441484805175418, -31296822441484799294523⟩, ⟨55705996832849291857973, 55705996832849297738649⟩⟩, ⟨⟨11112169678184294243713, 11112169678184295692758⟩, ⟨19073062567412650245525, 19073062567412651694570⟩⟩, ⟨⟨6129869716155300544822, 6129869716155300825282⟩, ⟨23806686942349564759, 23806686942349845224⟩⟩, ⟨⟨670971880813092824164, 670971880813092864805⟩, ⟨-1131267419656341740869, -1131267419656341700230⟩⟩, ⟨⟨-98830166045384400758, -98830166045384396571⟩, ⟨-179221067784924803738, -179221067784924799550⟩⟩, ⟨⟨-20542227803889270980, -20542227803889270701⟩, ⟨-567239730794026686, -567239730794026409⟩⟩, ⟨⟨-530259150678182657, -530259150678182642⟩, ⟨847243997812452160, 847243997812452176⟩⟩],
  [o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨17953614660612838, 17953614660612874⟩, ⟨-19, 18⟩⟩, ⟨⟨-92, 93⟩, ⟨-93, 93⟩⟩, ⟨⟨-2682320678464185, -2682320678463627⟩, ⟨-277, 281⟩⟩, ⟨⟨-601, 600⟩, ⟨-599, 602⟩⟩, ⟨⟨8738918596429614, 8738918596431565⟩, ⟨-975, 976⟩⟩, ⟨⟨-1215, 1216⟩, ⟨-1215, 1215⟩⟩, ⟨⟨-1017778694990223141, -1017778694990220818⟩, ⟨-1160, 1160⟩⟩, ⟨⟨-839, 838⟩, ⟨-836, 836⟩⟩, ⟨⟨33373907711855862, 33373907711856749⟩, ⟨-446, 445⟩⟩, ⟨⟨-164, 166⟩, ⟨-169, 167⟩⟩, ⟨⟨-39120953487548078, -39120953487547996⟩, ⟨-40, 41⟩⟩, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, o, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨17777530542382716, 17777530542382753⟩, ⟨-17, 18⟩⟩, ⟨⟨-96, 94⟩, ⟨-95, 96⟩⟩, ⟨⟨-2662678475321777, -2662678475321193⟩, ⟨-291, 291⟩⟩, ⟨⟨-624, 624⟩, ⟨-628, 626⟩⟩, ⟨⟨8703883919954435, 8703883919956434⟩, ⟨-998, 998⟩⟩, ⟨⟨-1214, 1213⟩, ⟨-1216, 1213⟩⟩, ⟨⟨-1017108864542757291, -1017108864542755021⟩, ⟨-1133, 1136⟩⟩, ⟨⟨-807, 809⟩, ⟨-808, 807⟩⟩, ⟨⟨33349496329366467, 33349496329367323⟩, ⟨-430, 428⟩⟩, ⟨⟨-162, 160⟩, ⟨-164, 164⟩⟩, ⟨⟨-39090489178583585, -39090489178583505⟩, ⟨-40, 40⟩⟩, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, o, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨17603323702355364, 17603323702355400⟩, ⟨-18, 18⟩⟩, ⟨⟨-95, 94⟩, ⟨-95, 94⟩⟩, ⟨⟨-2643200487081162, -2643200487080577⟩, ⟨-290, 292⟩⟩, ⟨⟨-636, 640⟩, ⟨-640, 638⟩⟩, ⟨⟨8669036008042199, 8669036008044273⟩, ⟨-1038, 1038⟩⟩, ⟨⟨-1278, 1280⟩, ⟨-1278, 1279⟩⟩, ⟨⟨-1016441000016633032, -1016441000016630622⟩, ⟨-1204, 1203⟩⟩, ⟨⟨-854, 856⟩, ⟨-853, 855⟩⟩, ⟨⟨33325185981230467, 33325185981231361⟩, ⟨-449, 450⟩⟩, ⟨⟨-167, 166⟩, ⟨-167, 168⟩⟩, ⟨⟨-39060127408771777, -39060127408771695⟩, ⟨-40, 40⟩⟩, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨17430972771932722, 17430972771932755⟩, ⟨-16, 17⟩⟩, ⟨⟨-91, 92⟩, ⟨-92, 92⟩⟩, ⟨⟨-2623885194553940, -2623885194553364⟩, ⟨-286, 287⟩⟩, ⟨⟨-628, 626⟩, ⟨-631, 628⟩⟩, ⟨⟨8634373594937200, 8634373594939241⟩, ⟨-1022, 1021⟩⟩, ⟨⟨-1254, 1254⟩, ⟨-1256, 1254⟩⟩, ⟨⟨-1015775082535103747, -1015775082535101400⟩, ⟨-1172, 1171⟩⟩, ⟨⟨-829, 827⟩, ⟨-827, 827⟩⟩, ⟨⟨33300975915669463, 33300975915670328⟩, ⟨-434, 436⟩⟩, ⟨⟨-161, 162⟩, ⟨-164, 163⟩⟩, ⟨⟨-39029867716729619, -39029867716729538⟩, ⟨-40, 39⟩⟩, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨17260456638125258, 17260456638125295⟩, ⟨-19, 18⟩⟩, ⟨⟨-97, 95⟩, ⟨-97, 98⟩⟩, ⟨⟨-2604731093715116, -2604731093714512⟩, ⟨-299, 301⟩⟩, ⟨⟨-649, 648⟩, ⟨-651, 650⟩⟩, ⟨⟨8599895425380201, 8599895425382268⟩, ⟨-1034, 1035⟩⟩, ⟨⟨-1251, 1252⟩, ⟨-1252, 1248⟩⟩, ⟨⟨-1015111093437797473, -1015111093437795142⟩, ⟨-1165, 1164⟩⟩, ⟨⟨-831, 831⟩, ⟨-829, 828⟩⟩, ⟨⟨33276865387041259, 33276865387042139⟩, ⟨-442, 439⟩⟩, ⟨⟨-166, 165⟩, ⟨-168, 165⟩⟩, ⟨⟨-38999709643176985, -38999709643176903⟩, ⟨-40, 40⟩⟩, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨17091754440386515, 17091754440386552⟩, ⟨-19, 19⟩⟩, ⟨⟨-99, 99⟩, ⟨-98, 99⟩⟩, ⟨⟨-2585736695543294, -2585736695542682⟩, ⟨-307, 306⟩⟩, ⟨⟨-658, 658⟩, ⟨-660, 658⟩⟩, ⟨⟨8565600254506616, 8565600254508703⟩, ⟨-1042, 1044⟩⟩, ⟨⟨-1249, 1250⟩, ⟨-1251, 1249⟩⟩, ⟨⟨-1014449014278130556, -1014449014278128255⟩, ⟨-1149, 1150⟩⟩, ⟨⟨-810, 812⟩, ⟨-807, 808⟩⟩, ⟨⟨33252853655788837, 33252853655789690⟩, ⟨-429, 429⟩⟩, ⟨⟨-160, 160⟩, ⟨-164, 164⟩⟩, ⟨⟨-38969652730928797, -38969652730928716⟩, ⟨-39, 40⟩⟩, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, o]
]

private def st10_9 : List (List CFpIv) := [
  [o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-6158601678849939, -6158601678849892⟩, ⟨-21, 21⟩⟩, ⟨⟨-46, 45⟩, ⟨-47, 47⟩⟩, ⟨⟨1215722580806784, 1215722580806915⟩, ⟨-67, 68⟩⟩, ⟨⟨-76, 74⟩, ⟨-74, 73⟩⟩, ⟨⟨-7762758849240702, -7762758849240566⟩, ⟨-69, 68⟩⟩, ⟨⟨-52, 52⟩, ⟨-53, 52⟩⟩, ⟨⟨150144744828, 150144744895⟩, ⟨-33, 36⟩⟩, ⟨⟨-21, 22⟩, ⟨-21, 21⟩⟩, ⟨⟨-93936308, -93936280⟩, ⟨-13, 15⟩⟩, ⟨⟨-7, 7⟩, ⟨-7, 7⟩⟩, ⟨⟨1883763, 1883768⟩, ⟨-3, 2⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-6159368101542351, -6159368101542305⟩, ⟨-20, 21⟩⟩, ⟨⟨-47, 47⟩, ⟨-48, 47⟩⟩, ⟨⟨1216024678990239, 1216024678990379⟩, ⟨-70, 69⟩⟩, ⟨⟨-80, 79⟩, ⟨-79, 80⟩⟩, ⟨⟨-7765652421193045, -7765652421192900⟩, ⟨-72, 72⟩⟩, ⟨⟨-55, 52⟩, ⟨-54, 53⟩⟩, ⟨⟨150229554316, 150229554384⟩, ⟨-35, 35⟩⟩, ⟨⟨-22, 21⟩, ⟨-22, 20⟩⟩, ⟨⟨-94007434, -94007408⟩, ⟨-13, 13⟩⟩, ⟨⟨-7, 7⟩, ⟨-8, 7⟩⟩, ⟨⟨1885551, 1885556⟩, ⟨-2, 3⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-6160134651779189, -6160134651779143⟩, ⟨-21, 21⟩⟩, ⟨⟨-46, 44⟩, ⟨-50, 49⟩⟩, ⟨⟨1216326864811423, 1216326864811562⟩, ⟨-71, 70⟩⟩, ⟨⟨-80, 79⟩, ⟨-78, 77⟩⟩, ⟨⟨-7768547192111371, -7768547192111225⟩, ⟨-73, 72⟩⟩, ⟨⟨-57, 56⟩, ⟨-57, 57⟩⟩, ⟨⟨150314416804, 150314416878⟩, ⟨-38, 39⟩⟩, ⟨⟨-24, 24⟩, ⟨-22, 23⟩⟩, ⟨⟨-94078621, -94078594⟩, ⟨-13, 12⟩⟩, ⟨⟨-7, 7⟩, ⟨-7, 6⟩⟩, ⟨⟨1887342, 1887346⟩, ⟨-3, 2⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-6160901329585472, -6160901329585427⟩, ⟨-21, 20⟩⟩, ⟨⟨-46, 45⟩, ⟨-44, 47⟩⟩, ⟨⟨1216629138298757, 1216629138298890⟩, ⟨-66, 69⟩⟩, ⟨⟨-75, 75⟩, ⟨-74, 74⟩⟩, ⟨⟨-7771443162536195, -7771443162536060⟩, ⟨-68, 67⟩⟩, ⟨⟨-52, 51⟩, ⟨-52, 50⟩⟩, ⟨⟨150399332336, 150399332404⟩, ⟨-35, 36⟩⟩, ⟨⟨-21, 22⟩, ⟨-22, 22⟩⟩, ⟨⟨-94149866, -94149840⟩, ⟨-13, 12⟩⟩, ⟨⟨-8, 7⟩, ⟨-7, 6⟩⟩, ⟨⟨1889132, 1889138⟩, ⟨-3, 2⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-6161668134986226, -6161668134986180⟩, ⟨-21, 21⟩⟩, ⟨⟨-47, 45⟩, ⟨-47, 46⟩⟩, ⟨⟨1216931499480676, 1216931499480809⟩, ⟨-67, 66⟩⟩, ⟨⟨-74, 73⟩, ⟨-74, 73⟩⟩, ⟨⟨-7774340333008303, -7774340333008169⟩, ⟨-66, 67⟩⟩, ⟨⟨-50, 51⟩, ⟨-50, 52⟩⟩, ⟨⟨150484300939, 150484301006⟩, ⟨-34, 35⟩⟩, ⟨⟨-22, 21⟩, ⟨-19, 20⟩⟩, ⟨⟨-94221169, -94221142⟩, ⟨-12, 12⟩⟩, ⟨⟨-6, 7⟩, ⟨-7, 7⟩⟩, ⟨⟨1890927, 1890932⟩, ⟨-2, 3⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-6162435068006480, -6162435068006433⟩, ⟨-21, 21⟩⟩, ⟨⟨-47, 46⟩, ⟨-48, 48⟩⟩, ⟨⟨1217233948385626, 1217233948385763⟩, ⟨-69, 68⟩⟩, ⟨⟨-76, 77⟩, ⟨-76, 76⟩⟩, ⟨⟨-7777238704068729, -7777238704068589⟩, ⟨-70, 71⟩⟩, ⟨⟨-51, 54⟩, ⟨-53, 55⟩⟩, ⟨⟨150569322653, 150569322722⟩, ⟨-35, 33⟩⟩, ⟨⟨-21, 20⟩, ⟨-20, 22⟩⟩, ⟨⟨-94292532, -94292505⟩, ⟨-13, 11⟩⟩, ⟨⟨-7, 6⟩, ⟨-7, 7⟩⟩, ⟨⟨1892723, 1892726⟩, ⟨-2, 2⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-6163202128671266, -6163202128671218⟩, ⟨-20, 21⟩⟩, ⟨⟨-44, 45⟩, ⟨-47, 48⟩⟩, ⟨⟨1217536485042071, 1217536485042203⟩, ⟨-66, 68⟩⟩, ⟨⟨-73, 77⟩, ⟨-77, 75⟩⟩, ⟨⟨-7780138276258767, -7780138276258626⟩, ⟨-74, 72⟩⟩, ⟨⟨-56, 56⟩, ⟨-54, 55⟩⟩, ⟨⟨150654397513, 150654397587⟩, ⟨-35, 36⟩⟩, ⟨⟨-22, 22⟩, ⟨-23, 22⟩⟩, ⟨⟨-94363956, -94363928⟩, ⟨-13, 14⟩⟩, ⟨⟨-7, 7⟩, ⟨-7, 6⟩⟩, ⟨⟨1894519, 1894524⟩, ⟨-2, 3⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-6163969317005624, -6163969317005577⟩, ⟨-21, 21⟩⟩, ⟨⟨-46, 47⟩, ⟨-48, 48⟩⟩, ⟨⟨1217839109478465, 1217839109478600⟩, ⟨-69, 70⟩⟩, ⟨⟨-78, 78⟩, ⟨-78, 77⟩⟩, ⟨⟨-7783039050119980, -7783039050119833⟩, ⟨-72, 73⟩⟩, ⟨⟨-57, 57⟩, ⟨-58, 58⟩⟩, ⟨⟨150739525558, 150739525635⟩, ⟨-38, 40⟩⟩, ⟨⟨-23, 25⟩, ⟨-22, 24⟩⟩, ⟨⟨-94435434, -94435407⟩, ⟨-13, 12⟩⟩, ⟨⟨-8, 7⟩, ⟨-7, 7⟩⟩, ⟨⟨1896318, 1896322⟩, ⟨-2, 3⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-6164736633034599, -6164736633034554⟩, ⟨-21, 21⟩⟩, ⟨⟨-45, 46⟩, ⟨-47, 47⟩⟩, ⟨⟨1218141821723296, 1218141821723429⟩, ⟨-67, 70⟩⟩, ⟨⟨-77, 79⟩, ⟨-76, 77⟩⟩, ⟨⟨-7785941026194177, -7785941026194038⟩, ⟨-71, 70⟩⟩, ⟨⟨-53, 52⟩, ⟨-52, 52⟩⟩, ⟨⟨150824706828, 150824706895⟩, ⟨-34, 37⟩⟩, ⟨⟨-22, 22⟩, ⟨-22, 23⟩⟩, ⟨⟨-94506976, -94506948⟩, ⟨-13, 14⟩⟩, ⟨⟨-7, 7⟩, ⟨-7, 8⟩⟩, ⟨⟨1898119, 1898123⟩, ⟨-3, 3⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-6165504076783243, -6165504076783195⟩, ⟨-21, 21⟩⟩, ⟨⟨-47, 48⟩, ⟨-47, 47⟩⟩, ⟨⟨1218444621805046, 1218444621805178⟩, ⟨-68, 67⟩⟩, ⟨⟨-75, 74⟩, ⟨-74, 74⟩⟩, ⟨⟨-7788844205023450, -7788844205023314⟩, ⟨-67, 69⟩⟩, ⟨⟨-53, 52⟩, ⟨-51, 52⟩⟩, ⟨⟨150909941350, 150909941419⟩, ⟨-36, 33⟩⟩, ⟨⟨-23, 22⟩, ⟨-22, 22⟩⟩, ⟨⟨-94578574, -94578547⟩, ⟨-13, 12⟩⟩, ⟨⟨-5, 7⟩, ⟨-6, 6⟩⟩, ⟨⟨1899921, 1899926⟩, ⟨-2, 2⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-6166271648276612, -6166271648276566⟩, ⟨-21, 21⟩⟩, ⟨⟨-45, 46⟩, ⟨-47, 48⟩⟩, ⟨⟨1218747509752206, 1218747509752345⟩, ⟨-70, 69⟩⟩, ⟨⟨-80, 82⟩, ⟨-79, 79⟩⟩, ⟨⟨-7791748587150145, -7791748587149998⟩, ⟨-73, 71⟩⟩, ⟨⟨-56, 54⟩, ⟨-57, 54⟩⟩, ⟨⟨150995229165, 150995229236⟩, ⟨-36, 37⟩⟩, ⟨⟨-22, 23⟩, ⟨-22, 23⟩⟩, ⟨⟨-94650232, -94650205⟩, ⟨-14, 13⟩⟩, ⟨⟨-7, 8⟩, ⟨-7, 6⟩⟩, ⟨⟨1901726, 1901730⟩, ⟨-3, 2⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-6167039347539763, -6167039347539716⟩, ⟨-22, 23⟩⟩, ⟨⟨-50, 49⟩, ⟨-48, 51⟩⟩, ⟨⟨1219050485593291, 1219050485593432⟩, ⟨-72, 70⟩⟩, ⟨⟨-76, 76⟩, ⟨-77, 77⟩⟩, ⟨⟨-7794654173116848, -7794654173116710⟩, ⟨-69, 68⟩⟩, ⟨⟨-51, 53⟩, ⟨-51, 52⟩⟩, ⟨⟨151080570312, 151080570380⟩, ⟨-35, 35⟩⟩, ⟨⟨-23, 22⟩, ⟨-22, 22⟩⟩, ⟨⟨-94721950, -94721923⟩, ⟨-13, 14⟩⟩, ⟨⟨-7, 7⟩, ⟨-7, 7⟩⟩, ⟨⟨1903532, 1903537⟩, ⟨-3, 2⟩⟩, z, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-6167807174597767, -6167807174597720⟩, ⟨-21, 21⟩⟩, ⟨⟨-46, 48⟩, ⟨-49, 47⟩⟩, ⟨⟨1219353549356816, 1219353549356955⟩, ⟨-72, 68⟩⟩, ⟨⟨-79, 79⟩, ⟨-79, 79⟩⟩, ⟨⟨-7797560963466445, -7797560963466299⟩, ⟨-72, 72⟩⟩, ⟨⟨-55, 56⟩, ⟨-55, 55⟩⟩, ⟨⟨151165964821, 151165964894⟩, ⟨-37, 37⟩⟩, ⟨⟨-22, 23⟩, ⟨-22, 21⟩⟩, ⟨⟨-94793727, -94793700⟩, ⟨-13, 14⟩⟩, ⟨⟨-7, 7⟩, ⟨-6, 7⟩⟩, ⟨⟨1905341, 1905345⟩, ⟨-3, 2⟩⟩, z, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-6168575129475692, -6168575129475647⟩, ⟨-21, 21⟩⟩, ⟨⟨-47, 46⟩, ⟨-47, 46⟩⟩, ⟨⟨1219656701071310, 1219656701071443⟩, ⟨-68, 68⟩⟩, ⟨⟨-77, 77⟩, ⟨-77, 78⟩⟩, ⟨⟨-7800468958742046, -7800468958741904⟩, ⟨-72, 72⟩⟩, ⟨⟨-56, 56⟩, ⟨-54, 56⟩⟩, ⟨⟨151251412734, 151251412809⟩, ⟨-37, 37⟩⟩, ⟨⟨-23, 23⟩, ⟨-23, 23⟩⟩, ⟨⟨-94865563, -94865536⟩, ⟨-13, 13⟩⟩, ⟨⟨-5, 6⟩, ⟨-6, 7⟩⟩, ⟨⟨1907151, 1907155⟩, ⟨-2, 2⟩⟩, z, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-6169343212198617, -6169343212198570⟩, ⟨-21, 21⟩⟩, ⟨⟨-46, 46⟩, ⟨-47, 46⟩⟩, ⟨⟨1219959940765301, 1219959940765433⟩, ⟨-68, 69⟩⟩, ⟨⟨-75, 74⟩, ⟨-75, 74⟩⟩, ⟨⟨-7803378159487046, -7803378159486910⟩, ⟨-67, 66⟩⟩, ⟨⟨-51, 50⟩, ⟨-51, 51⟩⟩, ⟨⟨151336914091, 151336914158⟩, ⟨-32, 34⟩⟩, ⟨⟨-20, 21⟩, ⟨-20, 20⟩⟩, ⟨⟨-94937459, -94937432⟩, ⟨-12, 11⟩⟩, ⟨⟨-7, 6⟩, ⟨-6, 6⟩⟩, ⟨⟨1908962, 1908966⟩, ⟨-1, 2⟩⟩, z, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-6170111422791624, -6170111422791578⟩, ⟨-20, 21⟩⟩, ⟨⟨-45, 44⟩, ⟨-46, 47⟩⟩, ⟨⟨1220263268467341, 1220263268467471⟩, ⟨-67, 67⟩⟩, ⟨⟨-74, 73⟩, ⟨-74, 73⟩⟩, ⟨⟨-7806288566245098, -7806288566244963⟩, ⟨-70, 67⟩⟩, ⟨⟨-52, 52⟩, ⟨-54, 54⟩⟩, ⟨⟨151422468918, 151422468991⟩, ⟨-36, 36⟩⟩, ⟨⟨-23, 23⟩, ⟨-22, 23⟩⟩, ⟨⟨-95009414, -95009387⟩, ⟨-14, 14⟩⟩, ⟨⟨-7, 7⟩, ⟨-7, 7⟩⟩, ⟨⟨1910776, 1910781⟩, ⟨-2, 2⟩⟩, z, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-6170879761279801, -6170879761279753⟩, ⟨-21, 21⟩⟩, ⟨⟨-47, 46⟩, ⟨-48, 47⟩⟩, ⟨⟨1220566684205982, 1220566684206117⟩, ⟨-68, 68⟩⟩, ⟨⟨-77, 76⟩, ⟨-76, 76⟩⟩, ⟨⟨-7809200179560115, -7809200179559976⟩, ⟨-71, 70⟩⟩, ⟨⟨-52, 55⟩, ⟨-52, 53⟩⟩, ⟨⟨151508077262, 151508077331⟩, ⟨-36, 35⟩⟩, ⟨⟨-20, 22⟩, ⟨-20, 21⟩⟩, ⟨⟨-95081427, -95081402⟩, ⟨-13, 11⟩⟩, ⟨⟨-6, 6⟩, ⟨-5, 7⟩⟩, ⟨⟨1912592, 1912597⟩, ⟨-2, 2⟩⟩, z, z, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, o, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, ⟨⟨-6171648227688240, -6171648227688193⟩, ⟨-21, 20⟩⟩, ⟨⟨-47, 46⟩, ⟨-47, 47⟩⟩, ⟨⟨1220870188009799, 1220870188009933⟩, ⟨-67, 67⟩⟩, ⟨⟨-75, 75⟩, ⟨-74, 75⟩⟩, ⟨⟨-7812112999976266, -7812112999976129⟩, ⟨-68, 69⟩⟩, ⟨⟨-54, 51⟩, ⟨-52, 53⟩⟩, ⟨⟨151593739154, 151593739224⟩, ⟨-35, 37⟩⟩, ⟨⟨-22, 24⟩, ⟨-23, 22⟩⟩, ⟨⟨-95153504, -95153475⟩, ⟨-14, 14⟩⟩, ⟨⟨-8, 7⟩, ⟨-7, 8⟩⟩, ⟨⟨1914409, 1914414⟩, ⟨-2, 3⟩⟩, z, z, z, z, z, z],
  [⟨⟨0, 1⟩, ⟨0, 0⟩⟩, ⟨⟨-16, 3⟩, ⟨-4, 4⟩⟩, ⟨⟨-45, 96⟩, ⟨-57, 58⟩⟩, ⟨⟨-427, 284⟩, ⟨-333, 330⟩⟩, ⟨⟨-1214, 1516⟩, ⟨-1334, 1335⟩⟩, ⟨⟨-4372, 3821⟩, ⟨-4063, 4073⟩⟩, ⟨⟨-8342, 11497⟩, ⟨-9903, 9879⟩⟩, ⟨⟨-104116, -64106⟩, ⟨-19956, 19981⟩⟩, ⟨⟨4680102, 4749459⟩, ⟨-34637, 34622⟩⟩, ⟨⟨-215775490, -215668878⟩, ⟨-53244, 53248⟩⟩, ⟨⟨8044947073, 8045096725⟩, ⟨-74753, 74757⟩⟩, ⟨⟨-244470871629, -244470674805⟩, ⟨-98327, 98322⟩⟩, ⟨⟨6028192048173, 6028192295614⟩, ⟨-123622, 123622⟩⟩, ⟨⟨-119607813886470, -119607813585043⟩, ⟨-150613, 150618⟩⟩, ⟨⟨1884289026008423, 1884289026367077⟩, ⟨-179231, 179219⟩⟩, ⟨⟨-23115157970688727, -23115157970270368⟩, ⟨-209058, 209072⟩⟩, ⟨⟨214883073132647909, 214883073133126836⟩, ⟨-239334, 239325⟩⟩, ⟨⟨-1459868120934440069, -1459868120933901560⟩, ⟨-269095, 269095⟩⟩, ⟨⟨6942711419629405333, 6942711419630001950⟩, ⟨-298147, 298152⟩⟩, ⟨⟨-22396295539627819705, -22396295539627164145⟩, ⟨-327683, 327680⟩⟩, ⟨⟨50397628547332967271, 50397628547333686326⟩, ⟨-359498, 359492⟩⟩, ⟨⟨-82014929595615512301, -82014929595614726589⟩, ⟨-392783, 392804⟩⟩, ⟨⟨98856371844075296904, 98856371844076137168⟩, ⟨-419977, 419947⟩⟩, ⟨⟨-88298755140603179881, -88298755140602327226⟩, ⟨-426082, 426118⟩⟩, ⟨⟨54034224268425189127, 54034224268425982605⟩, ⟨-396579, 396543⟩⟩, ⟨⟨-9143765922164204084, -9143765922163546167⟩, ⟨-328858, 328891⟩⟩, ⟨⟨-34969278563279046109, -34969278563278570209⟩, ⟨-237918, 237888⟩⟩, ⟨⟨68654230843995789708, 68654230843996085582⟩, ⟨-147824, 147847⟩⟩, ⟨⟨-81849111420011841946, -81849111420011685724⟩, ⟨-77957, 77953⟩⟩, ⟨⟨71160150210597336184, 71160150210597405413⟩, ⟨-34459, 34443⟩⟩, ⟨⟨-46106260681921248769, -46106260681921223397⟩, ⟨-12545, 12574⟩⟩, ⟨⟨21978774215845138600, 21978774215845146127⟩, ⟨-3704, 3678⟩⟩, ⟨⟨-7464219741638457758, -7464219741638456009⟩, ⟨-836, 853⟩⟩, ⟨⟨1704161942679393170, 1704161942679393472⟩, ⟨-146, 141⟩⟩, ⟨⟨-233851982553760656, -233851982553760619⟩, ⟨-18, 18⟩⟩, ⟨⟨14545027835068710, 14545027835068714⟩, ⟨-2, 2⟩⟩],
  [o],
  [⟨⟨-5, 5⟩, ⟨-5, 5⟩⟩, ⟨⟨-106, 106⟩, ⟨-106, 106⟩⟩, ⟨⟨-847, 847⟩, ⟨-847, 847⟩⟩, ⟨⟨-4439, 4439⟩, ⟨-4439, 4439⟩⟩, ⟨⟨-17018, 17018⟩, ⟨-17018, 17018⟩⟩, ⟨⟨-50617, 50646⟩, ⟨-50637, 50626⟩⟩, ⟨⟨-122866, 120931⟩, ⟨-122626, 121174⟩⟩, ⟨⟨-254226, 236280⟩, ⟨-162034, 328476⟩⟩, ⟨⟨3871639, 4718459⟩, ⟨-2368710, -1521902⟩⟩, ⟨⟨-177104506, -175821118⟩, ⟨-124787104, -123503700⟩⟩, ⟨⟨-649388950, -647646905⟩, ⟨8019626291, 8021368335⟩⟩, ⟨⟨220008123717, 220010280684⟩, ⟨-106738385946, -106736228989⟩⟩, ⟨⟨-5021581624583, -5021579142280⟩, ⟨-3338679891185, -3338677408886⟩⟩, ⟨⟨-6513310794905, -6513308081086⟩, ⟨119481310419835, 119481313133664⟩⟩, ⟨⟨1674237641355106, 1674237644247330⟩, ⟨-866871093560041, -866871090667803⟩⟩, ⟨⟨-19588028834626719, -19588028831543393⟩, ⟨-12306031811169725, -12306031808086422⟩⟩, ⟨⟨-6241024749751942, -6241024746406731⟩, ⟨215026798776014848, 215026798779360066⟩⟩, ⟨⟨1281473867055701988, 1281473867059404045⟩, ⟨-704319098283590716, -704319098279888658⟩⟩, ⟨⟨-5980340086365139606, -5980340086361001991⟩, ⟨-3563110041751376842, -3563110041747239228⟩⟩, ⟨⟨-170225105972672955, -170225105968065267⟩, ⟨22501000633088626437, 22501000633093234145⟩⟩, ⟨⟨44083917835377314266, 44083917835382367477⟩, ⟨-25278871944555520599, -25278871944550467421⟩⟩, ⟨⟨-72005753278695958956, -72005753278690566109⟩, ⟨-41616659961387646859, -41616659961382253999⟩⟩, ⟨⟨-146793336961017982, -146793336955513270⟩, ⟨101041199002223630152, 101041199002229134867⟩⟩, ⟨⟨79340654579907164027, 79340654579912410280⟩, ⟨-44824758477980278837, -44824758477975032580⟩⟩, ⟨⟨-47719822245604545159, -47719822245600001994⟩, ⟨-29908017364437859215, -29908017364433316055⟩⟩, ⟨⟨-3079428703183585332, -3079428703180100877⟩, ⟨9591722932726927275, 9591722932730411723⟩⟩, ⟨⟨-29847525683241946558, -29847525683239630393⟩, ⟨21223727022101260582, 21223727022103576764⟩⟩, ⟨⟨63149181642101408445, 63149181642102719376⟩, ⟨32714286442148665491, 32714286442149976411⟩⟩, ⟨⟨-2768428024122679004, -2768428024122056500⟩, ⟨-83900663228968568292, -83900663228967945786⟩⟩, ⟨⟨-61552517025769877274, -61552517025769632290⟩, ⟨38046113282340818017, 38046113282341063003⟩⟩, ⟨⟨41058127966282271265, 41058127966282350519⟩, ⟨22008925175083711312, 22008925175083790564⟩⟩, ⟨⟨-784890736053310103, -784890736053289079⟩, ⟨-22095387770480188874, -22095387770480167846⟩⟩, ⟨⟨-6325287493981346290, -6325287493981341705⟩, ⟨4006283571934514924, 4006283571934519508⟩⟩, ⟨⟨1516730568815947667, 1516730568815948486⟩, ⟨782120751168381196, 782120751168382016⟩⟩, ⟨⟨-12790129623504765, -12790129623504649⟩, ⟨-233604622442987362, -233604622442987246⟩⟩, ⟨⟨-12118478347681857, -12118478347681845⟩, ⟨8043757782092201, 8043757782092213⟩⟩],
  [o],
  [⟨⟨-5, 5⟩, ⟨-5, 5⟩⟩, ⟨⟨-106, 106⟩, ⟨-106, 106⟩⟩, ⟨⟨-845, 845⟩, ⟨-845, 845⟩⟩, ⟨⟨-4412, 4412⟩, ⟨-4412, 4412⟩⟩, ⟨⟨-16835, 16835⟩, ⟨-16835, 16835⟩⟩, ⟨⟨-49893, 49904⟩, ⟨-49913, 49884⟩⟩, ⟨⟨-120612, 119157⟩, ⟨-120852, 118915⟩⟩, ⟨⟨-324403, 157956⟩, ⟨-232207, 250156⟩⟩, ⟨⟨-2362392, -1528221⟩, ⟨3877968, 4712129⟩⟩, ⟨⟨123511592, 124779203⟩, ⟨175829000, 177096622⟩⟩, ⟨⟨8019634686, 8021359941⟩, ⟨-649380546, -647655299⟩⟩, ⟨⟨106736237241, 106738377728⟩, ⟨-220010272447, -220008131952⟩⟩, ⟨⟨-3338679883209, -3338677416810⟩, ⟨-5021581616664, -5021579150256⟩⟩, ⟨⟨-119481313126057, -119481310427448⟩, ⟨6513308088653, 6513310787237⟩⟩, ⟨⟨-866871093553106, -866871090674811⟩, ⟨1674237641362023, 1674237644240336⟩⟩, ⟨⟨12306031808092254, 12306031811163776⟩, ⟨19588028831549295, 19588028834620827⟩⟩, ⟨⟨215026798776019483, 215026798779355387⟩, ⟨-6241024749747224, -6241024746411343⟩⟩, ⟨⟨704319098279892457, 704319098283586951⟩, ⟨-1281473867059400231, -1281473867055705726⟩⟩, ⟨⟨-3563110041751373047, -3563110041747242995⟩, ⟨-5980340086365135802, -5980340086361005749⟩⟩, ⟨⟨-22501000633093229266, -22501000633088631275⟩, ⟨170225105968070159, 170225105972668135⟩⟩, ⟨⟨-25278871944555514113, -25278871944550473801⟩, ⟨44083917835377320729, 44083917835382361063⟩⟩, ⟨⟨41616659961382261272, 41616659961387639685⟩, ⟨72005753278690573313, 72005753278695951720⟩⟩, ⟨⟨101041199002223636191, 101041199002229128872⟩, ⟨-146793336961011997, -146793336955519322⟩⟩, ⟨⟨44824758477975035410, 44824758477980275992⟩, ⟨-79340654579912407490, -79340654579907166893⟩⟩, ⟨⟨-29908017364437860043, -29908017364433315306⟩, ⟨-47719822245604545962, -47719822245600001229⟩⟩, ⟨⟨-9591722932730414661, -9591722932726924422⟩, ⟨3079428703180098012, 3079428703183588244⟩⟩, ⟨⟨21223727022101257822, 21223727022103579533⟩, ⟨-29847525683241949285, -29847525683239627566⟩⟩, ⟨⟨-32714286442149977694, -32714286442148664116⟩, ⟨-63149181642102720696, -63149181642101407124⟩⟩, ⟨⟨-83900663228968568246, -83900663228967945841⟩, ⟨-2768428024122679001, -2768428024122056592⟩⟩, ⟨⟨-38046113282341062409, -38046113282340818697⟩, ⟨61552517025769632928, 61552517025769876636⟩⟩, ⟨⟨22008925175083711873, 22008925175083789978⟩, ⟨41058127966282271871, 41058127966282349973⟩⟩, ⟨⟨22095387770480168161, 22095387770480188578⟩, ⟨784890736053289400, 784890736053309818⟩⟩, ⟨⟨4006283571934515040, 4006283571934519412⟩, ⟨-6325287493981346181, -6325287493981341808⟩⟩, ⟨⟨-782120751168381989, -782120751168381216⟩, ⟨-1516730568815948466, -1516730568815947693⟩⟩, ⟨⟨-233604622442987360, -233604622442987248⟩, ⟨-12790129623504764, -12790129623504653⟩⟩, ⟨⟨-8043757782092213, -8043757782092201⟩, ⟨12118478347681845, 12118478347681857⟩⟩],
  [o],
  [⟨⟨391436540786, 391436540797⟩, ⟨-3, 4⟩⟩, ⟨⟨-22055533882462, -22055533882277⟩, ⟨-67, 56⟩⟩, ⟨⟨600970053382891, 600970053384259⟩, ⟨-462, 523⟩⟩, ⟨⟨-10549424115050314, -10549424115043835⟩, ⟨-2581, 2361⟩⟩, ⟨⟨134091863847101219, 134091863847123769⟩, ⟨-8668, 9235⟩⟩, ⟨⟨-1315185950231992386, -1315185950231929682⟩, ⟨-26131, 25019⟩⟩, ⟨⟨10357963227201280290, 10357963227201428783⟩, ⟨-60757, 62481⟩⟩, ⟨⟨-67303386628350131239, -67303386628349815202⟩, ⟨-133482, 131300⟩⟩, ⟨⟨367909634316268101593, 367909634316268734380⟩, ⟨-264787, 267062⟩⟩, ⟨⟨-1716753285476858785195, -1716753285476857549314⟩, ⟨-519587, 517666⟩⟩, ⟨⟨6914798847470720558600, 6914798847470722972179⟩, ⟨-1008624, 1009879⟩⟩, ⟨⟨-24251011541011190134212, -24251011541011185367790⟩, ⟨-1989003, 1988336⟩⟩, ⟨⟨74563763627633025876597, 74563763627633035358251⟩, ⟨-3964437, 3965069⟩⟩, ⟨⟨-202075725897548213917685, -202075725897548195231603⟩, ⟨-7875548, 7874163⟩⟩, ⟨⟨484754532816566643402503, 484754532816566679067652⟩, ⟨-15215214, 15217910⟩⟩, ⟨⟨-1032665711948129851115499, -1032665711948129786622787⟩, ⟨-27922508, 27918572⟩⟩, ⟨⟨1958255870309682137886611, 1958255870309682246427974⟩, ⟨-47684438, 47688934⟩⟩, ⟨⟨-3311031739894413556034454, -3311031739894413388225610⟩, ⟨-74708556, 74704327⟩⟩, ⟨⟨4996286539341087874260074, 4996286539341088110372042⟩, ⟨-106248230, 106251762⟩⟩, ⟨⟨-6730240337182286803112323, -6730240337182286502810744⟩, ⟨-136191208, 136188284⟩⟩, ⟨⟨8089537179517980635021152, 8089537179517980978453709⟩, ⟨-156468733, 156471284⟩⟩, ⟨⟨-8666131085660065361879093, -8666131085660065010321992⟩, ⟨-160404701, 160402558⟩⟩, ⟨⟨8258396463325670845051136, 8258396463325671165767801⟩, ⟨-146093498, 146094892⟩⟩, ⟨⟨-6980975904828933747594804, -6980975904828933488051258⟩, ⟨-117687654, 117687344⟩⟩, ⟨⟨5214682598721759256621333, 5214682598721759441972183⟩, ⟨-83422996, 83422208⟩⟩, ⟨⟨-3424890017848354955358253, -3424890017848354839265132⟩, ⟨-51718178, 51719721⟩⟩, ⟨⟨1964895581942240321856228, 1964895581942240385158900⟩, ⟨-27836269, 27834476⟩⟩, ⟨⟨-976442807147971580000321, -976442807147971550224331⟩, ⟨-12884652, 12886266⟩⟩, ⟨⟨415735557264640844737837, 415735557264640856681569⟩, ⟨-5071124, 5069912⟩⟩, ⟨⟨-149484849740852309405567, -149484849740852305380096⟩, ⟨-1670134, 1670909⟩⟩, ⟨⟨44520959824207899792119, 44520959824207900910138⟩, ⟨-451866, 451438⟩⟩, ⟨⟨-10689754617176476216871, -10689754617176475967528⟩, ⟨-97480, 97695⟩⟩, ⟨⟨1988454208538928000565, 1988454208538928043733⟩, ⟨-16343, 16238⟩⟩, ⟨⟨-268890535945166618042, -268890535945166612472⟩, ⟨-2001, 2047⟩⟩, ⟨⟨23515479662850685650, 23515479662850686163⟩, ⟨-187, 173⟩⟩, ⟨⟨-998245687807855561, -998245687807855530⟩, ⟨-9, 11⟩⟩],
  [o],
  [⟨⟨-287427956521, -287427956409⟩, ⟨-265723507637, -265723507524⟩⟩, ⟨⟨-4684389004714, -4684389002618⟩, ⟨21554349120027, 21554349122123⟩⟩, ⟨⟨570912716423753, 570912716442635⟩, ⟨-188026599291598, -188026599272714⟩⟩, ⟨⟨-7929788917431332, -7929788917319369⟩, ⟨-6962079736642376, -6962079736530418⟩⟩, ⟨⟨-25123084080798431, -25123084080300649⟩, ⟨131769259682046864, 131769259682544644⟩⟩, ⟨⟨1238879323476303569, 1238879323478102088⟩, ⟨-443377959547510528, -443377959545712001⟩⟩, ⟨⟨-7959872192858261346, -7959872192852661209⟩, ⟨-6637565856478802912, -6637565856473202777⟩⟩, ⟨⟨-10932265359330570235, -10932265359314856124⟩, ⟨66458838306188896385, 66458838306204610481⟩⟩, ⟨⟨343441378706971869179, 343441378707012842874⟩, ⟨-132795433074459313889, -132795433074418340190⟩⟩, ⟨⟨-1347062436429516412131, -1347062436429415595712⟩, ⟨-1066960487739258855179, -1066960487739158038779⟩⟩, ⟨⟨-951994068426596268831, -951994068426361716513⟩, ⟨6856655348529682144570, 6856655348529916697110⟩⟩, ⟨⟨22421256548275433435272, 22421256548275946220554⟩, ⟨-9319447998859956730961, -9319447998859443946560⟩⟩, ⟨⟨-59664367066033647057662, -59664367066032602997779⟩, ⟨-44890069894269149019798, -44890069894268104960126⟩⟩, ⟨⟨-22862155274798341496373, -22862155274796378329657⟩, ⟨201082397674637093858996, 201082397674639057033446⟩⟩, ⟨⟨443625300304361870812584, 443625300304365256969217⟩, ⟨-197346603014887453179554, -197346603014884067044192⟩⟩, ⟨⟨-841624686408201348380073, -841624686408196017522788⟩, ⟨-601479872944270215526087, -601479872944264884660002⟩⟩, ⟨⟨-173998708335912400122734, -173998708335904769546110⟩, ⟨1954143347247178464458737, 1954143347247186095098485⟩⟩, ⟨⟨2997449234918152958661106, 2997449234918162857162019⟩, ⟨-1421588263943660848090032, -1421588263943650949738194⟩⟩, ⟨⟨-4142323449179048143315377, -4142323449179036539129864⟩, ⟨-2811639213307025808619117, -2811639213307014204327456⟩⟩, ⟨⟨-436337441230760228034383, -436337441230747968802253⟩, ⟨6730176479838941203538107, 6730176479838953462878035⟩⟩, ⟨⟨7239422190506119803817764, 7239422190506131437259518⟩, ⟨-3648386401058108789870607, -3648386401058097156725579⟩⟩, ⟨⟨-7300165828995732200210138, -7300165828995722315332423⟩, ⟨-4704542319027370872531909, -4704542319027360987403828⟩⟩, ⟨⟨-338863207117711884067705, -338863207117704392931764⟩, ⟨8269145105740772705559261, 8269145105740780196665897⟩⟩, ⟨⟨6170774474641479506802709, 6170774474641484544478430⟩, ⟨-3295604226169438804767716, -3295604226169433767223238⟩⟩, ⟨⟨-4457997139832990881309291, -4457997139832987889513603⟩, ⟨-2725845937596846298783833, -2725845937596843306858379⟩⟩, ⟨⟨-59471312613067513283105, -59471312613065954579756⟩, ⟨3431036263024594860674281, 3431036263024596419324684⟩⟩, ⟨⟨1713988779925302025322459, 1713988779925302731226719⟩, ⟨-968057380416700151930309, -968057380416699446025462⟩⟩, ⟨⟨-846257518198776220269357, -846257518198775944662952⟩, ⟨-490385748857828347180548, -490385748857828071563648⟩⟩, ⟨⟨2620175763682510481691, 2620175763682602094552⟩, ⟨416349600998384703160833, 416349600998384794768115⟩⟩, ⟨⟨128550626357180684730222, 128550626357180710174743⟩, ⟨-76672640122959486490848, -76672640122959461044937⟩⟩, ⟨⟨-39082039707774420158411, -39082039707774414358785⟩, ⟨-21425249036044865885864, -21425249036044860086359⟩⟩, ⟨⟨321898175261147308448, 321898175261148368511⟩, ⟨10694225312440585537586, 10694225312440586597623⟩⟩, ⟨⟨1684029992069921497691, 1684029992069921647583⟩, ⟨-1059765385175379052923, -1059765385175378903023⟩⟩, ⟨⟨-238918417346845779973, -238918417346845764608⟩, ⟨-123616755786192417447, -123616755786192402082⟩⟩, ⟨⟨1274384372123730387, 1274384372123731479⟩, ⟨23485739012921704194, 23485739012921705286⟩⟩, ⟨⟨831733159172575625, 831733159172575690⟩, ⟨-552009424883113348, -552009424883113284⟩⟩],
  [o],
  [⟨⟨-265723507642, -265723507515⟩, ⟨-287427956528, -287427956401⟩⟩, ⟨⟨-21554349122236, -21554349119890⟩, ⟨4684389002477, 4684389004820⟩⟩, ⟨⟨-188026599292658, -188026599271769⟩, ⟨570912716422649, 570912716443545⟩⟩, ⟨⟨6962079736524989, 6962079736647013⟩, ⟨7929788917314330, 7929788917436345⟩⟩, ⟨⟨131769259682028709, 131769259682561385⟩, ⟨-25123084080815055, -25123084080282377⟩⟩, ⟨⟨443377959545667892, 443377959547555189⟩, ⟨-1238879323478143979, -1238879323476256673⟩⟩, ⟨⟨-6637565856478884381, -6637565856473113236⟩, ⟨-7959872192858343826, -7959872192852572688⟩⟩, ⟨⟨-66458838306204728985, -66458838306188761265⟩, ⟨10932265359314727472, 10932265359330695155⟩⟩, ⟨⟨-132795433074459453893, -132795433074418190395⟩, ⟨343441378706971713463, 343441378707012977146⟩⟩, ⟨⟨1066960487739157907063, 1066960487739258972805⟩, ⟨1347062436429415459917, 1347062436429516525385⟩⟩, ⟨⟨6856655348529682057534, 6856655348529916757581⟩, ⟨-951994068426596340963, -951994068426361642260⟩⟩, ⟨⟨9319447998859443922768, 9319447998859956745272⟩, ⟨-22421256548275946225626, -22421256548275433396509⟩⟩, ⟨⟨-44890069894269148994813, -44890069894268104925864⟩, ⟨-59664367066033647031664, -59664367066032602972903⟩⟩, ⟨⟨-201082397674639056996854, -201082397674637093709067⟩, ⟨22862155274796378240084, 22862155274798341519021⟩⟩, ⟨⟨-197346603014887453363846, -197346603014884066786149⟩, ⟨443625300304361870351074, 443625300304365256987478⟩⟩, ⟨⟨601479872944264883722738, 601479872944270215768038⟩, ⟨841624686408196016708808, 841624686408201348663087⟩⟩, ⟨⟨1954143347247178462743438, 1954143347247186095495753⟩, ⟨-173998708335912400903314, -173998708335904768123112⟩⟩, ⟨⟨1421588263943650948023791, 1421588263943660849836627⟩, ⟨-2997449234918162857813386, -2997449234918152955885680⟩⟩, ⟨⟨-2811639213307025809791997, -2811639213307014200682461⟩, ⟨-4142323449179048145178880, -4142323449179036536269594⟩⟩, ⟨⟨-6730176479838953464653453, -6730176479838941199851057⟩, ⟨436337441230747964850068, 436337441230760229787474⟩⟩, ⟨⟨-3648386401058108793403025, -3648386401058097154876554⟩, ⟨7239422190506119800115726, 7239422190506131438648679⟩⟩, ⟨⟨4704542319027360984429816, 4704542319027370873122376⟩, ⟨7300165828995722314160395, 7300165828995732202763806⟩⟩, ⟨⟨8269145105740772705539584, 8269145105740780197905533⟩, ⟨-338863207117711883438222, -338863207117704390994758⟩⟩, ⟨⟨3295604226169433769204486, 3295604226169438805647771⟩, ⟨-6170774474641484544219498, -6170774474641479507806871⟩⟩, ⟨⟨-2725845937596846297250004, -2725845937596843308251895⟩, ⟨-4457997139832990881302970, -4457997139832987892303732⟩⟩, ⟨⟨-3431036263024596418757017, -3431036263024594863301644⟩, ⟨59471312613065955727243, 59471312613067511187987⟩⟩, ⟨⟨-968057380416700151181828, -968057380416699447959194⟩, ⟨1713988779925302027178150, 1713988779925302730397691⟩⟩, ⟨⟨490385748857828072630497, 490385748857828346349755⟩, ⟨846257518198775946048765, 846257518198776219768921⟩⟩, ⟨⟨416349600998384703925026, 416349600998384794443201⟩, ⟨2620175763682511076090, 2620175763682601594128⟩⟩, ⟨⟨76672640122959461342312, 76672640122959486310521⟩, ⟨-128550626357180710006792, -128550626357180685038580⟩⟩, ⟨⟨-21425249036044865815049, -21425249036044860179802⟩, ⟨-39082039707774420104415, -39082039707774414469164⟩⟩, ⟨⟨-10694225312440586580523, -10694225312440585570668⟩, ⟨-321898175261148344380, -321898175261147334527⟩⟩, ⟨⟨-1059765385175379047899, -1059765385175378909992⟩, ⟨1684029992069921505004, 1684029992069921642913⟩⟩, ⟨⟨123616755786192403035, 123616755786192416682⟩, ⟨238918417346845765692, 238918417346845779339⟩⟩, ⟨⟨23485739012921704299, 23485739012921705231⟩, ⟨1274384372123730473, 1274384372123731406⟩⟩, ⟨⟨552009424883113291, 552009424883113345⟩, ⟨-831733159172575685, -831733159172575632⟩⟩],
  [o],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨17953614660612838, 17953614660612874⟩, ⟨-19, 18⟩⟩, ⟨⟨-92, 93⟩, ⟨-93, 93⟩⟩, ⟨⟨-2682320678464185, -2682320678463627⟩, ⟨-277, 281⟩⟩, ⟨⟨-601, 600⟩, ⟨-599, 602⟩⟩, ⟨⟨8738918596429614, 8738918596431565⟩, ⟨-975, 976⟩⟩, ⟨⟨-1215, 1216⟩, ⟨-1215, 1215⟩⟩, ⟨⟨-1017778694990223141, -1017778694990220818⟩, ⟨-1160, 1160⟩⟩, ⟨⟨-839, 838⟩, ⟨-836, 836⟩⟩, ⟨⟨33373907711855862, 33373907711856749⟩, ⟨-446, 445⟩⟩, ⟨⟨-164, 166⟩, ⟨-169, 167⟩⟩, ⟨⟨-39120953487548078, -39120953487547996⟩, ⟨-40, 41⟩⟩, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, o, z, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨17777530542382716, 17777530542382753⟩, ⟨-17, 18⟩⟩, ⟨⟨-96, 94⟩, ⟨-95, 96⟩⟩, ⟨⟨-2662678475321777, -2662678475321193⟩, ⟨-291, 291⟩⟩, ⟨⟨-624, 624⟩, ⟨-628, 626⟩⟩, ⟨⟨8703883919954435, 8703883919956434⟩, ⟨-998, 998⟩⟩, ⟨⟨-1214, 1213⟩, ⟨-1216, 1213⟩⟩, ⟨⟨-1017108864542757291, -1017108864542755021⟩, ⟨-1133, 1136⟩⟩, ⟨⟨-807, 809⟩, ⟨-808, 807⟩⟩, ⟨⟨33349496329366467, 33349496329367323⟩, ⟨-430, 428⟩⟩, ⟨⟨-162, 160⟩, ⟨-164, 164⟩⟩, ⟨⟨-39090489178583585, -39090489178583505⟩, ⟨-40, 40⟩⟩, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, o, z, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨17603323702355364, 17603323702355400⟩, ⟨-18, 18⟩⟩, ⟨⟨-95, 94⟩, ⟨-95, 94⟩⟩, ⟨⟨-2643200487081162, -2643200487080577⟩, ⟨-290, 292⟩⟩, ⟨⟨-636, 640⟩, ⟨-640, 638⟩⟩, ⟨⟨8669036008042199, 8669036008044273⟩, ⟨-1038, 1038⟩⟩, ⟨⟨-1278, 1280⟩, ⟨-1278, 1279⟩⟩, ⟨⟨-1016441000016633032, -1016441000016630622⟩, ⟨-1204, 1203⟩⟩, ⟨⟨-854, 856⟩, ⟨-853, 855⟩⟩, ⟨⟨33325185981230467, 33325185981231361⟩, ⟨-449, 450⟩⟩, ⟨⟨-167, 166⟩, ⟨-167, 168⟩⟩, ⟨⟨-39060127408771777, -39060127408771695⟩, ⟨-40, 40⟩⟩, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, o, z, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨17430972771932722, 17430972771932755⟩, ⟨-16, 17⟩⟩, ⟨⟨-91, 92⟩, ⟨-92, 92⟩⟩, ⟨⟨-2623885194553940, -2623885194553364⟩, ⟨-286, 287⟩⟩, ⟨⟨-628, 626⟩, ⟨-631, 628⟩⟩, ⟨⟨8634373594937200, 8634373594939241⟩, ⟨-1022, 1021⟩⟩, ⟨⟨-1254, 1254⟩, ⟨-1256, 1254⟩⟩, ⟨⟨-1015775082535103747, -1015775082535101400⟩, ⟨-1172, 1171⟩⟩, ⟨⟨-829, 827⟩, ⟨-827, 827⟩⟩, ⟨⟨33300975915669463, 33300975915670328⟩, ⟨-434, 436⟩⟩, ⟨⟨-161, 162⟩, ⟨-164, 163⟩⟩, ⟨⟨-39029867716729619, -39029867716729538⟩, ⟨-40, 39⟩⟩, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, o, z, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨17260456638125258, 17260456638125295⟩, ⟨-19, 18⟩⟩, ⟨⟨-97, 95⟩, ⟨-97, 98⟩⟩, ⟨⟨-2604731093715116, -2604731093714512⟩, ⟨-299, 301⟩⟩, ⟨⟨-649, 648⟩, ⟨-651, 650⟩⟩, ⟨⟨8599895425380201, 8599895425382268⟩, ⟨-1034, 1035⟩⟩, ⟨⟨-1251, 1252⟩, ⟨-1252, 1248⟩⟩, ⟨⟨-1015111093437797473, -1015111093437795142⟩, ⟨-1165, 1164⟩⟩, ⟨⟨-831, 831⟩, ⟨-829, 828⟩⟩, ⟨⟨33276865387041259, 33276865387042139⟩, ⟨-442, 439⟩⟩, ⟨⟨-166, 165⟩, ⟨-168, 165⟩⟩, ⟨⟨-38999709643176985, -38999709643176903⟩, ⟨-40, 40⟩⟩, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, o, z],
  [z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, z, ⟨⟨17091754440386515, 17091754440386552⟩, ⟨-19, 19⟩⟩, ⟨⟨-99, 99⟩, ⟨-98, 99⟩⟩, ⟨⟨-2585736695543294, -2585736695542682⟩, ⟨-307, 306⟩⟩, ⟨⟨-658, 658⟩, ⟨-660, 658⟩⟩, ⟨⟨8565600254506616, 8565600254508703⟩, ⟨-1042, 1044⟩⟩, ⟨⟨-1249, 1250⟩, ⟨-1251, 1249⟩⟩, ⟨⟨-1014449014278130556, -1014449014278128255⟩, ⟨-1149, 1150⟩⟩, ⟨⟨-810, 812⟩, ⟨-807, 808⟩⟩, ⟨⟨33252853655788837, 33252853655789690⟩, ⟨-429, 429⟩⟩, ⟨⟨-160, 160⟩, ⟨-164, 164⟩⟩, ⟨⟨-38969652730928797, -38969652730928716⟩, ⟨-39, 40⟩⟩, ⟨⟨-6, 6⟩, ⟨-4, 4⟩⟩, o]
]

private def m18ELit10 : List (List CFpIv) := [
  [o, ⟨⟨-6158601678849939, -6158601678849892⟩, ⟨-21, 21⟩⟩, ⟨⟨1215722580806784, 1215722580806915⟩, ⟨-67, 68⟩⟩, ⟨⟨-7762758849240702, -7762758849240566⟩, ⟨-69, 68⟩⟩, ⟨⟨150144744828, 150144744895⟩, ⟨-33, 36⟩⟩, ⟨⟨-93936308, -93936280⟩, ⟨-13, 15⟩⟩, ⟨⟨1883763, 1883768⟩, ⟨-3, 2⟩⟩, z, z, z, z, z, z, z, z, z, z, z],
  [z, o, ⟨⟨-6160134651779189, -6160134651779143⟩, ⟨-21, 21⟩⟩, ⟨⟨1216326864811423, 1216326864811562⟩, ⟨-71, 70⟩⟩, ⟨⟨-7768547192111371, -7768547192111225⟩, ⟨-73, 72⟩⟩, ⟨⟨150314416804, 150314416878⟩, ⟨-38, 39⟩⟩, ⟨⟨-94078621, -94078594⟩, ⟨-13, 12⟩⟩, ⟨⟨1887342, 1887346⟩, ⟨-3, 2⟩⟩, z, z, z, z, z, z, z, z, z, z],
  [z, z, o, ⟨⟨-6161668134986226, -6161668134986180⟩, ⟨-21, 21⟩⟩, ⟨⟨1216931499480676, 1216931499480809⟩, ⟨-67, 66⟩⟩, ⟨⟨-7774340333008303, -7774340333008169⟩, ⟨-66, 67⟩⟩, ⟨⟨150484300939, 150484301006⟩, ⟨-34, 35⟩⟩, ⟨⟨-94221169, -94221142⟩, ⟨-12, 12⟩⟩, ⟨⟨1890927, 1890932⟩, ⟨-2, 3⟩⟩, z, z, z, z, z, z, z, z, z],
  [z, z, z, o, ⟨⟨-6163202128671266, -6163202128671218⟩, ⟨-20, 21⟩⟩, ⟨⟨1217536485042071, 1217536485042203⟩, ⟨-66, 68⟩⟩, ⟨⟨-7780138276258767, -7780138276258626⟩, ⟨-74, 72⟩⟩, ⟨⟨150654397513, 150654397587⟩, ⟨-35, 36⟩⟩, ⟨⟨-94363956, -94363928⟩, ⟨-13, 14⟩⟩, ⟨⟨1894519, 1894524⟩, ⟨-2, 3⟩⟩, z, z, z, z, z, z, z, z],
  [z, z, z, z, o, ⟨⟨-6164736633034599, -6164736633034554⟩, ⟨-21, 21⟩⟩, ⟨⟨1218141821723296, 1218141821723429⟩, ⟨-67, 70⟩⟩, ⟨⟨-7785941026194177, -7785941026194038⟩, ⟨-71, 70⟩⟩, ⟨⟨150824706828, 150824706895⟩, ⟨-34, 37⟩⟩, ⟨⟨-94506976, -94506948⟩, ⟨-13, 14⟩⟩, ⟨⟨1898119, 1898123⟩, ⟨-3, 3⟩⟩, z, z, z, z, z, z, z],
  [z, z, z, z, z, o, ⟨⟨-6166271648276612, -6166271648276566⟩, ⟨-21, 21⟩⟩, ⟨⟨1218747509752206, 1218747509752345⟩, ⟨-70, 69⟩⟩, ⟨⟨-7791748587150145, -7791748587149998⟩, ⟨-73, 71⟩⟩, ⟨⟨150995229165, 150995229236⟩, ⟨-36, 37⟩⟩, ⟨⟨-94650232, -94650205⟩, ⟨-14, 13⟩⟩, ⟨⟨1901726, 1901730⟩, ⟨-3, 2⟩⟩, z, z, z, z, z, z],
  [z, z, z, z, z, z, o, ⟨⟨-6167807174597767, -6167807174597720⟩, ⟨-21, 21⟩⟩, ⟨⟨1219353549356816, 1219353549356955⟩, ⟨-72, 68⟩⟩, ⟨⟨-7797560963466445, -7797560963466299⟩, ⟨-72, 72⟩⟩, ⟨⟨151165964821, 151165964894⟩, ⟨-37, 37⟩⟩, ⟨⟨-94793727, -94793700⟩, ⟨-13, 14⟩⟩, ⟨⟨1905341, 1905345⟩, ⟨-3, 2⟩⟩, z, z, z, z, z],
  [z, z, z, z, z, z, z, o, ⟨⟨-6169343212198617, -6169343212198570⟩, ⟨-21, 21⟩⟩, ⟨⟨1219959940765301, 1219959940765433⟩, ⟨-68, 69⟩⟩, ⟨⟨-7803378159487046, -7803378159486910⟩, ⟨-67, 66⟩⟩, ⟨⟨151336914091, 151336914158⟩, ⟨-32, 34⟩⟩, ⟨⟨-94937459, -94937432⟩, ⟨-12, 11⟩⟩, ⟨⟨1908962, 1908966⟩, ⟨-1, 2⟩⟩, z, z, z, z],
  [z, z, z, z, z, z, z, z, o, ⟨⟨-6170879761279801, -6170879761279753⟩, ⟨-21, 21⟩⟩, ⟨⟨1220566684205982, 1220566684206117⟩, ⟨-68, 68⟩⟩, ⟨⟨-7809200179560115, -7809200179559976⟩, ⟨-71, 70⟩⟩, ⟨⟨151508077262, 151508077331⟩, ⟨-36, 35⟩⟩, ⟨⟨-95081427, -95081402⟩, ⟨-13, 11⟩⟩, ⟨⟨1912592, 1912597⟩, ⟨-2, 2⟩⟩, z, z, z],
  [⟨⟨0, 1⟩, ⟨0, 0⟩⟩, ⟨⟨-45, 96⟩, ⟨-57, 58⟩⟩, ⟨⟨-1214, 1516⟩, ⟨-1334, 1335⟩⟩, ⟨⟨-8342, 11497⟩, ⟨-9903, 9879⟩⟩, ⟨⟨4680102, 4749459⟩, ⟨-34637, 34622⟩⟩, ⟨⟨8044947073, 8045096725⟩, ⟨-74753, 74757⟩⟩, ⟨⟨6028192048173, 6028192295614⟩, ⟨-123622, 123622⟩⟩, ⟨⟨1884289026008423, 1884289026367077⟩, ⟨-179231, 179219⟩⟩, ⟨⟨214883073132647909, 214883073133126836⟩, ⟨-239334, 239325⟩⟩, ⟨⟨6942711419629405333, 6942711419630001950⟩, ⟨-298147, 298152⟩⟩, ⟨⟨50397628547332967271, 50397628547333686326⟩, ⟨-359498, 359492⟩⟩, ⟨⟨98856371844075296904, 98856371844076137168⟩, ⟨-419977, 419947⟩⟩, ⟨⟨54034224268425189127, 54034224268425982605⟩, ⟨-396579, 396543⟩⟩, ⟨⟨-34969278563279046109, -34969278563278570209⟩, ⟨-237918, 237888⟩⟩, ⟨⟨-81849111420011841946, -81849111420011685724⟩, ⟨-77957, 77953⟩⟩, ⟨⟨-46106260681921248769, -46106260681921223397⟩, ⟨-12545, 12574⟩⟩, ⟨⟨-7464219741638457758, -7464219741638456009⟩, ⟨-836, 853⟩⟩, ⟨⟨-233851982553760656, -233851982553760619⟩, ⟨-18, 18⟩⟩],
  [⟨⟨-5, 5⟩, ⟨-5, 5⟩⟩, ⟨⟨-847, 847⟩, ⟨-847, 847⟩⟩, ⟨⟨-17018, 17018⟩, ⟨-17018, 17018⟩⟩, ⟨⟨-122866, 120931⟩, ⟨-122626, 121174⟩⟩, ⟨⟨3871639, 4718459⟩, ⟨-2368710, -1521902⟩⟩, ⟨⟨-649388950, -647646905⟩, ⟨8019626291, 8021368335⟩⟩, ⟨⟨-5021581624583, -5021579142280⟩, ⟨-3338679891185, -3338677408886⟩⟩, ⟨⟨1674237641355106, 1674237644247330⟩, ⟨-866871093560041, -866871090667803⟩⟩, ⟨⟨-6241024749751942, -6241024746406731⟩, ⟨215026798776014848, 215026798779360066⟩⟩, ⟨⟨-5980340086365139606, -5980340086361001991⟩, ⟨-3563110041751376842, -3563110041747239228⟩⟩, ⟨⟨44083917835377314266, 44083917835382367477⟩, ⟨-25278871944555520599, -25278871944550467421⟩⟩, ⟨⟨-146793336961017982, -146793336955513270⟩, ⟨101041199002223630152, 101041199002229134867⟩⟩, ⟨⟨-47719822245604545159, -47719822245600001994⟩, ⟨-29908017364437859215, -29908017364433316055⟩⟩, ⟨⟨-29847525683241946558, -29847525683239630393⟩, ⟨21223727022101260582, 21223727022103576764⟩⟩, ⟨⟨-2768428024122679004, -2768428024122056500⟩, ⟨-83900663228968568292, -83900663228967945786⟩⟩, ⟨⟨41058127966282271265, 41058127966282350519⟩, ⟨22008925175083711312, 22008925175083790564⟩⟩, ⟨⟨-6325287493981346290, -6325287493981341705⟩, ⟨4006283571934514924, 4006283571934519508⟩⟩, ⟨⟨-12790129623504765, -12790129623504649⟩, ⟨-233604622442987362, -233604622442987246⟩⟩],
  [⟨⟨-5, 5⟩, ⟨-5, 5⟩⟩, ⟨⟨-845, 845⟩, ⟨-845, 845⟩⟩, ⟨⟨-16835, 16835⟩, ⟨-16835, 16835⟩⟩, ⟨⟨-120612, 119157⟩, ⟨-120852, 118915⟩⟩, ⟨⟨-2362392, -1528221⟩, ⟨3877968, 4712129⟩⟩, ⟨⟨8019634686, 8021359941⟩, ⟨-649380546, -647655299⟩⟩, ⟨⟨-3338679883209, -3338677416810⟩, ⟨-5021581616664, -5021579150256⟩⟩, ⟨⟨-866871093553106, -866871090674811⟩, ⟨1674237641362023, 1674237644240336⟩⟩, ⟨⟨215026798776019483, 215026798779355387⟩, ⟨-6241024749747224, -6241024746411343⟩⟩, ⟨⟨-3563110041751373047, -3563110041747242995⟩, ⟨-5980340086365135802, -5980340086361005749⟩⟩, ⟨⟨-25278871944555514113, -25278871944550473801⟩, ⟨44083917835377320729, 44083917835382361063⟩⟩, ⟨⟨101041199002223636191, 101041199002229128872⟩, ⟨-146793336961011997, -146793336955519322⟩⟩, ⟨⟨-29908017364437860043, -29908017364433315306⟩, ⟨-47719822245604545962, -47719822245600001229⟩⟩, ⟨⟨21223727022101257822, 21223727022103579533⟩, ⟨-29847525683241949285, -29847525683239627566⟩⟩, ⟨⟨-83900663228968568246, -83900663228967945841⟩, ⟨-2768428024122679001, -2768428024122056592⟩⟩, ⟨⟨22008925175083711873, 22008925175083789978⟩, ⟨41058127966282271871, 41058127966282349973⟩⟩, ⟨⟨4006283571934515040, 4006283571934519412⟩, ⟨-6325287493981346181, -6325287493981341808⟩⟩, ⟨⟨-233604622442987360, -233604622442987248⟩, ⟨-12790129623504764, -12790129623504653⟩⟩],
  [⟨⟨391436540786, 391436540797⟩, ⟨-3, 4⟩⟩, ⟨⟨600970053382891, 600970053384259⟩, ⟨-462, 523⟩⟩, ⟨⟨134091863847101219, 134091863847123769⟩, ⟨-8668, 9235⟩⟩, ⟨⟨10357963227201280290, 10357963227201428783⟩, ⟨-60757, 62481⟩⟩, ⟨⟨367909634316268101593, 367909634316268734380⟩, ⟨-264787, 267062⟩⟩, ⟨⟨6914798847470720558600, 6914798847470722972179⟩, ⟨-1008624, 1009879⟩⟩, ⟨⟨74563763627633025876597, 74563763627633035358251⟩, ⟨-3964437, 3965069⟩⟩, ⟨⟨484754532816566643402503, 484754532816566679067652⟩, ⟨-15215214, 15217910⟩⟩, ⟨⟨1958255870309682137886611, 1958255870309682246427974⟩, ⟨-47684438, 47688934⟩⟩, ⟨⟨4996286539341087874260074, 4996286539341088110372042⟩, ⟨-106248230, 106251762⟩⟩, ⟨⟨8089537179517980635021152, 8089537179517980978453709⟩, ⟨-156468733, 156471284⟩⟩, ⟨⟨8258396463325670845051136, 8258396463325671165767801⟩, ⟨-146093498, 146094892⟩⟩, ⟨⟨5214682598721759256621333, 5214682598721759441972183⟩, ⟨-83422996, 83422208⟩⟩, ⟨⟨1964895581942240321856228, 1964895581942240385158900⟩, ⟨-27836269, 27834476⟩⟩, ⟨⟨415735557264640844737837, 415735557264640856681569⟩, ⟨-5071124, 5069912⟩⟩, ⟨⟨44520959824207899792119, 44520959824207900910138⟩, ⟨-451866, 451438⟩⟩, ⟨⟨1988454208538928000565, 1988454208538928043733⟩, ⟨-16343, 16238⟩⟩, ⟨⟨23515479662850685650, 23515479662850686163⟩, ⟨-187, 173⟩⟩],
  [⟨⟨-287427956521, -287427956409⟩, ⟨-265723507637, -265723507524⟩⟩, ⟨⟨570912716423753, 570912716442635⟩, ⟨-188026599291598, -188026599272714⟩⟩, ⟨⟨-25123084080798431, -25123084080300649⟩, ⟨131769259682046864, 131769259682544644⟩⟩, ⟨⟨-7959872192858261346, -7959872192852661209⟩, ⟨-6637565856478802912, -6637565856473202777⟩⟩, ⟨⟨343441378706971869179, 343441378707012842874⟩, ⟨-132795433074459313889, -132795433074418340190⟩⟩, ⟨⟨-951994068426596268831, -951994068426361716513⟩, ⟨6856655348529682144570, 6856655348529916697110⟩⟩, ⟨⟨-59664367066033647057662, -59664367066032602997779⟩, ⟨-44890069894269149019798, -44890069894268104960126⟩⟩, ⟨⟨443625300304361870812584, 443625300304365256969217⟩, ⟨-197346603014887453179554, -197346603014884067044192⟩⟩, ⟨⟨-173998708335912400122734, -173998708335904769546110⟩, ⟨1954143347247178464458737, 1954143347247186095098485⟩⟩, ⟨⟨-4142323449179048143315377, -4142323449179036539129864⟩, ⟨-2811639213307025808619117, -2811639213307014204327456⟩⟩, ⟨⟨7239422190506119803817764, 7239422190506131437259518⟩, ⟨-3648386401058108789870607, -3648386401058097156725579⟩⟩, ⟨⟨-338863207117711884067705, -338863207117704392931764⟩, ⟨8269145105740772705559261, 8269145105740780196665897⟩⟩, ⟨⟨-4457997139832990881309291, -4457997139832987889513603⟩, ⟨-2725845937596846298783833, -2725845937596843306858379⟩⟩, ⟨⟨1713988779925302025322459, 1713988779925302731226719⟩, ⟨-968057380416700151930309, -968057380416699446025462⟩⟩, ⟨⟨2620175763682510481691, 2620175763682602094552⟩, ⟨416349600998384703160833, 416349600998384794768115⟩⟩, ⟨⟨-39082039707774420158411, -39082039707774414358785⟩, ⟨-21425249036044865885864, -21425249036044860086359⟩⟩, ⟨⟨1684029992069921497691, 1684029992069921647583⟩, ⟨-1059765385175379052923, -1059765385175378903023⟩⟩, ⟨⟨1274384372123730387, 1274384372123731479⟩, ⟨23485739012921704194, 23485739012921705286⟩⟩],
  [⟨⟨-265723507642, -265723507515⟩, ⟨-287427956528, -287427956401⟩⟩, ⟨⟨-188026599292658, -188026599271769⟩, ⟨570912716422649, 570912716443545⟩⟩, ⟨⟨131769259682028709, 131769259682561385⟩, ⟨-25123084080815055, -25123084080282377⟩⟩, ⟨⟨-6637565856478884381, -6637565856473113236⟩, ⟨-7959872192858343826, -7959872192852572688⟩⟩, ⟨⟨-132795433074459453893, -132795433074418190395⟩, ⟨343441378706971713463, 343441378707012977146⟩⟩, ⟨⟨6856655348529682057534, 6856655348529916757581⟩, ⟨-951994068426596340963, -951994068426361642260⟩⟩, ⟨⟨-44890069894269148994813, -44890069894268104925864⟩, ⟨-59664367066033647031664, -59664367066032602972903⟩⟩, ⟨⟨-197346603014887453363846, -197346603014884066786149⟩, ⟨443625300304361870351074, 443625300304365256987478⟩⟩, ⟨⟨1954143347247178462743438, 1954143347247186095495753⟩, ⟨-173998708335912400903314, -173998708335904768123112⟩⟩, ⟨⟨-2811639213307025809791997, -2811639213307014200682461⟩, ⟨-4142323449179048145178880, -4142323449179036536269594⟩⟩, ⟨⟨-3648386401058108793403025, -3648386401058097154876554⟩, ⟨7239422190506119800115726, 7239422190506131438648679⟩⟩, ⟨⟨8269145105740772705539584, 8269145105740780197905533⟩, ⟨-338863207117711883438222, -338863207117704390994758⟩⟩, ⟨⟨-2725845937596846297250004, -2725845937596843308251895⟩, ⟨-4457997139832990881302970, -4457997139832987892303732⟩⟩, ⟨⟨-968057380416700151181828, -968057380416699447959194⟩, ⟨1713988779925302027178150, 1713988779925302730397691⟩⟩, ⟨⟨416349600998384703925026, 416349600998384794443201⟩, ⟨2620175763682511076090, 2620175763682601594128⟩⟩, ⟨⟨-21425249036044865815049, -21425249036044860179802⟩, ⟨-39082039707774420104415, -39082039707774414469164⟩⟩, ⟨⟨-1059765385175379047899, -1059765385175378909992⟩, ⟨1684029992069921505004, 1684029992069921642913⟩⟩, ⟨⟨23485739012921704299, 23485739012921705231⟩, ⟨1274384372123730473, 1274384372123731406⟩⟩],
  [z, z, z, z, z, z, z, z, z, ⟨⟨17953614660612838, 17953614660612874⟩, ⟨-19, 18⟩⟩, ⟨⟨-2682320678464185, -2682320678463627⟩, ⟨-277, 281⟩⟩, ⟨⟨8738918596429614, 8738918596431565⟩, ⟨-975, 976⟩⟩, ⟨⟨-1017778694990223141, -1017778694990220818⟩, ⟨-1160, 1160⟩⟩, ⟨⟨33373907711855862, 33373907711856749⟩, ⟨-446, 445⟩⟩, ⟨⟨-39120953487548078, -39120953487547996⟩, ⟨-40, 41⟩⟩, o, z, z],
  [z, z, z, z, z, z, z, z, z, z, ⟨⟨17603323702355364, 17603323702355400⟩, ⟨-18, 18⟩⟩, ⟨⟨-2643200487081162, -2643200487080577⟩, ⟨-290, 292⟩⟩, ⟨⟨8669036008042199, 8669036008044273⟩, ⟨-1038, 1038⟩⟩, ⟨⟨-1016441000016633032, -1016441000016630622⟩, ⟨-1204, 1203⟩⟩, ⟨⟨33325185981230467, 33325185981231361⟩, ⟨-449, 450⟩⟩, ⟨⟨-39060127408771777, -39060127408771695⟩, ⟨-40, 40⟩⟩, o, z],
  [z, z, z, z, z, z, z, z, z, z, z, ⟨⟨17260456638125258, 17260456638125295⟩, ⟨-19, 18⟩⟩, ⟨⟨-2604731093715116, -2604731093714512⟩, ⟨-299, 301⟩⟩, ⟨⟨8599895425380201, 8599895425382268⟩, ⟨-1034, 1035⟩⟩, ⟨⟨-1015111093437797473, -1015111093437795142⟩, ⟨-1165, 1164⟩⟩, ⟨⟨33276865387041259, 33276865387042139⟩, ⟨-442, 439⟩⟩, ⟨⟨-38999709643176985, -38999709643176903⟩, ⟨-40, 40⟩⟩, o]
]

private def m18OLit10 : List (List CFpIv) := [
  [o, ⟨⟨-6159368101542351, -6159368101542305⟩, ⟨-20, 21⟩⟩, ⟨⟨1216024678990239, 1216024678990379⟩, ⟨-70, 69⟩⟩, ⟨⟨-7765652421193045, -7765652421192900⟩, ⟨-72, 72⟩⟩, ⟨⟨150229554316, 150229554384⟩, ⟨-35, 35⟩⟩, ⟨⟨-94007434, -94007408⟩, ⟨-13, 13⟩⟩, ⟨⟨1885551, 1885556⟩, ⟨-2, 3⟩⟩, z, z, z, z, z, z, z, z, z, z, z],
  [z, o, ⟨⟨-6160901329585472, -6160901329585427⟩, ⟨-21, 20⟩⟩, ⟨⟨1216629138298757, 1216629138298890⟩, ⟨-66, 69⟩⟩, ⟨⟨-7771443162536195, -7771443162536060⟩, ⟨-68, 67⟩⟩, ⟨⟨150399332336, 150399332404⟩, ⟨-35, 36⟩⟩, ⟨⟨-94149866, -94149840⟩, ⟨-13, 12⟩⟩, ⟨⟨1889132, 1889138⟩, ⟨-3, 2⟩⟩, z, z, z, z, z, z, z, z, z, z],
  [z, z, o, ⟨⟨-6162435068006480, -6162435068006433⟩, ⟨-21, 21⟩⟩, ⟨⟨1217233948385626, 1217233948385763⟩, ⟨-69, 68⟩⟩, ⟨⟨-7777238704068729, -7777238704068589⟩, ⟨-70, 71⟩⟩, ⟨⟨150569322653, 150569322722⟩, ⟨-35, 33⟩⟩, ⟨⟨-94292532, -94292505⟩, ⟨-13, 11⟩⟩, ⟨⟨1892723, 1892726⟩, ⟨-2, 2⟩⟩, z, z, z, z, z, z, z, z, z],
  [z, z, z, o, ⟨⟨-6163969317005624, -6163969317005577⟩, ⟨-21, 21⟩⟩, ⟨⟨1217839109478465, 1217839109478600⟩, ⟨-69, 70⟩⟩, ⟨⟨-7783039050119980, -7783039050119833⟩, ⟨-72, 73⟩⟩, ⟨⟨150739525558, 150739525635⟩, ⟨-38, 40⟩⟩, ⟨⟨-94435434, -94435407⟩, ⟨-13, 12⟩⟩, ⟨⟨1896318, 1896322⟩, ⟨-2, 3⟩⟩, z, z, z, z, z, z, z, z],
  [z, z, z, z, o, ⟨⟨-6165504076783243, -6165504076783195⟩, ⟨-21, 21⟩⟩, ⟨⟨1218444621805046, 1218444621805178⟩, ⟨-68, 67⟩⟩, ⟨⟨-7788844205023450, -7788844205023314⟩, ⟨-67, 69⟩⟩, ⟨⟨150909941350, 150909941419⟩, ⟨-36, 33⟩⟩, ⟨⟨-94578574, -94578547⟩, ⟨-13, 12⟩⟩, ⟨⟨1899921, 1899926⟩, ⟨-2, 2⟩⟩, z, z, z, z, z, z, z],
  [z, z, z, z, z, o, ⟨⟨-6167039347539763, -6167039347539716⟩, ⟨-22, 23⟩⟩, ⟨⟨1219050485593291, 1219050485593432⟩, ⟨-72, 70⟩⟩, ⟨⟨-7794654173116848, -7794654173116710⟩, ⟨-69, 68⟩⟩, ⟨⟨151080570312, 151080570380⟩, ⟨-35, 35⟩⟩, ⟨⟨-94721950, -94721923⟩, ⟨-13, 14⟩⟩, ⟨⟨1903532, 1903537⟩, ⟨-3, 2⟩⟩, z, z, z, z, z, z],
  [z, z, z, z, z, z, o, ⟨⟨-6168575129475692, -6168575129475647⟩, ⟨-21, 21⟩⟩, ⟨⟨1219656701071310, 1219656701071443⟩, ⟨-68, 68⟩⟩, ⟨⟨-7800468958742046, -7800468958741904⟩, ⟨-72, 72⟩⟩, ⟨⟨151251412734, 151251412809⟩, ⟨-37, 37⟩⟩, ⟨⟨-94865563, -94865536⟩, ⟨-13, 13⟩⟩, ⟨⟨1907151, 1907155⟩, ⟨-2, 2⟩⟩, z, z, z, z, z],
  [z, z, z, z, z, z, z, o, ⟨⟨-6170111422791624, -6170111422791578⟩, ⟨-20, 21⟩⟩, ⟨⟨1220263268467341, 1220263268467471⟩, ⟨-67, 67⟩⟩, ⟨⟨-7806288566245098, -7806288566244963⟩, ⟨-70, 67⟩⟩, ⟨⟨151422468918, 151422468991⟩, ⟨-36, 36⟩⟩, ⟨⟨-95009414, -95009387⟩, ⟨-14, 14⟩⟩, ⟨⟨1910776, 1910781⟩, ⟨-2, 2⟩⟩, z, z, z, z],
  [z, z, z, z, z, z, z, z, o, ⟨⟨-6171648227688240, -6171648227688193⟩, ⟨-21, 20⟩⟩, ⟨⟨1220870188009799, 1220870188009933⟩, ⟨-67, 67⟩⟩, ⟨⟨-7812112999976266, -7812112999976129⟩, ⟨-68, 69⟩⟩, ⟨⟨151593739154, 151593739224⟩, ⟨-35, 37⟩⟩, ⟨⟨-95153504, -95153475⟩, ⟨-14, 14⟩⟩, ⟨⟨1914409, 1914414⟩, ⟨-2, 3⟩⟩, z, z, z],
  [⟨⟨-16, 3⟩, ⟨-4, 4⟩⟩, ⟨⟨-427, 284⟩, ⟨-333, 330⟩⟩, ⟨⟨-4372, 3821⟩, ⟨-4063, 4073⟩⟩, ⟨⟨-104116, -64106⟩, ⟨-19956, 19981⟩⟩, ⟨⟨-215775490, -215668878⟩, ⟨-53244, 53248⟩⟩, ⟨⟨-244470871629, -244470674805⟩, ⟨-98327, 98322⟩⟩, ⟨⟨-119607813886470, -119607813585043⟩, ⟨-150613, 150618⟩⟩, ⟨⟨-23115157970688727, -23115157970270368⟩, ⟨-209058, 209072⟩⟩, ⟨⟨-1459868120934440069, -1459868120933901560⟩, ⟨-269095, 269095⟩⟩, ⟨⟨-22396295539627819705, -22396295539627164145⟩, ⟨-327683, 327680⟩⟩, ⟨⟨-82014929595615512301, -82014929595614726589⟩, ⟨-392783, 392804⟩⟩, ⟨⟨-88298755140603179881, -88298755140602327226⟩, ⟨-426082, 426118⟩⟩, ⟨⟨-9143765922164204084, -9143765922163546167⟩, ⟨-328858, 328891⟩⟩, ⟨⟨68654230843995789708, 68654230843996085582⟩, ⟨-147824, 147847⟩⟩, ⟨⟨71160150210597336184, 71160150210597405413⟩, ⟨-34459, 34443⟩⟩, ⟨⟨21978774215845138600, 21978774215845146127⟩, ⟨-3704, 3678⟩⟩, ⟨⟨1704161942679393170, 1704161942679393472⟩, ⟨-146, 141⟩⟩, ⟨⟨14545027835068710, 14545027835068714⟩, ⟨-2, 2⟩⟩],
  [⟨⟨-106, 106⟩, ⟨-106, 106⟩⟩, ⟨⟨-4439, 4439⟩, ⟨-4439, 4439⟩⟩, ⟨⟨-50617, 50646⟩, ⟨-50637, 50626⟩⟩, ⟨⟨-254226, 236280⟩, ⟨-162034, 328476⟩⟩, ⟨⟨-177104506, -175821118⟩, ⟨-124787104, -123503700⟩⟩, ⟨⟨220008123717, 220010280684⟩, ⟨-106738385946, -106736228989⟩⟩, ⟨⟨-6513310794905, -6513308081086⟩, ⟨119481310419835, 119481313133664⟩⟩, ⟨⟨-19588028834626719, -19588028831543393⟩, ⟨-12306031811169725, -12306031808086422⟩⟩, ⟨⟨1281473867055701988, 1281473867059404045⟩, ⟨-704319098283590716, -704319098279888658⟩⟩, ⟨⟨-170225105972672955, -170225105968065267⟩, ⟨22501000633088626437, 22501000633093234145⟩⟩, ⟨⟨-72005753278695958956, -72005753278690566109⟩, ⟨-41616659961387646859, -41616659961382253999⟩⟩, ⟨⟨79340654579907164027, 79340654579912410280⟩, ⟨-44824758477980278837, -44824758477975032580⟩⟩, ⟨⟨-3079428703183585332, -3079428703180100877⟩, ⟨9591722932726927275, 9591722932730411723⟩⟩, ⟨⟨63149181642101408445, 63149181642102719376⟩, ⟨32714286442148665491, 32714286442149976411⟩⟩, ⟨⟨-61552517025769877274, -61552517025769632290⟩, ⟨38046113282340818017, 38046113282341063003⟩⟩, ⟨⟨-784890736053310103, -784890736053289079⟩, ⟨-22095387770480188874, -22095387770480167846⟩⟩, ⟨⟨1516730568815947667, 1516730568815948486⟩, ⟨782120751168381196, 782120751168382016⟩⟩, ⟨⟨-12118478347681857, -12118478347681845⟩, ⟨8043757782092201, 8043757782092213⟩⟩],
  [⟨⟨-106, 106⟩, ⟨-106, 106⟩⟩, ⟨⟨-4412, 4412⟩, ⟨-4412, 4412⟩⟩, ⟨⟨-49893, 49904⟩, ⟨-49913, 49884⟩⟩, ⟨⟨-324403, 157956⟩, ⟨-232207, 250156⟩⟩, ⟨⟨123511592, 124779203⟩, ⟨175829000, 177096622⟩⟩, ⟨⟨106736237241, 106738377728⟩, ⟨-220010272447, -220008131952⟩⟩, ⟨⟨-119481313126057, -119481310427448⟩, ⟨6513308088653, 6513310787237⟩⟩, ⟨⟨12306031808092254, 12306031811163776⟩, ⟨19588028831549295, 19588028834620827⟩⟩, ⟨⟨704319098279892457, 704319098283586951⟩, ⟨-1281473867059400231, -1281473867055705726⟩⟩, ⟨⟨-22501000633093229266, -22501000633088631275⟩, ⟨170225105968070159, 170225105972668135⟩⟩, ⟨⟨41616659961382261272, 41616659961387639685⟩, ⟨72005753278690573313, 72005753278695951720⟩⟩, ⟨⟨44824758477975035410, 44824758477980275992⟩, ⟨-79340654579912407490, -79340654579907166893⟩⟩, ⟨⟨-9591722932730414661, -9591722932726924422⟩, ⟨3079428703180098012, 3079428703183588244⟩⟩, ⟨⟨-32714286442149977694, -32714286442148664116⟩, ⟨-63149181642102720696, -63149181642101407124⟩⟩, ⟨⟨-38046113282341062409, -38046113282340818697⟩, ⟨61552517025769632928, 61552517025769876636⟩⟩, ⟨⟨22095387770480168161, 22095387770480188578⟩, ⟨784890736053289400, 784890736053309818⟩⟩, ⟨⟨-782120751168381989, -782120751168381216⟩, ⟨-1516730568815948466, -1516730568815947693⟩⟩, ⟨⟨-8043757782092213, -8043757782092201⟩, ⟨12118478347681845, 12118478347681857⟩⟩],
  [⟨⟨-22055533882462, -22055533882277⟩, ⟨-67, 56⟩⟩, ⟨⟨-10549424115050314, -10549424115043835⟩, ⟨-2581, 2361⟩⟩, ⟨⟨-1315185950231992386, -1315185950231929682⟩, ⟨-26131, 25019⟩⟩, ⟨⟨-67303386628350131239, -67303386628349815202⟩, ⟨-133482, 131300⟩⟩, ⟨⟨-1716753285476858785195, -1716753285476857549314⟩, ⟨-519587, 517666⟩⟩, ⟨⟨-24251011541011190134212, -24251011541011185367790⟩, ⟨-1989003, 1988336⟩⟩, ⟨⟨-202075725897548213917685, -202075725897548195231603⟩, ⟨-7875548, 7874163⟩⟩, ⟨⟨-1032665711948129851115499, -1032665711948129786622787⟩, ⟨-27922508, 27918572⟩⟩, ⟨⟨-3311031739894413556034454, -3311031739894413388225610⟩, ⟨-74708556, 74704327⟩⟩, ⟨⟨-6730240337182286803112323, -6730240337182286502810744⟩, ⟨-136191208, 136188284⟩⟩, ⟨⟨-8666131085660065361879093, -8666131085660065010321992⟩, ⟨-160404701, 160402558⟩⟩, ⟨⟨-6980975904828933747594804, -6980975904828933488051258⟩, ⟨-117687654, 117687344⟩⟩, ⟨⟨-3424890017848354955358253, -3424890017848354839265132⟩, ⟨-51718178, 51719721⟩⟩, ⟨⟨-976442807147971580000321, -976442807147971550224331⟩, ⟨-12884652, 12886266⟩⟩, ⟨⟨-149484849740852309405567, -149484849740852305380096⟩, ⟨-1670134, 1670909⟩⟩, ⟨⟨-10689754617176476216871, -10689754617176475967528⟩, ⟨-97480, 97695⟩⟩, ⟨⟨-268890535945166618042, -268890535945166612472⟩, ⟨-2001, 2047⟩⟩, ⟨⟨-998245687807855561, -998245687807855530⟩, ⟨-9, 11⟩⟩],
  [⟨⟨-4684389004714, -4684389002618⟩, ⟨21554349120027, 21554349122123⟩⟩, ⟨⟨-7929788917431332, -7929788917319369⟩, ⟨-6962079736642376, -6962079736530418⟩⟩, ⟨⟨1238879323476303569, 1238879323478102088⟩, ⟨-443377959547510528, -443377959545712001⟩⟩, ⟨⟨-10932265359330570235, -10932265359314856124⟩, ⟨66458838306188896385, 66458838306204610481⟩⟩, ⟨⟨-1347062436429516412131, -1347062436429415595712⟩, ⟨-1066960487739258855179, -1066960487739158038779⟩⟩, ⟨⟨22421256548275433435272, 22421256548275946220554⟩, ⟨-9319447998859956730961, -9319447998859443946560⟩⟩, ⟨⟨-22862155274798341496373, -22862155274796378329657⟩, ⟨201082397674637093858996, 201082397674639057033446⟩⟩, ⟨⟨-841624686408201348380073, -841624686408196017522788⟩, ⟨-601479872944270215526087, -601479872944264884660002⟩⟩, ⟨⟨2997449234918152958661106, 2997449234918162857162019⟩, ⟨-1421588263943660848090032, -1421588263943650949738194⟩⟩, ⟨⟨-436337441230760228034383, -436337441230747968802253⟩, ⟨6730176479838941203538107, 6730176479838953462878035⟩⟩, ⟨⟨-7300165828995732200210138, -7300165828995722315332423⟩, ⟨-4704542319027370872531909, -4704542319027360987403828⟩⟩, ⟨⟨6170774474641479506802709, 6170774474641484544478430⟩, ⟨-3295604226169438804767716, -3295604226169433767223238⟩⟩, ⟨⟨-59471312613067513283105, -59471312613065954579756⟩, ⟨3431036263024594860674281, 3431036263024596419324684⟩⟩, ⟨⟨-846257518198776220269357, -846257518198775944662952⟩, ⟨-490385748857828347180548, -490385748857828071563648⟩⟩, ⟨⟨128550626357180684730222, 128550626357180710174743⟩, ⟨-76672640122959486490848, -76672640122959461044937⟩⟩, ⟨⟨321898175261147308448, 321898175261148368511⟩, ⟨10694225312440585537586, 10694225312440586597623⟩⟩, ⟨⟨-238918417346845779973, -238918417346845764608⟩, ⟨-123616755786192417447, -123616755786192402082⟩⟩, ⟨⟨831733159172575625, 831733159172575690⟩, ⟨-552009424883113348, -552009424883113284⟩⟩],
  [⟨⟨-21554349122236, -21554349119890⟩, ⟨4684389002477, 4684389004820⟩⟩, ⟨⟨6962079736524989, 6962079736647013⟩, ⟨7929788917314330, 7929788917436345⟩⟩, ⟨⟨443377959545667892, 443377959547555189⟩, ⟨-1238879323478143979, -1238879323476256673⟩⟩, ⟨⟨-66458838306204728985, -66458838306188761265⟩, ⟨10932265359314727472, 10932265359330695155⟩⟩, ⟨⟨1066960487739157907063, 1066960487739258972805⟩, ⟨1347062436429415459917, 1347062436429516525385⟩⟩, ⟨⟨9319447998859443922768, 9319447998859956745272⟩, ⟨-22421256548275946225626, -22421256548275433396509⟩⟩, ⟨⟨-201082397674639056996854, -201082397674637093709067⟩, ⟨22862155274796378240084, 22862155274798341519021⟩⟩, ⟨⟨601479872944264883722738, 601479872944270215768038⟩, ⟨841624686408196016708808, 841624686408201348663087⟩⟩, ⟨⟨1421588263943650948023791, 1421588263943660849836627⟩, ⟨-2997449234918162857813386, -2997449234918152955885680⟩⟩, ⟨⟨-6730176479838953464653453, -6730176479838941199851057⟩, ⟨436337441230747964850068, 436337441230760229787474⟩⟩, ⟨⟨4704542319027360984429816, 4704542319027370873122376⟩, ⟨7300165828995722314160395, 7300165828995732202763806⟩⟩, ⟨⟨3295604226169433769204486, 3295604226169438805647771⟩, ⟨-6170774474641484544219498, -6170774474641479507806871⟩⟩, ⟨⟨-3431036263024596418757017, -3431036263024594863301644⟩, ⟨59471312613065955727243, 59471312613067511187987⟩⟩, ⟨⟨490385748857828072630497, 490385748857828346349755⟩, ⟨846257518198775946048765, 846257518198776219768921⟩⟩, ⟨⟨76672640122959461342312, 76672640122959486310521⟩, ⟨-128550626357180710006792, -128550626357180685038580⟩⟩, ⟨⟨-10694225312440586580523, -10694225312440585570668⟩, ⟨-321898175261148344380, -321898175261147334527⟩⟩, ⟨⟨123616755786192403035, 123616755786192416682⟩, ⟨238918417346845765692, 238918417346845779339⟩⟩, ⟨⟨552009424883113291, 552009424883113345⟩, ⟨-831733159172575685, -831733159172575632⟩⟩],
  [z, z, z, z, z, z, z, z, z, ⟨⟨17777530542382716, 17777530542382753⟩, ⟨-17, 18⟩⟩, ⟨⟨-2662678475321777, -2662678475321193⟩, ⟨-291, 291⟩⟩, ⟨⟨8703883919954435, 8703883919956434⟩, ⟨-998, 998⟩⟩, ⟨⟨-1017108864542757291, -1017108864542755021⟩, ⟨-1133, 1136⟩⟩, ⟨⟨33349496329366467, 33349496329367323⟩, ⟨-430, 428⟩⟩, ⟨⟨-39090489178583585, -39090489178583505⟩, ⟨-40, 40⟩⟩, o, z, z],
  [z, z, z, z, z, z, z, z, z, z, ⟨⟨17430972771932722, 17430972771932755⟩, ⟨-16, 17⟩⟩, ⟨⟨-2623885194553940, -2623885194553364⟩, ⟨-286, 287⟩⟩, ⟨⟨8634373594937200, 8634373594939241⟩, ⟨-1022, 1021⟩⟩, ⟨⟨-1015775082535103747, -1015775082535101400⟩, ⟨-1172, 1171⟩⟩, ⟨⟨33300975915669463, 33300975915670328⟩, ⟨-434, 436⟩⟩, ⟨⟨-39029867716729619, -39029867716729538⟩, ⟨-40, 39⟩⟩, o, z],
  [z, z, z, z, z, z, z, z, z, z, z, ⟨⟨17091754440386515, 17091754440386552⟩, ⟨-19, 19⟩⟩, ⟨⟨-2585736695543294, -2585736695542682⟩, ⟨-307, 306⟩⟩, ⟨⟨8565600254506616, 8565600254508703⟩, ⟨-1042, 1044⟩⟩, ⟨⟨-1014449014278130556, -1014449014278128255⟩, ⟨-1149, 1150⟩⟩, ⟨⟨33252853655788837, 33252853655789690⟩, ⟨-429, 429⟩⟩, ⟨⟨-38969652730928797, -38969652730928716⟩, ⟨-39, 40⟩⟩, o]
]

end MidLitTables

set_option maxRecDepth 65536 in
set_option maxHeartbeats 2000000 in
private lemma w9_eq_lit : wRowsOf (pts36OfSn 9) rho9List = w9Lit := by decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 2000000 in
private lemma w10_eq_lit : wRowsOf (pts36OfSn 10) rho10List = w10Lit := by decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 2000000 in
private lemma fac9_eq_lit : activeRowFactors36 w9Lit = fac9Lit := by
  unfold activeRowFactors36
  refine map_eq_of_chunks3_12 (fun i => if isActiveSrc36 i then rowFactorsCIv S36 w9Lit i else [])
    (List.finRange 36) fac9Lit ?_ ?_ ?_
  · decide
  · decide
  · decide

private lemma fac9Lit_len : fac9Lit.length = 36 := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
private lemma st9_1_eq :
    stepRowsTake 0 4 fac9Lit (List.replicate 36 [CFpIv.ofInt S36 1]) = st9_1 := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
private lemma st9_2_eq : stepRowsTake 4 4 fac9Lit st9_1 = st9_2 := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
private lemma st9_3_eq : stepRowsTake 8 4 fac9Lit st9_2 = st9_3 := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
private lemma st9_4_eq : stepRowsTake 12 4 fac9Lit st9_3 = st9_4 := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
private lemma st9_5_eq : stepRowsTake 16 4 fac9Lit st9_4 = st9_5 := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
private lemma st9_6_eq : stepRowsTake 20 4 fac9Lit st9_5 = st9_6 := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
private lemma st9_7_eq : stepRowsTake 24 4 fac9Lit st9_6 = st9_7 := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
private lemma st9_8_eq : stepRowsTake 28 4 fac9Lit st9_7 = st9_8 := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
private lemma st9_9_eq : stepRowsTail 32 fac9Lit st9_8 = st9_9 := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
private lemma m18E9_from_st9 : mkEvenFromRows36 st9_9 = m18ELit9 := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
private lemma m18O9_from_st9 : mkOddFromRows36 st9_9 = m18OLit9 := by decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 2000000 in
private lemma fac10_eq_lit : activeRowFactors36 w10Lit = fac10Lit := by
  unfold activeRowFactors36
  refine map_eq_of_chunks3_12 (fun i => if isActiveSrc36 i then rowFactorsCIv S36 w10Lit i else [])
    (List.finRange 36) fac10Lit ?_ ?_ ?_
  · decide
  · decide
  · decide

private lemma fac10Lit_len : fac10Lit.length = 36 := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
private lemma st10_1_eq :
    stepRowsTake 0 4 fac10Lit (List.replicate 36 [CFpIv.ofInt S36 1]) = st10_1 := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
private lemma st10_2_eq : stepRowsTake 4 4 fac10Lit st10_1 = st10_2 := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
private lemma st10_3_eq : stepRowsTake 8 4 fac10Lit st10_2 = st10_3 := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
private lemma st10_4_eq : stepRowsTake 12 4 fac10Lit st10_3 = st10_4 := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
private lemma st10_5_eq : stepRowsTake 16 4 fac10Lit st10_4 = st10_5 := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
private lemma st10_6_eq : stepRowsTake 20 4 fac10Lit st10_5 = st10_6 := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
private lemma st10_7_eq : stepRowsTake 24 4 fac10Lit st10_6 = st10_7 := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
private lemma st10_8_eq : stepRowsTake 28 4 fac10Lit st10_7 = st10_8 := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
private lemma st10_9_eq : stepRowsTail 32 fac10Lit st10_8 = st10_9 := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
private lemma m18E10_from_st9 : mkEvenFromRows36 st10_9 = m18ELit10 := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
private lemma m18O10_from_st9 : mkOddFromRows36 st10_9 = m18OLit10 := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
private lemma red6E9_eq_lit : reduce18To6ListCIv S36 m18ELit9 = mat6ELit9 := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
private lemma red6O9_eq_lit : reduce18To6ListCIv S36 m18OLit9 = mat6OLit9 := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
private lemma red6E10_eq_lit : reduce18To6ListCIv S36 m18ELit10 = mat6ELit10 := by decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
private lemma red6O10_eq_lit : reduce18To6ListCIv S36 m18OLit10 = mat6OLit10 := by decide

private lemma mat6E9_eq_lit :
    reduce18To6ListCIv S36 (mkMat18EvenIv rows9Cached) = mat6ELit9 := by
  dsimp only [rows9Cached, w9Cached]
  rw [mkMat18EvenIv_polyRowsOf, w9_eq_lit, mkMat18EvenFast_eq_active, fac9_eq_lit,
    map_evalFactorsCIv_eq_stages9, fac9Lit_len,
    st9_1_eq, st9_2_eq, st9_3_eq, st9_4_eq, st9_5_eq, st9_6_eq, st9_7_eq, st9_8_eq, st9_9_eq,
    m18E9_from_st9, red6E9_eq_lit]

private lemma mat6O9_eq_lit :
    reduce18To6ListCIv S36 (mkMat18OddIv rows9Cached) = mat6OLit9 := by
  dsimp only [rows9Cached, w9Cached]
  rw [mkMat18OddIv_polyRowsOf, w9_eq_lit, mkMat18OddFast_eq_active, fac9_eq_lit,
    map_evalFactorsCIv_eq_stages9, fac9Lit_len,
    st9_1_eq, st9_2_eq, st9_3_eq, st9_4_eq, st9_5_eq, st9_6_eq, st9_7_eq, st9_8_eq, st9_9_eq,
    m18O9_from_st9, red6O9_eq_lit]

private lemma mat6E10_eq_lit :
    reduce18To6ListCIv S36 (mkMat18EvenIv rows10Cached) = mat6ELit10 := by
  dsimp only [rows10Cached, w10Cached]
  rw [mkMat18EvenIv_polyRowsOf, w10_eq_lit, mkMat18EvenFast_eq_active, fac10_eq_lit,
    map_evalFactorsCIv_eq_stages9, fac10Lit_len,
    st10_1_eq, st10_2_eq, st10_3_eq, st10_4_eq, st10_5_eq, st10_6_eq, st10_7_eq, st10_8_eq, st10_9_eq,
    m18E10_from_st9, red6E10_eq_lit]

private lemma mat6O10_eq_lit :
    reduce18To6ListCIv S36 (mkMat18OddIv rows10Cached) = mat6OLit10 := by
  dsimp only [rows10Cached, w10Cached]
  rw [mkMat18OddIv_polyRowsOf, w10_eq_lit, mkMat18OddFast_eq_active, fac10_eq_lit,
    map_evalFactorsCIv_eq_stages9, fac10Lit_len,
    st10_1_eq, st10_2_eq, st10_3_eq, st10_4_eq, st10_5_eq, st10_6_eq, st10_7_eq, st10_8_eq, st10_9_eq,
    m18O10_from_st9, red6O10_eq_lit]

def readMat6Lit (mat : List (List CFpIv)) (q c : Fin 6) : CFpIv :=
  (mat.getD q.1 []).getD c.1 CFpIv.zero

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private lemma prod9_eq_cert :
    CFpIv.mul S36 (detRecFinCIv S36 (readMat6Lit mat6ELit9))
      (detRecFinCIv S36 (readMat6Lit mat6OLit9)) = prod9Cert := by
  decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private lemma prod10_eq_cert :
    CFpIv.mul S36 (detRecFinCIv S36 (readMat6Lit mat6ELit10))
      (detRecFinCIv S36 (readMat6Lit mat6OLit10)) = prod10Cert := by
  decide

private lemma prod9_re_pos : 0 < prod9Cert.re.lo := by decide
private lemma prod10_re_neg : prod10Cert.re.hi < 0 := by decide

private lemma pos_re_of_CFpMem {S : ℤ} (hS : 0 < S) {iv : CFpIv} {z : ℂ}
    (hmem : CFpIv.CFpMem S iv z) (hlo : 0 < iv.re.lo) : 0 < z.re := by
  have hS_pos : (0 : ℝ) < (S : ℝ) := by exact_mod_cast hS
  have hlo_R : (0 : ℝ) < (iv.re.lo : ℝ) := by exact_mod_cast hlo
  have hprod : 0 < (S : ℝ) * z.re := lt_of_lt_of_le hlo_R hmem.1.1
  exact (mul_pos_iff.mp hprod).resolve_right (fun h => by linarith [h.1]) |>.2

private lemma neg_re_of_CFpMem {S : ℤ} (hS : 0 < S) {iv : CFpIv} {z : ℂ}
    (hmem : CFpIv.CFpMem S iv z) (hhi : iv.re.hi < 0) : z.re < 0 := by
  have hS_pos : (0 : ℝ) < (S : ℝ) := by exact_mod_cast hS
  have hhi_R : (iv.re.hi : ℝ) < 0 := by exact_mod_cast hhi
  have hprod : (S : ℝ) * z.re < 0 := lt_of_le_of_lt hmem.1.2 hhi_R
  exact (mul_neg_iff.mp hprod).resolve_right (fun h => by linarith [h.1]) |>.2

private lemma cast_int_9 : ((9 : ℤ) : ℝ) = (9 : ℝ) := by norm_num
private lemma cast_int_10 : ((10 : ℤ) : ℝ) = (10 : ℝ) := by norm_num

section
attribute [local irreducible] Matrix.det stereoDenR

lemma atiyahDet_x36Clamp_9_re_pos : 0 < (atiyahDet (x36Clamp 9)).re := by
  have hsn : (1 : ℤ) ≤ 9 := by decide
  have hmE := reduce18To6ListCIv_mem S36_pos (polyRowsOf_evenMat18_mem hsn rho9_ok)
  have hmO := reduce18To6ListCIv_mem S36_pos (polyRowsOf_oddMat18_mem hsn rho9_ok)
  have hmE' : ∀ q c : Fin 6,
      CFpIv.CFpMem S36 (readMat6Lit mat6ELit9 q c) (reduce18To6C (evenMat18 (x36Clamp 9).1) q c) := by
    intro q c
    have heq : readMat6Lit mat6ELit9 q c =
        (((reduce18To6ListCIv S36 (mkMat18EvenIv (polyRowsOf (wRowsOf (pts36OfSn 9) rho9List)))).getD q.1 []).getD c.1 CFpIv.zero) := by
      change readMat6Lit mat6ELit9 q c = readMat6Lit (reduce18To6ListCIv S36 (mkMat18EvenIv rows9Cached)) q c
      rw [mat6E9_eq_lit]
    have hm_q := hmE q c
    rw [cast_int_9, ← heq] at hm_q
    exact hm_q
  have hmO' : ∀ q c : Fin 6,
      CFpIv.CFpMem S36 (readMat6Lit mat6OLit9 q c) (reduce18To6C (oddMat18 (x36Clamp 9).1) q c) := by
    intro q c
    have heq : readMat6Lit mat6OLit9 q c =
        (((reduce18To6ListCIv S36 (mkMat18OddIv (polyRowsOf (wRowsOf (pts36OfSn 9) rho9List)))).getD q.1 []).getD c.1 CFpIv.zero) := by
      change readMat6Lit mat6OLit9 q c = readMat6Lit (reduce18To6ListCIv S36 (mkMat18OddIv rows9Cached)) q c
      rw [mat6O9_eq_lit]
    have hm_q := hmO q c
    rw [cast_int_9, ← heq] at hm_q
    exact hm_q
  have hdE := detRecFinCIv_mem S36_pos hmE'
  have hdO := detRecFinCIv_mem S36_pos hmO'
  have hprod := CFpIv.mul_mem S36_pos hdE hdO
  rw [prod9_eq_cert] at hprod
  have hprod_re_pos : 0 < ((Matrix.of (reduce18To6C (evenMat18 (x36Clamp 9).1))).det *
      (Matrix.of (reduce18To6C (oddMat18 (x36Clamp 9).1))).det).re :=
    pos_re_of_CFpMem S36_pos hprod prod9_re_pos
  have hE18 := evenMat18_triangular 9
  have hO18 := oddMat18_triangular 9
  have heqE : (evenMat18 (x36Clamp 9).1).det =
      (Matrix.of (reduce18To6C (evenMat18 (x36Clamp 9).1))).det :=
    det_18_eq_det_6 _ hE18.1 hE18.2.1 hE18.2.2.1 hE18.2.2.2.1 hE18.2.2.2.2
  have heqO : (oddMat18 (x36Clamp 9).1).det =
      (Matrix.of (reduce18To6C (oddMat18 (x36Clamp 9).1))).det :=
    det_18_eq_det_6 _ hO18.1 hO18.2.1 hO18.2.2.1 hO18.2.2.2.1 hO18.2.2.2.2
  rw [atiyahDet_eq_stereoMat_div (x36Clamp 9) (x36Clamp_z_monotone 9),
    det_stereoMat_eq_even_odd 9, heqE, heqO, mul_assoc]
  have hmat_re : (((64 : ℂ) * ((Matrix.of (reduce18To6C (evenMat18 (x36Clamp 9).1))).det *
      (Matrix.of (reduce18To6C (oddMat18 (x36Clamp 9).1))).det)) /
      (stereoDenR (x36Clamp 9).1 : ℂ)).re =
      64 * ((Matrix.of (reduce18To6C (evenMat18 (x36Clamp 9).1))).det *
        (Matrix.of (reduce18To6C (oddMat18 (x36Clamp 9).1))).det).re /
        stereoDenR (x36Clamp 9).1 := by
    have hr_ne : stereoDenR (x36Clamp 9).1 ≠ 0 := (stereoDenR_pos (x36Clamp 9).1).ne'
    simp [div_eq_mul_inv, ← Complex.ofReal_inv, mul_re]
  rw [hmat_re]
  exact div_pos (mul_pos (by norm_num) hprod_re_pos) (stereoDenR_pos (x36Clamp 9).1)

lemma atiyahDet_x36Clamp_10_re_neg : (atiyahDet (x36Clamp 10)).re < 0 := by
  have hsn : (1 : ℤ) ≤ 10 := by decide
  have hmE := reduce18To6ListCIv_mem S36_pos (polyRowsOf_evenMat18_mem hsn rho10_ok)
  have hmO := reduce18To6ListCIv_mem S36_pos (polyRowsOf_oddMat18_mem hsn rho10_ok)
  have hmE' : ∀ q c : Fin 6,
      CFpIv.CFpMem S36 (readMat6Lit mat6ELit10 q c) (reduce18To6C (evenMat18 (x36Clamp 10).1) q c) := by
    intro q c
    have heq : readMat6Lit mat6ELit10 q c =
        (((reduce18To6ListCIv S36 (mkMat18EvenIv (polyRowsOf (wRowsOf (pts36OfSn 10) rho10List)))).getD q.1 []).getD c.1 CFpIv.zero) := by
      change readMat6Lit mat6ELit10 q c = readMat6Lit (reduce18To6ListCIv S36 (mkMat18EvenIv rows10Cached)) q c
      rw [mat6E10_eq_lit]
    have hm_q := hmE q c
    rw [cast_int_10, ← heq] at hm_q
    exact hm_q
  have hmO' : ∀ q c : Fin 6,
      CFpIv.CFpMem S36 (readMat6Lit mat6OLit10 q c) (reduce18To6C (oddMat18 (x36Clamp 10).1) q c) := by
    intro q c
    have heq : readMat6Lit mat6OLit10 q c =
        (((reduce18To6ListCIv S36 (mkMat18OddIv (polyRowsOf (wRowsOf (pts36OfSn 10) rho10List)))).getD q.1 []).getD c.1 CFpIv.zero) := by
      change readMat6Lit mat6OLit10 q c = readMat6Lit (reduce18To6ListCIv S36 (mkMat18OddIv rows10Cached)) q c
      rw [mat6O10_eq_lit]
    have hm_q := hmO q c
    rw [cast_int_10, ← heq] at hm_q
    exact hm_q
  have hdE := detRecFinCIv_mem S36_pos hmE'
  have hdO := detRecFinCIv_mem S36_pos hmO'
  have hprod := CFpIv.mul_mem S36_pos hdE hdO
  rw [prod10_eq_cert] at hprod
  have hprod_re_neg : ((Matrix.of (reduce18To6C (evenMat18 (x36Clamp 10).1))).det *
      (Matrix.of (reduce18To6C (oddMat18 (x36Clamp 10).1))).det).re < 0 :=
    neg_re_of_CFpMem S36_pos hprod prod10_re_neg
  have hE18 := evenMat18_triangular 10
  have hO18 := oddMat18_triangular 10
  have heqE : (evenMat18 (x36Clamp 10).1).det =
      (Matrix.of (reduce18To6C (evenMat18 (x36Clamp 10).1))).det :=
    det_18_eq_det_6 _ hE18.1 hE18.2.1 hE18.2.2.1 hE18.2.2.2.1 hE18.2.2.2.2
  have heqO : (oddMat18 (x36Clamp 10).1).det =
      (Matrix.of (reduce18To6C (oddMat18 (x36Clamp 10).1))).det :=
    det_18_eq_det_6 _ hO18.1 hO18.2.1 hO18.2.2.1 hO18.2.2.2.1 hO18.2.2.2.2
  rw [atiyahDet_eq_stereoMat_div (x36Clamp 10) (x36Clamp_z_monotone 10),
    det_stereoMat_eq_even_odd 10, heqE, heqO, mul_assoc]
  have hmat_re : (((64 : ℂ) * ((Matrix.of (reduce18To6C (evenMat18 (x36Clamp 10).1))).det *
      (Matrix.of (reduce18To6C (oddMat18 (x36Clamp 10).1))).det)) /
      (stereoDenR (x36Clamp 10).1 : ℂ)).re =
      64 * ((Matrix.of (reduce18To6C (evenMat18 (x36Clamp 10).1))).det *
        (Matrix.of (reduce18To6C (oddMat18 (x36Clamp 10).1))).det).re /
        stereoDenR (x36Clamp 10).1 := by
    have hr_ne : stereoDenR (x36Clamp 10).1 ≠ 0 := (stereoDenR_pos (x36Clamp 10).1).ne'
    simp [div_eq_mul_inv, ← Complex.ofReal_inv, mul_re]
  rw [hmat_re]
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num) hprod_re_neg)
    (stereoDenR_pos (x36Clamp 10).1)

end

section
attribute [local irreducible] atiyahDet

/-- Explicit genuinely non-coplanar `36`-point 3D witness (`t = 10`) with strictly negative real
Atiyah–Sutcliffe determinant and vanishing imaginary part. -/
theorem exists_noncoplanar_3d_36_atiyahDet_neg :
    ∃ x : DistinctPoints 36, Noncoplanar3D x.1 ∧ (atiyahDet x).re < 0 ∧ (atiyahDet x).im = 0 :=
  ⟨x36Clamp 10, x36Clamp_noncoplanar 10, atiyahDet_x36Clamp_10_re_neg,
    atiyahDet_x36Clamp_im_zero 10⟩

/-- Explicit genuinely non-coplanar `36`-point 3D witness where Atiyah's determinant vanishes
(`D_36(x₀) = 0`), obtained by the Intermediate Value Theorem along `t ↦ x36Clamp t` on `[9, 10]`. -/
theorem exists_noncoplanar_3d_36_atiyahDet_zero :
    ∃ x : DistinctPoints 36, Noncoplanar3D x.1 ∧ atiyahDet x = 0 := by
  let f : ℝ → ℝ := fun t => (atiyahDet (x36Clamp t)).re
  have hcont : ContinuousOn f (Set.Icc (9 : ℝ) 10) :=
    continuous_atiyahDet_x36Clamp_re.continuousOn
  have hf9 : 0 < f 9 := atiyahDet_x36Clamp_9_re_pos
  have hf10 : f 10 < 0 := atiyahDet_x36Clamp_10_re_neg
  have hmem : (0 : ℝ) ∈ Set.Icc (f 10) (f 9) := ⟨hf10.le, hf9.le⟩
  obtain ⟨t₀, _, ht₀⟩ := intermediate_value_Icc' (by norm_num : (9 : ℝ) ≤ 10) hcont hmem
  refine ⟨x36Clamp t₀, x36Clamp_noncoplanar t₀, ?_⟩
  exact Complex.ext ht₀ (atiyahDet_x36Clamp_im_zero t₀)

/-- **Non-coplanar 3D Disproof of Atiyah–Sutcliffe Conjecture 1 (Determinant Form)** at `n = 36`. -/
theorem disproof_atiyah_det_nonzero_3d_36 : ¬ AtiyahDetNonzeroProp := by
  intro h
  obtain ⟨x, _, hx⟩ := exists_noncoplanar_3d_36_atiyahDet_zero
  exact h 36 (by norm_num) x hx

/-- **Non-coplanar 3D Disproof of Atiyah Conjecture 1 (Linear Independence Form)** at `n = 36`. -/
theorem disproof_atiyah_conjecture_1_3d_36 : ¬ AtiyahConjecture1Prop := by
  intro h
  obtain ⟨x, _, hx⟩ := exists_noncoplanar_3d_36_atiyahDet_zero
  exact not_linearIndependent_of_atiyahDet_eq_zero (by norm_num) x hx (h 36 (by norm_num) x)

/-- **Non-coplanar 3D Disproof of Atiyah–Sutcliffe Conjecture 2** at `n = 36`. -/
theorem disproof_atiyah_sutcliffe_conjecture_2_3d_36 : ¬ AtiyahSutcliffeConjecture2Prop := by
  intro h
  obtain ⟨x, _, hx⟩ := exists_noncoplanar_3d_36_atiyahDet_zero
  have hle := h 36 (by norm_num) x
  rw [hx, norm_zero] at hle
  linarith

end

end CertificationAndDisproofs

end Matematyka.AtiyahSutcliffe3D36




