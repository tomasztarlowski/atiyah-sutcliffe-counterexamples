module

public import Matematyka.AtiyahSutcliffe
public import Matematyka.AtiyahSutcliffeExtensions
public import Matematyka.AtiyahSutcliffe3D26
public import Matematyka.AtiyahSutcliffePlanar35
public import Matematyka.AtiyahSutcliffeSymplectic

/-!
# Part III: Universal $\mathrm{SU}(2) \times S_m$ Holomorphic Spinor Rigidity,
# Weighted Multi-Body No-Go Theorems, and Hyperbolic $n = 3$ 5-Gap Positivity

This module formalizes:
1. Schur–Weyl / $\mathrm{SU}(2) \times S_m$ equivariant multilinear rigidity
   (`su2_symmetric_multilinear_eq_atiyahFactor`): every degree-$\le m$ polynomial-valued map on
   $(\mathbb{C}^2)^m$ that is coordinatewise complex-bilinear, $S_m$-symmetric, and
   $\mathrm{SU}(2)$-equivariant is a constant multiple of the canonical Atiyah factor product.
2. Unconditional No-Go theorems (`universal_holomorphic_spinor_nogo_*`) showing that arbitrary finite
   multi-body weighted sums of $\mathrm{SU}(2) \times S_{n-1}$-equivariant multilinear spinor
   polynomials must become linearly dependent on:
   - strictly non-coplanar 3D configurations at $n = 26$,
   - planar configurations at $n = 35$,
   - centrally symmetric strictly non-coplanar 3D $\mathrm{Sp}(18)$ configurations at $n = 36$.
3. Exact hyperbolic $n = 3$ 5-gap identity and positivity ($D_3^{\mathbb{H}} > 1$).
-/

@[expose] public section

namespace Matematyka.AtiyahSutcliffeNoGo

open scoped ComplexConjugate
open Matematyka.MalkounCounterexample
open Matematyka.AtiyahSutcliffe
open Matematyka.AtiyahSutcliffe3D36
open Matematyka.AtiyahSutcliffe3D26
open Matematyka.AtiyahSutcliffePlanar35
open Matematyka.AtiyahSutcliffeSymplectic

/-! ## Section 1: $\mathrm{SU}(2) \times S_m$ Rigidity of Equivariant Multilinear Spinor Maps -/

section SpinorRigidity

/-- Predicate characterizing special unitary $2 \times 2$ complex matrices $\mathrm{SU}(2)$. -/
def IsSU2 (U : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  U * U.conjTranspose = 1 ∧ U.det = 1

/-- Canonical degree-1 spinor linear factor $v_0 + v_1 T$ matching `atiyahPoly`. -/
noncomputable def atiyahLinearFactor (v : Fin 2 → ℂ) : Polynomial ℂ :=
  Polynomial.C (v 0) + Polynomial.C (v 1) * Polynomial.X

/-- Standard $\mathrm{GL}_2(\mathbb{C})$ action on bivariate homogeneous lifts of degree $\le m$. -/
noncomputable def spinPolyAction (m : ℕ) (U : Matrix (Fin 2) (Fin 2) ℂ) (P : Polynomial ℂ) :
    Polynomial ℂ :=
  ∑ k ∈ Finset.range (m + 1),
    Polynomial.C (P.coeff k) *
      (Polynomial.C (U 0 1) + Polynomial.C (U 1 1) * Polynomial.X) ^ k *
      (Polynomial.C (U 0 0) + Polynomial.C (U 1 0) * Polynomial.X) ^ (m - k)

private lemma spinPolyAction_add (m : ℕ) (U : Matrix (Fin 2) (Fin 2) ℂ) (P Q : Polynomial ℂ) :
    spinPolyAction m U (P + Q) = spinPolyAction m U P + spinPolyAction m U Q := by
  simp only [spinPolyAction, Polynomial.coeff_add, Polynomial.C_add, add_mul, Finset.sum_add_distrib]

private lemma spinPolyAction_C_mul (m : ℕ) (U : Matrix (Fin 2) (Fin 2) ℂ) (a : ℂ) (P : Polynomial ℂ) :
    spinPolyAction m U (Polynomial.C a * P) = Polynomial.C a * spinPolyAction m U P := by
  simp only [spinPolyAction, Polynomial.coeff_C_mul, Polynomial.C_mul, Finset.mul_sum, mul_assoc]

private lemma coeff_sum_eq {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℂ) (k : ℕ) :
    (∑ i ∈ s, f i).coeff k = ∑ i ∈ s, (f i).coeff k := by
  change Polynomial.lcoeff ℂ k (∑ i ∈ s, f i) = ∑ i ∈ s, Polynomial.lcoeff ℂ k (f i)
  exact map_sum (Polynomial.lcoeff ℂ k) f s

private lemma coeff_spinPolyAction_diag (m : ℕ) (α β : ℂ) (P : Polynomial ℂ)
    {s : ℕ} (hs : s ≤ m) :
    (spinPolyAction m ![![α, 0], ![0, β]] P).coeff s =
      β ^ s * α ^ (m - s) * P.coeff s := by
  unfold spinPolyAction
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val',
    Matrix.empty_val', Fin.isValue, map_zero, zero_mul, zero_add, add_zero]
  rw [coeff_sum_eq]
  have hterm : ∀ k ∈ Finset.range (m + 1),
      (Polynomial.C (P.coeff k) * (Polynomial.C β * Polynomial.X) ^ k *
        (Polynomial.C α) ^ (m - k)).coeff s =
        if s = k then β ^ s * α ^ (m - s) * P.coeff s else 0 := by
    intro k _
    rw [mul_pow, ← map_pow Polynomial.C β k, ← map_pow Polynomial.C α (m - k)]
    have hrew :
        Polynomial.C (P.coeff k) * (Polynomial.C (β ^ k) * Polynomial.X ^ k) * Polynomial.C (α ^ (m - k)) =
          Polynomial.C (P.coeff k * β ^ k * α ^ (m - k)) * Polynomial.X ^ k := by
      simp only [map_mul]; ring
    rw [hrew, Polynomial.coeff_C_mul_X_pow]
    split_ifs with hks
    · subst hks; ring
    · rfl
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq]
  simp only [Finset.mem_range.mpr (Nat.lt_succ_of_le hs), ↓reduceIte]

private lemma spinPolyAction_eq_zero_of_natDegree (m : ℕ) (U : Matrix (Fin 2) (Fin 2) ℂ)
    (c₀ c₁ : ℂ) (P : Polynomial ℂ) (hdeg : ∀ d > m, P.coeff d = 0) :
    spinPolyAction (m + 1) U ((Polynomial.C c₀ + Polynomial.C c₁ * Polynomial.X) * P) =
      (Polynomial.C (c₀ * U 0 0 + c₁ * U 0 1) +
        Polynomial.C (c₀ * U 1 0 + c₁ * U 1 1) * Polynomial.X) * spinPolyAction m U P := by
  set B : Polynomial ℂ := Polynomial.C (U 0 0) + Polynomial.C (U 1 0) * Polynomial.X
  set A : Polynomial ℂ := Polynomial.C (U 0 1) + Polynomial.C (U 1 1) * Polynomial.X
  have hlin : Polynomial.C (c₀ * U 0 0 + c₁ * U 0 1) + Polynomial.C (c₀ * U 1 0 + c₁ * U 1 1) * Polynomial.X =
      Polynomial.C c₀ * B + Polynomial.C c₁ * A := by
    simp only [B, A, Polynomial.C_add, Polynomial.C_mul]; ring
  rw [hlin]
  unfold spinPolyAction
  change (∑ k ∈ Finset.range (m + 2),
      Polynomial.C (((Polynomial.C c₀ + Polynomial.C c₁ * Polynomial.X) * P).coeff k) *
        A ^ k * B ^ (m + 1 - k)) =
    (Polynomial.C c₀ * B + Polynomial.C c₁ * A) *
      ∑ k ∈ Finset.range (m + 1), Polynomial.C (P.coeff k) * A ^ k * B ^ (m - k)
  have hcoeff : ∀ k : ℕ,
      ((Polynomial.C c₀ + Polynomial.C c₁ * Polynomial.X) * P).coeff k =
        c₀ * P.coeff k + (if k = 0 then 0 else c₁ * P.coeff (k - 1)) := by
    intro k
    rw [add_mul, Polynomial.coeff_add, Polynomial.coeff_C_mul]
    congr 1
    rw [mul_assoc, Polynomial.coeff_C_mul]
    cases k with
    | zero => simp
    | succ k' => simp [Polynomial.coeff_X_mul]
  have hsplit : (∑ k ∈ Finset.range (m + 2),
      Polynomial.C (((Polynomial.C c₀ + Polynomial.C c₁ * Polynomial.X) * P).coeff k) *
        A ^ k * B ^ (m + 1 - k)) =
      (∑ k ∈ Finset.range (m + 2),
        Polynomial.C (c₀ * P.coeff k) * A ^ k * B ^ (m + 1 - k)) +
      (∑ k ∈ Finset.range (m + 2),
        Polynomial.C (if k = 0 then 0 else c₁ * P.coeff (k - 1)) * A ^ k * B ^ (m + 1 - k)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hcoeff k, Polynomial.C_add]
    ring
  rw [hsplit]
  have hS0 : (∑ k ∈ Finset.range (m + 2),
      Polynomial.C (c₀ * P.coeff k) * A ^ k * B ^ (m + 1 - k)) =
      (Polynomial.C c₀ * B) * ∑ k ∈ Finset.range (m + 1), Polynomial.C (P.coeff k) * A ^ k * B ^ (m - k) := by
    rw [Finset.sum_range_succ, hdeg (m + 1) (by omega), mul_zero, map_zero,
      zero_mul, zero_mul, add_zero, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hpow : B ^ (m + 1 - k) = B * B ^ (m - k) := by
      rw [show m + 1 - k = (m - k) + 1 by omega, pow_succ']
    rw [hpow, Polynomial.C_mul]
    ring
  have hS1 : (∑ k ∈ Finset.range (m + 2),
      Polynomial.C (if k = 0 then 0 else c₁ * P.coeff (k - 1)) * A ^ k * B ^ (m + 1 - k)) =
      (Polynomial.C c₁ * A) * ∑ k ∈ Finset.range (m + 1), Polynomial.C (P.coeff k) * A ^ k * B ^ (m - k) := by
    rw [Finset.sum_range_succ']
    simp only [↓reduceIte, map_zero, zero_mul, add_zero, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hnz : k + 1 ≠ 0 := Nat.succ_ne_zero k
    have hsub : m + 1 - (k + 1) = m - k := by omega
    simp only [hnz, ↓reduceIte, Nat.add_sub_cancel, hsub, Polynomial.C_mul, pow_succ']
    ring
  rw [hS0, hS1, add_mul]

/-- Multilinear, $S_m$-symmetric, $\mathrm{SU}(2)$-equivariant polynomial maps on $(\mathbb{C}^2)^m$. -/
def IsSpinorEquivariantMultilinear (m : ℕ) (Φ : (Fin m → Fin 2 → ℂ) → Polynomial ℂ) : Prop :=
  (∀ v, ∀ d > m, (Φ v).coeff d = 0) ∧
  (∀ (k : Fin m) (v : Fin m → Fin 2 → ℂ) (a b : ℂ) (x y : Fin 2 → ℂ),
    Φ (Function.update v k (a • x + b • y)) =
      Polynomial.C a * Φ (Function.update v k x) +
        Polynomial.C b * Φ (Function.update v k y)) ∧
  (∀ (σ : Equiv.Perm (Fin m)) (v : Fin m → Fin 2 → ℂ), Φ (v ∘ σ) = Φ v) ∧
  (∀ (U : Matrix (Fin 2) (Fin 2) ℂ), IsSU2 U →
    ∀ v : Fin m → Fin 2 → ℂ, Φ (fun k => U.mulVec (v k)) = spinPolyAction m U (Φ v))

private lemma pow_three_add_four_I_ne_pow_five : ∀ d : ℕ, 1 ≤ d →
    ∃ a b : ℤ, (3 + 4 * Complex.I) ^ d = ((3 + 5 * a : ℤ) : ℂ) + ((4 + 5 * b : ℤ) : ℂ) * Complex.I
  | 0, hd => by omega
  | 1, _ => ⟨0, 0, by simp⟩
  | d + 2, _ => by
    obtain ⟨a, b, ih⟩ := pow_three_add_four_I_ne_pow_five (d + 1) (by omega)
    refine ⟨-2 + 3 * a - 4 * b, 4 + 4 * a + 3 * b, ?_⟩
    rw [pow_succ, ih]
    push_cast
    linear_combination ((4 + 5 * (b : ℂ)) * 4) * Complex.I_sq

private lemma pow_three_add_four_I_eq_five_absurd {d : ℕ} (hd : 1 ≤ d) :
    ((3 + 4 * Complex.I) / 5) ^ d ≠ 1 := by
  intro h
  obtain ⟨a, b, hab⟩ := pow_three_add_four_I_ne_pow_five d hd
  have h5 : (5 : ℂ) ^ d ≠ 0 := pow_ne_zero d (by norm_num)
  rw [div_pow, div_eq_one_iff_eq h5, hab] at h
  have him := congr_arg Complex.im h
  have h5im : ((5 : ℂ) ^ d).im = 0 := by
    have : (5 : ℂ) ^ d = (((5 : ℝ) ^ d : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.ofReal_im]
  rw [h5im] at him
  simp only [Complex.add_im, Complex.intCast_im, Complex.mul_im, Complex.intCast_re,
    Complex.I_re, mul_zero, Complex.I_im, mul_one, zero_add] at him
  have himR : ((4 + 5 * b : ℤ) : ℝ) = ((0 : ℤ) : ℝ) := by simpa only [Int.cast_zero, add_zero] using him
  have himZ : (4 + 5 * b : ℤ) = 0 := Int.cast_injective himR
  omega

private lemma zeta_su2 :
    let ζ : ℂ := (3 + 4 * Complex.I) / 5
    IsSU2 ![![ζ, 0], ![0, star ζ]] := by
  intro ζ
  have hmul : ζ * star ζ = 1 := by
    apply Complex.ext <;> simp [ζ, Complex.mul_re, Complex.mul_im] <;> norm_num
  have hmul' : star ζ * ζ = 1 := by rw [mul_comm]; exact hmul
  let U : Matrix (Fin 2) (Fin 2) ℂ := ![![ζ, 0], ![0, star ζ]]
  change U * U.conjTranspose = 1 ∧ U.det = 1
  constructor
  · ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.conjTranspose_apply]
    dsimp [U]
    fin_cases i <;> fin_cases j
    · simp; change ζ * star ζ = 1; exact hmul
    · simp
    · simp
    · simp; change star ζ * ζ = 1; exact hmul'
  · rw [Matrix.det_fin_two]
    dsimp [U]
    simp
    change ζ * star ζ = 1
    exact hmul

private lemma hadamard_su2 :
    let s : ℂ := ((1 / Real.sqrt 2 : ℝ) : ℂ)
    IsSU2 (s • ![![(1 : ℂ), -1], ![1, 1]]) := by
  intro s
  have hsqrt : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hs2 : s * s = (1 / 2 : ℂ) := by
    have hR : (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = (1 / 2 : ℝ) := by
      field_simp [hsqrt]
      rw [Real.sq_sqrt (by norm_num)]
    have hR' : ((1 / Real.sqrt 2 : ℝ) : ℂ) * ((1 / Real.sqrt 2 : ℝ) : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
      exact_mod_cast hR
    simpa [s] using hR'
  have hconj' : (starRingEnd ℂ) s = s := Complex.conj_ofReal _
  let U : Matrix (Fin 2) (Fin 2) ℂ := s • ![![(1 : ℂ), -1], ![1, 1]]
  change U * U.conjTranspose = 1 ∧ U.det = 1
  constructor
  · ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Matrix.conjTranspose_apply]
    dsimp [U]
    fin_cases i <;> fin_cases j
    · simp [hconj']; linear_combination 2 * hs2
    · simp [hconj']
    · simp [hconj']
    · simp [hconj']; linear_combination 2 * hs2
  · rw [Matrix.det_fin_two]
    dsimp [U]
    simp
    linear_combination 2 * hs2

private lemma zeta_pow_balance {ζ : ℂ} (hζ : ζ = (3 + 4 * Complex.I) / 5)
    {m r s : ℕ} (hr : r ≤ m) (hs : s ≤ m) (hrs : r ≠ s) :
    (star ζ) ^ r * ζ ^ (m - r) ≠ (star ζ) ^ s * ζ ^ (m - s) := by
  have hmul : ζ * star ζ = 1 := by
    have hconj : star ζ = (3 - 4 * Complex.I) / 5 := by
      rw [hζ]; simp [Complex.conj_I]; ring
    rw [hconj, hζ]
    calc ((3 + 4 * Complex.I) / 5) * ((3 - 4 * Complex.I) / 5)
      = (9 - 16 * Complex.I ^ 2) / 25 := by ring
      _ = 1 := by rw [Complex.I_sq]; norm_num
  have hstar_inv : star ζ = ζ⁻¹ := eq_inv_of_mul_eq_one_right hmul
  have hζ_ne : ζ ≠ 0 := left_ne_zero_of_mul_eq_one hmul
  intro heq
  rw [hstar_inv, inv_pow, inv_pow] at heq
  rcases lt_or_gt_of_ne hrs with hlt | hgt
  · have hm : ζ ^ (m - r) * ζ ^ s = ζ ^ (m - s) * ζ ^ r := by
      have h1 := congr_arg (· * (ζ ^ r * ζ ^ s)) heq
      field_simp [hζ_ne] at h1
      exact h1.trans (mul_comm _ _)
    rw [← pow_add, ← pow_add] at hm
    have heq' : ζ ^ (m - r + s) = ζ ^ (m - s + r) := hm
    have hdiff2 : m - r + s = (m - s + r) + 2 * (s - r) := by omega
    rw [hdiff2, pow_add] at heq'
    have hpow1 : ζ ^ (2 * (s - r)) = 1 := by
      exact mul_left_cancel₀ (pow_ne_zero (m - s + r) hζ_ne) (heq'.trans (mul_one _).symm)
    rw [hζ] at hpow1
    exact pow_three_add_four_I_eq_five_absurd (by omega) hpow1
  · have hm : ζ ^ (m - r) * ζ ^ s = ζ ^ (m - s) * ζ ^ r := by
      have h1 := congr_arg (· * (ζ ^ r * ζ ^ s)) heq
      field_simp [hζ_ne] at h1
      exact h1.trans (mul_comm _ _)
    rw [← pow_add, ← pow_add] at hm
    have hdiff2 : m - s + r = (m - r + s) + 2 * (r - s) := by omega
    have hm' : ζ ^ (m - r + s) * 1 = ζ ^ (m - r + s) * ζ ^ (2 * (r - s)) := by
      rw [mul_one]
      nth_rw 1 [hm, hdiff2, pow_add]
    have hpow1 : ζ ^ (2 * (r - s)) = 1 :=
      (mul_left_cancel₀ (pow_ne_zero (m - r + s) hζ_ne) hm').symm
    rw [hζ] at hpow1
    exact pow_three_add_four_I_eq_five_absurd (by omega) hpow1

private lemma multilinear_smul {m : ℕ} {Φ : (Fin m → Fin 2 → ℂ) → Polynomial ℂ}
    (hmult : ∀ (k : Fin m) (v : Fin m → Fin 2 → ℂ) (a b : ℂ) (x y : Fin 2 → ℂ),
      Φ (Function.update v k (a • x + b • y)) =
        Polynomial.C a * Φ (Function.update v k x) +
          Polynomial.C b * Φ (Function.update v k y))
    (k : Fin m) (v : Fin m → Fin 2 → ℂ) (a : ℂ) (x : Fin 2 → ℂ) :
    Φ (Function.update v k (a • x)) = Polynomial.C a * Φ (Function.update v k x) := by
  have h := hmult k v a 0 x x
  simpa using h

private lemma multilinear_expand_finset {m : ℕ} {Φ : (Fin m → Fin 2 → ℂ) → Polynomial ℂ}
    (hmult : ∀ (k : Fin m) (v : Fin m → Fin 2 → ℂ) (a b : ℂ) (x y : Fin 2 → ℂ),
      Φ (Function.update v k (a • x + b • y)) =
        Polynomial.C a * Φ (Function.update v k x) +
          Polynomial.C b * Φ (Function.update v k y))
    (v : Fin m → Fin 2 → ℂ) :
    Φ v = ∑ s : Finset (Fin m),
      Polynomial.C ((∏ i ∈ s, v i 1) * (∏ i ∈ sᶜ, v i 0)) *
        Φ (fun i => if i ∈ s then ![0, 1] else ![1, 0]) := by
  let e₀ : Fin 2 → ℂ := ![1, 0]
  let e₁ : Fin 2 → ℂ := ![0, 1]
  have hdecomp : ∀ (t : ℕ) (ht : t ≤ m) (u : Fin m → Fin 2 → ℂ),
      (∀ i : Fin m, t ≤ i.1 → u i = e₀ ∨ u i = e₁) →
      Φ u = ∑ s ∈ Finset.univ.filter (fun s : Finset (Fin m) => ∀ i ∈ s, i.1 < t),
        (∏ i ∈ Finset.univ.filter (fun i : Fin m => i.1 < t),
          if i ∈ s then Polynomial.C (u i 1) else Polynomial.C (u i 0)) *
          Φ (fun i => if i.1 < t then (if i ∈ s then e₁ else e₀) else u i) := by
    intro t
    induction t with
    | zero =>
      intro _ u _
      have huniq : Finset.univ.filter (fun s : Finset (Fin m) => ∀ i ∈ s, i.1 < 0) = {∅} := by
        ext s; simp [Finset.eq_empty_iff_forall_notMem]
      rw [huniq, Finset.sum_singleton]
      have hfil : Finset.univ.filter (fun i : Fin m => i.1 < 0) = ∅ := by
        ext i; simp
      rw [hfil, Finset.prod_empty, one_mul]
      simp
    | succ t ih =>
      intro ht u hu
      let k : Fin m := ⟨t, ht⟩
      have hu_vec : u k = u k 0 • e₀ + u k 1 • e₁ := by
        ext j; fin_cases j <;> simp [e₀, e₁]
      have hstep : Φ u =
          Polynomial.C (u k 0) * Φ (Function.update u k e₀) +
            Polynomial.C (u k 1) * Φ (Function.update u k e₁) := by
        have h1 := hmult k u (u k 0) (u k 1) e₀ e₁
        rwa [← hu_vec, Function.update_eq_self] at h1
      have h0 : ∀ i : Fin m, t ≤ i.1 → Function.update u k e₀ i = e₀ ∨ Function.update u k e₀ i = e₁ := by
        intro i hi
        by_cases hik : i = k
        · left; simp [hik]
        · rw [Function.update_of_ne hik]; exact hu i (by
            have hne1 : i.1 ≠ t := fun h => hik (Fin.ext h)
            omega)
      have h1 : ∀ i : Fin m, t ≤ i.1 → Function.update u k e₁ i = e₀ ∨ Function.update u k e₁ i = e₁ := by
        intro i hi
        by_cases hik : i = k
        · right; simp [hik]
        · rw [Function.update_of_ne hik]; exact hu i (by
            have hne1 : i.1 ≠ t := fun h => hik (Fin.ext h)
            omega)
      rw [hstep, ih (by omega) (Function.update u k e₀) h0, ih (by omega) (Function.update u k e₁) h1]
      -- Simplify each branch and partition subsets below t+1 by whether k ∈ s:
      let Ft := Finset.univ.filter (fun s : Finset (Fin m) => ∀ i ∈ s, i.1 < t)
      let Ft1 := Finset.univ.filter (fun s : Finset (Fin m) => ∀ i ∈ s, i.1 < t + 1)
      let It := Finset.univ.filter (fun i : Fin m => i.1 < t)
      let It1 := Finset.univ.filter (fun i : Fin m => i.1 < t + 1)
      have hIt1 : It1 = insert k It := by
        ext i; simp only [It1, It, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ,
          true_and, Fin.ext_iff, k]; omega
      have hk_not_It : k ∉ It := by simp [It, k]
      have hpart : Ft1 = Ft ∪ Ft.image (insert k) := by
        ext s
        simp only [Ft1, Ft, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
          true_and]
        constructor
        · intro hs
          by_cases hks : k ∈ s
          · right
            refine ⟨s.erase k, fun i hi => ?_, Finset.insert_erase hks⟩
            have hne := (Finset.mem_erase.mp hi).1
            have hlt := hs i (Finset.mem_erase.mp hi).2
            have hne1 : i.1 ≠ t := fun h => hne (Fin.ext h)
            omega
          · left
            intro i his
            have hne : i ≠ k := fun h => hks (h ▸ his)
            have hlt := hs i his
            have hne1 : i.1 ≠ t := fun h => hne (Fin.ext h)
            omega
        · rintro (hs | ⟨s', hs', rfl⟩)
          · exact fun i hi => lt_trans (hs i hi) (Nat.lt_succ_self t)
          · intro i hi
            rcases Finset.mem_insert.mp hi with rfl | hi'
            · exact Nat.lt_succ_self t
            · exact lt_trans (hs' i hi') (Nat.lt_succ_self t)
      have hdisj : Disjoint Ft (Ft.image (insert k)) := by
        rw [Finset.disjoint_left]
        intro s hs1 hs2
        rcases Finset.mem_image.mp hs2 with ⟨s', _, rfl⟩
        have hlt := (Finset.mem_filter.mp hs1).2 k (Finset.mem_insert_self k s')
        exact Nat.lt_irrefl t hlt
      set g : Finset (Fin m) → Polynomial ℂ := fun s =>
        (∏ i ∈ It1, if i ∈ s then Polynomial.C (u i 1) else Polynomial.C (u i 0)) *
          Φ (fun i => if i.1 < t + 1 then (if i ∈ s then e₁ else e₀) else u i)
      have hsum_part : (∑ s ∈ Ft1, g s) = (∑ s ∈ Ft, g s) + ∑ s ∈ Ft, g (insert k s) := by
        rw [hpart, Finset.sum_union hdisj, Finset.sum_image]
        intro s₁ hs₁ s₂ hs₂ heq
        have h1not : k ∉ s₁ := fun h => Nat.lt_irrefl t ((Finset.mem_filter.mp hs₁).2 k h)
        have h2not : k ∉ s₂ := fun h => Nat.lt_irrefl t ((Finset.mem_filter.mp hs₂).2 k h)
        have htmp := congr_arg (fun a => Finset.erase a k) heq
        simpa [Finset.erase_insert h1not, Finset.erase_insert h2not] using htmp
      have hB0 :
          Polynomial.C (u k 0) *
            (∑ s ∈ Ft, (∏ i ∈ It, if i ∈ s then Polynomial.C ((Function.update u k e₀) i 1)
              else Polynomial.C ((Function.update u k e₀) i 0)) *
              Φ (fun i => if i.1 < t then (if i ∈ s then e₁ else e₀) else Function.update u k e₀ i)) =
          ∑ s ∈ Ft, g s := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s hs => ?_
        have hks : k ∉ s := fun h => Nat.lt_irrefl t ((Finset.mem_filter.mp hs).2 k h)
        have hprod_upd :
            (∏ i ∈ It, if i ∈ s then Polynomial.C ((Function.update u k e₀) i 1)
              else Polynomial.C ((Function.update u k e₀) i 0)) =
            ∏ i ∈ It, if i ∈ s then Polynomial.C (u i 1) else Polynomial.C (u i 0) := by
          refine Finset.prod_congr rfl fun i hi => ?_
          have hne : i ≠ k := fun h => hk_not_It (h ▸ hi)
          simp [Function.update_of_ne hne]
        have hprod1 :
            (∏ i ∈ It1, if i ∈ s then Polynomial.C (u i 1) else Polynomial.C (u i 0)) =
            Polynomial.C (u k 0) * ∏ i ∈ It, if i ∈ s then Polynomial.C (u i 1) else Polynomial.C (u i 0) := by
          rw [hIt1, Finset.prod_insert hk_not_It]
          simp [hks]
        have hvec : (fun i => if i.1 < t then (if i ∈ s then e₁ else e₀) else Function.update u k e₀ i) =
            fun i => if i.1 < t + 1 then (if i ∈ s then e₁ else e₀) else u i := by
          ext i
          by_cases hlt : i.1 < t
          · simp [hlt, lt_trans hlt (Nat.lt_succ_self t)]
          · by_cases hik : i = k
            · subst hik; simp [k, hks]
            · have hnlt : ¬ i.1 < t + 1 := by
                have hne : i.1 ≠ t := fun h => hik (Fin.ext h)
                omega
              simp [hlt, hnlt, Function.update_of_ne hik]
        dsimp only [g]
        rw [hprod_upd, hprod1, hvec, mul_assoc]
      have hB1 :
          Polynomial.C (u k 1) *
            (∑ s ∈ Ft, (∏ i ∈ It, if i ∈ s then Polynomial.C ((Function.update u k e₁) i 1)
              else Polynomial.C ((Function.update u k e₁) i 0)) *
              Φ (fun i => if i.1 < t then (if i ∈ s then e₁ else e₀) else Function.update u k e₁ i)) =
          ∑ s ∈ Ft, g (insert k s) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s hs => ?_
        have hks : k ∉ s := fun h => Nat.lt_irrefl t ((Finset.mem_filter.mp hs).2 k h)
        have hprod_upd :
            (∏ i ∈ It, if i ∈ s then Polynomial.C ((Function.update u k e₁) i 1)
              else Polynomial.C ((Function.update u k e₁) i 0)) =
            ∏ i ∈ It, if i ∈ s then Polynomial.C (u i 1) else Polynomial.C (u i 0) := by
          refine Finset.prod_congr rfl fun i hi => ?_
          have hne : i ≠ k := fun h => hk_not_It (h ▸ hi)
          simp [Function.update_of_ne hne]
        have hprod1 :
            (∏ i ∈ It1, if i ∈ insert k s then Polynomial.C (u i 1) else Polynomial.C (u i 0)) =
            Polynomial.C (u k 1) * ∏ i ∈ It, if i ∈ s then Polynomial.C (u i 1) else Polynomial.C (u i 0) := by
          rw [hIt1, Finset.prod_insert hk_not_It]
          simp only [Finset.mem_insert_self, ↓reduceIte]
          congr 1
          refine Finset.prod_congr rfl fun i hi => ?_
          have hne : i ≠ k := fun h => hk_not_It (h ▸ hi)
          simp [Finset.mem_insert, hne]
        have hvec : (fun i => if i.1 < t then (if i ∈ s then e₁ else e₀) else Function.update u k e₁ i) =
            fun i => if i.1 < t + 1 then (if i ∈ insert k s then e₁ else e₀) else u i := by
          ext i
          by_cases hlt : i.1 < t
          · have hne : i ≠ k := fun h => by subst h; exact Nat.lt_irrefl t hlt
            simp [hlt, lt_trans hlt (Nat.lt_succ_self t), Finset.mem_insert, hne]
          · by_cases hik : i = k
            · subst hik; simp [k]
            · have hnlt : ¬ i.1 < t + 1 := by
                have hne : i.1 ≠ t := fun h => hik (Fin.ext h)
                omega
              simp [hlt, hnlt, Function.update_of_ne hik]
        dsimp only [g]
        rw [hprod_upd, hprod1, hvec, mul_assoc]
      change _ = ∑ s ∈ Ft1, g s
      rw [hsum_part, hB0, hB1]
  have hfull := hdecomp m le_rfl v (fun i hi => absurd i.2 (not_lt.mpr hi))
  have hfuniv : Finset.univ.filter (fun s : Finset (Fin m) => ∀ i ∈ s, i.1 < m) = Finset.univ := by
    ext s; simp [Fin.is_lt]
  have hiuniv : Finset.univ.filter (fun i : Fin m => i.1 < m) = Finset.univ := by
    ext i; simp [Fin.is_lt]
  rw [hfuniv, hiuniv] at hfull
  rw [hfull]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hprod :
      (∏ i ∈ Finset.univ, if i ∈ s then Polynomial.C (v i 1) else Polynomial.C (v i 0)) =
        Polynomial.C ((∏ i ∈ s, v i 1) * (∏ i ∈ sᶜ, v i 0)) := by
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => i ∈ s)]
    have hs1 : (∏ i ∈ Finset.univ.filter (fun i => i ∈ s),
        if i ∈ s then Polynomial.C (v i 1) else Polynomial.C (v i 0)) =
        Polynomial.C (∏ i ∈ s, v i 1) := by
      have hf : Finset.univ.filter (fun i => i ∈ s) = s := by ext x; simp
      rw [hf, map_prod]
      refine Finset.prod_congr rfl fun i hi => by simp [hi]
    have hs2 : (∏ i ∈ Finset.univ.filter (fun i => ¬ i ∈ s),
        if i ∈ s then Polynomial.C (v i 1) else Polynomial.C (v i 0)) =
        Polynomial.C (∏ i ∈ sᶜ, v i 0) := by
      have hf : Finset.univ.filter (fun i => ¬ i ∈ s) = sᶜ := by ext x; simp
      rw [hf, map_prod]
      refine Finset.prod_congr rfl fun i hi => by simp [Finset.mem_compl.mp hi]
    rw [hs1, hs2, map_mul]
  rw [hprod]
  congr 1; ext i; simp [e₀, e₁]

private lemma perm_exists_subset_lt {m : ℕ} (s : Finset (Fin m)) :
    ∃ σ : Equiv.Perm (Fin m), ∀ i : Fin m, σ i ∈ s ↔ i.1 < s.card := by
  classical
  let sLt : Finset (Fin m) := Finset.univ.filter (fun i : Fin m => i.1 < s.card)
  have hcard_lt : sLt.card = s.card := by
    have hbij : sLt.card = (Finset.range s.card).card := by
      refine Finset.card_bij (fun i _ => i.1) ?_ ?_ ?_
      · intro i hi; exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
      · intro i₁ _ i₂ _ h; exact Fin.ext h
      · intro a ha
        have ham : a < m := lt_of_lt_of_le (Finset.mem_range.mp ha)
          (by simpa [Finset.card_fin] using Finset.card_le_univ s)
        exact ⟨⟨a, ham⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_range.mp ha⟩, rfl⟩
    rw [hbij, Finset.card_range]
  have e1 : (sLt : Finset (Fin m)) ≃ (s : Finset (Fin m)) :=
    (Fintype.equivFinOfCardEq (n := s.card) (by simp [hcard_lt])).trans
      (Fintype.equivFinOfCardEq (n := s.card) (by simp)).symm
  have e2 : (sLtᶜ : Finset (Fin m)) ≃ (sᶜ : Finset (Fin m)) :=
    (Fintype.equivFinOfCardEq (n := sᶜ.card) (by simp [Finset.card_compl, hcard_lt])).trans
      (Fintype.equivFinOfCardEq (n := sᶜ.card) (by simp [Finset.card_compl])).symm
  let f : Fin m → Fin m := fun i =>
    if h : i ∈ sLt then (e1 ⟨i, h⟩).1 else (e2 ⟨i, Finset.mem_compl.mpr h⟩).1
  have hf_bij : Function.Bijective f := by
    refine ⟨fun i₁ i₂ heq => ?_, fun j => ?_⟩
    · by_cases h1 : i₁ ∈ sLt <;> by_cases h2 : i₂ ∈ sLt
      · simp only [f, h1, h2, ↓reduceDIte] at heq
        exact congr_arg Subtype.val (e1.injective (Subtype.ext heq))
      · simp only [f, h1, h2, ↓reduceDIte] at heq
        have hj1 : f i₁ ∈ s := by simp only [f, h1, ↓reduceDIte]; exact (e1 ⟨i₁, h1⟩).2
        have hj2 : f i₂ ∈ sᶜ := by simp only [f, h2, ↓reduceDIte]; exact (e2 ⟨i₂, Finset.mem_compl.mpr h2⟩).2
        simp only [f, h1, h2, ↓reduceDIte] at hj1 hj2
        rw [heq] at hj1
        exact absurd hj1 (Finset.mem_compl.mp hj2)
      · simp only [f, h1, h2, ↓reduceDIte] at heq
        have hj1 : f i₁ ∈ sᶜ := by simp only [f, h1, ↓reduceDIte]; exact (e2 ⟨i₁, Finset.mem_compl.mpr h1⟩).2
        have hj2 : f i₂ ∈ s := by simp only [f, h2, ↓reduceDIte]; exact (e1 ⟨i₂, h2⟩).2
        simp only [f, h1, h2, ↓reduceDIte] at hj1 hj2
        rw [← heq] at hj2
        exact absurd hj2 (Finset.mem_compl.mp hj1)
      · simp only [f, h1, h2, ↓reduceDIte] at heq
        exact congr_arg Subtype.val (e2.injective (Subtype.ext heq))
    · by_cases hj : j ∈ s
      · obtain ⟨⟨i, hi⟩, h⟩ := e1.surjective ⟨j, hj⟩
        exact ⟨i, by simp [f, hi, h]⟩
      · obtain ⟨⟨i, hi⟩, h⟩ := e2.surjective ⟨j, Finset.mem_compl.mpr hj⟩
        have hni : i ∉ sLt := Finset.mem_compl.mp hi
        exact ⟨i, by simp [f, hni, h]⟩
  refine ⟨Equiv.ofBijective f hf_bij, fun i => ?_⟩
  change f i ∈ s ↔ i.1 < s.card
  by_cases hi : i ∈ sLt
  · have hlt : i.1 < s.card := (Finset.mem_filter.mp hi).2
    simp only [f, hi, ↓reduceDIte, hlt, iff_true]
    exact (e1 ⟨i, hi⟩).2
  · have hnlt : ¬ i.1 < s.card := fun h => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    simp only [f, hi, ↓reduceDIte, hnlt, iff_false]
    exact Finset.mem_compl.mp (e2 ⟨i, Finset.mem_compl.mpr hi⟩).2

/-- **Schur–Weyl / $\mathrm{SU}(2) \times S_m$ Rigidity:**
Every degree-$\le m$ polynomial map on $m$ spinors that is coordinatewise $\mathbb{C}$-linear,
$S_m$-symmetric, and $\mathrm{SU}(2)$-equivariant is a scalar multiple of the canonical
Atiyah factor product. -/
theorem su2_symmetric_multilinear_eq_atiyahFactor {m : ℕ}
    {Φ : (Fin m → Fin 2 → ℂ) → Polynomial ℂ} (hΦ : IsSpinorEquivariantMultilinear m Φ) :
    ∃ c : ℂ, ∀ v : Fin m → Fin 2 → ℂ, Φ v = Polynomial.C c * ∏ k : Fin m, atiyahLinearFactor (v k) := by
  rcases hΦ with ⟨hdeg, hmult, hperm, hsu2⟩
  let e₀ : Fin 2 → ℂ := ![1, 0]
  let e₁ : Fin 2 → ℂ := ![0, 1]
  let basisVec : ℕ → Fin m → Fin 2 → ℂ := fun r i => if i.1 < r then e₁ else e₀
  let Q : ℕ → Polynomial ℂ := fun r => Φ (basisVec r)
  have hQ_perm : ∀ s : Finset (Fin m),
      Φ (fun i => if i ∈ s then e₁ else e₀) = Q s.card := by
    intro s
    obtain ⟨σ, hσ⟩ := perm_exists_subset_lt s
    have h1 := hperm σ (fun i => if i ∈ s then e₁ else e₀)
    have h2 : (fun i => if σ i ∈ s then e₁ else e₀) = basisVec s.card := by
      ext i k
      simp only [basisVec]
      by_cases h : i.1 < s.card
      · have hs : σ i ∈ s := (hσ i).mpr h
        simp [h, hs]
      · have hns : σ i ∉ s := fun hs => h ((hσ i).mp hs)
        simp [h, hns]
    dsimp [Q]; rw [← h2]; exact h1.symm
  -- Step B: Diagonal U_ζ forces Q r = C (c r) * X ^ r for all r ≤ m
  let ζ : ℂ := (3 + 4 * Complex.I) / 5
  let Uζ : Matrix (Fin 2) (Fin 2) ℂ := ![![ζ, 0], ![0, star ζ]]
  have hUζ : IsSU2 Uζ := zeta_su2
  have hdiag_lhs : ∀ r : ℕ, r ≤ m →
      Φ (fun k => Uζ.mulVec (basisVec r k)) =
        Polynomial.C ((star ζ) ^ r * ζ ^ (m - r)) * Q r := by
    intro r hr
    have hmulVec : (fun k => Uζ.mulVec (basisVec r k)) =
        fun k => if k.1 < r then (star ζ) • e₁ else ζ • e₀ := by
      ext k j
      by_cases h : k.1 < r <;> fin_cases j <;>
        simp [Uζ, basisVec, e₀, e₁, Matrix.mulVec, dotProduct, Fin.sum_univ_two, h]
    rw [hmulVec, multilinear_expand_finset hmult]
    let Sr : Finset (Fin m) := Finset.univ.filter (fun i : Fin m => i.1 < r)
    have hSr_card : Sr.card = r := by
      have hbij : Sr.card = (Finset.range r).card := by
        refine Finset.card_bij (fun i _ => i.1) ?_ ?_ ?_
        · intro i hi; exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
        · intro _ _ _ _ h; exact Fin.ext h
        · intro a ha
          exact ⟨⟨a, lt_of_lt_of_le (Finset.mem_range.mp ha) hr⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_range.mp ha⟩, rfl⟩
      rw [hbij, Finset.card_range]
    have hSr_compl : Srᶜ.card = m - r := by rw [Finset.card_compl, Fintype.card_fin, hSr_card]
    have hterm : ∀ s : Finset (Fin m),
        (∏ i ∈ s, (if i.1 < r then (star ζ) • e₁ else ζ • e₀) 1) *
          (∏ i ∈ sᶜ, (if i.1 < r then (star ζ) • e₁ else ζ • e₀) 0) =
          if s = Sr then (star ζ) ^ r * ζ ^ (m - r) else 0 := by
      intro s
      split_ifs with hsr
      · subst hsr
        have hp1 : (∏ i ∈ Sr, (if i.1 < r then (star ζ) • e₁ else ζ • e₀) 1) = (star ζ) ^ r := by
          calc (∏ i ∈ Sr, (if i.1 < r then (star ζ) • e₁ else ζ • e₀) 1)
            = ∏ _i ∈ Sr, star ζ := Finset.prod_congr rfl fun i hi => by
                simp [(Finset.mem_filter.mp hi).2, e₁]
            _ = (star ζ) ^ Sr.card := Finset.prod_const _
            _ = (star ζ) ^ r := by rw [hSr_card]
        have hp2 : (∏ i ∈ Srᶜ, (if i.1 < r then (star ζ) • e₁ else ζ • e₀) 0) = ζ ^ (m - r) := by
          calc (∏ i ∈ Srᶜ, (if i.1 < r then (star ζ) • e₁ else ζ • e₀) 0)
            = ∏ _i ∈ Srᶜ, ζ := Finset.prod_congr rfl fun i hi => by
                have hn : ¬ i.1 < r := fun h => Finset.mem_compl.mp hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
                simp [hn, e₀]
            _ = ζ ^ Srᶜ.card := Finset.prod_const _
            _ = ζ ^ (m - r) := by rw [hSr_compl]
        rw [hp1, hp2]
      · by_cases hsub : ∃ i ∈ s, ¬ i.1 < r
        · obtain ⟨i, his, hni⟩ := hsub
          have hzero : (if i.1 < r then (star ζ) • e₁ else ζ • e₀) 1 = 0 := by simp [hni, e₀]
          rw [Finset.prod_eq_zero his hzero, zero_mul]
        · push Not at hsub
          have hs_sub : s ⊆ Sr := fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsub i hi⟩
          have hs_ssub : s ⊂ Sr := lt_of_le_of_ne hs_sub hsr
          obtain ⟨i, hiSr, hnis⟩ := Finset.exists_of_ssubset hs_ssub
          have hi_lt : i.1 < r := (Finset.mem_filter.mp hiSr).2
          have hzero : (if i.1 < r then (star ζ) • e₁ else ζ • e₀) 0 = 0 := by simp [hi_lt, e₁]
          rw [Finset.prod_eq_zero (Finset.mem_compl.mpr hnis) hzero, mul_zero]
    have hterm2 : ∀ x : Finset (Fin m),
        Polynomial.C (if x = Sr then (star ζ) ^ r * ζ ^ (m - r) else 0) *
          Φ (fun i => if i ∈ x then ![0, 1] else ![1, 0]) =
          if x = Sr then Polynomial.C ((star ζ) ^ r * ζ ^ (m - r)) * Q r else 0 := by
      intro x
      split_ifs with hx
      · subst hx; simp [hQ_perm Sr, hSr_card, e₁, e₀]
      · simp
    simp_rw [hterm, hterm2]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ↓reduceIte]
  have hQ_coeff_zero : ∀ r s : ℕ, r ≤ m → s ≠ r → (Q r).coeff s = 0 := by
    intro r s hr hrs
    by_cases hsm : s ≤ m
    · have heq := (hsu2 Uζ hUζ (basisVec r)).symm.trans (hdiag_lhs r hr)
      have hcs := congr_arg (fun P : Polynomial ℂ => P.coeff s) heq
      rw [coeff_spinPolyAction_diag m ζ (star ζ) (Q r) hsm, Polynomial.coeff_C_mul] at hcs
      have hne : (star ζ) ^ s * ζ ^ (m - s) ≠ (star ζ) ^ r * ζ ^ (m - r) :=
        zeta_pow_balance rfl hsm hr hrs
      have hmulz : ((star ζ) ^ s * ζ ^ (m - s) - (star ζ) ^ r * ζ ^ (m - r)) * (Q r).coeff s = 0 := by
        linear_combination hcs
      exact (mul_eq_zero.mp hmulz).resolve_left (sub_ne_zero.mpr hne)
    · exact hdeg (basisVec r) s (Nat.lt_of_not_le hsm)
  have hQ_eq : ∀ r : ℕ, r ≤ m → Q r = Polynomial.C ((Q r).coeff r) * Polynomial.X ^ r := by
    intro r hr
    ext k
    rw [Polynomial.coeff_C_mul_X_pow]
    split_ifs with hkr
    · subst hkr; rfl
    · exact hQ_coeff_zero r k hr hkr
  -- Step C: Hadamard U_H locks (Q r).coeff r = (Q 0).coeff 0 for all r ≤ m
  let c0 : ℂ := (Q 0).coeff 0
  let sH : ℂ := ((1 / Real.sqrt 2 : ℝ) : ℂ)
  let UH : Matrix (Fin 2) (Fin 2) ℂ := sH • ![![(1 : ℂ), -1], ![1, 1]]
  have hUH : IsSU2 UH := hadamard_su2
  have hUH_mul : ∀ i : Fin m, UH.mulVec (basisVec 0 i) = ![sH, sH] := by
    intro i; ext j; fin_cases j <;>
      simp [UH, basisVec, e₀, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hUH_lhs : Φ (fun i => UH.mulVec (basisVec 0 i)) =
      ∑ r ∈ Finset.range (m + 1),
        Polynomial.C ((Nat.choose m r : ℂ) * sH ^ m * (Q r).coeff r) * Polynomial.X ^ r := by
    have hv : (fun i => UH.mulVec (basisVec 0 i)) = fun _ => ![sH, sH] := funext hUH_mul
    rw [hv, multilinear_expand_finset hmult]
    have hprod_s : ∀ s : Finset (Fin m),
        (∏ _i ∈ s, (![sH, sH] : Fin 2 → ℂ) 1) * (∏ _i ∈ sᶜ, (![sH, sH] : Fin 2 → ℂ) 0) =
          sH ^ m := by
      intro s
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Finset.prod_const, ← pow_add,
        Finset.card_add_card_compl, Fintype.card_fin]
    have hterm : ∀ s : Finset (Fin m),
        Polynomial.C ((∏ _i ∈ s, (![sH, sH] : Fin 2 → ℂ) 1) * (∏ _i ∈ sᶜ, (![sH, sH] : Fin 2 → ℂ) 0)) *
          Φ (fun i => if i ∈ s then ![0, 1] else ![1, 0]) =
          Polynomial.C (sH ^ m * (Q s.card).coeff s.card) * Polynomial.X ^ s.card := by
      intro s
      have hsc : s.card ≤ m := by simpa [Finset.card_fin] using Finset.card_le_univ s
      rw [hprod_s s, hQ_perm s]
      nth_rw 1 [hQ_eq s.card hsc]
      rw [Polynomial.C_mul, mul_assoc]
    simp_rw [hterm]
    have hmap : ∀ s ∈ (Finset.univ : Finset (Finset (Fin m))), s.card ∈ Finset.range (m + 1) := by
      intro s _
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (by simpa [Fintype.card_fin] using Finset.card_le_univ s))
    have hfib_sum := Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset (Finset (Fin m)))) (t := Finset.range (m + 1))
      (g := fun s : Finset (Fin m) => s.card)
      (f := fun s : Finset (Fin m) => Polynomial.C (sH ^ m * (Q s.card).coeff s.card) * Polynomial.X ^ s.card)
      hmap
    change (∑ s ∈ (Finset.univ : Finset (Finset (Fin m))),
      Polynomial.C (sH ^ m * (Q s.card).coeff s.card) * Polynomial.X ^ s.card) = _
    rw [← hfib_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hfib : (Finset.univ.filter (fun s : Finset (Fin m) => s.card = r)).card = Nat.choose m r := by
      have heq : Finset.univ.filter (fun s : Finset (Fin m) => s.card = r) = Finset.powersetCard r Finset.univ := by
        ext s; simp
      rw [heq, Finset.card_powersetCard, Finset.card_fin]
    have hconst :
        (∑ i ∈ Finset.univ.filter (fun s : Finset (Fin m) => s.card = r),
          Polynomial.C (sH ^ m * (Q i.card).coeff i.card) * Polynomial.X ^ i.card) =
        ∑ _i ∈ Finset.univ.filter (fun s : Finset (Fin m) => s.card = r),
          Polynomial.C (sH ^ m * (Q r).coeff r) * Polynomial.X ^ r :=
      Finset.sum_congr rfl fun s hs => by rw [(Finset.mem_filter.mp hs).2]
    rw [hconst, Finset.sum_const, nsmul_eq_mul, hfib]
    simp only [Polynomial.C_mul, map_natCast]
    ring
  have hUH_rhs : spinPolyAction m UH (Q 0) =
      ∑ r ∈ Finset.range (m + 1), Polynomial.C ((Nat.choose m r : ℂ) * sH ^ m * c0) * Polynomial.X ^ r := by
    rw [hQ_eq 0 (Nat.zero_le m)]
    unfold spinPolyAction
    have hterm : ∀ k ∈ Finset.range (m + 1),
        Polynomial.C ((Polynomial.C c0 * Polynomial.X ^ 0).coeff k) *
          (Polynomial.C (UH 0 1) + Polynomial.C (UH 1 1) * Polynomial.X) ^ k *
          (Polynomial.C (UH 0 0) + Polynomial.C (UH 1 0) * Polynomial.X) ^ (m - k) =
          if k = 0 then Polynomial.C c0 * (Polynomial.C sH * (Polynomial.X + 1)) ^ m else 0 := by
      intro k _
      rw [pow_zero, mul_one, Polynomial.coeff_C]
      split_ifs with hk
      · subst hk
        simp [UH, mul_add, add_comm]
      · simp
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
    simp only [Finset.mem_range.mpr (Nat.zero_lt_succ m), ↓reduceIte, mul_pow, ← map_pow Polynomial.C sH m,
      add_pow, one_pow, mul_one, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [Polynomial.C_mul, map_natCast]
    ring
  have hc_eq : ∀ r : ℕ, r ≤ m → (Q r).coeff r = c0 := by
    intro r hr
    have heq := hUH_lhs.symm.trans ((hsu2 UH hUH (basisVec 0)).trans hUH_rhs)
    have hcr := congr_arg (fun P : Polynomial ℂ => P.coeff r) heq
    simp only [coeff_sum_eq, Polynomial.coeff_C_mul_X_pow] at hcr
    rw [Finset.sum_ite_eq, Finset.sum_ite_eq] at hcr
    simp only [Finset.mem_range.mpr (Nat.lt_succ_of_le hr), ↓reduceIte] at hcr
    have hsH_ne : sH ≠ 0 := Complex.ofReal_ne_zero.mpr (one_div_ne_zero (Real.sqrt_pos.mpr (by norm_num)).ne')
    have hch_ne : (Nat.choose m r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hr).ne'
    have hfac_ne : (Nat.choose m r : ℂ) * sH ^ m ≠ 0 := mul_ne_zero hch_ne (pow_ne_zero m hsH_ne)
    exact mul_left_cancel₀ hfac_ne (by linear_combination hcr)
  refine ⟨c0, fun v => ?_⟩
  rw [multilinear_expand_finset hmult v]
  have hprod_expand : ∏ k : Fin m, atiyahLinearFactor (v k) =
      ∑ s : Finset (Fin m),
        Polynomial.C ((∏ i ∈ s, v i 1) * (∏ i ∈ sᶜ, v i 0)) * Polynomial.X ^ s.card := by
    have hrew : ∏ k : Fin m, atiyahLinearFactor (v k) =
        ∏ k ∈ (Finset.univ : Finset (Fin m)), (Polynomial.C (v k 1) * Polynomial.X + Polynomial.C (v k 0)) := by
      refine Finset.prod_congr rfl fun k _ => ?_
      simp only [atiyahLinearFactor, add_comm]
    rw [hrew, Finset.prod_add]
    refine Finset.sum_congr rfl fun s _ => ?_
    have hps : (∏ i ∈ s, Polynomial.C (v i 1) * Polynomial.X) =
        Polynomial.C (∏ i ∈ s, v i 1) * Polynomial.X ^ s.card := by
      rw [Finset.prod_mul_distrib, map_prod, Finset.prod_const]
    have hpc : (∏ i ∈ Finset.univ \ s, Polynomial.C (v i 0)) =
        Polynomial.C (∏ i ∈ sᶜ, v i 0) := by
      have hdiff : Finset.univ \ s = sᶜ := by ext x; simp
      rw [hdiff]
      exact (map_prod Polynomial.C (fun i => v i 0) sᶜ).symm
    rw [hps, hpc, map_mul]
    ring
  rw [hprod_expand, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hsc : s.card ≤ m := by simpa [Finset.card_fin] using Finset.card_le_univ s
  rw [hQ_perm s, hQ_eq s.card hsc, hc_eq s.card hsc]
  ring

end SpinorRigidity

/-! ## Section 2: Unconditional Multi-Body Weighted No-Go Theorems -/

section WeightedNoGo

def omitIdx {n : ℕ} (i : Fin n) (r : Fin (n - 1)) : Fin n :=
  if r.1 < i.1 then ⟨r.1, by have := i.2; omega⟩
  else ⟨r.1 + 1, by have := r.2; have := i.2; omega⟩

lemma omitIdx_ne {n : ℕ} (i : Fin n) (r : Fin (n - 1)) : omitIdx i r ≠ i := by
  unfold omitIdx
  split_ifs with h <;> intro heq <;> have hv := congr_arg Fin.val heq <;> dsimp at hv <;> omega

/-- Arbitrary finite linear combination of $\mathrm{SU}(2) \times S_{n-1}$-equivariant multilinear
spinor polynomials weighted by completely arbitrary $n$-body scalar coefficients `W α x i`. -/
noncomputable def weightedSpinorCandidate {n : ℕ} {ι : Type*} [Fintype ι]
    (Φ : ι → (Fin (n - 1) → Fin 2 → ℂ) → Polynomial ℂ)
    (W : ι → DistinctPoints n → Fin n → ℂ)
    (x : DistinctPoints n) (i : Fin n) : Polynomial ℂ :=
  ∑ α : ι, Polynomial.C (W α x i) *
    Φ α (fun r : Fin (n - 1) => canonicalSpinor (unitDir (x.1 i) (x.1 (omitIdx i r))))

private lemma canonicalAtiyahPoly_eq_prod_linear {n : ℕ} (hn : 1 ≤ n)
    (x : DistinctPoints n) (i : Fin n) :
    atiyahPoly (fun u v => canonicalSpinor (unitDir (x.1 u) (x.1 v))) i =
      ∏ r : Fin (n - 1),
        atiyahLinearFactor (canonicalSpinor (unitDir (x.1 i) (x.1 (omitIdx i r)))) := by
  unfold atiyahPoly atiyahLinearFactor
  refine Finset.prod_bij
    (fun j _ => if h : j < i then ⟨j.1, by omega⟩ else ⟨j.1 - 1, by
      have hne := (Finset.mem_erase.mp ‹_›).1
      omega⟩) ?_ ?_ ?_ ?_
  · intro j _; exact Finset.mem_univ _
  · intro j₁ hj₁ j₂ hj₂ heq
    have h1 : j₁ ≠ i := (Finset.mem_erase.mp hj₁).1
    have h2 : j₂ ≠ i := (Finset.mem_erase.mp hj₂).1
    by_cases c1 : j₁ < i <;> by_cases c2 : j₂ < i <;> simp only [c1, c2, ↓reduceDIte, Fin.ext_iff] at heq <;>
      exact Fin.ext (by omega)
  · intro r _
    refine ⟨omitIdx i r, Finset.mem_erase.mpr ⟨omitIdx_ne i r, Finset.mem_univ _⟩, ?_⟩
    rcases lt_or_ge r.1 i.1 with hlt | hge
    · have hs : omitIdx i r = ⟨r.1, by have := i.2; omega⟩ := by simp [omitIdx, hlt]
      have hlt' : (⟨r.1, by have := i.2; omega⟩ : Fin n) < i := hlt
      simp [hs, hlt']
    · have hs : omitIdx i r = ⟨r.1 + 1, by have := r.2; have := i.2; omega⟩ := by
        simp [omitIdx, not_lt.mpr hge]
      have hnot : ¬ (⟨r.1 + 1, by have := r.2; have := i.2; omega⟩ : Fin n) < i := by
        simp [Fin.lt_def]; omega
      simp [hs, hnot]
  · intro j hj
    have hne : j ≠ i := (Finset.mem_erase.mp hj).1
    by_cases hlt : j < i
    · have hlt' : (⟨j.1, by omega⟩ : Fin (n - 1)).1 < i.1 := hlt
      have hs : omitIdx i ⟨j.1, by omega⟩ = j := Fin.ext (by simp [omitIdx, hlt'])
      simp [hlt, hs]
    · have hgt : i < j := lt_of_le_of_ne (not_lt.mp hlt) hne.symm
      have hnlt : ¬ (⟨j.1 - 1, by omega⟩ : Fin (n - 1)).1 < i.1 := by dsimp; omega
      have hs : omitIdx i ⟨j.1 - 1, by omega⟩ = j := Fin.ext (by simp [omitIdx, hnlt]; omega)
      simp [hlt, hs]

/-- Every weighted finite sum of $\mathrm{SU}(2) \times S_{n-1}$-equivariant multilinear spinor maps
collapses row-wise to a scalar multiple of the canonical Atiyah polynomial. -/
theorem weightedSpinorCandidate_eq_smul_atiyahPoly {n : ℕ} (hn : 1 ≤ n)
    {ι : Type*} [Fintype ι]
    (Φ : ι → (Fin (n - 1) → Fin 2 → ℂ) → Polynomial ℂ)
    (hΦ : ∀ α : ι, IsSpinorEquivariantMultilinear (n - 1) (Φ α))
    (W : ι → DistinctPoints n → Fin n → ℂ)
    (x : DistinctPoints n) :
    ∃ μ : Fin n → ℂ, ∀ i : Fin n,
      weightedSpinorCandidate Φ W x i =
        Polynomial.C (μ i) * atiyahPoly (fun u v => canonicalSpinor (unitDir (x.1 u) (x.1 v))) i := by
  choose c hc using fun α => su2_symmetric_multilinear_eq_atiyahFactor (hΦ α)
  refine ⟨fun i => ∑ α : ι, W α x i * c α, fun i => ?_⟩
  unfold weightedSpinorCandidate
  rw [canonicalAtiyahPoly_eq_prod_linear hn x i]
  calc
    (∑ α : ι, Polynomial.C (W α x i) *
        Φ α (fun r => canonicalSpinor (unitDir (x.1 i) (x.1 (omitIdx i r)))))
      = ∑ α : ι, Polynomial.C (W α x i * c α) *
          ∏ r : Fin (n - 1),
            atiyahLinearFactor (canonicalSpinor (unitDir (x.1 i) (x.1 (omitIdx i r)))) := by
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [hc α, map_mul]; ring
    _ = Polynomial.C (∑ α : ι, W α x i * c α) *
          ∏ r : Fin (n - 1),
            atiyahLinearFactor (canonicalSpinor (unitDir (x.1 i) (x.1 (omitIdx i r)))) := by
        rw [map_sum, Finset.sum_mul]

private lemma not_linearIndependent_scale_of_not_linearIndependent {n : ℕ}
    (P : Fin n → Polynomial ℂ) (hdep : ¬ LinearIndependent ℂ P) (μ : Fin n → ℂ) :
    ¬ LinearIndependent ℂ (fun i => Polynomial.C (μ i) * P i) := by
  intro hli
  by_cases hzero : ∃ i, μ i = 0
  · obtain ⟨i₀, hi0⟩ := hzero
    have h0 : (fun i => Polynomial.C (μ i) * P i) i₀ = 0 := by simp [hi0]
    exact hli.ne_zero i₀ h0
  · push Not at hzero
    apply hdep
    rw [Fintype.linearIndependent_iff] at hli ⊢
    intro g hg i
    have hhg : (∑ j : Fin n, (g j * (μ j)⁻¹) • (Polynomial.C (μ j) * P j)) = 0 := by
      have heq : (∑ j : Fin n, (g j * (μ j)⁻¹) • (Polynomial.C (μ j) * P j)) = ∑ j : Fin n, g j • P j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Polynomial.smul_eq_C_mul, Polynomial.smul_eq_C_mul]
        simp only [← mul_assoc, ← map_mul Polynomial.C]
        rw [mul_assoc (g j) (μ j)⁻¹ (μ j), inv_mul_cancel₀ (hzero j), mul_one]
      rw [heq]
      exact hg
    have hcoeff := hli (fun j => g j * (μ j)⁻¹) hhg i
    exact (mul_eq_zero.mp hcoeff).resolve_right (inv_ne_zero (hzero i))

/-- **Universal No-Go (`n = 26`, strictly non-coplanar 3D):** No finite multi-body weighted
$\mathrm{SU}(2) \times S_{25}$-equivariant holomorphic spinor polynomial ansatz can remain linearly
independent on all strictly non-coplanar 3D configurations. -/
theorem universal_holomorphic_spinor_nogo_noncoplanar_3d_26
    {ι : Type*} [Fintype ι]
    (Φ : ι → (Fin 25 → Fin 2 → ℂ) → Polynomial ℂ)
    (hΦ : ∀ α : ι, IsSpinorEquivariantMultilinear 25 (Φ α))
    (W : ι → DistinctPoints 26 → Fin 26 → ℂ) :
    ∃ x : DistinctPoints 26, Noncoplanar3D x.1 ∧
      ¬ LinearIndependent ℂ (fun i : Fin 26 => weightedSpinorCandidate Φ W x i) := by
  obtain ⟨x, hxnc, hx0⟩ := exists_noncoplanar_3d_26_atiyahDet_zero
  obtain ⟨μ, hμ⟩ := weightedSpinorCandidate_eq_smul_atiyahPoly (n := 26) (by omega) Φ hΦ W x
  have hdep := not_linearIndependent_of_atiyahDet_zero (by omega) x hx0
  have hdep2 := not_linearIndependent_scale_of_not_linearIndependent _ hdep μ
  exact ⟨x, hxnc, by simpa only [← hμ] using hdep2⟩

/-- **Universal No-Go (`n = 35`, planar):** No finite multi-body weighted
$\mathrm{SU}(2) \times S_{34}$-equivariant holomorphic spinor polynomial ansatz can remain linearly
independent on all planar configurations. -/
theorem universal_holomorphic_spinor_nogo_planar_35
    {ι : Type*} [Fintype ι]
    (Φ : ι → (Fin 34 → Fin 2 → ℂ) → Polynomial ℂ)
    (hΦ : ∀ α : ι, IsSpinorEquivariantMultilinear 34 (Φ α))
    (W : ι → DistinctPoints 35 → Fin 35 → ℂ) :
    ∃ x : DistinctPoints 35, IsCoplanar x ∧
      ¬ LinearIndependent ℂ (fun i : Fin 35 => weightedSpinorCandidate Φ W x i) := by
  obtain ⟨x, hxcop, _, hdep⟩ := exists_planar_35_atiyahDet_zero
  obtain ⟨μ, hμ⟩ := weightedSpinorCandidate_eq_smul_atiyahPoly (n := 35) (by omega) Φ hΦ W x
  have hdep2 := not_linearIndependent_scale_of_not_linearIndependent _ hdep μ
  exact ⟨x, hxcop, by simpa only [← hμ] using hdep2⟩

/-- **Universal No-Go ($\mathrm{Sp}(18)$, strictly non-coplanar 3D, `n = 36`):** Even within centrally
symmetric configurations, no finite multi-body weighted $\mathrm{SU}(2) \times S_{35}$-equivariant
holomorphic spinor polynomial ansatz remains linearly independent. -/
theorem universal_holomorphic_spinor_nogo_symplectic_36
    {ι : Type*} [Fintype ι]
    (Φ : ι → (Fin 35 → Fin 2 → ℂ) → Polynomial ℂ)
    (hΦ : ∀ α : ι, IsSpinorEquivariantMultilinear 35 (Φ α))
    (W : ι → DistinctPoints 36 → Fin 36 → ℂ) :
    ∃ c : SymplecticConfig 18, Noncoplanar3D c.p ∧
      ¬ LinearIndependent ℂ (fun i : Fin 36 => weightedSpinorCandidate Φ W (symplecticPoints c) i) := by
  obtain ⟨c, hcnc, hc0⟩ := exists_noncoplanar_symplectic_18_atiyahDet_zero
  obtain ⟨μ, hμ⟩ := weightedSpinorCandidate_eq_smul_atiyahPoly (n := 36) (by omega) Φ hΦ W (symplecticPoints c)
  have hdep := not_linearIndependent_of_atiyahDet_zero (by omega) (symplecticPoints c) hc0
  have hdep2 := not_linearIndependent_scale_of_not_linearIndependent _ hdep μ
  exact ⟨c, hcnc, by simpa only [← hμ] using hdep2⟩

end WeightedNoGo

/-! ## Section 3: Exact Hyperbolic $n = 3$ 5-Gap Positivity Identity ($D_3^{\mathbb{H}} > 1$) -/

section HyperbolicThreeGap

private lemma quad_linear_coeff (a b : ℂ) :
    let P := (Polynomial.C 1 + Polynomial.C a * Polynomial.X) * (Polynomial.C 1 + Polynomial.C b * Polynomial.X)
    P.coeff 0 = 1 ∧ P.coeff 1 = a + b ∧ P.coeff 2 = a * b := by
  intro P
  have hP : P = 1 + Polynomial.C (a + b) * Polynomial.X + Polynomial.C (a * b) * Polynomial.X ^ 2 := by
    dsimp [P]; simp only [map_one, map_add, map_mul]; ring
  rw [hP]
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C_mul_X_pow] <;> norm_num

/-- Exact algebraic 5-gap difference identity in the uniform projective chart $\psi_{ij} = [1, t_{ij}]$:
$\det M_3 - \mathrm{den}_3 = -(t_{01} - t_{21})(t_{02} - t_{12})(t_{10} - t_{20})$. -/
theorem three_point_uniform_gap_identity (t : Fin 3 → Fin 3 → ℝ) :
    let ψ : Fin 3 → Fin 3 → Fin 2 → ℂ := fun i j => ![1, (t i j : ℂ)]
    (atiyahMat ψ).det - atiyahDen ψ =
      -(((t 0 1 - t 2 1) * (t 0 2 - t 1 2) * (t 1 0 - t 2 0) : ℝ) : ℂ) := by
  intro ψ
  rw [Matrix.det_fin_three]
  have hE0 : (Finset.univ.erase (0 : Fin 3) : Finset (Fin 3)) = {1, 2} := by decide
  have hE1 : (Finset.univ.erase (1 : Fin 3) : Finset (Fin 3)) = {0, 2} := by decide
  have hE2 : (Finset.univ.erase (2 : Fin 3) : Finset (Fin 3)) = {0, 1} := by decide
  have hp0 : atiyahPoly ψ 0 =
      (Polynomial.C 1 + Polynomial.C (t 0 1 : ℂ) * Polynomial.X) *
        (Polynomial.C 1 + Polynomial.C (t 0 2 : ℂ) * Polynomial.X) := by
    unfold atiyahPoly; rw [hE0, Finset.prod_pair (by decide)]; simp [ψ]
  have hp1 : atiyahPoly ψ 1 =
      (Polynomial.C 1 + Polynomial.C (t 1 0 : ℂ) * Polynomial.X) *
        (Polynomial.C 1 + Polynomial.C (t 1 2 : ℂ) * Polynomial.X) := by
    unfold atiyahPoly; rw [hE1, Finset.prod_pair (by decide)]; simp [ψ]
  have hp2 : atiyahPoly ψ 2 =
      (Polynomial.C 1 + Polynomial.C (t 2 0 : ℂ) * Polynomial.X) *
        (Polynomial.C 1 + Polynomial.C (t 2 1 : ℂ) * Polynomial.X) := by
    unfold atiyahPoly; rw [hE2, Finset.prod_pair (by decide)]; simp [ψ]
  have hden : atiyahDen ψ =
      ((t 1 0 : ℂ) - (t 0 1 : ℂ)) * ((t 2 0 : ℂ) - (t 0 2 : ℂ)) * ((t 2 1 : ℂ) - (t 1 2 : ℂ)) := by
    unfold atiyahDen omega
    have hE : (Finset.univ : Finset { p : Fin 3 × Fin 3 // p.1 < p.2 }) =
        {⟨(0, 1), by decide⟩, ⟨(0, 2), by decide⟩, ⟨(1, 2), by decide⟩} := by
      ext ⟨⟨a, b⟩, hab⟩
      fin_cases a <;> fin_cases b <;> simp at hab ⊢
    rw [hE]
    simp only [Finset.prod_insert, Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq,
      Prod.mk.injEq, not_false_eq_true, ψ, Matrix.cons_val_zero,
      Matrix.cons_val_one, one_mul, mul_one, Fin.reduceEq, and_false, or_self]
    norm_num [Fin.isValue]
    ring
  simp only [atiyahMat, hp0, hp1, hp2, Fin.val_zero, Fin.val_one, Fin.val_two]
  have hP0 := quad_linear_coeff (t 0 1 : ℂ) (t 0 2 : ℂ)
  have hP1 := quad_linear_coeff (t 1 0 : ℂ) (t 1 2 : ℂ)
  have hP2 := quad_linear_coeff (t 2 0 : ℂ) (t 2 1 : ℂ)
  rw [hP0.1, hP0.2.1, hP0.2.2, hP1.1, hP1.2.1, hP1.2.2, hP2.1, hP2.2.1, hP2.2.2, hden]
  push_cast
  ring

private lemma pauliDot_eq_planar_proj {v : Fin 3 → ℝ}
    (hv1 : v 1 = 0) (hvnorm : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1) (hv2 : 1 + v 2 ≠ 0) :
    let t := v 0 / (1 + v 2)
    (pauliDot v).mulVec ![1, (t : ℂ)] = ![1, (t : ℂ)] := by
  intro t
  have hrsq : (v 0 : ℂ) ^ 2 + (v 2 : ℂ) ^ 2 = 1 := by
    rw [hv1] at hvnorm
    exact_mod_cast show v 0 ^ 2 + v 2 ^ 2 = 1 by linarith
  have hdenC : (1 + (v 2 : ℂ)) ≠ 0 := by exact_mod_cast hv2
  ext k
  fin_cases k
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, pauliDot, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, hv1, Complex.ofReal_zero,
      mul_zero, add_zero, sub_zero, mul_one, t]
    push_cast
    field_simp [hdenC]
    linear_combination hrsq
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, pauliDot, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, hv1, Complex.ofReal_zero,
      mul_zero, add_zero, mul_one, t]
    push_cast
    field_simp [hdenC]
    ring

private lemma kleinEndpoint_y_zero {a b : Fin 3 → ℝ} (ha : a 1 = 0) (hb : b 1 = 0) :
    kleinEndpoint a b 1 = 0 := by
  simp [kleinEndpoint, unitDir, ha, hb]

private lemma uniform_five_gap_gt_one_alg (t : Fin 3 → Fin 3 → ℝ)
    (hgap : t 2 0 < t 1 0 ∧ t 1 0 < t 1 2 ∧ t 1 2 < t 0 2 ∧ t 0 2 < t 0 1 ∧ t 0 1 < t 2 1) :
    let ψ : Fin 3 → Fin 3 → Fin 2 → ℂ := fun i j => ![1, (t i j : ℂ)]
    (atiyahDetOfSpinors ψ).im = 0 ∧ 1 < (atiyahDetOfSpinors ψ).re := by
  intro ψ
  have hdiff := three_point_uniform_gap_identity t
  have hdenR : atiyahDen ψ =
      (((t 1 0 - t 0 1) * (t 2 0 - t 0 2) * (t 2 1 - t 1 2) : ℝ) : ℂ) := by
    unfold atiyahDen omega
    have hE : (Finset.univ : Finset { p : Fin 3 × Fin 3 // p.1 < p.2 }) =
        {⟨(0, 1), by decide⟩, ⟨(0, 2), by decide⟩, ⟨(1, 2), by decide⟩} := by
      ext ⟨⟨a, b⟩, hab⟩; fin_cases a <;> fin_cases b <;> simp at hab ⊢
    rw [hE]
    simp only [Finset.prod_insert, Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq,
      Prod.mk.injEq, not_false_eq_true, ψ, Matrix.cons_val_zero,
      Matrix.cons_val_one, one_mul, mul_one, Fin.reduceEq, and_false, or_self]
    norm_num [Fin.isValue]
    ring
  set denR : ℝ := (t 1 0 - t 0 1) * (t 2 0 - t 0 2) * (t 2 1 - t 1 2)
  set gapR : ℝ := -((t 0 1 - t 2 1) * (t 0 2 - t 1 2) * (t 1 0 - t 2 0))
  obtain ⟨h1, h2, h3, h4, h5⟩ := hgap
  have hden_pos : 0 < denR := by
    have a1 : t 1 0 - t 0 1 < 0 := by linarith
    have a2 : t 2 0 - t 0 2 < 0 := by linarith
    have a3 : 0 < t 2 1 - t 1 2 := by linarith
    exact mul_pos (mul_pos_of_neg_of_neg a1 a2) a3
  have hgap_pos : 0 < gapR := by
    have b1 : t 0 1 - t 2 1 < 0 := by linarith
    have b2 : 0 < t 0 2 - t 1 2 := by linarith
    have b3 : 0 < t 1 0 - t 2 0 := by linarith
    have hb123 : (t 0 1 - t 2 1) * (t 0 2 - t 1 2) * (t 1 0 - t 2 0) < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos b1 b2) b3
    dsimp [gapR]; linarith
  have hmat_eq : (atiyahMat ψ).det = ((denR + gapR : ℝ) : ℂ) := by
    dsimp only [ψ] at hdiff
    have hsub := sub_eq_iff_eq_add.mp hdiff
    rw [hdenR] at hsub
    rw [hsub]
    dsimp only [denR, gapR]
    push_cast
    ring
  have hval : atiyahDetOfSpinors ψ = (((denR + gapR) / denR : ℝ) : ℂ) := by
    unfold atiyahDetOfSpinors
    rw [hmat_eq, hdenR, ← Complex.ofReal_div]
  rw [hval, Complex.ofReal_im, Complex.ofReal_re]
  refine ⟨rfl, ?_⟩
  rw [lt_div_iff₀ hden_pos]
  linarith

section GapFiveIrred
attribute [local irreducible] kleinEndpoint atiyahDetOfSpinors

/-- **General Hyperbolic $n = 3$ 5-Gap Positivity Theorem:** For any triangle in an equatorial
hyperbolic plane $y = 0 \subset \mathbb{B}^3$ avoiding the stereographic pole $(0, 0, -1)$ whose six
ideal chord slopes satisfy the cyclic 5-gap chain $t_{20} < t_{10} < t_{12} < t_{02} < t_{01} < t_{21}$,
we have $\mathrm{Im}(D_3^{\mathbb{H}}) = 0$ and $D_3^{\mathbb{H}} > 1$. -/
theorem hyperbolic_three_point_five_gap_gt_one (q : KleinBallPoints 3)
    (hy : ∀ i : Fin 3, q.1 i 1 = 0)
    (hpole : ∀ i j : Fin 3, i ≠ j → 1 + kleinEndpoint (q.1 i) (q.1 j) 2 ≠ 0)
    (hgap :
      let t := fun i j : Fin 3 => kleinEndpoint (q.1 i) (q.1 j) 0 / (1 + kleinEndpoint (q.1 i) (q.1 j) 2)
      t 2 0 < t 1 0 ∧ t 1 0 < t 1 2 ∧ t 1 2 < t 0 2 ∧ t 0 2 < t 0 1 ∧ t 0 1 < t 2 1) :
    (hyperbolicAtiyahDet q).im = 0 ∧ 1 < (hyperbolicAtiyahDet q).re := by
  let t : Fin 3 → Fin 3 → ℝ := fun i j =>
    kleinEndpoint (q.1 i) (q.1 j) 0 / (1 + kleinEndpoint (q.1 i) (q.1 j) 2)
  let ψ : Fin 3 → Fin 3 → Fin 2 → ℂ := fun i j => ![1, (t i j : ℂ)]
  have hnorm : ∀ i j, i ≠ j →
      kleinEndpoint (q.1 i) (q.1 j) 0 ^ 2 + kleinEndpoint (q.1 i) (q.1 j) 1 ^ 2 +
        kleinEndpoint (q.1 i) (q.1 j) 2 ^ 2 = 1 :=
    fun i j hij => kleinEndpoint_norm_sq (q.2.1 i) (q.2.2 i j hij)
  have hne_end : ∀ i j, i ≠ j → kleinEndpoint (q.1 i) (q.1 j) ≠ kleinEndpoint (q.1 j) (q.1 i) :=
    fun i j hij => kleinEndpoint_ne_swap (q.2.1 i) (q.2.1 j) (q.2.2 i j hij)
  have hψ_ne : ∀ i j, i ≠ j → ψ i j 0 ≠ 0 ∨ ψ i j 1 ≠ 0 := by
    intro i j _; left; simp [ψ]
  have hψ_mul : ∀ i j, i ≠ j →
      (pauliDot (kleinEndpoint (q.1 i) (q.1 j))).mulVec (ψ i j) = ψ i j := by
    intro i j hij
    exact pauliDot_eq_planar_proj (kleinEndpoint_y_zero (hy i) (hy j)) (hnorm i j hij) (hpole i j hij)
  have hdet_eq : hyperbolicAtiyahDet q = atiyahDetOfSpinors ψ := by
    unfold hyperbolicAtiyahDet
    exact atiyahDetOfSpinors_eq_of_unitSpinors
      (fun i j => kleinEndpoint (q.1 i) (q.1 j)) hnorm hne_end ψ hψ_ne hψ_mul
  rw [hdet_eq]
  exact uniform_five_gap_gt_one_alg t hgap

end GapFiveIrred

/-- Concrete unconditional witness verifying $D_3^{\mathbb{H}} > 1$ on the equilateral/Pythagorean
triangle $\{(-3/5, 0, 0), (3/5, 0, 0), (0, 0, 4/5)\} \subset \mathbb{B}^3$. -/
theorem exists_hyperbolic_three_point_det_gt_one :
    ∃ q : KleinBallPoints 3, (hyperbolicAtiyahDet q).im = 0 ∧ 1 < (hyperbolicAtiyahDet q).re := by
  let pts : Fin 3 → Fin 3 → ℝ := ![
    ![-(3 / 5 : ℝ), 0, 0],
    ![(3 / 5 : ℝ), 0, 0],
    ![0, 0, (4 / 5 : ℝ)]
  ]
  have hball : ∀ i : Fin 3, pts i 0 ^ 2 + pts i 1 ^ 2 + pts i 2 ^ 2 < 1 := by
    intro i; fin_cases i <;> simp [pts] <;> norm_num
  have hdist : ∀ i j : Fin 3, i ≠ j → pts i ≠ pts j := by
    intro i j hij h
    fin_cases i <;> fin_cases j <;> simp only [ne_eq, not_true_eq_false] at hij <;>
      have h0 := congr_fun h 0 <;> norm_num [pts] at h0
  let q : KleinBallPoints 3 := ⟨pts, hball, hdist⟩
  have hy : ∀ i : Fin 3, q.1 i 1 = 0 := by intro i; fin_cases i <;> rfl
  -- Direct coordinate calculations for the 6 ideal chord endpoints on this triangle:
  have hs_lo : (21 / 25 : ℝ) < Real.sqrt (481 / 625) := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hs_hi : Real.sqrt (481 / 625) < (22 / 25 : ℝ) := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have ht01 : kleinEndpoint (q.1 0) (q.1 1) 0 = 1 ∧ kleinEndpoint (q.1 0) (q.1 1) 2 = 0 := by
    have heu : euclidNorm (fun k => q.1 1 k - q.1 0 k) = (6 / 5 : ℝ) := by
      simp [euclidNorm, q, pts]; norm_num
    dsimp only [kleinEndpoint, unitDir]
    rw [heu]
    simp only [q, pts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    constructor <;> norm_num
  have ht10 : kleinEndpoint (q.1 1) (q.1 0) 0 = -1 ∧ kleinEndpoint (q.1 1) (q.1 0) 2 = 0 := by
    have heu : euclidNorm (fun k => q.1 0 k - q.1 1 k) = (6 / 5 : ℝ) := by
      simp [euclidNorm, q, pts]; norm_num
    dsimp only [kleinEndpoint, unitDir]
    rw [heu]
    simp only [q, pts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    constructor <;> norm_num
  have ht02 :
      let s := Real.sqrt (481 / 625)
      kleinEndpoint (q.1 0) (q.1 2) 0 = -(3 / 5) + (9 / 25 + s) * (3 / 5) ∧
      kleinEndpoint (q.1 0) (q.1 2) 2 = (9 / 25 + s) * (4 / 5) := by
    have heu : euclidNorm (fun k => q.1 2 k - q.1 0 k) = (1 : ℝ) := by
      simp [euclidNorm, q, pts]; norm_num
    dsimp only [kleinEndpoint, unitDir]
    rw [heu]
    simp only [div_one, q, pts, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    constructor <;> ring_nf
  have ht12 :
      let s := Real.sqrt (481 / 625)
      kleinEndpoint (q.1 1) (q.1 2) 0 = (3 / 5) - (9 / 25 + s) * (3 / 5) ∧
      kleinEndpoint (q.1 1) (q.1 2) 2 = (9 / 25 + s) * (4 / 5) := by
    have heu : euclidNorm (fun k => q.1 2 k - q.1 1 k) = (1 : ℝ) := by
      simp [euclidNorm, q, pts]; norm_num
    dsimp only [kleinEndpoint, unitDir]
    rw [heu]
    simp only [div_one, q, pts, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    constructor <;> ring_nf
  have ht20 :
      let s := Real.sqrt (481 / 625)
      kleinEndpoint (q.1 2) (q.1 0) 0 = (16 / 25 + s) * (-(3 / 5)) ∧
      kleinEndpoint (q.1 2) (q.1 0) 2 = (4 / 5) - (16 / 25 + s) * (4 / 5) := by
    have heu : euclidNorm (fun k => q.1 0 k - q.1 2 k) = (1 : ℝ) := by
      simp [euclidNorm, q, pts]; norm_num
    dsimp only [kleinEndpoint, unitDir]
    rw [heu]
    simp only [div_one, q, pts, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    constructor <;> ring_nf
  have ht21 :
      let s := Real.sqrt (481 / 625)
      kleinEndpoint (q.1 2) (q.1 1) 0 = (16 / 25 + s) * (3 / 5) ∧
      kleinEndpoint (q.1 2) (q.1 1) 2 = (4 / 5) - (16 / 25 + s) * (4 / 5) := by
    have heu : euclidNorm (fun k => q.1 1 k - q.1 2 k) = (1 : ℝ) := by
      simp [euclidNorm, q, pts]; norm_num
    dsimp only [kleinEndpoint, unitDir]
    rw [heu]
    simp only [div_one, q, pts, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    constructor <;> ring_nf
  have hpole : ∀ i j : Fin 3, i ≠ j → 1 + kleinEndpoint (q.1 i) (q.1 j) 2 ≠ 0 := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij
    · change 1 + kleinEndpoint (q.1 0) (q.1 1) 2 ≠ 0; rw [ht01.2]; norm_num
    · change 1 + kleinEndpoint (q.1 0) (q.1 2) 2 ≠ 0; rw [ht02.2]; linarith
    · change 1 + kleinEndpoint (q.1 1) (q.1 0) 2 ≠ 0; rw [ht10.2]; norm_num
    · change 1 + kleinEndpoint (q.1 1) (q.1 2) 2 ≠ 0; rw [ht12.2]; linarith
    · change 1 + kleinEndpoint (q.1 2) (q.1 0) 2 ≠ 0; rw [ht20.2]; linarith
    · change 1 + kleinEndpoint (q.1 2) (q.1 1) 2 ≠ 0; rw [ht21.2]; linarith
  have hgap :
      let t := fun i j : Fin 3 => kleinEndpoint (q.1 i) (q.1 j) 0 / (1 + kleinEndpoint (q.1 i) (q.1 j) 2)
      t 2 0 < t 1 0 ∧ t 1 0 < t 1 2 ∧ t 1 2 < t 0 2 ∧ t 0 2 < t 0 1 ∧ t 0 1 < t 2 1 := by
    dsimp only
    rw [ht01.1, ht01.2, ht10.1, ht10.2, ht02.1, ht02.2, ht12.1, ht12.2, ht20.1, ht20.2, ht21.1, ht21.2]
    have hden02 : 0 < 1 + (9 / 25 + Real.sqrt (481 / 625)) * (4 / 5) := by linarith
    have hden20 : 0 < 1 + ((4 / 5 : ℝ) - (16 / 25 + Real.sqrt (481 / 625)) * (4 / 5)) := by linarith
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [show (-1 : ℝ) / (1 + 0) = -1 by norm_num, div_lt_iff₀ hden20]
      nlinarith [hs_lo, hs_hi]
    · rw [show (-1 : ℝ) / (1 + 0) = -1 by norm_num, lt_div_iff₀ hden02]
      nlinarith [hs_lo, hs_hi]
    · rw [div_lt_div_iff_of_pos_right hden02]
      nlinarith [hs_lo, hs_hi]
    · rw [show (1 : ℝ) / (1 + 0) = 1 by norm_num, div_lt_one hden02]
      nlinarith [hs_lo, hs_hi]
    · rw [show (1 : ℝ) / (1 + 0) = 1 by norm_num, lt_div_iff₀ hden20]
      nlinarith [hs_lo, hs_hi]
  exact ⟨q, hyperbolic_three_point_five_gap_gt_one q hy hpole hgap⟩

end HyperbolicThreeGap

end Matematyka.AtiyahSutcliffeNoGo
