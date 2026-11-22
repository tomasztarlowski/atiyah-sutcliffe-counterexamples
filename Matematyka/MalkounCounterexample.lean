import Mathlib

/-!
# Shared Pauli Spinor Preliminaries on $\\mathbb{R}^3$ and $\\mathbb{C}^2$

This self-contained module provides Euclidean norms, unit chord directions, Pauli dot matrices,
normalized $+1$-eigenspinors, the $\\mathrm{SL}(2,\\mathbb{C})$ symplectic form `omega`, and
`canonicalSpinor` imported by `Matematyka.AtiyahSutcliffe`.
-/

namespace Matematyka.MalkounCounterexample

open Complex Real

section GeneralDefinitions

variable {n : ℕ}

/-- Configuration space $C_G(\mathbb{R}^3)$: adjacent vertices cannot collide. -/
def ConfigSpace (G : SimpleGraph (Fin n)) : Type :=
  { x : Fin n → Fin 3 → ℝ // ∀ u v, G.Adj u v → x u ≠ x v }

/-- Euclidean norm of a vector in $\mathbb{R}^3$. -/
noncomputable def euclidNorm (v : Fin 3 → ℝ) : ℝ :=
  Real.sqrt (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2)

lemma euclidNorm_pos_of_ne {a b : Fin 3 → ℝ} (h : a ≠ b) :
    0 < euclidNorm (fun k => b k - a k) := by
  rw [euclidNorm, Real.sqrt_pos]
  by_contra hle
  push Not at hle
  have h0 : b 0 - a 0 = 0 := by
    nlinarith [sq_nonneg (b 0 - a 0), sq_nonneg (b 1 - a 1), sq_nonneg (b 2 - a 2)]
  have h1 : b 1 - a 1 = 0 := by
    nlinarith [sq_nonneg (b 0 - a 0), sq_nonneg (b 1 - a 1), sq_nonneg (b 2 - a 2)]
  have h2 : b 2 - a 2 = 0 := by
    nlinarith [sq_nonneg (b 0 - a 0), sq_nonneg (b 1 - a 1), sq_nonneg (b 2 - a 2)]
  apply h
  ext k
  fin_cases k <;> dsimp <;> linarith

/-- Unit direction vector $v_{ij} = (\mathbf{x}_j - \mathbf{x}_i) / \|\mathbf{x}_j - \mathbf{x}_i\| \in S^2$. -/
noncomputable def unitDir (a b : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun k => (b k - a k) / euclidNorm (fun j => b j - a j)

lemma unitDir_norm_sq {a b : Fin 3 → ℝ} (h : a ≠ b) :
    (unitDir a b 0) ^ 2 + (unitDir a b 1) ^ 2 + (unitDir a b 2) ^ 2 = 1 := by
  have hpos : 0 < euclidNorm (fun j => b j - a j) := euclidNorm_pos_of_ne h
  have hne : euclidNorm (fun j => b j - a j) ≠ 0 := hpos.ne'
  have hsq : euclidNorm (fun j => b j - a j) ^ 2 =
      (b 0 - a 0) ^ 2 + (b 1 - a 1) ^ 2 + (b 2 - a 2) ^ 2 := by
    rw [euclidNorm, Real.sq_sqrt]
    positivity
  unfold unitDir
  field_simp [hne]
  linarith

lemma unitDir_swap (a b : Fin 3 → ℝ) :
    unitDir b a = fun k => -unitDir a b k := by
  ext k
  have hnorm : euclidNorm (fun j => a j - b j) = euclidNorm (fun j => b j - a j) := by
    simp only [euclidNorm]
    congr 1
    ring
  simp only [unitDir, hnorm]
  ring

/-- Hermitian $2 \times 2$ matrix $v \cdot \vec{\sigma}$. -/
def pauliDot (v : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(v 2 : ℂ), (v 0 : ℂ) - Complex.I * (v 1 : ℂ);
     (v 0 : ℂ) + Complex.I * (v 1 : ℂ), -(v 2 : ℂ)]

/-- Normalized $+1$-eigenvector of $v \cdot \vec{\sigma}$ (Malkoun Eq. (5)). -/
def IsPosSpinor (v : Fin 3 → ℝ) (ψ : Fin 2 → ℂ) : Prop :=
  ‖ψ 0‖ ^ 2 + ‖ψ 1‖ ^ 2 = 1 ∧ (pauliDot v).mulVec ψ = ψ

/-- Skew-symmetric bilinear form $\omega$ on $\mathbb{C}^2$ (Malkoun Eq. (7)). -/
def omega (ψ φ : Fin 2 → ℂ) : ℂ :=
  ψ 0 * φ 1 - ψ 1 * φ 0

lemma omega_swap (ψ φ : Fin 2 → ℂ) : omega φ ψ = -omega ψ φ := by
  simp only [omega]; ring

lemma omega_smul (c₁ c₂ : ℂ) (ψ φ : Fin 2 → ℂ) :
    omega (fun k => c₁ * ψ k) (fun k => c₂ * φ k) = (c₁ * c₂) * omega ψ φ := by
  simp only [omega]; ring

lemma pauliDot_neg (v : Fin 3 → ℝ) :
    pauliDot (fun k => -v k) = -pauliDot v := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliDot] <;> ring

/-- Any two $+1$-eigenvectors of `pauliDot v` satisfy `omega ψ φ = 0`. -/
lemma omega_eq_zero_of_mulVec {v : Fin 3 → ℝ} {ψ φ : Fin 2 → ℂ}
    (hψ : (pauliDot v).mulVec ψ = ψ) (hφ : (pauliDot v).mulVec φ = φ) :
    omega ψ φ = 0 := by
  have hψ0 := congr_fun hψ 0
  have hψ1 := congr_fun hψ 1
  have hφ0 := congr_fun hφ 0
  have hφ1 := congr_fun hφ 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, pauliDot, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one] at hψ0 hψ1 hφ0 hφ1
  have hA : ((v 2 : ℂ) - 1) * omega ψ φ = 0 := by
    unfold omega
    linear_combination (φ 1) * hψ0 - (ψ 1) * hφ0
  have hB : (-(v 2 : ℂ) - 1) * omega ψ φ = 0 := by
    unfold omega
    linear_combination (ψ 0) * hφ1 - (φ 0) * hψ1
  have hsum : (-2 : ℂ) * omega ψ φ = 0 := by linear_combination hA + hB
  exact (mul_eq_zero.mp hsum).resolve_left (by norm_num)

/-- Any two normalized $+1$-eigenvectors of `pauliDot v` differ by a nonzero scalar factor. -/
lemma isPosSpinor_collinear {v : Fin 3 → ℝ} {ψ φ : Fin 2 → ℂ}
    (hψ : IsPosSpinor v ψ) (hφ : IsPosSpinor v φ) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ k, φ k = c * ψ k := by
  have hom := omega_eq_zero_of_mulVec hψ.2 hφ.2
  have hψ_nz : ψ 0 ≠ 0 ∨ ψ 1 ≠ 0 := by
    by_contra h
    push Not at h
    have hn := hψ.1
    rw [h.1, h.2] at hn
    norm_num at hn
  have hφ_nz : φ 0 ≠ 0 ∨ φ 1 ≠ 0 := by
    by_contra h
    push Not at h
    have hn := hφ.1
    rw [h.1, h.2] at hn
    norm_num at hn
  have heq : ψ 0 * φ 1 = ψ 1 * φ 0 := sub_eq_zero.mp hom
  rcases hψ_nz with h0 | h1
  · refine ⟨φ 0 / ψ 0, ?_, ?_⟩
    · intro hc
      have hφ0 : φ 0 = 0 := (div_eq_zero_iff.mp hc).resolve_right h0
      rw [hφ0, mul_zero] at heq
      have hφ1 : φ 1 = 0 := (mul_eq_zero.mp heq).resolve_left h0
      rcases hφ_nz with h' | h'
      · exact h' hφ0
      · exact h' hφ1
    · intro k
      fin_cases k <;> dsimp
      · field_simp [h0]
      · field_simp [h0]; linear_combination heq
  · refine ⟨φ 1 / ψ 1, ?_, ?_⟩
    · intro hc
      have hφ1 : φ 1 = 0 := (div_eq_zero_iff.mp hc).resolve_right h1
      rw [hφ1, mul_zero] at heq
      have hφ0 : φ 0 = 0 := (mul_eq_zero.mp heq.symm).resolve_left h1
      rcases hφ_nz with h' | h'
      · exact h' hφ0
      · exact h' hφ1
    · intro k
      fin_cases k <;> dsimp
      · field_simp [h1]; linear_combination -heq
      · field_simp [h1]

/-- A $+1$-eigenvector of $v\cdot\vec{\sigma}$ and a $+1$-eigenvector of $(-v)\cdot\vec{\sigma}$
never have vanishing $\omega$. -/
lemma omega_opp_ne_zero {v : Fin 3 → ℝ} {ψ φ : Fin 2 → ℂ}
    (hψ : IsPosSpinor v ψ) (hφ : IsPosSpinor (fun k => -v k) φ) :
    omega ψ φ ≠ 0 := by
  intro hom
  have hψ_nz : ψ 0 ≠ 0 ∨ ψ 1 ≠ 0 := by
    by_contra h; push Not at h; have hn := hψ.1; rw [h.1, h.2] at hn; norm_num at hn
  have hφ_nz : φ 0 ≠ 0 ∨ φ 1 ≠ 0 := by
    by_contra h; push Not at h; have hn := hφ.1; rw [h.1, h.2] at hn; norm_num at hn
  have heq : ψ 0 * φ 1 = ψ 1 * φ 0 := sub_eq_zero.mp hom
  have hφ_neg : (pauliDot v).mulVec φ = -φ := by
    have hneg : -(pauliDot v).mulVec φ = φ := by
      simpa [pauliDot_neg, Matrix.neg_mulVec] using hφ.2
    ext k
    have hk := congr_fun hneg k
    simp only [Pi.neg_apply] at hk ⊢
    linear_combination -hk
  have hmul : (pauliDot v).mulVec φ = φ := by
    rcases hψ_nz with h0 | h1
    · have hrel : φ = (φ 0 / ψ 0) • ψ := by
        ext k; fin_cases k <;> dsimp
        · field_simp [h0]
        · field_simp [h0]; linear_combination heq
      rw [hrel, Matrix.mulVec_smul, hψ.2]
    · have hrel : φ = (φ 1 / ψ 1) • ψ := by
        ext k; fin_cases k <;> dsimp
        · field_simp [h1]; linear_combination -heq
        · field_simp [h1]
      rw [hrel, Matrix.mulVec_smul, hψ.2]
  have hcontra : φ = 0 := by
    ext k
    have hk := (congr_fun hmul k).symm.trans (congr_fun hφ_neg k)
    simp only [Pi.neg_apply] at hk
    exact CharZero.eq_neg_self_iff.mp hk
  rcases hφ_nz with h0 | h1
  · exact h0 (congr_fun hcontra 0)
  · exact h1 (congr_fun hcontra 1)

private def unnormPos (v : Fin 3 → ℝ) (i : Fin 2) : ℂ :=
  if i = 0 then ((1 + v 2 : ℝ) : ℂ) else (v 0 : ℂ) + Complex.I * (v 1 : ℂ)

private def unnormNeg (v : Fin 3 → ℝ) (i : Fin 2) : ℂ :=
  if i = 0 then (v 0 : ℂ) - Complex.I * (v 1 : ℂ) else ((1 - v 2 : ℝ) : ℂ)

private lemma pauliDot_unnormPos {v : Fin 3 → ℝ} (hv : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1) :
    (pauliDot v).mulVec (unnormPos v) = unnormPos v := by
  ext k
  simp only [unnormPos, Matrix.mulVec, dotProduct, Fin.sum_univ_two, pauliDot, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
  fin_cases k <;> dsimp <;> apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> nlinarith

private lemma pauliDot_unnormNeg {v : Fin 3 → ℝ} (hv : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1) :
    (pauliDot v).mulVec (unnormNeg v) = unnormNeg v := by
  ext k
  simp only [unnormNeg, Matrix.mulVec, dotProduct, Fin.sum_univ_two, pauliDot, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
  fin_cases k <;> dsimp <;> apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> nlinarith

/-- Canonical normalized $+1$-eigenvector of `pauliDot v` for unit `v ∈ S^2`. -/
noncomputable def canonicalSpinor (v : Fin 3 → ℝ) : Fin 2 → ℂ :=
  if 0 ≤ v 2 then
    ((1 / Real.sqrt (2 * (1 + v 2)) : ℝ) : ℂ) • unnormPos v
  else
    ((1 / Real.sqrt (2 * (1 - v 2)) : ℝ) : ℂ) • unnormNeg v

lemma isPosSpinor_canonicalSpinor {v : Fin 3 → ℝ} (hv : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1) :
    IsPosSpinor v (canonicalSpinor v) := by
  have hv2_ge : -1 ≤ v 2 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2 + 1)]
  have hv2_le : v 2 ≤ 1 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2 - 1)]
  by_cases h : 0 ≤ v 2
  · have hpos : 0 < 2 * (1 + v 2) := by linarith
    have hs_sq : Real.sqrt (2 * (1 + v 2)) ^ 2 = 2 * (1 + v 2) := Real.sq_sqrt hpos.le
    have hnorm0 : ‖(((1 / Real.sqrt (2 * (1 + v 2)) : ℝ) : ℂ) • unnormPos v) 0‖ ^ 2 =
        (1 + v 2) ^ 2 / (2 * (1 + v 2)) := by
      simp only [Pi.smul_apply, smul_eq_mul, unnormPos, ↓reduceIte, norm_mul, mul_pow,
        Complex.norm_real, Real.norm_eq_abs, sq_abs, one_div, inv_pow, hs_sq]
      ring
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    have hnorm1 : ‖(((1 / Real.sqrt (2 * (1 + v 2)) : ℝ) : ℂ) • unnormPos v) 1‖ ^ 2 =
        (v 0 ^ 2 + v 1 ^ 2) / (2 * (1 + v 2)) := by
      simp only [Pi.smul_apply, smul_eq_mul, unnormPos, h10, ↓reduceIte, norm_mul, mul_pow,
        Complex.norm_real, Real.norm_eq_abs, sq_abs, one_div, inv_pow, hs_sq]
      have hsq : ‖(v 0 : ℂ) + Complex.I * (v 1 : ℂ)‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
        ring
      rw [hsq]; ring
    refine ⟨?_, ?_⟩
    · simp only [canonicalSpinor, h, ↓reduceIte]
      rw [hnorm0, hnorm1, ← add_div, div_eq_one_iff_eq hpos.ne']
      linarith
    · simp only [canonicalSpinor, h, ↓reduceIte, Matrix.mulVec_smul, pauliDot_unnormPos hv]
  · push Not at h
    have hpos : 0 < 2 * (1 - v 2) := by linarith
    have hs_sq : Real.sqrt (2 * (1 - v 2)) ^ 2 = 2 * (1 - v 2) := Real.sq_sqrt hpos.le
    have hnorm0 : ‖(((1 / Real.sqrt (2 * (1 - v 2)) : ℝ) : ℂ) • unnormNeg v) 0‖ ^ 2 =
        (v 0 ^ 2 + v 1 ^ 2) / (2 * (1 - v 2)) := by
      simp only [Pi.smul_apply, smul_eq_mul, unnormNeg, ↓reduceIte, norm_mul, mul_pow,
        Complex.norm_real, Real.norm_eq_abs, sq_abs, one_div, inv_pow, hs_sq]
      have hsq : ‖(v 0 : ℂ) - Complex.I * (v 1 : ℂ)‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
        ring
      rw [hsq]; ring
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    have hnorm1 : ‖(((1 / Real.sqrt (2 * (1 - v 2)) : ℝ) : ℂ) • unnormNeg v) 1‖ ^ 2 =
        (1 - v 2) ^ 2 / (2 * (1 - v 2)) := by
      simp only [Pi.smul_apply, smul_eq_mul, unnormNeg, h10, ↓reduceIte, norm_mul, mul_pow,
        Complex.norm_real, Real.norm_eq_abs, sq_abs, one_div, inv_pow, hs_sq]
      ring
    refine ⟨?_, ?_⟩
    · simp only [canonicalSpinor, not_le.mpr h, ↓reduceIte]
      rw [hnorm0, hnorm1, ← add_div, div_eq_one_iff_eq hpos.ne']
      linarith
    · simp only [canonicalSpinor, not_le.mpr h, ↓reduceIte, Matrix.mulVec_smul, pauliDot_unnormNeg hv]


end GeneralDefinitions

end Matematyka.MalkounCounterexample
