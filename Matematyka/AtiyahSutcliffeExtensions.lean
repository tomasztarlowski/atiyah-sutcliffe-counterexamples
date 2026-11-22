import Matematyka.AtiyahSutcliffe

/-!
# Extensions: Direct $n = 57$ Record, Genuine Non-Coplanar 3D Disproofs, and Hyperbolic $\mathbb{H}^3$ Disproofs

We extend `Matematyka.AtiyahSutcliffe` without modifying or weakening any theorem in the base file:

1. **Part A (General Unit-Vector Spinor Theory):**
   - `atiyahDetOfSpinors_eq_of_unitSpinors`: projective invariance and nonvanishing denominator
     for arbitrary distinct unit-direction pairs $u_{ij} \neq u_{ji} \in S^2$.
   - `tendsto_atiyahDetOfSpinors_unit`: continuity of `atiyahDetOfSpinors` along any converging
     unit-vector family (covering arbitrary 3D perturbations and $\varepsilon \to 0^+$ Euclidean limits).
2. **Part B (Kernel Gaussian Elimination `FpIv` and Planar $n = 57$ Record + Direct $n = 63$ Norm):**
   - Exact outward-rounded division `FpIv.divFp` and verified Gaussian elimination `gaussDetIv`.
   - Direct $n = 57$ planar integer witness ($a=28$ lower axial, $3$ positive-$x$ points, $b=26$ upper
     axial) satisfying $D_{57}(1) < 0$ and $|D_{57}(1)| < 1$ (`-1 < D < 0` certified directly at
     scale $S_{57} = 10^{40}$), plus collision-free homotopy to $D_{57}(s_0) = 0$.
   - Direct kernel proof that $|D_{63}(\mathbf{x}^{(63)}(1))| < 1$ as well.
3. **Part C (Genuine Non-Coplanar 3D Disproofs):**
   - `IsCoplanar` predicate for $C_n(\mathbb{R}^3)$.
   - Sharp minimal $n = 5$ **non-coplanar** C3 witness obtained by 3D continuity perturbation.
   - Mirror-pair extension `mirrorPairExt`: exact reality $(\mathrm{Im}\, D_{n+2} = 0)$, non-coplanarity,
     and large-$H$ convergence $\lim_{H \to \infty} D_{n+2}(x \cup \{(0,\pm 1,H)\}) = D_n(x)$,
     yielding genuine non-coplanar 3D C1 & C2 counterexamples at $n = 59$.
4. **Part D (Hyperbolic 3-Space $\mathbb{H}^3$ Beltrami–Klein Disproofs):**
   - Intrinsic ideal-endpoint hyperbolic Atiyah determinant $D_n^{\mathbb{H}}$ on $\mathbb{B}^3 \subset \mathbb{R}^3$.
   - Tangent scaling theorem $\lim_{\varepsilon \to 0^+} D_n^{\mathbb{H}}(\varepsilon \mathbf{x}) = D_n(\mathbf{x})$.
   - Formal disproofs of Hyperbolic C1 (`¬ HyperbolicAtiyahConjecture1Prop`, `¬ HyperbolicAtiyahDetNonzeroProp`),
     Hyperbolic C2 (`¬ HyperbolicAtiyahSutcliffeConjecture2Prop`), and Hyperbolic C3 at $n = 5$
     (`¬ HyperbolicAtiyahSutcliffeConjecture3Prop`), both planar ($\mathbb{H}^2$) and strictly non-coplanar ($\mathbb{H}^3$).
-/

namespace Matematyka.AtiyahSutcliffe

open Complex Real Matrix Polynomial Filter Topology
open Matematyka.MalkounCounterexample

/-! ## Part A: General Unit-Vector Spinor Invariance & Everywhere Continuity -/

section UnitSpinorContinuity

lemma omega_ne_zero_of_unit_ne {u w : Fin 3 → ℝ}
    (hne : u ≠ w) {ψ φ : Fin 2 → ℂ}
    (hψ_ne : ψ 0 ≠ 0 ∨ ψ 1 ≠ 0) (hψ_mul : (pauliDot u).mulVec ψ = ψ)
    (hφ_ne : φ 0 ≠ 0 ∨ φ 1 ≠ 0) (hφ_mul : (pauliDot w).mulVec φ = φ) :
    omega ψ φ ≠ 0 := by
  intro hom
  have hcol : ∃ c : ℂ, c ≠ 0 ∧ ∀ k, φ k = c * ψ k := by
    have heq : ψ 0 * φ 1 = ψ 1 * φ 0 := sub_eq_zero.mp hom
    rcases hψ_ne with h0 | h1
    · refine ⟨φ 0 / ψ 0, ?_, fun k => ?_⟩
      · intro hc
        have hφ0 : φ 0 = 0 := (div_eq_zero_iff.mp hc).resolve_right h0
        rw [hφ0, mul_zero] at heq
        have hφ1 : φ 1 = 0 := (mul_eq_zero.mp heq).resolve_left h0
        rcases hφ_ne with h | h <;> contradiction
      · fin_cases k <;> dsimp
        · field_simp [h0]
        · field_simp [h0]; linear_combination heq
    · refine ⟨φ 1 / ψ 1, ?_, fun k => ?_⟩
      · intro hc
        have hφ1 : φ 1 = 0 := (div_eq_zero_iff.mp hc).resolve_right h1
        rw [hφ1, mul_zero] at heq
        have hφ0 : φ 0 = 0 := (mul_eq_zero.mp heq.symm).resolve_left h1
        rcases hφ_ne with h | h <;> contradiction
      · fin_cases k <;> dsimp
        · field_simp [h1]; linear_combination -heq
        · field_simp [h1]
  rcases hcol with ⟨c, _, hc⟩
  have hrel : φ = c • ψ := funext hc
  have huφ : (pauliDot u).mulVec φ = φ := by
    rw [hrel, Matrix.mulVec_smul, hψ_mul]
  have hsub : ∀ k, (pauliDot u).mulVec φ k - (pauliDot w).mulVec φ k = 0 := fun k => by
    rw [congr_fun huφ k, congr_fun hφ_mul k, sub_self]
  have r0 := hsub 0
  have r1 := hsub 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, pauliDot, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one] at r0 r1
  set d0 : ℂ := ((u 0 - w 0 : ℝ) : ℂ)
  set d1 : ℂ := ((u 1 - w 1 : ℝ) : ℂ)
  set d2 : ℂ := ((u 2 - w 2 : ℝ) : ℂ)
  have hd_nz : (u 0 - w 0) ^ 2 + (u 1 - w 1) ^ 2 + (u 2 - w 2) ^ 2 ≠ 0 := by
    intro hz
    apply hne; ext k
    have h0' : u 0 - w 0 = 0 := by
      nlinarith [sq_nonneg (u 0 - w 0), sq_nonneg (u 1 - w 1), sq_nonneg (u 2 - w 2)]
    have h1' : u 1 - w 1 = 0 := by
      nlinarith [sq_nonneg (u 0 - w 0), sq_nonneg (u 1 - w 1), sq_nonneg (u 2 - w 2)]
    have h2' : u 2 - w 2 = 0 := by
      nlinarith [sq_nonneg (u 0 - w 0), sq_nonneg (u 1 - w 1), sq_nonneg (u 2 - w 2)]
    fin_cases k <;> dsimp <;> linarith
  have h0eq : d2 * φ 0 + (d0 - Complex.I * d1) * φ 1 = 0 := by
    dsimp [d0, d1, d2]; push_cast; linear_combination r0
  have h1eq : (d0 + Complex.I * d1) * φ 0 - d2 * φ 1 = 0 := by
    dsimp [d0, d1, d2]; push_cast; linear_combination r1
  have hsqC : d0 ^ 2 + d1 ^ 2 + d2 ^ 2 ≠ 0 := by
    have : d0 ^ 2 + d1 ^ 2 + d2 ^ 2 =
        (((u 0 - w 0) ^ 2 + (u 1 - w 1) ^ 2 + (u 2 - w 2) ^ 2 : ℝ) : ℂ) := by
      dsimp [d0, d1, d2]; push_cast; ring
    rw [this]
    exact Complex.ofReal_ne_zero.mpr hd_nz
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hf0 : (d0 ^ 2 + d1 ^ 2 + d2 ^ 2) * φ 0 = 0 := by
    linear_combination d2 * h0eq + (d0 - Complex.I * d1) * h1eq + d1 ^ 2 * φ 0 * hI
  have hf1 : (d0 ^ 2 + d1 ^ 2 + d2 ^ 2) * φ 1 = 0 := by
    linear_combination (d0 + Complex.I * d1) * h0eq - d2 * h1eq + d1 ^ 2 * φ 1 * hI
  have z0 : φ 0 = 0 := (mul_eq_zero.mp hf0).resolve_left hsqC
  have z1 : φ 1 = 0 := (mul_eq_zero.mp hf1).resolve_left hsqC
  rcases hφ_ne with h | h <;> contradiction

lemma isPosSpinor_ne_zero {v : Fin 3 → ℝ} {ψ : Fin 2 → ℂ} (h : IsPosSpinor v ψ) :
    ψ 0 ≠ 0 ∨ ψ 1 ≠ 0 := by
  by_contra hc
  push Not at hc
  have hn := h.1
  rw [hc.1, hc.2] at hn
  norm_num at hn

private def unitLtSumEquiv (n : ℕ) :
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

private def unitOffDiagEquiv (n : ℕ) :
    { p : Fin n × Fin n // p.1 ≠ p.2 } ≃ Σ i : Fin n, { j : Fin n // j ∈ Finset.univ.erase i } where
  toFun p := ⟨p.1.1, ⟨p.1.2, Finset.mem_erase.mpr ⟨p.2.symm, Finset.mem_univ _⟩⟩⟩
  invFun q := ⟨(q.1, q.2.1), (Finset.mem_erase.mp q.2.2).1.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma atiyahDen_unit_ne_zero {n : ℕ} {u : Fin n → Fin n → Fin 3 → ℝ}
    (_hu_norm : ∀ i j, i ≠ j → u i j 0 ^ 2 + u i j 1 ^ 2 + u i j 2 ^ 2 = 1)
    (hu_ne : ∀ i j, i ≠ j → u i j ≠ u j i)
    {ψ : Fin n → Fin n → Fin 2 → ℂ}
    (hψ_ne : ∀ i j, i ≠ j → ψ i j 0 ≠ 0 ∨ ψ i j 1 ≠ 0)
    (hψ_mul : ∀ i j, i ≠ j → (pauliDot (u i j)).mulVec (ψ i j) = ψ i j) :
    atiyahDen ψ ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun e _ => ?_
  exact omega_ne_zero_of_unit_ne (hu_ne e.1.1 e.1.2 (ne_of_lt e.2))
    (hψ_ne _ _ (ne_of_lt e.2)) (hψ_mul _ _ (ne_of_lt e.2))
    (hψ_ne _ _ (ne_of_gt e.2)) (hψ_mul _ _ (ne_of_gt e.2))

theorem atiyahDetOfSpinors_eq_of_unitSpinors {n : ℕ}
    (u : Fin n → Fin n → Fin 3 → ℝ)
    (hu_norm : ∀ i j, i ≠ j → u i j 0 ^ 2 + u i j 1 ^ 2 + u i j 2 ^ 2 = 1)
    (hu_ne : ∀ i j, i ≠ j → u i j ≠ u j i)
    (ψ : Fin n → Fin n → Fin 2 → ℂ)
    (hψ_ne : ∀ i j, i ≠ j → ψ i j 0 ≠ 0 ∨ ψ i j 1 ≠ 0)
    (hψ_mul : ∀ i j, i ≠ j → (pauliDot (u i j)).mulVec (ψ i j) = ψ i j) :
    atiyahDetOfSpinors (fun i j => canonicalSpinor (u i j)) = atiyahDetOfSpinors ψ := by
  let ψ0 := fun i j => canonicalSpinor (u i j)
  have hcol : ∀ i j, i ≠ j → ∃ c : ℂ, c ≠ 0 ∧ ∀ k, ψ i j k = c * ψ0 i j k := fun i j hij =>
    mulVec_eq_self_collinear (hu_norm i j hij) (hψ_ne i j hij) (hψ_mul i j hij)
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
          Fintype.prod_equiv (unitOffDiagEquiv n).symm _ _ fun _ => rfl
      _ = ∏ s : { p : Fin n × Fin n // p.1 < p.2 } ⊕ { p : Fin n × Fin n // p.1 < p.2 },
            cFull (unitLtSumEquiv n s).1.1 (unitLtSumEquiv n s).1.2 :=
          (Fintype.prod_equiv (unitLtSumEquiv n) _ _ fun _ => rfl).symm
      _ = (∏ e : { p : Fin n × Fin n // p.1 < p.2 }, cFull e.1.1 e.1.2) *
            (∏ e : { p : Fin n × Fin n // p.1 < p.2 }, cFull e.1.2 e.1.1) := by
          simp only [Fintype.prod_sum_type, unitLtSumEquiv]; rfl
      _ = ∏ e : { p : Fin n × Fin n // p.1 < p.2 }, cFull e.1.1 e.1.2 * cFull e.1.2 e.1.1 :=
          Finset.prod_mul_distrib.symm
  have hS_ne : (∏ e : { p : Fin n × Fin n // p.1 < p.2 }, cFull e.1.1 e.1.2 * cFull e.1.2 e.1.1) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun e _ =>
      mul_ne_zero (hcFull_ne _ _ (ne_of_lt e.2)) (hcFull_ne _ _ (ne_of_gt e.2))
  have hden0_ne : atiyahDen ψ0 ≠ 0 := by
    refine atiyahDen_unit_ne_zero hu_norm hu_ne ?_ ?_
    · intro i j hij; exact isPosSpinor_ne_zero (isPosSpinor_canonicalSpinor (hu_norm i j hij))
    · intro i j hij; exact (isPosSpinor_canonicalSpinor (hu_norm i j hij)).2
  change atiyahDetOfSpinors ψ0 = atiyahDetOfSpinors ψ
  simp only [atiyahDetOfSpinors, hdet, hden, hprod_eq]
  field_simp [hS_ne, hden0_ne]

lemma not_linearIndependent_of_atiyahDetOfSpinors_eq_zero {n : ℕ} (hn : 1 ≤ n)
    {ψ : Fin n → Fin n → Fin 2 → ℂ} (hden : atiyahDen ψ ≠ 0)
    (h0 : atiyahDetOfSpinors ψ = 0) :
    ¬ LinearIndependent ℂ (fun i : Fin n => atiyahPoly ψ i) := by
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
      change w i * (atiyahPoly ψ i).coeff k = (atiyahMat ψ i ⟨k, hk⟩) * w i
      simp only [atiyahMat]; ring
    · have hdeg : ∀ i : Fin n, (atiyahPoly ψ i).natDegree ≤ n - 1 := by
        intro i
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
      refine Finset.sum_eq_zero fun i _ => ?_
      have hgt : (atiyahPoly ψ i).natDegree < k := lt_of_le_of_lt (hdeg i) (by omega)
      simp [Polynomial.coeff_eq_zero_of_natDegree_lt hgt]
  exact hw_ne (funext fun i => by
    have hfi := DFunLike.congr_fun ((linearIndependent_iff.mp hlin)
      (Finsupp.onFinset Finset.univ w fun _ _ => Finset.mem_univ _)
      (by simpa [Finsupp.linearCombination_apply] using hsum)) i
    simpa using hfi)

/-- Continuous chart-local polynomial spinor lift (free of `Real.sqrt`) centered near `v₀`. -/
noncomputable def chartSpinor (v₀ w : Fin 3 → ℝ) (k : Fin 2) : ℂ :=
  if 0 ≤ v₀ 2 then
    if k = 0 then ((1 + w 2 : ℝ) : ℂ) else (w 0 : ℂ) + Complex.I * (w 1 : ℂ)
  else
    if k = 0 then (w 0 : ℂ) - Complex.I * (w 1 : ℂ) else ((1 - w 2 : ℝ) : ℂ)

lemma pauliDot_chartSpinor {v₀ w : Fin 3 → ℝ} (hw : w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 = 1) :
    (pauliDot w).mulVec (chartSpinor v₀ w) = chartSpinor v₀ w := by
  ext k
  unfold chartSpinor
  fin_cases k <;> by_cases h0 : 0 ≤ v₀ 2 <;>
    simp only [h0, ↓reduceIte, Matrix.mulVec, dotProduct, Fin.sum_univ_two, pauliDot,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.isValue, Fin.reduceFinMk] <;>
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> nlinarith

lemma chartSpinor_ne_zero {v₀ w : Fin 3 → ℝ}
    (h : (0 ≤ v₀ 2 ∧ -(1 / 2 : ℝ) < w 2) ∨ (v₀ 2 < 0 ∧ w 2 < (1 / 2 : ℝ))) :
    chartSpinor v₀ w 0 ≠ 0 ∨ chartSpinor v₀ w 1 ≠ 0 := by
  unfold chartSpinor
  rcases h with ⟨h0, hw⟩ | ⟨h0, hw⟩
  · left
    simp only [h0, ↓reduceIte]
    exact Complex.ofReal_ne_zero.mpr (by linarith)
  · right
    have hnot : ¬ 0 ≤ v₀ 2 := not_le.mpr h0
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    simp only [hnot, h10, ↓reduceIte]
    exact Complex.ofReal_ne_zero.mpr (by linarith)

lemma continuous_chartSpinor (v₀ : Fin 3 → ℝ) (k : Fin 2) :
    Continuous (fun w : Fin 3 → ℝ => chartSpinor v₀ w k) := by
  unfold chartSpinor
  by_cases h0 : 0 ≤ v₀ 2 <;> simp only [h0, ↓reduceIte]
  · fin_cases k
    · exact Complex.continuous_ofReal.comp (continuous_const.add (continuous_apply 2))
    · exact (Complex.continuous_ofReal.comp (continuous_apply 0)).add
        (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply 1)))
  · fin_cases k
    · exact (Complex.continuous_ofReal.comp (continuous_apply 0)).sub
        (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply 1)))
    · exact Complex.continuous_ofReal.comp (continuous_const.sub (continuous_apply 2))

lemma continuous_atiyahMat_of_continuous {α : Type*} [TopologicalSpace α] {n : ℕ}
    (ψ : α → Fin n → Fin n → Fin 2 → ℂ)
    (hψ : ∀ i j k, Continuous (fun p => ψ p i j k)) (i k : Fin n) :
    Continuous (fun p => atiyahMat (ψ p) i k) := by
  have hpoly : ∀ (s : Finset (Fin n)) (m : ℕ),
      Continuous (fun p => (∏ j ∈ s, (Polynomial.C (ψ p i j 0) + Polynomial.C (ψ p i j 1) * Polynomial.X)).coeff m) := by
    intro s
    induction s using Finset.induction with
    | empty =>
      intro m
      simpa using (continuous_const : Continuous (fun _ : α => ((1 : Polynomial ℂ).coeff m)))
    | @insert a s has ih =>
      intro m
      have heq : ∀ p, (∏ j ∈ insert a s, (Polynomial.C (ψ p i j 0) + Polynomial.C (ψ p i j 1) * Polynomial.X)).coeff m =
          ψ p i a 0 * (∏ j ∈ s, (Polynomial.C (ψ p i j 0) + Polynomial.C (ψ p i j 1) * Polynomial.X)).coeff m +
            (if m = 0 then 0 else
              ψ p i a 1 * (∏ j ∈ s, (Polynomial.C (ψ p i j 0) + Polynomial.C (ψ p i j 1) * Polynomial.X)).coeff (m - 1)) := by
        intro p
        rw [Finset.prod_insert has, add_mul, Polynomial.coeff_add, Polynomial.coeff_C_mul]
        congr 1
        cases m with
        | zero => simp [mul_assoc]
        | succ m' =>
          simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
            Nat.add_sub_cancel]
          rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul]
      simp_rw [heq]
      refine ((hψ i a 0).mul (ih m)).add ?_
      split_ifs
      · exact continuous_const
      · exact (hψ i a 1).mul (ih (m - 1))
  exact hpoly (Finset.univ.erase i) k.1

lemma continuous_atiyahDen_of_continuous {α : Type*} [TopologicalSpace α] {n : ℕ}
    (ψ : α → Fin n → Fin n → Fin 2 → ℂ)
    (hψ : ∀ i j k, Continuous (fun p => ψ p i j k)) :
    Continuous (fun p => atiyahDen (ψ p)) := by
  have hterm : ∀ e : { p : Fin n × Fin n // p.1 < p.2 },
      Continuous (fun p => omega (ψ p e.1.1 e.1.2) (ψ p e.1.2 e.1.1)) := fun e =>
    ((hψ e.1.1 e.1.2 0).mul (hψ e.1.2 e.1.1 1)).sub
      ((hψ e.1.1 e.1.2 1).mul (hψ e.1.2 e.1.1 0))
  have hprod : ∀ s : Finset { p : Fin n × Fin n // p.1 < p.2 },
      Continuous (fun p => ∏ e ∈ s, omega (ψ p e.1.1 e.1.2) (ψ p e.1.2 e.1.1)) := by
    intro s
    induction s using Finset.induction with
    | empty => simpa using (continuous_const : Continuous (fun _ : α => (1 : ℂ)))
    | @insert a s has ih =>
      have heq : (fun p => ∏ e ∈ insert a s, omega (ψ p e.1.1 e.1.2) (ψ p e.1.2 e.1.1)) =
          fun p => omega (ψ p a.1.1 a.1.2) (ψ p a.1.2 a.1.1) *
            ∏ e ∈ s, omega (ψ p e.1.1 e.1.2) (ψ p e.1.2 e.1.1) := by
        funext p; exact Finset.prod_insert has
      rw [heq]
      exact (hterm a).mul ih
  exact hprod Finset.univ

theorem tendsto_atiyahDetOfSpinors_unit {α : Type*} [TopologicalSpace α] {n : ℕ}
    {l : Filter α} (u : α → Fin n → Fin n → Fin 3 → ℝ) (u₀ : Fin n → Fin n → Fin 3 → ℝ)
    (hu₀_norm : ∀ i j, i ≠ j → u₀ i j 0 ^ 2 + u₀ i j 1 ^ 2 + u₀ i j 2 ^ 2 = 1)
    (hu₀_ne : ∀ i j, i ≠ j → u₀ i j ≠ u₀ j i)
    (hu_norm : ∀ᶠ p in l, ∀ i j, i ≠ j → u p i j 0 ^ 2 + u p i j 1 ^ 2 + u p i j 2 ^ 2 = 1)
    (hu_ne : ∀ᶠ p in l, ∀ i j, i ≠ j → u p i j ≠ u p j i)
    (htend : ∀ i j, i ≠ j → Tendsto (fun p => u p i j) l (nhds (u₀ i j))) :
    Tendsto (fun p => atiyahDetOfSpinors (fun i j => canonicalSpinor (u p i j))) l
      (nhds (atiyahDetOfSpinors (fun i j => canonicalSpinor (u₀ i j)))) := by
  let ψMap : (Fin n → Fin n → Fin 3 → ℝ) → Fin n → Fin n → Fin 2 → ℂ :=
    fun v i j => chartSpinor (u₀ i j) (v i j)
  let cleanU : (Fin n → Fin n → Fin 3 → ℝ) → Fin n → Fin n → Fin 3 → ℝ :=
    fun v i j => if i = j then 0 else v i j
  let g : α → Fin n → Fin n → Fin 3 → ℝ := fun p => cleanU (u p)
  let g₀ : Fin n → Fin n → Fin 3 → ℝ := cleanU u₀
  have hg_tend : Tendsto g l (nhds g₀) := by
    rw [tendsto_pi_nhds]; intro i
    rw [tendsto_pi_nhds]; intro j
    by_cases hij : i = j
    · simp only [g, g₀, cleanU, hij, ↓reduceIte, tendsto_const_nhds]
    · simp only [g, g₀, cleanU, hij, ↓reduceIte]
      exact htend i j hij
  have hchart_pair : ∀ i j, i ≠ j →
      ∀ᶠ p in l, chartSpinor (u₀ i j) (u p i j) 0 ≠ 0 ∨ chartSpinor (u₀ i j) (u p i j) 1 ≠ 0 := by
    intro i j hij
    have ht2 := (continuous_apply 2).continuousAt.tendsto.comp (htend i j hij)
    by_cases h0 : 0 ≤ u₀ i j 2
    · exact (ht2.eventually (Ioi_mem_nhds (by linarith))).mono fun p hp => chartSpinor_ne_zero (Or.inl ⟨h0, hp⟩)
    · have hlt0 : u₀ i j 2 < 0 := lt_of_not_ge h0
      exact (ht2.eventually (Iio_mem_nhds (by linarith))).mono fun p hp => chartSpinor_ne_zero (Or.inr ⟨hlt0, hp⟩)
  have hchart_all : ∀ᶠ p in l, ∀ i j, i ≠ j →
      chartSpinor (u₀ i j) (g p i j) 0 ≠ 0 ∨ chartSpinor (u₀ i j) (g p i j) 1 ≠ 0 := by
    have hfin : ∀ᶠ p in l, ∀ q : Fin n × Fin n, q.1 ≠ q.2 →
        chartSpinor (u₀ q.1 q.2) (u p q.1 q.2) 0 ≠ 0 ∨ chartSpinor (u₀ q.1 q.2) (u p q.1 q.2) 1 ≠ 0 := by
      refine Filter.eventually_all.mpr fun q => ?_
      by_cases hq : q.1 ≠ q.2
      · exact (hchart_pair q.1 q.2 hq).mono fun _ h _ => h
      · exact Eventually.of_forall fun _ h => absurd h hq
    exact hfin.mono fun p hp i j hij => by simpa [g, cleanU, hij] using hp (i, j) hij
  have heq : ∀ᶠ p in l,
      atiyahDetOfSpinors (fun i j => canonicalSpinor (u p i j)) = atiyahDetOfSpinors (ψMap (g p)) := by
    filter_upwards [hu_norm, hu_ne, hchart_all] with p hn hne hc
    exact atiyahDetOfSpinors_eq_of_unitSpinors (u p) hn hne (ψMap (g p)) hc
      fun i j hij => by simpa [ψMap, g, cleanU, hij] using pauliDot_chartSpinor (hn i j hij)
  have heq0 :
      atiyahDetOfSpinors (fun i j => canonicalSpinor (u₀ i j)) = atiyahDetOfSpinors (ψMap g₀) := by
    refine atiyahDetOfSpinors_eq_of_unitSpinors u₀ hu₀_norm hu₀_ne (ψMap g₀) ?_ ?_
    · intro i j hij
      dsimp only [ψMap, g₀, cleanU]; simp only [hij, ↓reduceIte]
      by_cases h0 : 0 ≤ u₀ i j 2
      · exact chartSpinor_ne_zero (Or.inl ⟨h0, by linarith⟩)
      · exact chartSpinor_ne_zero (Or.inr ⟨lt_of_not_ge h0, by linarith⟩)
    · intro i j hij
      simpa [ψMap, g₀, cleanU, hij] using pauliDot_chartSpinor (hu₀_norm i j hij)
  have hψ_cont : ∀ i j k, Continuous (fun v : Fin n → Fin n → Fin 3 → ℝ => ψMap v i j k) := fun i j k =>
    (continuous_chartSpinor (u₀ i j) k).comp ((continuous_apply j).comp (continuous_apply i))
  have hdet_cont : Continuous (fun v => (atiyahMat (ψMap v)).det) :=
    Continuous.matrix_det (continuous_pi fun i => continuous_pi fun k =>
      continuous_atiyahMat_of_continuous ψMap hψ_cont i k)
  have hden_cont : Continuous (fun v => atiyahDen (ψMap v)) :=
    continuous_atiyahDen_of_continuous ψMap hψ_cont
  have hden₀_ne : atiyahDen (ψMap g₀) ≠ 0 := by
    refine atiyahDen_unit_ne_zero hu₀_norm hu₀_ne ?_ ?_
    · intro i j hij
      dsimp only [ψMap, g₀, cleanU]; simp only [hij, ↓reduceIte]
      by_cases h0 : 0 ≤ u₀ i j 2
      · exact chartSpinor_ne_zero (Or.inl ⟨h0, by linarith⟩)
      · exact chartSpinor_ne_zero (Or.inr ⟨lt_of_not_ge h0, by linarith⟩)
    · intro i j hij
      simpa [ψMap, g₀, cleanU, hij] using pauliDot_chartSpinor (hu₀_norm i j hij)
  have hquot : Tendsto (fun p => atiyahDetOfSpinors (ψMap (g p))) l (nhds (atiyahDetOfSpinors (ψMap g₀))) := by
    change Tendsto (fun p => (atiyahMat (ψMap (g p))).det / atiyahDen (ψMap (g p))) l
      (nhds ((atiyahMat (ψMap g₀)).det / atiyahDen (ψMap g₀)))
    exact ((hdet_cont.continuousAt.div hden_cont.continuousAt hden₀_ne).tendsto).comp hg_tend
  rw [heq0]
  exact hquot.congr' (heq.mono fun p hp => hp.symm)

lemma unitDir_ne_swap {a b : Fin 3 → ℝ} (h : a ≠ b) : unitDir a b ≠ unitDir b a := by
  intro heq
  have hsq := unitDir_norm_sq h
  have hzero : ∀ k, unitDir a b k = 0 := fun k => by
    have hk1 : unitDir a b k = unitDir b a k := congr_fun heq k
    have hk2 : unitDir b a k = -unitDir a b k := congr_fun (unitDir_swap a b) k
    linarith
  rw [hzero 0, hzero 1, hzero 2] at hsq
  norm_num at hsq

theorem tendsto_atiyahDet_of_tendsto {α : Type*} [TopologicalSpace α] {n : ℕ}
    {l : Filter α} (x : α → DistinctPoints n) (x₀ : DistinctPoints n)
    (htend : ∀ i : Fin n, Tendsto (fun p => (x p).1 i) l (nhds (x₀.1 i))) :
    Tendsto (fun p => atiyahDet (x p)) l (nhds (atiyahDet x₀)) := by
  refine tendsto_atiyahDetOfSpinors_unit (fun p i j => unitDir ((x p).1 i) ((x p).1 j))
    (fun i j => unitDir (x₀.1 i) (x₀.1 j))
    (fun i j hij => unitDir_norm_sq (x₀.2 i j hij))
    (fun i j hij => unitDir_ne_swap (x₀.2 i j hij))
    (Eventually.of_forall fun p i j hij => unitDir_norm_sq ((x p).2 i j hij))
    (Eventually.of_forall fun p i j hij => unitDir_ne_swap ((x p).2 i j hij)) ?_
  intro i j hij
  rw [tendsto_pi_nhds]; intro k
  have hsub : ∀ m, Tendsto (fun p => (x p).1 j m - (x p).1 i m) l (nhds (x₀.1 j m - x₀.1 i m)) := fun m =>
    ((continuous_apply m).continuousAt.tendsto.comp (htend j)).sub
      ((continuous_apply m).continuousAt.tendsto.comp (htend i))
  have hnorm_tend : Tendsto (fun p => euclidNorm (fun m => (x p).1 j m - (x p).1 i m)) l
      (nhds (euclidNorm (fun m => x₀.1 j m - x₀.1 i m))) := by
    unfold euclidNorm
    exact (((hsub 0).pow 2).add ((hsub 1).pow 2) |>.add ((hsub 2).pow 2)).sqrt
  exact (hsub k).div hnorm_tend (euclidNorm_pos_of_ne (x₀.2 i j hij)).ne'

end UnitSpinorContinuity

/-! ## Part B: Kernel Division `FpIv.divFp`, Gaussian Elimination `gaussDetIv`, Planar $n = 57$ Record & Direct `n = 63` Norm -/

namespace FpIv

def zmin4 (a b c d : ℤ) : ℤ := min (min a b) (min c d)
def zmax4 (a b c d : ℤ) : ℤ := max (max a b) (max c d)

/-- Outward-rounded fixed-point division `a / b` when `0 < b.lo`. -/
def divFpPos (S : ℤ) (a b : FpIv) : FpIv :=
  let n1 := S * a.lo
  let n2 := S * a.hi
  let d1 := b.lo
  let d2 := b.hi
  ⟨zmin4 (n1 / d1) (n1 / d2) (n2 / d1) (n2 / d2),
   zmax4 ((n1 + d1 - 1) / d1) ((n1 + d2 - 1) / d2)
     ((n2 + d1 - 1) / d1) ((n2 + d2 - 1) / d2)⟩

/-- General outward-rounded fixed-point division `a / b` for intervals separated from `0`. -/
def divFp (S : ℤ) (a b : FpIv) : FpIv :=
  if 0 < b.lo then divFpPos S a b else divFpPos S (neg a) (neg b)

private lemma real_ediv_floor_le (n d : ℤ) (hd : 0 < d) :
    ((n / d : ℤ) : ℝ) ≤ (n : ℝ) / (d : ℝ) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hid : ((d * (n / d) : ℤ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast ediv_floor_mul_le d n hd
  rw [Int.cast_mul] at hid
  exact (le_div_iff₀ hdR).mpr (by linarith)

private lemma real_le_ediv_ceil (n d : ℤ) (hd : 0 < d) :
    (n : ℝ) / (d : ℝ) ≤ (((n + d - 1) / d : ℤ) : ℝ) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hid : (n : ℝ) ≤ ((d * ((n + d - 1) / d) : ℤ) : ℝ) := by
    exact_mod_cast le_ediv_ceil_mul d n hd
  rw [Int.cast_mul] at hid
  exact (div_le_iff₀ hdR).mpr (by linarith)

private lemma div_bounds_of_pos {u v l1 h1 l2 h2 : ℝ}
    (hu : l1 ≤ u ∧ u ≤ h1) (hl2 : 0 < l2) (hv : l2 ≤ v ∧ v ≤ h2) :
    min (min (l1 / l2) (l1 / h2)) (min (h1 / l2) (h1 / h2)) ≤ u / v ∧
    u / v ≤ max (max (l1 / l2) (l1 / h2)) (max (h1 / l2) (h1 / h2)) := by
  have hvpos : 0 < v := lt_of_lt_of_le hl2 hv.1
  have hh2pos : 0 < h2 := lt_of_lt_of_le hvpos hv.2
  have hinv_lo : h2⁻¹ ≤ v⁻¹ := inv_anti₀ hvpos hv.2
  have hinv_hi : v⁻¹ ≤ l2⁻¹ := inv_anti₀ hl2 hv.1
  have hinv_nn : 0 ≤ v⁻¹ := inv_nonneg.mpr hvpos.le
  have hu1 : l1 / v ≤ u / v := by simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hu.1 hinv_nn
  have hu2 : u / v ≤ h1 / v := by simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hu.2 hinv_nn
  have hbnd : ∀ c : ℝ, min (c / l2) (c / h2) ≤ c / v ∧ c / v ≤ max (c / l2) (c / h2) := by
    intro c
    rcases le_total 0 c with hc | hc
    · have hlo : c / h2 ≤ c / v := by simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinv_lo hc
      have hhi : c / v ≤ c / l2 := by simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinv_hi hc
      exact ⟨le_trans (min_le_right _ _) hlo, le_trans hhi (le_max_left _ _)⟩
    · have hlo : c / l2 ≤ c / v := by simpa only [div_eq_mul_inv] using mul_le_mul_of_nonpos_left hinv_hi hc
      have hhi : c / v ≤ c / h2 := by simpa only [div_eq_mul_inv] using mul_le_mul_of_nonpos_left hinv_lo hc
      exact ⟨le_trans (min_le_left _ _) hlo, le_trans hhi (le_max_right _ _)⟩
  refine ⟨?_, ?_⟩
  · exact le_trans (min_le_left _ _) (le_trans (hbnd l1).1 hu1)
  · exact le_trans hu2 (le_trans (hbnd h1).2 (le_max_right _ _))

lemma divFpPos_mem {S : ℤ} (hS : 0 < S) {a b : FpIv} {x y : ℝ}
    (hb_pos : 0 < b.lo) (ha : FpMem S a x) (hb : FpMem S b y) :
    FpMem S (divFpPos S a b) (x / y) := by
  have hd1 : 0 < b.lo := hb_pos
  have hd2R : (b.lo : ℝ) ≤ (b.hi : ℝ) := by linarith [hb.1, hb.2]
  have hd2 : 0 < b.hi := Int.cast_pos.mp (lt_of_lt_of_le (Int.cast_pos.mpr hd1) hd2R)
  have hSR : (0 : ℝ) < (S : ℝ) := by exact_mod_cast hS
  have hy_pos : 0 < (S : ℝ) * y := lt_of_lt_of_le (by exact_mod_cast hd1) hb.1
  have hu : ((S * a.lo : ℤ) : ℝ) ≤ (S : ℝ) * ((S : ℝ) * x) ∧
      (S : ℝ) * ((S : ℝ) * x) ≤ ((S * a.hi : ℤ) : ℝ) := by
    rw [Int.cast_mul, Int.cast_mul]
    exact ⟨mul_le_mul_of_nonneg_left ha.1 hSR.le, mul_le_mul_of_nonneg_left ha.2 hSR.le⟩
  have hdiv := div_bounds_of_pos hu (by exact_mod_cast hd1 : (0 : ℝ) < b.lo) hb
  have hscaled : (S : ℝ) * (x / y) = ((S : ℝ) * ((S : ℝ) * x)) / ((S : ℝ) * y) := by
    have hy0 : y ≠ 0 := fun hyz => by rw [hyz, mul_zero] at hy_pos; exact lt_irrefl _ hy_pos
    field_simp [hSR.ne', hy0]
  rw [FpMem, hscaled]
  refine ⟨?_, ?_⟩
  · dsimp only [divFpPos, zmin4]
    have hle : (((min (min (S * a.lo / b.lo) (S * a.lo / b.hi))
        (min (S * a.hi / b.lo) (S * a.hi / b.hi)) : ℤ) : ℝ)) ≤
        min (min ((S * a.lo : ℤ) / (b.lo : ℝ)) ((S * a.lo : ℤ) / (b.hi : ℝ)))
            (min ((S * a.hi : ℤ) / (b.lo : ℝ)) ((S * a.hi : ℤ) / (b.hi : ℝ))) := by
      simp only [Int.cast_min]
      exact min_le_min (min_le_min (real_ediv_floor_le _ _ hd1) (real_ediv_floor_le _ _ hd2))
        (min_le_min (real_ediv_floor_le _ _ hd1) (real_ediv_floor_le _ _ hd2))
    exact le_trans hle hdiv.1
  · dsimp only [divFpPos, zmax4]
    have hge : max (max ((S * a.lo : ℤ) / (b.lo : ℝ)) ((S * a.lo : ℤ) / (b.hi : ℝ)))
        (max ((S * a.hi : ℤ) / (b.lo : ℝ)) ((S * a.hi : ℤ) / (b.hi : ℝ))) ≤
        (((max (max ((S * a.lo + b.lo - 1) / b.lo) ((S * a.lo + b.hi - 1) / b.hi))
               (max ((S * a.hi + b.lo - 1) / b.lo) ((S * a.hi + b.hi - 1) / b.hi)) : ℤ) : ℝ)) := by
      simp only [Int.cast_max]
      exact max_le_max (max_le_max (real_le_ediv_ceil _ _ hd1) (real_le_ediv_ceil _ _ hd2))
        (max_le_max (real_le_ediv_ceil _ _ hd1) (real_le_ediv_ceil _ _ hd2))
    exact le_trans hdiv.2 hge

lemma divFp_mem {S : ℤ} (hS : 0 < S) {a b : FpIv} {x y : ℝ}
    (hsep : 0 < b.lo ∨ b.hi < 0) (ha : FpMem S a x) (hb : FpMem S b y) :
    FpMem S (divFp S a b) (x / y) := by
  by_cases hpos : 0 < b.lo
  · simp only [divFp, hpos, ↓reduceIte]
    exact divFpPos_mem hS hpos ha hb
  · have hneg : b.hi < 0 := hsep.resolve_left hpos
    simp only [divFp, hpos, ↓reduceIte]
    have heq : x / y = (-x) / (-y) := by ring
    rw [heq]
    exact divFpPos_mem hS (show 0 < (neg b).lo by simp [neg]; omega) (neg_mem ha) (neg_mem hb)

end FpIv

section KernelGaussDet

/-- Real Schur-complement submatrix after eliminating column `0` using pivot `A 0 0`. -/
noncomputable def elimSubMatrix {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  fun i j => A i.succ j.succ + (-(A i.succ 0) / A 0 0) * A 0 j.succ

lemma det_eq_head_mul_det_elimSubMatrix {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (h0 : A 0 0 ≠ 0) :
    A.det = A 0 0 * (elimSubMatrix A).det := by
  let clearUpTo : ℕ → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ := fun k r c =>
    if r = 0 then A 0 c
    else if r.1 ≤ k then A r c + (-(A r 0) / A 0 0) * A 0 c
    else A r c
  have hdet_clear : ∀ k : ℕ, (clearUpTo k).det = A.det := by
    intro k
    induction k with
    | zero =>
      have h0eq : clearUpTo 0 = A := by
        ext r c
        by_cases hr : r = 0
        · subst hr; simp [clearUpTo]
        · have hr1 : ¬ r.1 ≤ 0 := by
            intro hle
            exact hr (Fin.ext (Nat.le_zero.mp hle))
          simp [clearUpTo, hr, hr1]
      rw [h0eq]
    | succ k ih =>
      by_cases hk : k + 1 ≤ m
      · let r0 : Fin (m + 1) := ⟨k + 1, by omega⟩
        have hr0_ne : r0 ≠ 0 := by intro h; have := congr_arg Fin.val h; dsimp [r0] at this; omega
        let c : ℝ := -(A r0 0) / A 0 0
        have hupd : (clearUpTo k).updateRow r0 (clearUpTo k r0 + c • clearUpTo k 0) =
            clearUpTo (k + 1) := by
          ext r col
          by_cases hr : r = r0
          · subst hr
            have hnot : ¬ r0.1 ≤ k := by dsimp [r0]; omega
            have hle : r0.1 ≤ k + 1 := by dsimp [r0]; omega
            rw [congr_fun (Matrix.updateRow_self (M := clearUpTo k) (i := r0)
              (b := clearUpTo k r0 + c • clearUpTo k 0)) col]
            simp [clearUpTo, hr0_ne, hnot, hle, c]
          · rw [congr_fun (Matrix.updateRow_ne (M := clearUpTo k)
              (b := clearUpTo k r0 + c • clearUpTo k 0) hr) col]
            by_cases hrz : r = 0
            · simp [clearUpTo, hrz]
            · have hne1 : r.1 ≠ k + 1 := fun he => hr (Fin.ext he)
              have hiff : r.1 ≤ k + 1 ↔ r.1 ≤ k := by omega
              simp [clearUpTo, hrz, hiff]
        rw [← ih, ← hupd, Matrix.det_updateRow_add_smul_self _ hr0_ne]
      · have heq : clearUpTo (k + 1) = clearUpTo k := by
          ext r c
          by_cases hr : r = 0
          · simp [clearUpTo, hr]
          · have hlt : r.1 ≤ m := Nat.lt_succ_iff.mp r.2
            have hiff : r.1 ≤ k + 1 ↔ r.1 ≤ k := by omega
            simp [clearUpTo, hr, hiff]
        rw [heq, ih]
  let B := clearUpTo m
  have hBdet : B.det = A.det := hdet_clear m
  have hB0 : B 0 0 = A 0 0 := by simp [B, clearUpTo]
  have hBcol : ∀ i : Fin m, B i.succ 0 = 0 := by
    intro i
    have hne : i.succ ≠ 0 := Fin.succ_ne_zero i
    have hle : i.succ.1 ≤ m := Nat.lt_succ_iff.mp i.succ.2
    simp only [B, clearUpTo, hne, hle, ↓reduceIte]
    field_simp [h0]
    ring
  have hBsub : B.submatrix Fin.succ Fin.succ = elimSubMatrix A := by
    ext i j
    have hne : i.succ ≠ 0 := Fin.succ_ne_zero i
    have hle : i.succ.1 ≤ m := Nat.lt_succ_iff.mp i.succ.2
    change B i.succ j.succ = elimSubMatrix A i j
    simp only [B, clearUpTo, elimSubMatrix, hne, hle, ↓reduceIte]
  rw [← hBdet, Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have htail : (∑ i : Fin m, (-1 : ℝ) ^ (i.succ : ℕ) * B i.succ 0 *
      (B.submatrix i.succ.succAbove Fin.succ).det) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    simp [hBcol i]
  rw [htail, add_zero, Fin.val_zero, pow_zero, one_mul, hB0, Fin.succAbove_zero, hBsub]

/-- Row-wise fixed-point enclosure for fixed length `m`. -/
def RowFpMem (S : ℤ) (m : ℕ) (row : List FpIv) (v : Fin m → ℝ) : Prop :=
  row.length = m ∧ ∀ j : Fin m, FpIv.FpMem S (row.getD j.1 FpIv.zero) (v j)

/-- Matrix fixed-point enclosure for fixed dimension `m × m`. -/
def MatFpMem (S : ℤ) (m : ℕ) (rows : List (List FpIv)) (A : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  rows.length = m ∧ ∀ i : Fin m, RowFpMem S m (rows.getD i.1 []) (A i)

def isZeroIv (a : FpIv) : Bool := (a.lo == 0) && (a.hi == 0)

def isSepZeroIv (a : FpIv) : Bool := decide (0 < a.lo ∨ a.hi < 0)

lemma eq_zero_of_isZeroIv {S : ℤ} (hS : 0 < S) {iv : FpIv} {x : ℝ}
    (hz : isZeroIv iv = true) (hx : FpIv.FpMem S iv x) : x = 0 := by
  cases iv with
  | mk lo hi =>
    simp only [isZeroIv, Bool.and_eq_true, beq_iff_eq] at hz
    rcases hz with ⟨rfl, rfl⟩
    exact fpMem_zero_eq_zero hS hx

lemma sepZero_of_isSepZeroIv {iv : FpIv} (hsep : isSepZeroIv iv = true) :
    0 < iv.lo ∨ iv.hi < 0 :=
  of_decide_eq_true hsep

lemma ne_zero_of_sepZero {S : ℤ} {iv : FpIv} {x : ℝ}
    (hsep : 0 < iv.lo ∨ iv.hi < 0) (hx : FpIv.FpMem S iv x) : x ≠ 0 := by
  intro hx0
  simp only [FpIv.FpMem, hx0, mul_zero] at hx
  rcases hsep with hlo | hhi
  · have : (0 : ℝ) < iv.lo := Int.cast_pos.mpr hlo; linarith [hx.1]
  · have : (iv.hi : ℝ) < 0 := Int.cast_lt_zero.mpr hhi; linarith [hx.2]

def zipElimIv (S : ℤ) (mult : FpIv) : List FpIv → List FpIv → List FpIv
  | r :: rs, p :: ps =>
    (if isZeroIv p then r else FpIv.add r (FpIv.mulFp S mult p)) :: zipElimIv S mult rs ps
  | _, _ => []

def elimRowsIv (S : ℤ) (piv : FpIv) (ptail : List FpIv) : List (List FpIv) → List (List FpIv)
  | [] => []
  | row :: rows =>
    let rhead := row.headD FpIv.zero
    let rtail := row.tail
    (if isZeroIv rhead then rtail else zipElimIv S (FpIv.divFp S (FpIv.neg rhead) piv) rtail ptail) ::
      elimRowsIv S piv ptail rows

/-- Certified Gaussian elimination without row pivoting, returning `(ok, ∏ pivots)`. -/
def gaussDetIv (S : ℤ) : ℕ → List (List FpIv) → FpIv → Bool × FpIv
  | 0, _, prod => (true, prod)
  | m + 1, pRow :: rest, prod =>
    let piv := pRow.headD FpIv.zero
    if isSepZeroIv piv then
      gaussDetIv S m (elimRowsIv S piv pRow.tail rest) (FpIv.mulFp S prod piv)
    else (false, prod)
  | _ + 1, [], prod => (false, prod)

private lemma rowFpMem_tail {S : ℤ} {m : ℕ} {row : List FpIv} {v : Fin (m + 1) → ℝ}
    (h : RowFpMem S (m + 1) row v) :
    RowFpMem S m row.tail (fun j => v j.succ) := by
  rcases h with ⟨hlen, hmem⟩
  cases row with
  | nil => simp at hlen
  | cons x xs =>
    refine ⟨by simp at hlen ⊢; exact hlen, fun j => ?_⟩
    simpa [List.tail_cons, List.getD_cons_succ] using hmem j.succ

private lemma rowFpMem_zipElimIv {S : ℤ} (hS : 0 < S) {m : ℕ}
    {rs ps : List FpIv} {vr vp : Fin m → ℝ} {mult : FpIv} {c : ℝ}
    (hrs : RowFpMem S m rs vr) (hps : RowFpMem S m ps vp) (hmult : FpIv.FpMem S mult c) :
    RowFpMem S m (zipElimIv S mult rs ps) (fun j => vr j + c * vp j) := by
  induction m generalizing rs ps with
  | zero =>
    rcases hrs with ⟨hrlen, _⟩
    rcases hps with ⟨hplen, _⟩
    cases rs <;> cases ps <;> simp at hrlen hplen
    exact ⟨rfl, fun j => j.elim0⟩
  | succ m ih =>
    rcases hrs with ⟨hrlen, hrmem⟩
    rcases hps with ⟨hplen, hpmem⟩
    cases rs with
    | nil => simp at hrlen
    | cons r rs =>
      cases ps with
      | nil => simp at hplen
      | cons p ps =>
        have ih_res := ih (vr := fun j => vr j.succ) (vp := fun j => vp j.succ)
          ⟨by simp at hrlen; exact hrlen, fun j => by simpa [List.getD_cons_succ] using hrmem j.succ⟩
          ⟨by simp at hplen; exact hplen, fun j => by simpa [List.getD_cons_succ] using hpmem j.succ⟩
        refine ⟨by simp [zipElimIv, ih_res.1], fun j => ?_⟩
        refine Fin.cases ?_ (fun k => ?_) j
        · simp only [Fin.val_zero, zipElimIv, List.getD_cons_zero]
          by_cases hzp : isZeroIv p = true
          · have hp0 : vp 0 = 0 := eq_zero_of_isZeroIv hS hzp (by simpa using hpmem 0)
            simp only [hzp, ↓reduceIte, hp0, mul_zero, add_zero]
            simpa using hrmem 0
          · simp only [hzp, Bool.false_eq_true, ↓reduceIte]
            exact FpIv.add_mem (by simpa using hrmem 0)
              (FpIv.mulFp_mem hS hmult (by simpa using hpmem 0))
        · simpa [zipElimIv, List.getD_cons_succ] using ih_res.2 k

private lemma elimRowsIv_length (S : ℤ) (piv : FpIv) (ptail : List FpIv)
    (rows : List (List FpIv)) :
    (elimRowsIv S piv ptail rows).length = rows.length := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simp [elimRowsIv, ih]

private lemma elimRowsIv_getD {S : ℤ} {piv : FpIv} {ptail : List FpIv}
    {rows : List (List FpIv)} {k : ℕ} (hk : k < rows.length) :
    (elimRowsIv S piv ptail rows).getD k [] =
      let row := rows.getD k []
      let rhead := row.headD FpIv.zero
      let rtail := row.tail
      if isZeroIv rhead then rtail
      else zipElimIv S (FpIv.divFp S (FpIv.neg rhead) piv) rtail ptail := by
  induction rows generalizing k with
  | nil => simp at hk
  | cons row rows ih =>
    cases k with
    | zero => simp [elimRowsIv]
    | succ k =>
      simp only [List.length_cons, Nat.succ_lt_succ_iff] at hk
      simpa [elimRowsIv, List.getD_cons_succ] using ih hk

lemma matFpMem_elimSubMatrix {S : ℤ} (hS : 0 < S) {m : ℕ}
    {pRow : List FpIv} {rest : List (List FpIv)} {A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (hmat : MatFpMem S (m + 1) (pRow :: rest) A)
    (hpiv_sep : isSepZeroIv (pRow.headD FpIv.zero) = true) :
    MatFpMem S m (elimRowsIv S (pRow.headD FpIv.zero) pRow.tail rest) (elimSubMatrix A) := by
  rcases hmat with ⟨hlen, hrow⟩
  have hrest_len : rest.length = m := by simpa using hlen
  have hpRow_mem : RowFpMem S (m + 1) pRow (A 0) := by simpa using hrow 0
  have hpiv_mem : FpIv.FpMem S (pRow.headD FpIv.zero) (A 0 0) := by
    cases pRow with
    | nil => have := hpRow_mem.1; simp at this
    | cons x xs => simpa using hpRow_mem.2 0
  have hptail_mem := rowFpMem_tail hpRow_mem
  have hsep : 0 < (pRow.headD FpIv.zero).lo ∨ (pRow.headD FpIv.zero).hi < 0 :=
    sepZero_of_isSepZeroIv hpiv_sep
  refine ⟨by rw [elimRowsIv_length, hrest_len], fun i => ?_⟩
  rw [elimRowsIv_getD (by rw [hrest_len]; exact i.2)]
  have hi_mem : RowFpMem S (m + 1) (rest.getD i.1 []) (A i.succ) := by
    simpa [List.getD_cons_succ] using hrow i.succ
  have hrhead_mem : FpIv.FpMem S ((rest.getD i.1 []).headD FpIv.zero) (A i.succ 0) := by
    cases hri : rest.getD i.1 [] with
    | nil => have hl := hi_mem.1; rw [hri] at hl; simp at hl
    | cons x xs =>
      have h0 := hi_mem.2 0
      rw [hri] at h0
      simpa using h0
  have hrtail_mem := rowFpMem_tail hi_mem
  dsimp only
  by_cases hzero : isZeroIv ((rest.getD i.1 []).headD FpIv.zero) = true
  · simp only [hzero, ↓reduceIte]
    have hA0 : A i.succ 0 = 0 := eq_zero_of_isZeroIv hS hzero hrhead_mem
    have heq : elimSubMatrix A i = (fun j => A i.succ j.succ) := by
      ext j; simp [elimSubMatrix, hA0]
    rw [heq]
    exact hrtail_mem
  · simp only [hzero, Bool.false_eq_true, ↓reduceIte]
    have hdiv_mem : FpIv.FpMem S (FpIv.divFp S (FpIv.neg ((rest.getD i.1 []).headD FpIv.zero))
        (pRow.headD FpIv.zero)) (-(A i.succ 0) / A 0 0) :=
      FpIv.divFp_mem hS hsep (FpIv.neg_mem hrhead_mem) hpiv_mem
    exact rowFpMem_zipElimIv hS hrtail_mem hptail_mem hdiv_mem

theorem gaussDetIv_mem {S : ℤ} (hS : 0 < S) :
    ∀ {m : ℕ} {rows : List (List FpIv)} {A : Matrix (Fin m) (Fin m) ℝ} {prod out : FpIv} {p₀ : ℝ},
      gaussDetIv S m rows prod = (true, out) →
      FpIv.FpMem S prod p₀ →
      MatFpMem S m rows A →
      FpIv.FpMem S out (p₀ * A.det) := by
  intro m
  induction m with
  | zero =>
    intro rows A prod out p₀ hres hp₀ _
    simp only [gaussDetIv, Prod.mk.injEq, true_and] at hres
    subst hres
    have hdet : A.det = 1 := Matrix.det_isEmpty
    simpa [hdet] using hp₀
  | succ m ih =>
    intro rows A prod out p₀ hres hp₀ hmat
    cases rows with
    | nil =>
      have hlen := hmat.1; simp at hlen
    | cons pRow rest =>
      dsimp only [gaussDetIv] at hres
      by_cases hpiv : isSepZeroIv (pRow.headD FpIv.zero) = true
      · simp only [hpiv, ↓reduceIte] at hres
        have hpRow_mem : RowFpMem S (m + 1) pRow (A 0) := by simpa using hmat.2 0
        have hpiv_mem : FpIv.FpMem S (pRow.headD FpIv.zero) (A 0 0) := by
          cases pRow with
          | nil => have := hpRow_mem.1; simp at this
          | cons x xs => simpa using hpRow_mem.2 0
        have hA00_ne : A 0 0 ≠ 0 := ne_zero_of_sepZero (sepZero_of_isSepZeroIv hpiv) hpiv_mem
        have hstep := ih hres (FpIv.mulFp_mem hS hp₀ hpiv_mem)
          (matFpMem_elimSubMatrix hS hmat hpiv)
        rw [mul_assoc, ← det_eq_head_mul_det_elimSubMatrix A hA00_ne] at hstep
        exact hstep
      · simp only [hpiv, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at hres
        exact False.elim hres.1

section FastPolyRowAndDen

def stepPolyFastIv {n : ℕ} (S : ℤ) (cIv : Fin n → Fin n → FpIv) (i : Fin n)
    (row : List FpIv) (j : Fin n) : List FpIv :=
  if j = i then row
  else if j < i then
    let iv := cIv j i
    if isZeroIv iv then FpIv.zero :: row
    else addListIv (scaleListIv S (FpIv.neg iv) row) (FpIv.zero :: row)
  else
    let iv := cIv i j
    if isZeroIv iv then row ++ [FpIv.zero]
    else addListIv row (FpIv.zero :: scaleListIv S iv row)

def polyRowFastIv {n : ℕ} (S : ℤ) (cIv : Fin n → Fin n → FpIv) (i : Fin n) : List FpIv :=
  (List.finRange n).foldl (stepPolyFastIv S cIv i) [FpIv.ofInt S 1]

private lemma scaleListIv_length (S : ℤ) (c : FpIv) (l : List FpIv) :
    (scaleListIv S c l).length = l.length := by
  induction l with
  | nil => rfl
  | cons _ _ ih => simp [scaleListIv, ih]

private lemma addListIv_length (as bs : List FpIv) :
    (addListIv as bs).length = max as.length bs.length := by
  induction as generalizing bs with
  | nil => simp [addListIv]
  | cons a as ih =>
    cases bs with
    | nil => simp [addListIv]
    | cons b bs =>
      simp only [addListIv, List.length_cons, ih]
      omega

private lemma stepPolyFastIv_length {n : ℕ} (S : ℤ) (cIv : Fin n → Fin n → FpIv)
    (i : Fin n) (row : List FpIv) (j : Fin n) :
    (stepPolyFastIv S cIv i row j).length =
      row.length + if j = i then 0 else 1 := by
  unfold stepPolyFastIv
  by_cases hji : j = i
  · simp [hji]
  · by_cases hlt : j < i
    · simp only [hji, hlt, ↓reduceIte]
      by_cases hzero : isZeroIv (cIv j i) = true
      · simp [hzero]
      · simp [hzero, addListIv_length, scaleListIv_length]
    · simp only [hji, hlt, ↓reduceIte]
      by_cases hzero : isZeroIv (cIv i j) = true
      · simp [hzero]
      · simp [hzero, addListIv_length, scaleListIv_length]

private lemma getD_append_zero (row : List FpIv) (k : ℕ) :
    (row ++ [FpIv.zero]).getD k FpIv.zero = row.getD k FpIv.zero := by
  induction row generalizing k with
  | nil => cases k <;> simp
  | cons a as ih =>
    cases k with
    | zero => simp
    | succ k => simpa [List.getD_cons_succ] using ih k

private lemma getD_mulLinListR_zero_one (ps : List ℝ) (k : ℕ) :
    (mulLinListR 0 1 ps).getD k 0 = (0 :: ps).getD k 0 := by
  rw [← coeff_evalListR, evalListR_mulLinListR]
  cases k with
  | zero => simp
  | succ k => simp [coeff_evalListR]

private lemma getD_mulLinListR_one_zero (ps : List ℝ) (k : ℕ) :
    (mulLinListR 1 0 ps).getD k 0 = ps.getD k 0 := by
  rw [← coeff_evalListR, evalListR_mulLinListR]
  simp [coeff_evalListR]

private lemma getD_addListIv_ext (as bs : List FpIv) (k : ℕ) :
    (addListIv as bs).getD k FpIv.zero = FpIv.add (as.getD k FpIv.zero) (bs.getD k FpIv.zero) := by
  have hzL : ∀ a : FpIv, FpIv.add FpIv.zero a = a := fun a => by cases a; simp [FpIv.add, FpIv.zero]
  have hzR : ∀ a : FpIv, FpIv.add a FpIv.zero = a := fun a => by cases a; simp [FpIv.add, FpIv.zero]
  induction as generalizing bs k with
  | nil => simp [addListIv, hzL]
  | cons a as ih =>
    cases bs with
    | nil => simp [addListIv, hzR]
    | cons b bs =>
      cases k with
      | zero => simp [addListIv]
      | succ k => rw [addListIv, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ, ih]

lemma polyRowFastIv_length {n : ℕ} (hn : 1 ≤ n) (S : ℤ) (cIv : Fin n → Fin n → FpIv) (i : Fin n) :
    (polyRowFastIv S cIv i).length = n := by
  have hfold : ∀ (l : List (Fin n)) (row : List FpIv),
      (l.foldl (stepPolyFastIv S cIv i) row).length =
        row.length + (l.map fun j => if j = i then (0 : ℕ) else 1).sum := by
    intro l
    induction l with
    | nil => intro row; simp
    | cons j js ih =>
      intro row
      rw [List.foldl_cons, ih, stepPolyFastIv_length, List.map_cons, List.sum_cons]
      omega
  unfold polyRowFastIv
  rw [hfold, List.length_singleton]
  have hsum_univ : ((List.finRange n).map fun j => if j = i then (0 : ℕ) else 1).sum =
      ∑ j : Fin n, (if j = i then (0 : ℕ) else 1) := by
    rw [← Multiset.sum_coe, ← Multiset.map_coe]
    exact (Finset.sum_eq_multiset_sum Finset.univ _).symm
  rw [hsum_univ]
  have hsplit : (∑ j : Fin n, (if j = i then (0 : ℕ) else 1)) =
      (if i = i then (0 : ℕ) else 1) + ∑ j ∈ Finset.univ.erase i, (if j = i then (0 : ℕ) else 1) :=
    (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)).symm
  rw [hsplit]
  simp only [↓reduceIte, zero_add]
  have hconst : (∑ j ∈ Finset.univ.erase i, (if j = i then (0 : ℕ) else 1)) =
      ∑ _j ∈ Finset.univ.erase i, (1 : ℕ) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hne : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [hne]
  rw [hconst, Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_fin]
  omega

lemma polyRowFastIv_mem {n : ℕ} {S : ℤ} (hS : 0 < S)
    {cIv : Fin n → Fin n → FpIv} {c : Fin n → Fin n → ℝ}
    (hc : ∀ i j : Fin n, i < j → FpIv.FpMem S (cIv i j) (c i j))
    (i : Fin n) :
    ListFpMem S (polyRowFastIv S cIv i) (polyListR c i) := by
  have hinit : ListFpMem S [FpIv.ofInt S 1] [1] := by
    intro k
    cases k with
    | zero => simpa using FpIv.ofInt_mem S 1
    | succ k => simp [FpIv.zero_mem S]
  have hfold : ∀ (l : List (Fin n)) (ivs : List FpIv) (ps : List ℝ),
      ListFpMem S ivs ps →
      ListFpMem S (l.foldl (stepPolyFastIv S cIv i) ivs) (l.foldl (stepPolyR c i) ps) := by
    intro l
    induction l with
    | nil => intro ivs ps h; exact h
    | cons j js ih =>
      intro ivs ps h
      apply ih
      by_cases hji : j = i
      · simp [stepPolyFastIv, stepPolyR, hji, h]
      · by_cases hlt : j < i
        · simp only [stepPolyFastIv, stepPolyR, hji, hlt, ↓reduceIte]
          by_cases hzero : isZeroIv (cIv j i) = true
          · simp only [hzero, ↓reduceIte]
            have hc0 : c j i = 0 := eq_zero_of_isZeroIv hS hzero (hc j i hlt)
            intro k
            rw [hc0, neg_zero, getD_mulLinListR_zero_one]
            cases k with
            | zero => simpa using FpIv.zero_mem S
            | succ k => simpa [List.getD_cons_succ] using h k
          · simp only [hzero, Bool.false_eq_true, ↓reduceIte]
            have hadd := addListIv_mem (scaleListIv_mem hS (FpIv.neg_mem (hc j i hlt)) h)
              (show ListFpMem S (FpIv.zero :: ivs) (0 :: scaleListR 1 ps) by
                intro k; cases k with
                | zero => simp [FpIv.zero_mem S]
                | succ k =>
                  have h1 : (0 :: scaleListR 1 ps).getD (k + 1) 0 = ps.getD k 0 := by
                    rw [← coeff_evalListR]; simp [evalListR, evalListR_scaleListR, coeff_evalListR]
                  rw [h1, List.getD_cons_succ]; exact h k)
            intro k
            simpa [mulLinListR, getD_addListIv_ext] using hadd k
        · have hij : i < j := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hji)
          simp only [stepPolyFastIv, stepPolyR, hji, hlt, ↓reduceIte]
          by_cases hzero : isZeroIv (cIv i j) = true
          · simp only [hzero, ↓reduceIte]
            have hc0 : c i j = 0 := eq_zero_of_isZeroIv hS hzero (hc i j hij)
            intro k
            rw [getD_append_zero, hc0, getD_mulLinListR_one_zero]
            exact h k
          · simp only [hzero, Bool.false_eq_true, ↓reduceIte]
            have hadd := addListIv_mem
              (show ListFpMem S ivs (scaleListR 1 ps) by
                intro k
                have h1 : (scaleListR 1 ps).getD k 0 = ps.getD k 0 := by
                  rw [← coeff_evalListR, evalListR_scaleListR]; simp [coeff_evalListR]
                rw [h1]; exact h k)
              (show ListFpMem S (FpIv.zero :: scaleListIv S (cIv i j) ivs) (0 :: scaleListR (c i j) ps) by
                intro k; cases k with
                | zero => simp [FpIv.zero_mem S]
                | succ k =>
                  have hs := scaleListIv_mem hS (hc i j hij) h k
                  simpa [List.getD_cons_succ] using hs)
            intro k
            simpa [mulLinListR] using hadd k
  exact hfold (List.finRange n) [FpIv.ofInt S 1] [1] hinit

lemma planarMat_matFpMem_polyRowFastIv {n : ℕ} (hn : 1 ≤ n) {S : ℤ} (hS : 0 < S)
    {p : Fin n → Fin 3 → ℝ} {cIv : Fin n → Fin n → FpIv}
    (hc : ∀ i j : Fin n, i < j → FpIv.FpMem S (cIv i j) (planarSlope p i j)) :
    MatFpMem S n ((List.finRange n).map (polyRowFastIv S cIv)) (planarMat p) := by
  refine ⟨by simp, fun i => ?_⟩
  have hget : ((List.finRange n).map (polyRowFastIv S cIv)).getD i.1 [] = polyRowFastIv S cIv i := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp), Option.getD_some,
      List.getElem_map, List.getElem_finRange]
    rfl
  rw [hget]
  refine ⟨polyRowFastIv_length hn S cIv i, fun j => ?_⟩
  have hcoeff : planarMat p i j = (polyListR (planarSlope p) i).getD j.1 0 := by
    unfold planarMat
    rw [← evalListR_polyListR_eq_planarPoly, coeff_evalListR]
  rw [hcoeff]
  exact polyRowFastIv_mem hS hc i j.1

/-- Canonical list of active off-diagonal upper-triangular pairs with `ptsX j ≠ ptsX i`. -/
def activePairs (n : ℕ) (ptsX : Fin n → ℤ) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun i =>
    (List.finRange n).filterMap fun j =>
      if i < j ∧ ptsX j ≠ ptsX i then some (i, j) else none

lemma activePairs_valid (n : ℕ) (ptsX : Fin n → ℤ) :
    (activePairs n ptsX).Nodup ∧ ∀ q ∈ activePairs n ptsX, q.1 < q.2 := by
  let rowPairs : Fin n → List (Fin n × Fin n) := fun i =>
    (List.finRange n).filterMap fun j => if i < j ∧ ptsX j ≠ ptsX i then some (i, j) else none
  have hmem_row : ∀ (i : Fin n) (q : Fin n × Fin n), q ∈ rowPairs i → q.1 = i ∧ q.1 < q.2 := by
    intro i q hq
    simp only [rowPairs, List.mem_filterMap] at hq
    rcases hq with ⟨j, _, hj⟩
    split_ifs at hj with hc
    · injection hj with hqe
      subst hqe
      exact ⟨rfl, hc.1⟩
  have hrow_nd : ∀ i : Fin n, (rowPairs i).Nodup := by
    intro i
    have hsub : ∀ l : List (Fin n), l.Nodup →
        (l.filterMap fun j => if i < j ∧ ptsX j ≠ ptsX i then some (i, j) else none).Nodup := by
      intro l hl
      induction hl with
      | nil => simp
      | @cons j js hnotin _ ih =>
        by_cases hc : i < j ∧ ptsX j ≠ ptsX i
        · have hite : (if i < j ∧ ptsX j ≠ ptsX i then some (i, j) else none) = some (i, j) := by
            simp [hc]
          rw [List.filterMap_cons, hite]
          refine List.nodup_cons.mpr ⟨?_, ih⟩
          intro hmem
          simp only [List.mem_filterMap] at hmem
          rcases hmem with ⟨k, hk, hkf⟩
          split_ifs at hkf
          · injection hkf with hpair
            have hjk : k = j := congr_arg Prod.snd hpair
            exact hnotin _ hk hjk.symm
        · have hite : (if i < j ∧ ptsX j ≠ ptsX i then some (i, j) else none) = none := by
            simp [hc]
          rw [List.filterMap_cons, hite]
          exact ih
    exact hsub (List.finRange n) (List.nodup_finRange n)
  refine ⟨?_, ?_⟩
  · unfold activePairs
    rw [List.nodup_flatMap]
    refine ⟨fun i _ => hrow_nd i, ?_⟩
    exact (List.nodup_iff_pairwise_ne.mp (List.nodup_finRange n)).imp fun hne q h1 h2 =>
      hne ((hmem_row _ q h1).1.symm.trans (hmem_row _ q h2).1)
  · intro q hq
    simp only [activePairs, List.mem_flatMap] at hq
    rcases hq with ⟨i, _, hi⟩
    exact (hmem_row i q hi).2

def denFoldIv {n : ℕ} (S : ℤ) (cIv : Fin n → Fin n → FpIv)
    (pairs : List (Fin n × Fin n)) : FpIv :=
  pairs.foldl
    (fun acc q =>
      FpIv.mulFp S acc (FpIv.add (FpIv.ofInt S 1) (FpIv.mulFp S (cIv q.1 q.2) (cIv q.1 q.2))))
    (FpIv.ofInt S 1)

lemma denFoldIv_lo_le_planarDen {n : ℕ} {S : ℤ} (hS : 0 < S)
    {p : Fin n → Fin 3 → ℝ} {cIv : Fin n → Fin n → FpIv}
    {pairs : List (Fin n × Fin n)}
    (hnodup : pairs.Nodup) (hlt : ∀ q ∈ pairs, q.1 < q.2)
    (hc : ∀ i j : Fin n, i < j → FpIv.FpMem S (cIv i j) (planarSlope p i j)) :
    ((denFoldIv S cIv pairs).lo : ℝ) ≤ (S : ℝ) * planarDen p := by
  let f : Fin n × Fin n → ℝ := fun q => 1 + planarSlope p q.1 q.2 ^ 2
  have hfold : ∀ (l : List (Fin n × Fin n)) (acc : FpIv) (v : ℝ),
      (∀ q ∈ l, q.1 < q.2) →
      FpIv.FpMem S acc v →
      FpIv.FpMem S
        (l.foldl (fun a q => FpIv.mulFp S a (FpIv.add (FpIv.ofInt S 1) (FpIv.mulFp S (cIv q.1 q.2) (cIv q.1 q.2)))) acc)
        (v * (l.map f).prod) := by
    intro l
    induction l with
    | nil => intro acc v _ hacc; simpa using hacc
    | cons q qs ih =>
      intro acc v hq hacc
      have hq0 : q.1 < q.2 := hq q (by simp)
      have hc0 := hc q.1 q.2 hq0
      have hterm : FpIv.FpMem S (FpIv.add (FpIv.ofInt S 1) (FpIv.mulFp S (cIv q.1 q.2) (cIv q.1 q.2))) (f q) := by
        simpa [f, sq] using FpIv.add_mem (FpIv.ofInt_mem S 1) (FpIv.mulFp_mem hS hc0 hc0)
      have hnext := ih (FpIv.mulFp S acc (FpIv.add (FpIv.ofInt S 1) (FpIv.mulFp S (cIv q.1 q.2) (cIv q.1 q.2))))
        (v * f q) (fun x hx => hq x (by simp [hx])) (FpIv.mulFp_mem hS hacc hterm)
      simpa [List.foldl_cons, List.map_cons, List.prod_cons, mul_assoc] using hnext
  have hden_mem := hfold pairs (FpIv.ofInt S 1) 1 hlt (FpIv.ofInt_mem S 1)
  rw [one_mul] at hden_mem
  let pairsSub : Finset { e : Fin n × Fin n // e.1 < e.2 } :=
    Finset.univ.filter fun e => e.1 ∈ pairs
  have himage : pairsSub.image Subtype.val = pairs.toFinset := by
    ext q
    simp only [pairsSub, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      List.mem_toFinset]
    constructor
    · rintro ⟨e, he, rfl⟩; exact he
    · intro hq; exact ⟨⟨q, hlt q hq⟩, hq, rfl⟩
  have hprod_eq : (pairs.map f).prod = ∏ e ∈ pairsSub, f e.1 := by
    have h1 : (pairs.map f).prod = ∏ q ∈ pairs.toFinset, f q := (List.prod_toFinset f hnodup).symm
    rw [h1, ← himage, Finset.prod_image (fun a _ b _ hab => Subtype.ext hab)]
  have hprod_le : (pairs.map f).prod ≤ planarDen p := by
    rw [hprod_eq]
    have hge1 : ∀ e : { e : Fin n × Fin n // e.1 < e.2 }, 1 ≤ f e.1 := fun e => by
      dsimp [f]; nlinarith [sq_nonneg (planarSlope p e.1.1 e.1.2)]
    have h0 : 0 ≤ ∏ e ∈ pairsSub, f e.1 := Finset.prod_nonneg fun e _ => by linarith [hge1 e]
    have hsdiff : 1 ≤ ∏ e ∈ Finset.univ \ pairsSub, f e.1 := by
      have hsub : ∀ T : Finset { e : Fin n × Fin n // e.1 < e.2 },
          (∀ e ∈ T, 1 ≤ f e.1) → 1 ≤ ∏ e ∈ T, f e.1 := by
        intro T
        induction T using Finset.induction_on with
        | empty => intro _; simp
        | @insert a S ha ih =>
          intro hS
          rw [Finset.prod_insert ha]
          exact one_le_mul_of_one_le_of_one_le (hS a (Finset.mem_insert_self a S))
            (ih fun e he => hS e (Finset.mem_insert_of_mem he))
      exact hsub _ fun e _ => hge1 e
    have huniv : planarDen p =
        (∏ e ∈ pairsSub, f e.1) * ∏ e ∈ Finset.univ \ pairsSub, f e.1 := by
      unfold planarDen
      rw [mul_comm]
      exact (Finset.prod_sdiff (Finset.subset_univ pairsSub)).symm
    rw [huniv]
    exact le_mul_of_one_le_right h0 hsdiff
  have hSR : (0 : ℝ) < (S : ℝ) := by exact_mod_cast hS
  exact le_trans hden_mem.1 (mul_le_mul_of_nonneg_left hprod_le hSR.le)

lemma planar_atiyahDet_neg_and_norm_lt_one_of_fpMem {n : ℕ} {S : ℤ} (hS : 0 < S)
    {x : DistinctPoints n} (hy : ∀ i, x.1 i 1 = 0) (hz : StrictMono (fun i => x.1 i 2))
    {detCert : FpIv} {denLo : ℤ}
    (hdet : FpIv.FpMem S detCert (planarMat x.1).det)
    (hden : (denLo : ℝ) ≤ (S : ℝ) * planarDen x.1)
    (hneg : detCert.hi < 0) (habs : -denLo < detCert.lo) :
    (atiyahDet x).im = 0 ∧ (atiyahDet x).re < 0 ∧ ‖atiyahDet x‖ < 1 := by
  have hre : atiyahDet x = (((planarMat x.1).det / planarDen x.1 : ℝ) : ℂ) :=
    atiyahDet_eq_planarMat_div x hy hz
  have hS_pos : (0 : ℝ) < (S : ℝ) := by exact_mod_cast hS
  have hden_pos : 0 < planarDen x.1 := planarDen_pos x.1
  have hdet_neg : (planarMat x.1).det < 0 := by
    have h1 : (S : ℝ) * (planarMat x.1).det ≤ (detCert.hi : ℝ) := hdet.2
    have h2 : (detCert.hi : ℝ) < 0 := by exact_mod_cast hneg
    have h3 : (S : ℝ) * (planarMat x.1).det < 0 := lt_of_le_of_lt h1 h2
    exact (mul_neg_iff.mp h3).resolve_right (fun h => by linarith [h.1]) |>.2
  have hnorm_lt : |(planarMat x.1).det| < planarDen x.1 := by
    have hlo : -((denLo : ℝ)) < (detCert.lo : ℝ) := by exact_mod_cast habs
    have h_abs : (S : ℝ) * (-(planarMat x.1).det) < (denLo : ℝ) := by
      linarith [hdet.1, hlo]
    have h_mul : (S : ℝ) * |(planarMat x.1).det| < (S : ℝ) * planarDen x.1 := by
      rw [abs_of_neg hdet_neg]
      exact lt_of_lt_of_le h_abs hden
    exact lt_of_mul_lt_mul_left h_mul hS_pos.le
  rw [hre]
  refine ⟨by simp, ?_, ?_⟩
  · simpa using div_neg_of_neg_of_pos hdet_neg hden_pos
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hden_pos]
    exact (div_lt_one hden_pos).mpr hnorm_lt

lemma planar_atiyahDet_norm_lt_one_of_fpMem {n : ℕ} {S : ℤ} (hS : 0 < S)
    {x : DistinctPoints n} (hy : ∀ i, x.1 i 1 = 0) (hz : StrictMono (fun i => x.1 i 2))
    {detCert : FpIv} {denLo : ℤ}
    (hdet : FpIv.FpMem S detCert (planarMat x.1).det)
    (hden : (denLo : ℝ) ≤ (S : ℝ) * planarDen x.1)
    (hneg : detCert.hi < 0) (habs : -denLo < detCert.lo) :
    ‖atiyahDet x‖ < 1 :=
  (planar_atiyahDet_neg_and_norm_lt_one_of_fpMem hS hy hz hdet hden hneg habs).2.2

end FastPolyRowAndDen

section Planar57AndDirect63

def S57 : ℤ := 10000000000000000000000000000000000000000
def c57_LA_rho : List (List ℤ) := [
  [1780756392210905416184382536649654320818392406, 4581995798961408912566149509903847132138672133, 4944599793643566458057510804703391915770897775],
  [1780746426109006683467047863377128247568896268, 4581991747220852426488583132504069194205041444, 4944595981574227667992583617451251489834501051],
  [1780736460007488025488045527375311442924452316, 4581987695498537673915715326652214841227569611, 4944592169522174050177699727425286986015661674],
  [1780726493906349448628810476447000117484040338, 4581983643794464703239538150759229213964090634, 4944588357487405644591096922491574085881357517],
  [1780716527805590959270920274426407474891475710, 4581979592108633562851996957238093393358595916, 4944584545469922491210954999683809625412609657],
  [1780706561705212563796095105156446517795462947, 4581975540441044301144990390370735919318484737, 4944580733469724630015395763582216300450818720],
  [1780696595605214268586197776466145727448307986, 4581971488791696966510370384174930670625380812, 4944576921486812100982483024692439682050703228],
  [1780686629505596080023233724148197622113216890, 4581967437160591607339942160271181106090697679, 4944573109521184944090222597824437541833758724],
  [1780676663406358004489351015936640199450338104, 4581963385547728272025464225749590867067139270, 4944569297572843199316562300471361487436158432],
  [1780666697307500048366840355484671268051934931, 4581959333953107008958648371036720741427325515, 4944565485641786906639391951188430908145018302],
  [1780656731209022218038135086342595673297304376, 4581955282376727866531159667762431989120736404, 4944561673728016106036543367971799230816951304],
  [1780646765110924519885811195935905422698288056, 4581951230818590893134616466626716029420171508, 4944557861831530837485790366637412486172837887],
  [1780636799013206960292587319543492715906450388, 4581947179278696137160590395266510489968925458, 4944554049952331140964848759199860185562741554],
  [1780626832915869545641324744275995884553228826, 4581943127757043647000606356122501617739883486, 4944550238090417056451376352251218508294900561],
  [1780616866818912282315027413054278247094590462, 4581939076253633471046142524305913052017744646, 4944546426245788623922972945339885799622728767],
  [1780606900722335176696841928588039883831958891, 4581935024768465657688630345465280959515583916, 4944542614418445883357180329349410379483760732],
  [1780596934626138235170057557354562337281404800, 4581930973301540255319454533653215531736967899, 4944538802608388874731482284877310662084478181],
  [1780586968530321464118106233577586243063323355, 4581926921852857312329953069193148844694842428, 4944534990815617638023304580613887586424956993],
  [1780577002434884869924562563206321896485051038, 4581922870422416877111417196546069081098413910, 4944531179040132213210014971721029357857275942],
  [1780567036339828458973143827894592759989104224, 4581918819010218998055091422177241115119249799, 4944527367281932640268923198211008500771630424],
  [1780557070245152237647709988980111916639951394, 4581914767616263723552173512422913459847827153, 4944523555541018959177280983325271222504096480],
  [1780547104150856212332263691463891474822460533, 4581910716240551101993814491357011577551761761, 4944519743817391209912282031913219088559992430],
  [1780537138056940389410950267989784929325392895, 4581906664883081181771118638657817552846953899, 4944515932111049432451062028810983009246787522],
  [1780527171963404775268057742824162483983543995, 4581902613543854011275143487474636128892890310, 4944512120421993666770698637220189537810508991],
  [1780517205870249376288016835835719341052362342, 4581898562222869638896899822294447106723345569, 4944508308750223952848211497086719480169601012],
  [1780507239777474198855400966475416962489106119, 4581894510920128113027351676808544107823729532, 4944504497095740330660562223479458816340191031],
  [1780497273685079249354926257756557308314827713, 4581890459635629482057416331779159700066331128, 4944500685458542840184654404969041933646721049],
  [1780487307593064534171451540234990057231705699, 4581886408369373794377964312906076887114712317, 4944496873838631521397333602006587171811903409]
]
def c57_AB_rho : List ℤ := [4043367316445539059677344306146365930235743774, 4426102078906450164701595490282821535171416780, 383244470540671988962650655273866532243055602]
def c57_AU_rho : List (List ℤ) := [
  [187811608799882229218197256957960081034906583, 4189192374969189690769339606282119125997141232, 4571235860825822669246169341058583224627295832],
  [187817866296047565337463260970498997980221479, 4189192460272027177276787280241455335997645576, 4571235876849935644764528598103641704382290361],
  [187824124116152874980288766404185140518777116, 4189192545598733875413396371642838339842862248, 4571235892895924486147401744622274038992630973],
  [187830382260165780667777608442296185130007140, 4189192630949309783720641527832090739363605577, 4571235908963789193164422262752696239880172815],
  [187836640728053907560147763733422336875735226, 4189192716323754900739589508568110780687938594, 4571235925053529765584909573902207271284451394],
  [187842899519784883456849957713197631054100585, 4189192801722069225010899186147551035239461085, 4571235941165146203177869038763747985481873972],
  [187849158635326338796686124169900191292684055, 4189192887144252755074821545529531921364882226, 4571235957298638505711991957332482601824427619],
  [187855418074645906657927717100009174386035978, 4189192972590305489471199684460390066566011886, 4571235973454006672955655568922402729595126619],
  [187861677837711222758433874899800822942093473, 4189193058060227426739468813598461510311297714, 4571235989631250704676923052182953934677418200],
  [187867937924489925455769436939060734046665038, 4189193143554018565418656256638899747402028178, 4571236005830370600643543525115684850035761732],
  [187874198334949655747322812562984135688249777, 4189193229071678904047381450438528611868314811, 4571236022051366360622952045090918830004592794],
  [187880459069058057270423702568330642609941072, 4189193314613208441163855945140730001369959945, 4571236038294237984382269608864448148382879724],
  [187886720126782776302460673199894639574033360, 4189193400178607175305883404300366442077309290, 4571236054558985471688303152594250740331476494],
  [187892981508091461760998582713347112741197606, 4189193485767875105010859605008738494007181775, 4571236070845608822307545551857229488070471960],
  [187899243212951765203895860550499418982707216, 4189193571381012228815772438018576996788962115, 4571236087154108036006175621665974050373731795],
  [187905505241331340829421639173034148464171123, 4189193657018018545257201907869070155835934632, 4571236103484483112550058116485545235857825603],
  [187911767593197845476372738600742897765553471, 4189193742678894052871320133010925468896929919, 4571236119836734051704743730250281920062527949],
  [187918030268518938624190503700305429137917332, 4189193828363638750193891345931466492963348988, 4571236136210860853235469096380630506320078274],
  [187924293267262282393077494270639346245309777, 4189193914072252635760271893279764451506622605, 4571236152606863516907156787799996930410380872],
  [187930556589395541544114027970844067903492983, 4189193999804735708105410235991804682021156575, 4571236169024742042484415316951621208999322339],
  [187936820234886383479374576136757528908805196, 4189194085561087965763846949415687923847806789, 4571236185464496429731539135815474531857380133],
  [187943084203702478242044012532138681053289750, 4189194171341309407269714723436866446252920916, 4571236201926126678412508635925178897855692082],
  [187949348495811498516533715080483507849342164, 4189194257145400031156738362603415016737976674, 4571236218409632788290990148384949294736752956],
  [187955613111181119628597520623476903341475834, 4189194342973359835958234786251336709554839668, 4571236234915014759130335943886558422656900363],
  [187961878049779019545447532752077398667376112, 4189194428825188820207113028629903554401656853, 4571236251442272590693584232726323961497748543],
  [187968143311572878875869782756226349748179645, 4189194514700886982435874239027032025274394726, 4571236267991406282743459164822118381943724778]
]
def c57_LA_lit : List (List FpIv) := [
  [⟨412040423952588135452732877109509953473, 412040423952588135452732877109509953474⟩, ⟨6506230064552758895990846375073637712074, 6506230064552758895990846375073637712075⟩, ⟨6693340290564173008265851433210299888150, 6693340290564173008265851433210299888151⟩],
  [⟨412042737816155868057874633251074919378, 412042737816155868057874633251074919379⟩, ⟨6506244264129376722324406385482280413185, 6506244264129376722324406385482280413186⟩, ⟨6693353827250494217076330916298789362675, 6693353827250494217076330916298789362676⟩],
  [⟨412045051705667268808568421522965387334, 412045051705667268808568421522965387335⟩, ⟨6506258463749540882674109883534687759552, 6506258463749540882674109883534687759553⟩, ⟨6693367363974628382684090993945364783692, 6693367363974628382684090993945364783693⟩],
  [⟨412047365621122773297643443481236688330, 412047365621122773297643443481236688331⟩, ⟨6506272663413251492560439028415172005910, 6506272663413251492560439028415172005911⟩, ⟨6693380900736575592545325705535652517771, 6693380900736575592545325705535652517772⟩],
  [⟨412049679562522817127663783372523883377, 412049679562522817127663783372523883378⟩, ⟨6506286863120508667503764483600284058778, 6506286863120508667503764483600284058779⟩, ⟨6693394437536335934116102229998949134943, 6693394437536335934116102229998949134944⟩],
  [⟨412051993529867835910928679620922716413, 412051993529867835910928679620922716414⟩, ⟨6506301062871312523024345411766743500464, 6506301062871312523024345411766743500465⟩, ⟨6693407974373909494852360882261921409447, 6693407974373909494852360882261921409448⟩],
  [⟨412054307523158265269472796323940440157, 412054307523158265269472796323940440158⟩, ⟨6506315262665663174642329469699336054622, 6506315262665663174642329469699336054623⟩, ⟨6693421511249296362209915109702289497685, 6693421511249296362209915109702289497686⟩],
  [⟨412056621542394540835066494757516867796, 412056621542394540835066494757516867797⟩, ⟨6506329462503560737877752803198778493618, 6506329462503560737877752803198778493619⟩, ⟨6693435048162496623644451488602493293563, 6693435048162496623644451488602493293564⟩],
  [⟨412058935587577098249216104890116003436, 412058935587577098249216104890116003437⟩, ⟨6506343662385005328250540041989550987976, 6506343662385005328250540041989550987977⟩, ⟨6693448585113510366611529720603341961433, 6693448585113510366611529720603341961434⟩],
  [⟨412061249658706373163164196905888604227, 412061249658706373163164196905888604228⟩, ⟨6506357862309997061280504294627696898161, 6506357862309997061280504294627696898162⟩, ⟨6693462122102337678566582629157646646843, 6693462122102337678566582629157646646844⟩],
  [⟨412063563755782801237889852736906027119, 412063563755782801237889852736906027120⟩, ⟨6506372062278536052487347143408590008977, 6506372062278536052487347143408590008978⟩, ⟨6693475659128978646964916155983836365304, 6693475659128978646964916155983836365305⟩],
  [⟨412065877878806818144108937604465713193, 412065877878806818144108937604465713194⟩, ⟨6506386262290622417390658639274669206835, 6506386262290622417390658639274669206836⟩, ⟨6693489196193433359261709357519557069263, 6693489196193433359261709357519557069264⟩],
  [⟨412068192027778859562274371569468662556, 412068192027778859562274371569468662557⟩, ⟨6506400462346256271509917296723140600158, 6506400462346256271509917296723140600159⟩, ⟨6693502733295701902912014401375253893509, 6693502733295701902912014401375253893510⟩],
  [⟨412070506202699361182576401091869252780, 412070506202699361182576401091869252781⟩, ⟨6506414662445437730364490088713647083197, 6506414662445437730364490088713647083198⟩, ⟨6693516270435784365370756562787736579202, 6693516270435784365370756562787736579203⟩],
  [⟨412072820403568758704942870599197753896, 412072820403568758704942870599197753897⟩, ⟨6506428862588166909473632441575905343510, 6506428862588166909473632441575905343511⟩, ⟨6693529807613680834092734221073728076738, 6693529807613680834092734221073728076739⟩],
  [⟨412075134630387487839039494064155892966, 412075134630387487839039494064155892967⟩, ⟨6506443062774443924356488229917310313378, 6506443062774443924356488229917310313379⟩, ⟨6693543344829391396532618856083396327648, 6693543344829391396532618856083396327649⟩],
  [⟨412077448883155984304270126591285821256, 412077448883155984304270126591285821257⟩, ⟨6506457263004268890532089771530507065430, 6506457263004268890532089771530507065431⟩, ⟨6693556882082916140144955044653869225754, 6693556882082916140144955044653869225755⟩],
  [⟨412079763161874683829777036012712837086, 412079763161874683829777036012712837087⟩, ⟨6506471463277641923519357822300930152719, 6506471463277641923519357822300930152720⟩, ⟨6693570419374255152384160457062732757758, 6693570419374255152384160457062732757759⟩],
  [⟨412082077466544022154441174492962217409, 412082077466544022154441174492962217410⟩, ⟨6506485663594563138837101571114310393547, 6506485663594563138837101571114310393548⟩, ⟨6693583956703408520704525853481512323504, 6693583956703408520704525853481512323505⟩],
  [⟨412084391797164435026882450142850511201, 412084391797164435026882450142850511202⟩, ⟨6506499863955032652004018634764149101272, 6506499863955032652004018634764149101273⟩, ⟨6693597494070376332560215080429137236086, 6693597494070376332560215080429137236087⟩],
  [⟨412086706153736358205459998642451647778, 412086706153736358205459998642451647779⟩, ⟨6506514064359050578538695052859159759390, 6506514064359050578538695052859159759391⟩, ⟨6693611031475158675405265067225388402036, 6693611031475158675405265067225388402037⟩],
  [⟨412089020536260227458272454873138213137, 412089020536260227458272454873138213138⟩, ⟨6506528264806617033959605282730677142141, 6506528264806617033959605282730677142142⟩, ⟨6693624568917755636693585822444329181773, 6693624568917755636693585822444329181774⟩],
  [⟨412091334944736478563158224558698247467, 412091334944736478563158224558698247468⟩, ⟨6506542465297732133785112194340033880905, 6506542465297732133785112194340033880906⟩, ⟨6693638106398167303878960430367719430540, 6693638106398167303878960430367719430541⟩],
  [⟨412093649379165547307695755915527916965, 412093649379165547307695755915527916966⟩, ⟨6506556665832395993533467065185904476665, 6506556665832395993533467065185904476666⟩, ⟨6693651643916393764415045047438412720013, 6693651643916393764415045047438412720014⟩],
  [⟨412095963839547869489203811311900413130, 412095963839547869489203811311900413131⟩, ⟨6506570866410608728722809575211616758788, 6506570866410608728722809575211616758789⟩, ⟨6693665181472435105755368898713736740810, 6693665181472435105755368898713736740811⟩],
  [⟨412098278325883880914741738936311432703, 412098278325883880914741738936311432704⟩, ⟨6506585067032370454871167801712430790404, 6506585067032370454871167801712430790405⟩, ⟨6693678719066291415353334274318856886090, 6693678719066291415353334274318856886091⟩],
  [⟨412100592838174017401109744474901591455, 412100592838174017401109744474901591456⟩, ⟨6506599267697681287496458214242785220638, 6506599267697681287496458214242785220639⟩, ⟨6693692256697962780662216525900123016445, 6693692256697962780662216525900123016446⟩],
  [⟨412102907376418714774849162797956125031, 412102907376418714774849162797956125032⟩, ⟨6506613468406541342116485669523511083958, 6506613468406541342116485669523511083959⟩, ⟨6693705794367449289135164063078399406312, 6693705794367449289135164063078399406313⟩]
]
def c57_AB_lit : List FpIv := [⟨9799723234514782932704053160009216804869, 9799723234514782932704053160009216804870⟩, ⟨9754046187917568223827432386344074181184, 9754046187917568223827432386344074181185⟩, ⟨9284242668323922367478234785679021749471, 9284242668323922367478234785679021749472⟩]
def c57_AU_lit : List (List FpIv) := [
  [⟨-4798062034121653871549300816243008944363, -4798062034121653871549300816243008944362⟩, ⟨-9915069741442406113976805201865150788719, -9915069741442406113976805201865150788718⟩, ⟨-9983999625540221492347069259386605409545, -9983999625540221492347069259386605409544⟩],
  [⟨-4797806573109048828495785731774675630050, -4797806573109048828495785731774675630049⟩, ⟨-9915046073257899607730619140045106601985, -9915046073257899607730619140045106601984⟩, ⟨-9983977784644254707736273602736335087892, -9983977784644254707736273602736335087891⟩],
  [⟨-4797551134208387370668175181173047134388, -4797551134208387370668175181173047134387⟩, ⟨-9915022405130373248795419407890204772079, -9915022405130373248795419407890204772078⟩, ⟨-9983955943796143458428916822435699010973, -9983955943796143458428916822435699010972⟩],
  [⟨-4797295717417459431247618323706224240957, -4797295717417459431247618323706224240956⟩, ⟨-9914998737059827033689440845234446888461, -9914998737059827033689440845234446888460⟩, ⟨-9983934102995887743921050270392643205178, -9983934102995887743921050270392643205177⟩],
  [⟨-4797040322734055123559574316274562244078, -4797040322734055123559574316274562244077⟩, ⟨-9914975069046260958929944590092505157955, -9914975069046260958929944590092505157954⟩, ⟨-9983912262243487563708038260823032906427, -9983912262243487563708038260823032906426⟩],
  [⟨-4796784950155964741081908376327483348403, -4796784950155964741081908376327483348402⟩, ⟨-9914951401089675021033218078957353081469, -9914951401089675021033218078957353081468⟩, ⟨-9983890421538942917284558070286876804453, -9983890421538942917284558070286876804452⟩],
  [⟨-4796529599680978757452977759037555719638, -4796529599680978757452977759037555719637⟩, ⟨-9914927733190069216514575047097979301618, -9914927733190069216514575047097979301617⟩, ⟨-9983868580882253804144599937724600603830, -9983868580882253804144599937724600603829⟩],
  [⟨-4796274271306887826479707651877759343757, -4796274271306887826479707651877759343756⟩, ⟨-9914904065347443541888355528857184621217, -9914904065347443541888355528857184621216⟩, ⟨-9983846740273420223781467064493369901745, -9983846740273420223781467064493369901744⟩],
  [⟨-4796018965031482782145656989747496446560, -4796018965031482782145656989747496446559⟩, ⟨-9914880397561797993667925857949462192558, -9914880397561797993667925857949462192557⟩, ⟨-9983824899712442175687775614403462382505, -9983824899712442175687775614403462382504⟩],
  [⟨-4795763680852554638619074193792541573152, -4795763680852554638619074193792541573151⟩, ⟨-9914856729833132568365678667758960877438, -9914856729833132568365678667758960877437⟩, ⟨-9983803059199319659355454713754689328771, -9983803059199319659355454713754689328770⟩],
  [⟨-4795508418767894590260942837063763528209, -4795508418767894590260942837063763528208⟩, ⟨-9914833062161447262493032891637531777850, -9914833062161447262493032891637531777849⟩, ⟨-9983781218734052674275746451372866449522, -9983781218734052674275746451372866449521⟩],
  [⟨-4795253178775294011633017240159088232761, -4795253178775294011633017240159088232760⟩, ⟨-9914809394546742072560433763202857937308, -9914809394546742072560433763202857937307⟩, ⟨-9983759378316641219939205878646334024722, -9983759378316641219939205878646334024721⟩],
  [⟨-4794997960872544457505847999992808162051, -4794997960872544457505847999992808162050⟩, ⟨-9914785726989016995077352816636667212721, -9914785726989016995077352816636667212720⟩, ⟨-9983737537947085295835701009562526366715, -9983737537947085295835701009562526366714⟩],
  [⟨-4794742765057437662866797454835980391891, -4794742765057437662866797454835980391890⟩, ⟨-9914762059488272026552287886983028316768, -9914762059488272026552287886983028316767⟩, ⟨-9983715697625384901454412820744590598309, -9983715697625384901454412820744590598308⟩],
  [⟨-4794487591327765542928045088771291398138, -4794487591327765542928045088771291398137⟩, ⟨-9914738392044507163492763110446730030721, -9914738392044507163492763110446730030720⟩, ⟨-9983693857351540036283835251488054747571, -9983693857351540036283835251488054747570⟩],
  [⟨-4794232439681320193134582878705402625541, -4794232439681320193134582878705402625540⟩, ⟨-9914714724657722402405328924691743587639, -9914714724657722402405328924691743587638⟩, ⟨-9983672017125550699811775203797545159307, -9983672017125550699811775203797545159306⟩],
  [⟨-4793977310115893889172200587081426468639, -4793977310115893889172200587081426468638⟩, ⟨-9914691057327917739795562069139768225887, -9914691057327917739795562069139768225886⟩, ⟨-9983650176947416891525352542423553223230, -9983650176947416891525352542423553223229⟩],
  [⟨-4793722202629279086975461003433817688596, -4793722202629279086975461003433817688595⟩, ⟨-9914667390055093172168065585268859912924, -9914667390055093172168065585268859912923⟩, ⟨-9983628336817138610911000094899251418809, -9983628336817138610911000094899251418808⟩],
  [⟨-4793467117219268422735665137927600426302, -4793467117219268422735665137927600426301⟩, ⟨-9914643722839248696026468816912143239279, -9914643722839248696026468816912143239278⟩, ⟨-9983606496734715857454463651577358676791, -9983606496734715857454463651577358676790⟩],
  [⟨-4793212053883654712908807370023485863720, -4793212053883654712908807370023485863719⟩, ⟨-9914620055680384307873427410556606482682, -9914620055680384307873427410556606482681⟩, ⟨-9983584656700148630640801965667055057391, -9983584656700148630640801965667055057390⟩],
  [⟨-4792957012620230954223520555410070232683, -4792957012620230954223520555410070232682⟩, ⟨-9914596388578500004210623315641979842274, -9914596388578500004210623315641979842273⟩, ⟨-9983562816713436929954386753270945745144, -9983562816713436929954386753270945745143⟩],
  [⟨-4792701993426790323689011094343937273263, -4792701993426790323689011094343937273262⟩, ⟨-9914572721533595781538764784859696842840, -9914572721533595781538764784859696842839⟩, ⟨-9983540976774580754878902693422074360415, -9983540976774580754878902693422074360414⟩],
  [⟨-4792446996301126178602983964538123402686, -4792446996301126178602983964538123402685⟩, ⟨-9914549054545671636357586374451938909006, -9914549054545671636357586374451938909005⟩, ⟨-9983519136883580104897347428120985587549, -9983519136883580104897347428120985587548⟩],
  [⟨-4792192021241032056559557721739037770750, -4792192021241032056559557721739037770749⟩, ⟨-9914525387614727565165848944510763109340, -9914525387614727565165848944510763109339⟩, ⟨-9983497297040434979492031562372837119675, -9983497297040434979492031562372837119674⟩],
  [⟨-4791937068244301675457169471131563048968, -4791937068244301675457169471131563048967⟩, ⟨-9914501720740763564461339659277313070302, -9914501720740763564461339659277313070301⟩, ⟨-9983475457245145378144578664224560920142, -9983475457245145378144578664224560920141⟩],
  [⟨-4791682137308728933506469812711696228545, -4791682137308728933506469812711696228544⟩, ⟨-9914478053923779630740871987441113059972, -9914478053923779630740871987441113059971⟩, ⟨-9983453617497711300335925264802073800583, -9983453617497711300335925264802073800582⟩]
]
def det57_cert : FpIv := ⟨-17411234991859714032811859894129118424785873099745261547036087859193, -17411234991829693892225341342105913129889341095524049480884492604588⟩
def den57_cert : FpIv := ⟨34939696798004197259243933067120385907974093935680562090090087257535, 34939696798004197259243933067120385908839369332867306230200120659093⟩
def den63_cert : FpIv := ⟨3572463025754843646294686642028955894118226387223898, 3572463025754843646294686642028962394159364947130643⟩

def pts57X : Fin 57 → ℤ := fun i =>
  if i.1 < 28 then 0
  else if i.1 = 28 then 14650
  else if i.1 = 29 then 418904
  else if i.1 = 30 then 457123
  else 0

def pts57Z : Fin 57 → ℤ := fun i =>
  if i.1 < 28 then i.1
  else if i.1 = 28 then 177472
  else if i.1 = 29 then 185651
  else if i.1 = 30 then 188492
  else 189224 + ((i.1 : ℤ) - 31)

lemma pts57Z_strictMono : StrictMono pts57Z := by
  intro i j hij
  have hi := i.2
  have hj := j.2
  have hlt : i.1 < j.1 := hij
  dsimp [pts57Z]
  split_ifs <;> omega

noncomputable def x57Path : ℝ → DistinctPoints 57 :=
  planarPath pts57X pts57Z pts57Z_strictMono

lemma S57_pos : 0 < S57 := by decide

private def abIdx (i j : ℕ) : ℕ :=
  if i = 28 ∧ j = 29 then 0 else if i = 28 ∧ j = 30 then 1 else 2

def c57Lit (i j : Fin 57) : FpIv :=
  if i.1 < 28 then
    if 28 ≤ j.1 ∧ j.1 ≤ 30 then (c57_LA_lit[i.1]?.getD [])[j.1 - 28]?.getD FpIv.zero
    else FpIv.zero
  else if i.1 ≤ 30 then
    if j.1 ≤ 30 then
      if i.1 < j.1 then c57_AB_lit[abIdx i.1 j.1]?.getD FpIv.zero else FpIv.zero
    else (c57_AU_lit[j.1 - 31]?.getD [])[i.1 - 28]?.getD FpIv.zero
  else FpIv.zero

private theorem rho57_LA_ok :
    ∀ (i : Fin 28) (m : Fin 3),
      rhoCheck S57 (pts57X ⟨28 + m.1, by omega⟩ - pts57X ⟨i.1, by omega⟩)
        (pts57Z ⟨28 + m.1, by omega⟩ - pts57Z ⟨i.1, by omega⟩)
        ((c57_LA_rho[i.1]?.getD [])[m.1]?.getD 0) = true ∧
      FpIv.slopeIv S57 (pts57X ⟨28 + m.1, by omega⟩ - pts57X ⟨i.1, by omega⟩)
        (pts57Z ⟨28 + m.1, by omega⟩ - pts57Z ⟨i.1, by omega⟩)
        ((c57_LA_rho[i.1]?.getD [])[m.1]?.getD 0) =
        (c57_LA_lit[i.1]?.getD [])[m.1]?.getD FpIv.zero := by
  decide

private theorem rho57_AB_ok :
    (rhoCheck S57 (pts57X ⟨29, by omega⟩ - pts57X ⟨28, by omega⟩)
      (pts57Z ⟨29, by omega⟩ - pts57Z ⟨28, by omega⟩) (c57_AB_rho[0]?.getD 0) = true ∧
     FpIv.slopeIv S57 (pts57X ⟨29, by omega⟩ - pts57X ⟨28, by omega⟩)
      (pts57Z ⟨29, by omega⟩ - pts57Z ⟨28, by omega⟩) (c57_AB_rho[0]?.getD 0) =
      c57_AB_lit[0]?.getD FpIv.zero) ∧
    (rhoCheck S57 (pts57X ⟨30, by omega⟩ - pts57X ⟨28, by omega⟩)
      (pts57Z ⟨30, by omega⟩ - pts57Z ⟨28, by omega⟩) (c57_AB_rho[1]?.getD 0) = true ∧
     FpIv.slopeIv S57 (pts57X ⟨30, by omega⟩ - pts57X ⟨28, by omega⟩)
      (pts57Z ⟨30, by omega⟩ - pts57Z ⟨28, by omega⟩) (c57_AB_rho[1]?.getD 0) =
      c57_AB_lit[1]?.getD FpIv.zero) ∧
    (rhoCheck S57 (pts57X ⟨30, by omega⟩ - pts57X ⟨29, by omega⟩)
      (pts57Z ⟨30, by omega⟩ - pts57Z ⟨29, by omega⟩) (c57_AB_rho[2]?.getD 0) = true ∧
     FpIv.slopeIv S57 (pts57X ⟨30, by omega⟩ - pts57X ⟨29, by omega⟩)
      (pts57Z ⟨30, by omega⟩ - pts57Z ⟨29, by omega⟩) (c57_AB_rho[2]?.getD 0) =
      c57_AB_lit[2]?.getD FpIv.zero) := by
  decide

private theorem rho57_AU_ok :
    ∀ (k : Fin 26) (m : Fin 3),
      rhoCheck S57 (pts57X ⟨31 + k.1, by omega⟩ - pts57X ⟨28 + m.1, by omega⟩)
        (pts57Z ⟨31 + k.1, by omega⟩ - pts57Z ⟨28 + m.1, by omega⟩)
        ((c57_AU_rho[k.1]?.getD [])[m.1]?.getD 0) = true ∧
      FpIv.slopeIv S57 (pts57X ⟨31 + k.1, by omega⟩ - pts57X ⟨28 + m.1, by omega⟩)
        (pts57Z ⟨31 + k.1, by omega⟩ - pts57Z ⟨28 + m.1, by omega⟩)
        ((c57_AU_rho[k.1]?.getD [])[m.1]?.getD 0) =
        (c57_AU_lit[k.1]?.getD [])[m.1]?.getD FpIv.zero := by
  decide

lemma x57Path_one_ax (i : Fin 57) (h28 : i.1 ≠ 28) (h29 : i.1 ≠ 29) (h30 : i.1 ≠ 30) :
    (x57Path 1).1 i 0 = 0 := by
  have hx : pts57X i = 0 := by dsimp [pts57X]; split_ifs <;> omega
  simp [x57Path, planarPath, hx]

private lemma planarSlope_eq_zero_of_x_zero {n : ℕ} (p : Fin n → Fin 3 → ℝ)
    {i j : Fin n} (hi : p i 0 = 0) (hj : p j 0 = 0) : planarSlope p i j = 0 := by
  simp [planarSlope, hi, hj]

lemma c57Lit_mem :
    ∀ i j : Fin 57, i < j → FpIv.FpMem S57 (c57Lit i j) (planarSlope (x57Path 1).1 i j) := by
  intro ⟨iv, hi⟩ ⟨jv, hj⟩ hij
  have hlt : iv < jv := hij
  unfold c57Lit
  dsimp only
  by_cases hi28 : iv < 28
  · simp only [hi28, ↓reduceIte]
    by_cases hjmid : 28 ≤ jv ∧ jv ≤ 30
    · simp only [hjmid]
      have hrok := rho57_LA_ok ⟨iv, hi28⟩ ⟨jv - 28, by omega⟩
      have hjeq : (⟨jv, hj⟩ : Fin 57) = ⟨28 + (jv - 28), by omega⟩ := Fin.ext (by dsimp; omega)
      rw [← hrok.2, hjeq]
      exact slopeIv_planarPath_one_mem S57_pos pts57X pts57Z pts57Z_strictMono
        (show (⟨iv, hi⟩ : Fin 57) < ⟨28 + (jv - 28), by omega⟩ from Fin.mk_lt_mk.mpr (by omega))
        hrok.1
    · simp only [hjmid, ↓reduceIte]
      rw [planarSlope_eq_zero_of_x_zero _
        (x57Path_one_ax ⟨iv, hi⟩ (by dsimp; omega) (by dsimp; omega) (by dsimp; omega))
        (x57Path_one_ax ⟨jv, hj⟩ (by dsimp; omega) (by dsimp; omega) (by dsimp; omega))]
      exact FpIv.zero_mem S57
  · by_cases hi30 : iv ≤ 30
    · simp only [hi28, hi30, ↓reduceIte]
      by_cases hj30 : jv ≤ 30
      · simp only [hj30, hlt, ↓reduceIte]
        have hrok := rho57_AB_ok
        have hcases : (iv = 28 ∧ jv = 29) ∨ (iv = 28 ∧ jv = 30) ∨ (iv = 29 ∧ jv = 30) := by omega
        rcases hcases with ⟨hiv, hjv⟩ | ⟨hiv, hjv⟩ | ⟨hiv, hjv⟩
        · have hi_eq : (⟨iv, hi⟩ : Fin 57) = ⟨28, by omega⟩ := Fin.ext hiv
          have hj_eq : (⟨jv, hj⟩ : Fin 57) = ⟨29, by omega⟩ := Fin.ext hjv
          have hab : abIdx iv jv = 0 := by subst hiv; subst hjv; rfl
          rw [hab, hi_eq, hj_eq, ← hrok.1.2]
          exact slopeIv_planarPath_one_mem S57_pos pts57X pts57Z pts57Z_strictMono
            (by decide) hrok.1.1
        · have hi_eq : (⟨iv, hi⟩ : Fin 57) = ⟨28, by omega⟩ := Fin.ext hiv
          have hj_eq : (⟨jv, hj⟩ : Fin 57) = ⟨30, by omega⟩ := Fin.ext hjv
          have hab : abIdx iv jv = 1 := by subst hiv; subst hjv; rfl
          rw [hab, hi_eq, hj_eq, ← hrok.2.1.2]
          exact slopeIv_planarPath_one_mem S57_pos pts57X pts57Z pts57Z_strictMono
            (by decide) hrok.2.1.1
        · have hi_eq : (⟨iv, hi⟩ : Fin 57) = ⟨29, by omega⟩ := Fin.ext hiv
          have hj_eq : (⟨jv, hj⟩ : Fin 57) = ⟨30, by omega⟩ := Fin.ext hjv
          have hab : abIdx iv jv = 2 := by subst hiv; subst hjv; rfl
          rw [hab, hi_eq, hj_eq, ← hrok.2.2.2]
          exact slopeIv_planarPath_one_mem S57_pos pts57X pts57Z pts57Z_strictMono
            (by decide) hrok.2.2.1
      · simp only [hj30, ↓reduceIte]
        have hj31 : 31 ≤ jv := by omega
        have hrok := rho57_AU_ok ⟨jv - 31, by omega⟩ ⟨iv - 28, by omega⟩
        have hieq : (⟨iv, hi⟩ : Fin 57) = ⟨28 + (iv - 28), by omega⟩ := Fin.ext (by dsimp; omega)
        have hjeq : (⟨jv, hj⟩ : Fin 57) = ⟨31 + (jv - 31), by omega⟩ := Fin.ext (by dsimp; omega)
        rw [← hrok.2, hieq, hjeq]
        exact slopeIv_planarPath_one_mem S57_pos pts57X pts57Z pts57Z_strictMono
          (show (⟨28 + (iv - 28), by omega⟩ : Fin 57) < ⟨31 + (jv - 31), by omega⟩ from
            Fin.mk_lt_mk.mpr (by omega))
          hrok.1
    · simp only [hi28, hi30, ↓reduceIte]
      rw [planarSlope_eq_zero_of_x_zero _
        (x57Path_one_ax ⟨iv, hi⟩ (by dsimp; omega) (by dsimp; omega) (by dsimp; omega))
        (x57Path_one_ax ⟨jv, hj⟩ (by dsimp; omega) (by dsimp; omega) (by dsimp; omega))]
      exact FpIv.zero_mem S57

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
private lemma gauss57_eq :
    gaussDetIv S57 57 ((List.finRange 57).map (polyRowFastIv S57 c57Lit)) (FpIv.ofInt S57 1) =
      (true, det57_cert) := by
  decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private lemma den57_eq :
    denFoldIv S57 c57Lit (activePairs 57 pts57X) = den57_cert := by
  decide

private lemma cert57_bounds :
    det57_cert.hi < 0 ∧ -den57_cert.lo < det57_cert.lo := by
  decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private lemma den63_eq :
    denFoldIv S63 c63Lit (activePairs 63 pts63X) = den63_cert := by
  decide

private lemma cert63_bounds :
    det2_63_cert.hi < 0 ∧ -den63_cert.lo < det2_63_cert.lo := by
  decide

lemma not_linearIndependent_of_atiyahDet_zero {n : ℕ} (hn : 1 ≤ n)
    (x : DistinctPoints n) (h0 : atiyahDet x = 0) :
    ¬ LinearIndependent ℂ (fun i : Fin n =>
        atiyahPoly (fun u v => canonicalSpinor (unitDir (x.1 u) (x.1 v))) i) :=
  not_linearIndependent_of_atiyahDetOfSpinors_eq_zero hn
    (atiyahDen_unit_ne_zero (fun i j hij => unitDir_norm_sq (x.2 i j hij))
      (fun i j hij => unitDir_ne_swap (x.2 i j hij))
      (fun i j hij => isPosSpinor_ne_zero (isPosSpinor_canonicalSpinor (unitDir_norm_sq (x.2 i j hij))))
      (fun i j hij => (isPosSpinor_canonicalSpinor (unitDir_norm_sq (x.2 i j hij))).2))
    h0

lemma x57Path_hy (s : ℝ) (i : Fin 57) : (x57Path s).1 i 1 = 0 := rfl

lemma x57Path_hz (s : ℝ) : StrictMono (fun i => (x57Path s).1 i 2) :=
  fun _ _ h => Int.cast_lt.mpr (pts57Z_strictMono h)

private lemma x57Path_zero_det : atiyahDet (x57Path 0) = 1 := by
  simp [x57Path, planarPath_zero_eq_one]

private lemma x57Path_cont_re : Continuous (fun s => (atiyahDet (x57Path s)).re) :=
  continuous_planarPath_re pts57X pts57Z pts57Z_strictMono

private lemma x57Path_det_eq (s : ℝ) :
    atiyahDet (x57Path s) = (((planarMat (x57Path s).1).det / planarDen (x57Path s).1 : ℝ) : ℂ) :=
  atiyahDet_eq_planarMat_div (x57Path s) (x57Path_hy s) (x57Path_hz s)

section ShieldPartB
attribute [local irreducible] Matrix.det planarMat planarDen atiyahDet S57 S63
  pts57X pts57Z x57Path c57Lit c63Lit det57_cert den57_cert det2_63_cert den63_cert

theorem x57Path_one_re_neg_and_norm_lt_one :
    (atiyahDet (x57Path 1)).im = 0 ∧ (atiyahDet (x57Path 1)).re < 0 ∧
      ‖atiyahDet (x57Path 1)‖ < 1 := by
  have hy := x57Path_hy 1
  have hz := x57Path_hz 1
  have hmat : MatFpMem S57 57 ((List.finRange 57).map (polyRowFastIv S57 c57Lit))
      (planarMat (x57Path 1).1) :=
    planarMat_matFpMem_polyRowFastIv (by decide) S57_pos c57Lit_mem
  have hdet : FpIv.FpMem S57 det57_cert (planarMat (x57Path 1).1).det := by
    have hg := gaussDetIv_mem S57_pos gauss57_eq (FpIv.ofInt_mem S57 1) hmat
    simpa [one_mul] using hg
  have hden : (den57_cert.lo : ℝ) ≤ (S57 : ℝ) * planarDen (x57Path 1).1 := by
    rw [← den57_eq]
    have hap := activePairs_valid 57 pts57X
    exact denFoldIv_lo_le_planarDen S57_pos hap.1 hap.2 c57Lit_mem
  exact planar_atiyahDet_neg_and_norm_lt_one_of_fpMem S57_pos hy hz hdet hden
    cert57_bounds.1 cert57_bounds.2

/-- Lowered finite threshold (`n = 57`, `K = 3` positive-`x` points) planar witness directly
violating Atiyah–Sutcliffe Conjecture 2 with `-1 < D_57 < 0`. -/
theorem exists_planar_57_violating_conjecture_2 :
    ∃ x : DistinctPoints 57, (atiyahDet x).im = 0 ∧ (atiyahDet x).re < 0 ∧ ‖atiyahDet x‖ < 1 :=
  ⟨x57Path 1, x57Path_one_re_neg_and_norm_lt_one⟩

/-- Lowered finite threshold (`n = 57`) planar witness where Atiyah's determinant vanishes (`D_57(x₀) = 0`)
and the 57 Atiyah polynomials are linearly dependent. -/
theorem exists_planar_57_atiyahDet_zero :
    ∃ x : DistinctPoints 57,
      atiyahDet x = 0 ∧
      ¬ LinearIndependent ℂ (fun i : Fin 57 =>
          atiyahPoly (fun u v => canonicalSpinor (unitDir (x.1 u) (x.1 v))) i) := by
  let f : ℝ → ℝ := fun s => (atiyahDet (x57Path s)).re
  have hcont : ContinuousOn f (Set.Icc (0 : ℝ) 1) := x57Path_cont_re.continuousOn
  have hf0 : f 0 = 1 := by
    change (atiyahDet (x57Path 0)).re = 1
    rw [x57Path_zero_det]; simp
  have hf1 : f 1 < 0 := by
    change (atiyahDet (x57Path 1)).re < 0
    exact x57Path_one_re_neg_and_norm_lt_one.2.1
  have hmem : (0 : ℝ) ∈ Set.Icc (f 1) (f 0) := ⟨hf1.le, by linarith [hf0]⟩
  obtain ⟨s₀, _, hs₀⟩ := intermediate_value_Icc' zero_le_one hcont hmem
  have hreal := x57Path_det_eq s₀
  have hdet0 : atiyahDet (x57Path s₀) = 0 := by
    have hre0 : ((planarMat (x57Path s₀).1).det / planarDen (x57Path s₀).1 : ℝ) = 0 := by
      have hs0' : (atiyahDet (x57Path s₀)).re = 0 := hs₀
      rw [hreal, Complex.ofReal_re] at hs0'
      exact hs0'
    rw [hreal, hre0, Complex.ofReal_zero]
  exact ⟨x57Path s₀, hdet0, not_linearIndependent_of_atiyahDet_zero (by omega) (x57Path s₀) hdet0⟩

/-- Direct integer endpoint certification that `|D_63(x63Path 1)| < 1` (without needing IVT). -/
theorem x63Path_one_norm_lt_one : ‖atiyahDet (x63Path 1)‖ < 1 := by
  have hy : ∀ i, (x63Path 1).1 i 1 = 0 := fun _ => rfl
  have hz : StrictMono (fun i => (x63Path 1).1 i 2) :=
    fun _ _ h => Int.cast_lt.mpr (pts63Z_strictMono h)
  have hden : (den63_cert.lo : ℝ) ≤ (S63 : ℝ) * planarDen (x63Path 1).1 := by
    rw [← den63_eq]
    have hap := activePairs_valid 63 pts63X
    exact denFoldIv_lo_le_planarDen S63_pos hap.1 hap.2 c63Lit_mem
  exact planar_atiyahDet_norm_lt_one_of_fpMem S63_pos hy hz x63Path_one_mat_det_fpMem hden
    cert63_bounds.1 cert63_bounds.2

end ShieldPartB

end Planar57AndDirect63

end KernelGaussDet

/-! ## Part C: Genuine Non-Coplanar 3D Disproofs at $n = 5$ and $n = 59$ -/

section NonCoplanar3DDisproofs

/-- Coplanarity predicate on $C_n(\mathbb{R}^3)$: all $n$ points lie in a common affine plane
$a x + b y + c z = d$ with $(a, b, c) \neq (0, 0, 0)$. -/
def IsCoplanar {n : ℕ} (x : DistinctPoints n) : Prop :=
  ∃ (normal : Fin 3 → ℝ) (d : ℝ),
    (normal 0 ≠ 0 ∨ normal 1 ≠ 0 ∨ normal 2 ≠ 0) ∧
    ∀ i : Fin n, normal 0 * x.1 i 0 + normal 1 * x.1 i 1 + normal 2 * x.1 i 2 = d

lemma pauliDot_yRefl (v : Fin 3 → ℝ) :
    pauliDot ![v 0, -v 1, v 2] = (starRingEnd ℂ).mapMatrix (pauliDot v) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliDot]

lemma pauliDot_mulVec_conj_yRefl {v : Fin 3 → ℝ} {ψ : Fin 2 → ℂ}
    (h : (pauliDot v).mulVec ψ = ψ) :
    (pauliDot ![v 0, -v 1, v 2]).mulVec (fun k => starRingEnd ℂ (ψ k)) =
      (fun k => starRingEnd ℂ (ψ k)) := by
  ext k
  have hk := congr_arg (starRingEnd ℂ) (congr_fun h k)
  rw [Matrix.mulVec, dotProduct] at hk ⊢
  simp only [map_sum, map_mul] at hk
  rw [← hk]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [pauliDot_yRefl v]
  rfl

lemma omega_conj (ψ φ : Fin 2 → ℂ) :
    omega (fun k => starRingEnd ℂ (ψ k)) (fun k => starRingEnd ℂ (φ k)) =
      starRingEnd ℂ (omega ψ φ) := by
  simp [omega]

theorem atiyahDetOfSpinors_im_eq_zero_of_yZero {n : ℕ}
    (u : Fin n → Fin n → Fin 3 → ℝ)
    (hu_norm : ∀ i j, i ≠ j → u i j 0 ^ 2 + u i j 1 ^ 2 + u i j 2 ^ 2 = 1)
    (hu_ne : ∀ i j, i ≠ j → u i j ≠ u j i)
    (hu_y : ∀ i j, i ≠ j → u i j 1 = 0) :
    (atiyahDetOfSpinors (fun i j => canonicalSpinor (u i j))).im = 0 := by
  let ψ0 := fun i j => canonicalSpinor (u i j)
  let φ := fun i j k => starRingEnd ℂ (ψ0 i j k)
  have hφ_ne : ∀ i j, i ≠ j → φ i j 0 ≠ 0 ∨ φ i j 1 ≠ 0 := by
    intro i j hij
    simpa [φ] using isPosSpinor_ne_zero (isPosSpinor_canonicalSpinor (hu_norm i j hij))
  have hφ_mul : ∀ i j, i ≠ j → (pauliDot (u i j)).mulVec (φ i j) = φ i j := by
    intro i j hij
    have hy0 : ![u i j 0, -u i j 1, u i j 2] = u i j := by
      ext m
      fin_cases m
      · rfl
      · simp [hu_y i j hij]
      · rfl
    rw [← hy0]
    exact pauliDot_mulVec_conj_yRefl (isPosSpinor_canonicalSpinor (hu_norm i j hij)).2
  have heq := atiyahDetOfSpinors_eq_of_unitSpinors u hu_norm hu_ne φ hφ_ne hφ_mul
  have hpoly : ∀ i, atiyahPoly φ i = (atiyahPoly ψ0 i).map (starRingEnd ℂ) := by
    intro i
    simp only [atiyahPoly, Polynomial.map_prod, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.map_X]
    rfl
  have hmat : atiyahMat φ = (starRingEnd ℂ).mapMatrix (atiyahMat ψ0) := by
    ext i k
    simp [atiyahMat, hpoly i, Polynomial.coeff_map]
  have hdet : (atiyahMat φ).det = starRingEnd ℂ (atiyahMat ψ0).det := by
    rw [hmat, ← RingHom.map_det]
  have hden : atiyahDen φ = starRingEnd ℂ (atiyahDen ψ0) := by
    simp only [atiyahDen, map_prod]
    refine Finset.prod_congr rfl fun e _ => ?_
    exact omega_conj (ψ0 e.1.1 e.1.2) (ψ0 e.1.2 e.1.1)
  have hconj : starRingEnd ℂ (atiyahDetOfSpinors ψ0) = atiyahDetOfSpinors ψ0 := by
    calc
      starRingEnd ℂ (atiyahDetOfSpinors ψ0)
        = (starRingEnd ℂ (atiyahMat ψ0).det) / (starRingEnd ℂ (atiyahDen ψ0)) := by
            simp [atiyahDetOfSpinors]
      _ = (atiyahMat φ).det / atiyahDen φ := by rw [← hdet, ← hden]
      _ = atiyahDetOfSpinors ψ0 := heq.symm
  exact Complex.conj_eq_iff_im.mp hconj

theorem atiyahDetOfSpinors_im_eq_zero_of_lastSwap_yRefl {n : ℕ}
    (u : Fin (n + 2) → Fin (n + 2) → Fin 3 → ℝ)
    (hu_norm : ∀ i j, i ≠ j → u i j 0 ^ 2 + u i j 1 ^ 2 + u i j 2 ^ 2 = 1)
    (hu_ne : ∀ i j, i ≠ j → u i j ≠ u j i)
    (hu_sym : ∀ i j, i ≠ j →
      let a₀ : Fin (n + 2) := ⟨n, by omega⟩
      let a₁ : Fin (n + 2) := ⟨n + 1, by omega⟩
      let σ := Equiv.swap a₀ a₁
      u (σ i) (σ j) = ![u i j 0, -u i j 1, u i j 2]) :
    (atiyahDetOfSpinors (fun i j => canonicalSpinor (u i j))).im = 0 := by
  let a₀ : Fin (n + 2) := ⟨n, by omega⟩
  let a₁ : Fin (n + 2) := ⟨n + 1, by omega⟩
  let σ : Equiv.Perm (Fin (n + 2)) := Equiv.swap a₀ a₁
  have ha_ne : a₀ ≠ a₁ := fun h => by
    have := congr_arg Fin.val h; dsimp [a₀, a₁] at this; omega
  have hσ_inv : ∀ i, σ (σ i) = i := fun i => Equiv.swap_apply_self a₀ a₁ i
  let ψ0 := fun i j => canonicalSpinor (u i j)
  let φ := fun i j k => starRingEnd ℂ (ψ0 (σ i) (σ j) k)
  have hφ_ne : ∀ i j, i ≠ j → φ i j 0 ≠ 0 ∨ φ i j 1 ≠ 0 := by
    intro i j hij
    have hσne : σ i ≠ σ j := σ.injective.ne hij
    simpa [φ] using isPosSpinor_ne_zero (isPosSpinor_canonicalSpinor (hu_norm (σ i) (σ j) hσne))
  have hφ_mul : ∀ i j, i ≠ j → (pauliDot (u i j)).mulVec (φ i j) = φ i j := by
    intro i j hij
    have hσne : σ i ≠ σ j := σ.injective.ne hij
    have hback := hu_sym (σ i) (σ j) hσne
    dsimp only at hback
    change u (σ (σ i)) (σ (σ j)) = ![u (σ i) (σ j) 0, -u (σ i) (σ j) 1, u (σ i) (σ j) 2] at hback
    rw [hσ_inv i, hσ_inv j] at hback
    rw [hback]
    exact pauliDot_mulVec_conj_yRefl (isPosSpinor_canonicalSpinor (hu_norm (σ i) (σ j) hσne)).2
  have heq := atiyahDetOfSpinors_eq_of_unitSpinors u hu_norm hu_ne φ hφ_ne hφ_mul
  have hpoly : ∀ i, atiyahPoly φ i = (atiyahPoly ψ0 (σ i)).map (starRingEnd ℂ) := by
    intro i
    simp only [atiyahPoly, Polynomial.map_prod, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.map_X]
    refine Finset.prod_bij (fun j _ => σ j) ?_ ?_ ?_ ?_
    · intro j hj
      exact Finset.mem_erase.mpr ⟨σ.injective.ne (Finset.mem_erase.mp hj).1, Finset.mem_univ _⟩
    · intro j₁ _ j₂ _ hj; exact σ.injective hj
    · intro k hk
      refine ⟨σ k, Finset.mem_erase.mpr ⟨fun heq' => ?_, Finset.mem_univ _⟩, hσ_inv k⟩
      have h' := congr_arg σ heq'
      rw [hσ_inv k] at h'
      exact (Finset.mem_erase.mp hk).1 h'
    · intro j _; rfl
  have hmat : atiyahMat φ = ((starRingEnd ℂ).mapMatrix (atiyahMat ψ0)).submatrix σ id := by
    ext i k
    simp [atiyahMat, hpoly i, Polynomial.coeff_map]
  have hdet : (atiyahMat φ).det = -(starRingEnd ℂ (atiyahMat ψ0).det) := by
    rw [hmat, ← Matrix.det_transpose ((starRingEnd ℂ).mapMatrix (atiyahMat ψ0) |>.submatrix σ id)]
    have hT : (((starRingEnd ℂ).mapMatrix (atiyahMat ψ0)).submatrix σ id)ᵀ =
        (((starRingEnd ℂ).mapMatrix (atiyahMat ψ0))ᵀ).submatrix id σ := by
      ext k i; rfl
    rw [hT, Matrix.det_permute', Equiv.Perm.sign_swap ha_ne, Matrix.det_transpose,
      ← RingHom.map_det]
    simp
  let swapOrd : { p : Fin (n + 2) × Fin (n + 2) // p.1 < p.2 } →
      { p : Fin (n + 2) × Fin (n + 2) // p.1 < p.2 } := fun e =>
    if hlt : σ e.1.1 < σ e.1.2 then ⟨(σ e.1.1, σ e.1.2), hlt⟩
    else ⟨(σ e.1.2, σ e.1.1), lt_of_le_of_ne (not_lt.mp hlt) (σ.injective.ne e.2.ne.symm)⟩
  have hswap_inv : ∀ e, swapOrd (swapOrd e) = e := by
    intro ⟨⟨i, j⟩, hij⟩
    dsimp only [swapOrd]
    by_cases hlt : σ i < σ j
    · simp only [hlt, ↓reduceDIte]
      have hback : σ (σ i) < σ (σ j) := by rw [hσ_inv i, hσ_inv j]; exact hij
      simp only [hback, ↓reduceDIte]
      ext <;> dsimp <;> rw [hσ_inv]
    · simp only [hlt, ↓reduceDIte]
      have hback : ¬ σ (σ j) < σ (σ i) := by rw [hσ_inv i, hσ_inv j]; exact not_lt.mpr hij.le
      simp only [hback, ↓reduceDIte]
      ext <;> dsimp <;> rw [hσ_inv]
  let τ : { p : Fin (n + 2) × Fin (n + 2) // p.1 < p.2 } ≃
      { p : Fin (n + 2) × Fin (n + 2) // p.1 < p.2 } :=
    ⟨swapOrd, swapOrd, hswap_inv, hswap_inv⟩
  let e₀ : { p : Fin (n + 2) × Fin (n + 2) // p.1 < p.2 } :=
    ⟨(a₀, a₁), Fin.mk_lt_mk.mpr (show n < n + 1 by omega)⟩
  have hlt_iff_ne : ∀ e : { p : Fin (n + 2) × Fin (n + 2) // p.1 < p.2 },
      e ≠ e₀ → σ e.1.1 < σ e.1.2 := by
    intro ⟨⟨i, j⟩, hij⟩ hne
    have hlt : i.1 < j.1 := hij
    have hi_le : i.1 ≤ n + 1 := Nat.lt_succ_iff.mp i.2
    have hj_le : j.1 ≤ n + 1 := Nat.lt_succ_iff.mp j.2
    by_cases hin : i.1 < n
    · have hσi : σ i = i := Equiv.swap_apply_of_ne_of_ne
        (Fin.ne_of_val_ne (by show i.1 ≠ n; omega))
        (Fin.ne_of_val_ne (by show i.1 ≠ n + 1; omega))
      by_cases hj0 : j = a₀
      · subst hj0; rw [hσi, Equiv.swap_apply_left]; exact Fin.mk_lt_mk.mpr (by show i.1 < n + 1; omega)
      · by_cases hj1 : j = a₁
        · subst hj1; rw [hσi, Equiv.swap_apply_right]; exact Fin.mk_lt_mk.mpr (by show i.1 < n; omega)
        · rw [hσi, Equiv.swap_apply_of_ne_of_ne hj0 hj1]; exact hij
    · have hin_eq : i = a₀ := Fin.ext (by show i.1 = n; omega)
      have hjn_eq : j = a₁ := Fin.ext (by show j.1 = n + 1; omega)
      exact absurd (Subtype.ext (Prod.ext hin_eq hjn_eq)) hne
  have hτ_e0 : τ e₀ = e₀ := by
    change swapOrd e₀ = e₀
    dsimp only [swapOrd, e₀]
    have hnot : ¬ σ a₀ < σ a₁ := by
      rw [Equiv.swap_apply_left, Equiv.swap_apply_right]
      exact not_lt.mpr (Fin.mk_le_mk.mpr (by show n ≤ n + 1; omega))
    simp only [hnot, ↓reduceDIte]
    refine Subtype.ext (Prod.ext ?_ ?_)
    · exact Equiv.swap_apply_right a₀ a₁
    · exact Equiv.swap_apply_left a₀ a₁
  have hden : atiyahDen φ = -(starRingEnd ℂ (atiyahDen ψ0)) := by
    let g : { p : Fin (n + 2) × Fin (n + 2) // p.1 < p.2 } → ℂ := fun e =>
      starRingEnd ℂ (omega (ψ0 e.1.1 e.1.2) (ψ0 e.1.2 e.1.1))
    have hterm : ∀ e, omega (φ e.1.1 e.1.2) (φ e.1.2 e.1.1) =
        if e = e₀ then -g (τ e) else g (τ e) := by
      intro e
      dsimp only [φ]
      rw [omega_conj]
      by_cases he : e = e₀
      · subst he
        simp only [↓reduceIte, hτ_e0, g, e₀]
        rw [Equiv.swap_apply_left, Equiv.swap_apply_right, omega_swap, map_neg]
      · have hσlt := hlt_iff_ne e he
        have hτe : τ e = ⟨(σ e.1.1, σ e.1.2), hσlt⟩ := by
          change swapOrd e = _; dsimp only [swapOrd]; simp only [hσlt, ↓reduceDIte]
        simp only [he, ↓reduceIte, hτe, g]
    have hprod_eq : atiyahDen φ =
        ∏ e : { p : Fin (n + 2) × Fin (n + 2) // p.1 < p.2 },
          (if e = e₀ then -g (τ e) else g (τ e)) :=
      Finset.prod_congr rfl fun e _ => hterm e
    rw [hprod_eq, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ e₀)]
    have hrest : (∏ e ∈ Finset.univ.erase e₀, if e = e₀ then -g (τ e) else g (τ e)) =
        ∏ e ∈ Finset.univ.erase e₀, g (τ e) := by
      refine Finset.prod_congr rfl fun e he => ?_
      simp [(Finset.mem_erase.mp he).1]
    simp only [↓reduceIte]
    rw [hrest, neg_mul]
    rw [Finset.mul_prod_erase Finset.univ (fun e => g (τ e)) (Finset.mem_univ e₀)]
    rw [Fintype.prod_equiv τ (fun e => g (τ e)) g fun _ => rfl]
    simp [atiyahDen, g, map_prod]
  have hconj : starRingEnd ℂ (atiyahDetOfSpinors ψ0) = atiyahDetOfSpinors ψ0 := by
    calc
      starRingEnd ℂ (atiyahDetOfSpinors ψ0)
        = (-(starRingEnd ℂ (atiyahMat ψ0).det)) / (-(starRingEnd ℂ (atiyahDen ψ0))) := by
            simp [atiyahDetOfSpinors]
      _ = (atiyahMat φ).det / atiyahDen φ := by rw [← hdet, ← hden]
      _ = atiyahDetOfSpinors ψ0 := heq.symm
  exact Complex.conj_eq_iff_im.mp hconj

/-- Perturbed 5-point configuration lifting point `0` of `x5` to `y = δ`. -/
noncomputable def x5Perturb (δ : ℝ) : DistinctPoints 5 :=
  ⟨fun i => if i = 0 then ![1198773, δ, -320821] else x5.1 i, by
    intro i j hij heq
    have hz := congr_fun heq 2
    dsimp only at hz
    have hzi : (if i = 0 then ![1198773, δ, -320821] else x5.1 i) 2 = (pts5Z i : ℝ) := by
      by_cases hi : i = 0
      · subst hi; simp [pts5Z]
      · simp [hi, x5, planarPath]
    have hzj : (if j = 0 then ![1198773, δ, -320821] else x5.1 j) 2 = (pts5Z j : ℝ) := by
      by_cases hj : j = 0
      · subst hj; simp [pts5Z]
      · simp [hj, x5, planarPath]
    rw [hzi, hzj] at hz
    exact hij (pts5Z_strictMono.injective (Int.cast_injective hz))⟩

lemma not_isCoplanar_x5Perturb {δ : ℝ} (hδ : δ ≠ 0) : ¬ IsCoplanar (x5Perturb δ) := by
  rintro ⟨normal, d, hne, hplane⟩
  have h0 := hplane 0
  have h1 := hplane 1
  have h2 := hplane 2
  have h3 := hplane 3
  have hp00 : (x5Perturb δ).1 0 0 = 1198773 := by simp [x5Perturb]
  have hp01 : (x5Perturb δ).1 0 1 = δ := by simp [x5Perturb]
  have hp02 : (x5Perturb δ).1 0 2 = -320821 := by simp [x5Perturb]
  have hp10 : (x5Perturb δ).1 1 0 = 212773 := by simp [x5Perturb, x5, planarPath, pts5X]
  have hp11 : (x5Perturb δ).1 1 1 = 0 := by simp [x5Perturb, x5, planarPath]
  have hp12 : (x5Perturb δ).1 1 2 = -58745 := by simp [x5Perturb, x5, planarPath, pts5Z]
  have hp20 : (x5Perturb δ).1 2 0 = -55 := by simp [x5Perturb, x5, planarPath, pts5X]
  have hp21 : (x5Perturb δ).1 2 1 = 0 := by simp [x5Perturb, x5, planarPath]
  have hp22 : (x5Perturb δ).1 2 2 = 3 := by simp [x5Perturb, x5, planarPath, pts5Z]
  have hp30 : (x5Perturb δ).1 3 0 = -56 := by simp [x5Perturb, x5, planarPath, pts5X]
  have hp31 : (x5Perturb δ).1 3 1 = 0 := by simp [x5Perturb, x5, planarPath]
  have hp32 : (x5Perturb δ).1 3 2 = 4 := by simp [x5Perturb, x5, planarPath, pts5Z]
  rw [hp00, hp01, hp02] at h0
  rw [hp10, hp11, hp12] at h1
  rw [hp20, hp21, hp22] at h2
  rw [hp30, hp31, hp32] at h3
  have hn0 : normal 0 = 0 := by linarith
  have hn2 : normal 2 = 0 := by linarith
  have hd0 : d = 0 := by linarith
  have hmul : normal 1 * δ = 0 := by linarith
  have hn1 : normal 1 = 0 := (mul_eq_zero.mp hmul).resolve_right hδ
  rcases hne with h | h | h
  · exact h hn0
  · exact h hn1
  · exact h hn2

/-- **Sharp Minimal Non-Coplanar 3D Disproof of Conjecture 3** at `n = 5`. -/
theorem exists_five_noncoplanar_points_violating_conjecture_3 :
    ∃ x : DistinctPoints 5, ¬ IsCoplanar x ∧
      ‖atiyahDet x‖ ^ (5 - 2) < ∏ k : Fin 5, ‖atiyahDet (deletePoint x k)‖ := by
  let l := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  have htend_full : Tendsto (fun δ => (atiyahDet (x5Perturb δ))) l (nhds (atiyahDet x5)) := by
    refine tendsto_atiyahDet_of_tendsto x5Perturb x5 fun i => ?_
    rw [tendsto_pi_nhds]; intro c
    by_cases hi : i = 0
    · subst hi
      fin_cases c
      · simp [x5Perturb, x5, planarPath, pts5X]
      · have hid : Tendsto (fun δ : ℝ => δ) l (nhds 0) :=
          continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
        simpa [x5Perturb, x5, planarPath] using hid
      · simp [x5Perturb, x5, planarPath, pts5Z]
    · simp [x5Perturb, hi]
  have htend_lhs : Tendsto (fun δ => ‖atiyahDet (x5Perturb δ)‖ ^ (5 - 2)) l
      (nhds (‖atiyahDet x5‖ ^ (5 - 2))) :=
    (htend_full.norm).pow 3
  have htend_del : ∀ k : Fin 5, Tendsto (fun δ => ‖atiyahDet (deletePoint (x5Perturb δ) k)‖) l
      (nhds ‖atiyahDet (deletePoint x5 k)‖) := by
    intro k
    refine (tendsto_atiyahDet_of_tendsto (fun δ => deletePoint (x5Perturb δ) k)
      (deletePoint x5 k) fun i => ?_).norm
    rw [tendsto_pi_nhds]; intro c
    by_cases hi : k.succAbove i = 0
    · simp only [deletePoint, x5Perturb, hi, ↓reduceIte]
      fin_cases c
      · simp [x5, planarPath, pts5X]
      · have hid : Tendsto (fun δ : ℝ => δ) l (nhds 0) :=
          continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
        simpa [x5, planarPath] using hid
      · simp [x5, planarPath, pts5Z]
    · simp [deletePoint, x5Perturb, hi]
  have htend_rhs : Tendsto (fun δ => ∏ k : Fin 5, ‖atiyahDet (deletePoint (x5Perturb δ) k)‖) l
      (nhds (∏ k : Fin 5, ‖atiyahDet (deletePoint x5 k)‖)) := by
    simp only [Fin.prod_univ_five]
    exact ((((htend_del 0).mul (htend_del 1)).mul (htend_del 2)).mul (htend_del 3)).mul (htend_del 4)
  have hev_lt : ∀ᶠ δ in l,
      ‖atiyahDet (x5Perturb δ)‖ ^ (5 - 2) < ∏ k : Fin 5, ‖atiyahDet (deletePoint (x5Perturb δ) k)‖ :=
    htend_lhs.eventually_lt htend_rhs x5_violates_conjecture_3
  have hev_pos : ∀ᶠ δ : ℝ in l, 0 < δ := self_mem_nhdsWithin
  obtain ⟨δ, hδ_lt, hδ_pos⟩ := (hev_lt.and hev_pos).exists
  exact ⟨x5Perturb δ, not_isCoplanar_x5Perturb hδ_pos.ne', hδ_lt⟩

/-- Append an out-of-plane mirror pair `(0, ±1, H)` onto an `(y = 0)` planar configuration `x`. -/
def mirrorPairExt {n : ℕ} (x : DistinctPoints n) (hy : ∀ i, x.1 i 1 = 0) (H : ℝ) :
    DistinctPoints (n + 2) :=
  ⟨fun i =>
    if h : i.1 < n then x.1 ⟨i.1, h⟩
    else if i.1 = n then ![0, 1, H]
    else ![0, -1, H], by
    intro i j hij heq
    have hyc := congr_fun heq 1
    by_cases hi : i.1 < n <;> by_cases hj : j.1 < n
    · simp only [hi, hj, ↓reduceDIte] at heq
      have hinj : (⟨i.1, hi⟩ : Fin n) = ⟨j.1, hj⟩ := by
        by_contra hne; exact x.2 _ _ hne heq
      have hval : i.1 = j.1 := congr_arg (@Fin.val n) hinj
      exact hij (Fin.ext hval)
    · by_cases hjn : j.1 = n <;> simp [hi, hj, hy _, hjn] at hyc
    · by_cases hin : i.1 = n <;> simp [hi, hj, hy _, hin] at hyc
    · have hi_eq : i.1 = n ∨ i.1 = n + 1 := by omega
      have hj_eq : j.1 = n ∨ j.1 = n + 1 := by omega
      rcases hi_eq with h1 | h1 <;> rcases hj_eq with h2 | h2
      · exact hij (Fin.ext (h1.trans h2.symm))
      · have hne : j.1 ≠ n := by omega
        simp [hj, h1, hne] at hyc
        norm_num at hyc
      · have hne : i.1 ≠ n := by omega
        simp [hi, hne, h2] at hyc
        norm_num at hyc
      · exact hij (Fin.ext (h1.trans h2.symm))⟩

theorem atiyahDet_mirrorPairExt_im_eq_zero {n : ℕ} (x : DistinctPoints n)
    (hy : ∀ i, x.1 i 1 = 0) (H : ℝ) :
    (atiyahDet (mirrorPairExt x hy H)).im = 0 := by
  let p := mirrorPairExt x hy H
  refine atiyahDetOfSpinors_im_eq_zero_of_lastSwap_yRefl
    (fun i j => unitDir (p.1 i) (p.1 j))
    (fun i j hij => unitDir_norm_sq (p.2 i j hij))
    (fun i j hij => unitDir_ne_swap (p.2 i j hij)) ?_
  intro i j _
  let a₀ : Fin (n + 2) := ⟨n, by omega⟩
  let a₁ : Fin (n + 2) := ⟨n + 1, by omega⟩
  let σ := Equiv.swap a₀ a₁
  have hp_sym : ∀ k : Fin (n + 2), p.1 (σ k) = ![p.1 k 0, -p.1 k 1, p.1 k 2] := by
    intro k
    by_cases hk : k.1 < n
    · have hk0 : k ≠ a₀ := Fin.ne_of_val_ne (by show k.1 ≠ n; omega)
      have hk1 : k ≠ a₁ := Fin.ne_of_val_ne (by show k.1 ≠ n + 1; omega)
      have hσk : σ k = k := Equiv.swap_apply_of_ne_of_ne hk0 hk1
      rw [hσk]
      ext c; fin_cases c <;> simp [p, mirrorPairExt, hk, hy ⟨k.1, hk⟩]
    · by_cases hkn : k = a₀
      · subst hkn
        rw [Equiv.swap_apply_left]
        ext c; fin_cases c <;> simp [p, mirrorPairExt, a₀, a₁]
      · have hk1 : k = a₁ := Fin.ext (by show k.1 = n + 1; have := k.2; have : k.1 ≠ n := fun h => hkn (Fin.ext h); omega)
        subst hk1
        rw [Equiv.swap_apply_right]
        ext c; fin_cases c <;> simp [p, mirrorPairExt, a₀, a₁]
  have hnorm_eq : euclidNorm (fun c => p.1 (σ j) c - p.1 (σ i) c) =
      euclidNorm (fun c => p.1 j c - p.1 i c) := by
    simp only [euclidNorm, hp_sym]
    congr 1; simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]; ring
  ext c
  dsimp only [unitDir]
  rw [hnorm_eq, hp_sym i, hp_sym j]
  fin_cases c
  · simp
  · simp; ring
  · simp

private lemma pts57_val0x : pts57X ⟨0, by omega⟩ = 0 := by decide
private lemma pts57_val0z : pts57Z ⟨0, by omega⟩ = 0 := by decide
private lemma pts57_val1x : pts57X ⟨1, by omega⟩ = 0 := by decide
private lemma pts57_val1z : pts57Z ⟨1, by omega⟩ = 1 := by decide
private lemma pts57_val28x : pts57X ⟨28, by omega⟩ = 14650 := by decide
private lemma pts57_val28z : pts57Z ⟨28, by omega⟩ = 177472 := by decide

private lemma vec3_eval (a b c : ℝ) :
    (![a, b, c] : Fin 3 → ℝ) 0 = a ∧
    (![a, b, c] : Fin 3 → ℝ) 1 = b ∧
    (![a, b, c] : Fin 3 → ℝ) 2 = c := ⟨rfl, rfl, rfl⟩

lemma not_isCoplanar_mirrorPairExt_x57Path {s H : ℝ} (hs : s ≠ 0) :
    ¬ IsCoplanar (mirrorPairExt (x57Path s) (x57Path_hy s) H) := by
  rintro ⟨normal, d, hne, hplane⟩
  have h0 := hplane ⟨0, by omega⟩
  have h1 := hplane ⟨1, by omega⟩
  have h28 := hplane ⟨28, by omega⟩
  have h57 := hplane ⟨57, by omega⟩
  simp only [mirrorPairExt, show (0 : ℕ) < 57 by omega, show (1 : ℕ) < 57 by omega,
    show (28 : ℕ) < 57 by omega, show ¬ (57 : ℕ) < 57 by omega, ↓reduceDIte, ↓reduceIte,
    x57Path, planarPath, pts57_val0x, pts57_val0z, pts57_val1x, pts57_val1z,
    pts57_val28x, pts57_val28z, Int.cast_zero, Int.cast_one, Int.cast_ofNat,
    vec3_eval] at h0 h1 h28 h57
  have hd0 : d = 0 := by linarith
  have hn2 : normal 2 = 0 := by linarith
  have hmul : normal 0 * (s * 14650) = 0 := by linarith
  have hs_ne : s * 14650 ≠ 0 := mul_ne_zero hs (by norm_num)
  have hn0 : normal 0 = 0 := (mul_eq_zero.mp hmul).resolve_right hs_ne
  rw [hn0, hn2, hd0] at h57
  have hn1 : normal 1 = 0 := by linarith
  rcases hne with h | h | h
  · exact h hn0
  · exact h hn1
  · exact h hn2

private lemma tendsto_div_euclidNorm_atTop (num C z0 : ℝ) (_hC : 0 ≤ C) :
    Tendsto (fun H : ℝ => num / Real.sqrt (C + (H - z0) ^ 2))
      atTop (nhds 0) := by
  refine tendsto_const_nhds.div_atTop ?_
  refine Filter.tendsto_atTop.mpr fun B => ?_
  rw [Filter.eventually_atTop]
  refine ⟨z0 + max B 0, fun H hH => ?_⟩
  have hB : max B 0 ≤ H - z0 := by linarith
  have h1 : (max B 0) ^ 2 ≤ C + (H - z0) ^ 2 := by
    have hsq : (max B 0) ^ 2 ≤ (H - z0) ^ 2 := by nlinarith [le_max_right B 0]
    linarith
  exact le_trans (le_max_left B 0) (by simpa [Real.sqrt_sq (le_max_right B 0)] using Real.sqrt_le_sqrt h1)

private lemma tendsto_zdiv_euclidNorm_atTop (C z0 : ℝ) (hC : 0 ≤ C) :
    Tendsto (fun H : ℝ => (H - z0) / Real.sqrt (C + (H - z0) ^ 2))
      atTop (nhds 1) := by
  have ht_id : Tendsto (fun H : ℝ => H - z0) atTop atTop :=
    tendsto_id.atTop_add tendsto_const_nhds
  have h_sq_id : Tendsto (fun H : ℝ => (H - z0) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by omega : 2 ≠ 0)).comp ht_id
  have h_inv_sq : Tendsto (fun H : ℝ => 1 + C / (H - z0) ^ 2) atTop (nhds (1 + 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.div_atTop h_sq_id)
  have h_sqrt : Tendsto (fun H : ℝ => (Real.sqrt (1 + C / (H - z0) ^ 2))⁻¹) atTop (nhds 1) := by
    simpa using (h_inv_sq.sqrt.inv₀ (by norm_num))
  refine h_sqrt.congr' ?_
  rw [Filter.EventuallyEq, Filter.eventually_atTop]
  refine ⟨z0 + 1, fun H hH => ?_⟩
  have hpos : 0 < H - z0 := by linarith
  have hfac : C + (H - z0) ^ 2 = (H - z0) ^ 2 * (1 + C / (H - z0) ^ 2) := by
    field_simp [hpos.ne']; ring
  have hsq : Real.sqrt (C + (H - z0) ^ 2) = (H - z0) * Real.sqrt (1 + C / (H - z0) ^ 2) := by
    rw [hfac, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hpos.le]
  have hspos : 0 < Real.sqrt (1 + C / (H - z0) ^ 2) :=
    Real.sqrt_pos.mpr (by positivity)
  rw [hsq]
  field_simp [hpos.ne', hspos.ne']

theorem tendsto_atiyahDet_mirrorPairExt_atTop {n : ℕ} (x : DistinctPoints n)
    (hy : ∀ i, x.1 i 1 = 0) :
    Tendsto (fun H => atiyahDet (mirrorPairExt x hy H)) atTop (nhds (atiyahDet x)) := by
  let uLim : Fin (n + 2) → Fin (n + 2) → Fin 3 → ℝ := fun i j =>
    if hi : i.1 < n then
      if hj : j.1 < n then unitDir (x.1 ⟨i.1, hi⟩) (x.1 ⟨j.1, hj⟩) else ![0, 0, 1]
    else
      if j.1 < n then ![0, 0, -1] else if i.1 = n then ![0, -1, 0] else ![0, 1, 0]
  have huLim_norm : ∀ i j, i ≠ j → uLim i j 0 ^ 2 + uLim i j 1 ^ 2 + uLim i j 2 ^ 2 = 1 := by
    intro i j hij
    dsimp only [uLim]
    split_ifs with hi hj
    · exact unitDir_norm_sq (x.2 _ _ (fun h => hij (Fin.ext (congr_arg (@Fin.val n) h))))
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  have huLim_ne : ∀ i j, i ≠ j → uLim i j ≠ uLim j i := by
    intro i j hij h
    dsimp only [uLim] at h
    by_cases hi : i.1 < n <;> by_cases hj : j.1 < n
    · simp only [hi, hj, ↓reduceDIte] at h
      exact unitDir_ne_swap (x.2 _ _ (fun he => hij (Fin.ext (congr_arg (@Fin.val n) he)))) h
    · have hz := congr_fun h 2
      simp [hi, hj] at hz
      norm_num at hz
    · have hz := congr_fun h 2
      simp [hi, hj] at hz
      norm_num at hz
    · have hy_c := congr_fun h 1
      have hne_val : i.1 ≠ j.1 := Fin.val_ne_of_ne hij
      have hic : i.1 = n ∨ i.1 = n + 1 := by omega
      have hjc : j.1 = n ∨ j.1 = n + 1 := by omega
      rcases hic with hin | hin <;> rcases hjc with hjn | hjn
      · exact hne_val (hin.trans hjn.symm)
      · simp [hin, hjn] at hy_c; norm_num at hy_c
      · simp [hin, hjn] at hy_c; norm_num at hy_c
      · exact hne_val (hin.trans hjn.symm)
  have h_up : ∀ (i₀ j₀ : Fin (n + 2)), i₀.1 < n → ¬ j₀.1 < n →
      Tendsto (fun H => unitDir ((mirrorPairExt x hy H).1 i₀) ((mirrorPairExt x hy H).1 j₀))
        atTop (nhds ![0, 0, 1]) := by
    intro i₀ j₀ hi₀ hj₀
    rw [tendsto_pi_nhds]; intro c
    let yj : ℝ := if j₀.1 = n then 1 else -1
    let C : ℝ := (0 - x.1 ⟨i₀.1, hi₀⟩ 0) ^ 2 + (yj - 0) ^ 2
    have hC : 0 ≤ C := by positivity
    have hnorm : ∀ H : ℝ,
        euclidNorm (fun k => (mirrorPairExt x hy H).1 j₀ k - (mirrorPairExt x hy H).1 i₀ k) =
          Real.sqrt (C + (H - x.1 ⟨i₀.1, hi₀⟩ 2) ^ 2) := by
      intro H
      unfold euclidNorm
      dsimp only [C]
      congr 1
      by_cases hjn : j₀.1 = n <;> simp [mirrorPairExt, hi₀, hj₀, hjn, yj, hy ⟨i₀.1, hi₀⟩]
    have hsub_c : ∀ H : ℝ, (mirrorPairExt x hy H).1 j₀ c - (mirrorPairExt x hy H).1 i₀ c =
        match c with
        | 0 => -(x.1 ⟨i₀.1, hi₀⟩ 0)
        | 1 => yj
        | 2 => H - x.1 ⟨i₀.1, hi₀⟩ 2 := by
      intro H
      by_cases hjn : j₀.1 = n <;> fin_cases c <;> simp [mirrorPairExt, hi₀, hj₀, hjn, yj, hy ⟨i₀.1, hi₀⟩]
    fin_cases c
    · simp only [unitDir, hnorm, hsub_c]
      exact tendsto_div_euclidNorm_atTop (-(x.1 ⟨i₀.1, hi₀⟩ 0)) C (x.1 ⟨i₀.1, hi₀⟩ 2) hC
    · simp only [unitDir, hnorm, hsub_c]
      exact tendsto_div_euclidNorm_atTop yj C (x.1 ⟨i₀.1, hi₀⟩ 2) hC
    · simp only [unitDir, hnorm, hsub_c]
      exact tendsto_zdiv_euclidNorm_atTop C (x.1 ⟨i₀.1, hi₀⟩ 2) hC
  have htend_u : Tendsto (fun H =>
      atiyahDet (mirrorPairExt x hy H)) atTop
      (nhds (atiyahDetOfSpinors (fun i j => canonicalSpinor (uLim i j)))) := by
    refine tendsto_atiyahDetOfSpinors_unit
      (fun H i j => unitDir ((mirrorPairExt x hy H).1 i) ((mirrorPairExt x hy H).1 j))
      uLim huLim_norm huLim_ne
      (Eventually.of_forall fun H i j hij => unitDir_norm_sq ((mirrorPairExt x hy H).2 i j hij))
      (Eventually.of_forall fun H i j hij => unitDir_ne_swap ((mirrorPairExt x hy H).2 i j hij)) ?_
    intro i j hij
    by_cases hi : i.1 < n <;> by_cases hj : j.1 < n
    · have hu_eq : uLim i j = unitDir (x.1 ⟨i.1, hi⟩) (x.1 ⟨j.1, hj⟩) := by simp [uLim, hi, hj]
      rw [hu_eq]
      have hconst : (fun H => unitDir ((mirrorPairExt x hy H).1 i) ((mirrorPairExt x hy H).1 j)) =
          fun _ => unitDir (x.1 ⟨i.1, hi⟩) (x.1 ⟨j.1, hj⟩) := by
        ext H c; simp [mirrorPairExt, hi, hj]
      rw [hconst]
      exact tendsto_const_nhds
    · have hu_eq : uLim i j = ![0, 0, 1] := by simp [uLim, hi, hj]
      rw [hu_eq]
      exact h_up i j hi hj
    · have hu_eq : uLim i j = -![0, 0, 1] := by ext c; fin_cases c <;> simp [uLim, hi, hj]
      rw [hu_eq]
      have hswap_fn : (fun H => unitDir ((mirrorPairExt x hy H).1 i) ((mirrorPairExt x hy H).1 j)) =
          fun H => -(unitDir ((mirrorPairExt x hy H).1 j) ((mirrorPairExt x hy H).1 i)) := by
        ext H c; exact congr_fun (unitDir_swap _ _) c
      rw [hswap_fn]
      exact (h_up j i hj hi).neg
    · have hic : i.1 = n ∨ i.1 = n + 1 := by omega
      have hjc : j.1 = n ∨ j.1 = n + 1 := by omega
      have hne_val : i.1 ≠ j.1 := Fin.val_ne_of_ne hij
      rcases hic with hin | hin <;> rcases hjc with hjn | hjn
      · exact absurd (hin.trans hjn.symm) hne_val
      · have hconst : ∀ H, unitDir ((mirrorPairExt x hy H).1 i) ((mirrorPairExt x hy H).1 j) =
            ![0, -1, 0] := by
          intro H
          have hnorm2 : euclidNorm (fun k => (mirrorPairExt x hy H).1 j k - (mirrorPairExt x hy H).1 i k) = 2 := by
            unfold euclidNorm
            have hsq : (fun k => (mirrorPairExt x hy H).1 j k - (mirrorPairExt x hy H).1 i k) 0 ^ 2 +
                (fun k => (mirrorPairExt x hy H).1 j k - (mirrorPairExt x hy H).1 i k) 1 ^ 2 +
                (fun k => (mirrorPairExt x hy H).1 j k - (mirrorPairExt x hy H).1 i k) 2 ^ 2 = 2 ^ 2 := by
              simp [mirrorPairExt, hin, hjn]; norm_num
            rw [hsq, Real.sqrt_sq (by norm_num)]
          ext c
          dsimp only [unitDir]
          rw [hnorm2]
          fin_cases c <;> simp [mirrorPairExt, hin, hjn]
          norm_num
        have hu_eq : uLim i j = ![0, -1, 0] := by simp [uLim, hj, hin]
        rw [hu_eq]
        simp_rw [hconst]
        exact tendsto_const_nhds
      · have hconst : ∀ H, unitDir ((mirrorPairExt x hy H).1 i) ((mirrorPairExt x hy H).1 j) =
            ![0, 1, 0] := by
          intro H
          have hnorm2 : euclidNorm (fun k => (mirrorPairExt x hy H).1 j k - (mirrorPairExt x hy H).1 i k) = 2 := by
            unfold euclidNorm
            have hsq : (fun k => (mirrorPairExt x hy H).1 j k - (mirrorPairExt x hy H).1 i k) 0 ^ 2 +
                (fun k => (mirrorPairExt x hy H).1 j k - (mirrorPairExt x hy H).1 i k) 1 ^ 2 +
                (fun k => (mirrorPairExt x hy H).1 j k - (mirrorPairExt x hy H).1 i k) 2 ^ 2 = 2 ^ 2 := by
              simp [mirrorPairExt, hin, hjn]; norm_num
            rw [hsq, Real.sqrt_sq (by norm_num)]
          ext c
          dsimp only [unitDir]
          rw [hnorm2]
          fin_cases c <;> simp [mirrorPairExt, hin, hjn]
        have hu_eq : uLim i j = ![0, 1, 0] := by simp [uLim, hj, hin]
        rw [hu_eq]
        simp_rw [hconst]
        exact tendsto_const_nhds
      · exact absurd (hin.trans hjn.symm) hne_val
  let ψX : Fin n → Fin n → Fin 2 → ℂ := fun i j => canonicalSpinor (unitDir (x.1 i) (x.1 j))
  let ψLim : Fin (n + 2) → Fin (n + 2) → Fin 2 → ℂ := fun i j =>
    if hi : i.1 < n then
      if hj : j.1 < n then ψX ⟨i.1, hi⟩ ⟨j.1, hj⟩ else ![1, 0]
    else
      if j.1 < n then ![0, 1] else if i.1 = n then ![1, -Complex.I] else ![1, Complex.I]
  have hψLim_ne : ∀ i j, i ≠ j → ψLim i j 0 ≠ 0 ∨ ψLim i j 1 ≠ 0 := by
    intro i j hij
    dsimp only [ψLim]
    split_ifs with hi hj
    · exact isPosSpinor_ne_zero (isPosSpinor_canonicalSpinor
        (unitDir_norm_sq (x.2 _ _ (fun h => hij (Fin.ext (congr_arg (@Fin.val n) h))))))
    · left; norm_num
    · right; norm_num
    · left; norm_num
    · left; norm_num
  have hψLim_mul : ∀ i j, i ≠ j → (pauliDot (uLim i j)).mulVec (ψLim i j) = ψLim i j := by
    intro i j hij
    dsimp only [uLim, ψLim]
    split_ifs with hi hj hi_eq
    · exact (isPosSpinor_canonicalSpinor (unitDir_norm_sq (x.2 _ _ (fun h => hij (Fin.ext (congr_arg (@Fin.val n) h)))))).2
    · ext k; fin_cases k <;> simp [Matrix.mulVec, dotProduct, pauliDot]
    · ext k; fin_cases k <;> simp [Matrix.mulVec, dotProduct, pauliDot]
    · ext k; fin_cases k <;> simp [Matrix.mulVec, dotProduct, pauliDot]
    · ext k; fin_cases k <;> simp [Matrix.mulVec, dotProduct, pauliDot]
  have heq_spinor : atiyahDetOfSpinors (fun i j => canonicalSpinor (uLim i j)) =
      atiyahDetOfSpinors ψLim :=
    atiyahDetOfSpinors_eq_of_unitSpinors uLim huLim_norm huLim_ne ψLim hψLim_ne hψLim_mul
  let a₀ : Fin (n + 2) := ⟨n, by omega⟩
  let a₁ : Fin (n + 2) := ⟨n + 1, by omega⟩
  have ha01 : a₀ ≠ a₁ := Fin.ne_of_val_ne (by dsimp [a₀, a₁]; omega)
  have hpoly_lo : ∀ (i₀ : Fin n),
      atiyahPoly ψLim ⟨i₀.1, by omega⟩ = atiyahPoly ψX i₀ := by
    intro i₀
    let i : Fin (n + 2) := ⟨i₀.1, by omega⟩
    have ha0_mem : a₀ ∈ Finset.univ.erase i :=
      Finset.mem_erase.mpr ⟨Fin.ne_of_val_ne (by dsimp [a₀, i]; omega), Finset.mem_univ _⟩
    have ha1_mem : a₁ ∈ (Finset.univ.erase i).erase a₀ :=
      Finset.mem_erase.mpr ⟨ha01.symm, Finset.mem_erase.mpr ⟨Fin.ne_of_val_ne (by dsimp [a₁, i]; omega), Finset.mem_univ _⟩⟩
    unfold atiyahPoly
    rw [← Finset.mul_prod_erase (Finset.univ.erase i) _ ha0_mem,
        ← Finset.mul_prod_erase ((Finset.univ.erase i).erase a₀) _ ha1_mem]
    have hf0 : Polynomial.C (ψLim i a₀ 0) + Polynomial.C (ψLim i a₀ 1) * Polynomial.X = 1 := by
      simp [ψLim, i, a₀]
    have hf1 : Polynomial.C (ψLim i a₁ 0) + Polynomial.C (ψLim i a₁ 1) * Polynomial.X = 1 := by
      simp [ψLim, i, a₁]
    rw [hf0, hf1, one_mul, one_mul]
    refine Finset.prod_bij (fun j hj => ⟨j.1, by
      have hj0 : j ≠ a₀ := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
      have hj1 : j ≠ a₁ := (Finset.mem_erase.mp hj).1
      have hjlt : j.1 < n + 2 := j.2
      have : j.1 ≠ n := fun h => hj0 (Fin.ext h)
      have : j.1 ≠ n + 1 := fun h => hj1 (Fin.ext h)
      omega⟩) ?_ ?_ ?_ ?_
    · intro j hj
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      have hji : j ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).2).1
      intro h; exact hji (Fin.ext (by simpa [i] using congr_arg Fin.val h))
    · intro j₁ _ j₂ _ h; exact Fin.ext (by simpa using congr_arg Fin.val h)
    · intro k hk
      have hki : k ≠ i₀ := (Finset.mem_erase.mp hk).1
      refine ⟨⟨k.1, by omega⟩, ?_, Fin.ext rfl⟩
      exact Finset.mem_erase.mpr ⟨Fin.ne_of_val_ne (by show k.1 ≠ n + 1; omega),
        Finset.mem_erase.mpr ⟨Fin.ne_of_val_ne (by show k.1 ≠ n; omega),
          Finset.mem_erase.mpr ⟨Fin.ne_of_val_ne (fun h => hki (Fin.ext h)), Finset.mem_univ _⟩⟩⟩
    · intro j hj
      have hjlt : j.1 < n := by
        have hj0 : j ≠ a₀ := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
        have hj1 : j ≠ a₁ := (Finset.mem_erase.mp hj).1
        have := j.2
        have : j.1 ≠ n := fun h => hj0 (Fin.ext h)
        have : j.1 ≠ n + 1 := fun h => hj1 (Fin.ext h)
        omega
      simp only [ψLim, hjlt, i₀.2, ↓reduceDIte]
  have hpoly_hi : ∀ (m : Fin 2),
      let r := finSumFinEquiv (.inr m : Fin n ⊕ Fin 2)
      let c : ℂ := if m = 0 then -Complex.I else Complex.I
      atiyahPoly ψLim r = (1 + Polynomial.C c * Polynomial.X) * Polynomial.X ^ n := by
    intro m r c
    let partner : Fin (n + 2) := finSumFinEquiv (.inr (1 - m) : Fin n ⊕ Fin 2)
    have hrp : r ≠ partner := by
      intro h
      have h' := finSumFinEquiv.injective h
      fin_cases m <;> simp at h'
    have hp_mem : partner ∈ Finset.univ.erase r := Finset.mem_erase.mpr ⟨hrp.symm, Finset.mem_univ _⟩
    unfold atiyahPoly
    rw [← Finset.mul_prod_erase (Finset.univ.erase r) _ hp_mem]
    have hrn : ¬ r.1 < n := by fin_cases m <;> simp [r]
    have hfac_p : Polynomial.C (ψLim r partner 0) + Polynomial.C (ψLim r partner 1) * Polynomial.X =
        1 + Polynomial.C c * Polynomial.X := by
      fin_cases m <;> simp [ψLim, r, partner, c]
    rw [hfac_p]
    congr 1
    have hcard : ((Finset.univ.erase r).erase partner).card = n := by
      rw [Finset.card_erase_of_mem hp_mem, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_fin]
      omega
    have hprod_X : ∏ j ∈ (Finset.univ.erase r).erase partner,
        (Polynomial.C (ψLim r j 0) + Polynomial.C (ψLim r j 1) * Polynomial.X) =
        ∏ _j ∈ (Finset.univ.erase r).erase partner, Polynomial.X := by
      refine Finset.prod_congr rfl fun j hj => ?_
      have hjr : j ≠ r := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
      have hjp : j ≠ partner := (Finset.mem_erase.mp hj).1
      have hjlt : j.1 < n := by
        fin_cases m
        · have hj1 : j.1 ≠ n := fun h => hjr (Fin.ext (by simp [r, h]))
          have hj2 : j.1 ≠ n + 1 := fun h => hjp (Fin.ext (by simp [partner, h]))
          have := j.2; omega
        · have hj1 : j.1 ≠ n + 1 := fun h => hjr (Fin.ext (by simp [r, h]))
          have hj2 : j.1 ≠ n := fun h => hjp (Fin.ext (by simp [partner, h]))
          have := j.2; omega
      simp [ψLim, hrn, hjlt]
    rw [hprod_X, Finset.prod_const, hcard]
  have hdegX : ∀ i : Fin n, (atiyahPoly ψX i).natDegree ≤ n - 1 := by
    intro i
    have hcard : (Finset.univ.erase i).card = n - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_fin]
    unfold atiyahPoly
    calc
      (∏ j ∈ Finset.univ.erase i, (Polynomial.C (ψX i j 0) + Polynomial.C (ψX i j 1) * Polynomial.X)).natDegree
        ≤ ∑ j ∈ Finset.univ.erase i, (Polynomial.C (ψX i j 0) + Polynomial.C (ψX i j 1) * Polynomial.X).natDegree :=
          Polynomial.natDegree_prod_le _ _
      _ ≤ ∑ _j ∈ Finset.univ.erase i, 1 := by
          refine Finset.sum_le_sum fun j _ => ?_
          compute_degree!
      _ = n - 1 := by simp [hcard]
  let D_blk : Matrix (Fin 2) (Fin 2) ℂ := !![1, -Complex.I; 1, Complex.I]
  let C_blk : Matrix (Fin 2) (Fin n) ℂ := fun m k =>
    (atiyahPoly ψLim (finSumFinEquiv (.inr m))).coeff k.1
  let e : Fin (n + 2) ≃ Fin n ⊕ Fin 2 := finSumFinEquiv.symm
  have hmat_blk : Matrix.reindex e e (atiyahMat ψLim) =
      Matrix.fromBlocks (atiyahMat ψX) 0 C_blk D_blk := by
    ext r c
    rcases r with i | m₁ <;> rcases c with k | m₂
    · simp only [Matrix.reindex_apply, Equiv.symm_symm, e, Matrix.submatrix_apply,
        finSumFinEquiv_apply_left, Matrix.fromBlocks_apply₁₁, atiyahMat]
      have hcast : Fin.castAdd 2 i = ⟨i.1, by omega⟩ := Fin.ext rfl
      rw [hcast]
      exact congr_arg (fun p : Polynomial ℂ => p.coeff k.1) (hpoly_lo i)
    · simp only [Matrix.reindex_apply, Equiv.symm_symm, e, Matrix.submatrix_apply,
        finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.val_natAdd,
        Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, atiyahMat]
      have hcast : Fin.castAdd 2 i = ⟨i.1, by omega⟩ := Fin.ext rfl
      rw [hcast, hpoly_lo i]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hdegX i) (by have := i.2; omega))
    · rfl
    · simp only [Matrix.reindex_apply, Equiv.symm_symm, e, Matrix.submatrix_apply,
        Matrix.fromBlocks_apply₂₂, atiyahMat]
      rw [hpoly_hi m₁]
      have hpow : ∀ c : ℂ, (1 + Polynomial.C c * Polynomial.X) * Polynomial.X ^ n =
          Polynomial.X ^ n + Polynomial.C c * Polynomial.X ^ (n + 1) := fun c => by ring
      rw [hpow, finSumFinEquiv_apply_right, Fin.val_natAdd]
      fin_cases m₁ <;> fin_cases m₂ <;> simp [D_blk]
  have hD_det : D_blk.det = 2 * Complex.I := by
    rw [Matrix.det_fin_two]
    simp [D_blk]; ring
  have hdet_eq : (atiyahMat ψLim).det = (atiyahMat ψX).det * (2 * Complex.I) := by
    rw [← Matrix.det_reindex_self e (atiyahMat ψLim), hmat_blk,
        Matrix.det_fromBlocks_zero₁₂, hD_det]
  let S₀ : Finset { p : Fin (n + 2) × Fin (n + 2) // p.1 < p.2 } :=
    Finset.univ.filter fun q => q.1.2.1 < n
  let e₀ : { p : Fin (n + 2) × Fin (n + 2) // p.1 < p.2 } :=
    ⟨(a₀, a₁), Fin.mk_lt_mk.mpr (show n < n + 1 by omega)⟩
  have he0_not_S0 : e₀ ∈ Finset.univ \ S₀ := by
    simp [S₀, e₀, a₁]
  have hden_eq : atiyahDen ψLim = (2 * Complex.I) * atiyahDen ψX := by
    unfold atiyahDen
    rw [← Finset.prod_sdiff (Finset.subset_univ S₀)]
    have hS0 : ∏ q ∈ S₀, omega (ψLim q.1.1 q.1.2) (ψLim q.1.2 q.1.1) =
        ∏ q : { p : Fin n × Fin n // p.1 < p.2 }, omega (ψX q.1.1 q.1.2) (ψX q.1.2 q.1.1) := by
      refine Finset.prod_bij (fun q hq =>
        ⟨(⟨q.1.1.1, lt_trans q.2 (Finset.mem_filter.mp hq).2⟩,
          ⟨q.1.2.1, (Finset.mem_filter.mp hq).2⟩), q.2⟩) ?_ ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro q₁ _ q₂ _ h
        ext <;> simp only [Subtype.mk.injEq, Prod.mk.injEq, Fin.mk.injEq] at h
        · exact h.1
        · exact h.2
      · intro q _
        refine ⟨⟨(⟨q.1.1.1, by omega⟩, ⟨q.1.2.1, by omega⟩), q.2⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, q.1.2.2⟩, rfl⟩
      · intro q hq
        have h2 : q.1.2.1 < n := (Finset.mem_filter.mp hq).2
        have h1 : q.1.1.1 < n := lt_trans q.2 h2
        simp [ψLim, h1, h2]
    have hsdiff : ∏ q ∈ Finset.univ \ S₀, omega (ψLim q.1.1 q.1.2) (ψLim q.1.2 q.1.1) =
        2 * Complex.I := by
      rw [← Finset.mul_prod_erase (Finset.univ \ S₀) _ he0_not_S0]
      have he0_val : omega (ψLim e₀.1.1 e₀.1.2) (ψLim e₀.1.2 e₀.1.1) = 2 * Complex.I := by
        simp [ψLim, e₀, a₀, a₁, omega]; ring
      have hrest_one : ∏ q ∈ (Finset.univ \ S₀).erase e₀,
          omega (ψLim q.1.1 q.1.2) (ψLim q.1.2 q.1.1) = 1 := by
        refine Finset.prod_eq_one fun q hq => ?_
        have hne_e0 : q ≠ e₀ := (Finset.mem_erase.mp hq).1
        have hnot_S0 : ¬ q.1.2.1 < n := by
          have := (Finset.mem_sdiff.mp (Finset.mem_erase.mp hq).2).2
          simpa [S₀] using this
        have hq1_lt : q.1.1.1 < n := by
          have h12 : q.1.1.1 < q.1.2.1 := q.2
          have hq2_le : q.1.2.1 ≤ n + 1 := Nat.lt_succ_iff.mp q.1.2.2
          by_contra hge
          have hq1_eq : q.1.1 = a₀ := Fin.ext (by dsimp [a₀]; omega)
          have hq2_eq : q.1.2 = a₁ := Fin.ext (by dsimp [a₁]; omega)
          exact hne_e0 (Subtype.ext (Prod.ext hq1_eq hq2_eq))
        simp [ψLim, hq1_lt, hnot_S0, omega]
      rw [he0_val, hrest_one, mul_one]
    rw [hS0, hsdiff]
  have hdenX_ne : atiyahDen ψX ≠ 0 := by
    refine atiyahDen_unit_ne_zero (fun i j hij => unitDir_norm_sq (x.2 i j hij))
      (fun i j hij => unitDir_ne_swap (x.2 i j hij))
      (fun i j hij => isPosSpinor_ne_zero (isPosSpinor_canonicalSpinor (unitDir_norm_sq (x.2 i j hij))))
      (fun i j hij => (isPosSpinor_canonicalSpinor (unitDir_norm_sq (x.2 i j hij))).2)
  have h2I_ne : (2 * Complex.I : ℂ) ≠ 0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
  have hfinal_eq : atiyahDetOfSpinors ψLim = atiyahDet x := by
    change (atiyahMat ψLim).det / atiyahDen ψLim = (atiyahMat ψX).det / atiyahDen ψX
    rw [hdet_eq, hden_eq]
    field_simp [hdenX_ne, h2I_ne]
  rw [heq_spinor, hfinal_eq] at htend_u
  exact htend_u

private lemma mirrorPair_anchor_H_of_bounds {n : ℕ} (x0 x1 : DistinctPoints n)
    (hy0 : ∀ i, x0.1 i 1 = 0) (hy1 : ∀ i, x1.1 i 1 = 0)
    (hre0 : 0 < (atiyahDet x0).re) (hre1 : (atiyahDet x1).re < 0)
    (hnorm1 : ‖atiyahDet x1‖ < 1) :
    ∃ H : ℝ,
      (0 < (atiyahDet (mirrorPairExt x0 hy0 H)).re) ∧
      ((atiyahDet (mirrorPairExt x1 hy1 H)).re < 0 ∧
       ‖atiyahDet (mirrorPairExt x1 hy1 H)‖ < 1) := by
  have ht0 := (Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_atiyahDet_mirrorPairExt_atTop x0 hy0))
  have hev0 : ∀ᶠ H : ℝ in atTop,
      0 < (atiyahDet (mirrorPairExt x0 hy0 H)).re :=
    ht0.eventually (lt_mem_nhds hre0)
  have ht1 := tendsto_atiyahDet_mirrorPairExt_atTop x1 hy1
  have hev1 : ∀ᶠ H : ℝ in atTop,
      (atiyahDet (mirrorPairExt x1 hy1 H)).re < 0 :=
    (Complex.continuous_re.continuousAt.tendsto.comp ht1).eventually (gt_mem_nhds hre1)
  have hev2 : ∀ᶠ H : ℝ in atTop,
      ‖atiyahDet (mirrorPairExt x1 hy1 H)‖ < 1 :=
    ht1.norm.eventually (gt_mem_nhds hnorm1)
  exact (hev0.and (hev1.and hev2)).exists

private lemma continuous_atiyahDet_mirrorPairExt_of_path {n : ℕ}
    (x : ℝ → DistinctPoints n) (hy : ∀ s i, (x s).1 i 1 = 0)
    (hcont : ∀ i c, Continuous (fun s => (x s).1 i c)) (H : ℝ) :
    Continuous (fun s => atiyahDet (mirrorPairExt (x s) (hy s) H)) := by
  rw [continuous_iff_continuousAt]
  intro s₀
  refine tendsto_atiyahDet_of_tendsto (fun s => mirrorPairExt (x s) (hy s) H)
    (mirrorPairExt (x s₀) (hy s₀) H) fun i => ?_
  rw [tendsto_pi_nhds]; intro c
  by_cases hi : i.1 < n
  · simp only [mirrorPairExt, hi, ↓reduceDIte]
    exact (hcont ⟨i.1, hi⟩ c).continuousAt.tendsto
  · by_cases hin : i.1 = n <;> simp [mirrorPairExt, hi, hin]

private lemma mirrorPair_zero_of_path {n : ℕ} (hn : 1 ≤ n)
    (x : ℝ → DistinctPoints n) (hy : ∀ s i, (x s).1 i 1 = 0)
    (hcont : ∀ i c, Continuous (fun s => (x s).1 i c))
    (hre0 : 0 < (atiyahDet (x 0)).re) (hre1 : (atiyahDet (x 1)).re < 0)
    (hnorm1 : ‖atiyahDet (x 1)‖ < 1) :
    ∃ (H s₀ : ℝ), s₀ ≠ 0 ∧
      atiyahDet (mirrorPairExt (x s₀) (hy s₀) H) = 0 ∧
      ¬ LinearIndependent ℂ (fun i : Fin (n + 2) =>
          atiyahPoly (fun u v => canonicalSpinor (unitDir ((mirrorPairExt (x s₀) (hy s₀) H).1 u)
            ((mirrorPairExt (x s₀) (hy s₀) H).1 v))) i) := by
  obtain ⟨Hc, hc0, hc1, _⟩ := mirrorPair_anchor_H_of_bounds (x 0) (x 1) (hy 0) (hy 1) hre0 hre1 hnorm1
  let path : ℝ → DistinctPoints (n + 2) := fun s => mirrorPairExt (x s) (hy s) Hc
  let f : ℝ → ℝ := fun s => (atiyahDet (path s)).re
  have hf_cont : ContinuousOn f (Set.Icc (0 : ℝ) 1) :=
    (Complex.continuous_re.comp (continuous_atiyahDet_mirrorPairExt_of_path x hy hcont Hc)).continuousOn
  have hmem : (0 : ℝ) ∈ Set.Icc (f 1) (f 0) := ⟨hc1.le, hc0.le⟩
  obtain ⟨s₀, _, hs₀⟩ := intermediate_value_Icc' zero_le_one hf_cont hmem
  have hs₀_ne : s₀ ≠ 0 := by
    intro hs0
    have h0 : f s₀ = 0 := hs₀
    rw [hs0] at h0
    linarith [hc0, h0]
  have him0 : (atiyahDet (path s₀)).im = 0 :=
    atiyahDet_mirrorPairExt_im_eq_zero (x s₀) (hy s₀) Hc
  have hdet0 : atiyahDet (path s₀) = 0 := Complex.ext hs₀ him0
  exact ⟨Hc, s₀, hs₀_ne, hdet0, not_linearIndependent_of_atiyahDet_zero (by omega) (path s₀) hdet0⟩

private lemma continuous_x57Path_coord (i : Fin 57) (c : Fin 3) :
    Continuous (fun s => (x57Path s).1 i c) := by
  fin_cases c <;> simp [x57Path, planarPath] <;> continuity

section ShieldPartC
attribute [local irreducible] atiyahDet x57Path pts57X pts57Z

private lemma x57Path_zero_re_pos : 0 < (atiyahDet (x57Path 0)).re := by
  rw [x57Path_zero_det, Complex.one_re]; norm_num

/-- **Genuine Non-Coplanar 3D Disproof of Conjecture 2** at `n = 59` (`|D_59| < 1` and `D_59 < 0`). -/
theorem exists_noncoplanar_59_violating_conjecture_2 :
    ∃ x : DistinctPoints 59, ¬ IsCoplanar x ∧
      (atiyahDet x).im = 0 ∧ (atiyahDet x).re < 0 ∧ ‖atiyahDet x‖ < 1 := by
  obtain ⟨H, _, hre1, hnorm1⟩ := mirrorPair_anchor_H_of_bounds (x57Path 0) (x57Path 1)
    (x57Path_hy 0) (x57Path_hy 1) x57Path_zero_re_pos
    x57Path_one_re_neg_and_norm_lt_one.2.1 x57Path_one_re_neg_and_norm_lt_one.2.2
  refine ⟨mirrorPairExt (x57Path 1) (x57Path_hy 1) H,
    not_isCoplanar_mirrorPairExt_x57Path one_ne_zero,
    atiyahDet_mirrorPairExt_im_eq_zero (x57Path 1) (x57Path_hy 1) H,
    hre1, hnorm1⟩

/-- **Genuine Non-Coplanar 3D Disproof of Conjecture 1 (Linear Dependence & Zero Determinant)** at `n = 59`. -/
theorem exists_noncoplanar_59_atiyahDet_zero :
    ∃ x : DistinctPoints 59, ¬ IsCoplanar x ∧
      atiyahDet x = 0 ∧
      ¬ LinearIndependent ℂ (fun i : Fin 59 =>
          atiyahPoly (fun u v => canonicalSpinor (unitDir (x.1 u) (x.1 v))) i) := by
  obtain ⟨H, s₀, hs₀_ne, hdet0, hdep⟩ := mirrorPair_zero_of_path (by omega) x57Path x57Path_hy
    continuous_x57Path_coord x57Path_zero_re_pos
    x57Path_one_re_neg_and_norm_lt_one.2.1 x57Path_one_re_neg_and_norm_lt_one.2.2
  exact ⟨mirrorPairExt (x57Path s₀) (x57Path_hy s₀) H,
    not_isCoplanar_mirrorPairExt_x57Path hs₀_ne, hdet0, hdep⟩

end ShieldPartC

end NonCoplanar3DDisproofs

/-! ## Part D: Beltrami–Klein Hyperbolic 3-Space $\mathbb{H}^3$ Disproofs of C1, C2, C3 -/

section HyperbolicH3Disproofs

/-- Configuration space $C_n(\mathbb{H}^3)$ in the Beltrami–Klein unit-ball model $\|q_i\| < 1$. -/
def KleinBallPoints (n : ℕ) : Type :=
  { q : Fin n → Fin 3 → ℝ //
    (∀ i : Fin n, q i 0 ^ 2 + q i 1 ^ 2 + q i 2 ^ 2 < 1) ∧
    (∀ i j : Fin n, i ≠ j → q i ≠ q j) }

/-- Hyperbolic coplanarity in the Beltrami–Klein model (geodesic planes equal affine planes $\cap \mathbb{B}^3$). -/
def IsHyperbolicCoplanar {n : ℕ} (q : KleinBallPoints n) : Prop :=
  ∃ (normal : Fin 3 → ℝ) (d : ℝ),
    (normal 0 ≠ 0 ∨ normal 1 ≠ 0 ∨ normal 2 ≠ 0) ∧
    ∀ i : Fin n, normal 0 * q.1 i 0 + normal 1 * q.1 i 1 + normal 2 * q.1 i 2 = d

/-- Forward ideal boundary endpoint $u_{ij} \in S^2 = \partial_\infty \mathbb{H}^3$ of the oriented
hyperbolic geodesic ray from `a` through `b` in the Beltrami–Klein unit ball. -/
noncomputable def kleinEndpoint (a b : Fin 3 → ℝ) : Fin 3 → ℝ :=
  let v := unitDir a b
  let c := a 0 * v 0 + a 1 * v 1 + a 2 * v 2
  let τ := -c + Real.sqrt (1 - (a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2) + c ^ 2)
  fun k => a k + τ * v k

lemma kleinEndpoint_norm_sq {a b : Fin 3 → ℝ}
    (ha : a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 < 1) (hab : a ≠ b) :
    kleinEndpoint a b 0 ^ 2 + kleinEndpoint a b 1 ^ 2 + kleinEndpoint a b 2 ^ 2 = 1 := by
  dsimp only [kleinEndpoint]
  set v := unitDir a b
  set c := a 0 * v 0 + a 1 * v 1 + a 2 * v 2
  set τ := -c + Real.sqrt (1 - (a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2) + c ^ 2)
  have hv := unitDir_norm_sq hab
  have hdisc : 0 ≤ 1 - (a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2) + c ^ 2 := by
    linarith [ha, sq_nonneg c]
  have hsqrt : (c + τ) ^ 2 = 1 - (a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2) + c ^ 2 := by
    have heq : c + τ = Real.sqrt (1 - (a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2) + c ^ 2) := by
      dsimp [τ]; ring
    rw [heq, Real.sq_sqrt hdisc]
  change (a 0 + τ * v 0) ^ 2 + (a 1 + τ * v 1) ^ 2 + (a 2 + τ * v 2) ^ 2 = 1
  linear_combination τ ^ 2 * hv + hsqrt

lemma kleinEndpoint_ne_swap {a b : Fin 3 → ℝ}
    (ha : a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 < 1)
    (hb : b 0 ^ 2 + b 1 ^ 2 + b 2 ^ 2 < 1)
    (hab : a ≠ b) :
    kleinEndpoint a b ≠ kleinEndpoint b a := by
  intro heq
  set v := unitDir a b
  set r := euclidNorm (fun k => b k - a k)
  set c₁ := a 0 * v 0 + a 1 * v 1 + a 2 * v 2
  set τ₁ := -c₁ + Real.sqrt (1 - (a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2) + c₁ ^ 2)
  set v₂ := unitDir b a
  set c₂ := b 0 * v₂ 0 + b 1 * v₂ 1 + b 2 * v₂ 2
  set τ₂ := -c₂ + Real.sqrt (1 - (b 0 ^ 2 + b 1 ^ 2 + b 2 ^ 2) + c₂ ^ 2)
  have hr_pos : 0 < r := euclidNorm_pos_of_ne hab
  have hv_sq : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1 := unitDir_norm_sq hab
  have hb_eq : ∀ k, b k = a k + r * v k := fun k => by
    have hv_def : v k = (b k - a k) / r := rfl
    rw [hv_def, mul_div_cancel₀ _ hr_pos.ne']
    ring
  have hb_norm : (a 0 + r * v 0) ^ 2 + (a 1 + r * v 1) ^ 2 + (a 2 + r * v 2) ^ 2 < 1 := by
    simpa only [← hb_eq 0, ← hb_eq 1, ← hb_eq 2] using hb
  have hdisc1 : 0 < 1 - (a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2) + c₁ ^ 2 := by
    linarith [ha, sq_nonneg c₁]
  have hs1_pos : 0 < c₁ + τ₁ := by
    have : c₁ + τ₁ = Real.sqrt (1 - (a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2) + c₁ ^ 2) := by
      dsimp [τ₁]; ring
    rw [this]
    exact Real.sqrt_pos.mpr hdisc1
  have hs1_sq : (c₁ + τ₁) ^ 2 = 1 - (a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2) + c₁ ^ 2 := by
    have : c₁ + τ₁ = Real.sqrt (1 - (a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2) + c₁ ^ 2) := by
      dsimp [τ₁]; ring
    rw [this, Real.sq_sqrt hdisc1.le]
  have hr_sq : (r + c₁) ^ 2 < (c₁ + τ₁) ^ 2 := by
    have hexp : (r + c₁) ^ 2 =
        ((a 0 + r * v 0) ^ 2 + (a 1 + r * v 1) ^ 2 + (a 2 + r * v 2) ^ 2) -
        (a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2) + c₁ ^ 2 + r ^ 2 * (1 - (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2)) := by
      dsimp [c₁]; ring
    rw [hexp, hv_sq, sub_self, mul_zero, add_zero, hs1_sq]
    linarith [hb_norm]
  have hr_lt_τ1 : r < τ₁ := by
    have hlt_sum : r + c₁ < c₁ + τ₁ := by nlinarith
    linarith
  have hdisc2 : c₂ ^ 2 < 1 - (b 0 ^ 2 + b 1 ^ 2 + b 2 ^ 2) + c₂ ^ 2 := by linarith [hb]
  have hs2_sq : c₂ ^ 2 < (c₂ + τ₂) ^ 2 := by
    have : c₂ + τ₂ = Real.sqrt (1 - (b 0 ^ 2 + b 1 ^ 2 + b 2 ^ 2) + c₂ ^ 2) := by
      dsimp [τ₂]; ring
    rw [this, Real.sq_sqrt (le_trans (sq_nonneg c₂) hdisc2.le)]
    exact hdisc2
  have hs2_pos : 0 < c₂ + τ₂ := by
    have : c₂ + τ₂ = Real.sqrt (1 - (b 0 ^ 2 + b 1 ^ 2 + b 2 ^ 2) + c₂ ^ 2) := by
      dsimp [τ₂]; ring
    rw [this]
    exact Real.sqrt_pos.mpr (lt_of_le_of_lt (sq_nonneg c₂) hdisc2)
  have hτ2_pos : 0 < τ₂ := by nlinarith
  have hv2_eq : ∀ k, v₂ k = -v k := fun k => congr_fun (unitDir_swap a b) k
  have hdiff : ∀ k, kleinEndpoint a b k - kleinEndpoint b a k = (τ₁ + τ₂ - r) * v k := fun k => by
    change (a k + τ₁ * v k) - (b k + τ₂ * v₂ k) = _
    rw [hb_eq k, hv2_eq k]
    ring
  have h0 := congr_fun heq 0
  have h1 := congr_fun heq 1
  have h2 := congr_fun heq 2
  have hdot : (kleinEndpoint a b 0 - kleinEndpoint b a 0) * v 0 +
      (kleinEndpoint a b 1 - kleinEndpoint b a 1) * v 1 +
      (kleinEndpoint a b 2 - kleinEndpoint b a 2) * v 2 = 0 := by
    rw [h0, h1, h2]; ring
  rw [hdiff 0, hdiff 1, hdiff 2] at hdot
  have hval : (τ₁ + τ₂ - r) * (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2) = 0 := by linarith
  rw [hv_sq, mul_one] at hval
  linarith

/-- Hyperbolic Atiyah polynomial $P_i^{\mathbb{H}}(T)$ formed from geodesic ideal endpoints. -/
noncomputable def hyperbolicAtiyahPoly {n : ℕ} (q : KleinBallPoints n) (i : Fin n) : Polynomial ℂ :=
  atiyahPoly (fun u v => canonicalSpinor (kleinEndpoint (q.1 u) (q.1 v))) i

/-- Intrinsic hyperbolic Atiyah–Sutcliffe determinant $D_n^{\mathbb{H}}(\mathbf{q})$ in $\mathbb{H}^3$. -/
noncomputable def hyperbolicAtiyahDet {n : ℕ} (q : KleinBallPoints n) : ℂ :=
  atiyahDetOfSpinors (fun u v => canonicalSpinor (kleinEndpoint (q.1 u) (q.1 v)))

def deleteKleinPoint {n : ℕ} (q : KleinBallPoints (n + 1)) (k : Fin (n + 1)) : KleinBallPoints n :=
  ⟨fun i => q.1 (k.succAbove i),
    ⟨fun i => q.2.1 (k.succAbove i),
     fun i j hij => q.2.2 (k.succAbove i) (k.succAbove j) ((Fin.succAbove_right_injective).ne hij)⟩⟩

/-- **Hyperbolic Atiyah Conjecture 1 (Linear Independence):** $\mathbb{H}^3$ Atiyah polynomials are linearly independent. -/
def HyperbolicAtiyahConjecture1Prop : Prop :=
  ∀ (n : ℕ) (_ : 2 ≤ n) (q : KleinBallPoints n),
    LinearIndependent ℂ (fun i : Fin n => hyperbolicAtiyahPoly q i)

/-- **Hyperbolic Atiyah Conjecture 1 (Determinant Form):** $D_n^{\mathbb{H}}(\mathbf{q}) \neq 0$. -/
def HyperbolicAtiyahDetNonzeroProp : Prop :=
  ∀ (n : ℕ) (_ : 2 ≤ n) (q : KleinBallPoints n), hyperbolicAtiyahDet q ≠ 0

/-- **Hyperbolic Atiyah–Sutcliffe Conjecture 2:** $|D_n^{\mathbb{H}}(\mathbf{q})| \ge 1$. -/
def HyperbolicAtiyahSutcliffeConjecture2Prop : Prop :=
  ∀ (n : ℕ) (_ : 2 ≤ n) (q : KleinBallPoints n), 1 ≤ ‖hyperbolicAtiyahDet q‖

/-- **Hyperbolic Atiyah–Sutcliffe Conjecture 3:** $|D_n^{\mathbb{H}}|^{n-2} \ge \prod_k |D_{n-1}^{\mathbb{H}}|$. -/
def HyperbolicAtiyahSutcliffeConjecture3Prop : Prop :=
  ∀ (m : ℕ) (_ : 2 ≤ m) (q : KleinBallPoints (m + 1)),
    (∏ k : Fin (m + 1), ‖hyperbolicAtiyahDet (deleteKleinPoint q k)‖) ≤ ‖hyperbolicAtiyahDet q‖ ^ (m - 1)

lemma not_linearIndependent_of_hyperbolicAtiyahDet_zero {n : ℕ} (hn : 1 ≤ n)
    (q : KleinBallPoints n) (h0 : hyperbolicAtiyahDet q = 0) :
    ¬ LinearIndependent ℂ (fun i : Fin n => hyperbolicAtiyahPoly q i) :=
  not_linearIndependent_of_atiyahDetOfSpinors_eq_zero hn
    (atiyahDen_unit_ne_zero
      (fun i j hij => kleinEndpoint_norm_sq (q.2.1 i) (q.2.2 i j hij))
      (fun i j hij => kleinEndpoint_ne_swap (q.2.1 i) (q.2.1 j) (q.2.2 i j hij))
      (fun i j hij => isPosSpinor_ne_zero (isPosSpinor_canonicalSpinor
        (kleinEndpoint_norm_sq (q.2.1 i) (q.2.2 i j hij))))
      (fun i j hij => (isPosSpinor_canonicalSpinor
        (kleinEndpoint_norm_sq (q.2.1 i) (q.2.2 i j hij))).2))
    h0

lemma kleinEndpoint_yZero {a b : Fin 3 → ℝ} (ha : a 1 = 0) (hb : b 1 = 0) :
    kleinEndpoint a b 1 = 0 := by
  have hv1 : unitDir a b 1 = 0 := by simp [unitDir, ha, hb]
  simp [kleinEndpoint, ha, hv1]

lemma kleinEndpoint_yRefl (a b : Fin 3 → ℝ) :
    kleinEndpoint ![a 0, -a 1, a 2] ![b 0, -b 1, b 2] =
      ![kleinEndpoint a b 0, -kleinEndpoint a b 1, kleinEndpoint a b 2] := by
  let ra : Fin 3 → ℝ := ![a 0, -a 1, a 2]
  let rb : Fin 3 → ℝ := ![b 0, -b 1, b 2]
  have hnorm : euclidNorm (fun k => rb k - ra k) = euclidNorm (fun k => b k - a k) := by
    simp only [euclidNorm, ra, rb, vec3_eval]
    congr 1; ring
  have hv0 : unitDir ra rb 0 = unitDir a b 0 := by
    simp only [unitDir, hnorm, ra, rb, vec3_eval]
  have hv1 : unitDir ra rb 1 = -unitDir a b 1 := by
    simp only [unitDir, hnorm, ra, rb, vec3_eval]; ring
  have hv2 : unitDir ra rb 2 = unitDir a b 2 := by
    simp only [unitDir, hnorm, ra, rb, vec3_eval]
  have hc : ra 0 * unitDir ra rb 0 + ra 1 * unitDir ra rb 1 + ra 2 * unitDir ra rb 2 =
      a 0 * unitDir a b 0 + a 1 * unitDir a b 1 + a 2 * unitDir a b 2 := by
    simp only [hv0, hv1, hv2, ra, vec3_eval]; ring
  have hra_norm : ra 0 ^ 2 + ra 1 ^ 2 + ra 2 ^ 2 = a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 := by
    simp only [ra, vec3_eval]; ring
  ext k
  rcases k with ⟨_ | _ | _ | k, hk⟩
  · change kleinEndpoint ra rb 0 = kleinEndpoint a b 0
    dsimp only [kleinEndpoint]; rw [hc, hra_norm, hv0]; dsimp [ra]
  · change kleinEndpoint ra rb 1 = -kleinEndpoint a b 1
    dsimp only [kleinEndpoint]; rw [hc, hra_norm, hv1]; dsimp [ra]; ring
  · change kleinEndpoint ra rb 2 = kleinEndpoint a b 2
    dsimp only [kleinEndpoint]; rw [hc, hra_norm, hv2]; dsimp [ra]
  · omega

def scaleKlein {n : ℕ} (x : DistinctPoints n) (ε : ℝ) (hε0 : 0 < ε)
    (hball : ∀ i : Fin n, (ε * x.1 i 0) ^ 2 + (ε * x.1 i 1) ^ 2 + (ε * x.1 i 2) ^ 2 < 1) :
    KleinBallPoints n :=
  ⟨fun i k => ε * x.1 i k,
    ⟨hball, fun i j hij heq => x.2 i j hij (funext fun k =>
      mul_left_cancel₀ hε0.ne' (congr_fun heq k))⟩⟩

lemma isHyperbolicCoplanar_scaleKlein_iff {n : ℕ} (x : DistinctPoints n) (ε : ℝ) (hε0 : 0 < ε)
    (hball : ∀ i : Fin n, (ε * x.1 i 0) ^ 2 + (ε * x.1 i 1) ^ 2 + (ε * x.1 i 2) ^ 2 < 1) :
    IsHyperbolicCoplanar (scaleKlein x ε hε0 hball) ↔ IsCoplanar x := by
  constructor
  · rintro ⟨normal, d, hne, hplane⟩
    refine ⟨normal, d / ε, hne, fun i => ?_⟩
    have hi := hplane i
    dsimp [scaleKlein] at hi
    field_simp [hε0.ne']
    linarith
  · rintro ⟨normal, d, hne, hplane⟩
    refine ⟨normal, ε * d, hne, fun i => ?_⟩
    have hi := congr_arg (ε * ·) (hplane i)
    dsimp only [scaleKlein] at hi ⊢
    linarith

/-- Total helper computing `D_n^{\mathbb{H}}(ε · x)` without requiring the ball proof inside the function value. -/
noncomputable def rawScaledHypDet {n : ℕ} (x : DistinctPoints n) (ε : ℝ) : ℂ :=
  atiyahDetOfSpinors (fun u v => canonicalSpinor
    (kleinEndpoint (fun k => ε * x.1 u k) (fun k => ε * x.1 v k)))

lemma unitDir_smul_pos {a b : Fin 3 → ℝ} {ε : ℝ} (hε : 0 < ε) :
    unitDir (fun k => ε * a k) (fun k => ε * b k) = unitDir a b := by
  have hnorm : euclidNorm (fun k => ε * b k - ε * a k) =
      ε * euclidNorm (fun k => b k - a k) := by
    unfold euclidNorm
    have hs : (ε * b 0 - ε * a 0) ^ 2 + (ε * b 1 - ε * a 1) ^ 2 + (ε * b 2 - ε * a 2) ^ 2 =
        ε ^ 2 * ((b 0 - a 0) ^ 2 + (b 1 - a 1) ^ 2 + (b 2 - a 2) ^ 2) := by ring
    rw [hs, Real.sqrt_mul (sq_nonneg ε), Real.sqrt_sq hε.le]
  ext k
  simp only [unitDir, hnorm]
  rw [show ε * b k - ε * a k = ε * (b k - a k) by ring, mul_div_mul_left _ _ hε.ne']

lemma exists_bound_norm_sq {n : ℕ} (x : DistinctPoints n) :
    ∃ B : ℝ, 0 < B ∧ ∀ i : Fin n, x.1 i 0 ^ 2 + x.1 i 1 ^ 2 + x.1 i 2 ^ 2 ≤ B := by
  refine ⟨(∑ i : Fin n, (x.1 i 0 ^ 2 + x.1 i 1 ^ 2 + x.1 i 2 ^ 2)) + 1, by positivity, fun i => ?_⟩
  have hle := Finset.single_le_sum (f := fun j : Fin n => x.1 j 0 ^ 2 + x.1 j 1 ^ 2 + x.1 j 2 ^ 2)
    (fun j _ => by positivity) (Finset.mem_univ i)
  linarith

lemma ball_of_lt_bound {n : ℕ} (x : DistinctPoints n) {B : ℝ} (hB : 0 < B)
    (hx : ∀ i : Fin n, x.1 i 0 ^ 2 + x.1 i 1 ^ 2 + x.1 i 2 ^ 2 ≤ B)
    {ε : ℝ} (hε0 : 0 < ε) (hε_hi : ε < min (1 / 2) (1 / B)) :
    ∀ i : Fin n, (ε * x.1 i 0) ^ 2 + (ε * x.1 i 1) ^ 2 + (ε * x.1 i 2) ^ 2 < 1 := by
  intro i
  have hε1 : ε < 1 := lt_trans (lt_of_lt_of_le hε_hi (min_le_left _ _)) (by norm_num)
  have hεB : ε < 1 / B := lt_of_lt_of_le hε_hi (min_le_right _ _)
  have hsq : ε ^ 2 ≤ ε := by nlinarith
  have hprod : ε ^ 2 * B < 1 := by
    have hlt : ε * B < 1 := (lt_div_iff₀ hB).mp hεB
    nlinarith [hx i]
  have hmul : ε ^ 2 * (x.1 i 0 ^ 2 + x.1 i 1 ^ 2 + x.1 i 2 ^ 2) ≤ ε ^ 2 * B :=
    mul_le_mul_of_nonneg_left (hx i) (sq_nonneg ε)
  linarith [show (ε * x.1 i 0) ^ 2 + (ε * x.1 i 1) ^ 2 + (ε * x.1 i 2) ^ 2 =
    ε ^ 2 * (x.1 i 0 ^ 2 + x.1 i 1 ^ 2 + x.1 i 2 ^ 2) by ring]

lemma eventually_scaleKlein_ball {n : ℕ} (x : DistinctPoints n) :
    ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0),
      0 < ε ∧ ∀ i : Fin n, (ε * x.1 i 0) ^ 2 + (ε * x.1 i 1) ^ 2 + (ε * x.1 i 2) ^ 2 < 1 := by
  obtain ⟨B, hB, hx⟩ := exists_bound_norm_sq x
  have hm : Set.Ioo (0 : ℝ) (min (1 / 2) (1 / B)) ∈ nhdsWithin 0 (Set.Ioi 0) :=
    Ioo_mem_nhdsGT (lt_min (by norm_num) (one_div_pos.mpr hB))
  filter_upwards [hm] with ε hε
  exact ⟨hε.1, ball_of_lt_bound x hB hx hε.1 hε.2⟩

theorem tendsto_rawScaledHypDet_zero {n : ℕ} (x : DistinctPoints n) :
    Tendsto (rawScaledHypDet x) (nhdsWithin 0 (Set.Ioi 0)) (nhds (atiyahDet x)) := by
  let l := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  have hev := eventually_scaleKlein_ball x
  have hnorm : ∀ᶠ ε in l, ∀ i j : Fin n, i ≠ j →
      kleinEndpoint (fun k => ε * x.1 i k) (fun k => ε * x.1 j k) 0 ^ 2 +
      kleinEndpoint (fun k => ε * x.1 i k) (fun k => ε * x.1 j k) 1 ^ 2 +
      kleinEndpoint (fun k => ε * x.1 i k) (fun k => ε * x.1 j k) 2 ^ 2 = 1 := by
    filter_upwards [hev] with ε hε i j hij
    exact kleinEndpoint_norm_sq (hε.2 i) fun h => x.2 i j hij (funext fun k =>
      mul_left_cancel₀ hε.1.ne' (congr_fun h k))
  have hne : ∀ᶠ ε in l, ∀ i j : Fin n, i ≠ j →
      kleinEndpoint (fun k => ε * x.1 i k) (fun k => ε * x.1 j k) ≠
      kleinEndpoint (fun k => ε * x.1 j k) (fun k => ε * x.1 i k) := by
    filter_upwards [hev] with ε hε i j hij
    exact kleinEndpoint_ne_swap (hε.2 i) (hε.2 j) fun h => x.2 i j hij (funext fun k =>
      mul_left_cancel₀ hε.1.ne' (congr_fun h k))
  refine tendsto_atiyahDetOfSpinors_unit
    (fun ε i j => kleinEndpoint (fun k => ε * x.1 i k) (fun k => ε * x.1 j k))
    (fun i j => unitDir (x.1 i) (x.1 j))
    (fun i j hij => unitDir_norm_sq (x.2 i j hij))
    (fun i j hij => unitDir_ne_swap (x.2 i j hij))
    hnorm hne ?_
  intro i j hij
  rw [tendsto_pi_nhds]; intro c
  let v := unitDir (x.1 i) (x.1 j)
  have hid : Tendsto (fun ε : ℝ => ε) l (nhds 0) :=
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
  let aε : ℝ → Fin 3 → ℝ := fun ε k => ε * x.1 i k
  have haε : ∀ k, Tendsto (fun ε => aε ε k) l (nhds 0) := fun k => by
    simpa [aε] using hid.mul tendsto_const_nhds
  let cε : ℝ → ℝ := fun ε => aε ε 0 * v 0 + aε ε 1 * v 1 + aε ε 2 * v 2
  have hcε : Tendsto cε l (nhds 0) := by
    simpa [cε] using ((haε 0).mul tendsto_const_nhds).add ((haε 1).mul tendsto_const_nhds) |>.add
      ((haε 2).mul tendsto_const_nhds)
  let τε : ℝ → ℝ := fun ε =>
    -cε ε + Real.sqrt (1 - (aε ε 0 ^ 2 + aε ε 1 ^ 2 + aε ε 2 ^ 2) + cε ε ^ 2)
  have hdisc : Tendsto (fun ε => 1 - (aε ε 0 ^ 2 + aε ε 1 ^ 2 + aε ε 2 ^ 2) + cε ε ^ 2) l
      (nhds (1 - (0 ^ 2 + 0 ^ 2 + 0 ^ 2) + 0 ^ 2)) :=
    (tendsto_const_nhds.sub (((haε 0).pow 2).add ((haε 1).pow 2) |>.add ((haε 2).pow 2))).add (hcε.pow 2)
  have hτε : Tendsto τε l (nhds 1) := by
    have hs := hdisc.sqrt
    have hsum := hcε.neg.add hs
    simpa [τε] using hsum
  have hlim : Tendsto (fun ε => aε ε c + τε ε * v c) l (nhds (v c)) := by
    have h0 := (haε c).add (hτε.mul (tendsto_const_nhds (x := v c)))
    simpa using h0
  refine hlim.congr' ?_
  filter_upwards [hev] with ε hε
  simp only [kleinEndpoint, unitDir_smul_pos hε.1, aε, v, cε, τε]

lemma hyperbolic_c3_of_euclidean_c3 (x : DistinctPoints 5)
    (hC3 : ‖atiyahDet x‖ ^ (5 - 2) < ∏ k : Fin 5, ‖atiyahDet (deletePoint x k)‖) :
    ∃ q : KleinBallPoints 5,
      (IsHyperbolicCoplanar q ↔ IsCoplanar x) ∧
      ‖hyperbolicAtiyahDet q‖ ^ (5 - 2) < ∏ k : Fin 5, ‖hyperbolicAtiyahDet (deleteKleinPoint q k)‖ := by
  let l := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  have ht_lhs := (tendsto_rawScaledHypDet_zero x).norm.pow 3
  have ht_del : ∀ k : Fin 5, Tendsto (fun ε => ‖rawScaledHypDet (deletePoint x k) ε‖) l
      (nhds ‖atiyahDet (deletePoint x k)‖) := fun k =>
    (tendsto_rawScaledHypDet_zero (deletePoint x k)).norm
  have ht_rhs : Tendsto (fun ε => ∏ k : Fin 5, ‖rawScaledHypDet (deletePoint x k) ε‖) l
      (nhds (∏ k : Fin 5, ‖atiyahDet (deletePoint x k)‖)) := by
    simp only [Fin.prod_univ_five]
    exact ((((ht_del 0).mul (ht_del 1)).mul (ht_del 2)).mul (ht_del 3)).mul (ht_del 4)
  have hev_lt : ∀ᶠ ε in l,
      ‖rawScaledHypDet x ε‖ ^ (5 - 2) < ∏ k : Fin 5, ‖rawScaledHypDet (deletePoint x k) ε‖ :=
    ht_lhs.eventually_lt ht_rhs hC3
  obtain ⟨ε, hlt, hε0, hball⟩ := (hev_lt.and (eventually_scaleKlein_ball x)).exists
  let q := scaleKlein x ε hε0 hball
  refine ⟨q, isHyperbolicCoplanar_scaleKlein_iff x ε hε0 hball, ?_⟩
  exact hlt

private lemma continuousOn_rawScaledHypDet_Icc {n : ℕ}
    (x : ℝ → DistinctPoints n) (hcont : ∀ i c, Continuous (fun s => (x s).1 i c))
    {ε : ℝ} (hε0 : 0 < ε)
    (hq_ball : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ∀ i : Fin n, (ε * (x s).1 i 0) ^ 2 + (ε * (x s).1 i 1) ^ 2 + (ε * (x s).1 i 2) ^ 2 < 1) :
    ContinuousOn (fun s => rawScaledHypDet (x s) ε) (Set.Icc (0 : ℝ) 1) := by
  intro s₀ hs₀
  let l := nhdsWithin s₀ (Set.Icc (0 : ℝ) 1)
  have hev_Icc : ∀ᶠ s in l, s ∈ Set.Icc (0 : ℝ) 1 := self_mem_nhdsWithin
  have hnorm : ∀ᶠ s in l, ∀ i j : Fin n, i ≠ j →
      kleinEndpoint (fun k => ε * (x s).1 i k) (fun k => ε * (x s).1 j k) 0 ^ 2 +
      kleinEndpoint (fun k => ε * (x s).1 i k) (fun k => ε * (x s).1 j k) 1 ^ 2 +
      kleinEndpoint (fun k => ε * (x s).1 i k) (fun k => ε * (x s).1 j k) 2 ^ 2 = 1 := by
    filter_upwards [hev_Icc] with s hs i j hij
    exact kleinEndpoint_norm_sq (hq_ball s hs i) fun h => (x s).2 i j hij (funext fun k =>
      mul_left_cancel₀ hε0.ne' (congr_fun h k))
  have hne : ∀ᶠ s in l, ∀ i j : Fin n, i ≠ j →
      kleinEndpoint (fun k => ε * (x s).1 i k) (fun k => ε * (x s).1 j k) ≠
      kleinEndpoint (fun k => ε * (x s).1 j k) (fun k => ε * (x s).1 i k) := by
    filter_upwards [hev_Icc] with s hs i j hij
    exact kleinEndpoint_ne_swap (hq_ball s hs i) (hq_ball s hs j) fun h => (x s).2 i j hij
      (funext fun k => mul_left_cancel₀ hε0.ne' (congr_fun h k))
  have hdiff_ne : ∀ i j : Fin n, i ≠ j →
      (fun k => ε * (x s₀).1 i k) ≠ (fun k => ε * (x s₀).1 j k) := fun i j hij h =>
    (x s₀).2 i j hij (funext fun k => mul_left_cancel₀ hε0.ne' (congr_fun h k))
  refine tendsto_atiyahDetOfSpinors_unit
    (fun s i j => kleinEndpoint (fun k => ε * (x s).1 i k) (fun k => ε * (x s).1 j k))
    (fun i j => kleinEndpoint (fun k => ε * (x s₀).1 i k) (fun k => ε * (x s₀).1 j k))
    (fun i j hij => kleinEndpoint_norm_sq (hq_ball s₀ hs₀ i) (hdiff_ne i j hij))
    (fun i j hij => kleinEndpoint_ne_swap (hq_ball s₀ hs₀ i) (hq_ball s₀ hs₀ j) (hdiff_ne i j hij))
    hnorm hne ?_
  intro i j hij
  rw [tendsto_pi_nhds]; intro c
  have hpt : ∀ m k, Tendsto (fun s => ε * (x s).1 m k) l (nhds (ε * (x s₀).1 m k)) := fun m k =>
    (tendsto_const_nhds.mul ((hcont m k).continuousAt.tendsto)).mono_left nhdsWithin_le_nhds
  have hsub : ∀ k, Tendsto (fun s => ε * (x s).1 j k - ε * (x s).1 i k) l
      (nhds (ε * (x s₀).1 j k - ε * (x s₀).1 i k)) := fun k => (hpt j k).sub (hpt i k)
  have hnorm_t : Tendsto (fun s => euclidNorm (fun k => ε * (x s).1 j k - ε * (x s).1 i k)) l
      (nhds (euclidNorm (fun k => ε * (x s₀).1 j k - ε * (x s₀).1 i k))) := by
    unfold euclidNorm
    exact (((hsub 0).pow 2).add ((hsub 1).pow 2) |>.add ((hsub 2).pow 2)).sqrt
  have hr_ne : euclidNorm (fun k => ε * (x s₀).1 j k - ε * (x s₀).1 i k) ≠ 0 :=
    (euclidNorm_pos_of_ne (hdiff_ne i j hij)).ne'
  have hv_t : ∀ k, Tendsto (fun s => unitDir (fun m => ε * (x s).1 i m) (fun m => ε * (x s).1 j m) k) l
      (nhds (unitDir (fun m => ε * (x s₀).1 i m) (fun m => ε * (x s₀).1 j m) k)) := fun k =>
    (hsub k).div hnorm_t hr_ne
  have hc_t : Tendsto (fun s =>
      (ε * (x s).1 i 0) * unitDir (fun m => ε * (x s).1 i m) (fun m => ε * (x s).1 j m) 0 +
      (ε * (x s).1 i 1) * unitDir (fun m => ε * (x s).1 i m) (fun m => ε * (x s).1 j m) 1 +
      (ε * (x s).1 i 2) * unitDir (fun m => ε * (x s).1 i m) (fun m => ε * (x s).1 j m) 2) l
      (nhds ((ε * (x s₀).1 i 0) * unitDir (fun m => ε * (x s₀).1 i m) (fun m => ε * (x s₀).1 j m) 0 +
      (ε * (x s₀).1 i 1) * unitDir (fun m => ε * (x s₀).1 i m) (fun m => ε * (x s₀).1 j m) 1 +
      (ε * (x s₀).1 i 2) * unitDir (fun m => ε * (x s₀).1 i m) (fun m => ε * (x s₀).1 j m) 2)) :=
    ((hpt i 0).mul (hv_t 0)).add ((hpt i 1).mul (hv_t 1)) |>.add ((hpt i 2).mul (hv_t 2))
  have h1_t : Tendsto (fun _ : ℝ => (1 : ℝ)) l (nhds 1) := tendsto_const_nhds
  have hdisc_t :=
    ((h1_t.sub ((((hpt i 0).pow 2).add ((hpt i 1).pow 2)).add ((hpt i 2).pow 2))).add
      (hc_t.pow 2)).sqrt
  have hτ_t := hc_t.neg.add hdisc_t
  exact (hpt i c).add (hτ_t.mul (hv_t c))

private lemma exists_uniform_eps_for_Icc {n : ℕ}
    (x : ℝ → DistinctPoints n) {B : ℝ} (hB : 0 < B)
    (hxB : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ i : Fin n,
      (x s).1 i 0 ^ 2 + (x s).1 i 1 ^ 2 + (x s).1 i 2 ^ 2 ≤ B)
    (hre0 : 0 < (atiyahDet (x 0)).re) (hre1 : (atiyahDet (x 1)).re < 0)
    (hnorm1 : ‖atiyahDet (x 1)‖ < 1) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ i : Fin n,
        (ε * (x s).1 i 0) ^ 2 + (ε * (x s).1 i 1) ^ 2 + (ε * (x s).1 i 2) ^ 2 < 1) ∧
      0 < (rawScaledHypDet (x 0) ε).re ∧
      (rawScaledHypDet (x 1) ε).re < 0 ∧
      ‖rawScaledHypDet (x 1) ε‖ < 1 := by
  let l := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  have hev_eps : ∀ᶠ ε : ℝ in l, ε ∈ Set.Ioo (0 : ℝ) (min (1 / 2) (1 / B)) :=
    Ioo_mem_nhdsGT (lt_min (by norm_num) (one_div_pos.mpr hB))
  have hev0 : ∀ᶠ ε in l, 0 < (rawScaledHypDet (x 0) ε).re :=
    (Complex.continuous_re.continuousAt.tendsto.comp (tendsto_rawScaledHypDet_zero (x 0))).eventually
      (lt_mem_nhds hre0)
  have ht1 := tendsto_rawScaledHypDet_zero (x 1)
  have hev1 : ∀ᶠ ε in l, (rawScaledHypDet (x 1) ε).re < 0 :=
    (Complex.continuous_re.continuousAt.tendsto.comp ht1).eventually (gt_mem_nhds hre1)
  have hev2 : ∀ᶠ ε in l, ‖rawScaledHypDet (x 1) ε‖ < 1 :=
    ht1.norm.eventually (gt_mem_nhds hnorm1)
  obtain ⟨ε, hmem, h0, h1, h2⟩ := (hev_eps.and (hev0.and (hev1.and hev2))).exists
  refine ⟨ε, hmem.1, fun s hs => ball_of_lt_bound (x s) hB (hxB s hs) hmem.1 hmem.2, h0, h1, h2⟩

theorem hyperbolic_planar_c2_and_zero_of_path {n : ℕ} (hn : 1 ≤ n)
    (x : ℝ → DistinctPoints n) (hy : ∀ s i, (x s).1 i 1 = 0)
    (hcont : ∀ i c, Continuous (fun s => (x s).1 i c))
    {B : ℝ} (hB : 0 < B)
    (hxB : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ i : Fin n,
      (x s).1 i 0 ^ 2 + (x s).1 i 1 ^ 2 + (x s).1 i 2 ^ 2 ≤ B)
    (hre0 : 0 < (atiyahDet (x 0)).re) (hre1 : (atiyahDet (x 1)).re < 0)
    (hnorm1 : ‖atiyahDet (x 1)‖ < 1) :
    (∃ q1 : KleinBallPoints n, IsHyperbolicCoplanar q1 ∧
      (hyperbolicAtiyahDet q1).im = 0 ∧ (hyperbolicAtiyahDet q1).re < 0 ∧ ‖hyperbolicAtiyahDet q1‖ < 1) ∧
    (∃ q0 : KleinBallPoints n, IsHyperbolicCoplanar q0 ∧
      hyperbolicAtiyahDet q0 = 0 ∧ ¬ LinearIndependent ℂ (fun i : Fin n => hyperbolicAtiyahPoly q0 i)) := by
  obtain ⟨ε, hε0, hq_ball, h0_re, h1_re, h1_norm⟩ :=
    exists_uniform_eps_for_Icc x hB hxB hre0 hre1 hnorm1
  have him_zero : ∀ s ∈ Set.Icc (0 : ℝ) 1, (rawScaledHypDet (x s) ε).im = 0 := by
    intro s hs
    refine atiyahDetOfSpinors_im_eq_zero_of_yZero
      (fun u v => kleinEndpoint (fun k => ε * (x s).1 u k) (fun k => ε * (x s).1 v k))
      (fun u v huv => kleinEndpoint_norm_sq (hq_ball s hs u) fun h => (x s).2 u v huv
        (funext fun k => mul_left_cancel₀ hε0.ne' (congr_fun h k)))
      (fun u v huv => kleinEndpoint_ne_swap (hq_ball s hs u) (hq_ball s hs v) fun h =>
        (x s).2 u v huv (funext fun k => mul_left_cancel₀ hε0.ne' (congr_fun h k))) ?_
    intro u v _
    exact kleinEndpoint_yZero (by simp [hy s u]) (by simp [hy s v])
  have hco_scale : ∀ s (hs : s ∈ Set.Icc (0 : ℝ) 1),
      IsHyperbolicCoplanar (scaleKlein (x s) ε hε0 (hq_ball s hs)) := by
    intro s hs
    rw [isHyperbolicCoplanar_scaleKlein_iff]
    exact ⟨![0, 1, 0], 0, Or.inr (Or.inl one_ne_zero), fun i => by simp [hy s i]⟩
  refine ⟨⟨scaleKlein (x 1) ε hε0 (hq_ball 1 ⟨zero_le_one, le_rfl⟩),
      hco_scale 1 ⟨zero_le_one, le_rfl⟩, him_zero 1 ⟨zero_le_one, le_rfl⟩, h1_re, h1_norm⟩, ?_⟩
  let f : ℝ → ℝ := fun s => (rawScaledHypDet (x s) ε).re
  have hf_cont : ContinuousOn f (Set.Icc (0 : ℝ) 1) :=
    Complex.continuous_re.comp_continuousOn (continuousOn_rawScaledHypDet_Icc x hcont hε0 hq_ball)
  obtain ⟨s₀, hs₀, hfs₀⟩ := intermediate_value_Icc' zero_le_one hf_cont ⟨h1_re.le, h0_re.le⟩
  let q₀ := scaleKlein (x s₀) ε hε0 (hq_ball s₀ hs₀)
  have hdet0 : hyperbolicAtiyahDet q₀ = 0 := Complex.ext hfs₀ (him_zero s₀ hs₀)
  exact ⟨q₀, hco_scale s₀ hs₀, hdet0, not_linearIndependent_of_hyperbolicAtiyahDet_zero hn q₀ hdet0⟩

theorem hyperbolic_mirrorPair_c2_and_zero_of_path {n : ℕ} (hn : 1 ≤ n)
    (x : ℝ → DistinctPoints n) (hy : ∀ s i, (x s).1 i 1 = 0)
    (hcont : ∀ i c, Continuous (fun s => (x s).1 i c))
    {B : ℝ} (hB : 0 < B)
    (hxB : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ i : Fin n,
      (x s).1 i 0 ^ 2 + (x s).1 i 1 ^ 2 + (x s).1 i 2 ^ 2 ≤ B)
    (hre0 : 0 < (atiyahDet (x 0)).re) (hre1 : (atiyahDet (x 1)).re < 0)
    (hnorm1 : ‖atiyahDet (x 1)‖ < 1) :
    ∃ H : ℝ,
      (∃ q1 : KleinBallPoints (n + 2),
        (IsHyperbolicCoplanar q1 ↔ IsCoplanar (mirrorPairExt (x 1) (hy 1) H)) ∧
        (hyperbolicAtiyahDet q1).im = 0 ∧ (hyperbolicAtiyahDet q1).re < 0 ∧ ‖hyperbolicAtiyahDet q1‖ < 1) ∧
      (∃ s₀ ∈ Set.Icc (0 : ℝ) 1, s₀ ≠ 0 ∧ ∃ q0 : KleinBallPoints (n + 2),
        (IsHyperbolicCoplanar q0 ↔ IsCoplanar (mirrorPairExt (x s₀) (hy s₀) H)) ∧
        hyperbolicAtiyahDet q0 = 0 ∧
        ¬ LinearIndependent ℂ (fun i : Fin (n + 2) => hyperbolicAtiyahPoly q0 i)) := by
  obtain ⟨H, hH0_re, hH1_re, hH1_norm⟩ :=
    mirrorPair_anchor_H_of_bounds (x 0) (x 1) (hy 0) (hy 1) hre0 hre1 hnorm1
  let p : ℝ → DistinctPoints (n + 2) := fun s => mirrorPairExt (x s) (hy s) H
  let Bp : ℝ := B + 1 + H ^ 2
  have hBp_pos : 0 < Bp := by positivity
  have hp_bound : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ i : Fin (n + 2),
      (p s).1 i 0 ^ 2 + (p s).1 i 1 ^ 2 + (p s).1 i 2 ^ 2 ≤ Bp := by
    intro s hs i
    by_cases hi : i.1 < n
    · have hiB := hxB s hs ⟨i.1, hi⟩
      simp only [p, mirrorPairExt, hi, ↓reduceDIte]
      linarith [sq_nonneg H]
    · by_cases hin : i.1 = n <;>
        (simp [p, mirrorPairExt, hi, hin, vec3_eval]; linarith [hB])
  have hp_cont : ∀ i c, Continuous (fun s => (p s).1 i c) := by
    intro i c
    by_cases hi : i.1 < n
    · simp only [p, mirrorPairExt, hi, ↓reduceDIte]
      exact hcont ⟨i.1, hi⟩ c
    · by_cases hin : i.1 = n <;> (simp [p, mirrorPairExt, hi, hin]; exact continuous_const)
  obtain ⟨ε, hε0, hq_ball, h0_re, h1_re, h1_norm⟩ :=
    exists_uniform_eps_for_Icc p hBp_pos hp_bound hH0_re hH1_re hH1_norm
  have him_zero : ∀ s ∈ Set.Icc (0 : ℝ) 1, (rawScaledHypDet (p s) ε).im = 0 := by
    intro s hs
    refine atiyahDetOfSpinors_im_eq_zero_of_lastSwap_yRefl
      (fun u v => kleinEndpoint (fun k => ε * (p s).1 u k) (fun k => ε * (p s).1 v k))
      (fun u v huv => kleinEndpoint_norm_sq (hq_ball s hs u) fun h => (p s).2 u v huv
        (funext fun k => mul_left_cancel₀ hε0.ne' (congr_fun h k)))
      (fun u v huv => kleinEndpoint_ne_swap (hq_ball s hs u) (hq_ball s hs v) fun h =>
        (p s).2 u v huv (funext fun k => mul_left_cancel₀ hε0.ne' (congr_fun h k))) ?_
    intro u v _
    let a₀ : Fin (n + 2) := ⟨n, by omega⟩
    let a₁ : Fin (n + 2) := ⟨n + 1, by omega⟩
    let σ := Equiv.swap a₀ a₁
    have hp_sym : ∀ k : Fin (n + 2), (p s).1 (σ k) = ![(p s).1 k 0, -(p s).1 k 1, (p s).1 k 2] := by
      intro k
      by_cases hk : k.1 < n
      · have hk0 : k ≠ a₀ := Fin.ne_of_val_ne (by show k.1 ≠ n; omega)
        have hk1 : k ≠ a₁ := Fin.ne_of_val_ne (by show k.1 ≠ n + 1; omega)
        rw [Equiv.swap_apply_of_ne_of_ne hk0 hk1]
        ext c; fin_cases c <;> simp [p, mirrorPairExt, hk, hy s ⟨k.1, hk⟩]
      · by_cases hkn : k = a₀
        · subst hkn; rw [Equiv.swap_apply_left]
          ext c; fin_cases c <;> simp [p, mirrorPairExt, a₀, a₁]
        · have hk1 : k = a₁ := Fin.ext (by
            show k.1 = n + 1; have := k.2; have : k.1 ≠ n := fun h => hkn (Fin.ext h); omega)
          subst hk1; rw [Equiv.swap_apply_right]
          ext c; fin_cases c <;> simp [p, mirrorPairExt, a₀, a₁]
    have hsmul : ∀ k : Fin (n + 2), (fun c => ε * (p s).1 (σ k) c) =
        ![(fun c => ε * (p s).1 k c) 0, -(fun c => ε * (p s).1 k c) 1, (fun c => ε * (p s).1 k c) 2] := by
      intro k; ext c; fin_cases c <;> simp [hp_sym k]
    have hEq := congrArg₂ kleinEndpoint (hsmul u) (hsmul v)
    exact hEq.trans (kleinEndpoint_yRefl (fun c => ε * (p s).1 u c) (fun c => ε * (p s).1 v c))
  refine ⟨H, ⟨scaleKlein (p 1) ε hε0 (hq_ball 1 ⟨zero_le_one, le_rfl⟩),
      isHyperbolicCoplanar_scaleKlein_iff (p 1) ε hε0 _,
      him_zero 1 ⟨zero_le_one, le_rfl⟩, h1_re, h1_norm⟩, ?_⟩
  let f : ℝ → ℝ := fun s => (rawScaledHypDet (p s) ε).re
  have hf_cont : ContinuousOn f (Set.Icc (0 : ℝ) 1) :=
    Complex.continuous_re.comp_continuousOn (continuousOn_rawScaledHypDet_Icc p hp_cont hε0 hq_ball)
  obtain ⟨s₀, hs₀, hfs₀⟩ := intermediate_value_Icc' zero_le_one hf_cont ⟨h1_re.le, h0_re.le⟩
  have hs₀_ne : s₀ ≠ 0 := by
    intro hs0
    have hz : f s₀ = 0 := hfs₀
    rw [hs0] at hz
    linarith [h0_re, hz]
  let q₀ := scaleKlein (p s₀) ε hε0 (hq_ball s₀ hs₀)
  have hdet0 : hyperbolicAtiyahDet q₀ = 0 := Complex.ext hfs₀ (him_zero s₀ hs₀)
  exact ⟨s₀, hs₀, hs₀_ne, q₀, isHyperbolicCoplanar_scaleKlein_iff (p s₀) ε hε0 _,
    hdet0, not_linearIndependent_of_hyperbolicAtiyahDet_zero (by omega) q₀ hdet0⟩

private lemma pts57_abs_le : ∀ i : Fin 57,
    |pts57X i| ≤ 500000 ∧ |pts57Z i| ≤ 200000 := by
  decide

private lemma x57Path_norm_sq_le : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ i : Fin 57,
    (x57Path s).1 i 0 ^ 2 + (x57Path s).1 i 1 ^ 2 + (x57Path s).1 i 2 ^ 2 ≤ 10 ^ 12 := by
  intro s hs i
  have hb := pts57_abs_le i
  have hxR : |(pts57X i : ℝ)| ≤ 500000 := by exact_mod_cast hb.1
  have hzR : |(pts57Z i : ℝ)| ≤ 200000 := by exact_mod_cast hb.2
  have hs_abs : |s| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1], hs.2⟩
  have hx_sq : (s * (pts57X i : ℝ)) ^ 2 ≤ 500000 ^ 2 := by
    have hmul : |s * (pts57X i : ℝ)| ≤ 500000 := by
      rw [abs_mul]; nlinarith [abs_nonneg s, abs_nonneg (pts57X i : ℝ)]
    have h1 : |s * (pts57X i : ℝ)| ^ 2 ≤ 500000 ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) hmul 2
    rwa [sq_abs] at h1
  have hz_sq : ((pts57Z i : ℝ)) ^ 2 ≤ 200000 ^ 2 := by
    have h1 : |(pts57Z i : ℝ)| ^ 2 ≤ 200000 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hzR 2
    rwa [sq_abs] at h1
  simp only [x57Path, planarPath, vec3_eval]
  linarith [hx_sq, hz_sq]

section ShieldPartD
attribute [local irreducible] atiyahDet hyperbolicAtiyahDet x57Path pts57X pts57Z

/-- Explicit `n = 5` planar ($\mathbb{H}^2 \subset \mathbb{H}^3$) counterexample to Hyperbolic C3. -/
theorem exists_five_planar_hyperbolic_violating_conjecture_3 :
    ∃ q : KleinBallPoints 5, IsHyperbolicCoplanar q ∧
      ‖hyperbolicAtiyahDet q‖ ^ (5 - 2) <
        ∏ k : Fin 5, ‖hyperbolicAtiyahDet (deleteKleinPoint q k)‖ := by
  obtain ⟨q, hco_iff, hC3⟩ := hyperbolic_c3_of_euclidean_c3 x5 x5_violates_conjecture_3
  refine ⟨q, hco_iff.mpr ?_, hC3⟩
  exact ⟨![0, 1, 0], 0, Or.inr (Or.inl one_ne_zero), fun i => by simp [x5, planarPath]⟩

/-- Strictly non-coplanar ($\mathbb{H}^3$) `n = 5` counterexample to Hyperbolic C3. -/
theorem exists_five_noncoplanar_hyperbolic_violating_conjecture_3 :
    ∃ q : KleinBallPoints 5, ¬ IsHyperbolicCoplanar q ∧
      ‖hyperbolicAtiyahDet q‖ ^ (5 - 2) <
        ∏ k : Fin 5, ‖hyperbolicAtiyahDet (deleteKleinPoint q k)‖ := by
  obtain ⟨x, hx_nc, hx_C3⟩ := exists_five_noncoplanar_points_violating_conjecture_3
  obtain ⟨q, hco_iff, hq_C3⟩ := hyperbolic_c3_of_euclidean_c3 x hx_C3
  exact ⟨q, fun hco => hx_nc (hco_iff.mp hco), hq_C3⟩

/-- **Formal Disproof of Hyperbolic Atiyah–Sutcliffe Conjecture 3** in both $\mathbb{H}^2$ and $\mathbb{H}^3$ at `n = 5`. -/
theorem disproof_hyperbolic_atiyah_sutcliffe_conjecture_3 :
    ¬ HyperbolicAtiyahSutcliffeConjecture3Prop := by
  intro hC3
  obtain ⟨q, _, hlt⟩ := exists_five_noncoplanar_hyperbolic_violating_conjecture_3
  have hle := hC3 4 (by norm_num) q
  simp only [Nat.reduceSub] at hle hlt
  linarith

/-- Planar ($\mathbb{H}^2$) `n = 57` counterexample directly violating Hyperbolic C2 with `-1 < D_{57}^{\mathbb{H}} < 0`. -/
theorem exists_planar_57_hyperbolic_violating_conjecture_2 :
    ∃ q : KleinBallPoints 57, IsHyperbolicCoplanar q ∧
      (hyperbolicAtiyahDet q).im = 0 ∧ (hyperbolicAtiyahDet q).re < 0 ∧ ‖hyperbolicAtiyahDet q‖ < 1 :=
  (hyperbolic_planar_c2_and_zero_of_path (by omega) x57Path x57Path_hy continuous_x57Path_coord
    (by norm_num) x57Path_norm_sq_le x57Path_zero_re_pos
    x57Path_one_re_neg_and_norm_lt_one.2.1 x57Path_one_re_neg_and_norm_lt_one.2.2).1

/-- Planar ($\mathbb{H}^2$) `n = 57` witness where $D_{57}^{\mathbb{H}} = 0$ and polynomials are linearly dependent. -/
theorem exists_planar_57_hyperbolic_atiyahDet_zero :
    ∃ q : KleinBallPoints 57, IsHyperbolicCoplanar q ∧
      hyperbolicAtiyahDet q = 0 ∧ ¬ LinearIndependent ℂ (fun i : Fin 57 => hyperbolicAtiyahPoly q i) :=
  (hyperbolic_planar_c2_and_zero_of_path (by omega) x57Path x57Path_hy continuous_x57Path_coord
    (by norm_num) x57Path_norm_sq_le x57Path_zero_re_pos
    x57Path_one_re_neg_and_norm_lt_one.2.1 x57Path_one_re_neg_and_norm_lt_one.2.2).2

/-- Strictly non-coplanar ($\mathbb{H}^3$) `n = 59` counterexample directly violating Hyperbolic C2. -/
theorem exists_noncoplanar_59_hyperbolic_violating_conjecture_2 :
    ∃ q : KleinBallPoints 59, ¬ IsHyperbolicCoplanar q ∧
      (hyperbolicAtiyahDet q).im = 0 ∧ (hyperbolicAtiyahDet q).re < 0 ∧ ‖hyperbolicAtiyahDet q‖ < 1 := by
  obtain ⟨H, ⟨q1, hco_iff, him, hre, hnorm⟩, _⟩ :=
    hyperbolic_mirrorPair_c2_and_zero_of_path (by omega) x57Path x57Path_hy continuous_x57Path_coord
      (by norm_num) x57Path_norm_sq_le x57Path_zero_re_pos
      x57Path_one_re_neg_and_norm_lt_one.2.1 x57Path_one_re_neg_and_norm_lt_one.2.2
  exact ⟨q1, fun hco => not_isCoplanar_mirrorPairExt_x57Path one_ne_zero (hco_iff.mp hco),
    him, hre, hnorm⟩

/-- Strictly non-coplanar ($\mathbb{H}^3$) `n = 59` witness where $D_{59}^{\mathbb{H}} = 0$ and polynomials are linearly dependent. -/
theorem exists_noncoplanar_59_hyperbolic_atiyahDet_zero :
    ∃ q : KleinBallPoints 59, ¬ IsHyperbolicCoplanar q ∧
      hyperbolicAtiyahDet q = 0 ∧ ¬ LinearIndependent ℂ (fun i : Fin 59 => hyperbolicAtiyahPoly q i) := by
  obtain ⟨H, _, ⟨s₀, _, hs₀_ne, q0, hco_iff, hdet0, hdep⟩⟩ :=
    hyperbolic_mirrorPair_c2_and_zero_of_path (by omega) x57Path x57Path_hy continuous_x57Path_coord
      (by norm_num) x57Path_norm_sq_le x57Path_zero_re_pos
      x57Path_one_re_neg_and_norm_lt_one.2.1 x57Path_one_re_neg_and_norm_lt_one.2.2
  exact ⟨q0, fun hco => not_isCoplanar_mirrorPairExt_x57Path hs₀_ne (hco_iff.mp hco), hdet0, hdep⟩

/-- **Formal Disproof of Hyperbolic Atiyah Conjecture 1 (Determinant Form)** at planar `n = 57` and non-coplanar `n = 59`. -/
theorem disproof_hyperbolic_atiyah_det_nonzero : ¬ HyperbolicAtiyahDetNonzeroProp := by
  intro h
  obtain ⟨q, _, hdet0, _⟩ := exists_noncoplanar_59_hyperbolic_atiyahDet_zero
  exact h 59 (by norm_num) q hdet0

/-- **Formal Disproof of Hyperbolic Atiyah Conjecture 1 (Linear Independence Form)** in $\mathbb{H}^3$. -/
theorem disproof_hyperbolic_atiyah_conjecture_1 : ¬ HyperbolicAtiyahConjecture1Prop := by
  intro h
  obtain ⟨q, _, _, hdep⟩ := exists_noncoplanar_59_hyperbolic_atiyahDet_zero
  exact hdep (h 59 (by norm_num) q)

/-- **Formal Disproof of Hyperbolic Atiyah–Sutcliffe Conjecture 2** in $\mathbb{H}^3$. -/
theorem disproof_hyperbolic_atiyah_sutcliffe_conjecture_2 :
    ¬ HyperbolicAtiyahSutcliffeConjecture2Prop := by
  intro h
  obtain ⟨q, _, hdet0, _⟩ := exists_noncoplanar_59_hyperbolic_atiyahDet_zero
  have hle := h 59 (by norm_num) q
  rw [hdet0, norm_zero] at hle
  linarith

end ShieldPartD

end HyperbolicH3Disproofs

end Matematyka.AtiyahSutcliffe
