module

public import Mathlib

/-!
# Challenge: Counterexamples & Holomorphic No-Go Rigidity for the Atiyah–Sutcliffe Conjectures

This lightweight Challenge module declares the Euclidean (`C_n(ℝ³)`), hyperbolic (`C_n(ℍ³)` via
the Beltrami–Klein ball `B³`), symplectic (`Sp(m)`), and orthogonal (`B_m = SO(2m+1)`)
Atiyah–Sutcliffe normalized determinants, conjectures (C1, C2, C3), $\mathrm{SU}(2) \times S_m$
holomorphic spinor rigidity / No-Go formulations, and 23 headline theorems covering:
- Euclidean & hyperbolic C3 refutations at `n = 5` (planar C3 failure first announced by Tan–Zhang, Oct 2026);
- Planar (`n = 35, 57, 63`) and strictly non-coplanar 3D (`n = 26, 36, 37, 59`) refutations of C1 and C2;
- Hyperbolic (`ℍ²` & `ℍ³`) refutations down to non-coplanar `n = 26`, plus the `n = 3` 5-gap positivity `D_3^ℍ > 1`;
- Symplectic `Sp(18)` (`2m = 36`) and orthogonal `B_{18} = SO(37)` (`n = 37`) C1 refutations;
- Universal $\mathrm{SU}(2) \times S_m$ multilinear spinor rigidity and weighted multi-body No-Go (`n = 26`).

Proofs are supplied in `Solution.lean` and audited using strictly `{propext, Quot.sound, Classical.choice}`.
-/

@[expose] public section

namespace Challenge

open Complex Real Matrix Polynomial
open scoped Classical

/-- Euclidean norm of a vector in $\mathbb{R}^3$. -/
noncomputable def euclidNorm (v : Fin 3 → ℝ) : ℝ :=
  Real.sqrt (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2)

/-- Unit direction vector $v_{ij} = (\mathbf{x}_j - \mathbf{x}_i) / \|\mathbf{x}_j - \mathbf{x}_i\| \in S^2$. -/
noncomputable def unitDir (a b : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun k => (b k - a k) / euclidNorm (fun j => b j - a j)

/-- Skew-symmetric bilinear form $\omega$ on $\mathbb{C}^2$. -/
def omega (ψ φ : Fin 2 → ℂ) : ℂ :=
  ψ 0 * φ 1 - ψ 1 * φ 0

def unnormPos (v : Fin 3 → ℝ) (i : Fin 2) : ℂ :=
  if i = 0 then ((1 + v 2 : ℝ) : ℂ) else (v 0 : ℂ) + Complex.I * (v 1 : ℂ)

def unnormNeg (v : Fin 3 → ℝ) (i : Fin 2) : ℂ :=
  if i = 0 then (v 0 : ℂ) - Complex.I * (v 1 : ℂ) else ((1 - v 2 : ℝ) : ℂ)

/-- Canonical normalized $+1$-eigenvector of $v \cdot \vec{\sigma}$ for unit $v \in S^2$. -/
noncomputable def canonicalSpinor (v : Fin 3 → ℝ) : Fin 2 → ℂ :=
  if 0 ≤ v 2 then
    ((1 / Real.sqrt (2 * (1 + v 2)) : ℝ) : ℂ) • unnormPos v
  else
    ((1 / Real.sqrt (2 * (1 - v 2)) : ℝ) : ℂ) • unnormNeg v

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

/-- Deleting vertex `k` from a distinct-point configuration yields a distinct `(n - 1)`-point configuration. -/
def deletePoint {n : ℕ} (x : DistinctPoints (n + 1)) (k : Fin (n + 1)) : DistinctPoints n :=
  ⟨fun i => x.1 (k.succAbove i),
    fun i j hij => x.2 (k.succAbove i) (k.succAbove j) ((Fin.succAbove_right_injective).ne hij)⟩

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

/-- **Atiyah–Sutcliffe Conjecture 3:** $|D_n(\mathbf{x})|^{n-2} \ge \prod_{k=0}^{n-1} |D_{n-1}(\mathbf{x}\setminus\{x_k\})|$. -/
def AtiyahSutcliffeConjecture3Prop : Prop :=
  ∀ (m : ℕ) (_ : 2 ≤ m) (x : DistinctPoints (m + 1)),
    (∏ k : Fin (m + 1), ‖atiyahDet (deletePoint x k)‖) ≤ ‖atiyahDet x‖ ^ (m - 1)

/-- Affine coplanarity of a configuration in $\mathbb{R}^3$. -/
def IsCoplanar {n : ℕ} (x : DistinctPoints n) : Prop :=
  ∃ (normal : Fin 3 → ℝ) (d : ℝ),
    (normal 0 ≠ 0 ∨ normal 1 ≠ 0 ∨ normal 2 ≠ 0) ∧
    ∀ i : Fin n, normal 0 * x.1 i 0 + normal 1 * x.1 i 1 + normal 2 * x.1 i 2 = d

/-- Explicit non-coplanarity of `p : Fin n → Fin 3 → ℝ` in $\mathbb{R}^3$. -/
def Noncoplanar3D {n : ℕ} (p : Fin n → Fin 3 → ℝ) : Prop :=
  ¬ ∃ (a b c d : ℝ), (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) ∧
    ∀ i : Fin n, a * p i 0 + b * p i 1 + c * p i 2 = d

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

/-- Centrally symmetric symplectic configuration ($\mathrm{Sp}(m)$ locus $\mathbf{X} = -\mathbf{X}$). -/
structure SymplecticConfig (m : ℕ) where
  p : Fin (2 * m) → Fin 3 → ℝ
  distinct : ∀ i j, i ≠ j → p i ≠ p j
  antipodal : Equiv.Perm (Fin (2 * m))
  involutive : ∀ i, antipodal (antipodal i) = i
  neg_eq : ∀ i k, p (antipodal i) k = -p i k

/-- Atiyah Conjecture 1 restricted to centrally symmetric `Sp(m)` configurations. -/
def SymplecticAtiyahConjecture1Prop (m : ℕ) : Prop :=
  ∀ c : SymplecticConfig m, LinearIndependent ℂ (fun i : Fin (2 * m) =>
    atiyahPoly (fun u v => canonicalSpinor (unitDir (c.p u) (c.p v))) i)

/-- Origin-augmented centrally symmetric orthogonal configuration ($B_m = \mathrm{SO}(2m+1)$ locus). -/
structure OrthogonalBConfig (m : ℕ) where
  p : Fin (2 * m + 1) → Fin 3 → ℝ
  distinct : ∀ i j, i ≠ j → p i ≠ p j
  originIdx : Fin (2 * m + 1)
  origin_eq : ∀ k, p originIdx k = 0
  antipodal : Equiv.Perm (Fin (2 * m + 1))
  involutive : ∀ i, antipodal (antipodal i) = i
  fix_origin : antipodal originIdx = originIdx
  neg_eq : ∀ i k, p (antipodal i) k = -p i k

/-- Atiyah Conjecture 1 restricted to origin-augmented `B_m` configurations. -/
def OrthogonalBAtiyahConjecture1Prop (m : ℕ) : Prop :=
  ∀ c : OrthogonalBConfig m, LinearIndependent ℂ (fun i : Fin (2 * m + 1) =>
    atiyahPoly (fun u v => canonicalSpinor (unitDir (c.p u) (c.p v))) i)

/-- Predicate characterizing special unitary $2 \times 2$ complex matrices $\mathrm{SU}(2)$. -/
def IsSU2 (U : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  U * U.conjTranspose = 1 ∧ U.det = 1

/-- Canonical degree-1 spinor linear factor $v_0 + v_1 T$. -/
noncomputable def atiyahLinearFactor (v : Fin 2 → ℂ) : Polynomial ℂ :=
  Polynomial.C (v 0) + Polynomial.C (v 1) * Polynomial.X

/-- Standard homogeneous $\mathrm{GL}_2(\mathbb{C})$ action on $\mathbb{C}[T]_{\le m}$. -/
noncomputable def spinPolyAction (m : ℕ) (U : Matrix (Fin 2) (Fin 2) ℂ) (P : Polynomial ℂ) :
    Polynomial ℂ :=
  ∑ k ∈ Finset.range (m + 1),
    Polynomial.C (P.coeff k) *
      (Polynomial.C (U 0 1) + Polynomial.C (U 1 1) * Polynomial.X) ^ k *
      (Polynomial.C (U 0 0) + Polynomial.C (U 1 0) * Polynomial.X) ^ (m - k)

/-- Predicate for coordinatewise $\mathbb{C}$-linear, $S_m$-symmetric, $\mathrm{SU}(2)$-equivariant spinor maps. -/
def IsSpinorEquivariantMultilinear (m : ℕ) (Φ : (Fin m → Fin 2 → ℂ) → Polynomial ℂ) : Prop :=
  (∀ v, ∀ d > m, (Φ v).coeff d = 0) ∧
  (∀ (k : Fin m) (v : Fin m → Fin 2 → ℂ) (a b : ℂ) (x y : Fin 2 → ℂ),
    Φ (Function.update v k (a • x + b • y)) =
      Polynomial.C a * Φ (Function.update v k x) +
        Polynomial.C b * Φ (Function.update v k y)) ∧
  (∀ (σ : Equiv.Perm (Fin m)) (v : Fin m → Fin 2 → ℂ), Φ (v ∘ σ) = Φ v) ∧
  (∀ (U : Matrix (Fin 2) (Fin 2) ℂ), IsSU2 U →
    ∀ v : Fin m → Fin 2 → ℂ, Φ (fun k => U.mulVec (v k)) = spinPolyAction m U (Φ v))

/-- Arbitrary finite linear combination of $\mathrm{SU}(2) \times S_m$-equivariant multilinear spinor maps
with arbitrary $(m + 1)$-body scalar weights `W α x i`. -/
noncomputable def weightedSpinorCandidate {m : ℕ} {ι : Type*} [Fintype ι]
    (Φ : ι → (Fin m → Fin 2 → ℂ) → Polynomial ℂ)
    (W : ι → DistinctPoints (m + 1) → Fin (m + 1) → ℂ)
    (x : DistinctPoints (m + 1)) (i : Fin (m + 1)) : Polynomial ℂ :=
  ∑ α : ι, Polynomial.C (W α x i) *
    Φ α (fun r : Fin m => canonicalSpinor (unitDir (x.1 i) (x.1 (i.succAbove r))))

/-- Disproof of Euclidean Atiyah–Sutcliffe Conjecture 3 at sharp minimal `n = 5`. -/
theorem disproof_atiyah_sutcliffe_conjecture_3 : ¬ AtiyahSutcliffeConjecture3Prop := by
  sorry

/-- Explicit 5-point witness violating Euclidean Conjecture 3 (`|D₅|³ < ∏ |D₄|`). -/
theorem exists_five_planar_points_violating_conjecture_3 :
    ∃ x : DistinctPoints 5,
      ‖atiyahDet x‖ ^ (5 - 2) < ∏ k : Fin 5, ‖atiyahDet (deletePoint x k)‖ := by
  sorry

/-- Disproof of Euclidean Atiyah Conjecture 1 (determinant non-vanishing form). -/
theorem disproof_atiyah_det_nonzero : ¬ AtiyahDetNonzeroProp := by
  sorry

/-- Disproof of Euclidean Atiyah Conjecture 1 (polynomial linear independence form). -/
theorem disproof_atiyah_conjecture_1 : ¬ AtiyahConjecture1Prop := by
  sorry

/-- Disproof of Euclidean Atiyah–Sutcliffe Conjecture 2 (`|D_n| ≥ 1`). -/
theorem disproof_atiyah_sutcliffe_conjecture_2 : ¬ AtiyahSutcliffeConjecture2Prop := by
  sorry

/-- Genuinely non-coplanar 3D `n = 26` singular configuration (`D_26 = 0`) from the mirror-symmetric `x26Clamp` family. -/
theorem exists_noncoplanar_3d_26_atiyahDet_zero :
    ∃ x : DistinctPoints 26, Noncoplanar3D x.1 ∧ atiyahDet x = 0 := by
  sorry

/-- Genuinely non-coplanar 3D `n = 36` singular configuration (`D_36 = 0`) from coaxial Pythagorean `(33,56,65)` rings. -/
theorem exists_noncoplanar_3d_36_atiyahDet_zero :
    ∃ x : DistinctPoints 36, Noncoplanar3D x.1 ∧ atiyahDet x = 0 := by
  sorry

/-- Strictly non-coplanar 3D `n = 59` witness directly violating Conjecture 2 with `-1 < D_59 < 0`. -/
theorem exists_noncoplanar_59_violating_conjecture_2 :
    ∃ x : DistinctPoints 59, ¬ IsCoplanar x ∧
      (atiyahDet x).im = 0 ∧ (atiyahDet x).re < 0 ∧ ‖atiyahDet x‖ < 1 := by
  sorry

/-- Planar `n = 35` witness directly violating Conjecture 2 with `-1 < D_35 < 0`. -/
theorem exists_planar_35_violating_conjecture_2 :
    ∃ x : DistinctPoints 35, IsCoplanar x ∧
      (atiyahDet x).im = 0 ∧ (atiyahDet x).re < 0 ∧ ‖atiyahDet x‖ < 1 := by
  sorry

/-- Planar `n = 35` singular configuration (`D_35 = 0`) refuting C1 and C2. -/
theorem exists_planar_35_atiyahDet_zero :
    ∃ x : DistinctPoints 35, IsCoplanar x ∧
      atiyahDet x = 0 ∧
      ¬ LinearIndependent ℂ (fun i : Fin 35 =>
          atiyahPoly (fun u v => canonicalSpinor (unitDir (x.1 u) (x.1 v))) i) := by
  sorry

/-- Strictly non-coplanar 3D `n = 37` mirror-pair witness directly violating Conjecture 2 with `-1 < D_37 < 0`. -/
theorem exists_noncoplanar_37_violating_conjecture_2 :
    ∃ x : DistinctPoints 37, ¬ IsCoplanar x ∧
      (atiyahDet x).im = 0 ∧ (atiyahDet x).re < 0 ∧ ‖atiyahDet x‖ < 1 := by
  sorry

/-- Disproof of Hyperbolic Atiyah–Sutcliffe Conjecture 3 in `ℍ²` and `ℍ³` at `n = 5`. -/
theorem disproof_hyperbolic_atiyah_sutcliffe_conjecture_3 :
    ¬ HyperbolicAtiyahSutcliffeConjecture3Prop := by
  sorry

/-- Disproof of Hyperbolic Atiyah Conjecture 1 (determinant form) in `ℍ³`. -/
theorem disproof_hyperbolic_atiyah_det_nonzero : ¬ HyperbolicAtiyahDetNonzeroProp := by
  sorry

/-- Disproof of Hyperbolic Atiyah Conjecture 1 (polynomial linear independence form) in `ℍ³`. -/
theorem disproof_hyperbolic_atiyah_conjecture_1 : ¬ HyperbolicAtiyahConjecture1Prop := by
  sorry

/-- Disproof of Hyperbolic Atiyah–Sutcliffe Conjecture 2 in `ℍ³`. -/
theorem disproof_hyperbolic_atiyah_sutcliffe_conjecture_2 :
    ¬ HyperbolicAtiyahSutcliffeConjecture2Prop := by
  sorry

/-- Strictly non-coplanar `ℍ³` `n = 59` witness directly violating Hyperbolic C2 (`-1 < D_59^ℍ < 0`). -/
theorem exists_noncoplanar_59_hyperbolic_violating_conjecture_2 :
    ∃ q : KleinBallPoints 59, ¬ IsHyperbolicCoplanar q ∧
      (hyperbolicAtiyahDet q).im = 0 ∧ (hyperbolicAtiyahDet q).re < 0 ∧ ‖hyperbolicAtiyahDet q‖ < 1 := by
  sorry

/-- Lowered strictly non-coplanar `ℍ³` `n = 26` singular configuration (`D_26^ℍ = 0`). -/
theorem exists_noncoplanar_26_hyperbolic_atiyahDet_zero :
    ∃ q : KleinBallPoints 26, ¬ IsHyperbolicCoplanar q ∧
      hyperbolicAtiyahDet q = 0 ∧ ¬ LinearIndependent ℂ (fun i : Fin 26 => hyperbolicAtiyahPoly q i) := by
  sorry

/-- Lowered strictly non-coplanar `ℍ³` `n = 26` direct nonzero C2 witness (`-1 < D_26^ℍ < 0`). -/
theorem exists_noncoplanar_26_hyperbolic_violating_conjecture_2 :
    ∃ q : KleinBallPoints 26, ¬ IsHyperbolicCoplanar q ∧
      (hyperbolicAtiyahDet q).im = 0 ∧ (hyperbolicAtiyahDet q).re < 0 ∧ ‖hyperbolicAtiyahDet q‖ < 1 := by
  sorry

/-- Disproof of Symplectic Atiyah Conjecture 1 at `Sp(18)` (`2m = 36`, strictly non-coplanar 3D). -/
theorem disproof_symplectic_18_conjecture_1 : ¬ SymplecticAtiyahConjecture1Prop 18 := by
  sorry

/-- Disproof of Orthogonal `B_18` (`SO(37)`, `n = 37`) Atiyah Conjecture 1. -/
theorem disproof_orthogonalB_18_conjecture_1 : ¬ OrthogonalBAtiyahConjecture1Prop 18 := by
  sorry

/-- Schur–Weyl / `SU(2) × S_m` rigidity: every equivariant multilinear spinor polynomial is scalar-proportional to Atiyah's product. -/
theorem su2_symmetric_multilinear_eq_atiyahFactor {m : ℕ}
    {Φ : (Fin m → Fin 2 → ℂ) → Polynomial ℂ} (hΦ : IsSpinorEquivariantMultilinear m Φ) :
    ∃ c : ℂ, ∀ v : Fin m → Fin 2 → ℂ, Φ v = Polynomial.C c * ∏ k : Fin m, atiyahLinearFactor (v k) := by
  sorry

/-- Universal holomorphic spinor No-Go at non-coplanar 3D `n = 26` under arbitrary multi-body scalar weights. -/
theorem universal_holomorphic_spinor_nogo_noncoplanar_3d_26
    {ι : Type*} [Fintype ι]
    (Φ : ι → (Fin 25 → Fin 2 → ℂ) → Polynomial ℂ)
    (hΦ : ∀ α : ι, IsSpinorEquivariantMultilinear 25 (Φ α))
    (W : ι → DistinctPoints 26 → Fin 26 → ℂ) :
    ∃ x : DistinctPoints 26, Noncoplanar3D x.1 ∧
      ¬ LinearIndependent ℂ (fun i : Fin 26 => weightedSpinorCandidate Φ W x i) := by
  sorry

/-- Concrete unconditional witness verifying `D_3^ℍ > 1` on a Klein triangle in `B³`. -/
theorem exists_hyperbolic_three_point_det_gt_one :
    ∃ q : KleinBallPoints 3, (hyperbolicAtiyahDet q).im = 0 ∧ 1 < (hyperbolicAtiyahDet q).re := by
  sorry

end Challenge
