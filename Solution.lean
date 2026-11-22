import Mathlib
import Matematyka.AtiyahSutcliffe
import Matematyka.AtiyahSutcliffeExtensions
import Matematyka.AtiyahSutcliffe3D36

/-!
# Solution: Explicit Finite Counterexamples to Euclidean & Hyperbolic Atiyah–Sutcliffe Conjectures

Supplies kernel-verified proofs for every theorem declared in `Challenge.lean` and audited in
`comparator.json`, bridging `namespace Challenge` definitions directly to
`Matematyka.AtiyahSutcliffe*`.
-/

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

/-- Disproof of Euclidean Atiyah–Sutcliffe Conjecture 3 at sharp minimal `n = 5`. -/
theorem disproof_atiyah_sutcliffe_conjecture_3 : ¬ AtiyahSutcliffeConjecture3Prop :=
  Matematyka.AtiyahSutcliffe.disproof_atiyah_sutcliffe_conjecture_3

/-- Explicit 5-point witness violating Euclidean Conjecture 3 (`|D₅|³ < ∏ |D₄|`). -/
theorem exists_five_planar_points_violating_conjecture_3 :
    ∃ x : DistinctPoints 5,
      ‖atiyahDet x‖ ^ (5 - 2) < ∏ k : Fin 5, ‖atiyahDet (deletePoint x k)‖ :=
  Matematyka.AtiyahSutcliffe.exists_five_planar_points_violating_conjecture_3

/-- Disproof of Euclidean Atiyah Conjecture 1 (determinant non-vanishing form). -/
theorem disproof_atiyah_det_nonzero : ¬ AtiyahDetNonzeroProp :=
  Matematyka.AtiyahSutcliffe.disproof_atiyah_det_nonzero

/-- Disproof of Euclidean Atiyah Conjecture 1 (polynomial linear independence form). -/
theorem disproof_atiyah_conjecture_1 : ¬ AtiyahConjecture1Prop :=
  Matematyka.AtiyahSutcliffe.disproof_atiyah_conjecture_1

/-- Disproof of Euclidean Atiyah–Sutcliffe Conjecture 2 (`|D_n| ≥ 1`). -/
theorem disproof_atiyah_sutcliffe_conjecture_2 : ¬ AtiyahSutcliffeConjecture2Prop :=
  Matematyka.AtiyahSutcliffe.disproof_atiyah_sutcliffe_conjecture_2

/-- Genuinely non-coplanar 3D `n = 36` singular configuration (`D_36 = 0`) from coaxial Pythagorean `(33,56,65)` rings. -/
theorem exists_noncoplanar_3d_36_atiyahDet_zero :
    ∃ x : DistinctPoints 36, Noncoplanar3D x.1 ∧ atiyahDet x = 0 :=
  Matematyka.AtiyahSutcliffe3D36.exists_noncoplanar_3d_36_atiyahDet_zero

/-- Strictly non-coplanar 3D `n = 59` witness directly violating Conjecture 2 with `-1 < D_59 < 0`. -/
theorem exists_noncoplanar_59_violating_conjecture_2 :
    ∃ x : DistinctPoints 59, ¬ IsCoplanar x ∧
      (atiyahDet x).im = 0 ∧ (atiyahDet x).re < 0 ∧ ‖atiyahDet x‖ < 1 :=
  Matematyka.AtiyahSutcliffe.exists_noncoplanar_59_violating_conjecture_2

/-- Disproof of Hyperbolic Atiyah–Sutcliffe Conjecture 3 in `ℍ²` and `ℍ³` at `n = 5`. -/
theorem disproof_hyperbolic_atiyah_sutcliffe_conjecture_3 :
    ¬ HyperbolicAtiyahSutcliffeConjecture3Prop :=
  Matematyka.AtiyahSutcliffe.disproof_hyperbolic_atiyah_sutcliffe_conjecture_3

/-- Disproof of Hyperbolic Atiyah Conjecture 1 (determinant form) in `ℍ³`. -/
theorem disproof_hyperbolic_atiyah_det_nonzero : ¬ HyperbolicAtiyahDetNonzeroProp :=
  Matematyka.AtiyahSutcliffe.disproof_hyperbolic_atiyah_det_nonzero

/-- Disproof of Hyperbolic Atiyah Conjecture 1 (polynomial linear independence form) in `ℍ³`. -/
theorem disproof_hyperbolic_atiyah_conjecture_1 : ¬ HyperbolicAtiyahConjecture1Prop :=
  Matematyka.AtiyahSutcliffe.disproof_hyperbolic_atiyah_conjecture_1

/-- Disproof of Hyperbolic Atiyah–Sutcliffe Conjecture 2 in `ℍ³`. -/
theorem disproof_hyperbolic_atiyah_sutcliffe_conjecture_2 :
    ¬ HyperbolicAtiyahSutcliffeConjecture2Prop :=
  Matematyka.AtiyahSutcliffe.disproof_hyperbolic_atiyah_sutcliffe_conjecture_2

/-- Strictly non-coplanar `ℍ³` `n = 59` witness directly violating Hyperbolic C2 (`-1 < D_59^ℍ < 0`). -/
theorem exists_noncoplanar_59_hyperbolic_violating_conjecture_2 :
    ∃ q : KleinBallPoints 59, ¬ IsHyperbolicCoplanar q ∧
      (hyperbolicAtiyahDet q).im = 0 ∧ (hyperbolicAtiyahDet q).re < 0 ∧ ‖hyperbolicAtiyahDet q‖ < 1 :=
  Matematyka.AtiyahSutcliffe.exists_noncoplanar_59_hyperbolic_violating_conjecture_2

end Challenge
