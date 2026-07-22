import LeanLab.Riemann.WeilGroundStateAlignment
import Mathlib.Data.Fin.Rev
import Mathlib.LinearAlgebra.Matrix.PosDef

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Finite Weil divided-difference matrices and reflection parity

This module formalizes the finite matrix shape and the `even-simple` certificate used by the
finite-prime Weil ground-state program. The index `Fin (2 * N + 1)` represents the source band
`{-N, ..., N}` in increasing order.
-/

open Matrix
open scoped BigOperators Matrix

namespace LeanLab.Riemann

noncomputable section

/-- The centered source frequency represented by a finite matrix index. -/
def weilFiniteCenteredFrequency (N : ℕ) (i : Fin (2 * N + 1)) : ℤ :=
  (i.1 : ℤ) - N

theorem weilFiniteCenteredFrequency_rev (N : ℕ) (i : Fin (2 * N + 1)) :
    weilFiniteCenteredFrequency N i.rev = -weilFiniteCenteredFrequency N i := by
  have hsum : i.1 + i.rev.1 = 2 * N := by
    simpa using Fin.add_rev_cast i
  unfold weilFiniteCenteredFrequency
  omega

theorem weilFiniteCenteredFrequency_injective (N : ℕ) :
    Function.Injective (weilFiniteCenteredFrequency N) := by
  intro i j hij
  unfold weilFiniteCenteredFrequency at hij
  have hval : i.1 = j.1 := by omega
  exact Fin.ext hval

theorem weilFiniteCenteredFrequency_sub_ne_zero {N : ℕ}
    {i j : Fin (2 * N + 1)} (hij : i ≠ j) :
    weilFiniteCenteredFrequency N i - weilFiniteCenteredFrequency N j ≠ 0 :=
  sub_ne_zero.mpr ((weilFiniteCenteredFrequency_injective N).ne hij)

/-- Reflection of a finite source vector across its centered index. -/
def weilFiniteReflect {N : ℕ} (x : Fin (2 * N + 1) → ℝ) : Fin (2 * N + 1) → ℝ :=
  x ∘ Fin.revPerm

@[simp]
theorem weilFiniteReflect_apply {N : ℕ} (x : Fin (2 * N + 1) → ℝ)
    (i : Fin (2 * N + 1)) :
    weilFiniteReflect x i = x i.rev :=
  rfl

@[simp]
theorem weilFiniteReflect_reflect {N : ℕ} (x : Fin (2 * N + 1) → ℝ) :
    weilFiniteReflect (weilFiniteReflect x) = x := by
  ext i
  simp [weilFiniteReflect]

/-- A finite source vector in the reflection-even sector. -/
def WeilFiniteIsEven {N : ℕ} (x : Fin (2 * N + 1) → ℝ) : Prop :=
  weilFiniteReflect x = x

/-- A finite source vector in the reflection-odd sector. -/
def WeilFiniteIsOdd {N : ℕ} (x : Fin (2 * N + 1) → ℝ) : Prop :=
  weilFiniteReflect x = -x

theorem weilFiniteIsEven_iff {N : ℕ} {x : Fin (2 * N + 1) → ℝ} :
    WeilFiniteIsEven x ↔ ∀ i, x i.rev = x i := by
  simp [WeilFiniteIsEven, funext_iff]

theorem weilFiniteIsOdd_iff {N : ℕ} {x : Fin (2 * N + 1) → ℝ} :
    WeilFiniteIsOdd x ↔ ∀ i, x i.rev = -x i := by
  simp [WeilFiniteIsOdd, funext_iff]

theorem weilFiniteIsEven_zero (N : ℕ) :
    WeilFiniteIsEven (0 : Fin (2 * N + 1) → ℝ) := by
  rw [weilFiniteIsEven_iff]
  simp

theorem WeilFiniteIsEven.add {N : ℕ} {x y : Fin (2 * N + 1) → ℝ}
    (hx : WeilFiniteIsEven x) (hy : WeilFiniteIsEven y) :
    WeilFiniteIsEven (x + y) := by
  rw [weilFiniteIsEven_iff] at hx hy ⊢
  intro i
  simp [hx i, hy i]

theorem WeilFiniteIsEven.sub {N : ℕ} {x y : Fin (2 * N + 1) → ℝ}
    (hx : WeilFiniteIsEven x) (hy : WeilFiniteIsEven y) :
    WeilFiniteIsEven (x - y) := by
  rw [weilFiniteIsEven_iff] at hx hy ⊢
  intro i
  simp [hx i, hy i]

theorem WeilFiniteIsEven.smul {N : ℕ} {x : Fin (2 * N + 1) → ℝ}
    (hx : WeilFiniteIsEven x) (c : ℝ) :
    WeilFiniteIsEven (c • x) := by
  rw [weilFiniteIsEven_iff] at hx ⊢
  intro i
  simp [hx i]

theorem weilFiniteIsOdd_zero (N : ℕ) :
    WeilFiniteIsOdd (0 : Fin (2 * N + 1) → ℝ) := by
  rw [weilFiniteIsOdd_iff]
  simp

theorem WeilFiniteIsOdd.add {N : ℕ} {x y : Fin (2 * N + 1) → ℝ}
    (hx : WeilFiniteIsOdd x) (hy : WeilFiniteIsOdd y) :
    WeilFiniteIsOdd (x + y) := by
  rw [weilFiniteIsOdd_iff] at hx hy ⊢
  intro i
  simp [hx i, hy i]
  ring

theorem WeilFiniteIsOdd.sub {N : ℕ} {x y : Fin (2 * N + 1) → ℝ}
    (hx : WeilFiniteIsOdd x) (hy : WeilFiniteIsOdd y) :
    WeilFiniteIsOdd (x - y) := by
  rw [weilFiniteIsOdd_iff] at hx hy ⊢
  intro i
  simp [hx i, hy i]
  ring

theorem WeilFiniteIsOdd.smul {N : ℕ} {x : Fin (2 * N + 1) → ℝ}
    (hx : WeilFiniteIsOdd x) (c : ℝ) :
    WeilFiniteIsOdd (c • x) := by
  rw [weilFiniteIsOdd_iff] at hx ⊢
  intro i
  simp [hx i]

/-- Reflection-even part of a finite source vector. -/
def weilFiniteEvenPart {N : ℕ} (x : Fin (2 * N + 1) → ℝ) :
    Fin (2 * N + 1) → ℝ :=
  fun i => (x i + x i.rev) / 2

/-- Reflection-odd part of a finite source vector. -/
def weilFiniteOddPart {N : ℕ} (x : Fin (2 * N + 1) → ℝ) :
    Fin (2 * N + 1) → ℝ :=
  fun i => (x i - x i.rev) / 2

theorem weilFiniteEvenPart_isEven {N : ℕ} (x : Fin (2 * N + 1) → ℝ) :
    WeilFiniteIsEven (weilFiniteEvenPart x) := by
  rw [weilFiniteIsEven_iff]
  intro i
  simp [weilFiniteEvenPart]
  ring

theorem weilFiniteOddPart_isOdd {N : ℕ} (x : Fin (2 * N + 1) → ℝ) :
    WeilFiniteIsOdd (weilFiniteOddPart x) := by
  rw [weilFiniteIsOdd_iff]
  intro i
  simp [weilFiniteOddPart]
  ring

theorem weilFiniteEvenPart_add_oddPart {N : ℕ} (x : Fin (2 * N + 1) → ℝ) :
    weilFiniteEvenPart x + weilFiniteOddPart x = x := by
  ext i
  simp [weilFiniteEvenPart, weilFiniteOddPart]
  ring

theorem weilFiniteReflect_dotProduct_reflect {N : ℕ}
    (x y : Fin (2 * N + 1) → ℝ) :
    weilFiniteReflect x ⬝ᵥ weilFiniteReflect y = x ⬝ᵥ y := by
  change (x ∘ Fin.revPerm) ⬝ᵥ (y ∘ Fin.revPerm) = x ⬝ᵥ y
  exact comp_equiv_dotProduct_comp_equiv x y
    (Fin.revPerm : Equiv.Perm (Fin (2 * N + 1)))

theorem weilFiniteEven_dotProduct_odd_eq_zero {N : ℕ}
    {x y : Fin (2 * N + 1) → ℝ}
    (hx : WeilFiniteIsEven x) (hy : WeilFiniteIsOdd y) :
    x ⬝ᵥ y = 0 := by
  have hreflect := weilFiniteReflect_dotProduct_reflect x y
  rw [hx, hy] at hreflect
  have hneg : x ⬝ᵥ (-y) = -(x ⬝ᵥ y) := by simp
  rw [hneg] at hreflect
  linarith

theorem weilFiniteEvenPart_dotProduct_oddPart_eq_zero {N : ℕ}
    (x : Fin (2 * N + 1) → ℝ) :
    weilFiniteEvenPart x ⬝ᵥ weilFiniteOddPart x = 0 :=
  weilFiniteEven_dotProduct_odd_eq_zero
    (weilFiniteEvenPart_isEven x) (weilFiniteOddPart_isOdd x)

/-- The source divided-difference matrix with independently supplied diagonal samples. -/
def weilFiniteDividedDifferenceMatrix (N : ℕ)
    (a b : Fin (2 * N + 1) → ℝ) : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ :=
  fun i j => if i = j then a i else
    (b i - b j) /
      ((weilFiniteCenteredFrequency N i - weilFiniteCenteredFrequency N j : ℤ) : ℝ)

theorem weilFiniteDividedDifferenceMatrix_transpose (N : ℕ)
    (a b : Fin (2 * N + 1) → ℝ) :
    (weilFiniteDividedDifferenceMatrix N a b)ᵀ =
      weilFiniteDividedDifferenceMatrix N a b := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [weilFiniteDividedDifferenceMatrix]
  · have hji : j ≠ i := Ne.symm hij
    simp only [transpose_apply, weilFiniteDividedDifferenceMatrix, hij, hji, if_false]
    have hden :
        ((weilFiniteCenteredFrequency N j - weilFiniteCenteredFrequency N i : ℤ) : ℝ) =
          -((weilFiniteCenteredFrequency N i - weilFiniteCenteredFrequency N j : ℤ) : ℝ) := by
      push_cast
      ring
    rw [hden]
    ring

theorem weilFiniteDividedDifferenceMatrix_reflection (N : ℕ)
    (a b : Fin (2 * N + 1) → ℝ)
    (ha : ∀ i, a i.rev = a i) (hb : ∀ i, b i.rev = -b i)
    (i j : Fin (2 * N + 1)) :
    weilFiniteDividedDifferenceMatrix N a b i.rev j.rev =
      weilFiniteDividedDifferenceMatrix N a b i j := by
  by_cases hij : i = j
  · subst j
    simp [weilFiniteDividedDifferenceMatrix, ha]
  · have hrev : i.rev ≠ j.rev := Fin.rev_injective.ne hij
    simp only [weilFiniteDividedDifferenceMatrix, hij, hrev, if_false]
    rw [hb i, hb j, weilFiniteCenteredFrequency_rev,
      weilFiniteCenteredFrequency_rev]
    push_cast
    have hden :
        -(weilFiniteCenteredFrequency N i : ℝ) -
            -(weilFiniteCenteredFrequency N j : ℝ) =
          -((weilFiniteCenteredFrequency N i : ℝ) - weilFiniteCenteredFrequency N j) := by
      ring
    rw [hden, div_neg]
    ring

/-- The centered frequency operator used in the source commutator identity. -/
def weilFiniteFrequencyDiagonal (N : ℕ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ :=
  Matrix.diagonal fun i => weilFiniteCenteredFrequency N i

/-- The all-ones vector in the source rank-two commutator. -/
def weilFiniteEta (N : ℕ) : Fin (2 * N + 1) → ℝ :=
  fun _ => 1

theorem weilFiniteDividedDifferenceMatrix_commutator (N : ℕ)
    (a b : Fin (2 * N + 1) → ℝ) :
    weilFiniteFrequencyDiagonal N * weilFiniteDividedDifferenceMatrix N a b -
        weilFiniteDividedDifferenceMatrix N a b * weilFiniteFrequencyDiagonal N =
      Matrix.vecMulVec b (weilFiniteEta N) -
        Matrix.vecMulVec (weilFiniteEta N) b := by
  ext i j
  unfold weilFiniteFrequencyDiagonal
  rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hij : i = j
  · subst j
    simp [weilFiniteDividedDifferenceMatrix,
      weilFiniteEta, Matrix.vecMulVec]
    ring
  · have hfreqInt := weilFiniteCenteredFrequency_sub_ne_zero hij
    have hfreqReal :
        (weilFiniteCenteredFrequency N i : ℝ) - weilFiniteCenteredFrequency N j ≠ 0 := by
      exact_mod_cast hfreqInt
    simp [weilFiniteDividedDifferenceMatrix, hij, weilFiniteEta, Matrix.vecMulVec]
    field_simp [hfreqReal]

theorem weilFiniteMatrix_mulVec_reflect {N : ℕ}
    (A : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ)
    (hA : ∀ i j, A i.rev j.rev = A i j)
    (x : Fin (2 * N + 1) → ℝ) :
    A *ᵥ weilFiniteReflect x = weilFiniteReflect (A *ᵥ x) := by
  ext i
  change (∑ j, A i j * x j.rev) = ∑ j, A i.rev j * x j
  calc
    (∑ j, A i j * x j.rev) = ∑ j, A i j.rev * x j := by
      have hsum :=
        Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (2 * N + 1)))
          (fun j => A i j * x j.rev)
      simpa using hsum.symm
    _ = ∑ j, A i.rev j * x j := by
      apply Finset.sum_congr rfl
      intro j _
      have hreflect := hA i.rev j
      simpa using congrArg (fun z : ℝ => z * x j) hreflect

theorem weilFiniteDividedDifferenceMatrix_mulVec_reflect (N : ℕ)
    (a b : Fin (2 * N + 1) → ℝ)
    (ha : ∀ i, a i.rev = a i) (hb : ∀ i, b i.rev = -b i)
    (x : Fin (2 * N + 1) → ℝ) :
    weilFiniteDividedDifferenceMatrix N a b *ᵥ weilFiniteReflect x =
      weilFiniteReflect (weilFiniteDividedDifferenceMatrix N a b *ᵥ x) :=
  weilFiniteMatrix_mulVec_reflect _
    (weilFiniteDividedDifferenceMatrix_reflection N a b ha hb) x

theorem weilFiniteMatrix_mulVec_isEven {N : ℕ}
    (A : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ)
    (hA : ∀ i j, A i.rev j.rev = A i j)
    {x : Fin (2 * N + 1) → ℝ} (hx : WeilFiniteIsEven x) :
    WeilFiniteIsEven (A *ᵥ x) := by
  rw [WeilFiniteIsEven] at hx ⊢
  rw [← weilFiniteMatrix_mulVec_reflect A hA, hx]

theorem weilFiniteMatrix_mulVec_isOdd {N : ℕ}
    (A : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ)
    (hA : ∀ i j, A i.rev j.rev = A i j)
    {x : Fin (2 * N + 1) → ℝ} (hx : WeilFiniteIsOdd x) :
    WeilFiniteIsOdd (A *ᵥ x) := by
  rw [WeilFiniteIsOdd] at hx ⊢
  rw [← weilFiniteMatrix_mulVec_reflect A hA, hx, Matrix.mulVec_neg]

theorem weilFiniteDotProduct_self_split {N : ℕ}
    (x : Fin (2 * N + 1) → ℝ) :
    x ⬝ᵥ x =
      weilFiniteEvenPart x ⬝ᵥ weilFiniteEvenPart x +
        weilFiniteOddPart x ⬝ᵥ weilFiniteOddPart x := by
  have hcross := weilFiniteEvenPart_dotProduct_oddPart_eq_zero x
  have hcross' : weilFiniteOddPart x ⬝ᵥ weilFiniteEvenPart x = 0 := by
    rw [dotProduct_comm]
    exact hcross
  conv_lhs =>
    rw [← weilFiniteEvenPart_add_oddPart x]
  simp [add_dotProduct, dotProduct_add, hcross, hcross']

theorem weilFiniteQuadratic_split {N : ℕ}
    (A : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ)
    (hA : ∀ i j, A i.rev j.rev = A i j)
    (x : Fin (2 * N + 1) → ℝ) :
    x ⬝ᵥ (A *ᵥ x) =
      weilFiniteEvenPart x ⬝ᵥ (A *ᵥ weilFiniteEvenPart x) +
        weilFiniteOddPart x ⬝ᵥ (A *ᵥ weilFiniteOddPart x) := by
  have hAe := weilFiniteMatrix_mulVec_isEven A hA (weilFiniteEvenPart_isEven x)
  have hAo := weilFiniteMatrix_mulVec_isOdd A hA (weilFiniteOddPart_isOdd x)
  have hcrossEO : weilFiniteEvenPart x ⬝ᵥ (A *ᵥ weilFiniteOddPart x) = 0 :=
    weilFiniteEven_dotProduct_odd_eq_zero (weilFiniteEvenPart_isEven x) hAo
  have hcrossOE : weilFiniteOddPart x ⬝ᵥ (A *ᵥ weilFiniteEvenPart x) = 0 := by
    rw [dotProduct_comm]
    exact weilFiniteEven_dotProduct_odd_eq_zero hAe (weilFiniteOddPart_isOdd x)
  conv_lhs =>
    rw [← weilFiniteEvenPart_add_oddPart x]
  rw [Matrix.mulVec_add]
  simp [add_dotProduct, dotProduct_add, hcrossEO, hcrossOE]

/-- The quadratic excess over the candidate Rayleigh value `mu`. -/
def weilFiniteRayleighDefect {N : ℕ}
    (A : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ)
    (mu : ℝ) (x : Fin (2 * N + 1) → ℝ) : ℝ :=
  x ⬝ᵥ (A *ᵥ x) - mu * (x ⬝ᵥ x)

theorem weilFiniteRayleighDefect_split {N : ℕ}
    (A : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ)
    (hA : ∀ i j, A i.rev j.rev = A i j)
    (mu : ℝ) (x : Fin (2 * N + 1) → ℝ) :
    weilFiniteRayleighDefect A mu x =
      weilFiniteRayleighDefect A mu (weilFiniteEvenPart x) +
        weilFiniteRayleighDefect A mu (weilFiniteOddPart x) := by
  rw [weilFiniteRayleighDefect, weilFiniteRayleighDefect,
    weilFiniteRayleighDefect, weilFiniteQuadratic_split A hA x,
    weilFiniteDotProduct_self_split]
  ring

theorem weilFiniteRayleighDefect_smul_eigen_add_orthogonal {N : ℕ}
    (A : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ)
    (hAT : Aᵀ = A) (mu : ℝ) (xi y : Fin (2 * N + 1) → ℝ)
    (heigen : A *ᵥ xi = mu • xi) (horth : xi ⬝ᵥ y = 0) (c : ℝ) :
    weilFiniteRayleighDefect A mu (c • xi + y) =
      weilFiniteRayleighDefect A mu y := by
  have horth' : y ⬝ᵥ xi = 0 := by
    rw [dotProduct_comm]
    exact horth
  have hcross : xi ⬝ᵥ (A *ᵥ y) = 0 := by
    have ht := Matrix.dotProduct_transpose_mulVec A y xi
    rw [hAT, heigen] at ht
    calc
      xi ⬝ᵥ (A *ᵥ y) = y ⬝ᵥ (mu • xi) := ht.symm
      _ = 0 := by simp [horth']
  rw [weilFiniteRayleighDefect, weilFiniteRayleighDefect,
    Matrix.mulVec_add, Matrix.mulVec_smul, heigen]
  simp only [add_dotProduct, dotProduct_add]
  simp [horth, horth', hcross]
  ring

/-- Source-faithful finite meaning of a simple ground-state eigenvalue with an even vector. -/
structure WeilFiniteEvenSimpleGroundState {N : ℕ}
    (A : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ)
    (mu : ℝ) (xi : Fin (2 * N + 1) → ℝ) : Prop where
  even_xi : WeilFiniteIsEven xi
  xi_ne_zero : xi ≠ 0
  eigen_xi : A *ᵥ xi = mu • xi
  rayleigh_min : ∀ x, mu * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x)
  equality_iff_smul : ∀ x,
    x ⬝ᵥ (A *ᵥ x) = mu * (x ⬝ᵥ x) ↔ ∃ c : ℝ, x = c • xi

theorem WeilFiniteEvenSimpleGroundState.mulVec_eq_smul_iff {N : ℕ}
    {A : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ}
    {mu : ℝ} {xi x : Fin (2 * N + 1) → ℝ}
    (h : WeilFiniteEvenSimpleGroundState A mu xi) :
    A *ᵥ x = mu • x ↔ ∃ c : ℝ, x = c • xi := by
  constructor
  · intro hx
    apply (h.equality_iff_smul x).mp
    rw [hx, dotProduct_smul]
    ring
  · rintro ⟨c, rfl⟩
    rw [Matrix.mulVec_smul, h.eigen_xi]
    simp [smul_smul]
    ring

/-- Strict positivity on the two parity blocks around one normalized even eigenvector. -/
structure WeilFiniteParityRayleighCertificate {N : ℕ}
    (A : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ)
    (mu : ℝ) (xi : Fin (2 * N + 1) → ℝ) : Prop where
  even_xi : WeilFiniteIsEven xi
  normalized_xi : xi ⬝ᵥ xi = 1
  eigen_xi : A *ᵥ xi = mu • xi
  strict_even : ∀ y, WeilFiniteIsEven y → xi ⬝ᵥ y = 0 → y ≠ 0 →
    mu * (y ⬝ᵥ y) < y ⬝ᵥ (A *ᵥ y)
  strict_odd : ∀ y, WeilFiniteIsOdd y → y ≠ 0 →
    mu * (y ⬝ᵥ y) < y ⬝ᵥ (A *ᵥ y)

theorem WeilFiniteParityRayleighCertificate.xi_ne_zero {N : ℕ}
    {A : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ}
    {mu : ℝ} {xi : Fin (2 * N + 1) → ℝ}
    (h : WeilFiniteParityRayleighCertificate A mu xi) :
    xi ≠ 0 := by
  intro hzero
  subst xi
  simpa using h.normalized_xi

theorem WeilFiniteParityRayleighCertificate.defect_nonneg_and_eq_smul {N : ℕ}
    {A : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ}
    {mu : ℝ} {xi : Fin (2 * N + 1) → ℝ}
    (h : WeilFiniteParityRayleighCertificate A mu xi)
    (hAT : Aᵀ = A) (hAR : ∀ i j, A i.rev j.rev = A i j)
    (x : Fin (2 * N + 1) → ℝ) :
    0 ≤ weilFiniteRayleighDefect A mu x ∧
      (weilFiniteRayleighDefect A mu x = 0 ↔ ∃ c : ℝ, x = c • xi) := by
  let e := weilFiniteEvenPart x
  let o := weilFiniteOddPart x
  let alpha := xi ⬝ᵥ e
  let y := e - alpha • xi
  have he : WeilFiniteIsEven e := by
    exact weilFiniteEvenPart_isEven x
  have ho : WeilFiniteIsOdd o := by
    exact weilFiniteOddPart_isOdd x
  have hy : WeilFiniteIsEven y := by
    exact he.sub (h.even_xi.smul alpha)
  have hyorth : xi ⬝ᵥ y = 0 := by
    dsimp [y, alpha]
    rw [dotProduct_sub, dotProduct_smul, h.normalized_xi]
    ring
  have he_decomp : e = alpha • xi + y := by
    dsimp [y]
    ext i
    simp
  have hdefe :
      weilFiniteRayleighDefect A mu e = weilFiniteRayleighDefect A mu y := by
    rw [he_decomp]
    exact weilFiniteRayleighDefect_smul_eigen_add_orthogonal
      A hAT mu xi y h.eigen_xi hyorth alpha
  have hy_nonneg : 0 ≤ weilFiniteRayleighDefect A mu y := by
    by_cases hyzero : y = 0
    · rw [hyzero]
      simp [weilFiniteRayleighDefect]
    · have hstrict := h.strict_even y hy hyorth hyzero
      unfold weilFiniteRayleighDefect
      linarith
  have hy_eq_zero : weilFiniteRayleighDefect A mu y = 0 ↔ y = 0 := by
    constructor
    · intro hzero
      by_contra hyzero
      have hstrict := h.strict_even y hy hyorth hyzero
      unfold weilFiniteRayleighDefect at hzero
      linarith
    · intro hyzero
      rw [hyzero]
      simp [weilFiniteRayleighDefect]
  have ho_nonneg : 0 ≤ weilFiniteRayleighDefect A mu o := by
    by_cases hozero : o = 0
    · rw [hozero]
      simp [weilFiniteRayleighDefect]
    · have hstrict := h.strict_odd o ho hozero
      unfold weilFiniteRayleighDefect
      linarith
  have ho_eq_zero : weilFiniteRayleighDefect A mu o = 0 ↔ o = 0 := by
    constructor
    · intro hzero
      by_contra hozero
      have hstrict := h.strict_odd o ho hozero
      unfold weilFiniteRayleighDefect at hzero
      linarith
    · intro hozero
      rw [hozero]
      simp [weilFiniteRayleighDefect]
  have hsplit : weilFiniteRayleighDefect A mu x =
      weilFiniteRayleighDefect A mu e + weilFiniteRayleighDefect A mu o := by
    simpa [e, o] using weilFiniteRayleighDefect_split A hAR mu x
  constructor
  · rw [hsplit, hdefe]
    exact add_nonneg hy_nonneg ho_nonneg
  · constructor
    · intro hzero
      have hsum :
          weilFiniteRayleighDefect A mu y + weilFiniteRayleighDefect A mu o = 0 := by
        rw [hsplit, hdefe] at hzero
        exact hzero
      have hyzero : y = 0 := hy_eq_zero.mp (by linarith)
      have hozero : o = 0 := ho_eq_zero.mp (by linarith)
      refine ⟨alpha, ?_⟩
      calc
        x = e + o := (weilFiniteEvenPart_add_oddPart x).symm
        _ = alpha • xi + y + o := by rw [he_decomp]
        _ = alpha • xi := by rw [hyzero, hozero]; simp
    · rintro ⟨c, rfl⟩
      rw [weilFiniteRayleighDefect]
      rw [Matrix.mulVec_smul, h.eigen_xi]
      simp
      ring

theorem WeilFiniteParityRayleighCertificate.evenSimpleGroundState {N : ℕ}
    {A : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ}
    {mu : ℝ} {xi : Fin (2 * N + 1) → ℝ}
    (h : WeilFiniteParityRayleighCertificate A mu xi)
    (hAT : Aᵀ = A) (hAR : ∀ i j, A i.rev j.rev = A i j) :
    WeilFiniteEvenSimpleGroundState A mu xi := by
  have hdefect := h.defect_nonneg_and_eq_smul hAT hAR
  refine
    { even_xi := h.even_xi
      xi_ne_zero := h.xi_ne_zero
      eigen_xi := h.eigen_xi
      rayleigh_min := ?_
      equality_iff_smul := ?_ }
  · intro x
    have hnonneg := (hdefect x).1
    unfold weilFiniteRayleighDefect at hnonneg
    linarith
  · intro x
    have heq := (hdefect x).2
    unfold weilFiniteRayleighDefect at heq
    constructor
    · intro hx
      apply heq.mp
      linarith
    · intro hx
      have := heq.mpr hx
      linarith

theorem weilFiniteDividedDifferenceMatrix_evenSimple_of_parityRayleigh {N : ℕ}
    (a b : Fin (2 * N + 1) → ℝ)
    (ha : ∀ i, a i.rev = a i) (hb : ∀ i, b i.rev = -b i)
    {mu : ℝ} {xi : Fin (2 * N + 1) → ℝ}
    (h : WeilFiniteParityRayleighCertificate
      (weilFiniteDividedDifferenceMatrix N a b) mu xi) :
    WeilFiniteEvenSimpleGroundState
      (weilFiniteDividedDifferenceMatrix N a b) mu xi :=
  h.evenSimpleGroundState
    (weilFiniteDividedDifferenceMatrix_transpose N a b)
    (weilFiniteDividedDifferenceMatrix_reflection N a b ha hb)

end

end LeanLab.Riemann
