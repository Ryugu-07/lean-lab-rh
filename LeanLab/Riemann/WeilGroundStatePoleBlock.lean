import LeanLab.Riemann.WeilGroundStateFiniteMatrix

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The finite Weil pole block

This module instantiates the pole block in the finite-prime Weil matrix. It proves the exact
closed divided-difference formula and its even-positive minus odd-positive rank-two decomposition.
It does not assemble the prime or archimedean blocks.
-/

open Matrix
open scoped BigOperators Matrix

namespace LeanLab.Riemann

noncomputable section

/-- The source parameter `beta = log(c)/(4*pi)`. -/
def weilPoleBeta (c : ℝ) : ℝ :=
  Real.log c / (4 * Real.pi)

/-- The scalar multiplying the finite source pole matrix. -/
def weilPoleCoefficient (c : ℝ) : ℝ :=
  Real.log c * (Real.sqrt c + 1 / Real.sqrt c - 2) / (2 * Real.pi ^ 2)

theorem weilPoleBeta_pos {c : ℝ} (hc : 1 < c) :
    0 < weilPoleBeta c := by
  exact div_pos (Real.log_pos hc) (mul_pos (by norm_num) Real.pi_pos)

theorem weilPoleCoefficient_pos {c : ℝ} (hc : 1 < c) :
    0 < weilPoleCoefficient c := by
  have hsqrt : 1 < Real.sqrt c := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num) hc
  have hsqrt_pos : 0 < Real.sqrt c := lt_trans zero_lt_one hsqrt
  have hbracket : 0 < Real.sqrt c + 1 / Real.sqrt c - 2 := by
    calc
      Real.sqrt c + 1 / Real.sqrt c - 2 =
          (Real.sqrt c - 1) ^ 2 / Real.sqrt c := by
            field_simp [ne_of_gt hsqrt_pos]
            ring
      _ > 0 := div_pos (sq_pos_of_pos (sub_pos.mpr hsqrt)) hsqrt_pos
  exact div_pos (mul_pos (Real.log_pos hc) hbracket)
    (mul_pos (by norm_num) (sq_pos_of_pos Real.pi_pos))

/-- The real centered frequency represented by a finite source index. -/
def weilPoleFrequency (N : ℕ) (i : Fin (2 * N + 1)) : ℝ :=
  weilFiniteCenteredFrequency N i

theorem weilPoleFrequency_rev (N : ℕ) (i : Fin (2 * N + 1)) :
    weilPoleFrequency N i.rev = -weilPoleFrequency N i := by
  simp [weilPoleFrequency, weilFiniteCenteredFrequency_rev]

/-- Source value sample `psi_0(k)`. -/
def weilPoleSourceValue (c : ℝ) (N : ℕ) (i : Fin (2 * N + 1)) : ℝ :=
  weilPoleCoefficient c * weilPoleFrequency N i /
    (weilPoleFrequency N i ^ 2 + weilPoleBeta c ^ 2)

/-- Source derivative sample `psi_0'(k)`. -/
def weilPoleSourceDerivative (c : ℝ) (N : ℕ) (i : Fin (2 * N + 1)) : ℝ :=
  weilPoleCoefficient c *
    (weilPoleBeta c ^ 2 - weilPoleFrequency N i ^ 2) /
      (weilPoleFrequency N i ^ 2 + weilPoleBeta c ^ 2) ^ 2

theorem weilPoleSourceValue_rev (c : ℝ) (N : ℕ) (i : Fin (2 * N + 1)) :
    weilPoleSourceValue c N i.rev = -weilPoleSourceValue c N i := by
  rw [weilPoleSourceValue, weilPoleSourceValue, weilPoleFrequency_rev]
  ring

theorem weilPoleSourceDerivative_rev (c : ℝ) (N : ℕ)
    (i : Fin (2 * N + 1)) :
    weilPoleSourceDerivative c N i.rev = weilPoleSourceDerivative c N i := by
  rw [weilPoleSourceDerivative, weilPoleSourceDerivative, weilPoleFrequency_rev]
  ring

/-- The pole block defined from the exact source value and derivative samples. -/
def weilFinitePoleSourceMatrix (c : ℝ) (N : ℕ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ :=
  weilFiniteDividedDifferenceMatrix N
    (weilPoleSourceDerivative c N) (weilPoleSourceValue c N)

/-- The closed source formula for a pole-block entry. -/
def weilFinitePoleClosedEntry (c : ℝ) (N : ℕ)
    (i j : Fin (2 * N + 1)) : ℝ :=
  weilPoleCoefficient c *
    (weilPoleBeta c ^ 2 - weilPoleFrequency N i * weilPoleFrequency N j) /
      ((weilPoleFrequency N i ^ 2 + weilPoleBeta c ^ 2) *
        (weilPoleFrequency N j ^ 2 + weilPoleBeta c ^ 2))

theorem weilPoleDenominator_pos {c : ℝ} (hc : 1 < c) (N : ℕ)
    (i : Fin (2 * N + 1)) :
    0 < weilPoleFrequency N i ^ 2 + weilPoleBeta c ^ 2 := by
  have hb := weilPoleBeta_pos hc
  positivity

theorem weilFinitePoleSourceMatrix_apply {c : ℝ} (hc : 1 < c) (N : ℕ)
    (i j : Fin (2 * N + 1)) :
    weilFinitePoleSourceMatrix c N i j = weilFinitePoleClosedEntry c N i j := by
  by_cases hij : i = j
  · subst j
    simp [weilFinitePoleSourceMatrix, weilFiniteDividedDifferenceMatrix,
      weilFinitePoleClosedEntry, weilPoleSourceDerivative]
    ring
  · have hdiffInt := weilFiniteCenteredFrequency_sub_ne_zero hij
    have hdiff : weilPoleFrequency N i - weilPoleFrequency N j ≠ 0 := by
      have hdiffCast :
          ((weilFiniteCenteredFrequency N i -
            weilFiniteCenteredFrequency N j : ℤ) : ℝ) ≠ 0 := by
        exact_mod_cast hdiffInt
      simpa [weilPoleFrequency, Int.cast_sub] using hdiffCast
    have hdi := (weilPoleDenominator_pos hc N i).ne'
    have hdj := (weilPoleDenominator_pos hc N j).ne'
    simp only [weilFinitePoleSourceMatrix, weilFiniteDividedDifferenceMatrix, hij, if_false]
    rw [weilPoleSourceValue, weilPoleSourceValue]
    rw [show
      ((weilFiniteCenteredFrequency N i -
        weilFiniteCenteredFrequency N j : ℤ) : ℝ) =
          weilPoleFrequency N i - weilPoleFrequency N j by
        simp [weilPoleFrequency, Int.cast_sub]]
    change
      (weilPoleCoefficient c * weilPoleFrequency N i /
            (weilPoleFrequency N i ^ 2 + weilPoleBeta c ^ 2) -
          weilPoleCoefficient c * weilPoleFrequency N j /
            (weilPoleFrequency N j ^ 2 + weilPoleBeta c ^ 2)) /
          (weilPoleFrequency N i - weilPoleFrequency N j) =
        weilFinitePoleClosedEntry c N i j
    rw [weilFinitePoleClosedEntry]
    field_simp [hdiff, hdi, hdj]
    ring

theorem weilFinitePoleSourceMatrix_eq_closed {c : ℝ} (hc : 1 < c) (N : ℕ) :
    weilFinitePoleSourceMatrix c N =
      fun i j => weilFinitePoleClosedEntry c N i j := by
  ext i j
  exact weilFinitePoleSourceMatrix_apply hc N i j

/-- The reflection-even vector in the source rank-two pole decomposition. -/
def weilFinitePoleEvenVector (c : ℝ) (N : ℕ) : Fin (2 * N + 1) → ℝ :=
  fun i => weilPoleBeta c /
    (weilPoleFrequency N i ^ 2 + weilPoleBeta c ^ 2)

/-- The reflection-odd vector in the source rank-two pole decomposition. -/
def weilFinitePoleOddVector (c : ℝ) (N : ℕ) : Fin (2 * N + 1) → ℝ :=
  fun i => weilPoleFrequency N i /
    (weilPoleFrequency N i ^ 2 + weilPoleBeta c ^ 2)

theorem weilFinitePoleEvenVector_isEven (c : ℝ) (N : ℕ) :
    WeilFiniteIsEven (weilFinitePoleEvenVector c N) := by
  rw [weilFiniteIsEven_iff]
  intro i
  simp [weilFinitePoleEvenVector, weilPoleFrequency_rev]

theorem weilFinitePoleOddVector_isOdd (c : ℝ) (N : ℕ) :
    WeilFiniteIsOdd (weilFinitePoleOddVector c N) := by
  rw [weilFiniteIsOdd_iff]
  intro i
  rw [weilFinitePoleOddVector, weilFinitePoleOddVector, weilPoleFrequency_rev]
  ring

theorem weilFinitePoleClosedEntry_eq_rankTwo {c : ℝ} (hc : 1 < c) (N : ℕ)
    (i j : Fin (2 * N + 1)) :
    weilFinitePoleClosedEntry c N i j =
      weilPoleCoefficient c *
        (weilFinitePoleEvenVector c N i * weilFinitePoleEvenVector c N j -
          weilFinitePoleOddVector c N i * weilFinitePoleOddVector c N j) := by
  have hdi := (weilPoleDenominator_pos hc N i).ne'
  have hdj := (weilPoleDenominator_pos hc N j).ne'
  rw [weilFinitePoleClosedEntry, weilFinitePoleEvenVector, weilFinitePoleEvenVector,
    weilFinitePoleOddVector, weilFinitePoleOddVector]
  field_simp [hdi, hdj]

theorem weilFinitePoleSourceMatrix_rankTwo {c : ℝ} (hc : 1 < c) (N : ℕ) :
    weilFinitePoleSourceMatrix c N =
      weilPoleCoefficient c •
        (Matrix.vecMulVec (weilFinitePoleEvenVector c N) (weilFinitePoleEvenVector c N) -
          Matrix.vecMulVec (weilFinitePoleOddVector c N) (weilFinitePoleOddVector c N)) := by
  ext i j
  rw [weilFinitePoleSourceMatrix_apply hc N i j,
    weilFinitePoleClosedEntry_eq_rankTwo hc N i j]
  simp [Matrix.vecMulVec]

theorem weilFinitePoleSourceMatrix_quadratic {c : ℝ} (hc : 1 < c) (N : ℕ)
    (x : Fin (2 * N + 1) → ℝ) :
    x ⬝ᵥ (weilFinitePoleSourceMatrix c N *ᵥ x) =
      weilPoleCoefficient c *
        ((weilFinitePoleEvenVector c N ⬝ᵥ x) ^ 2 -
          (weilFinitePoleOddVector c N ⬝ᵥ x) ^ 2) := by
  rw [weilFinitePoleSourceMatrix_rankTwo hc N, Matrix.smul_mulVec,
    Matrix.sub_mulVec, Matrix.vecMulVec_mulVec, Matrix.vecMulVec_mulVec]
  simp only [dotProduct_smul, dotProduct_sub, op_smul_eq_mul]
  rw [dotProduct_comm x (weilFinitePoleEvenVector c N),
    dotProduct_comm x (weilFinitePoleOddVector c N)]
  ring

theorem weilFinitePoleSourceMatrix_quadratic_even {c : ℝ} (hc : 1 < c) (N : ℕ)
    {x : Fin (2 * N + 1) → ℝ} (hx : WeilFiniteIsEven x) :
    x ⬝ᵥ (weilFinitePoleSourceMatrix c N *ᵥ x) =
      weilPoleCoefficient c * (weilFinitePoleEvenVector c N ⬝ᵥ x) ^ 2 := by
  have hxo : weilFinitePoleOddVector c N ⬝ᵥ x = 0 := by
    rw [dotProduct_comm]
    exact weilFiniteEven_dotProduct_odd_eq_zero hx
      (weilFinitePoleOddVector_isOdd c N)
  rw [weilFinitePoleSourceMatrix_quadratic hc N x, hxo]
  ring

theorem weilFinitePoleSourceMatrix_quadratic_odd {c : ℝ} (hc : 1 < c) (N : ℕ)
    {x : Fin (2 * N + 1) → ℝ} (hx : WeilFiniteIsOdd x) :
    x ⬝ᵥ (weilFinitePoleSourceMatrix c N *ᵥ x) =
      -weilPoleCoefficient c * (weilFinitePoleOddVector c N ⬝ᵥ x) ^ 2 := by
  have hxe : weilFinitePoleEvenVector c N ⬝ᵥ x = 0 :=
    weilFiniteEven_dotProduct_odd_eq_zero
      (weilFinitePoleEvenVector_isEven c N) hx
  rw [weilFinitePoleSourceMatrix_quadratic hc N x, hxe]
  ring

theorem weilFinitePoleSourceMatrix_nonneg_even {c : ℝ} (hc : 1 < c) (N : ℕ)
    {x : Fin (2 * N + 1) → ℝ} (hx : WeilFiniteIsEven x) :
    0 ≤ x ⬝ᵥ (weilFinitePoleSourceMatrix c N *ᵥ x) := by
  rw [weilFinitePoleSourceMatrix_quadratic_even hc N hx]
  positivity [weilPoleCoefficient_pos hc]

theorem weilFinitePoleSourceMatrix_nonpos_odd {c : ℝ} (hc : 1 < c) (N : ℕ)
    {x : Fin (2 * N + 1) → ℝ} (hx : WeilFiniteIsOdd x) :
    x ⬝ᵥ (weilFinitePoleSourceMatrix c N *ᵥ x) ≤ 0 := by
  rw [weilFinitePoleSourceMatrix_quadratic_odd hc N hx]
  nlinarith [weilPoleCoefficient_pos hc,
    sq_nonneg (weilFinitePoleOddVector c N ⬝ᵥ x)]

theorem weilFinitePoleBlockAudit_endpoint {c : ℝ} (hc : 1 < c) (N : ℕ) :
    0 < weilPoleCoefficient c ∧
      weilFinitePoleSourceMatrix c N =
        weilPoleCoefficient c •
          (Matrix.vecMulVec (weilFinitePoleEvenVector c N) (weilFinitePoleEvenVector c N) -
            Matrix.vecMulVec (weilFinitePoleOddVector c N) (weilFinitePoleOddVector c N)) ∧
      (∀ x, WeilFiniteIsEven x →
        0 ≤ x ⬝ᵥ (weilFinitePoleSourceMatrix c N *ᵥ x)) ∧
      (∀ x, WeilFiniteIsOdd x →
        x ⬝ᵥ (weilFinitePoleSourceMatrix c N *ᵥ x) ≤ 0) := by
  refine ⟨weilPoleCoefficient_pos hc, weilFinitePoleSourceMatrix_rankTwo hc N, ?_, ?_⟩
  · intro x hx
    exact weilFinitePoleSourceMatrix_nonneg_even hc N hx
  · intro x hx
    exact weilFinitePoleSourceMatrix_nonpos_odd hc N hx

end

end LeanLab.Riemann
