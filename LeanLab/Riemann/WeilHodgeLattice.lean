import LeanLab.Riemann.FinitePowerSumRigidity
import Mathlib.Topology.Algebra.Order.Archimedean

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The Hodge-lattice numerical hinge in Weil's surface proof

The Hodge index theorem applies to integral combinations of the diagonal and the Frobenius
graph. This module proves that positivity on that integer lattice is enough to recover the real
quadratic-form bound used in the Hasse--Weil estimate, and then feeds extension-wise bounds into
the existing finite power-sum rigidity theorem.
-/

open Complex Set Topology

namespace LeanLab.Riemann

noncomputable section

/-- The normalized binary quadratic form produced by the diagonal/Frobenius intersection table. -/
def weilHodgeForm (q g N a b : ℝ) : ℝ :=
  2 * (g * q * a ^ 2 + (q + 1 - N) * a * b + g * b ^ 2)

/-- The compact form agrees with the expanded intersection expression in the surface proof. -/
theorem weilHodgeForm_eq_intersectionExpression (q g N a b : ℝ) :
    weilHodgeForm q g N a b =
      2 * (a + b) * (q * a + b) -
        a ^ 2 * q * (2 - 2 * g) -
        b ^ 2 * (2 - 2 * g) -
        2 * a * b * N := by
  simp only [weilHodgeForm]
  ring

/-- The source quadratic form is homogeneous of degree two in the divisor coefficients. -/
theorem weilHodgeForm_scale (q g N c a b : ℝ) :
    weilHodgeForm q g N (c * a) (c * b) =
      c ^ 2 * weilHodgeForm q g N a b := by
  simp only [weilHodgeForm]
  ring

/-- Integer-lattice nonnegativity extends to rational coefficient pairs by common denominators. -/
theorem weilHodgeForm_nonneg_rat_of_int
    {q g N : ℝ}
    (hInt : ∀ a b : ℤ, 0 ≤ weilHodgeForm q g N a b) :
    ∀ a b : ℚ, 0 ≤ weilHodgeForm q g N a b := by
  intro a b
  let d : ℕ := a.den * b.den
  let A : ℤ := a.num * (b.den : ℤ)
  let B : ℤ := b.num * (a.den : ℤ)
  have haDen : (a.num : ℝ) = (a.den : ℝ) * (a : ℝ) := by
    have haDiv : (a.num : ℝ) / (a.den : ℝ) = (a : ℝ) := by
      exact_mod_cast a.num_div_den
    simpa [mul_comm] using
      (div_eq_iff (by positivity : (a.den : ℝ) ≠ 0)).mp haDiv
  have hbDen : (b.num : ℝ) = (b.den : ℝ) * (b : ℝ) := by
    have hbDiv : (b.num : ℝ) / (b.den : ℝ) = (b : ℝ) := by
      exact_mod_cast b.num_div_den
    simpa [mul_comm] using
      (div_eq_iff (by positivity : (b.den : ℝ) ≠ 0)).mp hbDiv
  have hA : (A : ℝ) = (d : ℝ) * (a : ℝ) := by
    dsimp only [A, d]
    push_cast
    rw [haDen]
    ring
  have hB : (B : ℝ) = (d : ℝ) * (b : ℝ) := by
    dsimp only [B, d]
    push_cast
    rw [hbDen]
    ring
  have hdPos : (0 : ℝ) < d := by
    dsimp only [d]
    positivity
  have hAB := hInt A B
  rw [hA, hB, weilHodgeForm_scale] at hAB
  nlinarith [sq_pos_of_pos hdPos]

/-- Rational density and continuity upgrade rational-pair positivity to the full real plane. -/
theorem weilHodgeForm_nonneg_real_of_rat
    {q g N : ℝ}
    (hRat : ∀ a b : ℚ, 0 ≤ weilHodgeForm q g N a b) :
    ∀ a b : ℝ, 0 ≤ weilHodgeForm q g N a b := by
  have hFirst (b : ℚ) (a : ℝ) : 0 ≤ weilHodgeForm q g N a b := by
    refine Rat.denseRange_cast.induction_on a ?_ (fun r => hRat r b)
    exact isClosed_le continuous_const (by
      simp only [weilHodgeForm]
      fun_prop)
  intro a b
  refine Rat.denseRange_cast.induction_on b ?_ (fun r => hFirst r a)
  exact isClosed_le continuous_const (by
    change Continuous fun b : ℝ =>
      2 * (g * q * a ^ 2 + (q + 1 - N) * a * b + g * b ^ 2)
    fun_prop)

/-- Positivity on every integral divisor combination already gives real semipositivity. -/
theorem weilHodgeForm_nonneg_real_of_int
    {q g N : ℝ}
    (hInt : ∀ a b : ℤ, 0 ≤ weilHodgeForm q g N a b) :
    ∀ a b : ℝ, 0 ≤ weilHodgeForm q g N a b :=
  weilHodgeForm_nonneg_real_of_rat (weilHodgeForm_nonneg_rat_of_int hInt)

/-- Real semipositivity gives the exact Hasse--Weil point-count bound. -/
theorem abs_pointCount_sub_le_of_weilHodgeForm_nonneg_real
    {q g N : ℝ} (hq : 0 < q) (hg : 0 ≤ g)
    (hReal : ∀ a b : ℝ, 0 ≤ weilHodgeForm q g N a b) :
    |N - (q + 1)| ≤ 2 * g * Real.sqrt q := by
  by_cases hgZero : g = 0
  · subst g
    have hPlus := hReal 1 1
    have hMinus := hReal 1 (-1)
    simp only [weilHodgeForm] at hPlus hMinus
    have hEq : N - (q + 1) = 0 := by nlinarith
    simp [hEq]
  · have hgPos : 0 < g := lt_of_le_of_ne hg (Ne.symm hgZero)
    have hTest := hReal (2 * g) (N - (q + 1))
    have hSqrtSq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq.le
    have hCore :
        (N - (q + 1)) ^ 2 ≤ 4 * g ^ 2 * q := by
      simp only [weilHodgeForm] at hTest
      ring_nf at hTest
      nlinarith
    have hSq :
        (N - (q + 1)) ^ 2 ≤ (2 * g * Real.sqrt q) ^ 2 := by
      calc
        (N - (q + 1)) ^ 2 ≤ 4 * g ^ 2 * q := hCore
        _ = (2 * g * Real.sqrt q) ^ 2 := by nlinarith
    exact abs_le_of_sq_le_sq hSq (by positivity)

/-- The source's integer-divisor inequality suffices for the Hasse--Weil point-count bound. -/
theorem abs_pointCount_sub_le_of_weilHodgeForm_nonneg_int
    {q g N : ℝ} (hq : 0 < q) (hg : 0 ≤ g)
    (hInt : ∀ a b : ℤ, 0 ≤ weilHodgeForm q g N a b) :
    |N - (q + 1)| ≤ 2 * g * Real.sqrt q :=
  abs_pointCount_sub_le_of_weilHodgeForm_nonneg_real hq hg
    (weilHodgeForm_nonneg_real_of_int hInt)

/-- The point-count expression associated with a finite reciprocal spectrum. -/
def weilHodgeSpectralPointCount {ι : Type*} [Fintype ι]
    (alpha : ι → ℂ) (q : ℝ) (n : ℕ) : ℝ :=
  q ^ n + 1 - (finiteComplexPowerSum alpha n).re

private theorem sqrt_pow_eq (q : ℝ) (hq : 0 ≤ q) :
    ∀ n : ℕ, Real.sqrt (q ^ n) = Real.sqrt q ^ n
  | 0 => by simp
  | n + 1 => by
      rw [pow_succ, Real.sqrt_mul (pow_nonneg hq n), sqrt_pow_eq q hq n, pow_succ]

/--
Extension-wise integral Hodge inequalities, reality of Frobenius traces, and reciprocal pairing
force every member of the finite spectrum onto the critical circle.
-/
theorem norm_eq_sqrt_of_weilHodge_lattice_extensions
    {ι : Type*} [Fintype ι] (alpha : ι → ℂ) (sigma : Equiv.Perm ι)
    {q g : ℝ} (hq : 0 < q) (hg : 0 ≤ g)
    (hpair : ∀ i, alpha (sigma i) * alpha i = (q : ℂ))
    (hreal : ∀ n, (finiteComplexPowerSum alpha n).im = 0)
    (hHodge : ∀ n : ℕ, 0 < n →
      ∀ a b : ℤ, 0 ≤ weilHodgeForm (q ^ n) g
        (weilHodgeSpectralPointCount alpha q n) a b) :
    ∀ i, ‖alpha i‖ = Real.sqrt q := by
  let C : ℝ := max (Fintype.card ι : ℝ) (2 * g)
  have hC : 0 ≤ C :=
    (Nat.cast_nonneg (Fintype.card ι)).trans (le_max_left _ _)
  have hbound : ∀ n : ℕ,
      ‖finiteComplexPowerSum alpha n‖ ≤ C * Real.sqrt q ^ n := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp [finiteComplexPowerSum, C]
    · have hnPos : 0 < n := Nat.pos_of_ne_zero hn
      have hPoint :=
        abs_pointCount_sub_le_of_weilHodgeForm_nonneg_int
          (pow_pos hq n) hg (hHodge n hnPos)
      have hRe :
          |(finiteComplexPowerSum alpha n).re| ≤
            2 * g * Real.sqrt (q ^ n) := by
        simpa [weilHodgeSpectralPointCount] using hPoint
      have hNorm :
          ‖finiteComplexPowerSum alpha n‖ =
            |(finiteComplexPowerSum alpha n).re| := by
        have hz :
            finiteComplexPowerSum alpha n =
              ((finiteComplexPowerSum alpha n).re : ℂ) := by
          apply Complex.ext
          · simp
          · simpa using hreal n
        calc
          ‖finiteComplexPowerSum alpha n‖ =
              ‖((finiteComplexPowerSum alpha n).re : ℂ)‖ :=
            congrArg norm hz
          _ = |(finiteComplexPowerSum alpha n).re| := by
            simp only [Complex.norm_real, Real.norm_eq_abs]
      calc
        ‖finiteComplexPowerSum alpha n‖ =
            |(finiteComplexPowerSum alpha n).re| := hNorm
        _ ≤ 2 * g * Real.sqrt (q ^ n) := hRe
        _ = 2 * g * Real.sqrt q ^ n := by rw [sqrt_pow_eq q hq.le n]
        _ ≤ C * Real.sqrt q ^ n :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  exact norm_eq_sqrt_of_powerSum_bound_and_reciprocal
    alpha sigma hq hC hpair hbound

/-- A homogeneous quadratic form used to falsify finite coefficient-box promotion. -/
def finiteHodgeBoxModel (a b : ℝ) : ℝ :=
  (b - 2 * a) ^ 2 - a ^ 2 / 2

/-- Every integer pair in the coefficient box `[-1,1]^2` passes the finite test. -/
theorem finiteHodgeBoxModel_nonneg_of_abs_le_one
    (a b : ℤ) (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    0 ≤ finiteHodgeBoxModel a b := by
  rcases abs_le.mp ha with ⟨haLower, haUpper⟩
  rcases abs_le.mp hb with ⟨hbLower, hbUpper⟩
  interval_cases a <;> interval_cases b <;> norm_num [finiteHodgeBoxModel]

/-- The same form is negative at the first unchecked point `(1,2)`. -/
theorem finiteHodgeBoxModel_one_two_neg :
    finiteHodgeBoxModel 1 2 < 0 := by
  norm_num [finiteHodgeBoxModel]

/-- Aggregate certificate for the integer-lattice bridge and its finite-box negative control. -/
structure WeilHodgeLatticeCertificate : Prop where
  pointBound :
    ∀ {q g N : ℝ}, 0 < q → 0 ≤ g →
      (∀ a b : ℤ, 0 ≤ weilHodgeForm q g N a b) →
      |N - (q + 1)| ≤ 2 * g * Real.sqrt q
  finiteBox :
    ∀ a b : ℤ, |a| ≤ 1 → |b| ≤ 1 →
      0 ≤ finiteHodgeBoxModel a b
  outsideBox :
    finiteHodgeBoxModel 1 2 < 0

/-- The fixed Hodge-lattice numerical endpoint. -/
theorem weilHodgeLattice_endpoint :
    WeilHodgeLatticeCertificate where
  pointBound := fun hq hg hInt =>
    abs_pointCount_sub_le_of_weilHodgeForm_nonneg_int hq hg hInt
  finiteBox := finiteHodgeBoxModel_nonneg_of_abs_le_one
  outsideBox := finiteHodgeBoxModel_one_two_neg

end

end LeanLab.Riemann
