import Mathlib.NumberTheory.Real.Irrational

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Conrey character-sum rationality audit

This module isolates the finite algebra used in Proposition 1 of Conrey's 2024 character-sum
route to RH. It proves the weighted-prefix identity and separates the unexcluded zero-moment
branch from the branch that determines a rational zero. It does not assert that an actual
quadratic-character prefix has zero moment.
-/

open scoped BigOperators

namespace LeanLab.Riemann

noncomputable section

/-- The unweighted integer mass of a source prefix `1 <= n <= m`. -/
def conreyPrefixMass (chi : ℕ → ℤ) (m : ℕ) : ℤ :=
  ∑ n ∈ Finset.Icc 1 m, chi n

/-- The first integer moment of a source prefix `1 <= n <= m`. -/
def conreyPrefixMoment (chi : ℕ → ℤ) (m : ℕ) : ℤ :=
  ∑ n ∈ Finset.Icc 1 m, (n : ℤ) * chi n

/-- The linearly weighted source prefix at a real scale `y`. -/
def conreyWeightedPrefix (chi : ℕ → ℤ) (m : ℕ) (y : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 m, (chi n : ℝ) * (1 - (n : ℝ) / y)

/-- Exact finite identity `S(y) = A_m - B_m/y` on a fixed prefix. -/
theorem conreyWeightedPrefix_eq_mass_sub_moment_div
    (chi : ℕ → ℤ) (m : ℕ) (y : ℝ) :
    conreyWeightedPrefix chi m y =
      (conreyPrefixMass chi m : ℝ) - (conreyPrefixMoment chi m : ℝ) / y := by
  rw [conreyWeightedPrefix, conreyPrefixMass, conreyPrefixMoment]
  push_cast
  calc
    (∑ n ∈ Finset.Icc 1 m, (chi n : ℝ) * (1 - (n : ℝ) / y)) =
        (∑ n ∈ Finset.Icc 1 m, (chi n : ℝ)) -
          ∑ n ∈ Finset.Icc 1 m, ((n : ℝ) * (chi n : ℝ)) / y := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ = (∑ n ∈ Finset.Icc 1 m, (chi n : ℝ)) -
        (∑ n ∈ Finset.Icc 1 m, (n : ℝ) * (chi n : ℝ)) / y := by
      simp_rw [div_eq_mul_inv]
      rw [Finset.sum_mul]

/-- A zero first moment makes the weighted prefix constant in the scale parameter. -/
theorem conreyWeightedPrefix_eq_mass_of_moment_eq_zero
    {chi : ℕ → ℤ} {m : ℕ} (hMoment : conreyPrefixMoment chi m = 0) (y : ℝ) :
    conreyWeightedPrefix chi m y = (conreyPrefixMass chi m : ℝ) := by
  rw [conreyWeightedPrefix_eq_mass_sub_moment_div, hMoment]
  norm_num

/-- The corrected algebraic alternative behind the source rationality inference. -/
theorem conreyAffineFraction_eq_dichotomy
    {q x A B H : ℝ} (hq : q ≠ 0) (hx : x ≠ 0)
    (hEq : A - B / (q * x) = H) :
    (B = 0 ∧ A = H) ∨
      (B ≠ 0 ∧ A ≠ H ∧ x = B / (q * (A - H))) := by
  by_cases hB : B = 0
  · left
    refine ⟨hB, ?_⟩
    simpa [hB] using hEq
  · right
    have hqx : q * x ≠ 0 := mul_ne_zero hq hx
    have hAH : A ≠ H := by
      intro hAH
      have hZero : B / (q * x) = 0 := by
        rw [hAH] at hEq
        linarith
      rcases (div_eq_zero_iff).mp hZero with hBZero | hqxZero
      · exact hB hBZero
      · exact hqx hqxZero
    have hFraction : B / (q * x) = A - H := by
      linarith
    have hProduct : B = (A - H) * (q * x) := (div_eq_iff hqx).mp hFraction
    refine ⟨hB, hAH, (eq_div_iff (mul_ne_zero hq (sub_ne_zero.mpr hAH))).2 ?_⟩
    calc
      x * (q * (A - H)) = (A - H) * (q * x) := by ring
      _ = B := hProduct.symm

/-- With rational coefficients, the nonflat branch gives a rational value of `x`. -/
theorem conreyAffineFraction_eq_rat_or_flat
    {q A B H : ℚ} {x : ℝ} (hq : q ≠ 0) (hx : x ≠ 0)
    (hEq : (A : ℝ) - (B : ℝ) / ((q : ℝ) * x) = (H : ℝ)) :
    (B = 0 ∧ A = H) ∨ ∃ r : ℚ, x = (r : ℝ) := by
  have hqReal : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  rcases conreyAffineFraction_eq_dichotomy hqReal hx hEq with hFlat | hRational
  · left
    exact ⟨by exact_mod_cast hFlat.1, by exact_mod_cast hFlat.2⟩
  · right
    refine ⟨B / (q * (A - H)), ?_⟩
    rw [hRational.2.2]
    push_cast
    rfl

/-- Rational parameters and an irrational `x` satisfy the omitted flat branch. -/
theorem conreyAffineRationalityInference_counterexample :
    ∃ (q A B H : ℚ) (x : ℝ),
      q ≠ 0 ∧ x ≠ 0 ∧
        (A : ℝ) - (B : ℝ) / ((q : ℝ) * x) = (H : ℝ) ∧ Irrational x := by
  refine ⟨1, 0, 0, 0, Real.sqrt 2, by norm_num, ?_, by norm_num,
    irrational_sqrt_two⟩
  positivity

end

end LeanLab.Riemann
