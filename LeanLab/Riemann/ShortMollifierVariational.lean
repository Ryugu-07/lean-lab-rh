import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Short-mollifier variational sufficiency

This module reconstructs the continuum variational core of equations (58)--(63) in Conrey,
Farmer, Kwan, Lin, and Turnage-Butterbaugh. It does not import a mollified mean-value theorem or
assert a new critical-line zero proportion.
-/

open MeasureTheory Set
open scoped Interval

namespace LeanLab.Riemann

noncomputable section

/-- The general source functional from equation (58), before division by `c1`. -/
def shortMollifierSourceEnergy (R beta c0 c1 : ℝ) (S dS : ℝ → ℝ) : ℝ :=
  ∫ t in 0..R,
    Real.exp t * (c0 * S t ^ 2 + c1 * dS t ^ 2) +
      Real.exp (-t) * (c0 * (beta - S t) ^ 2 + c1 * dS t ^ 2)

/-- Equation (58), normalized by `c1` and the source substitution `c = -c0/c1`. -/
def shortMollifierNormalizedEnergy (R beta c : ℝ) (S dS : ℝ → ℝ) : ℝ :=
  ∫ t in 0..R,
    2 * Real.cosh t * (dS t ^ 2 - c * S t ^ 2) +
      2 * c * beta * Real.exp (-t) * S t -
        c * beta ^ 2 * Real.exp (-t)

private theorem shortMollifierWeightedSquare_expansion (t x dx : ℝ) :
    Real.cosh t * (dx + Real.tanh t / 2 * x) ^ 2 =
      Real.cosh t * dx ^ 2 + Real.sinh t * x * dx +
        (1 / 4 : ℝ) * (Real.cosh t * x ^ 2) -
          (1 / 4 : ℝ) * (x ^ 2 / Real.cosh t) := by
  rw [Real.tanh_eq_sinh_div_cosh]
  have hcosh : Real.cosh t ≠ 0 := (Real.cosh_pos t).ne'
  field_simp [hcosh]
  nlinarith [Real.cosh_sq_sub_sinh_sq t]

/-- The cross term in the weighted completion of squares is fixed by the zero endpoint values. -/
theorem shortMollifierSinh_mul_mul_deriv_integral {R : ℝ} {h dh : ℝ → ℝ}
    (hh : ∀ t ∈ Set.uIcc 0 R, HasDerivAt h (dh t) t)
    (hdh : ContinuousOn dh (Set.uIcc 0 R))
    (h0 : h 0 = 0) (hR : h R = 0) :
    (∫ t in 0..R, Real.sinh t * h t * dh t) =
      -(1 / 2 : ℝ) * ∫ t in 0..R, Real.cosh t * h t ^ 2 := by
  have hhc : ContinuousOn h (Set.uIcc 0 R) :=
    fun t ht => (hh t ht).continuousAt.continuousWithinAt
  have hsq : ∀ t ∈ Set.uIcc 0 R,
      HasDerivAt (fun x => h x ^ 2) (2 * h t * dh t) t := by
    intro t ht
    simpa using (hh t ht).fun_pow 2
  have hcoshInt : IntervalIntegrable Real.cosh volume 0 R :=
    Real.continuous_cosh.intervalIntegrable 0 R
  have htwoInt : IntervalIntegrable (fun t => 2 * h t * dh t) volume 0 R :=
    ((continuousOn_const.mul hhc).mul hdh).intervalIntegrable
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun t _ => Real.hasDerivAt_sinh t) hsq hcoshInt htwoInt
  rw [h0, hR] at hibp
  simp only [pow_two, mul_zero, sub_zero] at hibp
  have hscale :
      (∫ t in 0..R, Real.sinh t * (2 * h t * dh t)) =
        2 * ∫ t in 0..R, Real.sinh t * h t * dh t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  rw [hscale] at hibp
  simp only [pow_two]
  linarith

/-- Exact weighted completion of squares behind the source threshold `c < 1/4`. -/
theorem shortMollifierWeightedHardyIdentity {R : ℝ} {h dh : ℝ → ℝ}
    (hh : ∀ t ∈ Set.uIcc 0 R, HasDerivAt h (dh t) t)
    (hdh : ContinuousOn dh (Set.uIcc 0 R))
    (h0 : h 0 = 0) (hR : h R = 0) :
    (∫ t in 0..R, Real.cosh t * (dh t + Real.tanh t / 2 * h t) ^ 2) =
      (∫ t in 0..R, Real.cosh t * dh t ^ 2) -
        (1 / 4 : ℝ) * (∫ t in 0..R, Real.cosh t * h t ^ 2) -
          (1 / 4 : ℝ) * (∫ t in 0..R, h t ^ 2 / Real.cosh t) := by
  have hcross := shortMollifierSinh_mul_mul_deriv_integral hh hdh h0 hR
  have hhc : ContinuousOn h (Set.uIcc 0 R) :=
    fun t ht => (hh t ht).continuousAt.continuousWithinAt
  have hA : IntervalIntegrable (fun t => Real.cosh t * dh t ^ 2) volume 0 R :=
    (Real.continuous_cosh.continuousOn.mul (hdh.pow 2)).intervalIntegrable
  have hB : IntervalIntegrable (fun t => Real.sinh t * h t * dh t) volume 0 R :=
    ((Real.continuous_sinh.continuousOn.mul hhc).mul hdh).intervalIntegrable
  have hC : IntervalIntegrable
      (fun t => (1 / 4 : ℝ) * (Real.cosh t * h t ^ 2)) volume 0 R :=
    (continuousOn_const.mul (Real.continuous_cosh.continuousOn.mul (hhc.pow 2))).intervalIntegrable
  have hD : IntervalIntegrable
      (fun t => (1 / 4 : ℝ) * (h t ^ 2 / Real.cosh t)) volume 0 R :=
    (continuousOn_const.mul ((hhc.pow 2).div Real.continuous_cosh.continuousOn
      (fun t _ => (Real.cosh_pos t).ne'))).intervalIntegrable
  simp_rw [shortMollifierWeightedSquare_expansion]
  rw [intervalIntegral.integral_sub ((hA.add hB).add hC) hD,
    intervalIntegral.integral_add (hA.add hB) hC,
    intervalIntegral.integral_add hA hB, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, hcross]
  ring

/-- The endpoint Hardy inequality with the exact source threshold `1/4`. -/
theorem shortMollifierWeightedHardy_quarter_le {R : ℝ} (hRnonneg : 0 ≤ R)
    {h dh : ℝ → ℝ}
    (hh : ∀ t ∈ Set.uIcc 0 R, HasDerivAt h (dh t) t)
    (hdh : ContinuousOn dh (Set.uIcc 0 R))
    (h0 : h 0 = 0) (hR : h R = 0) :
    (1 / 4 : ℝ) * (∫ t in 0..R, Real.cosh t * h t ^ 2) ≤
      ∫ t in 0..R, Real.cosh t * dh t ^ 2 := by
  have hid := shortMollifierWeightedHardyIdentity hh hdh h0 hR
  have hsquare : 0 ≤
      ∫ t in 0..R, Real.cosh t * (dh t + Real.tanh t / 2 * h t) ^ 2 := by
    apply intervalIntegral.integral_nonneg hRnonneg
    intro t _
    positivity
  have hextra : 0 ≤ ∫ t in 0..R, h t ^ 2 / Real.cosh t := by
    apply intervalIntegral.integral_nonneg hRnonneg
    intro t _
    positivity
  linarith

private theorem shortMollifierSourceIntegrand_eq_mul_normalized
    (beta c c1 t x dx : ℝ) :
    Real.exp t * ((-c * c1) * x ^ 2 + c1 * dx ^ 2) +
        Real.exp (-t) * ((-c * c1) * (beta - x) ^ 2 + c1 * dx ^ 2) =
      c1 * (2 * Real.cosh t * (dx ^ 2 - c * x ^ 2) +
        2 * c * beta * Real.exp (-t) * x - c * beta ^ 2 * Real.exp (-t)) := by
  rw [Real.cosh_eq]
  ring

/-- Exact alignment of source equation (58) with its normalization by `c1`. -/
theorem shortMollifierSourceEnergy_eq_mul_normalized
    (R beta c c1 : ℝ) (S dS : ℝ → ℝ) :
    shortMollifierSourceEnergy R beta (-c * c1) c1 S dS =
      c1 * shortMollifierNormalizedEnergy R beta c S dS := by
  rw [shortMollifierSourceEnergy, shortMollifierNormalizedEnergy,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  exact shortMollifierSourceIntegrand_eq_mul_normalized beta c c1 t (S t) (dS t)

/-- Division form of the exact source normalization. -/
theorem shortMollifierNormalizedEnergy_eq_source
    (R beta c c1 : ℝ) (S dS : ℝ → ℝ) (hc1 : c1 ≠ 0) :
    shortMollifierNormalizedEnergy R beta c S dS =
      shortMollifierSourceEnergy R beta (-c * c1) c1 S dS / c1 := by
  rw [shortMollifierSourceEnergy_eq_mul_normalized]
  field_simp

private theorem shortMollifierNormalizedIntegrand_gap
    (beta c t S dS h dh : ℝ) :
    (2 * Real.cosh t * ((dS + dh) ^ 2 - c * (S + h) ^ 2) +
        2 * c * beta * Real.exp (-t) * (S + h) -
          c * beta ^ 2 * Real.exp (-t)) -
      (2 * Real.cosh t * (dS ^ 2 - c * S ^ 2) +
        2 * c * beta * Real.exp (-t) * S -
          c * beta ^ 2 * Real.exp (-t)) =
    4 * ((-c * Real.cosh t * S + c * beta * Real.exp (-t) / 2) * h +
      Real.cosh t * dS * dh) +
        2 * Real.cosh t * (dh ^ 2 - c * h ^ 2) := by
  ring

/-- Exact second-variation identity. A source Euler-Lagrange solution has no linear energy term. -/
theorem shortMollifierNormalizedEnergy_gap_of_eulerLagrange
    {R beta c : ℝ} {S dS T dT : ℝ → ℝ}
    (hS : ∀ t ∈ Set.uIcc 0 R, HasDerivAt S (dS t) t)
    (hdS : ContinuousOn dS (Set.uIcc 0 R))
    (hT : ∀ t ∈ Set.uIcc 0 R, HasDerivAt T (dT t) t)
    (hdT : ContinuousOn dT (Set.uIcc 0 R))
    (h0 : T 0 = S 0) (hR : T R = S R)
    (hEL : ∀ t ∈ Set.uIcc 0 R,
      HasDerivAt (fun x => Real.cosh x * dS x)
        (-c * Real.cosh t * S t + c * beta * Real.exp (-t) / 2) t) :
    shortMollifierNormalizedEnergy R beta c T dT -
        shortMollifierNormalizedEnergy R beta c S dS =
      2 * ∫ t in 0..R, Real.cosh t *
        ((dT t - dS t) ^ 2 - c * (T t - S t) ^ 2) := by
  have hSc : ContinuousOn S (Set.uIcc 0 R) :=
    fun t ht => (hS t ht).continuousAt.continuousWithinAt
  have hTc : ContinuousOn T (Set.uIcc 0 R) :=
    fun t ht => (hT t ht).continuousAt.continuousWithinAt
  have hDiff : ∀ t ∈ Set.uIcc 0 R,
      HasDerivAt (fun x => T x - S x) (dT t - dS t) t :=
    fun t ht => (hT t ht).sub (hS t ht)
  have hDiffC : ContinuousOn (fun t => T t - S t) (Set.uIcc 0 R) := hTc.sub hSc
  have hdDiffC : ContinuousOn (fun t => dT t - dS t) (Set.uIcc 0 R) := hdT.sub hdS
  have hELC : ContinuousOn
      (fun t => -c * Real.cosh t * S t + c * beta * Real.exp (-t) / 2)
      (Set.uIcc 0 R) := by
    fun_prop
  have hELInt : IntervalIntegrable
      (fun t => -c * Real.cosh t * S t + c * beta * Real.exp (-t) / 2)
      volume 0 R := hELC.intervalIntegrable
  have hDiffInt : IntervalIntegrable (fun t => dT t - dS t) volume 0 R :=
    hdDiffC.intervalIntegrable
  have hlinear := intervalIntegral.integral_deriv_mul_eq_sub hEL hDiff hELInt hDiffInt
  simp only [h0, hR, sub_self, mul_zero] at hlinear
  have hSIntegrand : IntervalIntegrable
      (fun t => 2 * Real.cosh t * (dS t ^ 2 - c * S t ^ 2) +
        2 * c * beta * Real.exp (-t) * S t - c * beta ^ 2 * Real.exp (-t))
      volume 0 R := by
    apply ContinuousOn.intervalIntegrable
    fun_prop
  have hTIntegrand : IntervalIntegrable
      (fun t => 2 * Real.cosh t * (dT t ^ 2 - c * T t ^ 2) +
        2 * c * beta * Real.exp (-t) * T t - c * beta ^ 2 * Real.exp (-t))
      volume 0 R := by
    apply ContinuousOn.intervalIntegrable
    fun_prop
  have hLinearIntegrand : IntervalIntegrable
      (fun t => (-c * Real.cosh t * S t + c * beta * Real.exp (-t) / 2) *
        (T t - S t) + Real.cosh t * dS t * (dT t - dS t)) volume 0 R := by
    apply ContinuousOn.intervalIntegrable
    fun_prop
  have hQuadraticIntegrand : IntervalIntegrable
      (fun t => Real.cosh t * ((dT t - dS t) ^ 2 - c * (T t - S t) ^ 2))
      volume 0 R := by
    apply ContinuousOn.intervalIntegrable
    fun_prop
  rw [shortMollifierNormalizedEnergy, shortMollifierNormalizedEnergy,
    ← intervalIntegral.integral_sub hTIntegrand hSIntegrand]
  have hgap :
      (fun t =>
        (2 * Real.cosh t * (dT t ^ 2 - c * T t ^ 2) +
            2 * c * beta * Real.exp (-t) * T t - c * beta ^ 2 * Real.exp (-t)) -
          (2 * Real.cosh t * (dS t ^ 2 - c * S t ^ 2) +
            2 * c * beta * Real.exp (-t) * S t - c * beta ^ 2 * Real.exp (-t))) =
        fun t =>
          4 * ((-c * Real.cosh t * S t + c * beta * Real.exp (-t) / 2) *
              (T t - S t) + Real.cosh t * dS t * (dT t - dS t)) +
            2 * (Real.cosh t * ((dT t - dS t) ^ 2 - c * (T t - S t) ^ 2)) := by
    funext t
    convert shortMollifierNormalizedIntegrand_gap beta c t (S t) (dS t)
      (T t - S t) (dT t - dS t) using 1 <;> ring
  rw [hgap, intervalIntegral.integral_add (hLinearIntegrand.const_mul 4)
      (hQuadraticIntegrand.const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hlinear]
  ring

private theorem shortMollifierWeightedValue_integrable {R : ℝ} {h dh : ℝ → ℝ}
    (hh : ∀ t ∈ Set.uIcc 0 R, HasDerivAt h (dh t) t) :
    IntervalIntegrable (fun t => Real.cosh t * h t ^ 2) volume 0 R := by
  have hhc : ContinuousOn h (Set.uIcc 0 R) :=
    fun t ht => (hh t ht).continuousAt.continuousWithinAt
  exact (Real.continuous_cosh.continuousOn.mul (hhc.pow 2)).intervalIntegrable

private theorem shortMollifierWeightedDeriv_integrable {R : ℝ} {dh : ℝ → ℝ}
    (hdh : ContinuousOn dh (Set.uIcc 0 R)) :
    IntervalIntegrable (fun t => Real.cosh t * dh t ^ 2) volume 0 R :=
  (Real.continuous_cosh.continuousOn.mul (hdh.pow 2)).intervalIntegrable

/-- The quadratic variation is nonnegative throughout the source parameter range `c <= 1/4`. -/
theorem shortMollifierWeightedVariation_nonneg {R c : ℝ} (hRnonneg : 0 ≤ R)
    (hc : c ≤ 1 / 4) {h dh : ℝ → ℝ}
    (hh : ∀ t ∈ Set.uIcc 0 R, HasDerivAt h (dh t) t)
    (hdh : ContinuousOn dh (Set.uIcc 0 R))
    (h0 : h 0 = 0) (hR : h R = 0) :
    0 ≤ ∫ t in 0..R, Real.cosh t * (dh t ^ 2 - c * h t ^ 2) := by
  have hhardy := shortMollifierWeightedHardy_quarter_le hRnonneg hh hdh h0 hR
  have hvalueNonneg : 0 ≤ ∫ t in 0..R, Real.cosh t * h t ^ 2 := by
    apply intervalIntegral.integral_nonneg hRnonneg
    intro t _
    positivity
  have hDerivInt := shortMollifierWeightedDeriv_integrable hdh
  have hValueInt := shortMollifierWeightedValue_integrable hh
  have hpoint : (fun t => Real.cosh t * (dh t ^ 2 - c * h t ^ 2)) =
      fun t => Real.cosh t * dh t ^ 2 - c * (Real.cosh t * h t ^ 2) := by
    funext t
    ring
  rw [hpoint, intervalIntegral.integral_sub hDerivInt (hValueInt.const_mul c),
    intervalIntegral.integral_const_mul]
  nlinarith

/-- The quadratic variation is strictly positive when `c < 1/4` and the path is nonzero. -/
theorem shortMollifierWeightedVariation_pos {R c : ℝ} (hRpos : 0 < R)
    (hc : c < 1 / 4) {h dh : ℝ → ℝ}
    (hh : ∀ t ∈ Set.uIcc 0 R, HasDerivAt h (dh t) t)
    (hdh : ContinuousOn dh (Set.uIcc 0 R))
    (h0 : h 0 = 0) (hR : h R = 0)
    (hne : ∃ t ∈ Set.Icc 0 R, h t ≠ 0) :
    0 < ∫ t in 0..R, Real.cosh t * (dh t ^ 2 - c * h t ^ 2) := by
  have hhardy := shortMollifierWeightedHardy_quarter_le hRpos.le hh hdh h0 hR
  have hhc : ContinuousOn h (Set.Icc 0 R) := by
    intro t ht
    exact (hh t (by simpa [Set.uIcc_of_le hRpos.le] using ht)).continuousAt.continuousWithinAt
  have hvalueContinuous : ContinuousOn (fun t => Real.cosh t * h t ^ 2) (Set.Icc 0 R) :=
    Real.continuous_cosh.continuousOn.mul (hhc.pow 2)
  have hvaluePos : 0 < ∫ t in 0..R, Real.cosh t * h t ^ 2 := by
    apply intervalIntegral.integral_pos hRpos hvalueContinuous
    · intro t _
      positivity
    · rcases hne with ⟨t, ht, hne⟩
      exact ⟨t, ht, mul_pos (Real.cosh_pos t) (sq_pos_of_ne_zero hne)⟩
  have hDerivInt := shortMollifierWeightedDeriv_integrable hdh
  have hValueInt := shortMollifierWeightedValue_integrable hh
  have hpoint : (fun t => Real.cosh t * (dh t ^ 2 - c * h t ^ 2)) =
      fun t => Real.cosh t * dh t ^ 2 - c * (Real.cosh t * h t ^ 2) := by
    funext t
    ring
  rw [hpoint, intervalIntegral.integral_sub hDerivInt (hValueInt.const_mul c),
    intervalIntegral.integral_const_mul]
  nlinarith

/-- Every source Euler-Lagrange path is the unique minimizer of the normalized energy. -/
theorem shortMollifierNormalizedEnergy_unique_minimizer
    {R beta c : ℝ} (hRpos : 0 < R) (hc : c < 1 / 4)
    {S dS T dT : ℝ → ℝ}
    (hS : ∀ t ∈ Set.uIcc 0 R, HasDerivAt S (dS t) t)
    (hdS : ContinuousOn dS (Set.uIcc 0 R))
    (hT : ∀ t ∈ Set.uIcc 0 R, HasDerivAt T (dT t) t)
    (hdT : ContinuousOn dT (Set.uIcc 0 R))
    (h0 : T 0 = S 0) (hR : T R = S R)
    (hEL : ∀ t ∈ Set.uIcc 0 R,
      HasDerivAt (fun x => Real.cosh x * dS x)
        (-c * Real.cosh t * S t + c * beta * Real.exp (-t) / 2) t) :
    shortMollifierNormalizedEnergy R beta c S dS ≤
        shortMollifierNormalizedEnergy R beta c T dT ∧
      ((∃ t ∈ Set.Icc 0 R, T t ≠ S t) →
        shortMollifierNormalizedEnergy R beta c S dS <
          shortMollifierNormalizedEnergy R beta c T dT) := by
  have hDiff : ∀ t ∈ Set.uIcc 0 R,
      HasDerivAt (fun x => T x - S x) (dT t - dS t) t :=
    fun t ht => (hT t ht).sub (hS t ht)
  have hdDiff : ContinuousOn (fun t => dT t - dS t) (Set.uIcc 0 R) := hdT.sub hdS
  have hDiff0 : T 0 - S 0 = 0 := sub_eq_zero.mpr h0
  have hDiffR : T R - S R = 0 := sub_eq_zero.mpr hR
  have hgap := shortMollifierNormalizedEnergy_gap_of_eulerLagrange
    hS hdS hT hdT h0 hR hEL
  have hvariationNonneg := shortMollifierWeightedVariation_nonneg hRpos.le hc.le
    hDiff hdDiff hDiff0 hDiffR
  constructor
  · linarith
  · intro hne
    have hneDiff : ∃ t ∈ Set.Icc 0 R, T t - S t ≠ 0 := by
      rcases hne with ⟨t, ht, hne⟩
      exact ⟨t, ht, sub_ne_zero.mpr hne⟩
    have hvariationPos := shortMollifierWeightedVariation_pos hRpos hc
      hDiff hdDiff hDiff0 hDiffR hneDiff
    linarith

/-- The same unique-minimizer certificate for source equation (58), when `c1 > 0`. -/
theorem shortMollifierSourceEnergy_unique_minimizer
    {R beta c c1 : ℝ} (hRpos : 0 < R) (hc : c < 1 / 4) (hc1 : 0 < c1)
    {S dS T dT : ℝ → ℝ}
    (hS : ∀ t ∈ Set.uIcc 0 R, HasDerivAt S (dS t) t)
    (hdS : ContinuousOn dS (Set.uIcc 0 R))
    (hT : ∀ t ∈ Set.uIcc 0 R, HasDerivAt T (dT t) t)
    (hdT : ContinuousOn dT (Set.uIcc 0 R))
    (h0 : T 0 = S 0) (hR : T R = S R)
    (hEL : ∀ t ∈ Set.uIcc 0 R,
      HasDerivAt (fun x => Real.cosh x * dS x)
        (-c * Real.cosh t * S t + c * beta * Real.exp (-t) / 2) t) :
    shortMollifierSourceEnergy R beta (-c * c1) c1 S dS ≤
        shortMollifierSourceEnergy R beta (-c * c1) c1 T dT ∧
      ((∃ t ∈ Set.Icc 0 R, T t ≠ S t) →
        shortMollifierSourceEnergy R beta (-c * c1) c1 S dS <
          shortMollifierSourceEnergy R beta (-c * c1) c1 T dT) := by
  have hnormalized := shortMollifierNormalizedEnergy_unique_minimizer
    hRpos hc hS hdS hT hdT h0 hR hEL
  rw [shortMollifierSourceEnergy_eq_mul_normalized,
    shortMollifierSourceEnergy_eq_mul_normalized]
  constructor
  · exact (mul_le_mul_iff_of_pos_left hc1).mpr hnormalized.1
  · intro hne
    exact (mul_lt_mul_iff_of_pos_left hc1).mpr (hnormalized.2 hne)

end

end LeanLab.Riemann
