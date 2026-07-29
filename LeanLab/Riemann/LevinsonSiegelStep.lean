import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Levinson--Siegel step geometry

This module audits the source symmetry class used for derivative combinations in Levinson's
method. The explicit normalized logistic family is not the hypergeometric optimizer in the
source. It shows that the source endpoint and reflection conditions support smooth pointwise
approximations to Siegel's step, while the mean value theorem records the unavoidable growth
of transition steepness.
-/

open Filter Set
open scoped Topology

namespace LeanLab.Riemann

noncomputable section

/-- A decreasing logistic profile centered at `1 / 2`. -/
def levinsonLogistic (R y : ℝ) : ℝ :=
  (1 + Real.exp (R * (2 * y - 1)))⁻¹

/-- Endpoint normalization of the logistic profile to the Levinson--Conrey symmetry class. -/
def levinsonSiegelProfile (R y : ℝ) : ℝ :=
  (levinsonLogistic R y - levinsonLogistic R 1) /
    (levinsonLogistic R 0 - levinsonLogistic R 1)

/-- The discontinuous step associated with Siegel's auxiliary function. -/
def levinsonSiegelStep (y : ℝ) : ℝ :=
  if y < 1 / 2 then 1 else if y = 1 / 2 then 1 / 2 else 0

theorem levinsonLogistic_reflection (R y : ℝ) :
    levinsonLogistic R (1 - y) = 1 - levinsonLogistic R y := by
  unfold levinsonLogistic
  have hexp : Real.exp (R * (2 * y - 1)) ≠ 0 := (Real.exp_pos _).ne'
  rw [show R * (2 * (1 - y) - 1) = -(R * (2 * y - 1)) by ring, Real.exp_neg]
  field_simp [hexp]
  ring

theorem levinsonLogistic_zero_eq_one_sub_one (R : ℝ) :
    levinsonLogistic R 0 = 1 - levinsonLogistic R 1 := by
  simpa using levinsonLogistic_reflection R 1

theorem levinsonLogistic_denominator_eq (R : ℝ) :
    levinsonLogistic R 0 - levinsonLogistic R 1 =
      (Real.exp R - 1) / (Real.exp R + 1) := by
  unfold levinsonLogistic
  have hexp : Real.exp R ≠ 0 := (Real.exp_pos R).ne'
  rw [show R * (2 * (0 : ℝ) - 1) = -R by ring,
    show R * (2 * (1 : ℝ) - 1) = R by ring, Real.exp_neg]
  field_simp [hexp]
  ring

theorem levinsonLogistic_denominator_pos {R : ℝ} (hR : 0 < R) :
    0 < levinsonLogistic R 0 - levinsonLogistic R 1 := by
  rw [levinsonLogistic_denominator_eq]
  exact div_pos (sub_pos.mpr (Real.one_lt_exp_iff.mpr hR))
    (add_pos (Real.exp_pos R) zero_lt_one)

theorem levinsonLogistic_denominator_lt_one (R : ℝ) :
    levinsonLogistic R 0 - levinsonLogistic R 1 < 1 := by
  rw [levinsonLogistic_denominator_eq]
  have hden : 0 < Real.exp R + 1 := add_pos (Real.exp_pos R) zero_lt_one
  rw [div_lt_one hden]
  linarith

theorem levinsonSiegelProfile_zero {R : ℝ} (hR : 0 < R) :
    levinsonSiegelProfile R 0 = 1 := by
  unfold levinsonSiegelProfile
  field_simp [(levinsonLogistic_denominator_pos hR).ne']

theorem levinsonSiegelProfile_one (R : ℝ) :
    levinsonSiegelProfile R 1 = 0 := by
  simp [levinsonSiegelProfile]

theorem levinsonSiegelProfile_reflection {R : ℝ} (hR : 0 < R) (y : ℝ) :
    levinsonSiegelProfile R y + levinsonSiegelProfile R (1 - y) = 1 := by
  let d := levinsonLogistic R 0 - levinsonLogistic R 1
  have hden : d ≠ 0 := by
    exact (levinsonLogistic_denominator_pos hR).ne'
  have hnum :
      (levinsonLogistic R y - levinsonLogistic R 1) +
          (levinsonLogistic R (1 - y) - levinsonLogistic R 1) = d := by
    dsimp only [d]
    rw [levinsonLogistic_reflection, levinsonLogistic_zero_eq_one_sub_one]
    ring
  calc
    levinsonSiegelProfile R y + levinsonSiegelProfile R (1 - y) =
        ((levinsonLogistic R y - levinsonLogistic R 1) +
          (levinsonLogistic R (1 - y) - levinsonLogistic R 1)) / d := by
            unfold levinsonSiegelProfile
            dsimp only [d]
            ring
    _ = d / d := by rw [hnum]
    _ = 1 := div_self hden

theorem levinsonSiegelProfile_half {R : ℝ} (hR : 0 < R) :
    levinsonSiegelProfile R (1 / 2) = 1 / 2 := by
  have href := levinsonSiegelProfile_reflection hR (1 / 2)
  norm_num at href ⊢
  linarith

theorem hasDerivAt_levinsonLogistic (R y : ℝ) :
    HasDerivAt (levinsonLogistic R)
      (-(2 * R * Real.exp (R * (2 * y - 1))) /
        (1 + Real.exp (R * (2 * y - 1))) ^ 2) y := by
  have hinner : HasDerivAt (fun x : ℝ => R * (2 * x - 1)) (2 * R) y := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id y).const_mul 2).sub_const 1).const_mul R
  have hexp :
      HasDerivAt (fun x : ℝ => Real.exp (R * (2 * x - 1)))
        (Real.exp (R * (2 * y - 1)) * (2 * R)) y := by
    simpa only [Function.comp_def] using
      (Real.hasDerivAt_exp (R * (2 * y - 1))).comp y hinner
  have hden :
      HasDerivAt (fun x : ℝ => 1 + Real.exp (R * (2 * x - 1)))
        (Real.exp (R * (2 * y - 1)) * (2 * R)) y :=
    hexp.const_add 1
  have hne : 1 + Real.exp (R * (2 * y - 1)) ≠ 0 := by positivity
  unfold levinsonLogistic
  convert! hden.inv hne using 1
  ring

theorem hasDerivAt_levinsonSiegelProfile (R y : ℝ) :
    HasDerivAt (levinsonSiegelProfile R)
      ((-(2 * R * Real.exp (R * (2 * y - 1))) /
          (1 + Real.exp (R * (2 * y - 1))) ^ 2) /
        (levinsonLogistic R 0 - levinsonLogistic R 1)) y := by
  unfold levinsonSiegelProfile
  exact
    ((hasDerivAt_levinsonLogistic R y).sub_const (levinsonLogistic R 1)).div_const
      (levinsonLogistic R 0 - levinsonLogistic R 1)

theorem deriv_levinsonSiegelProfile_half (R : ℝ) :
    deriv (levinsonSiegelProfile R) (1 / 2) =
      -(R / 2) / (levinsonLogistic R 0 - levinsonLogistic R 1) := by
  have hderiv := (hasDerivAt_levinsonSiegelProfile R (1 / 2)).deriv
  norm_num at hderiv
  convert hderiv using 1
  ring

theorem half_le_abs_deriv_levinsonSiegelProfile_half {R : ℝ} (hR : 0 < R) :
    R / 2 ≤ |deriv (levinsonSiegelProfile R) (1 / 2)| := by
  let d := levinsonLogistic R 0 - levinsonLogistic R 1
  have hdpos : 0 < d := levinsonLogistic_denominator_pos hR
  have hdle : d ≤ 1 := (levinsonLogistic_denominator_lt_one R).le
  have hderiv : deriv (levinsonSiegelProfile R) (1 / 2) = -(R / 2) / d := by
    simpa only [d] using deriv_levinsonSiegelProfile_half R
  rw [hderiv, abs_div, abs_neg, abs_of_pos (by positivity : 0 < R / 2),
    abs_of_pos hdpos]
  exact (le_div_iff₀ hdpos).2 (by nlinarith)

theorem tendsto_levinsonLogistic_one_of_lt_half {y : ℝ} (hy : y < 1 / 2) :
    Tendsto (fun R : ℝ => levinsonLogistic R y) atTop (𝓝 1) := by
  have hcoef : 2 * y - 1 < 0 := by linarith
  have harg : Tendsto (fun R : ℝ => R * (2 * y - 1)) atTop atBot :=
    by simpa [mul_comm] using tendsto_id.const_mul_atTop_of_neg hcoef
  have hexp : Tendsto (fun R : ℝ => Real.exp (R * (2 * y - 1))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp harg
  have hden : Tendsto (fun R : ℝ => 1 + Real.exp (R * (2 * y - 1))) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hexp
  simpa only [levinsonLogistic, one_div, inv_one] using
    hden.inv₀ (by norm_num : (1 : ℝ) ≠ 0)

theorem tendsto_levinsonLogistic_zero_of_half_lt {y : ℝ} (hy : 1 / 2 < y) :
    Tendsto (fun R : ℝ => levinsonLogistic R y) atTop (𝓝 0) := by
  have href :
      (fun R : ℝ => levinsonLogistic R y) =
        fun R : ℝ => 1 - levinsonLogistic R (1 - y) := by
    funext R
    rw [levinsonLogistic_reflection]
    ring
  rw [href]
  have hy' : 1 - y < 1 / 2 := by linarith
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  simpa using hone.sub (tendsto_levinsonLogistic_one_of_lt_half hy')

theorem tendsto_levinsonSiegelProfile_one_of_lt_half {y : ℝ} (hy : y < 1 / 2) :
    Tendsto (fun R : ℝ => levinsonSiegelProfile R y) atTop (𝓝 1) := by
  have hnum :=
    (tendsto_levinsonLogistic_one_of_lt_half hy).sub
      (tendsto_levinsonLogistic_zero_of_half_lt (by norm_num : (1 / 2 : ℝ) < 1))
  have hden :=
    (tendsto_levinsonLogistic_one_of_lt_half (by norm_num : (0 : ℝ) < 1 / 2)).sub
      (tendsto_levinsonLogistic_zero_of_half_lt (by norm_num : (1 / 2 : ℝ) < 1))
  unfold levinsonSiegelProfile
  change Tendsto
    ((fun R : ℝ => levinsonLogistic R y - levinsonLogistic R 1) /
      (fun R : ℝ => levinsonLogistic R 0 - levinsonLogistic R 1))
    atTop (𝓝 1)
  simpa using hnum.div hden (by norm_num)

theorem tendsto_levinsonSiegelProfile_zero_of_half_lt {y : ℝ} (hy : 1 / 2 < y) :
    Tendsto (fun R : ℝ => levinsonSiegelProfile R y) atTop (𝓝 0) := by
  have hnum :=
    (tendsto_levinsonLogistic_zero_of_half_lt hy).sub
      (tendsto_levinsonLogistic_zero_of_half_lt (by norm_num : (1 / 2 : ℝ) < 1))
  have hden :=
    (tendsto_levinsonLogistic_one_of_lt_half (by norm_num : (0 : ℝ) < 1 / 2)).sub
      (tendsto_levinsonLogistic_zero_of_half_lt (by norm_num : (1 / 2 : ℝ) < 1))
  unfold levinsonSiegelProfile
  change Tendsto
    ((fun R : ℝ => levinsonLogistic R y - levinsonLogistic R 1) /
      (fun R : ℝ => levinsonLogistic R 0 - levinsonLogistic R 1))
    atTop (𝓝 0)
  simpa using hnum.div hden (by norm_num)

theorem tendsto_levinsonSiegelProfile_step (y : ℝ) :
    Tendsto (fun R : ℝ => levinsonSiegelProfile R y) atTop
      (𝓝 (levinsonSiegelStep y)) := by
  rcases lt_trichotomy y (1 / 2) with hy | hy | hy
  · rw [levinsonSiegelStep, if_pos hy]
    exact tendsto_levinsonSiegelProfile_one_of_lt_half hy
  · subst y
    have hevent :
        ∀ᶠ R : ℝ in atTop, levinsonSiegelProfile R (1 / 2) = 1 / 2 := by
      filter_upwards [eventually_gt_atTop 0] with R hR
      exact levinsonSiegelProfile_half hR
    have hconst : Tendsto (fun _ : ℝ => (1 / 2 : ℝ)) atTop (𝓝 (1 / 2)) :=
      tendsto_const_nhds
    have hevent' :
        (fun _ : ℝ => (1 / 2 : ℝ)) =ᶠ[atTop]
          (fun R : ℝ => levinsonSiegelProfile R (1 / 2)) :=
      Filter.EventuallyEq.symm hevent
    rw [show levinsonSiegelStep (1 / 2) = 1 / 2 by simp [levinsonSiegelStep]]
    exact hconst.congr' hevent'
  · rw [levinsonSiegelStep, if_neg (not_lt.mpr hy.le),
      if_neg (ne_of_gt hy)]
    exact tendsto_levinsonSiegelProfile_zero_of_half_lt hy

/-- Every real transition from a higher left endpoint to a lower right endpoint has a point
where the derivative magnitude is at least the secant magnitude. -/
theorem exists_abs_deriv_ge_transition
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn f (Icc a b))
    (hdiff : DifferentiableOn ℝ f (Ioo a b))
    (hfall : f b < f a) :
    ∃ c ∈ Ioo a b, (f a - f b) / (b - a) ≤ |deriv f c| := by
  obtain ⟨c, hc, hderiv⟩ := exists_deriv_eq_slope f hab hcont hdiff
  refine ⟨c, hc, ?_⟩
  rw [hderiv]
  have hden : 0 < b - a := sub_pos.mpr hab
  have hnum : 0 < f a - f b := sub_pos.mpr hfall
  rw [show (f b - f a) / (b - a) = -((f a - f b) / (b - a)) by ring,
    abs_neg, abs_of_pos (div_pos hnum hden)]

/-- Quantitative no-uniform-slope corollary for an epsilon-approximation to a step across a
window of radius `delta`. -/
theorem exists_abs_deriv_gt_of_step_transition
    {f : ℝ → ℝ} {M delta epsilon : ℝ}
    (hdelta : 0 < delta)
    (hcont : ContinuousOn f (Icc (1 / 2 - delta) (1 / 2 + delta)))
    (hdiff : DifferentiableOn ℝ f (Ioo (1 / 2 - delta) (1 / 2 + delta)))
    (hleft : 1 - epsilon ≤ f (1 / 2 - delta))
    (hright : f (1 / 2 + delta) ≤ epsilon)
    (hsharp : M < (1 - 2 * epsilon) / (2 * delta)) :
    ∃ c ∈ Ioo (1 / 2 - delta) (1 / 2 + delta), M < |deriv f c| := by
  have hab : 1 / 2 - delta < 1 / 2 + delta := by linarith
  by_cases hM : M < 0
  · refine ⟨1 / 2, ⟨by linarith, by linarith⟩, ?_⟩
    exact hM.trans_le (abs_nonneg _)
  have hM0 : 0 ≤ M := le_of_not_gt hM
  have hgap :
      (1 - 2 * epsilon) ≤
        f (1 / 2 - delta) - f (1 / 2 + delta) := by
    linarith
  have hgapPos : f (1 / 2 + delta) < f (1 / 2 - delta) := by
    have hden : 0 < 2 * delta := by positivity
    have hquotPos : 0 < (1 - 2 * epsilon) / (2 * delta) :=
      hM0.trans_lt hsharp
    have hsourcePos : 0 < 1 - 2 * epsilon := by
      exact (div_pos_iff_of_pos_right hden).mp hquotPos
    linarith
  obtain ⟨c, hc, hcderiv⟩ :=
    exists_abs_deriv_ge_transition hab hcont hdiff hgapPos
  refine ⟨c, hc, ?_⟩
  have hden : 0 < 2 * delta := by positivity
  have hsecant :
      (1 - 2 * epsilon) / (2 * delta) ≤
        (f (1 / 2 - delta) - f (1 / 2 + delta)) /
          ((1 / 2 + delta) - (1 / 2 - delta)) := by
    rw [show (1 / 2 + delta) - (1 / 2 - delta) = 2 * delta by ring]
    exact (div_le_div_iff_of_pos_right hden).2 hgap
  exact hsharp.trans_le (hsecant.trans hcderiv)

/-- Aggregate certificate for source admissibility, the Siegel-step limit, and the steepness
obstruction. -/
theorem levinsonSiegelStep_endpoint :
    (∀ R : ℝ, 0 < R →
      levinsonSiegelProfile R 0 = 1 ∧
      levinsonSiegelProfile R 1 = 0 ∧
      (∀ y : ℝ,
        levinsonSiegelProfile R y + levinsonSiegelProfile R (1 - y) = 1) ∧
      R / 2 ≤ |deriv (levinsonSiegelProfile R) (1 / 2)|) ∧
    (∀ y : ℝ, Tendsto (fun R : ℝ => levinsonSiegelProfile R y) atTop
      (𝓝 (levinsonSiegelStep y))) ∧
    (∀ (f : ℝ → ℝ) (a b : ℝ), a < b →
      ContinuousOn f (Icc a b) →
      DifferentiableOn ℝ f (Ioo a b) →
      f b < f a →
      ∃ c ∈ Ioo a b, (f a - f b) / (b - a) ≤ |deriv f c|) := by
  refine ⟨?_, tendsto_levinsonSiegelProfile_step, ?_⟩
  · intro R hR
    exact ⟨levinsonSiegelProfile_zero hR, levinsonSiegelProfile_one R,
      levinsonSiegelProfile_reflection hR,
      half_le_abs_deriv_levinsonSiegelProfile_half hR⟩
  · intro f a b hab hcont hdiff hfall
    exact exists_abs_deriv_ge_transition hab hcont hdiff hfall

end

end LeanLab.Riemann
