import LeanLab.Riemann.SpeiserAdmissibleContour
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Left-half-plane winding in the Levinson--Montgomery contour

This file formalizes the source inference that a closed path contained in the strict left half
plane has zero logarithmic winding. Negating the path places it in the principal-log slit plane,
so its logarithmic derivative has a global primitive. The final theorem applies the endpoint
formula to an actual horizontal path of `zeta'/zeta`.
-/

namespace LeanLab.Riemann

open Complex Function MeasureTheory Set
open scoped Topology

noncomputable section

/-- A differentiable path in the strict left half-plane has the principal-log endpoint formula
for its logarithmic derivative. -/
theorem intervalIntegral_deriv_div_eq_log_sub_of_re_neg
    {g g' : ℝ → ℂ} {a b : ℝ}
    (hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt g (g' x) x)
    (hintegrable :
      IntervalIntegrable (fun x => g' x / g x) (volume : Measure ℝ) a b)
    (hneg : ∀ x ∈ Set.uIcc a b, (g x).re < 0) :
    (∫ x : ℝ in a..b, g' x / g x) =
      Complex.log (-g b) - Complex.log (-g a) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    have hslit : -g x ∈ Complex.slitPlane := by
      left
      simp only [neg_re]
      exact neg_pos.mpr (hneg x hx)
    simpa only [Pi.neg_apply, neg_div_neg_eq] using
      (hderiv x hx).neg.clog_real hslit
  · exact hintegrable

/-- Strict left-half-plane containment forces zero logarithmic winding for a closed path. -/
theorem intervalIntegral_deriv_div_eq_zero_of_re_neg_of_eq
    {g g' : ℝ → ℂ} {a b : ℝ}
    (hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt g (g' x) x)
    (hintegrable :
      IntervalIntegrable (fun x => g' x / g x) (volume : Measure ℝ) a b)
    (hneg : ∀ x ∈ Set.uIcc a b, (g x).re < 0)
    (hclosed : g b = g a) :
    (∫ x : ℝ in a..b, g' x / g x) = 0 := by
  rw [intervalIntegral_deriv_div_eq_log_sub_of_re_neg
    hderiv hintegrable hneg, hclosed, sub_self]

/-- The actual ratio whose change of argument is used in the Levinson--Montgomery proof. -/
def speiserZetaDerivRatio (s : ℂ) : ℂ :=
  deriv riemannZeta s / riemannZeta s

/-- A horizontal source segment on which the actual ratio is everywhere strictly left-pointing. -/
def SpeiserStrictNegativeHorizontal (t : ℝ) : Prop :=
  0 < t ∧
    ∀ sigma : ℝ, sigma ∈ Set.Icc (0 : ℝ) (1 / 2) →
      riemannZeta (sigma + t * I) ≠ 0 ∧
        deriv riemannZeta (sigma + t * I) ≠ 0 ∧
        (speiserZetaDerivRatio (sigma + t * I)).re < 0

theorem SpeiserStrictNegativeHorizontal.toCommonZeroFree
    {t : ℝ} (ht : SpeiserStrictNegativeHorizontal t) :
    SpeiserCommonZeroFreeHorizontal t := by
  refine ⟨ht.1, fun sigma hsigma => ?_⟩
  exact ⟨(ht.2 sigma hsigma).1, (ht.2 sigma hsigma).2.1⟩

private theorem differentiableAt_deriv_riemannZeta_of_ne_one
    {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ (deriv riemannZeta) s :=
  (analyticOnNhd_deriv_riemannZeta s (by simpa using hs)).differentiableAt

/-- The complex derivative of the actual ratio is its logarithmic-derivative difference times
the ratio itself. -/
theorem hasDerivAt_speiserZetaDerivRatio
    {s : ℂ} (hs : s ≠ 1)
    (hzeta : riemannZeta s ≠ 0)
    (hderivZeta : deriv riemannZeta s ≠ 0) :
    HasDerivAt speiserZetaDerivRatio
      ((logDeriv (deriv riemannZeta) s - logDeriv riemannZeta s) *
        speiserZetaDerivRatio s) s := by
  have hnum : DifferentiableAt ℂ (deriv riemannZeta) s :=
    differentiableAt_deriv_riemannZeta_of_ne_one hs
  have hden : DifferentiableAt ℂ riemannZeta s :=
    differentiableAt_riemannZeta hs
  have hratio : DifferentiableAt ℂ speiserZetaDerivRatio s := by
    exact hnum.div hden hzeta
  have hratioNe : speiserZetaDerivRatio s ≠ 0 := by
    exact div_ne_zero hderivZeta hzeta
  have hlog :
      logDeriv speiserZetaDerivRatio s =
        logDeriv (deriv riemannZeta) s - logDeriv riemannZeta s := by
    exact logDeriv_div s hderivZeta hzeta hnum hden
  have hderiv :
      deriv speiserZetaDerivRatio s =
        (logDeriv (deriv riemannZeta) s - logDeriv riemannZeta s) *
          speiserZetaDerivRatio s := by
    rw [← hlog, logDeriv_apply]
    exact (div_mul_cancel₀ _ hratioNe).symm
  simpa only [hderiv] using hratio.hasDerivAt

/-- Real-parameter derivative of the actual ratio along a horizontal source segment. -/
theorem hasDerivAt_speiserZetaDerivRatio_horizontal
    {t sigma : ℝ}
    (ht : 0 < t)
    (hzeta : riemannZeta (sigma + t * I) ≠ 0)
    (hderivZeta : deriv riemannZeta (sigma + t * I) ≠ 0) :
    HasDerivAt
      (fun x : ℝ => speiserZetaDerivRatio (x + t * I))
      ((logDeriv (deriv riemannZeta) (sigma + t * I) -
          logDeriv riemannZeta (sigma + t * I)) *
        speiserZetaDerivRatio (sigma + t * I)) sigma := by
  have hs : (sigma : ℂ) + t * I ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    norm_num at him
    linarith
  have houter :=
    hasDerivAt_speiserZetaDerivRatio hs hzeta hderivZeta
  have hline :
      HasDerivAt (fun x : ℝ => (x : ℂ) + t * I) 1 sigma := by
    simpa using (hasDerivAt_id sigma).ofReal_comp.add_const (t * I)
  change HasDerivAt
    (speiserZetaDerivRatio ∘ fun x : ℝ => (x : ℂ) + t * I) _ sigma
  simpa only [one_smul] using houter.scomp sigma hline

/-- On an actual strict-negative horizontal slice, the difference of the two logarithmic
derivatives is the endpoint variation of one principal logarithm. -/
theorem intervalIntegral_speiserZetaDerivRatio_horizontal
    {t : ℝ} (ht : SpeiserStrictNegativeHorizontal t) :
    (∫ sigma : ℝ in (0 : ℝ)..(1 / 2),
      (logDeriv (deriv riemannZeta) (sigma + t * I) -
        logDeriv riemannZeta (sigma + t * I))) =
      Complex.log (-speiserZetaDerivRatio (1 / 2 + t * I)) -
        Complex.log (-speiserZetaDerivRatio (t * I)) := by
  let g : ℝ → ℂ := fun sigma =>
    speiserZetaDerivRatio (sigma + t * I)
  let g' : ℝ → ℂ := fun sigma =>
    (logDeriv (deriv riemannZeta) (sigma + t * I) -
      logDeriv riemannZeta (sigma + t * I)) * g sigma
  have hderiv : ∀ sigma ∈ Set.uIcc (0 : ℝ) (1 / 2),
      HasDerivAt g (g' sigma) sigma := by
    intro sigma hsigma
    have hsigmaIcc : sigma ∈ Set.Icc (0 : ℝ) (1 / 2) := by
      simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] using hsigma
    have hdata := ht.2 sigma hsigmaIcc
    exact hasDerivAt_speiserZetaDerivRatio_horizontal ht.1 hdata.1 hdata.2.1
  have hneg : ∀ sigma ∈ Set.uIcc (0 : ℝ) (1 / 2), (g sigma).re < 0 := by
    intro sigma hsigma
    have hsigmaIcc : sigma ∈ Set.Icc (0 : ℝ) (1 / 2) := by
      simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] using hsigma
    exact (ht.2 sigma hsigmaIcc).2.2
  have hdiffInt :
      IntervalIntegrable
        (fun sigma : ℝ =>
          logDeriv (deriv riemannZeta) (sigma + t * I) -
            logDeriv riemannZeta (sigma + t * I))
        (volume : Measure ℝ) (0 : ℝ) (1 / 2) :=
    (intervalIntegrable_speiserZetaDerivLogDeriv_horizontal
      ht.toCommonZeroFree).sub
      (intervalIntegrable_speiserZetaLogDeriv_horizontal
        ht.toCommonZeroFree)
  have hpoint : ∀ sigma ∈ Set.uIcc (0 : ℝ) (1 / 2),
      g' sigma / g sigma =
        logDeriv (deriv riemannZeta) (sigma + t * I) -
          logDeriv riemannZeta (sigma + t * I) := by
    intro sigma hsigma
    have hsigmaIcc : sigma ∈ Set.Icc (0 : ℝ) (1 / 2) := by
      simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] using hsigma
    have hratioNe : g sigma ≠ 0 := by
      dsimp only [g, speiserZetaDerivRatio]
      exact div_ne_zero (ht.2 sigma hsigmaIcc).2.1 (ht.2 sigma hsigmaIcc).1
    dsimp only [g']
    exact mul_div_cancel_right₀ _ hratioNe
  have hquotInt :
      IntervalIntegrable (fun sigma => g' sigma / g sigma)
        (volume : Measure ℝ) (0 : ℝ) (1 / 2) :=
    hdiffInt.congr fun sigma hsigma =>
      (hpoint sigma (Set.uIoc_subset_uIcc hsigma)).symm
  have hformula :=
    intervalIntegral_deriv_div_eq_log_sub_of_re_neg
      hderiv hquotInt hneg
  calc
    (∫ sigma : ℝ in (0 : ℝ)..(1 / 2),
      (logDeriv (deriv riemannZeta) (sigma + t * I) -
        logDeriv riemannZeta (sigma + t * I))) =
        ∫ sigma : ℝ in (0 : ℝ)..(1 / 2), g' sigma / g sigma := by
          apply intervalIntegral.integral_congr
          intro sigma hsigma
          exact (hpoint sigma hsigma).symm
    _ = Complex.log (-g (1 / 2)) - Complex.log (-g 0) := hformula
    _ = Complex.log (-speiserZetaDerivRatio (1 / 2 + t * I)) -
        Complex.log (-speiserZetaDerivRatio (t * I)) := by
          simp only [g]
          norm_num

/-- Aggregate certificate for the left-half-plane winding step and its actual horizontal
`zeta'/zeta` instantiation. -/
theorem levinsonMontgomeryLeftHalfPlaneWinding_endpoint :
    (∀ (g g' : ℝ → ℂ) (a b : ℝ),
      (∀ x ∈ Set.uIcc a b, HasDerivAt g (g' x) x) →
      IntervalIntegrable (fun x => g' x / g x) (volume : Measure ℝ) a b →
      (∀ x ∈ Set.uIcc a b, (g x).re < 0) →
      g b = g a →
      (∫ x : ℝ in a..b, g' x / g x) = 0) ∧
    ∀ t : ℝ, SpeiserStrictNegativeHorizontal t →
      (∫ sigma : ℝ in (0 : ℝ)..(1 / 2),
        (logDeriv (deriv riemannZeta) (sigma + t * I) -
          logDeriv riemannZeta (sigma + t * I))) =
        Complex.log (-speiserZetaDerivRatio (1 / 2 + t * I)) -
          Complex.log (-speiserZetaDerivRatio (t * I)) := by
  exact ⟨fun _g _g' _a _b =>
    intervalIntegral_deriv_div_eq_zero_of_re_neg_of_eq,
    fun t ht => intervalIntegral_speiserZetaDerivRatio_horizontal (t := t) ht⟩

end

end LeanLab.Riemann
