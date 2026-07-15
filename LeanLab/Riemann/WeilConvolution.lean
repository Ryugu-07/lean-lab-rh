import LeanLab.Riemann.WeilTestAlgebra
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.MellinInversion

set_option linter.style.header false

/-!
# Multiplicative convolution for Weil test functions

This file formalizes the Mellin-convolution product used in Lagarias, Appendix A, formula (A.7).
The proof transports multiplicative convolution to additive convolution in logarithmic coordinates
and applies Mathlib's Bochner-integral convolution theorem.
-/

noncomputable section

open Complex MeasureTheory Real Set
open scoped ComplexConjugate Convolution

namespace LeanLab.Riemann

private theorem rexpNeg_hasDerivWithin :
    ∀ x ∈ univ, HasDerivWithinAt (rexp ∘ Neg.neg) (-rexp (-x)) univ x :=
  fun x _ ↦ mul_neg_one (rexp (-x)) ▸
    ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).hasDerivWithinAt

private theorem rexpNeg_image : rexp ∘ Neg.neg '' univ = Ioi 0 := by
  rw [Set.image_comp, Set.image_univ_of_surjective neg_surjective, Set.image_univ, Real.range_exp]

private theorem rexpNeg_injOn : univ.InjOn (rexp ∘ Neg.neg) :=
  Real.exp_injective.injOn.comp neg_injective.injOn (univ.mapsTo_univ _)

private theorem rexpNeg_mellinJacobian (x : ℝ) (s : ℂ) (z : ℂ) :
    cexp (-↑x) * (cexp (-↑x) ^ (s - 1) * z) = cexp (-s * ↑x) * z := by
  rw [← mul_assoc]
  congr 1
  conv_lhs => lhs; rw [← cpow_one (cexp _)]
  rw [← cpow_add _ _ (Complex.exp_ne_zero _),
    cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simp [pi_pos]) (by simpa using pi_nonneg)]
  ring_nf

/-- The Mellin integrand in logarithmic coordinates `x = exp(-u)`. -/
def mellinLogLift (f : ℝ → ℂ) (s : ℂ) (u : ℝ) : ℂ :=
  cexp (-s * u) * f (rexp (-u))

/-- Mellin convergence is exactly integrability of the logarithmic lift. -/
theorem mellinConvergent_iff_integrable_mellinLogLift (f : ℝ → ℂ) (s : ℂ) :
    MellinConvergent f s ↔ Integrable (mellinLogLift f s) := by
  rw [MellinConvergent, ← rexpNeg_image,
    integrableOn_image_iff_integrableOn_abs_deriv_smul
      MeasurableSet.univ rexpNeg_hasDerivWithin rexpNeg_injOn]
  simp only [IntegrableOn, Measure.restrict_univ, Function.comp_apply, abs_neg,
    abs_of_pos (Real.exp_pos _), Complex.real_smul, smul_eq_mul, Complex.ofReal_exp]
  exact integrable_congr (Filter.Eventually.of_forall fun x ↦ by
    simpa only [mellinLogLift, Complex.ofReal_neg] using
      rexpNeg_mellinJacobian x s (f (rexp (-x))))

/-- The Mellin transform is the integral of its logarithmic lift. -/
theorem mellin_eq_integral_mellinLogLift (f : ℝ → ℂ) (s : ℂ) :
    mellin f s = ∫ u : ℝ, mellinLogLift f s u := by
  rw [mellin, ← rexpNeg_image,
    integral_image_eq_integral_abs_deriv_smul
      MeasurableSet.univ rexpNeg_hasDerivWithin rexpNeg_injOn]
  simp only [Measure.restrict_univ, Function.comp_apply, abs_neg,
    abs_of_pos (Real.exp_pos _), Complex.real_smul, smul_eq_mul, Complex.ofReal_exp]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦ by
    simpa only [mellinLogLift, Complex.ofReal_neg] using
      rexpNeg_mellinJacobian x s (f (rexp (-x)))

/-- Source-faithful multiplicative convolution with Haar element `dy / y` on `ℝ_{>0}`. -/
def weilConvolution (f g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y : ℝ in Ioi 0, f y * g (x / y) / (y : ℂ)

private theorem weilConvolution_eq_mellin_zero (f g : ℝ → ℂ) (x : ℝ) :
    weilConvolution f g x = mellin (fun y : ℝ ↦ f y * g (x / y)) 0 := by
  rw [weilConvolution, mellin]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y hy
  simp only [zero_sub, cpow_neg_one, smul_eq_mul]
  ring

/-- In logarithmic coordinates, multiplicative convolution is additive convolution. -/
theorem weilConvolution_exp_neg (f g : ℝ → ℂ) (w : ℝ) :
    weilConvolution f g (rexp (-w)) =
      ∫ u : ℝ, f (rexp (-u)) * g (rexp (-(w - u))) := by
  rw [weilConvolution_eq_mellin_zero, mellin_eq_integral_mellinLogLift]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u ↦ by
    simp only [mellinLogLift, neg_zero, zero_mul, Complex.exp_zero, one_mul]
    congr 2
    rw [← Real.exp_sub]
    congr 1
    ring

/-- The logarithmic lift of multiplicative convolution is additive convolution of the lifts. -/
theorem mellinLogLift_weilConvolution (f g : ℝ → ℂ) (s : ℂ) :
    mellinLogLift (weilConvolution f g) s =
      mellinLogLift f s ⋆[ContinuousLinearMap.mul ℂ ℂ] mellinLogLift g s := by
  funext w
  rw [mellinLogLift, weilConvolution_exp_neg, convolution_mul, ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u ↦ by
    have hexp : cexp (-s * (w : ℂ)) =
        cexp (-s * (u : ℂ)) * cexp (-s * ((w - u : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp only [mellinLogLift]
    rw [hexp]
    ring

/-- Convergent Mellin inputs have a convergent multiplicative convolution. -/
theorem mellinConvergent_weilConvolution {f g : ℝ → ℂ} {s : ℂ}
    (hf : MellinConvergent f s) (hg : MellinConvergent g s) :
    MellinConvergent (weilConvolution f g) s := by
  rw [mellinConvergent_iff_integrable_mellinLogLift,
    mellinLogLift_weilConvolution]
  exact (mellinConvergent_iff_integrable_mellinLogLift f s).mp hf |>.integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ)
    ((mellinConvergent_iff_integrable_mellinLogLift g s).mp hg)

/-- Mellin transform converts source-faithful multiplicative convolution into multiplication. -/
theorem mellin_weilConvolution {f g : ℝ → ℂ} {s : ℂ}
    (hf : MellinConvergent f s) (hg : MellinConvergent g s) :
    mellin (weilConvolution f g) s = mellin f s * mellin g s := by
  rw [mellin_eq_integral_mellinLogLift, mellinLogLift_weilConvolution,
    integral_convolution (ContinuousLinearMap.mul ℂ ℂ)
      ((mellinConvergent_iff_integrable_mellinLogLift f s).mp hf)
      ((mellinConvergent_iff_integrable_mellinLogLift g s).mp hg),
    ← mellin_eq_integral_mellinLogLift, ← mellin_eq_integral_mellinLogLift]
  rfl

/-- Formula (A.7)'s convolution-star Mellin factorization. -/
theorem mellin_weilConvolution_star {f g : ℝ → ℂ} {s : ℂ}
    (hf : MellinConvergent f s) (hg : MellinConvergent g (1 - conj s)) :
    mellin (weilConvolution f (weilStar g)) s =
      mellin f s * conj (mellin g (1 - conj s)) := by
  rw [mellin_weilConvolution hf ((mellinConvergent_weilStar_iff g s).2 hg),
    mellin_weilStar]

/-- On the critical line, convolution with the Weil star becomes the Hermitian product. -/
theorem mellin_weilConvolution_star_criticalLine {f g : ℝ → ℂ} (t : ℝ)
    (hf : MellinConvergent f (1 / 2 + (t : ℂ) * I))
    (hg : MellinConvergent g (1 / 2 + (t : ℂ) * I)) :
    mellin (weilConvolution f (weilStar g)) (1 / 2 + (t : ℂ) * I) =
      mellin f (1 / 2 + (t : ℂ) * I) * conj (mellin g (1 / 2 + (t : ℂ) * I)) := by
  have hstar : MellinConvergent (weilStar g) (1 / 2 + (t : ℂ) * I) := by
    rw [mellinConvergent_weilStar_iff]
    convert hg using 1
    apply Complex.ext
    · norm_num
    · norm_num
  rw [mellin_weilConvolution hf hstar, mellin_weilStar_criticalLine]

/-- A critical-line Weil autocorrelation has pointwise spectral value `normSq`. -/
theorem mellin_weilAutocorrelation_criticalLine {f : ℝ → ℂ} (t : ℝ)
    (hf : MellinConvergent f (1 / 2 + (t : ℂ) * I)) :
    mellin (weilConvolution f (weilStar f)) (1 / 2 + (t : ℂ) * I) =
      normSq (mellin f (1 / 2 + (t : ℂ) * I)) := by
  rw [mellin_weilConvolution_star_criticalLine t hf hf, Complex.mul_conj]

end LeanLab.Riemann
