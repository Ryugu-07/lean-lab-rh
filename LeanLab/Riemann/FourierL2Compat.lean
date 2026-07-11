import LeanLab.Riemann.FourierMellin
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

set_option linter.style.header false

/-!
# Compatibility of classical and `L²` Fourier transforms
-/

noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap

namespace LeanLab.Riemann

/-- Composition with a nonzero dilation preserves membership in `Lᵖ` over the real line. -/
theorem MemLp.comp_mul_left_volume
    {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞} {g : ℝ → E}
    (hg : MemLp g p volume) {c : ℝ} (hc : c ≠ 0) :
    MemLp (fun x : ℝ => g (c * x)) p volume := by
  let C : ℝ≥0∞ := ENNReal.ofReal (abs (c ^ Module.finrank ℝ ℝ)⁻¹)
  have hmap : Measure.map (fun x : ℝ => c * x) volume = C • volume := by
    simpa only [C, smul_eq_mul] using
      (Measure.map_addHaar_smul (volume : Measure ℝ) hc)
  have hgmap : MemLp g p (Measure.map (fun x : ℝ => c * x) volume) := by
    rw [hmap]
    exact hg.smul_measure (by simp [C])
  exact hgmap.comp_of_map (by fun_prop)

/-- Critical-line Mellin convergence is exactly the `L¹` condition for the weighted logarithmic
pullback used by the Fourier-Mellin transform. -/
theorem integrable_weightedLog_of_mellinConvergent
    {f : ℝ → ℂ} (hf : MellinConvergent f (1 / 2 : ℂ)) :
    Integrable (fun u : ℝ =>
      (Real.exp (-u / 2) : ℂ) * f (Real.exp (-u))) := by
  have hsource : IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ (-(1 / 2 : ℂ)) * f x) (Set.Ioi 0) := by
    rw [MellinConvergent] at hf
    refine hf.congr_fun (fun x _hx => ?_) measurableSet_Ioi
    simp only [smul_eq_mul]
    congr 2
    ring
  have hchange :=
    (integrableOn_image_iff_integrableOn_abs_deriv_smul
      (s := (Set.univ : Set ℝ)) MeasurableSet.univ
      expNeg_hasDerivWithinAt expNeg_injOn_univ
      (fun x : ℝ => (x : ℂ) ^ (-(1 / 2 : ℂ)) * f x)).mp (by
        rwa [expNeg_image_univ])
  rw [integrableOn_univ] at hchange
  exact hchange.congr (ae_of_all volume fun u => by
    simp only [abs_neg, abs_of_pos (Real.exp_pos _), Complex.real_smul, expNeg]
    rw [show (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) by norm_num]
    rw [← Complex.ofReal_cpow (Real.exp_pos _).le]
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, ← mul_assoc,
      ← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring_nf)

/-- For an `L¹ ∩ L²` function whose classical Fourier transform is in `L²`, Mathlib's abstract
`L²` Fourier transform is represented by the classical Fourier integral. -/
theorem fourier_toLp_eq_toLp_fourier
    {f : ℝ → ℂ} (hf1 : Integrable f) (hf2 : MemLp f (2 : ℝ≥0∞) volume)
    (hFourier2 : MemLp (𝓕 f) (2 : ℝ≥0∞) volume) :
    𝓕 (hf2.toLp f) = hFourier2.toLp (𝓕 f) := by
  have hdist :
      ((𝓕 (hf2.toLp f) : realLineComplexL2) : 𝓢'(ℝ, ℂ)) =
        ((hFourier2.toLp (𝓕 f) : realLineComplexL2) : 𝓢'(ℝ, ℂ)) := by
    rw [← MeasureTheory.Lp.fourier_toTemperedDistribution_eq]
    ext g
    simp only [TemperedDistribution.fourier_apply, MeasureTheory.Lp.toTemperedDistribution_apply]
    have hFubini := VectorFourier.integral_fourierIntegral_smul_eq_flip
      (μ := volume) (ν := volume) (L := innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner hf1 g.integrable
    calc
      ∫ x : ℝ, (𝓕 g x) • (hf2.toLp f) x =
          ∫ x : ℝ, (𝓕 g x) • f x := by
            apply integral_congr_ae
            filter_upwards [hf2.coeFn_toLp] with x hx
            rw [hx]
      _ = ∫ x : ℝ, f x • (𝓕 g x) := by
            congr with x
            exact mul_comm _ _
      _ = ∫ x : ℝ, (𝓕 f x) • g x := by
            simpa using! hFubini.symm
      _ = ∫ x : ℝ, g x • (𝓕 f x) := by
            congr with x
            exact mul_comm _ _
      _ = ∫ x : ℝ, g x • (hFourier2.toLp (𝓕 f)) x := by
            apply integral_congr_ae
            filter_upwards [hFourier2.coeFn_toLp] with x hx
            rw [hx]
  have hinjective : Function.Injective
      (MeasureTheory.Lp.toTemperedDistributionCLM ℂ (volume : Measure ℝ) (2 : ℝ≥0∞)) := by
    exact LinearMap.ker_eq_bot.1
      MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot
  exact hinjective hdist

end LeanLab.Riemann
