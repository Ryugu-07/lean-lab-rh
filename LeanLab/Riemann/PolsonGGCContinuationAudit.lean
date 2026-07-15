import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option linter.style.header false

/-!
# Audit of an imaginary-axis Levy-Frullani component

This module checks the convergence boundary of one exponential component in the Levy-Frullani
representation used in Polson's 2018 GGC approach to the Riemann xi function. After substituting
`s = i*y`, the component has a positive exponentially growing tail when `y^2 > 2*gamma^2`.
Consequently, analytic continuation of the closed form cannot retain the original integral
representation in that regime.

This is a source-specific convergence audit. It does not obstruct analytic continuation itself
and has no implication for the truth or falsity of the Riemann hypothesis.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace LeanLab.Riemann

noncomputable section

/-- The real tail obtained from one Frullani exponential component after substituting `s=i*y`. -/
def polsonImaginaryFrullaniIntegrand (gamma y t : ℝ) : ℝ :=
  (Real.exp ((y ^ 2 / 2 - gamma ^ 2) * t) -
      Real.exp (-(gamma ^ 2) * t)) / t

/-- The corresponding complex source component before simplifying the imaginary substitution. -/
def polsonImaginaryFrullaniComponent (gamma y t : ℝ) : ℂ :=
  (Complex.exp (-((Complex.I * (y : ℂ)) ^ 2) * (t : ℂ) / 2) - 1) *
      Complex.exp ((-(gamma ^ 2 * t) : ℝ) : ℂ) / (t : ℂ)

theorem polsonImaginaryFrullaniComponent_eq_ofReal (gamma y t : ℝ) :
    polsonImaginaryFrullaniComponent gamma y t =
      (polsonImaginaryFrullaniIntegrand gamma y t : ℂ) := by
  dsimp only [polsonImaginaryFrullaniComponent, polsonImaginaryFrullaniIntegrand]
  rw [show -((Complex.I * (y : ℂ)) ^ 2) * (t : ℂ) / 2 =
      (((y ^ 2 / 2) * t : ℝ) : ℂ) by
    calc
      -((Complex.I * (y : ℂ)) ^ 2) * (t : ℂ) / 2 =
          -(Complex.I ^ 2 * (y : ℂ) ^ 2) * (t : ℂ) / 2 := by ring
      _ = (((y ^ 2 / 2) * t : ℝ) : ℂ) := by
        rw [Complex.I_sq]
        push_cast
        ring]
  rw [sub_mul, one_mul, ← Complex.exp_add]
  rw [show ((((y ^ 2 / 2) * t : ℝ) : ℂ) + ((-(gamma ^ 2 * t) : ℝ) : ℂ)) =
      ((((y ^ 2 / 2 - gamma ^ 2) * t : ℝ)) : ℂ) by
    push_cast
    ring]
  rw [← Complex.ofReal_exp, ← Complex.ofReal_exp]
  push_cast
  congr 2
  ring_nf

theorem not_integrableOn_polsonImaginaryFrullaniIntegrand
    {gamma y : ℝ} (hgamma : 0 < gamma) (hy : 2 * gamma ^ 2 < y ^ 2) :
    ¬ IntegrableOn (polsonImaginaryFrullaniIntegrand gamma y) (Ioi 1) := by
  let c : ℝ := y ^ 2 / 2 - gamma ^ 2
  have hc : 0 < c := by
    dsimp only [c]
    linarith
  have hgammaSq : 0 < gamma ^ 2 := sq_pos_of_pos hgamma
  have hgrow : Tendsto (fun t : ℝ => Real.exp (c * t) / t) atTop atTop := by
    simpa only [Real.rpow_one] using
      (tendsto_exp_mul_div_rpow_atTop 1 c hc)
  have hdecay :
      Tendsto (fun t : ℝ => Real.exp (-(gamma ^ 2) * t) / t) atTop (nhds 0) := by
    have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (-1) (gamma ^ 2) hgammaSq
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [Real.rpow_neg_one]
    field_simp
  have hgrowTwo : ∀ᶠ t : ℝ in atTop,
      2 ≤ Real.exp (c * t) / t :=
    (tendsto_atTop.1 hgrow) 2
  have hdecayOne : ∀ᶠ t : ℝ in atTop,
      Real.exp (-(gamma ^ 2) * t) / t ≤ 1 :=
    ((tendsto_order.1 hdecay).2 1 zero_lt_one).mono fun _ ht => ht.le
  have htail : ∀ᶠ t : ℝ in atTop,
      1 ≤ polsonImaginaryFrullaniIntegrand gamma y t := by
    filter_upwards [hgrowTwo, hdecayOne] with t htwo hone
    dsimp only [polsonImaginaryFrullaniIntegrand, c] at *
    rw [sub_div]
    linarith
  obtain ⟨T, hT⟩ := eventually_atTop.1 htail
  let B : ℝ := max T 1
  have hB1 : 1 ≤ B := le_max_right _ _
  have hTB : T ≤ B := le_max_left _ _
  intro hint
  have hintB : IntegrableOn (polsonImaginaryFrullaniIntegrand gamma y) (Ioi B) :=
    hint.mono_set (Ioi_subset_Ioi hB1)
  have honeInt : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioi B) := by
    refine hintB.mono' stronglyMeasurable_const.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htailAt : 1 ≤ polsonImaginaryFrullaniIntegrand gamma y t :=
      hT t (hTB.trans ht.le)
    have hnonneg : 0 ≤ polsonImaginaryFrullaniIntegrand gamma y t :=
      zero_le_one.trans htailAt
    simpa only [Real.norm_eq_abs, abs_one, abs_of_nonneg hnonneg] using htailAt
  rw [integrableOn_const_iff] at honeInt
  have hvol : volume (Ioi B) = ∞ := by simp
  rw [hvol] at honeInt
  simp at honeInt

theorem not_integrableOn_polsonImaginaryFrullaniComponent
    {gamma y : ℝ} (hgamma : 0 < gamma) (hy : 2 * gamma ^ 2 < y ^ 2) :
    ¬ IntegrableOn (polsonImaginaryFrullaniComponent gamma y) (Ioi 1) := by
  intro hint
  have heq : polsonImaginaryFrullaniComponent gamma y =
      fun t => (polsonImaginaryFrullaniIntegrand gamma y t : ℂ) := by
    funext t
    exact polsonImaginaryFrullaniComponent_eq_ofReal gamma y t
  rw [heq] at hint
  have hre := hint.re
  have hre' : IntegrableOn (polsonImaginaryFrullaniIntegrand gamma y) (Ioi 1) := by
    change Integrable
      (fun t => polsonImaginaryFrullaniIntegrand gamma y t) (volume.restrict (Ioi 1)) at hre
    exact hre
  exact not_integrableOn_polsonImaginaryFrullaniIntegrand hgamma hy hre'

end

end LeanLab.Riemann
