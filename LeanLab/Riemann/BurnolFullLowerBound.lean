import LeanLab.Riemann.BurnolFiniteLowerBound
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

set_option linter.style.header false

/-!
# Burnol's full-zero-sum lower bound and natural transfer

This file assembles the full nonnegative zero sum and transfers the continuous Burnol lower bound
to the finite positive-natural kernel spaces.
-/

noncomputable section

open Complex Filter Set
open scoped ENNReal Real Topology

namespace LeanLab.Riemann

/-- The nonnegative real contribution of one nontrivial zeta zero to Burnol's lower bound. -/
def burnolZeroContribution
    (rho : {rho : ℂ // IsNontrivialZero rho}) : ℝ :=
  (burnolZetaZeroMultiplicity (rho : ℂ) : ℝ) ^ 2 / ‖(rho : ℂ)‖ ^ 2

theorem burnolZeroContribution_nonneg
    (rho : {rho : ℂ // IsNontrivialZero rho}) :
    0 ≤ burnolZeroContribution rho :=
  div_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The extended full-zero constant in Burnol's lower bound. -/
def burnolFullZeroLowerConstant : ℝ≥0∞ :=
  (∑' rho : {rho : ℂ // IsNontrivialZero rho},
    ENNReal.ofReal (burnolZeroContribution rho)) ^ (1 / 2 : ℝ)

theorem burnolFiniteZeroLowerConstant_eq_rpow
    (R : Finset {rho : ℂ // IsNontrivialZero rho}) :
    ENNReal.ofReal (Real.sqrt (∑ rho ∈ R, burnolZeroContribution rho)) =
      (∑ rho ∈ R, ENNReal.ofReal (burnolZeroContribution rho)) ^ (1 / 2 : ℝ) := by
  have hsum : 0 ≤ ∑ rho ∈ R, burnolZeroContribution rho :=
    Finset.sum_nonneg fun _ _ => burnolZeroContribution_nonneg _
  rw [Real.sqrt_eq_rpow,
    ← ENNReal.ofReal_rpow_of_nonneg hsum (by norm_num),
    ENNReal.ofReal_sum_of_nonneg]
  exact fun _ _ => burnolZeroContribution_nonneg _

theorem RiemannHypothesis.burnolDistance_liminf_ge_fullZeroSum
    (hRH : RiemannHypothesis) :
    burnolFullZeroLowerConstant ≤
      Filter.liminf (fun lambda : ℝ =>
        ENNReal.ofReal (burnolDistance lambda) *
          ENNReal.ofReal (Real.sqrt (burnolLogScale lambda)))
        (nhdsWithin 0 (Ioi 0)) := by
  rw [burnolFullZeroLowerConstant, ENNReal.tsum_eq_iSup_sum]
  change (ENNReal.orderIsoRpow (1 / 2 : ℝ) (by norm_num))
      (⨆ R : Finset {rho : ℂ // IsNontrivialZero rho},
        ∑ rho ∈ R, ENNReal.ofReal (burnolZeroContribution rho)) ≤ _
  rw [(ENNReal.orderIsoRpow (1 / 2 : ℝ) (by norm_num)).map_iSup]
  apply iSup_le
  intro R
  change (∑ rho ∈ R, ENNReal.ofReal (burnolZeroContribution rho)) ^
      (1 / 2 : ℝ) ≤ _
  rw [← burnolFiniteZeroLowerConstant_eq_rpow R]
  simpa only [burnolZeroContribution] using
    RiemannHypothesis.burnolDistance_liminf_ge_finset hRH R

theorem burnolLogScale_inv_natCast (N : ℕ) :
    burnolLogScale ((N : ℝ)⁻¹) = Real.log (N : ℝ) := by
  simp [burnolLogScale]

theorem eventually_burnolScaledDistance_inv_natCast_le_naturalDistance :
    ∀ᶠ N : ℕ in atTop,
      ENNReal.ofReal (burnolDistance ((N : ℝ)⁻¹)) *
          ENNReal.ofReal (Real.sqrt (burnolLogScale ((N : ℝ)⁻¹))) ≤
        ENNReal.ofReal (baezDuarteNaturalDistance N) *
          ENNReal.ofReal (Real.sqrt (Real.log (N : ℝ))) := by
  filter_upwards [eventually_atTop.2 ⟨1, fun N hN => hN⟩] with N hN
  have hNpos : 0 < N := by omega
  rw [burnolLogScale_inv_natCast]
  exact mul_le_mul_left
    (ENNReal.ofReal_le_ofReal
      (burnolDistance_inv_natCast_le_baezDuarteNaturalDistance N hNpos)) _

theorem RiemannHypothesis.baezDuarteNaturalDistance_liminf_ge_fullZeroSum
    (hRH : RiemannHypothesis) :
    burnolFullZeroLowerConstant ≤
      Filter.liminf (fun N : ℕ =>
        ENNReal.ofReal (baezDuarteNaturalDistance N) *
          ENNReal.ofReal (Real.sqrt (Real.log (N : ℝ)))) atTop := by
  let F : ℝ → ℝ≥0∞ := fun lambda =>
    ENNReal.ofReal (burnolDistance lambda) *
      ENNReal.ofReal (Real.sqrt (burnolLogScale lambda))
  let G : ℕ → ℝ≥0∞ := fun N =>
    ENNReal.ofReal (baezDuarteNaturalDistance N) *
      ENNReal.ofReal (Real.sqrt (Real.log (N : ℝ)))
  calc
    burnolFullZeroLowerConstant ≤
        Filter.liminf F (nhdsWithin 0 (Ioi 0)) :=
      RiemannHypothesis.burnolDistance_liminf_ge_fullZeroSum hRH
    _ ≤ Filter.liminf (F ∘ fun N : ℕ => ((N : ℝ)⁻¹)) atTop :=
      tendsto_natCast_inv_nhdsWithin_Ioi_zero.liminf_le_liminf_comp
    _ ≤ Filter.liminf G atTop := by
      refine Filter.liminf_le_liminf ?_ (by isBoundedDefault) (by isBoundedDefault)
      simpa only [F, G, Function.comp_apply] using
        eventually_burnolScaledDistance_inv_natCast_le_naturalDistance

end LeanLab.Riemann
