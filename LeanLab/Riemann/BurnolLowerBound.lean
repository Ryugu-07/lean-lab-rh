import LeanLab.Riemann.NymanBeurling
import Mathlib.Topology.MetricSpace.HausdorffDistance

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Burnol's continuous approximation spaces

This file aligns the continuously parameterized spaces in Burnol's distance lower bound with the
project's finite positive-natural kernel spaces. It contains no form of Burnol's lower bound.
-/

namespace LeanLab.Riemann

open Filter MeasureTheory Metric Set Topology
open scoped ENNReal NNReal Topology

/-- The source parameter range `0 < theta <= 1` for Burnol's continuous kernel family. -/
abbrev burnolContinuousParameter : Type :=
  {θ : ℝ // 0 < θ ∧ θ ≤ 1}

/-- Burnol's continuously parameterized fractional-part kernel in complex `L2(0, infinity)`. -/
noncomputable def burnolContinuousKernelL2
    (θ : burnolContinuousParameter) : positiveHalfLineComplexL2 :=
  baezDuarteOfRealLp
    ((fractionalPartKernel_memLp_two_positiveHalfLine θ.property.1 θ.property.2).toLp
      (fractionalPartKernel (θ : ℝ)))

/-- The kernel set with source cutoff `lambda <= theta <= 1`. -/
noncomputable def burnolKernelSet (cutoff : ℝ) : Set positiveHalfLineComplexL2 :=
  burnolContinuousKernelL2 '' {θ : burnolContinuousParameter | cutoff ≤ (θ : ℝ)}

/-- Burnol's complex finite-linear-combination space `B_lambda`. -/
noncomputable def burnolKernelSpan (cutoff : ℝ) : Submodule ℂ positiveHalfLineComplexL2 :=
  Submodule.span ℂ (burnolKernelSet cutoff)

/-- Burnol's distance `D(lambda)` from the source target to `B_lambda`. -/
noncomputable def burnolDistance (cutoff : ℝ) : ℝ :=
  infDist baezDuarteComplexTargetL2 (burnolKernelSpan cutoff : Set positiveHalfLineComplexL2)

/-- The positive-natural kernels with index at most `N`. -/
def baezDuarteFiniteComplexKernelSet
    (N : ℕ) : Set positiveHalfLineComplexL2 :=
  baezDuarteComplexKernelL2 ''
    {n : baezDuartePositiveNatIndex | (n : ℕ) ≤ N}

/-- The finite complex natural-kernel space `V_N`. -/
noncomputable def baezDuarteFiniteComplexKernelSpan
    (N : ℕ) : Submodule ℂ positiveHalfLineComplexL2 :=
  Submodule.span ℂ (baezDuarteFiniteComplexKernelSet N)

/-- The natural finite-dimensional distance `d_N`. -/
noncomputable def baezDuarteNaturalDistance (N : ℕ) : ℝ :=
  infDist baezDuarteComplexTargetL2
    (baezDuarteFiniteComplexKernelSpan N : Set positiveHalfLineComplexL2)

/-- A positive natural index supplies Burnol's continuous parameter `theta = 1/n`. -/
noncomputable def burnolContinuousParameterOfNatural
    (n : baezDuartePositiveNatIndex) : burnolContinuousParameter :=
  ⟨(((n : ℕ) : ℝ)⁻¹), baezDuarte_reciprocal_mem_restricted n⟩

theorem burnolContinuousKernelL2_ofNatural
    (n : baezDuartePositiveNatIndex) :
    burnolContinuousKernelL2 (burnolContinuousParameterOfNatural n) =
      baezDuarteComplexKernelL2 n := by
  rfl

/-- For `N > 0`, every natural kernel with index at most `N` belongs to Burnol's space at
`lambda = 1/N`. -/
theorem baezDuarteFiniteComplexKernelSpan_le_burnolKernelSpan
    (N : ℕ) (hN : 0 < N) :
    baezDuarteFiniteComplexKernelSpan N ≤
      burnolKernelSpan ((N : ℝ)⁻¹) := by
  apply Submodule.span_mono
  rintro f ⟨n, hn, rfl⟩
  refine ⟨burnolContinuousParameterOfNatural n, ?_,
    burnolContinuousKernelL2_ofNatural n⟩
  change ((N : ℝ)⁻¹) ≤ (((n : ℕ) : ℝ)⁻¹)
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hnR : (0 : ℝ) < ((n : ℕ) : ℝ) := by exact_mod_cast n.property
  exact (inv_le_inv₀ hNR hnR).2 (by exact_mod_cast hn)

/-- Distance reverses the inclusion `V_N <= B_(1/N)`. -/
theorem burnolDistance_inv_natCast_le_baezDuarteNaturalDistance
    (N : ℕ) (hN : 0 < N) :
    burnolDistance ((N : ℝ)⁻¹) ≤ baezDuarteNaturalDistance N := by
  apply infDist_le_infDist_of_subset
  · exact fun _ hx =>
      baezDuarteFiniteComplexKernelSpan_le_burnolKernelSpan N hN hx
  · exact ⟨0, (baezDuarteFiniteComplexKernelSpan N).zero_mem⟩

/-- Positive reciprocal natural parameters tend to zero from the right. -/
theorem tendsto_natCast_inv_nhdsWithin_Ioi_zero :
    Tendsto (fun N : ℕ => ((N : ℝ)⁻¹)) atTop (nhdsWithin 0 (Ioi 0)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · exact tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  · filter_upwards [eventually_atTop.2 ⟨1, fun N hN => hN⟩] with N hN
    have hNR : (0 : ℝ) < (N : ℝ) := by
      exact_mod_cast Nat.zero_lt_of_lt hN
    exact inv_pos.mpr hNR

end LeanLab.Riemann
