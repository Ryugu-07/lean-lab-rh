import LeanLab.Riemann.FourierMellin
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

set_option linter.style.header false

/-!
# Quantitative convergence inputs in the Baez-Duarte criterion

This file starts the source-specific convergence layer by formalizing the `L²` membership of the
vertical-line power majorant used in Section 2.2 of Baez-Duarte's proof.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace LeanLab.Riemann

/-- The vertical-line power majorant appearing in Baez-Duarte's convergence proof. -/
def baezDuarteVerticalMajorant (β τ : ℝ) : ℂ :=
  ((1 + |τ|) ^ (-1 + β) : ℝ)

theorem baezDuarteVerticalMajorant_stronglyMeasurable (β : ℝ) :
    StronglyMeasurable (baezDuarteVerticalMajorant β) := by
  change StronglyMeasurable (fun τ : ℝ =>
    (((1 + |τ|) ^ (-1 + β) : ℝ) : ℂ))
  fun_prop

theorem baezDuarteVerticalMajorant_sq_norm (β τ : ℝ) :
    ‖baezDuarteVerticalMajorant β τ‖ ^ 2 =
      (1 + ‖τ‖) ^ (-(2 - 2 * β)) := by
  rw [baezDuarteVerticalMajorant, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _), Real.norm_eq_abs,
    ← Real.rpow_mul_natCast (by positivity : 0 ≤ 1 + |τ|) (-1 + β) 2]
  congr 1
  ring

/-- The source majorant `(1 + |tau|)^(-1 + beta)` belongs to `L²(R)` exactly in the
parameter range needed by the proof. -/
theorem baezDuarteVerticalMajorant_memLp
    (β : ℝ) (hβ : β < 1 / 2) :
    MemLp (baezDuarteVerticalMajorant β) (2 : ℝ≥0∞) volume := by
  rw [memLp_two_iff_integrable_sq_norm
    (baezDuarteVerticalMajorant_stronglyMeasurable β).aestronglyMeasurable]
  have hpower : (1 : ℝ) < 2 - 2 * β := by linarith
  have hintegrable :
      Integrable (fun τ : ℝ => (1 + ‖τ‖) ^ (-(2 - 2 * β))) := by
    exact integrable_one_add_norm (E := ℝ) (μ := volume) (by
      simpa only [Module.finrank_self, Nat.cast_one] using hpower)
  exact hintegrable.congr (ae_of_all volume fun τ =>
    (baezDuarteVerticalMajorant_sq_norm β τ).symm)

/-- The specialization used for the first convergence passage in Baez-Duarte's proof. -/
theorem baezDuarteFirstConvergenceMajorant_memLp
    (ε : ℝ) (hε : ε < 1 / 4) :
    MemLp (baezDuarteVerticalMajorant (2 * ε)) (2 : ℝ≥0∞) volume := by
  apply baezDuarteVerticalMajorant_memLp
  linarith

/-- Ordinates of zeros of zeta on the critical line. These are the exceptional points in the
pointwise limit of the source's zeta ratio. -/
def baezDuarteCriticalLineZetaZeroOrdinates : Set ℝ :=
  {τ | riemannZeta ((1 / 2 : ℂ) + τ * Complex.I) = 0}

theorem riemannZetaZeros_countable : riemannZetaZeros.Countable := by
  exact (HereditarilyLindelofSpace.isLindelof riemannZetaZeros).countable_of_isDiscrete
    isDiscrete_riemannZetaZeros

theorem baezDuarteCriticalLineMap_injective :
    Function.Injective (fun τ : ℝ => (1 / 2 : ℂ) + τ * Complex.I) := by
  intro τ υ h
  have him := congrArg Complex.im h
  simpa using him

theorem baezDuarteCriticalLineZetaZeroOrdinates_countable :
    baezDuarteCriticalLineZetaZeroOrdinates.Countable := by
  have hpreimage :=
    riemannZetaZeros_countable.preimage baezDuarteCriticalLineMap_injective
  change ((fun τ : ℝ => (1 / 2 : ℂ) + τ * Complex.I) ⁻¹'
    riemannZetaZeros).Countable
  exact hpreimage

theorem baezDuarteCriticalLineZetaZeroOrdinates_measure_zero :
    volume baezDuarteCriticalLineZetaZeroOrdinates = 0 :=
  baezDuarteCriticalLineZetaZeroOrdinates_countable.measure_zero volume

theorem ae_riemannZeta_criticalLine_ne_zero :
    ∀ᵐ τ : ℝ ∂volume,
      riemannZeta ((1 / 2 : ℂ) + τ * Complex.I) ≠ 0 := by
  simpa only [baezDuarteCriticalLineZetaZeroOrdinates, Set.mem_setOf_eq] using
    (measure_eq_zero_iff_ae_notMem.mp
      baezDuarteCriticalLineZetaZeroOrdinates_measure_zero)

/-- The zeta ratio in the source's unconditional convergence passage. -/
def baezDuarteZetaRatio (ε τ : ℝ) : ℂ :=
  riemannZeta ((1 / 2 : ℂ) - ε + τ * Complex.I) /
    riemannZeta ((1 / 2 : ℂ) + ε + τ * Complex.I)

theorem tendsto_baezDuarteZetaRatio_one_of_ne_zero
    (τ : ℝ) (hζ : riemannZeta ((1 / 2 : ℂ) + τ * Complex.I) ≠ 0) :
    Filter.Tendsto (fun ε : ℝ => baezDuarteZetaRatio ε τ)
      (nhds 0) (nhds 1) := by
  have hs_ne : (1 / 2 : ℂ) + τ * Complex.I ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
  have hz_cont : ContinuousAt riemannZeta ((1 / 2 : ℂ) + τ * Complex.I) :=
    (differentiableAt_riemannZeta hs_ne).continuousAt
  have hcoe :
      Filter.Tendsto (fun ε : ℝ => (ε : ℂ)) (nhds 0) (nhds 0) :=
    Complex.continuous_ofReal.continuousAt
  have hminus :
      Filter.Tendsto (fun ε : ℝ => (1 / 2 : ℂ) - ε + τ * Complex.I)
        (nhds 0) (nhds ((1 / 2 : ℂ) + τ * Complex.I)) := by
    simpa using (tendsto_const_nhds.sub hcoe).add tendsto_const_nhds
  have hplus :
      Filter.Tendsto (fun ε : ℝ => (1 / 2 : ℂ) + ε + τ * Complex.I)
        (nhds 0) (nhds ((1 / 2 : ℂ) + τ * Complex.I)) := by
    simpa using (tendsto_const_nhds.add hcoe).add tendsto_const_nhds
  have hnum :
      Filter.Tendsto
        (fun ε : ℝ => riemannZeta ((1 / 2 : ℂ) - ε + τ * Complex.I))
        (nhds 0) (nhds (riemannZeta ((1 / 2 : ℂ) + τ * Complex.I))) :=
    hz_cont.tendsto.comp hminus
  have hden :
      Filter.Tendsto
        (fun ε : ℝ => riemannZeta ((1 / 2 : ℂ) + ε + τ * Complex.I))
        (nhds 0) (nhds (riemannZeta ((1 / 2 : ℂ) + τ * Complex.I))) :=
    hz_cont.tendsto.comp hplus
  change
    Filter.Tendsto
      ((fun ε : ℝ => riemannZeta ((1 / 2 : ℂ) - ε + τ * Complex.I)) /
        fun ε : ℝ => riemannZeta ((1 / 2 : ℂ) + ε + τ * Complex.I))
      (nhds 0) (nhds 1)
  simpa only [div_self hζ] using hnum.div hden hζ

theorem ae_tendsto_baezDuarteZetaRatio_one :
    ∀ᵐ τ : ℝ ∂volume,
      Filter.Tendsto (fun ε : ℝ => baezDuarteZetaRatio ε τ)
        (nhds 0) (nhds 1) := by
  filter_upwards [ae_riemannZeta_criticalLine_ne_zero] with τ hζ
  exact tendsto_baezDuarteZetaRatio_one_of_ne_zero τ hζ

end LeanLab.Riemann
