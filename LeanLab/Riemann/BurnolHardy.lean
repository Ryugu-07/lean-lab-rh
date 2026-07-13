import LeanLab.Riemann.BurnolA
import LeanLab.Riemann.BaezDuarteForwardLimit
import LeanLab.Riemann.FourierL2Compat
import Mathlib.MeasureTheory.Function.Holder

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Burnol's critical-line phase operator

This file constructs the unitary multiplier used in Burnol's distance model and transports it
through the project's Fourier--Mellin isometry.
-/

noncomputable section

namespace LeanLab.Riemann

open MeasureTheory Metric Set
open scoped ENNReal FourierTransform NNReal Topology

/-- The critical-line point corresponding to the project's Fourier frequency `xi`. -/
def burnolCriticalLineAtFrequency (xi : ℝ) : ℂ :=
  (1 / 2 : ℂ) + ((2 * Real.pi * xi : ℝ) : ℂ) * Complex.I

theorem continuous_burnolCriticalLineAtFrequency :
    Continuous burnolCriticalLineAtFrequency := by
  unfold burnolCriticalLineAtFrequency
  fun_prop

theorem burnolCriticalLineAtFrequency_ne_zero (xi : ℝ) :
    burnolCriticalLineAtFrequency xi ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num [burnolCriticalLineAtFrequency] at hre

/-- Burnol's multiplier for `T=(1-M)^{-1}` on the critical line. -/
def burnolHardyInverseMultiplier (xi : ℝ) : ℂ :=
  (burnolCriticalLineAtFrequency xi - 1) / burnolCriticalLineAtFrequency xi

theorem continuous_burnolHardyInverseMultiplier :
    Continuous burnolHardyInverseMultiplier := by
  apply Continuous.div
  · exact continuous_burnolCriticalLineAtFrequency.sub continuous_const
  · exact continuous_burnolCriticalLineAtFrequency
  exact burnolCriticalLineAtFrequency_ne_zero

theorem norm_burnolCriticalLine_sub_one (xi : ℝ) :
    ‖burnolCriticalLineAtFrequency xi - 1‖ =
      ‖burnolCriticalLineAtFrequency xi‖ := by
  rw [Complex.norm_def, Complex.norm_def]
  congr 1
  simp only [Complex.normSq_apply]
  norm_num [burnolCriticalLineAtFrequency]

theorem norm_burnolHardyInverseMultiplier (xi : ℝ) :
    ‖burnolHardyInverseMultiplier xi‖ = 1 := by
  rw [burnolHardyInverseMultiplier, norm_div,
    norm_burnolCriticalLine_sub_one]
  exact div_self (norm_ne_zero_iff.mpr (burnolCriticalLineAtFrequency_ne_zero xi))

/-- The inverse phase, written explicitly as complex conjugation. -/
def burnolHardyInverseMultiplierInv (xi : ℝ) : ℂ :=
  (starRingEnd ℂ) (burnolHardyInverseMultiplier xi)

theorem continuous_burnolHardyInverseMultiplierInv :
    Continuous burnolHardyInverseMultiplierInv := by
  change Continuous (fun xi =>
    (starRingEnd ℂ) (burnolHardyInverseMultiplier xi))
  exact Complex.continuous_conj.comp continuous_burnolHardyInverseMultiplier

theorem norm_burnolHardyInverseMultiplierInv (xi : ℝ) :
    ‖burnolHardyInverseMultiplierInv xi‖ = 1 := by
  rw [burnolHardyInverseMultiplierInv, Complex.norm_conj,
    norm_burnolHardyInverseMultiplier]

theorem burnolHardyInverseMultiplierInv_mul (xi : ℝ) :
    burnolHardyInverseMultiplierInv xi * burnolHardyInverseMultiplier xi = 1 := by
  rw [burnolHardyInverseMultiplierInv, Complex.conj_mul',
    norm_burnolHardyInverseMultiplier]
  norm_num

theorem burnolHardyInverseMultiplier_mul_inv (xi : ℝ) :
    burnolHardyInverseMultiplier xi * burnolHardyInverseMultiplierInv xi = 1 := by
  rw [mul_comm, burnolHardyInverseMultiplierInv_mul]

theorem burnolHardyInverseMultiplier_memLp_top :
    MemLp burnolHardyInverseMultiplier ∞ volume := by
  apply memLp_top_of_bound
    continuous_burnolHardyInverseMultiplier.aestronglyMeasurable 1
  exact ae_of_all volume fun xi => (norm_burnolHardyInverseMultiplier xi).le

theorem burnolHardyInverseMultiplierInv_memLp_top :
    MemLp burnolHardyInverseMultiplierInv ∞ volume := by
  apply memLp_top_of_bound
    continuous_burnolHardyInverseMultiplierInv.aestronglyMeasurable 1
  exact ae_of_all volume fun xi => (norm_burnolHardyInverseMultiplierInv xi).le

/-- The forward phase as an `L-infinity` function. -/
def burnolHardyInverseMultiplierLInf : Lp (α := ℝ) ℂ ∞ volume :=
  burnolHardyInverseMultiplier_memLp_top.toLp burnolHardyInverseMultiplier

theorem burnolHardyInverseMultiplierLInf_coeFn :
    burnolHardyInverseMultiplierLInf =ᵐ[volume]
      burnolHardyInverseMultiplier := by
  exact MemLp.coeFn_toLp burnolHardyInverseMultiplier_memLp_top

/-- The inverse phase as an `L-infinity` function. -/
def burnolHardyInverseMultiplierInvLInf : Lp (α := ℝ) ℂ ∞ volume :=
  burnolHardyInverseMultiplierInv_memLp_top.toLp burnolHardyInverseMultiplierInv

theorem burnolHardyInverseMultiplierInvLInf_coeFn :
    burnolHardyInverseMultiplierInvLInf =ᵐ[volume]
      burnolHardyInverseMultiplierInv := by
  exact MemLp.coeFn_toLp burnolHardyInverseMultiplierInv_memLp_top

theorem burnolFrequencyPhase_left_inv (g : realLineComplexL2) :
    burnolHardyInverseMultiplierInvLInf •
        (burnolHardyInverseMultiplierLInf • g : realLineComplexL2) = g := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞))
      burnolHardyInverseMultiplierInvLInf
      (burnolHardyInverseMultiplierLInf • g : realLineComplexL2),
    Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) burnolHardyInverseMultiplierLInf g,
    burnolHardyInverseMultiplierInvLInf_coeFn,
    burnolHardyInverseMultiplierLInf_coeFn] with xi hout hinv hinvPhase hphase
  rw [hout]
  change burnolHardyInverseMultiplierInvLInf xi *
    (burnolHardyInverseMultiplierLInf • g : realLineComplexL2) xi = g xi
  rw [hinv, hinvPhase]
  change burnolHardyInverseMultiplierInv xi *
    (burnolHardyInverseMultiplierLInf xi * g xi) = g xi
  rw [hphase]
  rw [← mul_assoc, burnolHardyInverseMultiplierInv_mul, one_mul]

theorem burnolFrequencyPhase_right_inv (g : realLineComplexL2) :
    burnolHardyInverseMultiplierLInf •
        (burnolHardyInverseMultiplierInvLInf • g : realLineComplexL2) = g := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞))
      burnolHardyInverseMultiplierLInf
      (burnolHardyInverseMultiplierInvLInf • g : realLineComplexL2),
    Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) burnolHardyInverseMultiplierInvLInf g,
    burnolHardyInverseMultiplierLInf_coeFn,
    burnolHardyInverseMultiplierInvLInf_coeFn] with xi hout hinv hphase hinvPhase
  rw [hout]
  change burnolHardyInverseMultiplierLInf xi *
    (burnolHardyInverseMultiplierInvLInf • g : realLineComplexL2) xi = g xi
  rw [hinv, hphase]
  change burnolHardyInverseMultiplier xi *
    (burnolHardyInverseMultiplierInvLInf xi * g xi) = g xi
  rw [hinvPhase]
  rw [← mul_assoc, burnolHardyInverseMultiplier_mul_inv, one_mul]

/-- Pointwise multiplication by Burnol's phase as a complex-linear equivalence of frequency
`L2`. -/
def burnolFrequencyPhaseLinearEquiv :
    realLineComplexL2 ≃ₗ[ℂ] realLineComplexL2 where
  toFun g := burnolHardyInverseMultiplierLInf • g
  invFun g := burnolHardyInverseMultiplierInvLInf • g
  map_add' g h := Lp.add_smul burnolHardyInverseMultiplierLInf g h
  map_smul' c g := (Lp.smul_comm c burnolHardyInverseMultiplierLInf g).symm
  left_inv := burnolFrequencyPhase_left_inv
  right_inv := burnolFrequencyPhase_right_inv

theorem norm_burnolFrequencyPhase (g : realLineComplexL2) :
    ‖(burnolHardyInverseMultiplierLInf • g : realLineComplexL2)‖ = ‖g‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae
  filter_upwards [Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞))
      burnolHardyInverseMultiplierLInf g,
    burnolHardyInverseMultiplierLInf_coeFn] with xi hmul hphase
  rw [hmul]
  change ‖burnolHardyInverseMultiplierLInf xi * g xi‖ = ‖g xi‖
  rw [hphase]
  simp only [norm_mul,
    norm_burnolHardyInverseMultiplier, one_mul]

/-- Burnol's unit-modulus phase as a complex-linear isometric equivalence of frequency `L2`. -/
def burnolFrequencyPhaseL2 :
    realLineComplexL2 ≃ₗᵢ[ℂ] realLineComplexL2 where
  toLinearEquiv := burnolFrequencyPhaseLinearEquiv
  norm_map' := norm_burnolFrequencyPhase

theorem burnolFrequencyPhaseL2_apply (g : realLineComplexL2) :
    burnolFrequencyPhaseL2 g = burnolHardyInverseMultiplierLInf • g :=
  rfl

/-- Burnol's phase transported to complex `L2(0,infinity)` by the Fourier--Mellin isometry. -/
def burnolHardyInverseL2 :
    positiveHalfLineComplexL2 ≃ₗᵢ[ℂ] positiveHalfLineComplexL2 :=
  baezDuarteFourierMellinL2.trans
    (burnolFrequencyPhaseL2.trans baezDuarteFourierMellinL2.symm)

theorem baezDuarteFourierMellinL2_burnolHardyInverseL2
    (f : positiveHalfLineComplexL2) :
    baezDuarteFourierMellinL2 (burnolHardyInverseL2 f) =
      burnolFrequencyPhaseL2 (baezDuarteFourierMellinL2 f) := by
  simp [burnolHardyInverseL2]

/-! ## The explicit transformed target -/

/-- Burnol's transformed target `(1 + log t) * 1_(0,1](t)`. -/
def burnolChiOne (t : ℝ) : ℝ :=
  (Ioc (0 : ℝ) 1).indicator (fun x => 1 + Real.log x) t

theorem measurable_burnolChiOne : Measurable burnolChiOne := by
  exact (measurable_const.add Real.measurable_log).indicator measurableSet_Ioc

theorem burnolChiOne_eq_of_mem {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    burnolChiOne t = 1 + Real.log t := by
  simp [burnolChiOne, ht]

theorem burnolChiOne_eq_zero_of_not_mem {t : ℝ} (ht : t ∉ Ioc (0 : ℝ) 1) :
    burnolChiOne t = 0 := by
  simp [burnolChiOne, ht]

theorem burnolChiOne_memLp_two_positiveHalfLine :
    MemLp burnolChiOne (2 : ℝ≥0∞)
      (volume.restrict (Ioi (0 : ℝ))) := by
  rw [memLp_two_iff_integrable_sq measurable_burnolChiOne.aestronglyMeasurable]
  change IntegrableOn (fun t : ℝ => burnolChiOne t ^ 2) (Ioi (0 : ℝ)) volume
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  apply IntegrableOn.union
  · have hbase : IntegrableOn (fun t : ℝ => t ^ (-1 / 2 : ℝ)) (Ioc 0 1) volume := by
      rw [integrableOn_Ioc_iff_integrableOn_Ioo]
      exact (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 (by norm_num)
    refine Integrable.mono' (hbase.const_mul (25 : ℝ)) ?_ ?_
    · exact (measurable_burnolChiOne.pow_const 2).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : 0 < t := ht.1
      have ht1 : t ≤ 1 := ht.2
      have hquarter : 0 < t ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos ht0 _
      have hlogMul :=
        Real.abs_log_mul_self_rpow_lt t (1 / 4 : ℝ) ht0 ht1 (by norm_num)
      rw [abs_mul, abs_of_pos hquarter] at hlogMul
      have hlog : |Real.log t| < 4 * t ^ (-1 / 4 : ℝ) := by
        calc
          |Real.log t| < 4 / t ^ (1 / 4 : ℝ) := by
            apply (lt_div_iff₀ hquarter).2
            simpa using hlogMul
          _ = 4 * t ^ (-1 / 4 : ℝ) := by
            rw [show (-1 / 4 : ℝ) = -(1 / 4 : ℝ) by norm_num,
              Real.rpow_neg ht0.le, div_eq_mul_inv]
      have hpower : 1 ≤ t ^ (-1 / 4 : ℝ) :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht0 ht1 (by norm_num)
      have hchi : |burnolChiOne t| ≤ 5 * t ^ (-1 / 4 : ℝ) := by
        rw [burnolChiOne_eq_of_mem ht]
        calc
          |1 + Real.log t| ≤ |(1 : ℝ)| + |Real.log t| := abs_add_le _ _
          _ = 1 + |Real.log t| := by norm_num
          _ ≤ 5 * t ^ (-1 / 4 : ℝ) := by linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
      calc
        |burnolChiOne t| ^ 2 ≤ (5 * t ^ (-1 / 4 : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hchi 2
        _ = 25 * t ^ (-1 / 2 : ℝ) := by
          rw [mul_pow, show (5 : ℝ) ^ 2 = 25 by norm_num,
            ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
          norm_num
  · refine integrableOn_zero.congr_fun ?_ measurableSet_Ioi
    intro t ht
    change 0 = burnolChiOne t ^ 2
    rw [burnolChiOne_eq_zero_of_not_mem (fun hmem => (not_le_of_gt ht) hmem.2)]
    norm_num

/-- The explicit transformed target as a real `L2(0,infinity)` element. -/
def burnolChiOneRealL2 : positiveHalfLineL2 :=
  burnolChiOne_memLp_two_positiveHalfLine.toLp burnolChiOne

theorem burnolChiOneRealL2_coeFn :
    burnolChiOneRealL2 =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      burnolChiOne := by
  exact MemLp.coeFn_toLp burnolChiOne_memLp_two_positiveHalfLine

/-- The explicit transformed target as a complex `L2(0,infinity)` element. -/
def burnolChiOneL2 : positiveHalfLineComplexL2 :=
  baezDuarteOfRealLp burnolChiOneRealL2

theorem burnolChiOneL2_coeFn :
    burnolChiOneL2 =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun t => (burnolChiOne t : ℂ) := by
  filter_upwards [baezDuarteOfRealLp_coeFn burnolChiOneRealL2,
    burnolChiOneRealL2_coeFn] with t hcomplex hreal
  exact hcomplex.trans (congrArg Complex.ofReal hreal)

private theorem hasMellin_burnolLogOneIoc
    (s : ℂ) (hs : 0 < s.re) :
    HasMellin
      (fun t : ℝ => Real.log t •
        (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) t) s
      (-1 / s ^ 2) := by
  let f : ℝ → ℂ := (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ))
  have hfInt : IntegrableOn f (Ioi (0 : ℝ)) := by
    have hM := (hasMellin_one_Ioc (s := (1 : ℂ)) (by norm_num)).1
    rw [MellinConvergent] at hM
    simpa [f] using hM
  have hfTop : f =O[Filter.atTop]
      (fun x : ℝ => x ^ (-(s.re + 1))) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
    have hxnot : x ∉ Ioc (0 : ℝ) 1 := fun hmem => (not_le_of_gt hx) hmem.2
    simp [f, hxnot]
  have hfBot : f =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (-(0 : ℝ))) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨1, Filter.Eventually.of_forall fun x => ?_⟩
    by_cases hx : x ∈ Ioc (0 : ℝ) 1
    · simp [f, hx]
    · simp [f, hx]
  have hdiff := mellin_hasDerivAt_of_isBigO_rpow
    hfInt.locallyIntegrableOn hfTop (by linarith) hfBot hs
  have hsne : s ≠ 0 := by
    intro hzero
    rw [hzero, Complex.zero_re] at hs
    exact lt_irrefl 0 hs
  have hpos : ∀ᶠ z : ℂ in 𝓝 s, 0 < z.re :=
    Complex.continuous_re.tendsto s (Ioi_mem_nhds hs)
  have heq : (fun z : ℂ => mellin f z) =ᶠ[𝓝 s] fun z => z⁻¹ := by
    filter_upwards [hpos] with z hz
    simpa [f, one_div] using
      (hasMellin_one_Ioc (s := z) hz).2
  have hderInv : HasDerivAt (fun z : ℂ => z⁻¹) (-(s ^ 2)⁻¹) s :=
    hasDerivAt_inv hsne
  have hvalue : mellin (fun t : ℝ => Real.log t • f t) s = -(s ^ 2)⁻¹ :=
    hdiff.2.unique (hderInv.congr_of_eventuallyEq heq)
  constructor
  · simpa only [f] using hdiff.1
  · simpa only [f, neg_div, one_div] using hvalue

/-- Mellin transform of Burnol's explicit transformed target. -/
theorem hasMellin_burnolChiOne
    (s : ℂ) (hs : 0 < s.re) :
    HasMellin (fun t : ℝ => (burnolChiOne t : ℂ)) s
      ((s - 1) / s ^ 2) := by
  have honeSource := hasMellin_one_Ioc (s := s) hs
  have hlog := hasMellin_burnolLogOneIoc s hs
  have hadd := hasMellin_add honeSource.1 hlog.1
  have hsne : s ≠ 0 := by
    intro hzero
    rw [hzero, Complex.zero_re] at hs
    exact lt_irrefl 0 hs
  have hfun : (fun t : ℝ => (burnolChiOne t : ℂ)) =
      fun t => (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) t +
        Real.log t • (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) t := by
    funext t
    by_cases ht : t ∈ Ioc (0 : ℝ) 1
    · simp [burnolChiOne, ht]
    · simp [burnolChiOne, ht]
  rw [hfun]
  constructor
  · exact hadd.1
  · rw [hadd.2, honeSource.2, hlog.2]
    field_simp [hsne]
    ring

/-- Weighted logarithmic representative of the explicit transformed target. -/
def burnolChiOneWeightedLog (u : ℝ) : ℂ :=
  (Real.exp (-u / 2) : ℂ) * (burnolChiOne (Real.exp (-u)) : ℂ)

theorem burnolChiOneWeightedLog_ae_weightedLogForwardFun :
    burnolChiOneWeightedLog =ᵐ[volume]
      weightedLogForwardFun burnolChiOneL2 := by
  have hsource := expNeg_quasiMeasurePreserving.ae_eq burnolChiOneL2_coeFn
  filter_upwards [hsource] with u hu
  change burnolChiOneL2 (Real.exp (-u)) =
    (burnolChiOne (Real.exp (-u)) : ℂ) at hu
  simp only [burnolChiOneWeightedLog, weightedLogForwardFun, expNeg]
  rw [hu]

theorem burnolChiOneWeightedLog_memLp :
    MemLp burnolChiOneWeightedLog (2 : ℝ≥0∞) volume :=
  (weightedLogForwardFun_memLp burnolChiOneL2).ae_eq
    burnolChiOneWeightedLog_ae_weightedLogForwardFun.symm

theorem burnolChiOneWeightedLog_toLp :
    burnolChiOneWeightedLog_memLp.toLp burnolChiOneWeightedLog =
      weightedLogPullback burnolChiOneL2 := by
  rw [weightedLogPullback_apply]
  exact MemLp.toLp_congr burnolChiOneWeightedLog_memLp
    (weightedLogForwardFun_memLp burnolChiOneL2)
    burnolChiOneWeightedLog_ae_weightedLogForwardFun

theorem burnolChiOneWeightedLog_integrable :
    Integrable burnolChiOneWeightedLog := by
  have hM := hasMellin_burnolChiOne (1 / 2 : ℂ) (by norm_num)
  exact integrable_weightedLog_of_mellinConvergent hM.1

/-- Frequency representative of the transformed target. -/
def burnolChiOneTransform (xi : ℝ) : ℂ :=
  let s := burnolCriticalLineAtFrequency xi
  (s - 1) / s ^ 2

theorem fourier_burnolChiOneWeightedLog (xi : ℝ) :
    𝓕 burnolChiOneWeightedLog xi = burnolChiOneTransform xi := by
  let tau : ℝ := 2 * Real.pi * xi
  let s : ℂ := (1 / 2 : ℂ) + tau * Complex.I
  have hs : 0 < s.re := by dsimp only [s]; norm_num
  have hM := hasMellin_burnolChiOne s hs
  have hFourier := mellin_criticalLine_eq_fourier
    (fun t : ℝ => (burnolChiOne t : ℂ)) tau
  rw [hM.2] at hFourier
  have htau : tau / (2 * Real.pi) = xi := by
    dsimp only [tau]
    field_simp [Real.pi_ne_zero]
  rw [htau] at hFourier
  change 𝓕 (fun u : ℝ => (Real.exp (-u / 2) : ℂ) *
    (burnolChiOne (Real.exp (-u)) : ℂ)) xi = _
  rw [← hFourier]
  rfl

theorem burnolChiOneTransform_eq_phase_mul_target (xi : ℝ) :
    burnolChiOneTransform xi =
      burnolHardyInverseMultiplier xi * baezDuarteScaledTargetTransform xi := by
  have hsne := burnolCriticalLineAtFrequency_ne_zero xi
  rw [burnolChiOneTransform, burnolHardyInverseMultiplier,
    baezDuarteScaledTargetTransform]
  change (burnolCriticalLineAtFrequency xi - 1) /
      burnolCriticalLineAtFrequency xi ^ 2 =
    ((burnolCriticalLineAtFrequency xi - 1) /
      burnolCriticalLineAtFrequency xi) *
      (1 / burnolCriticalLineAtFrequency xi)
  field_simp [hsne]

theorem burnolChiOneTransform_memLp :
    MemLp burnolChiOneTransform (2 : ℝ≥0∞) volume := by
  have hprod : MemLp
      (fun xi => burnolHardyInverseMultiplier xi •
        baezDuarteScaledTargetTransform xi)
      (2 : ℝ≥0∞) volume :=
    baezDuarteScaledTargetTransform_memLp.smul
      burnolHardyInverseMultiplier_memLp_top
  refine hprod.ae_eq (ae_of_all volume fun xi => ?_)
  simp only [smul_eq_mul, burnolChiOneTransform_eq_phase_mul_target]

theorem baezDuarteFourierMellinL2_chiOne_eq :
    baezDuarteFourierMellinL2 burnolChiOneL2 =
      burnolChiOneTransform_memLp.toLp burnolChiOneTransform := by
  have hFourier2 : MemLp (𝓕 burnolChiOneWeightedLog)
      (2 : ℝ≥0∞) volume :=
    burnolChiOneTransform_memLp.ae_eq
      (ae_of_all volume fun xi => (fourier_burnolChiOneWeightedLog xi).symm)
  have hcompat := fourier_toLp_eq_toLp_fourier
    burnolChiOneWeightedLog_integrable burnolChiOneWeightedLog_memLp hFourier2
  rw [baezDuarteFourierMellinL2, LinearIsometryEquiv.trans_apply]
  rw [← burnolChiOneWeightedLog_toLp]
  calc
    _ = hFourier2.toLp (𝓕 burnolChiOneWeightedLog) := hcompat
    _ = _ := MemLp.toLp_congr hFourier2 burnolChiOneTransform_memLp
      (ae_of_all volume fun xi => fourier_burnolChiOneWeightedLog xi)

theorem burnolFrequencyPhaseL2_targetTransform :
    burnolFrequencyPhaseL2
        (baezDuarteScaledTargetTransform_memLp.toLp
          baezDuarteScaledTargetTransform) =
      burnolChiOneTransform_memLp.toLp burnolChiOneTransform := by
  rw [burnolFrequencyPhaseL2_apply]
  apply Lp.ext
  filter_upwards [Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞))
      burnolHardyInverseMultiplierLInf
      (baezDuarteScaledTargetTransform_memLp.toLp
        baezDuarteScaledTargetTransform),
    burnolHardyInverseMultiplierLInf_coeFn,
    MemLp.coeFn_toLp baezDuarteScaledTargetTransform_memLp,
    MemLp.coeFn_toLp burnolChiOneTransform_memLp] with
      xi hmul hphase htarget hchi
  rw [hmul, hchi]
  change burnolHardyInverseMultiplierLInf xi *
    (baezDuarteScaledTargetTransform_memLp.toLp
      baezDuarteScaledTargetTransform) xi = burnolChiOneTransform xi
  rw [hphase, htarget, burnolChiOneTransform_eq_phase_mul_target]

/-- Burnol's unitary sends the original indicator target to the explicit function `chi1`. -/
theorem burnolHardyInverseL2_target :
    burnolHardyInverseL2 baezDuarteComplexTargetL2 = burnolChiOneL2 := by
  apply baezDuarteFourierMellinL2.injective
  rw [baezDuarteFourierMellinL2_burnolHardyInverseL2,
    baezDuarteFourierMellinL2_target_eq,
    baezDuarteFourierMellinL2_chiOne_eq,
    burnolFrequencyPhaseL2_targetTransform]

/-! ## Explicit transformed kernels -/

theorem burnolA_memLp_two_volume :
    MemLp burnolA (2 : ℝ≥0∞) volume := by
  have hindicator : MemLp ((Ioi (0 : ℝ)).indicator burnolA)
      (2 : ℝ≥0∞) volume :=
    (memLp_indicator_iff_restrict measurableSet_Ioi).2
      burnolA_memLp_two_positiveHalfLine
  have heq : (Ioi (0 : ℝ)).indicator burnolA = burnolA := by
    funext t
    by_cases ht : 0 < t
    · simp [ht]
    · simp [ht, burnolA_eq_zero_of_nonpos (not_lt.mp ht)]
  rwa [heq] at hindicator

/-- The explicit unnormalized model kernel `A(t/theta)`. -/
def burnolModelKernel (theta : burnolContinuousParameter) (t : ℝ) : ℝ :=
  burnolA (t / (theta : ℝ))

theorem measurable_burnolModelKernel (theta : burnolContinuousParameter) :
    Measurable (burnolModelKernel theta) := by
  exact measurable_burnolA.comp (measurable_id.div measurable_const)

theorem burnolModelKernel_memLp_two_positiveHalfLine
    (theta : burnolContinuousParameter) :
    MemLp (burnolModelKernel theta) (2 : ℝ≥0∞)
      (volume.restrict (Ioi (0 : ℝ))) := by
  have hscaled := MemLp.comp_mul_left_volume burnolA_memLp_two_volume
    (inv_ne_zero theta.property.1.ne')
  have hrestricted := hscaled.restrict (Ioi (0 : ℝ))
  change MemLp (fun t : ℝ => burnolA (t / (theta : ℝ)))
    (2 : ℝ≥0∞) (volume.restrict (Ioi (0 : ℝ)))
  simpa only [div_eq_mul_inv, mul_comm] using hrestricted

/-- The explicit model kernel as a real `L2(0,infinity)` element. -/
def burnolModelKernelRealL2
    (theta : burnolContinuousParameter) : positiveHalfLineL2 :=
  (burnolModelKernel_memLp_two_positiveHalfLine theta).toLp
    (burnolModelKernel theta)

theorem burnolModelKernelRealL2_coeFn (theta : burnolContinuousParameter) :
    burnolModelKernelRealL2 theta =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      burnolModelKernel theta := by
  exact MemLp.coeFn_toLp (burnolModelKernel_memLp_two_positiveHalfLine theta)

/-- The explicit model kernel as a complex `L2(0,infinity)` element. -/
def burnolModelKernelL2
    (theta : burnolContinuousParameter) : positiveHalfLineComplexL2 :=
  baezDuarteOfRealLp (burnolModelKernelRealL2 theta)

theorem burnolModelKernelL2_coeFn (theta : burnolContinuousParameter) :
    burnolModelKernelL2 theta =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun t => (burnolA (t / (theta : ℝ)) : ℂ) := by
  filter_upwards [baezDuarteOfRealLp_coeFn (burnolModelKernelRealL2 theta),
    burnolModelKernelRealL2_coeFn theta] with t hcomplex hreal
  exact hcomplex.trans (congrArg Complex.ofReal hreal)

theorem burnolContinuousKernelL2_coeFn (theta : burnolContinuousParameter) :
    burnolContinuousKernelL2 theta =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun t => (fractionalPartKernel (theta : ℝ) t : ℂ) := by
  filter_upwards [baezDuarteOfRealLp_coeFn
      ((fractionalPartKernel_memLp_two_positiveHalfLine
        theta.property.1 theta.property.2).toLp
        (fractionalPartKernel (theta : ℝ))),
    MemLp.coeFn_toLp (fractionalPartKernel_memLp_two_positiveHalfLine
      theta.property.1 theta.property.2)] with t hcomplex hreal
  exact hcomplex.trans (congrArg Complex.ofReal hreal)

/-- The Mellin scaling factor generated by `t ↦ t/theta`. -/
def burnolDilationFactor (theta : burnolContinuousParameter) (s : ℂ) : ℂ :=
  ((((theta : ℝ)⁻¹ : ℝ) : ℂ) ^ (-s))

theorem hasMellin_burnolContinuousKernel
    (theta : burnolContinuousParameter) (s : ℂ)
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    HasMellin
      (fun t : ℝ => (fractionalPartKernel (theta : ℝ) t : ℂ)) s
      (burnolDilationFactor theta s * (-riemannZeta s / s)) := by
  have hfun :
      (fun t : ℝ => (fractionalPartKernel (theta : ℝ) t : ℂ)) =
        fun t : ℝ =>
          (fractionalPartKernel 1 ((theta : ℝ)⁻¹ * t) : ℂ) := by
    funext t
    simp [fractionalPartKernel, div_eq_mul_inv, mul_inv_rev,
      mul_comm]
  rw [hfun]
  constructor
  · rw [MellinConvergent.comp_mul_left
      (f := fun t : ℝ => (fractionalPartKernel 1 t : ℂ))
      (s := s) (a := (theta : ℝ)⁻¹) (inv_pos.mpr theta.property.1)]
    exact (hasMellin_fractionalPartKernel_one s hs0 hs1).1
  · rw [mellin_comp_mul_left
      (fun t : ℝ => (fractionalPartKernel 1 t : ℂ)) s
      (inv_pos.mpr theta.property.1),
      (hasMellin_fractionalPartKernel_one s hs0 hs1).2]
    rfl

theorem hasMellin_burnolModelKernel
    (theta : burnolContinuousParameter) (s : ℂ)
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    HasMellin (fun t : ℝ => (burnolModelKernel theta t : ℂ)) s
      (burnolDilationFactor theta s *
        ((s - 1) * riemannZeta s / s ^ 2)) := by
  have hfun : (fun t : ℝ => (burnolModelKernel theta t : ℂ)) =
      fun t : ℝ => (burnolA ((theta : ℝ)⁻¹ * t) : ℂ) := by
    funext t
    simp only [burnolModelKernel, div_eq_mul_inv, mul_comm]
  rw [hfun]
  constructor
  · rw [MellinConvergent.comp_mul_left
      (f := fun t : ℝ => (burnolA t : ℂ))
      (s := s) (a := (theta : ℝ)⁻¹) (inv_pos.mpr theta.property.1)]
    exact (hasMellin_burnolA s hs0 hs1).1
  · rw [mellin_comp_mul_left (fun t : ℝ => (burnolA t : ℂ)) s
      (inv_pos.mpr theta.property.1),
      (hasMellin_burnolA s hs0 hs1).2]
    rfl

/-- Weighted logarithmic representative of an original Burnol kernel. -/
def burnolContinuousKernelWeightedLog
    (theta : burnolContinuousParameter) (u : ℝ) : ℂ :=
  (Real.exp (-u / 2) : ℂ) *
    (fractionalPartKernel (theta : ℝ) (Real.exp (-u)) : ℂ)

theorem burnolContinuousKernelWeightedLog_ae_weightedLogForwardFun
    (theta : burnolContinuousParameter) :
    burnolContinuousKernelWeightedLog theta =ᵐ[volume]
      weightedLogForwardFun (burnolContinuousKernelL2 theta) := by
  have hsource := expNeg_quasiMeasurePreserving.ae_eq
    (burnolContinuousKernelL2_coeFn theta)
  filter_upwards [hsource] with u hu
  change burnolContinuousKernelL2 theta (Real.exp (-u)) =
    (fractionalPartKernel (theta : ℝ) (Real.exp (-u)) : ℂ) at hu
  simp only [burnolContinuousKernelWeightedLog, weightedLogForwardFun, expNeg]
  rw [hu]

theorem burnolContinuousKernelWeightedLog_memLp
    (theta : burnolContinuousParameter) :
    MemLp (burnolContinuousKernelWeightedLog theta)
      (2 : ℝ≥0∞) volume :=
  (weightedLogForwardFun_memLp (burnolContinuousKernelL2 theta)).ae_eq
    (burnolContinuousKernelWeightedLog_ae_weightedLogForwardFun theta).symm

theorem burnolContinuousKernelWeightedLog_toLp
    (theta : burnolContinuousParameter) :
    (burnolContinuousKernelWeightedLog_memLp theta).toLp
        (burnolContinuousKernelWeightedLog theta) =
      weightedLogPullback (burnolContinuousKernelL2 theta) := by
  rw [weightedLogPullback_apply]
  exact MemLp.toLp_congr (burnolContinuousKernelWeightedLog_memLp theta)
    (weightedLogForwardFun_memLp (burnolContinuousKernelL2 theta))
    (burnolContinuousKernelWeightedLog_ae_weightedLogForwardFun theta)

theorem burnolContinuousKernelWeightedLog_integrable
    (theta : burnolContinuousParameter) :
    Integrable (burnolContinuousKernelWeightedLog theta) := by
  have hM := hasMellin_burnolContinuousKernel theta (1 / 2 : ℂ)
    (by norm_num) (by norm_num)
  exact integrable_weightedLog_of_mellinConvergent hM.1

/-- Weighted logarithmic representative of the explicit model kernel. -/
def burnolModelKernelWeightedLog
    (theta : burnolContinuousParameter) (u : ℝ) : ℂ :=
  (Real.exp (-u / 2) : ℂ) *
    (burnolModelKernel theta (Real.exp (-u)) : ℂ)

theorem burnolModelKernelWeightedLog_ae_weightedLogForwardFun
    (theta : burnolContinuousParameter) :
    burnolModelKernelWeightedLog theta =ᵐ[volume]
      weightedLogForwardFun (burnolModelKernelL2 theta) := by
  have hsource := expNeg_quasiMeasurePreserving.ae_eq
    (burnolModelKernelL2_coeFn theta)
  filter_upwards [hsource] with u hu
  change burnolModelKernelL2 theta (Real.exp (-u)) =
    (burnolA (Real.exp (-u) / (theta : ℝ)) : ℂ) at hu
  simp only [burnolModelKernelWeightedLog, burnolModelKernel,
    weightedLogForwardFun, expNeg]
  rw [hu]

theorem burnolModelKernelWeightedLog_memLp
    (theta : burnolContinuousParameter) :
    MemLp (burnolModelKernelWeightedLog theta)
      (2 : ℝ≥0∞) volume :=
  (weightedLogForwardFun_memLp (burnolModelKernelL2 theta)).ae_eq
    (burnolModelKernelWeightedLog_ae_weightedLogForwardFun theta).symm

theorem burnolModelKernelWeightedLog_toLp
    (theta : burnolContinuousParameter) :
    (burnolModelKernelWeightedLog_memLp theta).toLp
        (burnolModelKernelWeightedLog theta) =
      weightedLogPullback (burnolModelKernelL2 theta) := by
  rw [weightedLogPullback_apply]
  exact MemLp.toLp_congr (burnolModelKernelWeightedLog_memLp theta)
    (weightedLogForwardFun_memLp (burnolModelKernelL2 theta))
    (burnolModelKernelWeightedLog_ae_weightedLogForwardFun theta)

theorem burnolModelKernelWeightedLog_integrable
    (theta : burnolContinuousParameter) :
    Integrable (burnolModelKernelWeightedLog theta) := by
  have hM := hasMellin_burnolModelKernel theta (1 / 2 : ℂ)
    (by norm_num) (by norm_num)
  exact integrable_weightedLog_of_mellinConvergent hM.1

/-- Frequency representative of an original Burnol kernel. -/
def burnolContinuousKernelTransform
    (theta : burnolContinuousParameter) (xi : ℝ) : ℂ :=
  let s := burnolCriticalLineAtFrequency xi
  burnolDilationFactor theta s * (-riemannZeta s / s)

/-- Frequency representative of an explicit model kernel. -/
def burnolModelKernelTransform
    (theta : burnolContinuousParameter) (xi : ℝ) : ℂ :=
  let s := burnolCriticalLineAtFrequency xi
  burnolDilationFactor theta s *
    ((s - 1) * riemannZeta s / s ^ 2)

theorem fourier_burnolContinuousKernelWeightedLog
    (theta : burnolContinuousParameter) (xi : ℝ) :
    𝓕 (burnolContinuousKernelWeightedLog theta) xi =
      burnolContinuousKernelTransform theta xi := by
  let tau : ℝ := 2 * Real.pi * xi
  let s : ℂ := (1 / 2 : ℂ) + tau * Complex.I
  have hs0 : 0 < s.re := by dsimp only [s]; norm_num
  have hs1 : s.re < 1 := by dsimp only [s]; norm_num
  have hM := hasMellin_burnolContinuousKernel theta s hs0 hs1
  have hFourier := mellin_criticalLine_eq_fourier
    (fun t : ℝ => (fractionalPartKernel (theta : ℝ) t : ℂ)) tau
  rw [hM.2] at hFourier
  have htau : tau / (2 * Real.pi) = xi := by
    dsimp only [tau]
    field_simp [Real.pi_ne_zero]
  rw [htau] at hFourier
  change 𝓕 (fun u : ℝ => (Real.exp (-u / 2) : ℂ) *
    (fractionalPartKernel (theta : ℝ) (Real.exp (-u)) : ℂ)) xi = _
  rw [← hFourier]
  rfl

theorem fourier_burnolModelKernelWeightedLog
    (theta : burnolContinuousParameter) (xi : ℝ) :
    𝓕 (burnolModelKernelWeightedLog theta) xi =
      burnolModelKernelTransform theta xi := by
  let tau : ℝ := 2 * Real.pi * xi
  let s : ℂ := (1 / 2 : ℂ) + tau * Complex.I
  have hs0 : 0 < s.re := by dsimp only [s]; norm_num
  have hs1 : s.re < 1 := by dsimp only [s]; norm_num
  have hM := hasMellin_burnolModelKernel theta s hs0 hs1
  have hFourier := mellin_criticalLine_eq_fourier
    (fun t : ℝ => (burnolModelKernel theta t : ℂ)) tau
  rw [hM.2] at hFourier
  have htau : tau / (2 * Real.pi) = xi := by
    dsimp only [tau]
    field_simp [Real.pi_ne_zero]
  rw [htau] at hFourier
  change 𝓕 (fun u : ℝ => (Real.exp (-u / 2) : ℂ) *
    (burnolModelKernel theta (Real.exp (-u)) : ℂ)) xi = _
  rw [← hFourier]
  rfl

theorem burnol_phase_mul_continuousKernelTransform
    (theta : burnolContinuousParameter) (xi : ℝ) :
    burnolHardyInverseMultiplier xi *
        burnolContinuousKernelTransform theta xi =
      -burnolModelKernelTransform theta xi := by
  have hsne := burnolCriticalLineAtFrequency_ne_zero xi
  rw [burnolHardyInverseMultiplier, burnolContinuousKernelTransform,
    burnolModelKernelTransform]
  field_simp [hsne]

theorem norm_burnolDilationFactor_atFrequency
    (theta : burnolContinuousParameter) (xi : ℝ) :
    ‖burnolDilationFactor theta (burnolCriticalLineAtFrequency xi)‖ =
      ((theta : ℝ)⁻¹) ^ (-1 / 2 : ℝ) := by
  rw [burnolDilationFactor,
    Complex.norm_cpow_eq_rpow_re_of_pos (inv_pos.mpr theta.property.1)]
  congr 1
  norm_num [burnolCriticalLineAtFrequency]

theorem continuous_burnolContinuousKernelTransform
    (theta : burnolContinuousParameter) :
    Continuous (burnolContinuousKernelTransform theta) := by
  rw [← funext (fourier_burnolContinuousKernelWeightedLog theta)]
  change Continuous (VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ)
    (burnolContinuousKernelWeightedLog theta))
  exact VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar continuous_inner
    (burnolContinuousKernelWeightedLog_integrable theta)

theorem continuous_burnolModelKernelTransform
    (theta : burnolContinuousParameter) :
    Continuous (burnolModelKernelTransform theta) := by
  rw [← funext (fourier_burnolModelKernelWeightedLog theta)]
  change Continuous (VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ)
    (burnolModelKernelWeightedLog theta))
  exact VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar continuous_inner
    (burnolModelKernelWeightedLog_integrable theta)

theorem burnolContinuousKernelTransform_memLp
    (theta : burnolContinuousParameter) :
    MemLp (burnolContinuousKernelTransform theta)
      (2 : ℝ≥0∞) volume := by
  obtain ⟨C, hC, hquotient⟩ :=
    exists_norm_riemannZeta_div_criticalLine_le_rpow
  let D : ℝ := ((theta : ℝ)⁻¹) ^ (-1 / 2 : ℝ) * C
  have hfactor : 0 < ((theta : ℝ)⁻¹) ^ (-1 / 2 : ℝ) :=
    Real.rpow_pos_of_pos (inv_pos.mpr theta.property.1) _
  have hD : 0 ≤ D := (mul_pos hfactor hC).le
  have hmajor := (baezDuarteScaledMajorant_memLp (η := 0) (by norm_num)).const_smul
    (D : ℂ)
  refine hmajor.of_le
    (continuous_burnolContinuousKernelTransform theta).aestronglyMeasurable
    (ae_of_all volume fun xi => ?_)
  rw [Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hD]
  have hquotientXi := hquotient (2 * Real.pi * xi)
  have hmajorNorm :
      ‖baezDuarteScaledMajorant 0 xi‖ =
        (1 + |2 * Real.pi * xi|) ^ (-5 / 8 : ℝ) := by
    rw [baezDuarteScaledMajorant,
      norm_baezDuarteVerticalMajorant_three_eighths_add]
    norm_num
  rw [burnolContinuousKernelTransform, norm_mul, norm_div, norm_neg,
    norm_burnolDilationFactor_atFrequency, hmajorNorm]
  rw [norm_div] at hquotientXi
  change ((theta : ℝ)⁻¹) ^ (-1 / 2 : ℝ) *
      (‖riemannZeta ((1 / 2 : ℂ) +
          ((2 * Real.pi * xi : ℝ) : ℂ) * Complex.I)‖ /
        ‖(1 / 2 : ℂ) + ((2 * Real.pi * xi : ℝ) : ℂ) * Complex.I‖) ≤
    ((theta : ℝ)⁻¹) ^ (-1 / 2 : ℝ) * C *
      (1 + |2 * Real.pi * xi|) ^ (-5 / 8 : ℝ)
  calc
    _ ≤ ((theta : ℝ)⁻¹) ^ (-1 / 2 : ℝ) *
        (C * (1 + |2 * Real.pi * xi|) ^ (-5 / 8 : ℝ)) :=
      mul_le_mul_of_nonneg_left hquotientXi hfactor.le
    _ = _ := by ring

theorem burnolModelKernelTransform_memLp
    (theta : burnolContinuousParameter) :
    MemLp (burnolModelKernelTransform theta)
      (2 : ℝ≥0∞) volume := by
  have hprod : MemLp
      (fun xi => burnolHardyInverseMultiplier xi •
        burnolContinuousKernelTransform theta xi)
      (2 : ℝ≥0∞) volume :=
    (burnolContinuousKernelTransform_memLp theta).smul
      burnolHardyInverseMultiplier_memLp_top
  have hneg := hprod.neg
  refine hneg.ae_eq (ae_of_all volume fun xi => ?_)
  have hphase := burnol_phase_mul_continuousKernelTransform theta xi
  simpa only [Pi.neg_apply, smul_eq_mul, neg_neg] using congrArg Neg.neg hphase

theorem baezDuarteFourierMellinL2_continuousKernel_eq
    (theta : burnolContinuousParameter) :
    baezDuarteFourierMellinL2 (burnolContinuousKernelL2 theta) =
      (burnolContinuousKernelTransform_memLp theta).toLp
        (burnolContinuousKernelTransform theta) := by
  have hFourier2 : MemLp (𝓕 (burnolContinuousKernelWeightedLog theta))
      (2 : ℝ≥0∞) volume :=
    (burnolContinuousKernelTransform_memLp theta).ae_eq
      (ae_of_all volume fun xi =>
        (fourier_burnolContinuousKernelWeightedLog theta xi).symm)
  have hcompat := fourier_toLp_eq_toLp_fourier
    (burnolContinuousKernelWeightedLog_integrable theta)
    (burnolContinuousKernelWeightedLog_memLp theta) hFourier2
  rw [baezDuarteFourierMellinL2, LinearIsometryEquiv.trans_apply]
  rw [← burnolContinuousKernelWeightedLog_toLp theta]
  calc
    _ = hFourier2.toLp (𝓕 (burnolContinuousKernelWeightedLog theta)) := hcompat
    _ = _ := MemLp.toLp_congr hFourier2
      (burnolContinuousKernelTransform_memLp theta)
      (ae_of_all volume fun xi =>
        fourier_burnolContinuousKernelWeightedLog theta xi)

theorem baezDuarteFourierMellinL2_modelKernel_eq
    (theta : burnolContinuousParameter) :
    baezDuarteFourierMellinL2 (burnolModelKernelL2 theta) =
      (burnolModelKernelTransform_memLp theta).toLp
        (burnolModelKernelTransform theta) := by
  have hFourier2 : MemLp (𝓕 (burnolModelKernelWeightedLog theta))
      (2 : ℝ≥0∞) volume :=
    (burnolModelKernelTransform_memLp theta).ae_eq
      (ae_of_all volume fun xi =>
        (fourier_burnolModelKernelWeightedLog theta xi).symm)
  have hcompat := fourier_toLp_eq_toLp_fourier
    (burnolModelKernelWeightedLog_integrable theta)
    (burnolModelKernelWeightedLog_memLp theta) hFourier2
  rw [baezDuarteFourierMellinL2, LinearIsometryEquiv.trans_apply]
  rw [← burnolModelKernelWeightedLog_toLp theta]
  calc
    _ = hFourier2.toLp (𝓕 (burnolModelKernelWeightedLog theta)) := hcompat
    _ = _ := MemLp.toLp_congr hFourier2
      (burnolModelKernelTransform_memLp theta)
      (ae_of_all volume fun xi => fourier_burnolModelKernelWeightedLog theta xi)

theorem burnolFrequencyPhaseL2_continuousKernelTransform
    (theta : burnolContinuousParameter) :
    burnolFrequencyPhaseL2
        ((burnolContinuousKernelTransform_memLp theta).toLp
          (burnolContinuousKernelTransform theta)) =
      -((burnolModelKernelTransform_memLp theta).toLp
          (burnolModelKernelTransform theta)) := by
  rw [burnolFrequencyPhaseL2_apply]
  apply Lp.ext
  filter_upwards [Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞))
      burnolHardyInverseMultiplierLInf
      ((burnolContinuousKernelTransform_memLp theta).toLp
        (burnolContinuousKernelTransform theta)),
    burnolHardyInverseMultiplierLInf_coeFn,
    MemLp.coeFn_toLp (burnolContinuousKernelTransform_memLp theta),
    Lp.coeFn_neg ((burnolModelKernelTransform_memLp theta).toLp
      (burnolModelKernelTransform theta)),
    MemLp.coeFn_toLp (burnolModelKernelTransform_memLp theta)] with
      xi hmul hphase horiginal hneg hmodel
  rw [hmul, hneg]
  change burnolHardyInverseMultiplierLInf xi *
      ((burnolContinuousKernelTransform_memLp theta).toLp
        (burnolContinuousKernelTransform theta)) xi =
    -((burnolModelKernelTransform_memLp theta).toLp
      (burnolModelKernelTransform theta)) xi
  rw [hphase, horiginal, hmodel,
    burnol_phase_mul_continuousKernelTransform]

/-- Burnol's unitary sends every original kernel to minus the explicit dilate `A(t/theta)`. -/
theorem burnolHardyInverseL2_kernel
    (theta : burnolContinuousParameter) :
    burnolHardyInverseL2 (burnolContinuousKernelL2 theta) =
      -burnolModelKernelL2 theta := by
  apply baezDuarteFourierMellinL2.injective
  rw [baezDuarteFourierMellinL2_burnolHardyInverseL2,
    baezDuarteFourierMellinL2_continuousKernel_eq,
    map_neg, baezDuarteFourierMellinL2_modelKernel_eq,
    burnolFrequencyPhaseL2_continuousKernelTransform]

/-! ## Span transport and distance equality -/

/-- Explicit model kernels with source cutoff `cutoff <= theta <= 1`. -/
def burnolModelKernelSet (cutoff : ℝ) : Set positiveHalfLineComplexL2 :=
  burnolModelKernelL2 ''
    {theta : burnolContinuousParameter | cutoff ≤ (theta : ℝ)}

/-- Burnol's explicit model space `C_cutoff`, generated by the functions `A(t/theta)`. -/
def burnolModelKernelSpan (cutoff : ℝ) :
    Submodule ℂ positiveHalfLineComplexL2 :=
  Submodule.span ℂ (burnolModelKernelSet cutoff)

theorem burnolHardyInverseL2_map_kernelSpan (cutoff : ℝ) :
    (burnolKernelSpan cutoff).map burnolHardyInverseL2.toLinearMap =
      burnolModelKernelSpan cutoff := by
  apply le_antisymm
  · rw [burnolKernelSpan, Submodule.map_span]
    apply Submodule.span_le.2
    rintro y ⟨x, hx, rfl⟩
    rcases hx with ⟨theta, htheta, rfl⟩
    change burnolHardyInverseL2 (burnolContinuousKernelL2 theta) ∈
      burnolModelKernelSpan cutoff
    rw [burnolHardyInverseL2_kernel]
    exact (burnolModelKernelSpan cutoff).neg_mem
      (Submodule.subset_span
        (show burnolModelKernelL2 theta ∈ burnolModelKernelSet cutoff from
          ⟨theta, htheta, rfl⟩))
  · rw [burnolModelKernelSpan]
    apply Submodule.span_le.2
    rintro y ⟨theta, htheta, rfl⟩
    have hsource : burnolContinuousKernelL2 theta ∈ burnolKernelSpan cutoff :=
      Submodule.subset_span
        (show burnolContinuousKernelL2 theta ∈ burnolKernelSet cutoff from
          ⟨theta, htheta, rfl⟩)
    refine ⟨-burnolContinuousKernelL2 theta,
      (burnolKernelSpan cutoff).neg_mem hsource, ?_⟩
    rw [map_neg]
    change -burnolHardyInverseL2 (burnolContinuousKernelL2 theta) =
      burnolModelKernelL2 theta
    rw [burnolHardyInverseL2_kernel, neg_neg]

/-- Distance from the explicit transformed target to Burnol's explicit model space. -/
def burnolModelDistance (cutoff : ℝ) : ℝ :=
  infDist burnolChiOneL2
    (burnolModelKernelSpan cutoff : Set positiveHalfLineComplexL2)

/-- Burnol's original and explicit transformed approximation distances are exactly equal. -/
theorem burnolDistance_eq_modelDistance (cutoff : ℝ) :
    burnolDistance cutoff = burnolModelDistance cutoff := by
  rw [burnolDistance, burnolModelDistance,
    ← burnolHardyInverseL2_target,
    ← burnolHardyInverseL2_map_kernelSpan,
    Submodule.map_coe]
  exact (Metric.infDist_image burnolHardyInverseL2.isometry).symm

end LeanLab.Riemann
