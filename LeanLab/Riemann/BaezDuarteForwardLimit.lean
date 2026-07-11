import LeanLab.Riemann.BaezDuarteForward
import LeanLab.Riemann.BaezDuarteZetaRatio
import LeanLab.Riemann.ReciprocalZetaSubpower

set_option linter.style.header false

/-!
# The epsilon-to-zero passage in the Baez-Duarte forward criterion
-/

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal FourierTransform

namespace LeanLab.Riemann

/-- The RH logarithm-branch estimate also gives the zeta, rather than reciprocal-zeta,
subpower bound on every fixed line strictly right of the critical line. -/
theorem RiemannHypothesis.exists_norm_riemannZeta_half_add_delta_le_rpow
    (hRH : RiemannHypothesis) {δ η : ℝ} (hδ : 0 < δ)
    (hδ_top : δ ≤ 1 / 4) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖riemannZeta ((1 / 2 : ℂ) + δ + t * Complex.I)‖ ≤
        C * (1 + |t|) ^ η := by
  let θ := reciprocalZetaThreeCirclesMaxExponent δ
  let K := 2 * (160 / δ) ^ θ
  obtain ⟨hθ_nonneg, hθ_lt_one, hbranch⟩ :=
    RiemannHypothesis.exists_logBranch_log_rpow_bound hRH hδ (hδ_top.trans (by norm_num))
  have hevent := eventually_const_mul_rpow_le_mul_self
    (K := K) hθ_lt_one hη
  rw [eventually_atTop] at hevent
  obtain ⟨A, hA⟩ := hevent
  have hlarge : ∀ t : ℝ, 5 ≤ |t| → A ≤ Real.log (2 + |t|) →
      ‖riemannZeta ((1 / 2 : ℂ) + δ + t * Complex.I)‖ ≤
        (2 + |t|) ^ η := by
    intro t ht hlog
    let s : ℂ := (1 / 2 : ℂ) + δ + t * Complex.I
    obtain ⟨f, _hf_diff, hf_exp, hf_bound⟩ := hbranch t ht
    have hsre_eq : s.re = (1 / 2 : ℝ) + δ := by simp [s]
    have hsim_eq : s.im = t := by simp [s]
    have hsre : s.re ∈ Set.Icc (1 / 2 + δ : ℝ) 3 := by
      rw [hsre_eq]
      constructor <;> linarith [hδ_top]
    have hs_mem : s ∈ Metric.ball (reciprocalZetaBorelCenter t)
        (reciprocalZetaBorelOuterRadius (δ / 2)) := by
      rw [Metric.mem_ball, dist_eq_norm]
      have hrho := norm_sub_reciprocalZetaBorelCenter_eq (s := s) hsim_eq hsre.2
      rw [hrho]
      dsimp only [reciprocalZetaBorelOuterRadius]
      linarith [hsre.1]
    have hexp : Complex.exp (f s) = riemannZeta s := by
      simpa only [Function.comp_apply] using hf_exp hs_mem
    have hf := hf_bound s hsim_eq hsre
    have hsublinear : K * (Real.log (2 + |t|)) ^ θ ≤
        η * Real.log (2 + |t|) := hA _ hlog
    have hfη : ‖f s‖ ≤ η * Real.log (2 + |t|) := by
      exact hf.trans (by simpa only [K, θ] using hsublinear)
    have hre : (f s).re ≤ ‖f s‖ := Complex.re_le_norm _
    have hheight : 0 < 2 + |t| := by positivity
    change ‖riemannZeta s‖ ≤ (2 + |t|) ^ η
    calc
      ‖riemannZeta s‖ = Real.exp (f s).re := by rw [← hexp, Complex.norm_exp]
      _ ≤ Real.exp ‖f s‖ := Real.exp_le_exp.mpr hre
      _ ≤ Real.exp (η * Real.log (2 + |t|)) := Real.exp_le_exp.mpr hfη
      _ = (2 + |t|) ^ η := by
        rw [Real.rpow_def_of_pos hheight]
        congr 1
        ring
  let T : ℝ := max 5 (Real.exp A)
  let line : ℝ → ℂ := fun t => (1 / 2 : ℂ) + δ + t * Complex.I
  have hT_pos : 0 < T := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hline_ne (t : ℝ) : line t ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    have hre' : (1 / 2 : ℝ) + δ = 1 := by simpa [line] using hre
    linarith [hδ_top, hre']
  have hcontinuous : ContinuousOn (fun t : ℝ => ‖riemannZeta (line t)‖) (Set.Icc (-T) T) := by
    intro t _ht
    exact ((differentiableAt_riemannZeta (hline_ne t)).continuousAt.comp
      (by fun_prop : ContinuousAt line t)).norm.continuousWithinAt
  obtain ⟨M, hM⟩ := bddAbove_def.mp
    (isCompact_Icc.bddAbove_image hcontinuous)
  let C : ℝ := max (2 ^ η) M
  have htwo_pos : 0 < (2 : ℝ) ^ η := Real.rpow_pos_of_pos (by norm_num) _
  have hC : 0 < C := htwo_pos.trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro t
  have hpower_one : 1 ≤ (1 + |t|) ^ η :=
    Real.one_le_rpow (by linarith [abs_nonneg t]) hη.le
  by_cases htlarge : T ≤ |t|
  · have ht : 5 ≤ |t| := (le_max_left _ _).trans htlarge
    have hexpA : Real.exp A ≤ 2 + |t| :=
      (le_max_right _ _).trans htlarge |>.trans (by linarith)
    have hlog : A ≤ Real.log (2 + |t|) := by
      rw [← Real.exp_le_exp, Real.exp_log (by positivity)]
      exact hexpA
    have h := hlarge t ht hlog
    have hbase : 2 + |t| ≤ 2 * (1 + |t|) := by linarith [abs_nonneg t]
    calc
      ‖riemannZeta (line t)‖ ≤ (2 + |t|) ^ η := by simpa only [line] using h
      _ ≤ (2 * (1 + |t|)) ^ η := Real.rpow_le_rpow (by positivity) hbase hη.le
      _ = 2 ^ η * (1 + |t|) ^ η := Real.mul_rpow (by norm_num) (by positivity)
      _ ≤ C * (1 + |t|) ^ η :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by positivity) _)
  · have htmem : t ∈ Set.Icc (-T) T := by
      have ht : |t| < T := lt_of_not_ge htlarge
      exact ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
    have hlocal : ‖riemannZeta (line t)‖ ≤ M := hM _ ⟨t, htmem, rfl⟩
    exact (hlocal.trans (le_max_right _ _)).trans
      (le_mul_of_one_le_right hC.le hpower_one)

/-- Multiplying a positive-natural Nyman--Beurling kernel by the source weight
`x ^ (-epsilon)` preserves square-integrability while `epsilon < 1 / 2`. -/
theorem weighted_fractionalPartKernel_memLp_two_positiveHalfLine
    {ε a : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1 / 2)
    (ha0 : 0 < a) (ha1 : a ≤ 1) :
    MemLp (fun x : ℝ => x ^ (-ε) * fractionalPartKernel a x) (2 : ℝ≥0∞)
      (volume.restrict (Ioi (0 : ℝ))) := by
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => x ^ (-ε) * fractionalPartKernel a x)
      (volume.restrict (Ioi (0 : ℝ))) := by
    have hrpow : Measurable (fun x : ℝ => x ^ (-ε)) :=
      measurable_of_continuousOn_compl_singleton (0 : ℝ)
        (continuousOn_id.rpow_const fun x hx => Or.inl hx)
    exact (hrpow.mul (measurable_fractionalPartKernel a)).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hmeas]
  change IntegrableOn
    (fun x : ℝ => (x ^ (-ε) * fractionalPartKernel a x) ^ 2)
    (Ioi (0 : ℝ)) volume
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  apply IntegrableOn.union
  · have hbase : IntegrableOn (fun x : ℝ => x ^ (-2 * ε)) (Ioc 0 1) volume := by
      rw [integrableOn_Ioc_iff_integrableOn_Ioo]
      exact (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 (by linarith)
    refine Integrable.mono' hbase ?_ ?_
    · have hrpow : Measurable (fun x : ℝ => x ^ (-ε)) :=
        measurable_of_continuousOn_compl_singleton (0 : ℝ)
          (continuousOn_id.rpow_const fun x hx => Or.inl hx)
      exact ((hrpow.mul (measurable_fractionalPartKernel a)).pow_const 2).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      have hx0 : 0 < x := hx.1
      have hk := norm_fractionalPartKernel_le_one a x
      rw [Real.norm_eq_abs, abs_pow, abs_mul,
        abs_of_pos (Real.rpow_pos_of_pos hx0 _)]
      have hw_nonneg : 0 ≤ x ^ (-ε) := (Real.rpow_pos_of_pos hx0 _).le
      have hk_nonneg : 0 ≤ |fractionalPartKernel a x| := abs_nonneg _
      calc
        (x ^ (-ε) * |fractionalPartKernel a x|) ^ 2 ≤
            (x ^ (-ε) * 1) ^ 2 := by
          exact pow_le_pow_left₀ (mul_nonneg hw_nonneg hk_nonneg)
            (mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hk) hw_nonneg) 2
        _ = x ^ (-2 * ε) := by
          rw [mul_one, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
          congr 1
          ring
  · have hbase : IntegrableOn (fun x : ℝ => x ^ (-2 - 2 * ε)) (Ioi 1) volume :=
      integrableOn_Ioi_rpow_of_lt (a := -2 - 2 * ε) (c := 1)
        (by nlinarith) (by norm_num)
    have hscaled : IntegrableOn
        (fun x : ℝ => a ^ 2 * x ^ (-2 - 2 * ε)) (Ioi 1) volume :=
      hbase.const_mul (a ^ 2)
    refine hscaled.congr_fun ?_ measurableSet_Ioi
    intro x hx
    change a ^ 2 * x ^ (-2 - 2 * ε) =
      (x ^ (-ε) * fractionalPartKernel a x) ^ 2
    have hx0 : 0 < x := zero_lt_one.trans hx
    have hfract : fractionalPartKernel a x = a / x := by
      rw [fractionalPartKernel, Int.fract_eq_self.mpr]
      exact ⟨(div_pos ha0 hx0).le,
        (div_lt_one hx0).mpr (ha1.trans_lt hx)⟩
    rw [hfract]
    rw [div_eq_mul_inv]
    have hinv : x⁻¹ ^ 2 = x ^ (-2 : ℝ) := by
      rw [Real.rpow_neg hx0.le]
      exact (inv_pow x 2).trans
        (congrArg Inv.inv (Real.rpow_natCast x 2).symm)
    have hweight : (x ^ (-ε)) ^ 2 = x ^ (-2 * ε) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      congr 1
      ring
    simp only [mul_pow]
    rw [hinv, hweight]
    have hcombine : x ^ (-2 * ε) * x ^ (-2 : ℝ) =
        x ^ (-2 - 2 * ε) := by
      rw [← Real.rpow_add hx0]
      congr 1
      ring
    rw [← hcombine]
    ring

/-- The finite source approximation after applying Baez-Duarte's physical-space
weight `X_epsilon`. -/
def baezDuarteWeightedMobiusApprox (ε : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  x ^ (-ε) * baezDuarteMobiusApprox (2 * ε) N x

theorem baezDuarteWeightedMobiusApprox_memLp
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1 / 2) (N : ℕ) :
    MemLp (baezDuarteWeightedMobiusApprox ε N) (2 : ℝ≥0∞)
      (volume.restrict (Ioi (0 : ℝ))) := by
  classical
  change MemLp
    (fun x : ℝ => x ^ (-ε) *
      ∑ a ∈ Finset.Icc 1 N,
        ((ArithmeticFunction.moebius a : ℤ) : ℝ) * (a : ℝ) ^ (-(2 * ε)) *
          fractionalPartKernel ((a : ℝ)⁻¹) x)
    (2 : ℝ≥0∞) (volume.restrict (Ioi (0 : ℝ)))
  simp_rw [Finset.mul_sum]
  apply memLp_finsetSum
  intro a ha
  have ha_pos : 0 < a := (Finset.mem_Icc.mp ha).1
  have ha_one_real : (1 : ℝ) ≤ a := by exact_mod_cast (Finset.mem_Icc.mp ha).1
  have hk := weighted_fractionalPartKernel_memLp_two_positiveHalfLine
    hε0 hε1 (inv_pos.mpr (by exact_mod_cast ha_pos))
    (inv_le_one_of_one_le₀ ha_one_real)
  convert hk.const_smul
      (((ArithmeticFunction.moebius a : ℤ) : ℝ) * (a : ℝ) ^ (-(2 * ε))) using 1
  funext x
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- The weighted finite source approximation as a real `L²(0,infinity)` element. -/
def baezDuarteWeightedMobiusApproxL2
    (ε : ℝ) (N : ℕ) (hε0 : 0 ≤ ε) (hε1 : ε < 1 / 2) : positiveHalfLineL2 :=
  (baezDuarteWeightedMobiusApprox_memLp hε0 hε1 N).toLp
    (baezDuarteWeightedMobiusApprox ε N)

theorem baezDuarteWeightedMobiusApproxL2_coeFn
    (ε : ℝ) (N : ℕ) (hε0 : 0 ≤ ε) (hε1 : ε < 1 / 2) :
    baezDuarteWeightedMobiusApproxL2 ε N hε0 hε1
      =ᵐ[volume.restrict (Ioi (0 : ℝ))]
        baezDuarteWeightedMobiusApprox ε N :=
  MemLp.coeFn_toLp (baezDuarteWeightedMobiusApprox_memLp hε0 hε1 N)

/-- Weight shifting in the Mellin transform gives the finite formula (2.7) before
specializing to the critical line. -/
theorem hasMellin_baezDuarteWeightedMobiusApprox
    (ε : ℝ) (N : ℕ) (s : ℂ)
    (hs0 : 0 < (s - ε).re) (hs1 : (s - ε).re < 1) :
    HasMellin
      (fun x : ℝ => (baezDuarteWeightedMobiusApprox ε N x : ℂ)) s
      ((-riemannZeta (s - ε) / (s - ε)) *
        mobiusDirichletPartialSum N (s + ε)) := by
  let f : ℝ → ℂ := fun x => (baezDuarteMobiusApprox (2 * ε) N x : ℂ)
  let g : ℝ → ℂ := fun x => (x : ℂ) ^ (-(ε : ℂ)) * f x
  have hM := hasMellin_baezDuarteMobiusApprox (2 * ε) N (s - ε) hs0 hs1
  have hshift : (s - ε) + ((2 * ε : ℝ) : ℂ) = s + ε := by
    push_cast
    ring
  rw [hshift] at hM
  have hgconv : MellinConvergent g s := by
    change MellinConvergent
      (fun x : ℝ => (x : ℂ) ^ (-(ε : ℂ)) * f x) s
    apply MellinConvergent.cpow_smul.mpr
    simpa only [sub_eq_add_neg] using hM.1
  have hgf : ∀ x ∈ Ioi (0 : ℝ),
      g x = (baezDuarteWeightedMobiusApprox ε N x : ℂ) := by
    intro x hx
    change (x : ℂ) ^ (-(ε : ℂ)) *
      (baezDuarteMobiusApprox (2 * ε) N x : ℂ) = _
    rw [baezDuarteWeightedMobiusApprox]
    rw [Complex.ofReal_mul, Complex.ofReal_cpow hx.le]
    simp only [Complex.ofReal_neg]
  have hconv : MellinConvergent
      (fun x : ℝ => (baezDuarteWeightedMobiusApprox ε N x : ℂ)) s := by
    rw [MellinConvergent]
    rw [MellinConvergent] at hgconv
    refine hgconv.congr_fun ?_ measurableSet_Ioi
    intro x hx
    change (x : ℂ) ^ (s - 1) • g x =
      (x : ℂ) ^ (s - 1) •
        (baezDuarteWeightedMobiusApprox ε N x : ℂ)
    rw [hgf x hx]
  refine ⟨hconv, ?_⟩
  calc
    mellin (fun x : ℝ => (baezDuarteWeightedMobiusApprox ε N x : ℂ)) s =
        mellin g s := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      change (x : ℂ) ^ (s - 1) •
          (baezDuarteWeightedMobiusApprox ε N x : ℂ) =
        (x : ℂ) ^ (s - 1) • g x
      rw [hgf x hx]
    _ = mellin f (s + (-(ε : ℂ))) := by
      exact mellin_cpow_smul f s (-(ε : ℂ))
    _ = mellin f (s - ε) := by
      congr 2
    _ = (-riemannZeta (s - ε) / (s - ε)) *
        mobiusDirichletPartialSum N (s + ε) := by
      simpa [f] using hM.2

/-- The weighted finite approximation in complex `L²(0,infinity)`. -/
def baezDuarteWeightedMobiusApproxComplexL2
    (ε : ℝ) (N : ℕ) (hε0 : 0 ≤ ε) (hε1 : ε < 1 / 2) :
    positiveHalfLineComplexL2 :=
  baezDuarteOfRealLp (baezDuarteWeightedMobiusApproxL2 ε N hε0 hε1)

theorem baezDuarteWeightedMobiusApproxComplexL2_coeFn
    (ε : ℝ) (N : ℕ) (hε0 : 0 ≤ ε) (hε1 : ε < 1 / 2) :
    baezDuarteWeightedMobiusApproxComplexL2 ε N hε0 hε1
      =ᵐ[volume.restrict (Ioi (0 : ℝ))]
        fun x : ℝ => (baezDuarteWeightedMobiusApprox ε N x : ℂ) := by
  filter_upwards [
    baezDuarteOfRealLp_coeFn (baezDuarteWeightedMobiusApproxL2 ε N hε0 hε1),
    baezDuarteWeightedMobiusApproxL2_coeFn ε N hε0 hε1] with x hc hr
  rw [baezDuarteWeightedMobiusApproxComplexL2, hc, hr]

/-- A concrete logarithmic representative of the weighted finite approximation. -/
def baezDuarteWeightedMobiusLog (ε : ℝ) (N : ℕ) (u : ℝ) : ℂ :=
  (Real.exp (-u / 2) : ℂ) *
    baezDuarteWeightedMobiusApprox ε N (Real.exp (-u))

theorem baezDuarteWeightedMobiusLog_ae_weightedLogForwardFun
    (ε : ℝ) (N : ℕ) (hε0 : 0 ≤ ε) (hε1 : ε < 1 / 2) :
    baezDuarteWeightedMobiusLog ε N =ᵐ[volume]
      weightedLogForwardFun
        (baezDuarteWeightedMobiusApproxComplexL2 ε N hε0 hε1) := by
  have hsource := expNeg_quasiMeasurePreserving.ae_eq
    (baezDuarteWeightedMobiusApproxComplexL2_coeFn ε N hε0 hε1)
  filter_upwards [hsource] with u hu
  change baezDuarteWeightedMobiusApproxComplexL2 ε N hε0 hε1
      (Real.exp (-u)) =
    (baezDuarteWeightedMobiusApprox ε N (Real.exp (-u)) : ℂ) at hu
  simp only [baezDuarteWeightedMobiusLog, weightedLogForwardFun, expNeg]
  rw [hu]

theorem baezDuarteWeightedMobiusLog_memLp
    (ε : ℝ) (N : ℕ) (hε0 : 0 ≤ ε) (hε1 : ε < 1 / 2) :
    MemLp (baezDuarteWeightedMobiusLog ε N) (2 : ℝ≥0∞) volume :=
  (weightedLogForwardFun_memLp
    (baezDuarteWeightedMobiusApproxComplexL2 ε N hε0 hε1)).ae_eq
      (baezDuarteWeightedMobiusLog_ae_weightedLogForwardFun ε N hε0 hε1).symm

theorem baezDuarteWeightedMobiusLog_toLp
    (ε : ℝ) (N : ℕ) (hε0 : 0 ≤ ε) (hε1 : ε < 1 / 2) :
    (baezDuarteWeightedMobiusLog_memLp ε N hε0 hε1).toLp
        (baezDuarteWeightedMobiusLog ε N) =
      weightedLogPullback
        (baezDuarteWeightedMobiusApproxComplexL2 ε N hε0 hε1) := by
  rw [weightedLogPullback_apply]
  exact MemLp.toLp_congr (baezDuarteWeightedMobiusLog_memLp ε N hε0 hε1)
    (weightedLogForwardFun_memLp
      (baezDuarteWeightedMobiusApproxComplexL2 ε N hε0 hε1))
    (baezDuarteWeightedMobiusLog_ae_weightedLogForwardFun ε N hε0 hε1)

theorem baezDuarteWeightedMobiusLog_integrable
    (ε : ℝ) (N : ℕ) (hε0 : 0 ≤ ε) (hε1 : ε < 1 / 2) :
    Integrable (baezDuarteWeightedMobiusLog ε N) := by
  have hM := hasMellin_baezDuarteWeightedMobiusApprox ε N (1 / 2 : ℂ)
    (by norm_num; linarith) (by norm_num; linarith)
  exact integrable_weightedLog_of_mellinConvergent hM.1

/-- The exact finite weighted Fourier formula in Mathlib's frequency normalization. -/
theorem fourier_baezDuarteWeightedMobiusLog
    (ε : ℝ) (N : ℕ) (hε0 : 0 ≤ ε) (hε1 : ε < 1 / 2) (ξ : ℝ) :
    𝓕 (baezDuarteWeightedMobiusLog ε N) ξ =
      let τ : ℝ := 2 * Real.pi * ξ
      let sMinus : ℂ := (1 / 2 : ℂ) - ε + τ * Complex.I
      let sPlus : ℂ := (1 / 2 : ℂ) + ε + τ * Complex.I
      (-riemannZeta sMinus / sMinus) * mobiusDirichletPartialSum N sPlus := by
  let τ : ℝ := 2 * Real.pi * ξ
  let s : ℂ := (1 / 2 : ℂ) + τ * Complex.I
  have hs0 : 0 < (s - ε).re := by dsimp only [s]; norm_num; linarith
  have hs1 : (s - ε).re < 1 := by dsimp only [s]; norm_num; linarith
  have hM := hasMellin_baezDuarteWeightedMobiusApprox ε N s hs0 hs1
  have hFourier := mellin_criticalLine_eq_fourier
    (fun x : ℝ => (baezDuarteWeightedMobiusApprox ε N x : ℂ)) τ
  rw [hM.2] at hFourier
  have hτ : τ / (2 * Real.pi) = ξ := by
    dsimp only [τ]
    field_simp [Real.pi_ne_zero]
  rw [hτ] at hFourier
  change 𝓕 (fun u : ℝ => (Real.exp (-u / 2) : ℂ) *
    (baezDuarteWeightedMobiusApprox ε N (Real.exp (-u)) : ℂ)) ξ = _
  rw [← hFourier]
  dsimp only [τ, s]
  have hminus : (1 / 2 : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I - ε =
      (1 / 2 : ℂ) - ε + ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I := by
    ring
  have hplus : (1 / 2 : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I + ε =
      (1 / 2 : ℂ) + ε + ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I := by
    ring
  rw [hminus, hplus]

/-- The source's weighted finite transform, written in the vertical ordinate. -/
def baezDuarteWeightedFiniteTransform (ε : ℝ) (N : ℕ) (τ : ℝ) : ℂ :=
  let sMinus : ℂ := (1 / 2 : ℂ) - ε + τ * Complex.I
  let sPlus : ℂ := (1 / 2 : ℂ) + ε + τ * Complex.I
  (-riemannZeta sMinus / sMinus) * mobiusDirichletPartialSum N sPlus

/-- The fixed-epsilon transform limit in Baez-Duarte's equation (2.7). -/
def baezDuarteWeightedLimitTransform (ε τ : ℝ) : ℂ :=
  -baezDuarteZetaRatioIntegrand ε τ

theorem RiemannHypothesis.continuous_baezDuarteWeightedLimitTransform
    (hRH : RiemannHypothesis) {ε : ℝ} (hε : 0 < ε) (hε_top : ε < 1 / 2) :
    Continuous (baezDuarteWeightedLimitTransform ε) := by
  apply continuous_iff_continuousAt.mpr
  intro τ
  let sMinus : ℝ → ℂ := fun t => (1 / 2 : ℂ) - ε + t * Complex.I
  let sPlus : ℝ → ℂ := fun t => (1 / 2 : ℂ) + ε + t * Complex.I
  have hsMinus_one : sMinus τ ≠ 1 := by
    intro hs
    have hre := congrArg Complex.re hs
    norm_num [sMinus, Complex.div_re, Complex.normSq] at hre
    linarith
  have hsPlus_one : sPlus τ ≠ 1 := by
    intro hs
    have hre := congrArg Complex.re hs
    norm_num [sPlus, Complex.div_re, Complex.normSq] at hre
    linarith
  have hzetaPlus : riemannZeta (sPlus τ) ≠ 0 :=
    RiemannHypothesis.riemannZeta_ne_zero_of_half_le_lt_re hRH (by rfl) (by
      norm_num [sPlus, Complex.div_re, Complex.normSq]
      linarith)
  have hsMinus_zero : sMinus τ ≠ 0 := by
    intro hs
    have hre := congrArg Complex.re hs
    norm_num [sMinus, Complex.div_re, Complex.normSq] at hre
    linarith
  have hminus : ContinuousAt (fun t => riemannZeta (sMinus t)) τ :=
    (differentiableAt_riemannZeta hsMinus_one).continuousAt.comp (by fun_prop)
  have hplus : ContinuousAt (fun t => riemannZeta (sPlus t)) τ :=
    (differentiableAt_riemannZeta hsPlus_one).continuousAt.comp (by fun_prop)
  have hsMinus_cont : ContinuousAt sMinus τ := by fun_prop
  change ContinuousAt (fun t =>
    -(riemannZeta (sMinus t) / riemannZeta (sPlus t) / sMinus t)) τ
  exact ((hminus.div hplus hzetaPlus).div hsMinus_cont hsMinus_zero).neg

theorem fourier_baezDuarteWeightedMobiusLog_eq_finiteTransform
    (ε : ℝ) (N : ℕ) (hε0 : 0 ≤ ε) (hε1 : ε < 1 / 2) (ξ : ℝ) :
    𝓕 (baezDuarteWeightedMobiusLog ε N) ξ =
      baezDuarteWeightedFiniteTransform ε N (2 * Real.pi * ξ) := by
  rw [fourier_baezDuarteWeightedMobiusLog ε N hε0 hε1 ξ]
  rfl

/-- The transformed finite-sum error after subtracting the fixed-epsilon zeta-ratio limit. -/
def baezDuarteWeightedMobiusTransformedError (ε : ℝ) (N : ℕ) (τ : ℝ) : ℂ :=
  let sMinus : ℂ := (1 / 2 : ℂ) - ε + τ * Complex.I
  let sPlus : ℂ := (1 / 2 : ℂ) + ε + τ * Complex.I
  (-riemannZeta sMinus / sMinus) *
    (mobiusDirichletPartialSum N sPlus - analyticReciprocalRiemannZeta sPlus)

theorem RiemannHypothesis.weightedFiniteTransform_sub_limitTransform
    (hRH : RiemannHypothesis) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    (N : ℕ) (τ : ℝ) :
    baezDuarteWeightedFiniteTransform ε N τ -
        baezDuarteWeightedLimitTransform ε τ =
      baezDuarteWeightedMobiusTransformedError ε N τ := by
  let sMinus : ℂ := (1 / 2 : ℂ) - ε + τ * Complex.I
  let sPlus : ℂ := (1 / 2 : ℂ) + ε + τ * Complex.I
  have hsPlus_re : 1 / 2 < sPlus.re := by
    norm_num [sPlus, Complex.div_re, Complex.normSq]
    linarith
  have hzeta : riemannZeta sPlus ≠ 0 :=
    RiemannHypothesis.riemannZeta_ne_zero_of_half_le_lt_re hRH (by rfl) hsPlus_re
  have hsPlus_one : sPlus ≠ 1 := by
    intro hs
    have hre := congrArg Complex.re hs
    norm_num [sPlus, Complex.div_re, Complex.normSq] at hre
    linarith
  have hrecip := analyticReciprocalRiemannZeta_eq_inv hsPlus_one hzeta
  have hsMinus_ne : sMinus ≠ 0 := by
    intro hs
    have hre := congrArg Complex.re hs
    norm_num [sMinus, Complex.div_re, Complex.normSq] at hre
    linarith
  simp only [baezDuarteWeightedFiniteTransform, baezDuarteWeightedLimitTransform,
    baezDuarteWeightedMobiusTransformedError, baezDuarteZetaRatioIntegrand,
    baezDuarteZetaRatio]
  change (-riemannZeta sMinus / sMinus) * mobiusDirichletPartialSum N sPlus -
      (-(riemannZeta sMinus / riemannZeta sPlus /
        ((1 / 2 : ℂ) - ε + τ * Complex.I))) =
    (-riemannZeta sMinus / sMinus) *
      (mobiusDirichletPartialSum N sPlus - analyticReciprocalRiemannZeta sPlus)
  rw [show (1 / 2 : ℂ) - ε + τ * Complex.I = sMinus by rfl, hrecip]
  field_simp [hzeta, hsMinus_ne]
  ring

/-- Combining the ratio estimate, fixed-line Lindelof bound, and compiled
Balazard--Saias estimate gives the square-integrable fixed-epsilon error majorant. -/
theorem RiemannHypothesis.exists_norm_weightedMobiusTransformedError_le
    (hRH : RiemannHypothesis) {ε β R η : ℝ}
    (hε : 0 < ε) (hε_top : ε ≤ 1 / 4)
    (hR : 0 < R) (hη : 0 < η)
    (hratio : ∀ τ : ℝ,
      ‖baezDuarteZetaRatioIntegrand ε τ‖ ≤
        R * (1 + |τ|) ^ (-1 + β)) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (τ : ℝ), 2 ≤ N →
      ‖baezDuarteWeightedMobiusTransformedError ε N τ‖ ≤
        K * (N : ℝ) ^ (-ε / 3) *
          ‖baezDuarteVerticalMajorant (β + 2 * η) τ‖ := by
  obtain ⟨A, hA, hzetaBound⟩ :=
    RiemannHypothesis.exists_norm_riemannZeta_half_add_delta_le_rpow
      hRH hε hε_top hη
  obtain ⟨B, hB, hmobiusBound⟩ :=
    RiemannHypothesis.exists_balazardSaias_specialized_bound_compiled hRH hε hη
  refine ⟨R * A * B, mul_pos (mul_pos hR hA) hB, ?_⟩
  intro N τ hN
  let sMinus : ℂ := (1 / 2 : ℂ) - ε + τ * Complex.I
  let sPlus : ℂ := (1 / 2 : ℂ) + ε + τ * Complex.I
  let x : ℝ := 1 + |τ|
  have hx : 0 < x := by dsimp only [x]; positivity
  have hsPlus_re : sPlus.re = (1 / 2 : ℝ) + ε := by
    norm_num [sPlus, Complex.div_re, Complex.normSq]
  have hsPlus_im : sPlus.im = τ := by
    norm_num [sPlus, Complex.div_im, Complex.normSq]
  have hzeta : riemannZeta sPlus ≠ 0 :=
    RiemannHypothesis.riemannZeta_ne_zero_of_half_le_lt_re hRH (by rfl) (by
      rw [hsPlus_re]
      linarith)
  have hsMinus_ne : sMinus ≠ 0 := by
    intro hs
    have hre := congrArg Complex.re hs
    norm_num [sMinus, Complex.div_re, Complex.normSq] at hre
    linarith
  have hfactor : -riemannZeta sMinus / sMinus =
      -baezDuarteZetaRatioIntegrand ε τ * riemannZeta sPlus := by
    simp only [baezDuarteZetaRatioIntegrand, baezDuarteZetaRatio]
    change -riemannZeta sMinus / sMinus =
      -(riemannZeta sMinus / riemannZeta sPlus /
        ((1 / 2 : ℂ) - ε + τ * Complex.I)) * riemannZeta sPlus
    rw [show (1 / 2 : ℂ) - ε + τ * Complex.I = sMinus by rfl]
    field_simp [hzeta, hsMinus_ne]
  have hratio' : ‖baezDuarteZetaRatioIntegrand ε τ‖ ≤
      R * x ^ (-1 + β) := by simpa only [x] using hratio τ
  have hzeta' : ‖riemannZeta sPlus‖ ≤ A * x ^ η := by
    have h := hzetaBound τ
    simpa only [sPlus, x] using h
  have hmobius' :
      ‖mobiusDirichletPartialSum N sPlus - analyticReciprocalRiemannZeta sPlus‖ ≤
        B * (N : ℝ) ^ (-ε / 3) * x ^ η := by
    have h := hmobiusBound N sPlus hN (by rw [hsPlus_re]) (by
      rw [hsPlus_re]
      linarith)
    simpa only [hsPlus_im, x] using h
  have hpower : x ^ (-1 + β) * x ^ η * x ^ η =
      x ^ (-1 + (β + 2 * η)) := by
    rw [← Real.rpow_add hx, ← Real.rpow_add hx]
    congr 1
    ring
  change ‖(-riemannZeta sMinus / sMinus) *
    (mobiusDirichletPartialSum N sPlus - analyticReciprocalRiemannZeta sPlus)‖ ≤ _
  rw [norm_mul, hfactor, norm_mul, norm_neg]
  calc
    (‖baezDuarteZetaRatioIntegrand ε τ‖ * ‖riemannZeta sPlus‖) *
        ‖mobiusDirichletPartialSum N sPlus - analyticReciprocalRiemannZeta sPlus‖
        ≤ (R * x ^ (-1 + β) * (A * x ^ η)) *
          (B * (N : ℝ) ^ (-ε / 3) * x ^ η) := by gcongr
    _ = (R * A * B) * (N : ℝ) ^ (-ε / 3) *
        x ^ (-1 + (β + 2 * η)) := by
      rw [show R * x ^ (-1 + β) * (A * x ^ η) *
          (B * (N : ℝ) ^ (-ε / 3) * x ^ η) =
        (R * A * B) * (N : ℝ) ^ (-ε / 3) *
          (x ^ (-1 + β) * x ^ η * x ^ η) by ring, hpower]
    _ = (R * A * B) * (N : ℝ) ^ (-ε / 3) *
        ‖baezDuarteVerticalMajorant (β + 2 * η) τ‖ := by
      rw [baezDuarteVerticalMajorant, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]

/-- A single small-epsilon interval supports fixed-epsilon transformed error estimates with an
`L²` power majorant. Constants may depend on epsilon, while the admissible interval does not. -/
theorem RiemannHypothesis.exists_weightedMobiusTransformedError_majorant
    (hRH : RiemannHypothesis) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 / 4 ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
        ∃ γ K : ℝ, γ < 1 / 2 ∧ 0 < K ∧
          MemLp (baezDuarteWeightedLimitTransform ε) (2 : ℝ≥0∞) volume ∧
          ∀ (N : ℕ) (τ : ℝ), 2 ≤ N →
            ‖baezDuarteWeightedMobiusTransformedError ε N τ‖ ≤
              K * (N : ℝ) ^ (-ε / 3) *
                ‖baezDuarteVerticalMajorant γ τ‖ := by
  obtain ⟨C, ε₀, D, hC, hε₀, hε₀_top, hCε₀, hD, _hmajorant, hratio⟩ :=
    exists_baezDuarteZetaRatioIntegrand_majorant
  refine ⟨ε₀, hε₀, hε₀_top, ?_⟩
  intro ε hε hε_le
  let β : ℝ := C * ε₀
  let η : ℝ := (1 / 2 - β) / 4
  have hβ : β < 1 / 2 := by simpa only [β] using hCε₀
  have hη : 0 < η := by dsimp only [η]; linarith
  have hγ : β + 2 * η < 1 / 2 := by dsimp only [η]; linarith
  have hratioPower : ∀ τ : ℝ,
      ‖baezDuarteZetaRatioIntegrand ε τ‖ ≤
        (5 * D) * (1 + |τ|) ^ (-1 + β) := by
    intro τ
    have h := hratio ε τ hε.le hε_le
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < 5 * D),
      baezDuarteVerticalMajorant, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (by positivity) _)] at h
    simpa only [β] using h
  have hlimit : MemLp (baezDuarteWeightedLimitTransform ε)
      (2 : ℝ≥0∞) volume := by
    refine _hmajorant.of_le
      (RiemannHypothesis.continuous_baezDuarteWeightedLimitTransform
        hRH hε ((hε_le.trans_lt hε₀_top).trans (by norm_num))).aestronglyMeasurable
      (ae_of_all volume fun τ => ?_)
    rw [baezDuarteWeightedLimitTransform, norm_neg]
    exact hratio ε τ hε.le hε_le
  obtain ⟨K, hK, hbound⟩ :=
    RiemannHypothesis.exists_norm_weightedMobiusTransformedError_le
      hRH hε (hε_le.trans hε₀_top.le) (by positivity : 0 < 5 * D) hη hratioPower
  exact ⟨β + 2 * η, K, hγ, hK, hlimit, hbound⟩

theorem continuous_fourier_baezDuarteWeightedMobiusLog
    (ε : ℝ) (N : ℕ) (hε0 : 0 ≤ ε) (hε1 : ε < 1 / 2) :
    Continuous (𝓕 (baezDuarteWeightedMobiusLog ε N)) := by
  change Continuous (VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ)
    (baezDuarteWeightedMobiusLog ε N))
  exact VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar continuous_inner
    (baezDuarteWeightedMobiusLog_integrable ε N hε0 hε1)

theorem continuous_baezDuarteWeightedFiniteTransform
    (ε : ℝ) (N : ℕ) (hε0 : 0 ≤ ε) (hε1 : ε < 1 / 2) :
    Continuous (baezDuarteWeightedFiniteTransform ε N) := by
  have hscale : Continuous (fun τ : ℝ => τ / (2 * Real.pi)) := by fun_prop
  have hcomp :=
    (continuous_fourier_baezDuarteWeightedMobiusLog ε N hε0 hε1).comp hscale
  convert hcomp using 1
  funext τ
  change baezDuarteWeightedFiniteTransform ε N τ =
    𝓕 (baezDuarteWeightedMobiusLog ε N) (τ / (2 * Real.pi))
  rw [fourier_baezDuarteWeightedMobiusLog_eq_finiteTransform
    ε N hε0 hε1 (τ / (2 * Real.pi))]
  congr 2
  field_simp [Real.pi_ne_zero]

theorem RiemannHypothesis.continuous_baezDuarteWeightedMobiusTransformedError
    (hRH : RiemannHypothesis) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 2)
    (N : ℕ) :
    Continuous (baezDuarteWeightedMobiusTransformedError ε N) := by
  have hdiff := (continuous_baezDuarteWeightedFiniteTransform ε N hε.le hε1).sub
    (RiemannHypothesis.continuous_baezDuarteWeightedLimitTransform hRH hε hε1)
  convert hdiff using 1
  funext τ
  exact (RiemannHypothesis.weightedFiniteTransform_sub_limitTransform
    hRH hε hε1 N τ).symm

theorem baezDuarteWeightedMobiusTransformedError_memLp
    {ε γ K : ℝ} (hγ : γ < 1 / 2) (hK : 0 ≤ K)
    (hcontinuous : ∀ N : ℕ,
      Continuous (baezDuarteWeightedMobiusTransformedError ε N))
    (hbound : ∀ (N : ℕ) (τ : ℝ), 2 ≤ N →
      ‖baezDuarteWeightedMobiusTransformedError ε N τ‖ ≤
        K * (N : ℝ) ^ (-ε / 3) * ‖baezDuarteVerticalMajorant γ τ‖)
    {N : ℕ} (hN : 2 ≤ N) :
    MemLp (baezDuarteWeightedMobiusTransformedError ε N)
      (2 : ℝ≥0∞) volume := by
  let c : ℝ := K * (N : ℝ) ^ (-ε / 3)
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hmajor := (baezDuarteVerticalMajorant_memLp γ hγ).const_smul (c : ℂ)
  refine hmajor.of_le (hcontinuous N).aestronglyMeasurable
    (ae_of_all volume fun τ => ?_)
  rw [Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hc]
  exact hbound N τ hN

/-- Fourier-frequency versions of the finite transform, fixed-epsilon limit, error, and majorant. -/
def baezDuarteScaledWeightedFiniteTransform (ε : ℝ) (N : ℕ) (ξ : ℝ) : ℂ :=
  baezDuarteWeightedFiniteTransform ε N (2 * Real.pi * ξ)

def baezDuarteScaledWeightedLimitTransform (ε ξ : ℝ) : ℂ :=
  baezDuarteWeightedLimitTransform ε (2 * Real.pi * ξ)

def baezDuarteScaledWeightedTransformedError (ε : ℝ) (N : ℕ) (ξ : ℝ) : ℂ :=
  baezDuarteWeightedMobiusTransformedError ε N (2 * Real.pi * ξ)

def baezDuarteScaledVerticalMajorant (γ ξ : ℝ) : ℂ :=
  baezDuarteVerticalMajorant γ (2 * Real.pi * ξ)

theorem baezDuarteScaledVerticalMajorant_memLp
    {γ : ℝ} (hγ : γ < 1 / 2) :
    MemLp (baezDuarteScaledVerticalMajorant γ) (2 : ℝ≥0∞) volume := by
  apply MemLp.comp_mul_left_volume (baezDuarteVerticalMajorant_memLp γ hγ)
  exact mul_ne_zero (by norm_num) Real.pi_ne_zero

theorem baezDuarteScaledWeightedLimitTransform_memLp
    {ε : ℝ} (hlimit : MemLp (baezDuarteWeightedLimitTransform ε)
      (2 : ℝ≥0∞) volume) :
    MemLp (baezDuarteScaledWeightedLimitTransform ε) (2 : ℝ≥0∞) volume := by
  apply MemLp.comp_mul_left_volume hlimit
  exact mul_ne_zero (by norm_num) Real.pi_ne_zero

theorem baezDuarteScaledWeightedTransformedError_memLp
    {ε γ K : ℝ} (hγ : γ < 1 / 2) (hK : 0 ≤ K)
    (hcontinuous : ∀ N : ℕ,
      Continuous (baezDuarteWeightedMobiusTransformedError ε N))
    (hbound : ∀ (N : ℕ) (τ : ℝ), 2 ≤ N →
      ‖baezDuarteWeightedMobiusTransformedError ε N τ‖ ≤
        K * (N : ℝ) ^ (-ε / 3) * ‖baezDuarteVerticalMajorant γ τ‖)
    {N : ℕ} (hN : 2 ≤ N) :
    MemLp (baezDuarteScaledWeightedTransformedError ε N)
      (2 : ℝ≥0∞) volume := by
  apply MemLp.comp_mul_left_volume
    (baezDuarteWeightedMobiusTransformedError_memLp hγ hK hcontinuous hbound hN)
  exact mul_ne_zero (by norm_num) Real.pi_ne_zero

theorem RiemannHypothesis.scaledWeightedFiniteTransform_sub_limitTransform
    (hRH : RiemannHypothesis) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 2)
    (N : ℕ) (ξ : ℝ) :
    baezDuarteScaledWeightedFiniteTransform ε N ξ -
        baezDuarteScaledWeightedLimitTransform ε ξ =
      baezDuarteScaledWeightedTransformedError ε N ξ := by
  exact RiemannHypothesis.weightedFiniteTransform_sub_limitTransform
    hRH hε hε1 N (2 * Real.pi * ξ)

theorem baezDuarteScaledWeightedFiniteTransform_memLp
    (hRH : RiemannHypothesis) {ε γ K : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1 / 2)
    (hγ : γ < 1 / 2) (hK : 0 ≤ K)
    (hlimit : MemLp (baezDuarteWeightedLimitTransform ε) (2 : ℝ≥0∞) volume)
    (hbound : ∀ (N : ℕ) (τ : ℝ), 2 ≤ N →
      ‖baezDuarteWeightedMobiusTransformedError ε N τ‖ ≤
        K * (N : ℝ) ^ (-ε / 3) * ‖baezDuarteVerticalMajorant γ τ‖)
    {N : ℕ} (hN : 2 ≤ N) :
    MemLp (baezDuarteScaledWeightedFiniteTransform ε N)
      (2 : ℝ≥0∞) volume := by
  have hcontinuous : ∀ M : ℕ,
      Continuous (baezDuarteWeightedMobiusTransformedError ε M) := fun M =>
    RiemannHypothesis.continuous_baezDuarteWeightedMobiusTransformedError
      hRH hε hε1 M
  have herror := baezDuarteScaledWeightedTransformedError_memLp
    hγ hK hcontinuous hbound hN
  have hlimitScaled := baezDuarteScaledWeightedLimitTransform_memLp hlimit
  convert herror.add hlimitScaled using 1
  funext ξ
  change baezDuarteScaledWeightedFiniteTransform ε N ξ =
    baezDuarteScaledWeightedTransformedError ε N ξ +
      baezDuarteScaledWeightedLimitTransform ε ξ
  rw [← RiemannHypothesis.scaledWeightedFiniteTransform_sub_limitTransform
    hRH hε hε1 N ξ]
  ring

theorem norm_toLp_scaledWeightedFiniteTransform_sub_limit_le
    (hRH : RiemannHypothesis) {ε γ K : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1 / 2)
    (hγ : γ < 1 / 2) (hK : 0 ≤ K)
    (hlimit : MemLp (baezDuarteWeightedLimitTransform ε) (2 : ℝ≥0∞) volume)
    (hbound : ∀ (N : ℕ) (τ : ℝ), 2 ≤ N →
      ‖baezDuarteWeightedMobiusTransformedError ε N τ‖ ≤
        K * (N : ℝ) ^ (-ε / 3) * ‖baezDuarteVerticalMajorant γ τ‖)
    {N : ℕ} (hN : 2 ≤ N) :
    ‖(baezDuarteScaledWeightedFiniteTransform_memLp hRH hε hε1 hγ hK
          hlimit hbound hN).toLp (baezDuarteScaledWeightedFiniteTransform ε N) -
        (baezDuarteScaledWeightedLimitTransform_memLp hlimit).toLp
          (baezDuarteScaledWeightedLimitTransform ε)‖ ≤
      K * (N : ℝ) ^ (-ε / 3) *
        ‖(baezDuarteScaledVerticalMajorant_memLp hγ).toLp
          (baezDuarteScaledVerticalMajorant γ)‖ := by
  let c : ℝ := K * (N : ℝ) ^ (-ε / 3)
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hcontinuous : ∀ M : ℕ,
      Continuous (baezDuarteWeightedMobiusTransformedError ε M) := fun M =>
    RiemannHypothesis.continuous_baezDuarteWeightedMobiusTransformedError
      hRH hε hε1 M
  let herror := baezDuarteScaledWeightedTransformedError_memLp
    hγ hK hcontinuous hbound hN
  have herrorNorm :
      ‖herror.toLp (baezDuarteScaledWeightedTransformedError ε N)‖ ≤
        c * ‖(baezDuarteScaledVerticalMajorant_memLp hγ).toLp
          (baezDuarteScaledVerticalMajorant γ)‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [herror.coeFn_toLp,
      (baezDuarteScaledVerticalMajorant_memLp hγ).coeFn_toLp] with ξ he hm
    rw [he, hm]
    exact hbound N (2 * Real.pi * ξ) hN
  have htoLpSub := MemLp.toLp_sub
    (baezDuarteScaledWeightedFiniteTransform_memLp hRH hε hε1 hγ hK
      hlimit hbound hN)
    (baezDuarteScaledWeightedLimitTransform_memLp hlimit)
  have heq :
      (baezDuarteScaledWeightedFiniteTransform_memLp hRH hε hε1 hγ hK
          hlimit hbound hN).toLp (baezDuarteScaledWeightedFiniteTransform ε N) -
        (baezDuarteScaledWeightedLimitTransform_memLp hlimit).toLp
          (baezDuarteScaledWeightedLimitTransform ε) =
      herror.toLp (baezDuarteScaledWeightedTransformedError ε N) := by
    rw [← htoLpSub]
    exact MemLp.toLp_congr
      ((baezDuarteScaledWeightedFiniteTransform_memLp hRH hε hε1 hγ hK
        hlimit hbound hN).sub (baezDuarteScaledWeightedLimitTransform_memLp hlimit))
      herror (ae_of_all volume fun ξ =>
        RiemannHypothesis.scaledWeightedFiniteTransform_sub_limitTransform
          hRH hε hε1 N ξ)
  rw [heq]
  simpa only [c] using herrorNorm

theorem RiemannHypothesis.exists_weightedFiniteTransform_close_to_limit
    (hRH : RiemannHypothesis) {ε γ K e : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1 / 2)
    (hγ : γ < 1 / 2) (hK : 0 < K)
    (hlimit : MemLp (baezDuarteWeightedLimitTransform ε) (2 : ℝ≥0∞) volume)
    (hbound : ∀ (N : ℕ) (τ : ℝ), 2 ≤ N →
      ‖baezDuarteWeightedMobiusTransformedError ε N τ‖ ≤
        K * (N : ℝ) ^ (-ε / 3) * ‖baezDuarteVerticalMajorant γ τ‖)
    (he : 0 < e) :
    ∃ (N : ℕ) (hN : 2 ≤ N),
      ‖(baezDuarteScaledWeightedFiniteTransform_memLp hRH hε hε1 hγ hK.le
            hlimit hbound hN).toLp (baezDuarteScaledWeightedFiniteTransform ε N) -
          (baezDuarteScaledWeightedLimitTransform_memLp hlimit).toLp
            (baezDuarteScaledWeightedLimitTransform ε)‖ < e := by
  let B : ℝ := ‖(baezDuarteScaledVerticalMajorant_memLp hγ).toLp
    (baezDuarteScaledVerticalMajorant γ)‖
  have hsmall : Tendsto (fun N : ℕ => K * (N : ℝ) ^ (-ε / 3) * B)
      atTop (nhds 0) := by
    simpa only [mul_zero, zero_mul] using
      ((tendsto_natCast_rpow_neg_delta_div_three hε).const_mul K).mul_const B
  have hevent : ∀ᶠ N : ℕ in atTop, K * (N : ℝ) ^ (-ε / 3) * B < e :=
    hsmall.eventually (Iio_mem_nhds he)
  rcases eventually_atTop.1 (hevent.and (eventually_ge_atTop 2)) with ⟨N, hNall⟩
  have hdata := hNall N le_rfl
  rcases hdata with ⟨hclose, hN⟩
  exact ⟨N, hN,
    (norm_toLp_scaledWeightedFiniteTransform_sub_limit_le hRH hε hε1 hγ hK.le
      hlimit hbound hN).trans_lt (by simpa only [B] using hclose)⟩

theorem RiemannHypothesis.baezDuarteFourierMellinL2_weightedApprox_eq
    (hRH : RiemannHypothesis) {ε γ K : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1 / 2)
    (hγ : γ < 1 / 2) (hK : 0 ≤ K)
    (hlimit : MemLp (baezDuarteWeightedLimitTransform ε) (2 : ℝ≥0∞) volume)
    (hbound : ∀ (N : ℕ) (τ : ℝ), 2 ≤ N →
      ‖baezDuarteWeightedMobiusTransformedError ε N τ‖ ≤
        K * (N : ℝ) ^ (-ε / 3) * ‖baezDuarteVerticalMajorant γ τ‖)
    {N : ℕ} (hN : 2 ≤ N) :
    baezDuarteFourierMellinL2
        (baezDuarteWeightedMobiusApproxComplexL2 ε N hε.le hε1) =
      (baezDuarteScaledWeightedFiniteTransform_memLp hRH hε hε1 hγ hK
        hlimit hbound hN).toLp (baezDuarteScaledWeightedFiniteTransform ε N) := by
  let f := baezDuarteWeightedMobiusLog ε N
  have hf1 : Integrable f :=
    baezDuarteWeightedMobiusLog_integrable ε N hε.le hε1
  have hf2 : MemLp f (2 : ℝ≥0∞) volume :=
    baezDuarteWeightedMobiusLog_memLp ε N hε.le hε1
  have hF2 : MemLp (𝓕 f) (2 : ℝ≥0∞) volume := by
    have hexplicit := baezDuarteScaledWeightedFiniteTransform_memLp
      hRH hε hε1 hγ hK hlimit hbound hN
    exact hexplicit.ae_eq (ae_of_all volume fun ξ =>
      fourier_baezDuarteWeightedMobiusLog_eq_finiteTransform
        ε N hε.le hε1 ξ |>.symm)
  have hcompat := fourier_toLp_eq_toLp_fourier hf1 hf2 hF2
  rw [baezDuarteFourierMellinL2, LinearIsometryEquiv.trans_apply]
  rw [← baezDuarteWeightedMobiusLog_toLp ε N hε.le hε1]
  change (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ) (hf2.toLp f) = _
  calc
    _ = hF2.toLp (𝓕 f) := hcompat
    _ = _ := MemLp.toLp_congr hF2
      (baezDuarteScaledWeightedFiniteTransform_memLp hRH hε hε1 hγ hK
        hlimit hbound hN)
      (ae_of_all volume fun ξ =>
        fourier_baezDuarteWeightedMobiusLog_eq_finiteTransform
          ε N hε.le hε1 ξ)

/-- The physical-space fixed-epsilon limit obtained by inverse Fourier--Mellin transport. -/
def baezDuarteWeightedLimitPhysicalL2
    (ε : ℝ) (hlimit : MemLp (baezDuarteWeightedLimitTransform ε)
      (2 : ℝ≥0∞) volume) : positiveHalfLineComplexL2 :=
  baezDuarteFourierMellinL2.symm
    ((baezDuarteScaledWeightedLimitTransform_memLp hlimit).toLp
      (baezDuarteScaledWeightedLimitTransform ε))

theorem norm_weightedMobiusApproxComplexL2_sub_limitPhysical_eq
    (hRH : RiemannHypothesis) {ε γ K : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1 / 2)
    (hγ : γ < 1 / 2) (hK : 0 ≤ K)
    (hlimit : MemLp (baezDuarteWeightedLimitTransform ε) (2 : ℝ≥0∞) volume)
    (hbound : ∀ (N : ℕ) (τ : ℝ), 2 ≤ N →
      ‖baezDuarteWeightedMobiusTransformedError ε N τ‖ ≤
        K * (N : ℝ) ^ (-ε / 3) * ‖baezDuarteVerticalMajorant γ τ‖)
    {N : ℕ} (hN : 2 ≤ N) :
    ‖baezDuarteWeightedMobiusApproxComplexL2 ε N hε.le hε1 -
        baezDuarteWeightedLimitPhysicalL2 ε hlimit‖ =
      ‖(baezDuarteScaledWeightedFiniteTransform_memLp hRH hε hε1 hγ hK
            hlimit hbound hN).toLp (baezDuarteScaledWeightedFiniteTransform ε N) -
        (baezDuarteScaledWeightedLimitTransform_memLp hlimit).toLp
          (baezDuarteScaledWeightedLimitTransform ε)‖ := by
  rw [← baezDuarteFourierMellinL2.norm_map]
  rw [map_sub, RiemannHypothesis.baezDuarteFourierMellinL2_weightedApprox_eq
    hRH hε hε1 hγ hK hlimit hbound hN]
  simp only [baezDuarteWeightedLimitPhysicalL2,
    LinearIsometryEquiv.apply_symm_apply]

/-- The target indicator's concrete logarithmic representative. -/
def baezDuarteTargetWeightedLog (u : ℝ) : ℂ :=
  (Real.exp (-u / 2) : ℂ) * baezDuarteTargetFunction (Real.exp (-u))

theorem baezDuarteComplexTargetL2_coeFn :
    baezDuarteComplexTargetL2
      =ᵐ[volume.restrict (Ioi (0 : ℝ))]
        fun x : ℝ => (baezDuarteTargetFunction x : ℂ) := by
  filter_upwards [baezDuarteOfRealLp_coeFn baezDuarteTargetL2,
    baezDuarteTargetL2_coeFn] with x hc hr
  rw [baezDuarteComplexTargetL2, hc, hr]

theorem baezDuarteTargetWeightedLog_ae_weightedLogForwardFun :
    baezDuarteTargetWeightedLog =ᵐ[volume]
      weightedLogForwardFun baezDuarteComplexTargetL2 := by
  have hsource := expNeg_quasiMeasurePreserving.ae_eq
    baezDuarteComplexTargetL2_coeFn
  filter_upwards [hsource] with u hu
  change baezDuarteComplexTargetL2 (Real.exp (-u)) =
    (baezDuarteTargetFunction (Real.exp (-u)) : ℂ) at hu
  simp only [baezDuarteTargetWeightedLog, weightedLogForwardFun, expNeg]
  rw [hu]

theorem baezDuarteTargetWeightedLog_memLp :
    MemLp baezDuarteTargetWeightedLog (2 : ℝ≥0∞) volume :=
  (weightedLogForwardFun_memLp baezDuarteComplexTargetL2).ae_eq
    baezDuarteTargetWeightedLog_ae_weightedLogForwardFun.symm

theorem baezDuarteTargetWeightedLog_toLp :
    baezDuarteTargetWeightedLog_memLp.toLp baezDuarteTargetWeightedLog =
      weightedLogPullback baezDuarteComplexTargetL2 := by
  rw [weightedLogPullback_apply]
  exact MemLp.toLp_congr baezDuarteTargetWeightedLog_memLp
    (weightedLogForwardFun_memLp baezDuarteComplexTargetL2)
    baezDuarteTargetWeightedLog_ae_weightedLogForwardFun

theorem baezDuarteTargetWeightedLog_integrable :
    Integrable baezDuarteTargetWeightedLog := by
  have hM := hasMellin_one_Ioc (s := (1 / 2 : ℂ)) (by norm_num)
  have heq : (fun x : ℝ => (baezDuarteTargetFunction x : ℂ)) =
      (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) := by
    funext x
    by_cases hx : x ∈ Ioc (0 : ℝ) 1 <;>
      simp [baezDuarteTargetFunction, Set.indicator, hx]
  have hconv : MellinConvergent
      (fun x : ℝ => (baezDuarteTargetFunction x : ℂ)) (1 / 2 : ℂ) := by
    rw [heq]
    exact hM.1
  exact integrable_weightedLog_of_mellinConvergent hconv

/-- The critical-line Mellin transform of the target indicator. -/
theorem fourier_baezDuarteTargetWeightedLog (ξ : ℝ) :
    𝓕 baezDuarteTargetWeightedLog ξ =
      1 / ((1 / 2 : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) := by
  let τ : ℝ := 2 * Real.pi * ξ
  let s : ℂ := (1 / 2 : ℂ) + τ * Complex.I
  have hs : 0 < s.re := by dsimp only [s]; norm_num
  have hM := hasMellin_one_Ioc (s := s) hs
  have heq : (fun x : ℝ => (baezDuarteTargetFunction x : ℂ)) =
      (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) := by
    funext x
    by_cases hx : x ∈ Ioc (0 : ℝ) 1 <;>
      simp [baezDuarteTargetFunction, Set.indicator, hx]
  have hMtarget : mellin (fun x : ℝ => (baezDuarteTargetFunction x : ℂ)) s = 1 / s := by
    rw [heq]
    exact hM.2
  have hFourier := mellin_criticalLine_eq_fourier
    (fun x : ℝ => (baezDuarteTargetFunction x : ℂ)) τ
  rw [hMtarget] at hFourier
  have hτ : τ / (2 * Real.pi) = ξ := by
    dsimp only [τ]
    field_simp [Real.pi_ne_zero]
  rw [hτ] at hFourier
  change 𝓕 (fun u : ℝ => (Real.exp (-u / 2) : ℂ) *
    (baezDuarteTargetFunction (Real.exp (-u)) : ℂ)) ξ = _
  rw [← hFourier]

def baezDuarteScaledTargetTransform (ξ : ℝ) : ℂ :=
  1 / ((1 / 2 : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I)

theorem baezDuarteScaledTargetTransform_memLp :
    MemLp baezDuarteScaledTargetTransform (2 : ℝ≥0∞) volume := by
  have hcontinuous : Continuous baezDuarteScaledTargetTransform := by
    apply continuous_iff_continuousAt.mpr
    intro ξ
    apply ContinuousAt.div continuousAt_const (by fun_prop)
    intro hs
    have hre := congrArg Complex.re hs
    norm_num [Complex.div_re, Complex.normSq] at hre
  have hmajor := (baezDuarteScaledVerticalMajorant_memLp (γ := 0) (by norm_num)).const_smul
    (5 : ℂ)
  refine hmajor.of_le hcontinuous.aestronglyMeasurable (ae_of_all volume fun ξ => ?_)
  rw [Pi.smul_apply, norm_smul, show ‖(5 : ℂ)‖ = 5 by norm_num]
  have hden := one_div_norm_baezDuarteDenominator_le 0 (2 * Real.pi * ξ) (by norm_num)
  rw [baezDuarteScaledTargetTransform, norm_div, norm_one,
    baezDuarteScaledVerticalMajorant, baezDuarteVerticalMajorant,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _),
    show (-1 + 0 : ℝ) = -1 by norm_num, Real.rpow_neg_one]
  simpa [div_eq_mul_inv] using hden

theorem baezDuarteFourierMellinL2_target_eq :
    baezDuarteFourierMellinL2 baezDuarteComplexTargetL2 =
      baezDuarteScaledTargetTransform_memLp.toLp
        baezDuarteScaledTargetTransform := by
  have hF2 : MemLp (𝓕 baezDuarteTargetWeightedLog) (2 : ℝ≥0∞) volume :=
    baezDuarteScaledTargetTransform_memLp.ae_eq
      (ae_of_all volume fun ξ => (fourier_baezDuarteTargetWeightedLog ξ).symm)
  have hcompat := fourier_toLp_eq_toLp_fourier
    baezDuarteTargetWeightedLog_integrable baezDuarteTargetWeightedLog_memLp hF2
  rw [baezDuarteFourierMellinL2, LinearIsometryEquiv.trans_apply]
  rw [← baezDuarteTargetWeightedLog_toLp]
  calc
    _ = hF2.toLp (𝓕 baezDuarteTargetWeightedLog) := hcompat
    _ = _ := MemLp.toLp_congr hF2 baezDuarteScaledTargetTransform_memLp
      (ae_of_all volume fun ξ => fourier_baezDuarteTargetWeightedLog ξ)

theorem realLineComplexL2_norm_sq_eq_integral_norm_sq
    (f : realLineComplexL2) :
    ‖f‖ ^ 2 = ∫ ξ : ℝ, ‖f ξ‖ ^ 2 := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), MeasureTheory.L2.inner_def]
  rw [← integral_re (MeasureTheory.L2.integrable_inner f f)]
  apply integral_congr_ae
  exact ae_of_all volume fun ξ => by
    change (inner ℂ (f ξ) (f ξ)).re = ‖f ξ‖ ^ 2
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (f ξ)

theorem ae_tendsto_baezDuarteWeightedLimitTransform_neg_target :
    ∀ᵐ τ : ℝ ∂volume,
      Tendsto (fun ε : ℝ => baezDuarteWeightedLimitTransform ε τ)
        (nhds 0)
        (nhds (-1 / ((1 / 2 : ℂ) + τ * Complex.I))) := by
  filter_upwards [ae_tendsto_baezDuarteZetaRatio_one] with τ hratio
  have hden : Tendsto
      (fun ε : ℝ => (1 / 2 : ℂ) - ε + τ * Complex.I)
      (nhds 0) (nhds ((1 / 2 : ℂ) + τ * Complex.I)) := by
    have hc : ContinuousAt
        (fun ε : ℝ => (1 / 2 : ℂ) - ε + τ * Complex.I) 0 := by fun_prop
    rw [show (1 / 2 : ℂ) + τ * Complex.I =
      (1 / 2 : ℂ) - (0 : ℝ) + τ * Complex.I by norm_num]
    exact hc
  have hden_ne : (1 / 2 : ℂ) + τ * Complex.I ≠ 0 := by
    intro hs
    have hre := congrArg Complex.re hs
    norm_num [Complex.div_re, Complex.normSq] at hre
  change Tendsto (fun ε : ℝ =>
    -(baezDuarteZetaRatio ε τ /
      ((1 / 2 : ℂ) - ε + τ * Complex.I))) (nhds 0)
      (nhds (-1 / ((1 / 2 : ℂ) + τ * Complex.I)))
  simpa only [Pi.div_apply, Pi.neg_apply, neg_div] using
    (hratio.div hden hden_ne).neg

theorem ae_tendsto_baezDuarteScaledWeightedLimitTransform_neg_target :
    ∀ᵐ ξ : ℝ ∂volume,
      Tendsto (fun ε : ℝ => baezDuarteScaledWeightedLimitTransform ε ξ)
        (nhds 0) (nhds (-baezDuarteScaledTargetTransform ξ)) := by
  have hscaled := (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
    (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)).ae
      ae_tendsto_baezDuarteWeightedLimitTransform_neg_target
  simpa only [baezDuarteScaledWeightedLimitTransform,
    baezDuarteScaledTargetTransform, smul_eq_mul, div_eq_mul_inv,
    neg_mul] using hscaled

def baezDuarteEpsilonSequence (ε₀ : ℝ) (n : ℕ) : ℝ :=
  ε₀ / ((n : ℝ) + 1)

theorem baezDuarteEpsilonSequence_pos {ε₀ : ℝ} (hε₀ : 0 < ε₀) (n : ℕ) :
    0 < baezDuarteEpsilonSequence ε₀ n := by
  dsimp only [baezDuarteEpsilonSequence]
  positivity

theorem baezDuarteEpsilonSequence_le {ε₀ : ℝ} (hε₀ : 0 ≤ ε₀) (n : ℕ) :
    baezDuarteEpsilonSequence ε₀ n ≤ ε₀ := by
  dsimp only [baezDuarteEpsilonSequence]
  have hone : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    linarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
  exact div_le_self hε₀ hone

theorem tendsto_baezDuarteEpsilonSequence_zero (ε₀ : ℝ) :
    Tendsto (baezDuarteEpsilonSequence ε₀) atTop (nhds 0) := by
  have h := (tendsto_const_nhds (x := ε₀)).mul
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  convert h using 1
  · funext n
    simp [baezDuarteEpsilonSequence, div_eq_mul_inv]
  · simp

theorem baezDuarteNegScaledTargetTransform_memLp :
    MemLp (fun ξ => -baezDuarteScaledTargetTransform ξ) (2 : ℝ≥0∞) volume := by
  convert baezDuarteScaledTargetTransform_memLp.const_smul (-1 : ℂ) using 1
  funext ξ
  simp

/-- Along an explicit positive sequence `epsilon_n -> 0`, the fixed-epsilon zeta-ratio limits
converge in transformed `L²` to the negative target transform. -/
theorem RiemannHypothesis.exists_tendsto_scaledWeightedLimitTransform_neg_target
    (hRH : RiemannHypothesis) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 / 4 ∧
      ∃ hmem : ∀ n : ℕ,
          MemLp (baezDuarteScaledWeightedLimitTransform
            (baezDuarteEpsilonSequence ε₀ n)) (2 : ℝ≥0∞) volume,
        Tendsto
          (fun n => (hmem n).toLp
            (baezDuarteScaledWeightedLimitTransform
              (baezDuarteEpsilonSequence ε₀ n)))
          atTop
          (nhds (baezDuarteNegScaledTargetTransform_memLp.toLp
            (fun ξ => -baezDuarteScaledTargetTransform ξ))) := by
  obtain ⟨C, ε₀, D, hC, hε₀, hε₀_top, hCε₀, hD, hmajor, hratio⟩ :=
    exists_baezDuarteZetaRatioIntegrand_majorant
  let G : ℝ → ℂ := fun ξ =>
    ((5 * D : ℝ) : ℂ) *
      baezDuarteVerticalMajorant (C * ε₀) (2 * Real.pi * ξ)
  have hG : MemLp G (2 : ℝ≥0∞) volume := by
    apply MemLp.comp_mul_left_volume hmajor
    exact mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hseq_pos (n : ℕ) : 0 < baezDuarteEpsilonSequence ε₀ n :=
    baezDuarteEpsilonSequence_pos hε₀ n
  have hseq_le (n : ℕ) : baezDuarteEpsilonSequence ε₀ n ≤ ε₀ :=
    baezDuarteEpsilonSequence_le hε₀.le n
  have hseq_half (n : ℕ) : baezDuarteEpsilonSequence ε₀ n < 1 / 2 :=
    (hseq_le n).trans_lt (hε₀_top.trans (by norm_num))
  have hmem : ∀ n : ℕ,
      MemLp (baezDuarteScaledWeightedLimitTransform
        (baezDuarteEpsilonSequence ε₀ n)) (2 : ℝ≥0∞) volume := by
    intro n
    have hcontinuous : Continuous (baezDuarteScaledWeightedLimitTransform
        (baezDuarteEpsilonSequence ε₀ n)) :=
      (RiemannHypothesis.continuous_baezDuarteWeightedLimitTransform
        hRH (hseq_pos n) (hseq_half n)).comp (by fun_prop)
    refine hG.of_le hcontinuous.aestronglyMeasurable (ae_of_all volume fun ξ => ?_)
    rw [baezDuarteScaledWeightedLimitTransform, baezDuarteWeightedLimitTransform,
      norm_neg]
    exact hratio _ _ (hseq_pos n).le (hseq_le n)
  let T : ℝ → ℂ := fun ξ => -baezDuarteScaledTargetTransform ξ
  have hT : MemLp T (2 : ℝ≥0∞) volume := by
    simpa only [T] using baezDuarteNegScaledTargetTransform_memLp
  let bound : ℝ → ℝ := fun ξ => (‖G ξ‖ + ‖T ξ‖) ^ 2
  have hsum : MemLp (fun ξ => ‖G ξ‖ + ‖T ξ‖) (2 : ℝ≥0∞) volume :=
    hG.norm.add hT.norm
  have hbound_integrable : Integrable bound := by
    exact (memLp_two_iff_integrable_sq hsum.1).mp hsum
  let F : ℕ → ℝ → ℝ := fun n ξ =>
    ‖baezDuarteScaledWeightedLimitTransform
      (baezDuarteEpsilonSequence ε₀ n) ξ - T ξ‖ ^ 2
  have hF_meas : ∀ n, AEStronglyMeasurable (F n) volume := by
    intro n
    exact (((hmem n).sub hT).1.norm.aemeasurable.pow_const 2).aestronglyMeasurable
  have hF_bound : ∀ n, ∀ᵐ ξ ∂volume, ‖F n ξ‖ ≤ bound ξ := by
    intro n
    exact ae_of_all volume fun ξ => by
      have hlim : ‖baezDuarteScaledWeightedLimitTransform
          (baezDuarteEpsilonSequence ε₀ n) ξ‖ ≤ ‖G ξ‖ := by
        rw [baezDuarteScaledWeightedLimitTransform,
          baezDuarteWeightedLimitTransform, norm_neg]
        exact hratio _ _ (hseq_pos n).le (hseq_le n)
      have hdiff : ‖baezDuarteScaledWeightedLimitTransform
          (baezDuarteEpsilonSequence ε₀ n) ξ - T ξ‖ ≤ ‖G ξ‖ + ‖T ξ‖ :=
        (norm_sub_le _ _).trans (add_le_add hlim le_rfl)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) hdiff 2
  have hF_lim : ∀ᵐ ξ ∂volume,
      Tendsto (fun n => F n ξ) atTop (nhds 0) := by
    filter_upwards [ae_tendsto_baezDuarteScaledWeightedLimitTransform_neg_target]
      with ξ hξ
    have hpoint := hξ.comp (tendsto_baezDuarteEpsilonSequence_zero ε₀)
    change Tendsto (fun n => baezDuarteScaledWeightedLimitTransform
      (baezDuarteEpsilonSequence ε₀ n) ξ) atTop
        (nhds (-baezDuarteScaledTargetTransform ξ)) at hpoint
    have hpointT : Tendsto (fun n =>
        baezDuarteScaledWeightedLimitTransform
          (baezDuarteEpsilonSequence ε₀ n) ξ) atTop (nhds (T ξ)) := by
      simpa only [T] using hpoint
    have hsub : Tendsto (fun n =>
        baezDuarteScaledWeightedLimitTransform
          (baezDuarteEpsilonSequence ε₀ n) ξ - T ξ)
        atTop (nhds 0) := by
      simpa only [sub_self] using hpointT.sub_const (T ξ)
    simpa only [F, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hsub.norm.pow 2
  have hintegral : Tendsto (fun n => ∫ ξ, F n ξ) atTop (nhds 0) := by
    simpa only [integral_zero] using
      tendsto_integral_of_dominated_convergence bound hF_meas hbound_integrable
        hF_bound hF_lim
  let targetL2 : realLineComplexL2 := hT.toLp T
  let seqL2 : ℕ → realLineComplexL2 := fun n => (hmem n).toLp
    (baezDuarteScaledWeightedLimitTransform (baezDuarteEpsilonSequence ε₀ n))
  have hnormSq : ∀ n : ℕ, ‖seqL2 n - targetL2‖ ^ 2 = ∫ ξ, F n ξ := by
    intro n
    rw [realLineComplexL2_norm_sq_eq_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (seqL2 n) targetL2,
      (hmem n).coeFn_toLp, hT.coeFn_toLp] with ξ hsub hseq ht
    rw [hsub]
    change ‖(hmem n).toLp
        (baezDuarteScaledWeightedLimitTransform
          (baezDuarteEpsilonSequence ε₀ n)) ξ -
      hT.toLp T ξ‖ ^ 2 = F n ξ
    rw [hseq, ht]
  have hsq : Tendsto (fun n => ‖seqL2 n - targetL2‖ ^ 2) atTop (nhds 0) := by
    simpa only [hnormSq] using hintegral
  have hnorm : Tendsto (fun n => ‖seqL2 n - targetL2‖) atTop (nhds 0) := by
    have hsqrt := hsq.sqrt
    simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsqrt
  refine ⟨ε₀, hε₀, hε₀_top, hmem, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [seqL2, targetL2, T] using hnorm

theorem baezDuarteFourierMellinL2_neg_target_eq :
    baezDuarteFourierMellinL2 (-baezDuarteComplexTargetL2) =
      baezDuarteNegScaledTargetTransform_memLp.toLp
        (fun ξ => -baezDuarteScaledTargetTransform ξ) := by
  rw [map_neg, baezDuarteFourierMellinL2_target_eq]
  rw [← MemLp.toLp_neg baezDuarteScaledTargetTransform_memLp]
  exact MemLp.toLp_congr baezDuarteScaledTargetTransform_memLp.neg
    baezDuarteNegScaledTargetTransform_memLp (EventuallyEq.rfl)

theorem norm_weightedMobiusApproxComplexL2_sub_neg_target_eq
    (hRH : RiemannHypothesis) {ε γ K : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1 / 2)
    (hγ : γ < 1 / 2) (hK : 0 ≤ K)
    (hlimit : MemLp (baezDuarteWeightedLimitTransform ε) (2 : ℝ≥0∞) volume)
    (hbound : ∀ (N : ℕ) (τ : ℝ), 2 ≤ N →
      ‖baezDuarteWeightedMobiusTransformedError ε N τ‖ ≤
        K * (N : ℝ) ^ (-ε / 3) * ‖baezDuarteVerticalMajorant γ τ‖)
    {N : ℕ} (hN : 2 ≤ N) :
    ‖baezDuarteWeightedMobiusApproxComplexL2 ε N hε.le hε1 -
        (-baezDuarteComplexTargetL2)‖ =
      ‖(baezDuarteScaledWeightedFiniteTransform_memLp hRH hε hε1 hγ hK
            hlimit hbound hN).toLp (baezDuarteScaledWeightedFiniteTransform ε N) -
        baezDuarteNegScaledTargetTransform_memLp.toLp
          (fun ξ => -baezDuarteScaledTargetTransform ξ)‖ := by
  rw [← baezDuarteFourierMellinL2.norm_map]
  rw [map_sub,
    RiemannHypothesis.baezDuarteFourierMellinL2_weightedApprox_eq
      hRH hε hε1 hγ hK hlimit hbound hN,
    baezDuarteFourierMellinL2_neg_target_eq]

/-- Diagonalizing `N -> infinity` and `epsilon -> 0` produces a finite weighted source
approximation arbitrarily close to the negative target in physical `L²`. -/
theorem RiemannHypothesis.exists_weightedMobiusApproxComplexL2_close_neg_target
    (hRH : RiemannHypothesis) {e : ℝ} (he : 0 < e) :
    ∃ (ε : ℝ) (N : ℕ) (hε : 0 < ε) (hε1 : ε < 1 / 2) (_hN : 2 ≤ N),
      ‖baezDuarteWeightedMobiusApproxComplexL2 ε N hε.le hε1 -
        (-baezDuarteComplexTargetL2)‖ < e := by
  obtain ⟨εseq, hεseq, hεseq_top, hmem, htend⟩ :=
    RiemannHypothesis.exists_tendsto_scaledWeightedLimitTransform_neg_target hRH
  obtain ⟨εfix, hεfix, hεfix_top, hfixed⟩ :=
    RiemannHypothesis.exists_weightedMobiusTransformedError_majorant hRH
  let targetT : realLineComplexL2 :=
    baezDuarteNegScaledTargetTransform_memLp.toLp
      (fun ξ => -baezDuarteScaledTargetTransform ξ)
  have hcloseEv : ∀ᶠ n : ℕ in atTop,
      dist ((hmem n).toLp (baezDuarteScaledWeightedLimitTransform
        (baezDuarteEpsilonSequence εseq n))) targetT < e / 2 := by
    exact htend.eventually (Metric.ball_mem_nhds targetT (half_pos he))
  have hεEv : ∀ᶠ n : ℕ in atTop,
      baezDuarteEpsilonSequence εseq n < εfix :=
    (tendsto_baezDuarteEpsilonSequence_zero εseq).eventually
      (Iio_mem_nhds hεfix)
  rcases eventually_atTop.1 (hcloseEv.and hεEv) with ⟨n, hnall⟩
  obtain ⟨hclose, hεsmall⟩ := hnall n le_rfl
  let ε := baezDuarteEpsilonSequence εseq n
  have hε : 0 < ε := baezDuarteEpsilonSequence_pos hεseq n
  have hε_le : ε ≤ εfix := hεsmall.le
  have hε1 : ε < 1 / 2 :=
    hεsmall.trans (hεfix_top.trans (by norm_num))
  obtain ⟨γ, K, hγ, hK, hlimit, hbound⟩ := hfixed ε hε hε_le
  obtain ⟨N, hN, hfinite⟩ :=
    RiemannHypothesis.exists_weightedFiniteTransform_close_to_limit
      hRH hε hε1 hγ hK hlimit hbound (half_pos he)
  have hlimitClose :
      ‖(baezDuarteScaledWeightedLimitTransform_memLp hlimit).toLp
          (baezDuarteScaledWeightedLimitTransform ε) - targetT‖ < e / 2 := by
    simpa only [ε, targetT, dist_eq_norm] using hclose
  have htransform :
      ‖(baezDuarteScaledWeightedFiniteTransform_memLp hRH hε hε1 hγ hK.le
            hlimit hbound hN).toLp (baezDuarteScaledWeightedFiniteTransform ε N) -
          targetT‖ < e := by
    calc
      _ ≤ ‖(baezDuarteScaledWeightedFiniteTransform_memLp hRH hε hε1 hγ hK.le
              hlimit hbound hN).toLp (baezDuarteScaledWeightedFiniteTransform ε N) -
            (baezDuarteScaledWeightedLimitTransform_memLp hlimit).toLp
              (baezDuarteScaledWeightedLimitTransform ε)‖ +
          ‖(baezDuarteScaledWeightedLimitTransform_memLp hlimit).toLp
              (baezDuarteScaledWeightedLimitTransform ε) - targetT‖ := by
        convert norm_add_le
          ((baezDuarteScaledWeightedFiniteTransform_memLp hRH hε hε1 hγ hK.le
              hlimit hbound hN).toLp (baezDuarteScaledWeightedFiniteTransform ε N) -
            (baezDuarteScaledWeightedLimitTransform_memLp hlimit).toLp
              (baezDuarteScaledWeightedLimitTransform ε))
          ((baezDuarteScaledWeightedLimitTransform_memLp hlimit).toLp
              (baezDuarteScaledWeightedLimitTransform ε) - targetT) using 1
        all_goals abel_nf
      _ < e / 2 + e / 2 := add_lt_add hfinite hlimitClose
      _ = e := by ring
  refine ⟨ε, N, hε, hε1, hN, ?_⟩
  rw [norm_weightedMobiusApproxComplexL2_sub_neg_target_eq
    hRH hε hε1 hγ hK.le hlimit hbound hN]
  simpa only [targetT] using htransform

/-- A bounded positive weight on the target, used to match the exact hypothesis of the
weighted-to-unweighted tail estimate. -/
def baezDuartePositiveWeightedTargetFunction (ε x : ℝ) : ℝ :=
  x ^ ε * baezDuarteTargetFunction x

theorem baezDuartePositiveWeightedTargetFunction_memLp
    {ε : ℝ} (hε : 0 ≤ ε) :
    MemLp (baezDuartePositiveWeightedTargetFunction ε) (2 : ℝ≥0∞)
      (volume.restrict (Ioi (0 : ℝ))) := by
  have hmeas : AEStronglyMeasurable (baezDuartePositiveWeightedTargetFunction ε)
      (volume.restrict (Ioi (0 : ℝ))) := by
    exact ((Real.continuous_rpow_const hε).measurable.mul
      (measurable_const.indicator measurableSet_Ioc)).aestronglyMeasurable
  refine baezDuarteTargetFunction_memLp_two_positiveHalfLine.of_le hmeas
    (ae_of_all _ fun x => ?_)
  by_cases hx : x ∈ Ioc (0 : ℝ) 1
  · have hxpow : x ^ ε ≤ 1 :=
      Real.rpow_le_one hx.1.le hx.2 hε
    simp only [baezDuartePositiveWeightedTargetFunction,
      baezDuarteTargetFunction, Set.indicator_of_mem hx, mul_one,
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx.1.le _)]
    simpa [baezDuarteTargetFunction, Set.indicator_of_mem hx] using hxpow
  · simp [baezDuartePositiveWeightedTargetFunction,
      baezDuarteTargetFunction, Set.indicator, hx]

def baezDuartePositiveWeightedTargetL2
    (ε : ℝ) (hε : 0 ≤ ε) : positiveHalfLineL2 :=
  (baezDuartePositiveWeightedTargetFunction_memLp hε).toLp
    (baezDuartePositiveWeightedTargetFunction ε)

theorem baezDuartePositiveWeightedTargetL2_coeFn
    (ε : ℝ) (hε : 0 ≤ ε) :
    baezDuartePositiveWeightedTargetL2 ε hε
      =ᵐ[volume.restrict (Ioi (0 : ℝ))]
        baezDuartePositiveWeightedTargetFunction ε :=
  MemLp.coeFn_toLp (baezDuartePositiveWeightedTargetFunction_memLp hε)

theorem tendsto_positiveWeightedTargetL2_epsilonSequence
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    Tendsto
      (fun n => baezDuartePositiveWeightedTargetL2
        (baezDuarteEpsilonSequence ε₀ n)
        (baezDuarteEpsilonSequence_pos hε₀ n).le)
      atTop (nhds baezDuarteTargetL2) := by
  let μ := volume.restrict (Ioi (0 : ℝ))
  let F : ℕ → ℝ → ℝ := fun n x =>
    (baezDuartePositiveWeightedTargetFunction
      (baezDuarteEpsilonSequence ε₀ n) x - baezDuarteTargetFunction x) ^ 2
  have hF_meas : ∀ n, AEStronglyMeasurable (F n) μ := by
    intro n
    have hp := baezDuartePositiveWeightedTargetFunction_memLp
      (baezDuarteEpsilonSequence_pos hε₀ n).le
    exact ((hp.1.sub baezDuarteTargetFunction_memLp_two_positiveHalfLine.1).pow 2)
  have htarget_integrable : Integrable baezDuarteTargetFunction μ := by
    have hsquare := (memLp_two_iff_integrable_sq
      baezDuarteTargetFunction_memLp_two_positiveHalfLine.1).mp
        baezDuarteTargetFunction_memLp_two_positiveHalfLine
    exact hsquare.congr (ae_of_all μ fun x => by
      by_cases hx : x ∈ Ioc (0 : ℝ) 1 <;>
        simp [baezDuarteTargetFunction, Set.indicator, hx])
  have hF_bound : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ baezDuarteTargetFunction x := by
    intro n
    exact ae_of_all μ fun x => by
      by_cases hx : x ∈ Ioc (0 : ℝ) 1
      · have hpos := baezDuarteEpsilonSequence_pos hε₀ n
        have hxpow0 : 0 ≤ x ^ baezDuarteEpsilonSequence ε₀ n :=
          Real.rpow_nonneg hx.1.le _
        have hxpow1 : x ^ baezDuarteEpsilonSequence ε₀ n ≤ 1 :=
          Real.rpow_le_one hx.1.le hx.2 hpos.le
        have ht : baezDuarteTargetFunction x = 1 := by
          simp [baezDuarteTargetFunction, Set.indicator, hx]
        dsimp only [F]
        rw [ht]
        rw [baezDuartePositiveWeightedTargetFunction, ht, mul_one]
        rw [Real.norm_eq_abs]
        change |(x ^ baezDuarteEpsilonSequence ε₀ n - 1) ^ 2| ≤ 1
        rw [abs_of_nonneg (sq_nonneg _)]
        nlinarith
      · have ht : baezDuarteTargetFunction x = 0 := by
          simp [baezDuarteTargetFunction, Set.indicator, hx]
        dsimp only [F]
        rw [ht]
        rw [baezDuartePositiveWeightedTargetFunction, ht, mul_zero]
        norm_num
  have hF_lim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (nhds 0) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hrpow : Tendsto (fun n => x ^ baezDuarteEpsilonSequence ε₀ n)
        atTop (nhds 1) := by
      simpa only [Real.rpow_zero] using
        (tendsto_const_nhds.rpow (tendsto_baezDuarteEpsilonSequence_zero ε₀)
          (Or.inl hx.ne'))
    have hfun : Tendsto (fun n =>
        baezDuartePositiveWeightedTargetFunction
          (baezDuarteEpsilonSequence ε₀ n) x)
        atTop (nhds (baezDuarteTargetFunction x)) := by
      simpa only [baezDuartePositiveWeightedTargetFunction, one_mul] using
        hrpow.mul_const (baezDuarteTargetFunction x)
    simpa only [F, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      (hfun.sub_const (baezDuarteTargetFunction x)).pow 2
  have hintegral : Tendsto (fun n => ∫ x, F n x ∂μ) atTop (nhds 0) := by
    simpa only [integral_zero] using
      tendsto_integral_of_dominated_convergence baezDuarteTargetFunction
        hF_meas htarget_integrable hF_bound hF_lim
  have hnormSq : ∀ n : ℕ,
      ‖baezDuartePositiveWeightedTargetL2
          (baezDuarteEpsilonSequence ε₀ n)
          (baezDuarteEpsilonSequence_pos hε₀ n).le - baezDuarteTargetL2‖ ^ 2 =
        ∫ x, F n x ∂μ := by
    intro n
    rw [positiveHalfLineL2_norm_sq_eq_integral_mul_self]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub
        (baezDuartePositiveWeightedTargetL2
          (baezDuarteEpsilonSequence ε₀ n)
          (baezDuarteEpsilonSequence_pos hε₀ n).le) baezDuarteTargetL2,
      baezDuartePositiveWeightedTargetL2_coeFn
        (baezDuarteEpsilonSequence ε₀ n)
        (baezDuarteEpsilonSequence_pos hε₀ n).le,
      baezDuarteTargetL2_coeFn] with x hsub hp ht
    rw [hsub]
    change (baezDuartePositiveWeightedTargetL2
        (baezDuarteEpsilonSequence ε₀ n)
        (baezDuarteEpsilonSequence_pos hε₀ n).le x - baezDuarteTargetL2 x) *
      (baezDuartePositiveWeightedTargetL2
        (baezDuarteEpsilonSequence ε₀ n)
        (baezDuarteEpsilonSequence_pos hε₀ n).le x - baezDuarteTargetL2 x) = F n x
    rw [hp, ht]
    simp only [F, pow_two]
  have hsq : Tendsto (fun n =>
      ‖baezDuartePositiveWeightedTargetL2
          (baezDuarteEpsilonSequence ε₀ n)
          (baezDuarteEpsilonSequence_pos hε₀ n).le - baezDuarteTargetL2‖ ^ 2)
      atTop (nhds 0) := by
    simpa only [hnormSq] using hintegral
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsqrt := hsq.sqrt
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsqrt

theorem norm_baezDuarteOfRealLp (f : positiveHalfLineL2) :
    ‖baezDuarteOfRealLp f‖ = ‖f‖ := by
  have hof_norm : ‖baezDuarteOfRealLp‖ ≤ 1 := by
    change ‖Complex.ofRealCLM.compLpL (2 : ℝ≥0∞)
      (volume.restrict (Ioi (0 : ℝ)))‖ ≤ 1
    exact (ContinuousLinearMap.norm_compLpL_le Complex.ofRealCLM).trans_eq
      Complex.ofRealCLM_norm
  have hre_norm : ‖baezDuarteRealPartLp‖ ≤ 1 := by
    change ‖Complex.reCLM.compLpL (2 : ℝ≥0∞)
      (volume.restrict (Ioi (0 : ℝ)))‖ ≤ 1
    exact (ContinuousLinearMap.norm_compLpL_le Complex.reCLM).trans_eq
      Complex.reCLM_norm
  apply le_antisymm
  · exact (baezDuarteOfRealLp.le_opNorm f).trans
      (mul_le_of_le_one_left (norm_nonneg f) hof_norm)
  · calc
      ‖f‖ = ‖baezDuarteRealPartLp (baezDuarteOfRealLp f)‖ := by
        rw [baezDuarteRealPartLp_ofReal]
      _ ≤ ‖baezDuarteRealPartLp‖ * ‖baezDuarteOfRealLp f‖ :=
        baezDuarteRealPartLp.le_opNorm _
      _ ≤ ‖baezDuarteOfRealLp f‖ :=
        mul_le_of_le_one_left (norm_nonneg _) hre_norm

theorem norm_weightedMobiusApproxComplexL2_sub_neg_target_eq_real
    (ε : ℝ) (N : ℕ) (hε0 : 0 ≤ ε) (hε1 : ε < 1 / 2) :
    ‖baezDuarteWeightedMobiusApproxComplexL2 ε N hε0 hε1 -
        (-baezDuarteComplexTargetL2)‖ =
      ‖baezDuarteWeightedMobiusApproxL2 ε N hε0 hε1 -
        (-baezDuarteTargetL2)‖ := by
  rw [baezDuarteWeightedMobiusApproxComplexL2,
    baezDuarteComplexTargetL2, ← map_neg, ← map_sub,
    norm_baezDuarteOfRealLp]

theorem RiemannHypothesis.exists_weightedApprox_and_target_corrections
    (hRH : RiemannHypothesis) {e : ℝ} (he : 0 < e) :
    ∃ (ε : ℝ) (N : ℕ) (hε : 0 < ε) (hε1 : ε < 1 / 2) (_hN : 2 ≤ N),
      ‖baezDuarteWeightedMobiusApproxL2 ε N hε.le hε1 -
          (-baezDuarteTargetL2)‖ < e ∧
        ‖baezDuartePositiveWeightedTargetL2 ε hε.le - baezDuarteTargetL2‖ < e := by
  obtain ⟨εseq, hεseq, hεseq_top, hmem, htend⟩ :=
    RiemannHypothesis.exists_tendsto_scaledWeightedLimitTransform_neg_target hRH
  obtain ⟨εfix, hεfix, hεfix_top, hfixed⟩ :=
    RiemannHypothesis.exists_weightedMobiusTransformedError_majorant hRH
  let targetT : realLineComplexL2 :=
    baezDuarteNegScaledTargetTransform_memLp.toLp
      (fun ξ => -baezDuarteScaledTargetTransform ξ)
  have hlimitEv : ∀ᶠ n : ℕ in atTop,
      dist ((hmem n).toLp (baezDuarteScaledWeightedLimitTransform
        (baezDuarteEpsilonSequence εseq n))) targetT < e / 2 :=
    htend.eventually (Metric.ball_mem_nhds targetT (half_pos he))
  have htargetEv : ∀ᶠ n : ℕ in atTop,
      dist (baezDuartePositiveWeightedTargetL2
        (baezDuarteEpsilonSequence εseq n)
        (baezDuarteEpsilonSequence_pos hεseq n).le) baezDuarteTargetL2 < e :=
    (tendsto_positiveWeightedTargetL2_epsilonSequence hεseq).eventually
      (Metric.ball_mem_nhds baezDuarteTargetL2 he)
  have hεEv : ∀ᶠ n : ℕ in atTop,
      baezDuarteEpsilonSequence εseq n < εfix :=
    (tendsto_baezDuarteEpsilonSequence_zero εseq).eventually (Iio_mem_nhds hεfix)
  rcases eventually_atTop.1 (hlimitEv.and (htargetEv.and hεEv)) with ⟨n, hnall⟩
  obtain ⟨hlimitClose0, htargetClose0, hεsmall⟩ := hnall n le_rfl
  let ε := baezDuarteEpsilonSequence εseq n
  have hε : 0 < ε := baezDuarteEpsilonSequence_pos hεseq n
  have hε_le : ε ≤ εfix := hεsmall.le
  have hε1 : ε < 1 / 2 := hεsmall.trans (hεfix_top.trans (by norm_num))
  obtain ⟨γ, K, hγ, hK, hlimit, hbound⟩ := hfixed ε hε hε_le
  obtain ⟨N, hN, hfinite⟩ :=
    RiemannHypothesis.exists_weightedFiniteTransform_close_to_limit
      hRH hε hε1 hγ hK hlimit hbound (half_pos he)
  have hlimitClose :
      ‖(baezDuarteScaledWeightedLimitTransform_memLp hlimit).toLp
          (baezDuarteScaledWeightedLimitTransform ε) - targetT‖ < e / 2 := by
    simpa only [ε, targetT, dist_eq_norm] using hlimitClose0
  have htransform :
      ‖(baezDuarteScaledWeightedFiniteTransform_memLp hRH hε hε1 hγ hK.le
            hlimit hbound hN).toLp (baezDuarteScaledWeightedFiniteTransform ε N) -
          targetT‖ < e := by
    calc
      _ ≤ ‖(baezDuarteScaledWeightedFiniteTransform_memLp hRH hε hε1 hγ hK.le
              hlimit hbound hN).toLp (baezDuarteScaledWeightedFiniteTransform ε N) -
            (baezDuarteScaledWeightedLimitTransform_memLp hlimit).toLp
              (baezDuarteScaledWeightedLimitTransform ε)‖ +
          ‖(baezDuarteScaledWeightedLimitTransform_memLp hlimit).toLp
              (baezDuarteScaledWeightedLimitTransform ε) - targetT‖ := by
        convert norm_add_le
          ((baezDuarteScaledWeightedFiniteTransform_memLp hRH hε hε1 hγ hK.le
              hlimit hbound hN).toLp (baezDuarteScaledWeightedFiniteTransform ε N) -
            (baezDuarteScaledWeightedLimitTransform_memLp hlimit).toLp
              (baezDuarteScaledWeightedLimitTransform ε))
          ((baezDuarteScaledWeightedLimitTransform_memLp hlimit).toLp
              (baezDuarteScaledWeightedLimitTransform ε) - targetT) using 1
        all_goals abel_nf
      _ < e / 2 + e / 2 := add_lt_add hfinite hlimitClose
      _ = e := by ring
  have happComplex :
      ‖baezDuarteWeightedMobiusApproxComplexL2 ε N hε.le hε1 -
          (-baezDuarteComplexTargetL2)‖ < e := by
    rw [norm_weightedMobiusApproxComplexL2_sub_neg_target_eq
      hRH hε hε1 hγ hK.le hlimit hbound hN]
    simpa only [targetT] using htransform
  have happReal :
      ‖baezDuarteWeightedMobiusApproxL2 ε N hε.le hε1 -
          (-baezDuarteTargetL2)‖ < e := by
    rw [← norm_weightedMobiusApproxComplexL2_sub_neg_target_eq_real]
    exact happComplex
  have htargetClose :
      ‖baezDuartePositiveWeightedTargetL2 ε hε.le - baezDuarteTargetL2‖ < e := by
    simpa only [ε, dist_eq_norm] using htargetClose0
  exact ⟨ε, N, hε, hε1, hN, happReal, htargetClose⟩

/-- The weighted tail estimate removes the physical-space weight after the diagonal choice. -/
theorem RiemannHypothesis.exists_mobiusApproxL2_close_neg_target
    (hRH : RiemannHypothesis) {e : ℝ} (he : 0 < e) :
    ∃ δ : ℝ, ∃ N : ℕ,
      ‖baezDuarteMobiusApproxL2 δ N - (-baezDuarteTargetL2)‖ < e := by
  obtain ⟨ε, N, hε, hε1, hN, hweightedSmall, htargetSmall⟩ :=
    RiemannHypothesis.exists_weightedApprox_and_target_corrections
      hRH (show 0 < e / 4 by positivity)
  let f : positiveHalfLineL2 :=
    baezDuarteMobiusApproxL2 (2 * ε) N +
      baezDuartePositiveWeightedTargetL2 ε hε.le
  let w : positiveHalfLineL2 :=
    baezDuarteWeightedMobiusApproxL2 ε N hε.le hε1 + baezDuarteTargetL2
  let m : ℝ := ∑ a ∈ Finset.Icc 1 N,
    ((ArithmeticFunction.moebius a : ℤ) : ℝ) * (a : ℝ) ^ (-(1 + 2 * ε))
  have hweighted :
      w =ᵐ[volume.restrict (Ioi (0 : ℝ))]
        fun x : ℝ => x ^ (-ε) * f x := by
    filter_upwards [Lp.coeFn_add
        (baezDuarteWeightedMobiusApproxL2 ε N hε.le hε1) baezDuarteTargetL2,
      baezDuarteWeightedMobiusApproxL2_coeFn ε N hε.le hε1,
      baezDuarteTargetL2_coeFn,
      Lp.coeFn_add (baezDuarteMobiusApproxL2 (2 * ε) N)
        (baezDuartePositiveWeightedTargetL2 ε hε.le),
      baezDuarteMobiusApproxL2_coeFn (2 * ε) N,
      baezDuartePositiveWeightedTargetL2_coeFn ε hε.le,
      ae_restrict_mem measurableSet_Ioi] with x hw hwa ht hf hfa hpt hx
    rw [hw]
    change baezDuarteWeightedMobiusApproxL2 ε N hε.le hε1 x +
      baezDuarteTargetL2 x = x ^ (-ε) * f x
    rw [hwa, ht]
    rw [hf]
    change baezDuarteWeightedMobiusApprox ε N x + baezDuarteTargetFunction x =
      x ^ (-ε) * (baezDuarteMobiusApproxL2 (2 * ε) N x +
        baezDuartePositiveWeightedTargetL2 ε hε.le x)
    rw [hfa, hpt]
    rw [baezDuarteWeightedMobiusApprox,
      baezDuartePositiveWeightedTargetFunction, mul_add]
    have hx0 : 0 < x := hx
    have hcancel : x ^ (-ε) * x ^ ε = 1 := by
      rw [← Real.rpow_add hx0]
      simp
    rw [← mul_assoc, hcancel, one_mul]
  have htail :
      ∀ᵐ x : ℝ ∂(volume.restrict (Ioi (0 : ℝ))),
        1 < x → f x = m / x := by
    filter_upwards [Lp.coeFn_add (baezDuarteMobiusApproxL2 (2 * ε) N)
        (baezDuartePositiveWeightedTargetL2 ε hε.le),
      baezDuarteMobiusApproxL2_coeFn (2 * ε) N,
      baezDuartePositiveWeightedTargetL2_coeFn ε hε.le] with x hf hfa hpt
    intro hx
    rw [hf]
    change baezDuarteMobiusApproxL2 (2 * ε) N x +
      baezDuartePositiveWeightedTargetL2 ε hε.le x = m / x
    rw [hfa, hpt]
    have htzero : baezDuarteTargetFunction x = 0 := by
      have hnot : x ∉ Ioc (0 : ℝ) 1 := by intro hmem; linarith [hmem.2]
      simp [baezDuarteTargetFunction, Set.indicator, hnot]
    rw [baezDuartePositiveWeightedTargetFunction, htzero, mul_zero, add_zero]
    exact baezDuarteMobiusApprox_eq_dirichletTail_of_one_lt (2 * ε) N hx
  have hwSmall : ‖w‖ < e / 4 := by
    simpa only [w, sub_neg_eq_add] using hweightedSmall
  have hfBound := baezDuarte_weightedTail_norm_le ε m hε.le f w hweighted htail
  have hsqrt : Real.sqrt (1 + 2 * ε) ≤ 2 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · nlinarith
  have hfSmall : ‖f‖ < e / 2 := by
    calc
      ‖f‖ ≤ Real.sqrt (1 + 2 * ε) * ‖w‖ := hfBound
      _ ≤ 2 * ‖w‖ := mul_le_mul_of_nonneg_right hsqrt (norm_nonneg _)
      _ < 2 * (e / 4) := mul_lt_mul_of_pos_left hwSmall (by norm_num)
      _ = e / 2 := by ring
  have hfinal :
      ‖baezDuarteMobiusApproxL2 (2 * ε) N - (-baezDuarteTargetL2)‖ < e := by
    calc
      _ ≤ ‖f‖ +
          ‖baezDuartePositiveWeightedTargetL2 ε hε.le - baezDuarteTargetL2‖ := by
        dsimp only [f]
        convert norm_add_le
          (baezDuarteMobiusApproxL2 (2 * ε) N +
            baezDuartePositiveWeightedTargetL2 ε hε.le)
          (baezDuarteTargetL2 - baezDuartePositiveWeightedTargetL2 ε hε.le) using 1
        · abel_nf
        · rw [norm_sub_rev]
      _ < e / 2 + e / 4 := add_lt_add hfSmall htargetSmall
      _ < e := by linarith
  exact ⟨2 * ε, N, hfinal⟩

/-- Forward implication of the exact positive-natural Baez-Duarte closure criterion. -/
theorem RiemannHypothesis.baezDuarteTargetL2_mem_kernelClosure
    (hRH : RiemannHypothesis) :
    baezDuarteTargetL2 ∈ baezDuarteKernelClosure := by
  change baezDuarteTargetL2 ∈ (baezDuarteKernelClosure : Set positiveHalfLineL2)
  rw [baezDuarteKernelClosure_coe]
  apply Metric.mem_closure_iff.mpr
  intro e he
  obtain ⟨δ, N, hclose⟩ :=
    RiemannHypothesis.exists_mobiusApproxL2_close_neg_target hRH he
  refine ⟨-baezDuarteMobiusApproxL2 δ N, ?_, ?_⟩
  · exact Submodule.neg_mem _ (baezDuarteMobiusApproxL2_mem_span δ N)
  · rw [dist_eq_norm]
    simpa only [sub_neg_eq_add, norm_neg, neg_sub, add_comm] using hclose

/-- Under RH, the source-aligned complex target belongs to the closure of the natural kernels. -/
theorem RiemannHypothesis.baezDuarteComplexTargetL2_mem_kernelClosure
    (hRH : RiemannHypothesis) :
    baezDuarteComplexTargetL2 ∈ baezDuarteComplexKernelClosure :=
  baezDuarteTarget_mem_realClosure_imp_complexClosure
    (RiemannHypothesis.baezDuarteTargetL2_mem_kernelClosure hRH)

/-- The published strong positive-natural Baez-Duarte criterion, in the project's exact
full-half-line complex closure formulation. -/
theorem riemannHypothesis_iff_baezDuarteComplexTarget_mem_kernelClosure :
    RiemannHypothesis ↔
      baezDuarteComplexTargetL2 ∈ baezDuarteComplexKernelClosure := by
  exact ⟨RiemannHypothesis.baezDuarteComplexTargetL2_mem_kernelClosure,
    baezDuarteComplexTarget_mem_closure_imp_riemannHypothesis⟩

end LeanLab.Riemann
