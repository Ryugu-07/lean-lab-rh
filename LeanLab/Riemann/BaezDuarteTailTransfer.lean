import LeanLab.Riemann.BaezDuarteConvergence

set_option linter.style.header false

/-!
# Weighted-to-unweighted tail transfer in the Baez-Duarte proof

This file formalizes the split-at-one estimate used twice in Section 2.2 of Baez-Duarte's proof.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace LeanLab.Riemann

/-- The source's finite Mobius approximation, written with real powers. -/
def baezDuarteMobiusApprox (δ : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 N,
    ((ArithmeticFunction.moebius a : ℤ) : ℝ) * (a : ℝ) ^ (-δ) *
      fractionalPartKernel ((a : ℝ)⁻¹) x

/-- Above one, the source approximation has exponent `1 + δ`. In particular, substituting
`δ = 2 * ε` verifies that the exponent is `1 + 2 * ε`, correcting the printed formula. -/
theorem baezDuarteMobiusApprox_eq_dirichletTail_of_one_lt
    (δ : ℝ) (N : ℕ) {x : ℝ} (hx : 1 < x) :
    baezDuarteMobiusApprox δ N x =
      (∑ a ∈ Finset.Icc 1 N,
        ((ArithmeticFunction.moebius a : ℤ) : ℝ) *
          (a : ℝ) ^ (-(1 + δ))) / x := by
  classical
  rw [baezDuarteMobiusApprox]
  calc
    (∑ a ∈ Finset.Icc 1 N,
      ((ArithmeticFunction.moebius a : ℤ) : ℝ) * (a : ℝ) ^ (-δ) *
        fractionalPartKernel ((a : ℝ)⁻¹) x) =
        ∑ a ∈ Finset.Icc 1 N,
          (((ArithmeticFunction.moebius a : ℤ) : ℝ) *
            (a : ℝ) ^ (-(1 + δ))) / x := by
      refine Finset.sum_congr rfl (fun a ha => ?_)
      have ha_one : 1 ≤ a := (Finset.mem_Icc.mp ha).1
      have ha_one_real : (1 : ℝ) ≤ a := by exact_mod_cast ha_one
      have ha_pos : (0 : ℝ) < a := zero_lt_one.trans_le ha_one_real
      have hainv_pos : (0 : ℝ) < (a : ℝ)⁻¹ := inv_pos.mpr ha_pos
      have hainv_le_one : (a : ℝ)⁻¹ ≤ 1 :=
        inv_le_one_of_one_le₀ ha_one_real
      have hfract :
          fractionalPartKernel ((a : ℝ)⁻¹) x = (a : ℝ)⁻¹ / x := by
        rw [fractionalPartKernel, Int.fract_eq_self.mpr]
        exact ⟨(div_pos hainv_pos (zero_lt_one.trans hx)).le,
          (div_lt_one (zero_lt_one.trans hx)).mpr (hainv_le_one.trans_lt hx)⟩
      rw [hfract, div_eq_mul_inv]
      have hrpow :
          (a : ℝ) ^ (-δ) * (a : ℝ)⁻¹ =
            (a : ℝ) ^ (-(1 + δ)) := by
        rw [← Real.rpow_neg_one, ← Real.rpow_add ha_pos]
        congr 1
        ring
      calc
        ((ArithmeticFunction.moebius a : ℤ) : ℝ) * (a : ℝ) ^ (-δ) *
            ((a : ℝ)⁻¹ * x⁻¹) =
            ((ArithmeticFunction.moebius a : ℤ) : ℝ) *
              (((a : ℝ) ^ (-δ) * (a : ℝ)⁻¹) * x⁻¹) := by ring
        _ = (((ArithmeticFunction.moebius a : ℤ) : ℝ) *
            (a : ℝ) ^ (-(1 + δ))) / x := by
          rw [hrpow, div_eq_mul_inv]
          ring
    _ = (∑ a ∈ Finset.Icc 1 N,
        ((ArithmeticFunction.moebius a : ℤ) : ℝ) *
          (a : ℝ) ^ (-(1 + δ))) / x := by
      rw [Finset.sum_div]

theorem baezDuarteMobiusApprox_two_mul_eq_dirichletTail_of_one_lt
    (ε : ℝ) (N : ℕ) {x : ℝ} (hx : 1 < x) :
    baezDuarteMobiusApprox (2 * ε) N x =
      (∑ a ∈ Finset.Icc 1 N,
        ((ArithmeticFunction.moebius a : ℤ) : ℝ) *
          (a : ℝ) ^ (-(1 + 2 * ε))) / x :=
  baezDuarteMobiusApprox_eq_dirichletTail_of_one_lt (2 * ε) N hx

theorem integral_Ioi_weighted_moment_mul_self
    (ε m : ℝ) (hε : 0 ≤ ε) :
    (∫ x : ℝ in Set.Ioi 1,
      (x ^ (-ε) * (m / x)) * (x ^ (-ε) * (m / x))) =
        m ^ 2 / (1 + 2 * ε) := by
  have hpower : -2 - 2 * ε < (-1 : ℝ) := by linarith
  have hden : 1 + 2 * ε ≠ 0 := by positivity
  calc
    (∫ x : ℝ in Set.Ioi 1,
      (x ^ (-ε) * (m / x)) * (x ^ (-ε) * (m / x))) =
        ∫ x : ℝ in Set.Ioi 1, m ^ 2 * x ^ (-2 - 2 * ε) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
      have hx0 : 0 < x := lt_trans zero_lt_one hx
      rw [div_eq_mul_inv, ← Real.rpow_neg_one]
      calc
        (x ^ (-ε) * (m * x ^ (-1 : ℝ))) *
            (x ^ (-ε) * (m * x ^ (-1 : ℝ))) =
            m ^ 2 * (x ^ (-ε) * x ^ (-1 : ℝ)) ^ 2 := by ring
        _ = m ^ 2 * (x ^ (-ε - (1 : ℝ))) ^ 2 := by
          rw [← Real.rpow_add hx0]
          ring_nf
        _ = m ^ 2 * x ^ (-2 - 2 * ε) := by
          rw [← Real.rpow_mul_natCast hx0.le (-ε - (1 : ℝ)) 2]
          congr 1
          ring_nf
    _ = m ^ 2 * (∫ x : ℝ in Set.Ioi 1, x ^ (-2 - 2 * ε)) := by
      rw [integral_const_mul]
    _ = m ^ 2 / (1 + 2 * ε) := by
      rw [integral_Ioi_rpow_of_lt hpower zero_lt_one, Real.one_rpow]
      have hpden : -2 - 2 * ε + 1 = -(1 + 2 * ε) := by ring
      rw [hpden]
      field_simp [hden]

/-- The quantitative weighted-to-unweighted estimate used in Baez-Duarte's split-at-one
argument. The only tail information required is the source's exact `m / x` shape. -/
theorem baezDuarte_weightedTail_norm_sq_le
    (ε m : ℝ) (hε : 0 ≤ ε) (f w : positiveHalfLineL2)
    (hweighted :
      w =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        fun x : ℝ => x ^ (-ε) * f x)
    (htail :
      ∀ᵐ x : ℝ ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        1 < x → f x = m / x) :
    ‖f‖ ^ 2 ≤ (1 + 2 * ε) * ‖w‖ ^ 2 := by
  let μ₀ := volume.restrict (Set.Ioi (0 : ℝ))
  let μsmall := volume.restrict (Set.Ioc (0 : ℝ) 1)
  let μtail := volume.restrict (Set.Ioi (1 : ℝ))
  have hsmall_le : μsmall ≤ μ₀ := by
    exact Measure.restrict_mono (by
      intro x hx
      exact hx.1) le_rfl
  have htail_le : μtail ≤ μ₀ := by
    exact Measure.restrict_mono (by
      intro x hx
      change (1 : ℝ) < x at hx
      exact lt_trans zero_lt_one hx) le_rfl
  have hfint : Integrable (fun x : ℝ => f x * f x) μ₀ := by
    simpa only [pow_two] using
      (memLp_two_iff_integrable_sq (Lp.memLp f).1).mp (Lp.memLp f)
  have hwint : Integrable (fun x : ℝ => w x * w x) μ₀ := by
    simpa only [pow_two] using
      (memLp_two_iff_integrable_sq (Lp.memLp w).1).mp (Lp.memLp w)
  have hfsmall : Integrable (fun x : ℝ => f x * f x) μsmall :=
    hfint.mono_measure hsmall_le
  have hwsmall : Integrable (fun x : ℝ => w x * w x) μsmall :=
    hwint.mono_measure hsmall_le
  have hftail : Integrable (fun x : ℝ => f x * f x) μtail :=
    hfint.mono_measure htail_le
  have hwtail : Integrable (fun x : ℝ => w x * w x) μtail :=
    hwint.mono_measure htail_le
  have hweighted_small := hweighted.filter_mono (ae_mono hsmall_le)
  have hsmall_ae :
      (fun x : ℝ => f x * f x) ≤ᵐ[μsmall]
        fun x : ℝ => w x * w x := by
    filter_upwards [hweighted_small,
      ae_restrict_mem measurableSet_Ioc] with x hwx hx
    rw [hwx]
    have hq : 1 ≤ x ^ (-ε) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx.1 hx.2 (by linarith)
    have hq_sq : 1 ≤ (x ^ (-ε)) ^ 2 := by nlinarith
    have hnonneg :
        0 ≤ (f x) ^ 2 * ((x ^ (-ε)) ^ 2 - 1) :=
      mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hq_sq)
    nlinarith [hnonneg]
  have hsmall_integral :
      (∫ x : ℝ, f x * f x ∂μsmall) ≤
        ∫ x : ℝ, w x * w x ∂μsmall :=
    integral_mono_ae hfsmall hwsmall hsmall_ae
  have htail_source := htail.filter_mono (ae_mono htail_le)
  have htail_mem : ∀ᵐ x : ℝ ∂μtail, 1 < x :=
    ae_restrict_mem measurableSet_Ioi
  have hf_tail_eq :
      (fun x : ℝ => f x * f x) =ᵐ[μtail]
        fun x : ℝ => (m / x) * (m / x) := by
    filter_upwards [htail_source, htail_mem] with x hfx hx
    rw [hfx hx]
  have hweighted_tail := hweighted.filter_mono (ae_mono htail_le)
  have hw_tail_eq :
      (fun x : ℝ => w x * w x) =ᵐ[μtail]
        fun x : ℝ =>
          (x ^ (-ε) * (m / x)) * (x ^ (-ε) * (m / x)) := by
    filter_upwards [hweighted_tail, htail_source, htail_mem] with x hwx hfx hx
    rw [hwx, hfx hx]
  have hf_tail_integral :
      (∫ x : ℝ, f x * f x ∂μtail) = m ^ 2 := by
    rw [integral_congr_ae hf_tail_eq]
    exact integral_Ioi_moment_div_mul_self m
  have hw_tail_integral :
      (∫ x : ℝ, w x * w x ∂μtail) = m ^ 2 / (1 + 2 * ε) := by
    rw [integral_congr_ae hw_tail_eq]
    exact integral_Ioi_weighted_moment_mul_self ε m hε
  have hwsmall_nonneg : 0 ≤ ∫ x : ℝ, w x * w x ∂μsmall :=
    integral_nonneg_of_ae (ae_of_all μsmall fun x => mul_self_nonneg (w x))
  have hden_pos : 0 < 1 + 2 * ε := by linarith
  have htail_scale :
      m ^ 2 = (1 + 2 * ε) * (m ^ 2 / (1 + 2 * ε)) := by
    field_simp
  have htail_integral_scale :
      (∫ x : ℝ, f x * f x ∂μtail) =
        (1 + 2 * ε) * ∫ x : ℝ, w x * w x ∂μtail := by
    rw [hf_tail_integral, hw_tail_integral]
    exact htail_scale
  have hsmall_extra_nonneg :
      0 ≤ (2 * ε) * ∫ x : ℝ, w x * w x ∂μsmall :=
    mul_nonneg (mul_nonneg (by norm_num) hε) hwsmall_nonneg
  have hmeasure : μ₀ = μsmall + μtail := by
    dsimp [μ₀, μsmall, μtail]
    rw [← Set.Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
    exact Measure.restrict_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
  rw [positiveHalfLineL2_norm_sq_eq_integral_mul_self f,
    positiveHalfLineL2_norm_sq_eq_integral_mul_self w]
  change (∫ x : ℝ, f x * f x ∂μ₀) ≤
    (1 + 2 * ε) * ∫ x : ℝ, w x * w x ∂μ₀
  rw [hmeasure, integral_add_measure hfsmall hftail,
    integral_add_measure hwsmall hwtail, htail_integral_scale]
  nlinarith

theorem baezDuarte_weightedTail_norm_le
    (ε m : ℝ) (hε : 0 ≤ ε) (f w : positiveHalfLineL2)
    (hweighted :
      w =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        fun x : ℝ => x ^ (-ε) * f x)
    (htail :
      ∀ᵐ x : ℝ ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        1 < x → f x = m / x) :
    ‖f‖ ≤ Real.sqrt (1 + 2 * ε) * ‖w‖ := by
  refine (sq_le_sq₀ (norm_nonneg f)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg w))).mp ?_
  rw [mul_pow, Real.sq_sqrt (by linarith : 0 ≤ 1 + 2 * ε)]
  exact baezDuarte_weightedTail_norm_sq_le ε m hε f w hweighted htail

/-- The source's weighted convergence implies ordinary convergence when the errors retain their
`m_i / x` tail. This also covers a fixed positive exponent by taking `ε` constant. -/
theorem tendsto_norm_zero_of_baezDuarte_weightedTail
    {ι : Type*} {l : Filter ι}
    (ε m : ι → ℝ) (ε₀ : ℝ) (f w : ι → positiveHalfLineL2)
    (hε : ∀ i, 0 ≤ ε i)
    (hweighted : ∀ i,
      w i =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        fun x : ℝ => x ^ (-ε i) * f i x)
    (htail : ∀ i,
      ∀ᵐ x : ℝ ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        1 < x → f i x = m i / x)
    (hε_lim : Filter.Tendsto ε l (nhds ε₀))
    (hw_zero : Filter.Tendsto (fun i => ‖w i‖) l (nhds 0)) :
    Filter.Tendsto (fun i => ‖f i‖) l (nhds 0) := by
  have harg :
      Filter.Tendsto (fun i => 1 + 2 * ε i) l (nhds (1 + 2 * ε₀)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul hε_lim)
  have hsqrt :
      Filter.Tendsto (fun i => Real.sqrt (1 + 2 * ε i)) l
        (nhds (Real.sqrt (1 + 2 * ε₀))) := by
    change Filter.Tendsto
      ((fun x : ℝ => Real.sqrt x) ∘ (fun i => 1 + 2 * ε i)) l
        (nhds (Real.sqrt (1 + 2 * ε₀)))
    simpa only [Function.comp_apply] using
      Real.continuous_sqrt.continuousAt.tendsto.comp harg
  have hupper :
      Filter.Tendsto
        (fun i => Real.sqrt (1 + 2 * ε i) * ‖w i‖) l (nhds 0) := by
    simpa using hsqrt.mul hw_zero
  exact squeeze_zero (fun i => norm_nonneg (f i))
    (fun i => baezDuarte_weightedTail_norm_le
      (ε i) (m i) (hε i) (f i) (w i) (hweighted i) (htail i)) hupper

/-- The fixed estimate instantiated on an actual positive-natural finite kernel combination. -/
theorem baezDuarte_finsupp_norm_sq_le_of_weighted
    (ε : ℝ) (hε : 0 ≤ ε)
    (c : baezDuartePositiveNatIndex →₀ ℝ) (w : positiveHalfLineL2)
    (hweighted :
      w =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        fun x : ℝ => x ^ (-ε) *
          (c.sum fun n r => r • baezDuarteKernelL2 n) x) :
    ‖c.sum fun n r => r • baezDuarteKernelL2 n‖ ^ 2 ≤
      (1 + 2 * ε) * ‖w‖ ^ 2 := by
  apply baezDuarte_weightedTail_norm_sq_le
    ε (baezDuarteReciprocalMoment c) hε
      (c.sum fun n r => r • baezDuarteKernelL2 n) w hweighted
  filter_upwards [baezDuarte_finsupp_sum_kernelL2_coeFn c] with x hx
  intro hx1
  rw [hx]
  exact baezDuarte_finsupp_sum_eq_reciprocalMoment_div_of_one_lt c hx1

end LeanLab.Riemann
