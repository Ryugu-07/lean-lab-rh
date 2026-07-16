import LeanLab.Riemann.DeBruijnNewmanZeros
import LeanLab.Riemann.DeBruijnNewmanHeat
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option linter.style.header false

/-!
# Closedness infrastructure for the de Bruijn-Newman threshold

This file proves that the set of real times at which every zero of the source-normalized
de Bruijn-Newman family is real is closed.
-/

open Complex Filter MeasureTheory Real Set Topology

namespace LeanLab.Riemann

noncomputable section

theorem deBruijnNewmanPhiTerm_pos (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    0 < deBruijnNewmanPhiTerm n u := by
  rw [deBruijnNewmanPhiTerm_eq]
  let x : ℝ := (n : ℝ) + 1
  have hx : 1 ≤ x := by
    dsimp [x]
    have hn : 0 ≤ (n : ℝ) := by positivity
    linarith
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hx2 : 1 ≤ x ^ 2 := by nlinarith [sq_nonneg (x - 1)]
  have he4 : 1 ≤ Real.exp (4 * u) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hpi : 3 < π := Real.pi_gt_three
  have hpi0 : 0 ≤ π := Real.pi_pos.le
  have hcore : 0 < 2 * π * x ^ 2 * Real.exp (4 * u) - 3 := by
    have h₁ : π ≤ π * x ^ 2 :=
      by simpa using mul_le_mul_of_nonneg_left hx2 hpi0
    have h₂ : π * x ^ 2 ≤ π * x ^ 2 * Real.exp (4 * u) :=
      le_mul_of_one_le_right (mul_nonneg hpi0 (sq_nonneg x)) he4
    nlinarith
  have he9 : Real.exp (9 * u) = Real.exp (5 * u) * Real.exp (4 * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he9]
  change 0 <
    (2 * π ^ 2 * x ^ 4 * (Real.exp (5 * u) * Real.exp (4 * u)) -
      3 * π * x ^ 2 * Real.exp (5 * u)) *
        Real.exp (-π * x ^ 2 * Real.exp (4 * u))
  rw [show
      2 * π ^ 2 * x ^ 4 * (Real.exp (5 * u) * Real.exp (4 * u)) -
          3 * π * x ^ 2 * Real.exp (5 * u) =
        π * x ^ 2 * Real.exp (5 * u) *
          (2 * π * x ^ 2 * Real.exp (4 * u) - 3) by ring]
  positivity

theorem deBruijnNewmanPhi_pos {u : ℝ} (hu : 0 ≤ u) :
    0 < deBruijnNewmanPhi u := by
  rw [deBruijnNewmanPhi]
  exact (summable_deBruijnNewmanPhiTerm u).tsum_pos
    (fun n ↦ (deBruijnNewmanPhiTerm_pos n hu).le) 0
    (deBruijnNewmanPhiTerm_pos 0 hu)

private theorem integrableOn_dbnThresholdZeroIntegrand (t : ℝ) :
    IntegrableOn
      (fun u : ℝ ↦ Real.exp (t * u ^ 2) * deBruijnNewmanPhi u) (Ioi 0) := by
  let major : ℝ → ℝ := fun u ↦
    (1 + u ^ 2) * Real.exp (|t| * u ^ 2 + 0 * u) *
      ‖deBruijnNewmanPhi u‖
  have hmajor : Integrable major (volume.restrict (Ioi 0)) := by
    exact integrableOn_one_add_sq_mul_exp_mul_norm_deBruijnNewmanPhi
      |t| (abs_nonneg t) 0
  apply Integrable.mono' hmajor
  · have hterms : ∀ n : ℕ, AEStronglyMeasurable
        (fun u : ℝ ↦ deBruijnNewmanPhiTerm n u)
        (volume.restrict (Ioi 0)) := fun n ↦ by
      apply Continuous.aestronglyMeasurable
      simp_rw [deBruijnNewmanPhiTerm_eq]
      fun_prop
    have hphi : AEStronglyMeasurable deBruijnNewmanPhi
        (volume.restrict (Ioi 0)) :=
      AEStronglyMeasurable.tsum hterms
    exact
      (by fun_prop : Continuous (fun u : ℝ ↦ Real.exp (t * u ^ 2))).aestronglyMeasurable.mul hphi
  · rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with u hu
    have hu0 : 0 ≤ u := hu.le
    have ht : t * u ^ 2 ≤ |t| * u ^ 2 := by
      gcongr
      exact le_abs_self t
    dsimp only [major]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (t * u ^ 2) * |deBruijnNewmanPhi u| ≤
          Real.exp (|t| * u ^ 2) * ‖deBruijnNewmanPhi u‖ := by
        rw [← Real.norm_eq_abs]
        gcongr
      _ ≤ (1 + u ^ 2) * Real.exp (|t| * u ^ 2 + 0 * u) *
          ‖deBruijnNewmanPhi u‖ := by
        rw [zero_mul, add_zero]
        rw [mul_assoc]
        exact le_mul_of_one_le_left
          (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
          (by nlinarith [sq_nonneg u])

theorem deBruijnNewmanH_zero_pos (t : ℝ) :
    0 < (deBruijnNewmanH t 0).re := by
  let f : ℝ → ℝ := fun u ↦ Real.exp (t * u ^ 2) * deBruijnNewmanPhi u
  have hf_int : Integrable f (volume.restrict (Ioi 0)) :=
    integrableOn_dbnThresholdZeroIntegrand t
  have hf_nonneg : 0 ≤ᵐ[volume.restrict (Ioi 0)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (mul_pos (Real.exp_pos _) (deBruijnNewmanPhi_pos hu.le)).le
  have hsupport : 0 < (volume.restrict (Ioi 0)) (Function.support f) := by
    have hsubset : Ioo (0 : ℝ) 1 ⊆ Function.support f := by
      intro u hu
      exact (mul_pos (Real.exp_pos _) (deBruijnNewmanPhi_pos hu.1.le)).ne'
    have hmeasure : 0 < (volume.restrict (Ioi 0)) (Ioo (0 : ℝ) 1) := by
      rw [Measure.restrict_apply measurableSet_Ioo]
      simp only [Ioo_inter_Ioi, max_eq_left (by norm_num : (0 : ℝ) ≤ 0),
        Real.volume_Ioo, sub_zero, ENNReal.ofReal_one]
      norm_num
    exact hmeasure.trans_le (measure_mono hsubset)
  have hf_pos : 0 < ∫ u, f u ∂volume.restrict (Ioi 0) :=
    (integral_pos_iff_support_of_nonneg_ae hf_nonneg hf_int).2 hsupport
  have hH : deBruijnNewmanH t 0 =
      ((∫ u, f u ∂volume.restrict (Ioi 0) : ℝ) : ℂ) := by
    rw [deBruijnNewmanH]
    simp only [zero_mul, Complex.cos_zero, mul_one, f]
    exact integral_complex_ofReal
  rw [hH]
  simpa using hf_pos

theorem deBruijnNewmanH_zero_ne_zero (t : ℝ) :
    deBruijnNewmanH t 0 ≠ 0 := by
  intro h
  have := deBruijnNewmanH_zero_pos t
  rw [h, Complex.zero_re] at this
  exact lt_irrefl 0 this

theorem continuousAt_deBruijnNewmanH_joint (p : ℝ × ℂ) :
    ContinuousAt (fun q : ℝ × ℂ ↦ deBruijnNewmanH q.1 q.2) p := by
  change Tendsto (fun q : ℝ × ℂ ↦ deBruijnNewmanH q.1 q.2) (𝓝 p)
    (𝓝 (deBruijnNewmanH p.1 p.2))
  let F : (ℝ × ℂ) → ℝ → ℂ := fun q u ↦
    (((Real.exp (q.1 * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ) *
      Complex.cos (q.2 * (u : ℂ)))
  let bound : ℝ → ℝ := fun u ↦
    (1 + u ^ 2) *
      Real.exp ((|p.1| + 1) * u ^ 2 + (‖p.2‖ + 1) * u) *
        ‖deBruijnNewmanPhi u‖
  have htime : ∀ᶠ q : ℝ × ℂ in 𝓝 p, q.1 ∈ Metric.ball p.1 1 := by
    exact continuousAt_fst (Metric.ball_mem_nhds p.1 one_pos)
  have hspace : ∀ᶠ q : ℝ × ℂ in 𝓝 p, q.2 ∈ Metric.ball p.2 1 := by
    exact continuousAt_snd (Metric.ball_mem_nhds p.2 one_pos)
  have hF_meas : ∀ᶠ q : ℝ × ℂ in 𝓝 p,
      AEStronglyMeasurable (F q) (volume.restrict (Ioi 0)) := by
    filter_upwards with q
    have hterms : ∀ n : ℕ, AEStronglyMeasurable
        (fun u : ℝ ↦ deBruijnNewmanPhiTerm n u)
        (volume.restrict (Ioi 0)) := fun n ↦ by
      apply Continuous.aestronglyMeasurable
      simp_rw [deBruijnNewmanPhiTerm_eq]
      fun_prop
    have hphi : AEStronglyMeasurable deBruijnNewmanPhi
        (volume.restrict (Ioi 0)) :=
      AEStronglyMeasurable.tsum hterms
    have hreal : AEStronglyMeasurable
        (fun u : ℝ ↦ Real.exp (q.1 * u ^ 2) * deBruijnNewmanPhi u)
        (volume.restrict (Ioi 0)) :=
      (by fun_prop : Continuous
        (fun u : ℝ ↦ Real.exp (q.1 * u ^ 2))).aestronglyMeasurable.mul hphi
    have hcos : AEStronglyMeasurable
        (fun u : ℝ ↦ Complex.cos (q.2 * (u : ℂ)))
        (volume.restrict (Ioi 0)) :=
      (by fun_prop : Continuous
        (fun u : ℝ ↦ Complex.cos (q.2 * (u : ℂ)))).aestronglyMeasurable
    exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hreal).mul hcos
  have h_bound : ∀ᶠ q : ℝ × ℂ in 𝓝 p,
      ∀ᵐ u ∂volume.restrict (Ioi 0), ‖F q u‖ ≤ bound u := by
    filter_upwards [htime, hspace] with q hqt hqz
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 ≤ u := hu.le
    have hqtAbs : |q.1| ≤ |p.1| + 1 := by
      calc
        |q.1| = |p.1 + (q.1 - p.1)| := by congr 1; ring
        _ ≤ |p.1| + |q.1 - p.1| := abs_add_le _ _
        _ ≤ |p.1| + 1 := by
          gcongr
          simpa only [Real.dist_eq] using hqt.le
    have hqtUpper : q.1 ≤ |p.1| + 1 := (le_abs_self q.1).trans hqtAbs
    have hqzNorm : ‖q.2‖ ≤ ‖p.2‖ + 1 := by
      calc
        ‖q.2‖ = ‖p.2 + (q.2 - p.2)‖ := by congr 1; ring
        _ ≤ ‖p.2‖ + ‖q.2 - p.2‖ := norm_add_le _ _
        _ ≤ ‖p.2‖ + 1 := by
          gcongr
          simpa only [Complex.dist_eq] using (Metric.mem_ball.mp hqz).le
    dsimp only [F, bound]
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.exp_pos _), ← Real.norm_eq_abs]
    calc
      Real.exp (q.1 * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
          ‖Complex.cos (q.2 * (u : ℂ))‖ ≤
        Real.exp ((|p.1| + 1) * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
          Real.exp (‖q.2‖ * u) := by
        gcongr
        exact norm_complex_cos_mul_real_le q.2 hu0
      _ ≤
        Real.exp ((|p.1| + 1) * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
          Real.exp ((‖p.2‖ + 1) * u) := by
        gcongr
      _ ≤ (1 + u ^ 2) *
          Real.exp ((|p.1| + 1) * u ^ 2 + (‖p.2‖ + 1) * u) *
            ‖deBruijnNewmanPhi u‖ := by
        rw [Real.exp_add]
        have hA : 0 ≤
            Real.exp ((|p.1| + 1) * u ^ 2) *
              Real.exp ((‖p.2‖ + 1) * u) * ‖deBruijnNewmanPhi u‖ := by positivity
        have hscale := le_mul_of_one_le_left hA
          (show (1 : ℝ) ≤ 1 + u ^ 2 by nlinarith [sq_nonneg u])
        simpa only [mul_assoc, mul_left_comm, mul_comm] using hscale
  have hbound_int : Integrable bound (volume.restrict (Ioi 0)) := by
    exact integrableOn_one_add_sq_mul_exp_mul_norm_deBruijnNewmanPhi
      (|p.1| + 1) (by positivity) (‖p.2‖ + 1)
  have h_lim : ∀ᵐ u ∂volume.restrict (Ioi 0),
      Tendsto (fun q : ℝ × ℂ ↦ F q u) (𝓝 p) (𝓝 (F p u)) := by
    filter_upwards with u
    exact (by fun_prop : ContinuousAt (fun q : ℝ × ℂ ↦ F q u) p)
  have hmain := tendsto_integral_filter_of_dominated_convergence bound hF_meas h_bound
    hbound_int h_lim
  simpa only [F, deBruijnNewmanH] using hmain

theorem continuous_deBruijnNewmanH_joint :
    Continuous (fun p : ℝ × ℂ ↦ deBruijnNewmanH p.1 p.2) :=
  continuous_iff_continuousAt.mpr continuousAt_deBruijnNewmanH_joint

private theorem eventually_exists_deBruijnNewmanH_zero_mem_closedBall
    {t : ℝ} {z₀ : ℂ} {R : ℝ} (hR : 0 < R)
    (hz₀ : deBruijnNewmanH t z₀ = 0)
    (hboundary : ∀ z ∈ Metric.sphere z₀ R, deBruijnNewmanH t z ≠ 0) :
    ∀ᶠ τ in 𝓝 t, ∃ z ∈ Metric.closedBall z₀ R, deBruijnNewmanH τ z = 0 := by
  have hsphere_nonempty : (Metric.sphere z₀ R).Nonempty :=
    NormedSpace.sphere_nonempty.mpr hR.le
  have hnorm_cont : ContinuousOn (fun z : ℂ ↦ ‖deBruijnNewmanH t z‖)
      (Metric.sphere z₀ R) :=
    (differentiable_deBruijnNewmanH t).continuous.norm.continuousOn
  obtain ⟨x, hx, hxmin⟩ :=
    (isCompact_sphere z₀ R).exists_isMinOn hsphere_nonempty hnorm_cont
  let m : ℝ := ‖deBruijnNewmanH t x‖
  have hm : 0 < m := by
    exact norm_pos_iff.mpr (hboundary x hx)
  have huniform : ∀ᶠ τ in 𝓝 t, ∀ z ∈ Metric.sphere z₀ R,
      ‖deBruijnNewmanH τ z - deBruijnNewmanH t z‖ < m / 2 := by
    apply (isCompact_sphere z₀ R).eventually_forall_of_forall_eventually
    intro z hz
    have hcont : ContinuousAt
        (fun q : ℝ × ℂ ↦ deBruijnNewmanH q.1 q.2 - deBruijnNewmanH t q.2)
        (t, z) := by
      exact continuous_deBruijnNewmanH_joint.continuousAt.sub
        ((differentiable_deBruijnNewmanH t).continuous.comp continuous_snd).continuousAt
    have hcont0 : Tendsto
        (fun q : ℝ × ℂ ↦ deBruijnNewmanH q.1 q.2 - deBruijnNewmanH t q.2)
        (𝓝 (t, z)) (𝓝 0) := by simpa using hcont.tendsto
    have hevent := hcont0.eventually (Metric.ball_mem_nhds (0 : ℂ) (half_pos hm))
    simpa only [Prod.fst, Prod.snd, sub_self, Metric.mem_ball, dist_zero_right] using hevent
  have hcenter : ∀ᶠ τ in 𝓝 t, ‖deBruijnNewmanH τ z₀‖ < m / 2 := by
    have hcont := (hasDerivAt_deBruijnNewmanH_time t z₀).continuousAt
    have hcont0 : Tendsto (fun τ : ℝ ↦ deBruijnNewmanH τ z₀) (𝓝 t) (𝓝 0) := by
      simpa only [hz₀] using hcont.tendsto
    have hevent := hcont0.eventually (Metric.ball_mem_nhds (0 : ℂ) (half_pos hm))
    simpa only [Metric.mem_ball, dist_zero_right] using hevent
  filter_upwards [huniform, hcenter] with τ hclose hcenter_small
  by_contra hexists
  have hzero_free : ∀ z ∈ Metric.closedBall z₀ R, deBruijnNewmanH τ z ≠ 0 := by
    intro z hz hzero
    exact hexists ⟨z, hz, hzero⟩
  have hanalytic : AnalyticOnNhd ℂ (deBruijnNewmanH τ) (Metric.closedBall z₀ R) :=
    fun z _ ↦ (differentiable_deBruijnNewmanH τ).analyticAt z
  have hanalytic_abs : AnalyticOnNhd ℂ (deBruijnNewmanH τ)
      (Metric.closedBall z₀ |R|) := by
    simpa [abs_of_pos hR] using hanalytic
  have hnorm_boundary : ∀ z ∈ Metric.sphere z₀ R,
      m / 2 < ‖deBruijnNewmanH τ z‖ := by
    intro z hz
    have hmin : m ≤ ‖deBruijnNewmanH t z‖ := hxmin hz
    have htriangle : ‖deBruijnNewmanH t z‖ ≤
        ‖deBruijnNewmanH τ z - deBruijnNewmanH t z‖ +
          ‖deBruijnNewmanH τ z‖ := by
      calc
        ‖deBruijnNewmanH t z‖ =
            ‖(deBruijnNewmanH t z - deBruijnNewmanH τ z) +
              deBruijnNewmanH τ z‖ := by congr 1; ring
        _ ≤ ‖deBruijnNewmanH t z - deBruijnNewmanH τ z‖ +
            ‖deBruijnNewmanH τ z‖ := norm_add_le _ _
        _ = ‖deBruijnNewmanH τ z - deBruijnNewmanH t z‖ +
            ‖deBruijnNewmanH τ z‖ := by rw [norm_sub_rev]
    nlinarith [hclose z hz]
  have hcircle : CircleIntegrable
      (fun z : ℂ ↦ Real.log ‖deBruijnNewmanH τ z‖) z₀ R :=
    (hanalytic_abs.mono Metric.sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
  have hlog_boundary : ∀ z ∈ Metric.sphere z₀ |R|,
      Real.log (m / 2) ≤ Real.log ‖deBruijnNewmanH τ z‖ := by
    intro z hz
    have hz' : z ∈ Metric.sphere z₀ R := by simpa [abs_of_pos hR] using hz
    have hnorm := hnorm_boundary z hz'
    have hnorm_pos : 0 < ‖deBruijnNewmanH τ z‖ := (half_pos hm).trans hnorm
    exact Real.strictMonoOn_log.monotoneOn (half_pos hm) hnorm_pos hnorm.le
  have havg_lower : Real.log (m / 2) ≤
      circleAverage (fun z : ℂ ↦ Real.log ‖deBruijnNewmanH τ z‖) z₀ R := by
    calc
      Real.log (m / 2) = circleAverage (fun _ : ℂ ↦ Real.log (m / 2)) z₀ R :=
        (circleAverage_const _ _ _).symm
      _ ≤ circleAverage (fun z : ℂ ↦ Real.log ‖deBruijnNewmanH τ z‖) z₀ R :=
        circleAverage_mono (circleIntegrable_const _ _ _) hcircle hlog_boundary
  have hcenter_ne : deBruijnNewmanH τ z₀ ≠ 0 :=
    hzero_free z₀ (Metric.mem_closedBall_self hR.le)
  have hcenter_log : Real.log ‖deBruijnNewmanH τ z₀‖ < Real.log (m / 2) :=
    Real.log_lt_log (norm_pos_iff.mpr hcenter_ne) hcenter_small
  have hzero_free_abs : ∀ z ∈ Metric.closedBall z₀ |R|,
      deBruijnNewmanH τ z ≠ 0 := by
    simpa [abs_of_pos hR] using hzero_free
  rw [hanalytic_abs.circleAverage_log_norm_of_ne_zero hzero_free_abs] at havg_lower
  exact (not_lt_of_ge havg_lower) hcenter_log

theorem exists_deBruijnNewmanH_isolating_nonreal_closedBall
    {t : ℝ} {z₀ : ℂ} (hz₀_im : z₀.im ≠ 0) :
    ∃ R > 0,
      (∀ z ∈ Metric.sphere z₀ R, deBruijnNewmanH t z ≠ 0) ∧
      (∀ z ∈ Metric.closedBall z₀ R, z.im ≠ 0) := by
  have hanalytic : AnalyticOnNhd ℂ (deBruijnNewmanH t) (Set.univ : Set ℂ) :=
    fun z _ ↦ (differentiable_deBruijnNewmanH t).analyticAt z
  have hnot_local_zero : ¬deBruijnNewmanH t =ᶠ[𝓝 z₀] 0 := by
    intro hlocal
    have hglobal := hanalytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ z₀) hlocal
    exact deBruijnNewmanH_zero_ne_zero t (hglobal (mem_univ 0))
  have hisolated : ∀ᶠ z in 𝓝[≠] z₀, deBruijnNewmanH t z ≠ 0 :=
    ((hanalytic z₀ (mem_univ z₀)).eventually_eq_zero_or_eventually_ne_zero).resolve_left
      hnot_local_zero
  have hnear_nonzero : ∀ᶠ z in 𝓝 z₀, z ≠ z₀ → deBruijnNewmanH t z ≠ 0 :=
    eventually_nhdsWithin_iff.mp hisolated
  have hnear_ball : ∀ᶠ z in 𝓝 z₀, z ∈ Metric.ball z₀ |z₀.im| :=
    Metric.ball_mem_nhds z₀ (abs_pos.mpr hz₀_im)
  have hcombined : ∀ᶠ z in 𝓝 z₀,
      (z ≠ z₀ → deBruijnNewmanH t z ≠ 0) ∧ z ∈ Metric.ball z₀ |z₀.im| :=
    hnear_nonzero.and hnear_ball
  obtain ⟨R, hR, hsubset⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hcombined
  refine ⟨R, hR, ?_, ?_⟩
  · intro z hz
    exact (hsubset (Metric.sphere_subset_closedBall hz)).1
      (Metric.ne_of_mem_sphere hz hR.ne')
  · intro z hz him
    have hball : z ∈ Metric.ball z₀ |z₀.im| := (hsubset hz).2
    have habs_le : |z₀.im| ≤ dist z z₀ := by
      calc
        |z₀.im| = |(z - z₀).im| := by simp [him]
        _ ≤ ‖z - z₀‖ := Complex.abs_im_le_norm (z - z₀)
        _ = dist z z₀ := by rw [Complex.dist_eq]
    exact (not_lt_of_ge habs_le) (Metric.mem_ball.mp hball)

theorem isClosed_setOf_deBruijnNewmanAllZerosReal :
    IsClosed {t : ℝ | deBruijnNewmanAllZerosReal t} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro t ht
  change ¬deBruijnNewmanAllZerosReal t at ht
  rw [deBruijnNewmanAllZerosReal] at ht
  push Not at ht
  obtain ⟨z₀, hz₀, hz₀_im⟩ := ht
  obtain ⟨R, hR, hboundary, hnonreal⟩ :=
    exists_deBruijnNewmanH_isolating_nonreal_closedBall hz₀_im
  have hpersist := eventually_exists_deBruijnNewmanH_zero_mem_closedBall hR hz₀ hboundary
  filter_upwards [hpersist] with τ hτ
  rcases hτ with ⟨z, hzball, hzero⟩
  change ¬deBruijnNewmanAllZerosReal τ
  intro hall
  exact hnonreal z hzball (hall z hzero)

end

end LeanLab.Riemann
