import LeanLab.Riemann.DeBruijnNewmanUpperHalf

set_option linter.style.header false

/-!
# General de Bruijn strip contraction

This module generalizes the source-normalized time-zero strip contraction to an arbitrary base
heat time and arbitrary squared strip width. It also proves the exact all-real endpoint after an
additional heat time equal to half the squared strip width.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped BigOperators ComplexConjugate

namespace LeanLab.Riemann

noncomputable section

private theorem dbnCoshApprox_order_one_general (t a : ℝ) (n : ℕ) :
    Complex.Hadamard.EntireOfOrderAtMost (1 : ℝ) (dbnCoshApprox t a n) := by
  rw [← verticalAverageIterate_deBruijnNewmanH]
  induction n with
  | zero => exact deBruijnNewmanH_entireOfOrderAtMost_one t
  | succ n hn => exact entireOfOrderAtMost_verticalAverage hn a

private theorem dbnCoshApprox_even_general (t a : ℝ) (n : ℕ) :
    ∀ z : ℂ, dbnCoshApprox t a n (-z) = dbnCoshApprox t a n z := by
  rw [← verticalAverageIterate_deBruijnNewmanH]
  induction n with
  | zero => exact deBruijnNewmanH_neg t
  | succ n hn => exact verticalAverage_even hn a

private theorem dbnCoshApprox_conj_general (t a : ℝ) (n : ℕ) :
    ∀ z : ℂ, dbnCoshApprox t a n (conj z) = conj (dbnCoshApprox t a n z) := by
  rw [← verticalAverageIterate_deBruijnNewmanH]
  induction n with
  | zero => exact deBruijnNewmanH_conj t
  | succ n hn => exact verticalAverage_conj hn a

/-- Finite vertical-average iteration subtracts exactly one squared shift width per step from an
arbitrary source-time zero strip. -/
theorem dbnCoshApprox_zero_im_sq_le_of
    {t a muSq : ℝ} (ha : 0 ≤ a)
    (hstrip : ∀ z : ℂ, deBruijnNewmanH t z = 0 → z.im ^ 2 ≤ muSq)
    (n : ℕ) (hbudget : (n : ℝ) * a ^ 2 ≤ muSq)
    {z : ℂ} (hz : dbnCoshApprox t a n z = 0) :
    z.im ^ 2 ≤ muSq - (n : ℝ) * a ^ 2 := by
  induction n generalizing z with
  | zero =>
      rw [dbnCoshApprox_zero] at hz
      simpa only [Nat.cast_zero, zero_mul, sub_zero] using hstrip z hz
  | succ n hn =>
      have hbudget' : (n : ℝ) * a ^ 2 ≤ muSq := by
        norm_num [Nat.cast_add, Nat.cast_one] at hbudget
        nlinarith [sq_nonneg a]
      have haSq : a ^ 2 ≤ muSq - (n : ℝ) * a ^ 2 := by
        norm_num [Nat.cast_add, Nat.cast_one] at hbudget
        nlinarith
      have hzavg : verticalAverage a (dbnCoshApprox t a n) z = 0 := by
        rw [verticalAverage_dbnCoshApprox]
        exact hz
      have hstep := verticalAverage_zero_im_sq_le
        (dbnCoshApprox_order_one_general t a n)
        (dbnCoshApprox_even_general t a n)
        (dbnCoshApprox_zero_ne_zero t a n)
        (dbnCoshApprox_conj_general t a n)
        (fun w hw ↦ hn hbudget' hw) ha haSq z hzavg
      norm_num [Nat.cast_add, Nat.cast_one] at hbudget ⊢
      nlinarith

/-- Every positive-index finite heat approximant inherits the exact contracted arbitrary-base
strip. -/
theorem dbnForwardApprox_zero_im_sq_le_of
    {t delta muSq : ℝ} (hdelta : 0 ≤ delta)
    (hbudget : 2 * delta ≤ muSq)
    (hstrip : ∀ z : ℂ, deBruijnNewmanH t z = 0 → z.im ^ 2 ≤ muSq)
    {n : ℕ} (hn : 0 < n) {z : ℂ}
    (hz : dbnForwardApprox t delta n z = 0) :
    z.im ^ 2 ≤ muSq - 2 * delta := by
  let a : ℝ := Real.sqrt (2 * delta / (n : ℝ))
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hrad : 0 ≤ 2 * delta / (n : ℝ) := by positivity
  have haSq : a ^ 2 = 2 * delta / (n : ℝ) := Real.sq_sqrt hrad
  have hfiniteBudget : (n : ℝ) * a ^ 2 ≤ muSq := by
    rw [haSq]
    field_simp [hnR.ne']
    exact hbudget
  have hfinite := dbnCoshApprox_zero_im_sq_le_of (Real.sqrt_nonneg _)
    hstrip n hfiniteBudget
    (show dbnCoshApprox t a n z = 0 by
      simpa only [dbnForwardApprox, a] using hz)
  rw [haSq] at hfinite
  field_simp [hnR.ne'] at hfinite
  exact hfinite

private theorem dbnForwardApprox_order_one_general (t delta : ℝ) (n : ℕ) :
    Complex.Hadamard.EntireOfOrderAtMost (1 : ℝ) (dbnForwardApprox t delta n) := by
  simpa only [dbnForwardApprox] using
    dbnCoshApprox_order_one_general t (Real.sqrt (2 * delta / (n : ℝ))) n

/-- A zero of the arbitrary-base heat limit persists inside any isolating closed ball for all
sufficiently late finite cosh approximants. -/
theorem eventually_exists_dbnForwardApprox_zero_mem_closedBall_of
    {t delta : ℝ} (hdelta : 0 ≤ delta) {z0 : ℂ} {R : ℝ} (hR : 0 < R)
    (hz0 : deBruijnNewmanH (t + delta) z0 = 0)
    (hboundary : ∀ z ∈ Metric.sphere z0 R,
      deBruijnNewmanH (t + delta) z ≠ 0) :
    ∀ᶠ n : ℕ in atTop,
      ∃ z ∈ Metric.closedBall z0 R, dbnForwardApprox t delta n z = 0 := by
  have hsphere_nonempty : (Metric.sphere z0 R).Nonempty :=
    NormedSpace.sphere_nonempty.mpr hR.le
  have hnorm_cont : ContinuousOn (fun z : ℂ ↦ ‖deBruijnNewmanH (t + delta) z‖)
      (Metric.sphere z0 R) :=
    (differentiable_deBruijnNewmanH (t + delta)).continuous.norm.continuousOn
  obtain ⟨x, hx, hxmin⟩ :=
    (isCompact_sphere z0 R).exists_isMinOn hsphere_nonempty hnorm_cont
  let m : ℝ := ‖deBruijnNewmanH (t + delta) x‖
  have hm : 0 < m := norm_pos_iff.mpr (hboundary x hx)
  let B : ℝ := ‖z0‖ + R
  have hsphere_bound : ∀ z ∈ Metric.sphere z0 R, ‖z‖ ≤ B := by
    intro z hz
    have hdist : ‖z - z0‖ = R := by
      rw [← Complex.dist_eq]
      exact Metric.mem_sphere.mp hz
    dsimp only [B]
    calc
      ‖z‖ = ‖(z - z0) + z0‖ := by congr 1; ring
      _ ≤ ‖z - z0‖ + ‖z0‖ := norm_add_le _ _
      _ = ‖z0‖ + R := by rw [hdist]; ring
  have hz0_bound : ‖z0‖ ≤ B := by
    dsimp only [B]
    linarith
  have herr : ∀ᶠ n : ℕ in atTop,
      (∫ u in Ioi (0 : ℝ), dbnForwardError t delta B n u) < m / 2 := by
    exact (tendsto_integral_dbnForwardError t hdelta B).eventually
      (Iio_mem_nhds (half_pos hm))
  filter_upwards [herr] with n hn
  have hclose : ∀ z ∈ Metric.sphere z0 R,
      ‖dbnForwardApprox t delta n z - deBruijnNewmanH (t + delta) z‖ < m / 2 := by
    intro z hz
    exact (norm_dbnForwardApprox_sub_le_errorIntegral t hdelta
      (hsphere_bound z hz) n).trans_lt hn
  have hcenter_small : ‖dbnForwardApprox t delta n z0‖ < m / 2 := by
    have hcenter := norm_dbnForwardApprox_sub_le_errorIntegral t hdelta hz0_bound n
    rw [hz0, sub_zero] at hcenter
    exact hcenter.trans_lt hn
  by_contra hexists
  have hzero_free : ∀ z ∈ Metric.closedBall z0 R,
      dbnForwardApprox t delta n z ≠ 0 := by
    intro z hz hzero
    exact hexists ⟨z, hz, hzero⟩
  have hdiff := (dbnForwardApprox_order_one_general t delta n).differentiable
  have hanalytic : AnalyticOnNhd ℂ (dbnForwardApprox t delta n)
      (Metric.closedBall z0 R) := fun z _ ↦ hdiff.analyticAt z
  have hanalytic_abs : AnalyticOnNhd ℂ (dbnForwardApprox t delta n)
      (Metric.closedBall z0 |R|) := by
    simpa [abs_of_pos hR] using hanalytic
  have hnorm_boundary : ∀ z ∈ Metric.sphere z0 R,
      m / 2 < ‖dbnForwardApprox t delta n z‖ := by
    intro z hz
    have hmin : m ≤ ‖deBruijnNewmanH (t + delta) z‖ := hxmin hz
    have htriangle : ‖deBruijnNewmanH (t + delta) z‖ ≤
        ‖dbnForwardApprox t delta n z - deBruijnNewmanH (t + delta) z‖ +
          ‖dbnForwardApprox t delta n z‖ := by
      calc
        ‖deBruijnNewmanH (t + delta) z‖ =
            ‖(deBruijnNewmanH (t + delta) z - dbnForwardApprox t delta n z) +
              dbnForwardApprox t delta n z‖ := by congr 1; ring
        _ ≤ ‖deBruijnNewmanH (t + delta) z - dbnForwardApprox t delta n z‖ +
            ‖dbnForwardApprox t delta n z‖ := norm_add_le _ _
        _ = ‖dbnForwardApprox t delta n z - deBruijnNewmanH (t + delta) z‖ +
            ‖dbnForwardApprox t delta n z‖ := by rw [norm_sub_rev]
    nlinarith [hclose z hz]
  have hcircle : CircleIntegrable
      (fun z : ℂ ↦ Real.log ‖dbnForwardApprox t delta n z‖) z0 R :=
    (hanalytic_abs.mono Metric.sphere_subset_closedBall).meromorphicOn
      |>.circleIntegrable_log_norm
  have hlog_boundary : ∀ z ∈ Metric.sphere z0 |R|,
      Real.log (m / 2) ≤ Real.log ‖dbnForwardApprox t delta n z‖ := by
    intro z hz
    have hz' : z ∈ Metric.sphere z0 R := by simpa [abs_of_pos hR] using hz
    have hnorm := hnorm_boundary z hz'
    have hnorm_pos : 0 < ‖dbnForwardApprox t delta n z‖ := (half_pos hm).trans hnorm
    exact Real.strictMonoOn_log.monotoneOn (half_pos hm) hnorm_pos hnorm.le
  have havg_lower : Real.log (m / 2) ≤
      circleAverage (fun z : ℂ ↦ Real.log ‖dbnForwardApprox t delta n z‖) z0 R := by
    calc
      Real.log (m / 2) = circleAverage (fun _ : ℂ ↦ Real.log (m / 2)) z0 R :=
        (circleAverage_const _ _ _).symm
      _ ≤ circleAverage (fun z : ℂ ↦ Real.log ‖dbnForwardApprox t delta n z‖) z0 R :=
        circleAverage_mono (circleIntegrable_const _ _ _) hcircle hlog_boundary
  have hcenter_ne : dbnForwardApprox t delta n z0 ≠ 0 :=
    hzero_free z0 (Metric.mem_closedBall_self hR.le)
  have hcenter_log : Real.log ‖dbnForwardApprox t delta n z0‖ < Real.log (m / 2) :=
    Real.log_lt_log (norm_pos_iff.mpr hcenter_ne) hcenter_small
  have hzero_free_abs : ∀ z ∈ Metric.closedBall z0 |R|,
      dbnForwardApprox t delta n z ≠ 0 := by
    simpa [abs_of_pos hR] using hzero_free
  rw [hanalytic_abs.circleAverage_log_norm_of_ne_zero hzero_free_abs] at havg_lower
  exact (not_lt_of_ge havg_lower) hcenter_log

private theorem exists_deBruijnNewmanH_isolating_outside_sq_strip_closedBall_general
    {t bound : ℝ} {z0 : ℂ} (houtside : bound < z0.im ^ 2) :
    ∃ R > 0,
      (∀ z ∈ Metric.sphere z0 R, deBruijnNewmanH t z ≠ 0) ∧
      (∀ z ∈ Metric.closedBall z0 R, bound < z.im ^ 2) := by
  have hanalytic : AnalyticOnNhd ℂ (deBruijnNewmanH t) (Set.univ : Set ℂ) :=
    fun z _ ↦ (differentiable_deBruijnNewmanH t).analyticAt z
  have hnot_local_zero : ¬deBruijnNewmanH t =ᶠ[𝓝 z0] 0 := by
    intro hlocal
    have hglobal := hanalytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ z0) hlocal
    exact deBruijnNewmanH_zero_ne_zero t (hglobal (mem_univ 0))
  have hisolated : ∀ᶠ z in 𝓝[≠] z0, deBruijnNewmanH t z ≠ 0 :=
    ((hanalytic z0 (mem_univ z0)).eventually_eq_zero_or_eventually_ne_zero).resolve_left
      hnot_local_zero
  have hnear_nonzero : ∀ᶠ z in 𝓝 z0, z ≠ z0 → deBruijnNewmanH t z ≠ 0 :=
    eventually_nhdsWithin_iff.mp hisolated
  have hopen : IsOpen {z : ℂ | bound < z.im ^ 2} :=
    isOpen_lt continuous_const (Complex.continuous_im.pow 2)
  have hnear_outside : ∀ᶠ z in 𝓝 z0, bound < z.im ^ 2 :=
    hopen.mem_nhds houtside
  have hcombined : ∀ᶠ z in 𝓝 z0,
      (z ≠ z0 → deBruijnNewmanH t z ≠ 0) ∧ bound < z.im ^ 2 :=
    hnear_nonzero.and hnear_outside
  obtain ⟨R, hR, hsubset⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hcombined
  refine ⟨R, hR, ?_, ?_⟩
  · intro z hz
    exact (hsubset (Metric.sphere_subset_closedBall hz)).1
      (Metric.ne_of_mem_sphere hz hR.ne')
  · intro z hz
    exact (hsubset hz).2

/-- General source-normalized de Bruijn strip contraction from an arbitrary base heat time and
arbitrary squared strip width. -/
theorem deBruijnNewmanH_zero_im_sq_le_sub_two_mul
    {t delta muSq : ℝ} (hdelta : 0 ≤ delta)
    (hbudget : 2 * delta ≤ muSq)
    (hstrip : ∀ z : ℂ, deBruijnNewmanH t z = 0 → z.im ^ 2 ≤ muSq)
    {z : ℂ} (hz : deBruijnNewmanH (t + delta) z = 0) :
    z.im ^ 2 ≤ muSq - 2 * delta := by
  by_contra hcontracted
  have houtside : muSq - 2 * delta < z.im ^ 2 := lt_of_not_ge hcontracted
  obtain ⟨R, hR, hboundary, hball_outside⟩ :=
    exists_deBruijnNewmanH_isolating_outside_sq_strip_closedBall_general houtside
  have hpersist := eventually_exists_dbnForwardApprox_zero_mem_closedBall_of
    hdelta hR hz hboundary
  obtain ⟨n, hnzero, hnpos⟩ :=
    (hpersist.and (eventually_gt_atTop 0)).exists
  obtain ⟨w, hwball, hwzero⟩ := hnzero
  have hfinite := dbnForwardApprox_zero_im_sq_le_of
    hdelta hbudget hstrip hnpos hwzero
  exact (not_lt_of_ge hfinite) (hball_outside w hwball)

/-- If the zeros at one heat time lie in a strip of half-width `y`, then after exactly `y^2/2`
additional heat time all zeros are real. -/
theorem deBruijnNewmanAllZerosReal_add_half_sq
    {t y : ℝ} (_hy : 0 ≤ y)
    (hstrip : ∀ z : ℂ, deBruijnNewmanH t z = 0 → z.im ^ 2 ≤ y ^ 2) :
    deBruijnNewmanAllZerosReal (t + y ^ 2 / 2) := by
  intro z hz
  have hdelta : 0 ≤ y ^ 2 / 2 := by positivity
  have hbudget : 2 * (y ^ 2 / 2) ≤ y ^ 2 := by
    ring_nf
    exact le_rfl
  have hcontracted := deBruijnNewmanH_zero_im_sq_le_sub_two_mul
    hdelta hbudget hstrip hz
  have hzero : z.im ^ 2 ≤ 0 := by
    calc
      z.im ^ 2 ≤ y ^ 2 - 2 * (y ^ 2 / 2) := hcontracted
      _ = 0 := by ring
  nlinarith [sq_nonneg z.im]

end

end LeanLab.Riemann
