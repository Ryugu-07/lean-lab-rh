import LeanLab.Riemann.TruncatedPerron
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

set_option linter.style.header false

/-!
# The literal Mellin boundary for the classical Riesz function

This module isolates the ordinary-integral domain in the `k = 2` Riesz criterion.  In
particular, it records the nonzero boundary value at the origin before any use of analytic
continuation.
-/

noncomputable section

open Filter MeasureTheory Set Topology Asymptotics
open scoped ArithmeticFunction.Moebius LSeries.notation

namespace LeanLab.Riemann

/-- The coefficient `μ(n) / n²`, with the `n = 0` term set to zero. -/
def rieszTwoCoefficient (n : ℕ) : ℂ :=
  LSeries.term (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) (2 : ℂ) n

/-- The positive frequency `n⁻²`, with the harmless value zero at `n = 0`. -/
def rieszTwoFrequency (n : ℕ) : ℝ :=
  1 / (n : ℝ) ^ 2

/-- The `n`th exponential term in the classical `k = 2` Riesz function. -/
def rieszTwoSeriesTerm (x : ℝ) (n : ℕ) : ℂ :=
  rieszTwoCoefficient n * Real.exp (-(rieszTwoFrequency n * x))

/-- The classical Riesz function `P₂(x) = ∑ μ(n)n⁻² exp(-x/n²)`. -/
def rieszTwoKernel (x : ℝ) : ℂ :=
  ∑' n : ℕ, rieszTwoSeriesTerm x n

@[simp]
theorem rieszTwoCoefficient_zero : rieszTwoCoefficient 0 = 0 := by
  simp [rieszTwoCoefficient]

@[simp]
theorem rieszTwoFrequency_zero : rieszTwoFrequency 0 = 0 := by
  simp [rieszTwoFrequency]

theorem rieszTwoFrequency_pos {n : ℕ} (hn : n ≠ 0) : 0 < rieszTwoFrequency n := by
  simp only [rieszTwoFrequency, one_div, inv_pos]
  positivity

theorem norm_rieszTwoSeriesTerm_le
    {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    ‖rieszTwoSeriesTerm x n‖ ≤ ‖rieszTwoCoefficient n‖ := by
  rw [rieszTwoSeriesTerm, norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]
  have hnonpos : -(rieszTwoFrequency n * x) ≤ 0 := by
    have hfreq : 0 ≤ rieszTwoFrequency n := by
      rcases eq_or_ne n 0 with rfl | hn
      · simp
      · exact (rieszTwoFrequency_pos hn).le
    exact neg_nonpos.mpr (mul_nonneg hfreq hx)
  have hexp : Real.exp (-(rieszTwoFrequency n * x)) ≤ 1 := by
    simpa using Real.exp_le_one_iff.mpr hnonpos
  nlinarith [norm_nonneg (rieszTwoCoefficient n),
    Real.exp_pos (-(rieszTwoFrequency n * x))]

theorem summable_rieszTwoCoefficient :
    Summable (fun n : ℕ => rieszTwoCoefficient n) := by
  exact ArithmeticFunction.LSeriesSummable_moebius_iff.mpr (by norm_num)

theorem summable_norm_rieszTwoCoefficient :
    Summable (fun n : ℕ => ‖rieszTwoCoefficient n‖) := by
  exact summable_rieszTwoCoefficient.norm

theorem summable_rieszTwoSeriesTerm {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun n : ℕ => rieszTwoSeriesTerm x n) := by
  apply Summable.of_norm
  exact summable_norm_rieszTwoCoefficient.of_nonneg_of_le
    (fun n => norm_nonneg _) (norm_rieszTwoSeriesTerm_le hx)

theorem hasSum_rieszTwoSeriesTerm {x : ℝ} (hx : 0 ≤ x) :
    HasSum (fun n : ℕ => rieszTwoSeriesTerm x n) (rieszTwoKernel x) := by
  exact (summable_rieszTwoSeriesTerm hx).hasSum

theorem continuous_rieszTwoSeriesTerm (n : ℕ) :
    Continuous (fun x : ℝ => rieszTwoSeriesTerm x n) := by
  unfold rieszTwoSeriesTerm
  fun_prop

theorem continuousOn_rieszTwoKernel :
    ContinuousOn rieszTwoKernel (Ici 0) := by
  change ContinuousOn (fun x : ℝ => ∑' n : ℕ, rieszTwoSeriesTerm x n) (Ici 0)
  exact continuousOn_tsum
    (fun n => (continuous_rieszTwoSeriesTerm n).continuousOn)
    summable_norm_rieszTwoCoefficient
    (fun n x hx => norm_rieszTwoSeriesTerm_le hx n)

theorem locallyIntegrableOn_rieszTwoKernel :
    LocallyIntegrableOn rieszTwoKernel (Ioi 0) := by
  apply ContinuousOn.locallyIntegrableOn _ measurableSet_Ioi
  exact continuousOn_rieszTwoKernel.mono Ioi_subset_Ici_self

theorem rieszTwoKernel_zero_eq_LSeries :
    rieszTwoKernel 0 =
      L ↗ArithmeticFunction.moebius (2 : ℂ) := by
  rw [rieszTwoKernel, LSeries]
  apply tsum_congr
  intro n
  simp [rieszTwoSeriesTerm, rieszTwoCoefficient]

theorem rieszTwoKernel_zero :
    rieszTwoKernel 0 = (riemannZeta (2 : ℂ))⁻¹ := by
  rw [rieszTwoKernel_zero_eq_LSeries]
  exact LSeries_moebius_eq_reciprocal_riemannZeta (by norm_num)

theorem rieszTwoKernel_zero_ne : rieszTwoKernel 0 ≠ 0 := by
  rw [rieszTwoKernel_zero]
  exact inv_ne_zero (riemannZeta_ne_zero_of_one_lt_re (by norm_num))

theorem norm_rieszTwoCoefficient_div_frequency_rpow
    (s : ℂ) (n : ℕ) :
    ‖rieszTwoCoefficient n‖ / (rieszTwoFrequency n) ^ (-s).re =
      ‖LSeries.term (fun m : ℕ => (ArithmeticFunction.moebius m : ℂ))
        (2 * s + 2) n‖ := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  simp only [rieszTwoCoefficient, rieszTwoFrequency, LSeries.norm_term_eq, if_neg hn,
    Complex.neg_re, Complex.mul_re, Complex.add_re]
  norm_num
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hfreq :
      ((n : ℝ) ^ 2)⁻¹ ^ (-s.re) = (n : ℝ) ^ (2 * s.re) := by
    rw [Real.inv_rpow (sq_nonneg (n : ℝ)),
      Real.rpow_neg (sq_nonneg (n : ℝ)), inv_inv]
    rw [← Real.rpow_natCast_mul hnpos.le 2 s.re]
    norm_num
  rw [hfreq, div_div, ← Real.rpow_natCast (n : ℝ) 2, ← Real.rpow_add hnpos]
  congr 2
  ring

theorem summable_norm_rieszTwoCoefficient_div_frequency_rpow
    {s : ℂ} (hs : -(1 / 2 : ℝ) < s.re) :
    Summable
      (fun n : ℕ =>
        ‖rieszTwoCoefficient n‖ / (rieszTwoFrequency n) ^ (-s).re) := by
  rw [show
    (fun n : ℕ =>
      ‖rieszTwoCoefficient n‖ / (rieszTwoFrequency n) ^ (-s).re) =
      (fun n : ℕ =>
        ‖LSeries.term (fun m : ℕ => (ArithmeticFunction.moebius m : ℂ))
          (2 * s + 2) n‖) by
      funext n
      exact norm_rieszTwoCoefficient_div_frequency_rpow s n]
  exact
    (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr (by
      norm_num [Complex.mul_re, Complex.add_re]
      linarith)).norm

theorem rieszTwoCoefficient_div_frequency_cpow
    (s : ℂ) (n : ℕ) :
    rieszTwoCoefficient n / (rieszTwoFrequency n : ℂ) ^ (-s) =
      LSeries.term (fun m : ℕ => (ArithmeticFunction.moebius m : ℂ))
        (2 * s + 2) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  simp only [rieszTwoCoefficient, rieszTwoFrequency, LSeries.term_of_ne_zero hn]
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hbase :
      ((1 / (n : ℝ) ^ 2 : ℝ) : ℂ) = ((n : ℂ) ^ 2)⁻¹ := by
    push_cast
    simp [one_div]
  have harg : (n : ℂ).arg = 0 := by
    exact Complex.arg_ofReal_of_nonneg hnpos.le
  have hargpow : ((n : ℂ) ^ 2).arg ≠ Real.pi := by
    rw [show (n : ℂ) ^ 2 = (((n : ℝ) ^ 2 : ℝ) : ℂ) by norm_num,
      Complex.arg_ofReal_of_nonneg (sq_nonneg (n : ℝ))]
    exact Real.pi_ne_zero.symm
  have hfreq :
      ((1 / (n : ℝ) ^ 2 : ℝ) : ℂ) ^ (-s) = (n : ℂ) ^ (2 * s) := by
    rw [hbase, Complex.inv_cpow _ _ hargpow]
    rw [← Complex.cpow_nat_mul'
      (x := (n : ℂ)) (n := 2) (by simp [harg, Real.pi_pos])
      (by rw [harg]; norm_num; exact Real.pi_pos.le)
      (-s)]
    rw [show ((2 : ℕ) : ℂ) * -s = -(2 * s) by norm_num,
      Complex.cpow_neg, inv_inv]
  rw [hfreq, div_div, ← Complex.cpow_add]
  · congr 2
    ring
  · exact_mod_cast hn

theorem rieszTwoCoefficient_zero_or_frequency_pos (n : ℕ) :
    rieszTwoCoefficient n = 0 ∨ 0 < rieszTwoFrequency n := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact Or.inl rieszTwoCoefficient_zero
  · exact Or.inr (rieszTwoFrequency_pos hn)

theorem hasSum_rieszTwoExponential (t : ℝ) (ht : 0 < t) :
    HasSum
      (fun n : ℕ =>
        rieszTwoCoefficient n *
          Real.exp (-rieszTwoFrequency n * t))
      (rieszTwoKernel t) := by
  simpa only [rieszTwoSeriesTerm, neg_mul] using hasSum_rieszTwoSeriesTerm ht.le

theorem hasSum_rieszTwoMellinSeries
    {s : ℂ} (hs_left : -(1 / 2 : ℝ) < s.re) (hs_right : s.re < 0) :
    HasSum
      (fun n : ℕ =>
        Complex.Gamma (-s) *
          LSeries.term (fun m : ℕ => (ArithmeticFunction.moebius m : ℂ))
            (2 * s + 2) n)
      (mellin rieszTwoKernel (-s)) := by
  have hsource := hasSum_mellin
    (a := rieszTwoCoefficient)
    (p := rieszTwoFrequency)
    (F := rieszTwoKernel)
    (s := -s)
    rieszTwoCoefficient_zero_or_frequency_pos
    (by simpa using hs_right)
    (fun t ht => hasSum_rieszTwoExponential t ht)
    (summable_norm_rieszTwoCoefficient_div_frequency_rpow hs_left)
  simpa only [mul_div_assoc, rieszTwoCoefficient_div_frequency_cpow] using hsource

theorem mellin_rieszTwoKernel_eq
    {s : ℂ} (hs_left : -(1 / 2 : ℝ) < s.re) (hs_right : s.re < 0) :
    mellin rieszTwoKernel (-s) =
      Complex.Gamma (-s) * (riemannZeta (2 * s + 2))⁻¹ := by
  have hq : 1 < (2 * s + 2).re := by
    norm_num [Complex.mul_re, Complex.add_re]
    linarith
  have hsource := hasSum_rieszTwoMellinSeries hs_left hs_right
  have htarget :
      HasSum
        (fun n : ℕ =>
          Complex.Gamma (-s) *
            LSeries.term (fun m : ℕ => (ArithmeticFunction.moebius m : ℂ))
              (2 * s + 2) n)
        (Complex.Gamma (-s) * (riemannZeta (2 * s + 2))⁻¹) := by
    have hbase :=
      (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hq).LSeriesHasSum
    rw [LSeries_moebius_eq_reciprocal_riemannZeta hq] at hbase
    exact hbase.mul_left (Complex.Gamma (-s))
  exact hsource.unique htarget

theorem riemannZeta_mul_mellin_rieszTwoKernel
    {s : ℂ} (hs_left : -(1 / 2 : ℝ) < s.re) (hs_right : s.re < 0) :
    riemannZeta (2 * s + 2) * mellin rieszTwoKernel (-s) =
      Complex.Gamma (-s) := by
  rw [mellin_rieszTwoKernel_eq hs_left hs_right]
  have hq : 1 < (2 * s + 2).re := by
    norm_num [Complex.mul_re, Complex.add_re]
    linarith
  have hzeta := riemannZeta_ne_zero_of_one_lt_re hq
  calc
    riemannZeta (2 * s + 2) *
        (Complex.Gamma (-s) * (riemannZeta (2 * s + 2))⁻¹) =
      Complex.Gamma (-s) *
        (riemannZeta (2 * s + 2) * (riemannZeta (2 * s + 2))⁻¹) := by ring
    _ = Complex.Gamma (-s) := by rw [mul_inv_cancel₀ hzeta, mul_one]

theorem rpow_mul_exp_neg_le_one
    {a y : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hy : 0 < y) :
    y ^ a * Real.exp (-y) ≤ 1 := by
  rcases le_total y 1 with hy1 | hy1
  · calc
      y ^ a * Real.exp (-y) ≤ 1 * 1 := by
        gcongr
        · exact Real.rpow_le_one hy.le hy1 ha0
        · exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hy.le)
      _ = 1 := one_mul 1
  · have hypow : y ^ a ≤ y := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hy1 ha1
    calc
      y ^ a * Real.exp (-y) ≤ y * Real.exp (-y) := by
        gcongr
      _ ≤ Real.exp (-1) := Real.mul_exp_neg_le_exp_neg_one y
      _ ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)

theorem exp_neg_le_rpow_neg
    {a y : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hy : 0 < y) :
    Real.exp (-y) ≤ y ^ (-a) := by
  rw [Real.rpow_neg hy.le]
  rw [← one_div]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hy a)).mpr
  simpa only [mul_comm] using rpow_mul_exp_neg_le_one ha0 ha1 hy

theorem norm_rieszTwoSeriesTerm_le_rpow
    {a x : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hx : 0 < x) (n : ℕ) :
    ‖rieszTwoSeriesTerm x n‖ ≤
      (‖rieszTwoCoefficient n‖ / (rieszTwoFrequency n) ^ a) * x ^ (-a) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [rieszTwoSeriesTerm]
  have hp : 0 < rieszTwoFrequency n := rieszTwoFrequency_pos hn
  have hpx : 0 < rieszTwoFrequency n * x := mul_pos hp hx
  rw [rieszTwoSeriesTerm, norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]
  calc
    ‖rieszTwoCoefficient n‖ * Real.exp (-(rieszTwoFrequency n * x)) ≤
        ‖rieszTwoCoefficient n‖ * (rieszTwoFrequency n * x) ^ (-a) := by
      gcongr
      exact exp_neg_le_rpow_neg ha0 ha1 hpx
    _ = (‖rieszTwoCoefficient n‖ / (rieszTwoFrequency n) ^ a) * x ^ (-a) := by
      rw [Real.mul_rpow hp.le hx.le, Real.rpow_neg hp.le]
      ring

theorem summable_norm_rieszTwoCoefficient_div_frequency_rpow_real
    {a : ℝ} (ha : a < 1 / 2) :
    Summable
      (fun n : ℕ =>
        ‖rieszTwoCoefficient n‖ / (rieszTwoFrequency n) ^ a) := by
  simpa using
    (summable_norm_rieszTwoCoefficient_div_frequency_rpow
      (s := (-(a : ℂ))) (by simpa using ha))

theorem isBigO_rieszTwoKernel_rpow_atTop
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    rieszTwoKernel =O[atTop] (fun x : ℝ => x ^ (-a)) := by
  have ha1 : a ≤ 1 := by linarith
  let weight : ℕ → ℝ :=
    fun n => ‖rieszTwoCoefficient n‖ / (rieszTwoFrequency n) ^ a
  have hweight : Summable weight :=
    summable_norm_rieszTwoCoefficient_div_frequency_rpow_real ha
  rw [Asymptotics.isBigO_iff]
  refine ⟨∑' n : ℕ, weight n, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hterms : Summable (fun n : ℕ => rieszTwoSeriesTerm x n) :=
    summable_rieszTwoSeriesTerm hx.le
  calc
    ‖rieszTwoKernel x‖ =
        ‖∑' n : ℕ, rieszTwoSeriesTerm x n‖ := rfl
    _ ≤ ∑' n : ℕ, ‖rieszTwoSeriesTerm x n‖ :=
      norm_tsum_le_tsum_norm hterms.norm
    _ ≤ ∑' n : ℕ, weight n * x ^ (-a) := by
      exact hterms.norm.tsum_le_tsum
        (fun n => norm_rieszTwoSeriesTerm_le_rpow ha0 ha1 hx n)
        (hweight.mul_right (x ^ (-a)))
    _ = (∑' n : ℕ, weight n) * x ^ (-a) := by
      rw [← tsum_mul_right]
    _ = (∑' n : ℕ, weight n) * ‖x ^ (-a)‖ := by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hx.le (-a))]

theorem isBigO_rieszTwoKernel_one_atZero :
    rieszTwoKernel =O[𝓝[>] 0] (fun _x : ℝ => (1 : ℝ)) := by
  have hc : ContinuousWithinAt rieszTwoKernel (Ici 0) 0 :=
    continuousOn_rieszTwoKernel 0 (by simp)
  exact (hc.mono Ioi_subset_Ici_self).isBigO_one ℝ

theorem mellinConvergent_rieszTwoKernel_baseStrip
    {s : ℂ} (hs_left : -(1 / 2 : ℝ) < s.re) (hs_right : s.re < 0) :
    MellinConvergent rieszTwoKernel (-s) := by
  let a : ℝ := ((-s).re + 1 / 2) / 2
  have hwpos : 0 < (-s).re := by simpa using hs_right
  have hwlt : (-s).re < 1 / 2 := by
    rw [Complex.neg_re]
    linarith
  have ha0 : 0 ≤ a := by
    dsimp only [a]
    linarith
  have ha : a < 1 / 2 := by
    dsimp only [a]
    linarith
  have hwa : (-s).re < a := by
    dsimp only [a]
    linarith
  apply mellinConvergent_of_isBigO_rpow
    locallyIntegrableOn_rieszTwoKernel
    (isBigO_rieszTwoKernel_rpow_atTop ha0 ha)
    hwa
    (b := 0)
  · simpa using isBigO_rieszTwoKernel_one_atZero
  · simpa using hwpos

theorem mellinConvergent_rieszTwoKernel_of_decay
    {a : ℝ} (hdecay : rieszTwoKernel =O[atTop] (fun x : ℝ => x ^ (-a)))
    {s : ℂ} (hs_left : -a < s.re) (hs_right : s.re < 0) :
    MellinConvergent rieszTwoKernel (-s) := by
  apply mellinConvergent_of_isBigO_rpow
    locallyIntegrableOn_rieszTwoKernel hdecay (b := 0)
  · rw [Complex.neg_re]
    linarith
  · simpa using isBigO_rieszTwoKernel_one_atZero
  · simpa using hs_right

theorem mellin_differentiableAt_rieszTwoKernel_of_decay
    {a : ℝ} (hdecay : rieszTwoKernel =O[atTop] (fun x : ℝ => x ^ (-a)))
    {s : ℂ} (hs_left : -a < s.re) (hs_right : s.re < 0) :
    DifferentiableAt ℂ (mellin rieszTwoKernel) (-s) := by
  apply mellin_differentiableAt_of_isBigO_rpow
    locallyIntegrableOn_rieszTwoKernel hdecay (b := 0)
  · rw [Complex.neg_re]
    linarith
  · simpa using isBigO_rieszTwoKernel_one_atZero
  · simpa using hs_right

theorem not_mellinConvergent_rieszTwoKernel_neg_one_half :
    ¬ MellinConvergent rieszTwoKernel (-(1 / 2 : ℂ)) := by
  intro hconv
  have hc : ContinuousWithinAt rieszTwoKernel (Ioi 0) 0 :=
    (continuousOn_rieszTwoKernel 0 (by simp)).mono Ioi_subset_Ici_self
  have hnormpos : 0 < ‖rieszTwoKernel 0‖ := norm_pos_iff.mpr rieszTwoKernel_zero_ne
  let c : ℝ := ‖rieszTwoKernel 0‖ / 2
  have hcpos : 0 < c := by
    dsimp only [c]
    linarith
  have hevent :
      {x : ℝ | c < ‖rieszTwoKernel x‖} ∈ 𝓝[>] (0 : ℝ) := by
    have htend :
        Tendsto (fun x : ℝ => ‖rieszTwoKernel x‖) (𝓝[>] (0 : ℝ))
          (𝓝 ‖rieszTwoKernel 0‖) :=
      hc.norm
    exact (tendsto_order.1 htend).1 c (by
      dsimp only [c]
      linarith)
  rw [Metric.mem_nhdsWithin_iff] at hevent
  obtain ⟨delta, hdelta, hbound⟩ := hevent
  have hlocal :
      IntegrableOn
        (fun x : ℝ =>
          (x : ℂ) ^ (-(1 / 2 : ℂ) - 1) * rieszTwoKernel x)
        (Ioo 0 delta) := by
    rw [MellinConvergent] at hconv
    exact hconv.mono_set (Ioo_subset_Ioi_self)
  have hmajor :
      IntegrableOn
        (fun x : ℝ =>
          c⁻¹ * ‖(x : ℂ) ^ (-(1 / 2 : ℂ) - 1) * rieszTwoKernel x‖)
        (Ioo 0 delta) := by
    exact hlocal.norm.const_mul c⁻¹
  have hrpow :
      IntegrableOn (fun x : ℝ => x ^ (-(3 / 2 : ℝ))) (Ioo 0 delta) := by
    apply hmajor.mono'
    · exact
        (continuousOn_id.rpow_const
          (fun x hx => Or.inl hx.1.ne')).aestronglyMeasurable measurableSet_Ioo
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      have hxball : x ∈ Metric.ball (0 : ℝ) delta := by
        simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hx.1] using hx.2
      have hkernel : c ≤ ‖rieszTwoKernel x‖ := (hbound ⟨hxball, hx.1⟩).le
      have hxpow : 0 ≤ x ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hx.1.le _
      calc
        ‖x ^ (-(3 / 2 : ℝ))‖ = x ^ (-(3 / 2 : ℝ)) :=
          Real.norm_of_nonneg hxpow
        _ = c⁻¹ * (x ^ (-(3 / 2 : ℝ)) * c) := by
          field_simp [hcpos.ne']
        _ ≤ c⁻¹ * (x ^ (-(3 / 2 : ℝ)) * ‖rieszTwoKernel x‖) := by
          gcongr
        _ = c⁻¹ *
            ‖(x : ℂ) ^ (-(1 / 2 : ℂ) - 1) * rieszTwoKernel x‖ := by
          rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx.1]
          norm_num [Complex.sub_re, Complex.neg_re]
  have hexponent :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hdelta).mp hrpow
  norm_num at hexponent

/-- The complete ordinary-integral boundary certificate for the classical `k = 2` Riesz kernel. -/
structure RieszTwoMellinBoundaryCertificate : Prop where
  continuousKernel : ContinuousOn rieszTwoKernel (Ici 0)
  valueAtZero : rieszTwoKernel 0 = (riemannZeta (2 : ℂ))⁻¹
  nonzeroAtZero : rieszTwoKernel 0 ≠ 0
  subhalfDecay :
    ∀ {a : ℝ}, 0 ≤ a → a < 1 / 2 →
      rieszTwoKernel =O[atTop] (fun x : ℝ => x ^ (-a))
  literalBaseStrip :
    ∀ {s : ℂ}, -(1 / 2 : ℝ) < s.re → s.re < 0 →
      MellinConvergent rieszTwoKernel (-s) ∧
        riemannZeta (2 * s + 2) * mellin rieszTwoKernel (-s) =
          Complex.Gamma (-s)
  divergentDisplayedPoint :
    ¬ MellinConvergent rieszTwoKernel (-(1 / 2 : ℂ))
  conditionalDecayStrip :
    ∀ {a : ℝ}, rieszTwoKernel =O[atTop] (fun x : ℝ => x ^ (-a)) →
      ∀ {s : ℂ}, -a < s.re → s.re < 0 →
        MellinConvergent rieszTwoKernel (-s) ∧
          DifferentiableAt ℂ (mellin rieszTwoKernel) (-s)

theorem rieszTwoMellinBoundary_endpoint :
    RieszTwoMellinBoundaryCertificate where
  continuousKernel := continuousOn_rieszTwoKernel
  valueAtZero := rieszTwoKernel_zero
  nonzeroAtZero := rieszTwoKernel_zero_ne
  subhalfDecay := isBigO_rieszTwoKernel_rpow_atTop
  literalBaseStrip := fun hs_left hs_right =>
    ⟨mellinConvergent_rieszTwoKernel_baseStrip hs_left hs_right,
      riemannZeta_mul_mellin_rieszTwoKernel hs_left hs_right⟩
  divergentDisplayedPoint := not_mellinConvergent_rieszTwoKernel_neg_one_half
  conditionalDecayStrip := by
    intro a hdecay s hs_left hs_right
    exact
      ⟨mellinConvergent_rieszTwoKernel_of_decay hdecay hs_left hs_right,
        mellin_differentiableAt_rieszTwoKernel_of_decay hdecay hs_left hs_right⟩

end LeanLab.Riemann
