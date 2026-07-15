import LeanLab.Riemann.WeilGaussianHeight
import LeanLab.Riemann.WeilExplicitIntegrand
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The arithmetic explicit formula for the fixed xi Gaussian

This module evaluates the pole and von-Mangoldt parts of the right-half-plane contour for
`exp (a * (s - 1 / 2)^2)` and proves integrability of the real-Gamma part. The intended endpoint is
one fixed-test explicit formula; no generic test class, positivity statement, or Riemann hypothesis
is asserted.
-/

open Complex Filter Function MeasureTheory Set Topology
open scoped BigOperators Interval LSeries.notation Topology

namespace LeanLab.Riemann

noncomputable section

/-- The explicit Gaussian-smoothed von-Mangoldt prime-power weight. -/
def gaussianVonMangoldtWeight (a : ℝ) (n : ℕ) : ℂ :=
  (((Real.pi / a : ℝ) : ℂ) ^ (1 / 2 : ℂ)) *
    (ArithmeticFunction.vonMangoldt n : ℂ) *
      Complex.exp
        (-(Real.log n : ℂ) / 2 -
          (Real.log n : ℂ) ^ 2 / (4 * a))

/-- The fixed Gaussian real-place contribution on a right vertical line. -/
def gaussianXiArchimedeanIntegral (a c : ℝ) : ℂ :=
  ∫ y : ℝ,
    riemannXiGaussianWeight a ((c : ℂ) + y * I) *
      logDeriv Gammaℝ ((c : ℂ) + y * I)

/-- One von-Mangoldt L-series term after multiplication by the fixed Gaussian. -/
def gaussianXiPrimeLineTerm (a c : ℝ) (n : ℕ) (y : ℝ) : ℂ :=
  riemannXiGaussianWeight a ((c : ℂ) + y * I) *
    LSeries.term (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
      ((c : ℂ) + y * I) n

/-- The real Gamma factor logarithmic derivative in terms of the digamma function. -/
theorem logDeriv_GammaR_eq_digamma {s : ℂ} (hs : 0 < s.re) :
    logDeriv Gammaℝ s =
      -(Real.log Real.pi : ℂ) / 2 + digamma (s / 2) / 2 := by
  let A : ℂ → ℂ := fun z => (Real.pi : ℂ) ^ (-z / 2)
  let B : ℂ → ℂ := fun z => Gamma (z / 2)
  have hA : A s ≠ 0 := by
    dsimp [A]
    exact Complex.cpow_ne_zero_iff.mpr
      (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hs2 : 0 < (s / 2).re := by
    norm_num [div_re]
    linarith
  have hnotpole : ∀ m : ℕ, s / 2 ≠ -m := by
    intro m h
    have hnonpos : (-((m : ℕ) : ℂ)).re ≤ 0 := by simp
    rw [h] at hs2
    exact (not_lt_of_ge hnonpos) hs2
  have hGammaDiff : DifferentiableAt ℂ Gamma (s / 2) :=
    differentiableAt_Gamma (s / 2) hnotpole
  have hB : B s ≠ 0 := by
    dsimp [B]
    exact Gamma_ne_zero hnotpole
  have hAdiff : DifferentiableAt ℂ A s := by
    dsimp [A]
    exact ((differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow
      (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero)))
  have hHalfDiff : DifferentiableAt ℂ (fun z : ℂ => z / 2) s :=
    differentiableAt_id.div_const (2 : ℂ)
  have hBdiff : DifferentiableAt ℂ B s := by
    dsimp [B]
    exact hGammaDiff.comp s (by fun_prop)
  have hderivNegHalf : deriv (fun z : ℂ => -z / 2) s = -1 / 2 := by
    simp
  have hderivHalf : deriv (fun z : ℂ => z / 2) s = 1 / 2 := by
    simp
  have hlogA : logDeriv A s = -(Real.log Real.pi : ℂ) / 2 := by
    rw [logDeriv_apply]
    change deriv (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s / A s = _
    rw [Complex.deriv_const_cpow (by fun_prop), hderivNegHalf]
    change Complex.log (Real.pi : ℂ) * (-1 / 2) * A s / A s = _
    rw [mul_div_cancel_right₀ _ hA]
    rw [← Complex.ofReal_log Real.pi_pos.le]
    ring
  have hlogB : logDeriv B s = digamma (s / 2) / 2 := by
    change logDeriv (Gamma ∘ fun z : ℂ => z / 2) s = _
    rw [logDeriv_comp (f := Gamma) (g := fun z : ℂ => z / 2) (x := s)
      hGammaDiff hHalfDiff, hderivHalf, ← digamma_def]
    ring
  change logDeriv (fun z : ℂ => A z * B z) s = _
  rw [logDeriv_mul s hA hB hAdiff hBdiff, hlogA, hlogB]

/-- A linear factor is still integrable against a positive real Gaussian. -/
theorem integrable_one_add_abs_mul_exp_neg_mul_sq {a : ℝ} (ha : 0 < a) :
    Integrable (fun y : ℝ => (|y| + 1) * Real.exp (-a * y ^ 2)) := by
  have habs : Integrable (fun y : ℝ => |y| * Real.exp (-a * y ^ 2)) := by
    simpa [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using
      (integrable_mul_exp_neg_mul_sq ha).norm
  have hone : Integrable (fun y : ℝ => Real.exp (-a * y ^ 2)) :=
    integrable_exp_neg_mul_sq ha
  have hfun :
      (fun y : ℝ => (|y| + 1) * Real.exp (-a * y ^ 2)) =
        (fun y : ℝ => |y| * Real.exp (-a * y ^ 2) + Real.exp (-a * y ^ 2)) := by
    funext y
    ring
  rw [hfun]
  exact habs.add hone

/-- The Gaussian-weighted real-place logarithmic derivative is integrable on the full line. -/
theorem integrable_gaussianXiArchimedean
    {a c : ℝ} (ha : 0 < a) (hc : 1 < c) :
    Integrable (fun y : ℝ =>
      riemannXiGaussianWeight a ((c : ℂ) + y * I) *
        logDeriv Gammaℝ ((c : ℂ) + y * I)) := by
  have hc0 : 0 < c := lt_trans zero_lt_one hc
  obtain ⟨C, hC, hdigamma⟩ :=
    exists_norm_digamma_div_two_le_log (a := c) (b := c) hc0
  have hlog (y : ℝ) : Real.log (|y| + 2) ≤ |y| + 1 := by
    calc
      Real.log (|y| + 2) ≤ (|y| + 2) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      _ = |y| + 1 := by ring
  have hdigamma' (y : ℝ) :
      ‖digamma (((c : ℂ) + y * I) / 2)‖ ≤ C * (|y| + 1) := by
    calc
      ‖digamma (((c : ℂ) + y * I) / 2)‖ ≤ C * Real.log (|y| + 2) := by
        simpa using hdigamma ((c : ℂ) + y * I) (by simp) (by simp)
      _ ≤ C * (|y| + 1) := mul_le_mul_of_nonneg_left (hlog y) hC.le
  have hlogGamma (y : ℝ) :
      ‖-(Real.log Real.pi : ℂ) / 2 +
          digamma (((c : ℂ) + y * I) / 2) / 2‖ ≤
        (|Real.log Real.pi| + C) * (|y| + 1) := by
    calc
      ‖-(Real.log Real.pi : ℂ) / 2 +
          digamma (((c : ℂ) + y * I) / 2) / 2‖ ≤
          ‖-(Real.log Real.pi : ℂ) / 2‖ +
            ‖digamma (((c : ℂ) + y * I) / 2) / 2‖ := norm_add_le _ _
      _ = |Real.log Real.pi| / 2 +
          ‖digamma (((c : ℂ) + y * I) / 2)‖ / 2 := by
        simp [Real.norm_eq_abs]
      _ ≤ |Real.log Real.pi| / 2 + (C * (|y| + 1)) / 2 := by
        gcongr
        exact hdigamma' y
      _ ≤ (|Real.log Real.pi| + C) * (|y| + 1) := by
        nlinarith [abs_nonneg (Real.log Real.pi), abs_nonneg y,
          hC.le, mul_nonneg hC.le (by positivity : 0 ≤ |y| + 1)]
  have hweightContinuous : Continuous (fun y : ℝ =>
      riemannXiGaussianWeight a ((c : ℂ) + y * I)) := by
    unfold riemannXiGaussianWeight
    fun_prop
  have hdigammaContinuous : Continuous (fun y : ℝ =>
      digamma (((c : ℂ) + y * I) / 2)) := by
    rw [continuous_iff_continuousAt]
    intro y
    exact (continuousAt_digamma_of_re_pos (by norm_num [div_re]; linarith)).comp (by fun_prop)
  have hrewritten :
      (fun y : ℝ =>
        riemannXiGaussianWeight a ((c : ℂ) + y * I) *
          logDeriv Gammaℝ ((c : ℂ) + y * I)) =
      (fun y : ℝ =>
        riemannXiGaussianWeight a ((c : ℂ) + y * I) *
          (-(Real.log Real.pi : ℂ) / 2 +
            digamma (((c : ℂ) + y * I) / 2) / 2)) := by
    funext y
    rw [logDeriv_GammaR_eq_digamma (by
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
        mul_one, sub_self, add_zero]
      exact hc0)]
  rw [hrewritten]
  refine MeasureTheory.Integrable.mono'
    ((integrable_one_add_abs_mul_exp_neg_mul_sq ha).const_mul
      (Real.exp (a * (c - 1 / 2) ^ 2) * (|Real.log Real.pi| + C)))
    (hweightContinuous.mul
      (continuous_const.add (hdigammaContinuous.div_const (2 : ℂ)))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  rw [norm_mul, norm_riemannXiGaussianWeight]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, zero_mul, mul_im, I_re, I_im,
    mul_zero, zero_add, add_im]
  simp only [sub_self, add_zero, mul_one]
  have hsplit :
      Real.exp (a * ((c - 1 / 2) ^ 2 - y ^ 2)) =
        Real.exp (a * (c - 1 / 2) ^ 2) * Real.exp (-a * y ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hsplit]
  calc
    Real.exp (a * (c - 1 / 2) ^ 2) * Real.exp (-a * y ^ 2) *
          ‖-(Real.log Real.pi : ℂ) / 2 +
            digamma (((c : ℂ) + y * I) / 2) / 2‖ ≤
        Real.exp (a * (c - 1 / 2) ^ 2) * Real.exp (-a * y ^ 2) *
          ((|Real.log Real.pi| + C) * (|y| + 1)) := by
      gcongr
      exact hlogGamma y
    _ = Real.exp (a * (c - 1 / 2) ^ 2) * (|Real.log Real.pi| + C) *
          ((|y| + 1) * Real.exp (-a * y ^ 2)) := by ring

/-- Exact expansion of the centered Gaussian on a right vertical line. -/
theorem riemannXiGaussianWeight_vertical (a c y : ℝ) :
    riemannXiGaussianWeight a ((c : ℂ) + y * I) =
      Complex.exp
        (-(a : ℂ) * y ^ 2 +
          (2 * a * (c - 1 / 2) * I) * y +
          a * (c - 1 / 2) ^ 2) := by
  unfold riemannXiGaussianWeight
  congr 1
  ring_nf
  rw [Complex.I_sq]
  ring

/-- A positive-index L-series term is a Fourier phase times its fixed real-line value. -/
theorem vonMangoldtLSeriesTerm_vertical
    {c y : ℝ} {n : ℕ} (hn : n ≠ 0) :
    LSeries.term (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
        ((c : ℂ) + y * I) n =
      (ArithmeticFunction.vonMangoldt n : ℂ) *
        Complex.exp
          (-((c : ℂ) + y * I) * (Real.log n : ℂ)) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [LSeries.term_of_ne_zero hn, Complex.cpow_def_of_ne_zero hnC]
  rw [← Complex.natCast_log]
  rw [div_eq_mul_inv, ← Complex.exp_neg]
  congr 1
  ring

/-- Exact quadratic-exponential form of one positive-index prime-line term. -/
theorem gaussianXiPrimeLineTerm_vertical
    {a c : ℝ} {n : ℕ} (hn : n ≠ 0) (y : ℝ) :
    gaussianXiPrimeLineTerm a c n y =
      (ArithmeticFunction.vonMangoldt n : ℂ) *
        Complex.exp
          (-(a : ℂ) * y ^ 2 +
            (((2 * a * (c - 1 / 2) - Real.log n : ℝ) : ℂ) * I) * y +
            (a * (c - 1 / 2) ^ 2 - c * Real.log n : ℝ)) := by
  rw [gaussianXiPrimeLineTerm, riemannXiGaussianWeight_vertical,
    vonMangoldtLSeriesTerm_vertical hn]
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The full right-line integral of one von-Mangoldt term is its explicit Gaussian weight. -/
theorem integral_gaussianXiPrimeLineTerm
    {a c : ℝ} (ha : 0 < a) (n : ℕ) :
    (∫ y : ℝ, gaussianXiPrimeLineTerm a c n y) =
      gaussianVonMangoldtWeight a n := by
  by_cases hn : n = 0
  · subst n
    simp [gaussianXiPrimeLineTerm, gaussianVonMangoldtWeight, LSeries.term_zero]
  simp_rw [gaussianXiPrimeLineTerm_vertical hn]
  rw [MeasureTheory.integral_const_mul]
  have haC : (-(a : ℂ)).re < 0 := by simpa using ha
  rw [integral_cexp_quadratic haC]
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hexp :
      ((a * (c - 1 / 2) ^ 2 - c * Real.log n : ℝ) : ℂ) -
          ((((2 * a * (c - 1 / 2) - Real.log n : ℝ) : ℂ) * I) ^ 2) /
            (4 * (-(a : ℂ))) =
        -(Real.log n : ℂ) / 2 - (Real.log n : ℂ) ^ 2 / (4 * a) := by
    field_simp [ha0]
    rw [Complex.I_sq]
    push_cast
    ring
  rw [hexp]
  unfold gaussianVonMangoldtWeight
  simp only [neg_neg]
  push_cast
  ring

/-- Exact separated norm: Gaussian decay in height times the fixed `c`-line L-series norm. -/
theorem norm_gaussianXiPrimeLineTerm (a c : ℝ) (n : ℕ) (y : ℝ) :
    ‖gaussianXiPrimeLineTerm a c n y‖ =
      Real.exp (a * (c - 1 / 2) ^ 2) * Real.exp (-a * y ^ 2) *
        ‖LSeries.term (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ)) (c : ℂ) n‖ := by
  unfold gaussianXiPrimeLineTerm
  rw [norm_mul, norm_riemannXiGaussianWeight]
  have hterm :
      ‖LSeries.term (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
          ((c : ℂ) + y * I) n‖ =
        ‖LSeries.term (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
          (c : ℂ) n‖ := by
    simp [LSeries.norm_term_eq]
  rw [hterm, ← Real.exp_add]
  congr 2
  simp only [add_re, ofReal_re, mul_re, ofReal_im, zero_mul, mul_im, I_re, I_im,
    mul_zero, zero_add, add_im]
  ring

/-- Every individual Gaussian prime-line term is Bochner integrable. -/
theorem integrable_gaussianXiPrimeLineTerm
    {a c : ℝ} (ha : 0 < a) (n : ℕ) :
    Integrable (gaussianXiPrimeLineTerm a c n) := by
  by_cases hn : n = 0
  · subst n
    have hzero : gaussianXiPrimeLineTerm a c 0 = 0 := by
      funext y
      simp [gaussianXiPrimeLineTerm, LSeries.term_zero]
    rw [hzero]
    exact MeasureTheory.integrable_zero ℝ ℂ volume
  rw [show gaussianXiPrimeLineTerm a c n = fun y : ℝ =>
      (ArithmeticFunction.vonMangoldt n : ℂ) *
        Complex.exp
          (-(a : ℂ) * y ^ 2 +
            (((2 * a * (c - 1 / 2) - Real.log n : ℝ) : ℂ) * I) * y +
            (a * (c - 1 / 2) ^ 2 - c * Real.log n : ℝ)) from
      funext (gaussianXiPrimeLineTerm_vertical hn)]
  exact (integrable_cexp_quadratic' (by simpa using ha)
    (((2 * a * (c - 1 / 2) - Real.log n : ℝ) : ℂ) * I)
    (a * (c - 1 / 2) ^ 2 - c * Real.log n : ℝ)).const_mul _

/-- The integral of the norm factors into a fixed Gaussian constant and an L-series term norm. -/
theorem integral_norm_gaussianXiPrimeLineTerm
    {a c : ℝ} (_ha : 0 < a) (n : ℕ) :
    (∫ y : ℝ, ‖gaussianXiPrimeLineTerm a c n y‖) =
      Real.exp (a * (c - 1 / 2) ^ 2) * Real.sqrt (Real.pi / a) *
        ‖LSeries.term (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ)) (c : ℂ) n‖ := by
  simp_rw [norm_gaussianXiPrimeLineTerm, mul_assoc]
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const,
    integral_gaussian]

/-- The integrals of the prime-line term norms are summable when `c > 1`. -/
theorem summable_integral_norm_gaussianXiPrimeLineTerm
    {a c : ℝ} (ha : 0 < a) (hc : 1 < c) :
    Summable (fun n : ℕ => ∫ y : ℝ, ‖gaussianXiPrimeLineTerm a c n y‖) := by
  simp_rw [integral_norm_gaussianXiPrimeLineTerm ha]
  exact Summable.mul_left
    (Real.exp (a * (c - 1 / 2) ^ 2) * Real.sqrt (Real.pi / a))
    (ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hc)).norm

/-- Absolute convergence justifies exchanging the fixed Gaussian prime sum and full-line integral. -/
theorem hasSum_integral_gaussianXiPrimeLineTerm
    {a c : ℝ} (ha : 0 < a) (hc : 1 < c) :
    HasSum (fun n : ℕ => gaussianVonMangoldtWeight a n)
      (∫ y : ℝ, ∑' n : ℕ, gaussianXiPrimeLineTerm a c n y) := by
  refine (MeasureTheory.hasSum_integral_of_summable_integral_norm
    (fun n : ℕ => integrable_gaussianXiPrimeLineTerm ha n)
    (summable_integral_norm_gaussianXiPrimeLineTerm ha hc)).congr_fun ?_
  intro n
  exact (integral_gaussianXiPrimeLineTerm ha n).symm

/-- The pointwise prime-line sum is the Gaussian times the von-Mangoldt L-series. -/
theorem tsum_gaussianXiPrimeLineTerm (a c y : ℝ) :
    (∑' n : ℕ, gaussianXiPrimeLineTerm a c n y) =
      riemannXiGaussianWeight a ((c : ℂ) + y * I) *
        L ↗ArithmeticFunction.vonMangoldt ((c : ℂ) + y * I) := by
  unfold gaussianXiPrimeLineTerm LSeries
  exact tsum_mul_left

/-- The explicit Gaussian von-Mangoldt series is summable for every positive width. -/
theorem summable_gaussianVonMangoldtWeight
    {a c : ℝ} (ha : 0 < a) (hc : 1 < c) :
    Summable (gaussianVonMangoldtWeight a) :=
  (hasSum_integral_gaussianXiPrimeLineTerm ha hc).summable

/-- The full Gaussian prime integral is exactly the explicit von-Mangoldt prime-power sum. -/
theorem tsum_gaussianVonMangoldtWeight_eq_integral
    {a c : ℝ} (ha : 0 < a) (hc : 1 < c) :
    (∑' n : ℕ, gaussianVonMangoldtWeight a n) =
      ∫ y : ℝ,
        riemannXiGaussianWeight a ((c : ℂ) + y * I) *
          L ↗ArithmeticFunction.vonMangoldt ((c : ℂ) + y * I) := by
  calc
    (∑' n : ℕ, gaussianVonMangoldtWeight a n) =
        ∫ y : ℝ, ∑' n : ℕ, gaussianXiPrimeLineTerm a c n y :=
      (hasSum_integral_gaussianXiPrimeLineTerm ha hc).tsum_eq
    _ = ∫ y : ℝ,
          riemannXiGaussianWeight a ((c : ℂ) + y * I) *
            L ↗ArithmeticFunction.vonMangoldt ((c : ℂ) + y * I) := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall (tsum_gaussianXiPrimeLineTerm a c)

/-- The full Gaussian times von-Mangoldt L-series is itself Bochner integrable. -/
theorem integrable_gaussianXi_mul_vonMangoldtLSeries
    {a c : ℝ} (ha : 0 < a) (hc : 1 < c) :
    Integrable (fun y : ℝ =>
      riemannXiGaussianWeight a ((c : ℂ) + y * I) *
        L ↗ArithmeticFunction.vonMangoldt ((c : ℂ) + y * I)) := by
  let S : ℝ := ∑' n : ℕ,
    ‖LSeries.term (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ)) (c : ℂ) n‖
  have htermsMeasurable : ∀ n : ℕ,
      AEStronglyMeasurable (gaussianXiPrimeLineTerm a c n) := fun n =>
    (integrable_gaussianXiPrimeLineTerm ha n).aestronglyMeasurable
  have htsumMeasurable : AEStronglyMeasurable
      (fun y : ℝ => ∑' n : ℕ, gaussianXiPrimeLineTerm a c n y) :=
    MeasureTheory.AEStronglyMeasurable.tsum htermsMeasurable
  have hpoint (y : ℝ) :
      ‖∑' n : ℕ, gaussianXiPrimeLineTerm a c n y‖ ≤
        Real.exp (a * (c - 1 / 2) ^ 2) * S * Real.exp (-a * y ^ 2) := by
    have hsum : Summable (fun n : ℕ => gaussianXiPrimeLineTerm a c n y) := by
      unfold gaussianXiPrimeLineTerm
      exact Summable.mul_left _
        (ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hc))
    calc
      ‖∑' n : ℕ, gaussianXiPrimeLineTerm a c n y‖ ≤
          ∑' n : ℕ, ‖gaussianXiPrimeLineTerm a c n y‖ :=
        norm_tsum_le_tsum_norm hsum.norm
      _ = ∑' n : ℕ,
          (Real.exp (a * (c - 1 / 2) ^ 2) * Real.exp (-a * y ^ 2)) *
            ‖LSeries.term (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
              (c : ℂ) n‖ := by
        congr 1
        funext n
        rw [norm_gaussianXiPrimeLineTerm]
      _ = (Real.exp (a * (c - 1 / 2) ^ 2) * Real.exp (-a * y ^ 2)) * S :=
        tsum_mul_left
      _ = Real.exp (a * (c - 1 / 2) ^ 2) * S * Real.exp (-a * y ^ 2) := by ring
  have htsumIntegrable : Integrable
      (fun y : ℝ => ∑' n : ℕ, gaussianXiPrimeLineTerm a c n y) := by
    refine MeasureTheory.Integrable.mono'
      ((integrable_exp_neg_mul_sq ha).const_mul
        (Real.exp (a * (c - 1 / 2) ^ 2) * S))
      htsumMeasurable (Filter.Eventually.of_forall hpoint)
  rw [show (fun y : ℝ =>
      riemannXiGaussianWeight a ((c : ℂ) + y * I) *
        L ↗ArithmeticFunction.vonMangoldt ((c : ℂ) + y * I)) =
      (fun y : ℝ => ∑' n : ℕ, gaussianXiPrimeLineTerm a c n y) by
    funext y
    exact (tsum_gaussianXiPrimeLineTerm a c y).symm]
  exact htsumIntegrable

/-- The two elementary pole terms weighted by the centered xi Gaussian. -/
def gaussianXiPolePairIntegrand (a : ℝ) (z : ℂ) : ℂ :=
  riemannXiGaussianWeight a z / (z - 0) +
    riemannXiGaussianWeight a z / (z - 1)

/-- The pole-pair integral along a selected top horizontal edge. -/
noncomputable def gaussianXiPoleTopHorizontalIntegral (a c : ℝ) (n : ℕ) : ℂ :=
  ∫ x : ℝ in 1 - c..c,
    gaussianXiPolePairIntegrand a
      ((x : ℂ) + gaussianXiSelectedHeight c n * I)

/-- The pole-pair integral along a selected right vertical edge. -/
noncomputable def gaussianXiPoleRightVerticalIntegral (a c : ℝ) (n : ℕ) : ℂ :=
  ∫ y : ℝ in -gaussianXiSelectedHeight c n..gaussianXiSelectedHeight c n,
    gaussianXiPolePairIntegrand a ((c : ℂ) + y * I)

/-- The pole pair is odd under the same reflection that fixes the centered Gaussian. -/
theorem gaussianXiPolePairIntegrand_one_sub (a : ℝ) (z : ℂ) :
    gaussianXiPolePairIntegrand a (1 - z) = -gaussianXiPolePairIntegrand a z := by
  unfold gaussianXiPolePairIntegrand
  rw [riemannXiGaussianWeight_one_sub]
  have hzero : (1 : ℂ) - z - 0 = -(z - 1) := by ring
  have hone : (1 : ℂ) - z - 1 = -(z - 0) := by ring
  rw [hzero, hone, div_neg, div_neg]
  ring

/-- Reflection identifies the selected bottom pole-pair integral with the negative top one. -/
theorem gaussianXiPoleBottomHorizontalIntegral_eq_neg_top
    (a c : ℝ) (n : ℕ) :
    (∫ x : ℝ in 1 - c..c,
      gaussianXiPolePairIntegrand a
        ((x : ℂ) - gaussianXiSelectedHeight c n * I)) =
      -gaussianXiPoleTopHorizontalIntegral a c n := by
  let T : ℝ := gaussianXiSelectedHeight c n
  let f : ℝ → ℂ := fun x =>
    gaussianXiPolePairIntegrand a ((x : ℂ) + T * I)
  have hpoint (x : ℝ) :
      gaussianXiPolePairIntegrand a ((x : ℂ) - T * I) = -f (1 - x) := by
    have href := gaussianXiPolePairIntegrand_one_sub a ((x : ℂ) - T * I)
    have harg : (1 : ℂ) - ((x : ℂ) - T * I) = ((1 - x : ℝ) : ℂ) + T * I := by
      push_cast
      ring
    rw [harg] at href
    simpa only [f, neg_neg, Complex.ofReal_neg] using (congrArg Neg.neg href).symm
  calc
    (∫ x : ℝ in 1 - c..c,
      gaussianXiPolePairIntegrand a ((x : ℂ) - T * I)) =
        ∫ x : ℝ in 1 - c..c, -f (1 - x) := by
      apply intervalIntegral.integral_congr
      intro x _hx
      exact hpoint x
    _ = -(∫ x : ℝ in 1 - c..c, f (1 - x)) := by
      rw [intervalIntegral.integral_neg]
    _ = -(∫ x : ℝ in 1 - c..c, f x) := by
      rw [intervalIntegral.integral_comp_sub_left f 1]
      congr 2
      all_goals ring
    _ = -gaussianXiPoleTopHorizontalIntegral a c n := by rfl

/-- Reflection and ordinate reversal identify the selected left and right pole-pair integrals. -/
theorem gaussianXiPoleLeftVerticalIntegral_eq_neg_right
    (a c : ℝ) (n : ℕ) :
    (∫ y : ℝ in -gaussianXiSelectedHeight c n..gaussianXiSelectedHeight c n,
      gaussianXiPolePairIntegrand a (((1 - c : ℝ) : ℂ) + y * I)) =
      -gaussianXiPoleRightVerticalIntegral a c n := by
  let T : ℝ := gaussianXiSelectedHeight c n
  let f : ℝ → ℂ := fun y =>
    gaussianXiPolePairIntegrand a ((c : ℂ) + y * I)
  have hpoint (y : ℝ) :
      gaussianXiPolePairIntegrand a (((1 - c : ℝ) : ℂ) + y * I) = -f (-y) := by
    have href := gaussianXiPolePairIntegrand_one_sub a
      (((1 - c : ℝ) : ℂ) + y * I)
    have harg : (1 : ℂ) - (((1 - c : ℝ) : ℂ) + y * I) =
        (c : ℂ) + (-y) * I := by
      push_cast
      ring
    rw [harg] at href
    simpa only [f, neg_neg, Complex.ofReal_neg] using (congrArg Neg.neg href).symm
  calc
    (∫ y : ℝ in -T..T,
      gaussianXiPolePairIntegrand a (((1 - c : ℝ) : ℂ) + y * I)) =
        ∫ y : ℝ in -T..T, -f (-y) := by
      apply intervalIntegral.integral_congr
      intro y _hy
      exact hpoint y
    _ = -(∫ y : ℝ in -T..T, f (-y)) := by
      rw [intervalIntegral.integral_neg]
    _ = -(∫ y : ℝ in -T..T, f y) := by
      simpa only [zero_sub, neg_neg] using congrArg Neg.neg
        (intervalIntegral.integral_comp_sub_left (a := -T) (b := T) f 0)
    _ = -gaussianXiPoleRightVerticalIntegral a c n := by rfl

/-- Reflection reduces the pole-pair rectangle boundary to its selected top and right edges. -/
theorem gaussianXiPoleRectangleBoundary_eq_top_right
    (a c : ℝ) (n : ℕ) :
    rectangleBoundaryIntegral (gaussianXiPolePairIntegrand a)
        (1 - c) c (-gaussianXiSelectedHeight c n) (gaussianXiSelectedHeight c n) =
      -2 * gaussianXiPoleTopHorizontalIntegral a c n +
        2 * I * gaussianXiPoleRightVerticalIntegral a c n := by
  let T : ℝ := gaussianXiSelectedHeight c n
  rw [rectangleBoundaryIntegral]
  simp only [Complex.ofReal_neg]
  rw [show (∫ x : ℝ in 1 - c..c,
      gaussianXiPolePairIntegrand a ((x : ℂ) + (-T) * I)) =
        -gaussianXiPoleTopHorizontalIntegral a c n by
      simpa only [T, neg_mul, sub_eq_add_neg] using
        gaussianXiPoleBottomHorizontalIntegral_eq_neg_top a c n]
  rw [show (∫ x : ℝ in 1 - c..c,
      gaussianXiPolePairIntegrand a ((x : ℂ) + T * I)) =
        gaussianXiPoleTopHorizontalIntegral a c n by rfl]
  rw [show (∫ y : ℝ in -T..T,
      gaussianXiPolePairIntegrand a ((c : ℂ) + y * I)) =
        gaussianXiPoleRightVerticalIntegral a c n by rfl]
  rw [show (∫ y : ℝ in -T..T,
      gaussianXiPolePairIntegrand a (((1 - c : ℝ) : ℂ) + y * I)) =
        -gaussianXiPoleRightVerticalIntegral a c n by
      exact gaussianXiPoleLeftVerticalIntegral_eq_neg_right a c n]
  ring

/-- The centered xi Gaussian has the same real value at both elementary poles. -/
theorem riemannXiGaussianWeight_zero (a : ℝ) :
    riemannXiGaussianWeight a 0 = (Real.exp (a / 4) : ℂ) := by
  unfold riemannXiGaussianWeight
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

theorem riemannXiGaussianWeight_one (a : ℝ) :
    riemannXiGaussianWeight a 1 = (Real.exp (a / 4) : ℂ) := by
  rw [show (1 : ℂ) = 1 - 0 by ring, riemannXiGaussianWeight_one_sub,
    riemannXiGaussianWeight_zero]

/-- The selected symmetric rectangle encloses both elementary poles, each with Gaussian residue
`exp (a / 4)`. -/
theorem gaussianXiPoleRectangleBoundary_eq_residues
    {a c : ℝ} (hc : 1 < c) (n : ℕ) :
    rectangleBoundaryIntegral (gaussianXiPolePairIntegrand a)
        (1 - c) c (-gaussianXiSelectedHeight c n) (gaussianXiSelectedHeight c n) =
      4 * (Real.pi : ℂ) * I * (Real.exp (a / 4) : ℂ) := by
  let F : ℂ → ℂ := riemannXiGaussianWeight a
  let T : ℝ := gaussianXiSelectedHeight c n
  have hF : Differentiable ℂ F := differentiable_riemannXiGaussianWeight a
  have hT : 0 < T := lt_trans (gaussianXiHeightScale_pos hc n)
    (gaussianXiSelectedHeight_spec c n).1.1
  have hbottom (rho : ℂ) (him : rho.im = 0) :
      IntervalIntegrable (fun x : ℝ => F ((x : ℂ) + ((-T : ℝ) : ℂ) * I) /
        ((x : ℂ) + ((-T : ℝ) : ℂ) * I - rho)) volume (1 - c) c := by
    apply intervalIntegrable_weighted_cauchyKernel_of_avoids hF (by fun_prop)
    intro x _hx heq
    have hi := congrArg Complex.im heq
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero,
      mul_one, zero_add, Complex.ofReal_neg, neg_re] at hi
    rw [him] at hi
    linarith
  have htop (rho : ℂ) (him : rho.im = 0) :
      IntervalIntegrable (fun x : ℝ => F ((x : ℂ) + T * I) /
        ((x : ℂ) + T * I - rho)) volume (1 - c) c := by
    apply intervalIntegrable_weighted_cauchyKernel_of_avoids hF (by fun_prop)
    intro x _hx heq
    have hi := congrArg Complex.im heq
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero,
      mul_one, zero_add] at hi
    rw [him] at hi
    linarith
  have hright (rho : ℂ) (hre : rho.re < c) :
      IntervalIntegrable (fun y : ℝ => F ((c : ℂ) + y * I) /
        ((c : ℂ) + y * I - rho)) volume (-T) T := by
    apply intervalIntegrable_weighted_cauchyKernel_of_avoids hF (by fun_prop)
    intro y _hy heq
    have hr := congrArg Complex.re heq
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
      zero_mul] at hr
    linarith
  have hleft (rho : ℂ) (hre : 1 - c < rho.re) :
      IntervalIntegrable (fun y : ℝ => F (((1 - c : ℝ) : ℂ) + y * I) /
        (((1 - c : ℝ) : ℂ) + y * I - rho)) volume (-T) T := by
    apply intervalIntegrable_weighted_cauchyKernel_of_avoids hF (by fun_prop)
    intro y _hy heq
    have hr := congrArg Complex.re heq
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
      zero_mul] at hr
    linarith
  have hadd :
      rectangleBoundaryIntegral
          (fun z : ℂ => F z / (z - 0) + F z / (z - 1))
          (1 - c) c (-T) T =
        rectangleBoundaryIntegral (fun z : ℂ => F z / (z - 0))
            (1 - c) c (-T) T +
          rectangleBoundaryIntegral (fun z : ℂ => F z / (z - 1))
            (1 - c) c (-T) T := by
    apply rectangleBoundaryIntegral_add
    · exact hbottom 0 (by simp)
    · exact hbottom 1 (by simp)
    · exact htop 0 (by simp)
    · exact htop 1 (by simp)
    · exact hright 0 (by simp; linarith)
    · exact hright 1 (by simp; linarith)
    · exact hleft 0 (by simp; linarith)
    · exact hleft 1 (by simp; linarith)
  have hres0 :
      rectangleBoundaryIntegral (fun z : ℂ => F z / (z - 0))
          (1 - c) c (-T) T = 2 * (Real.pi : ℂ) * I * F 0 := by
    apply rectangleBoundaryIntegral_weighted_cauchyKernel hF
    all_goals norm_num
    all_goals linarith
  have hres1 :
      rectangleBoundaryIntegral (fun z : ℂ => F z / (z - 1))
          (1 - c) c (-T) T = 2 * (Real.pi : ℂ) * I * F 1 := by
    apply rectangleBoundaryIntegral_weighted_cauchyKernel hF
    all_goals norm_num
    all_goals linarith
  change rectangleBoundaryIntegral
      (fun z : ℂ => F z / (z - 0) + F z / (z - 1))
        (1 - c) c (-T) T = _
  rw [hadd, hres0, hres1]
  dsimp only [F]
  rw [riemannXiGaussianWeight_zero, riemannXiGaussianWeight_one]
  ring

/-- A horizontal line of height at least one keeps either real elementary pole at inverse norm at
most one. -/
theorem norm_inv_horizontal_sub_real_le_one
    {x T rho : ℝ} (hT : 1 ≤ T) :
    ‖(((x : ℂ) + T * I) - (rho : ℂ))⁻¹‖ ≤ 1 := by
  rw [norm_inv]
  apply inv_le_one_of_one_le₀
  calc
    1 ≤ T := hT
    _ = |(((x : ℂ) + T * I) - (rho : ℂ)).im| := by
      simp [abs_of_nonneg (by linarith : 0 ≤ T)]
    _ ≤ ‖((x : ℂ) + T * I) - (rho : ℂ)‖ := Complex.abs_im_le_norm _

/-- The pole pair costs at most a factor two on a horizontal line above height one. -/
theorem norm_gaussianXiPolePairIntegrand_horizontal_le
    {a x T : ℝ} (hT : 1 ≤ T) :
    ‖gaussianXiPolePairIntegrand a ((x : ℂ) + T * I)‖ ≤
      2 * ‖riemannXiGaussianWeight a ((x : ℂ) + T * I)‖ := by
  unfold gaussianXiPolePairIntegrand
  simp only [sub_zero, div_eq_mul_inv]
  calc
    ‖riemannXiGaussianWeight a ((x : ℂ) + T * I) * ((x : ℂ) + T * I)⁻¹ +
        riemannXiGaussianWeight a ((x : ℂ) + T * I) *
          ((x : ℂ) + T * I - 1)⁻¹‖ ≤
        ‖riemannXiGaussianWeight a ((x : ℂ) + T * I) *
          ((x : ℂ) + T * I)⁻¹‖ +
        ‖riemannXiGaussianWeight a ((x : ℂ) + T * I) *
          ((x : ℂ) + T * I - 1)⁻¹‖ := norm_add_le _ _
    _ = ‖riemannXiGaussianWeight a ((x : ℂ) + T * I)‖ *
          ‖((x : ℂ) + T * I)⁻¹‖ +
        ‖riemannXiGaussianWeight a ((x : ℂ) + T * I)‖ *
          ‖((x : ℂ) + T * I - 1)⁻¹‖ := by rw [norm_mul, norm_mul]
    _ ≤ ‖riemannXiGaussianWeight a ((x : ℂ) + T * I)‖ * 1 +
        ‖riemannXiGaussianWeight a ((x : ℂ) + T * I)‖ * 1 := by
      gcongr
      · simpa using norm_inv_horizontal_sub_real_le_one (rho := 0) hT
      · simpa using norm_inv_horizontal_sub_real_le_one (rho := 1) hT
    _ = 2 * ‖riemannXiGaussianWeight a ((x : ℂ) + T * I)‖ := by ring

/-- A polynomially padded Gaussian bound for the selected pole-pair top edge. -/
theorem norm_gaussianXiPoleTopHorizontalIntegral_le
    {a c : ℝ} (ha : 0 < a) (hc : 1 < c) (n : ℕ) :
    ‖gaussianXiPoleTopHorizontalIntegral a c n‖ ≤
      (2 * (2 * c - 1) * Real.exp (a * (c - 1 / 2) ^ 2)) *
        (gaussianXiHeightScale c n ^ 4 *
          Real.exp (-a * gaussianXiHeightScale c n ^ 2)) := by
  let R : ℝ := gaussianXiHeightScale c n
  let T : ℝ := gaussianXiSelectedHeight c n
  have hRone : 1 ≤ R := by
    dsimp only [R, gaussianXiHeightScale]
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hTone : 1 ≤ T := hRone.trans (gaussianXiSelectedHeight_spec c n).1.1.le
  have hRfour : 1 ≤ R ^ 4 := one_le_pow₀ hRone
  have hpoint : ∀ x ∈ Ι (1 - c) c,
      ‖gaussianXiPolePairIntegrand a ((x : ℂ) + T * I)‖ ≤
        2 * Real.exp (a * (c - 1 / 2) ^ 2) *
          (R ^ 4 * Real.exp (-a * R ^ 2)) := by
    intro x hx
    calc
      ‖gaussianXiPolePairIntegrand a ((x : ℂ) + T * I)‖ ≤
          2 * ‖riemannXiGaussianWeight a ((x : ℂ) + T * I)‖ :=
        norm_gaussianXiPolePairIntegrand_horizontal_le hTone
      _ ≤ 2 * (Real.exp (a * (c - 1 / 2) ^ 2) *
          Real.exp (-a * R ^ 2)) := by
        gcongr
        simpa only [T, R] using norm_riemannXiGaussianWeight_selectedTopEdge_le
          ha hc n (Set.uIoc_subset_uIcc hx)
      _ ≤ 2 * Real.exp (a * (c - 1 / 2) ^ 2) *
          (R ^ 4 * Real.exp (-a * R ^ 2)) := by
        have hdecay : Real.exp (-a * R ^ 2) ≤ R ^ 4 * Real.exp (-a * R ^ 2) :=
          le_mul_of_one_le_left (Real.exp_pos _).le hRfour
        nlinarith [Real.exp_pos (a * (c - 1 / 2) ^ 2)]
  have hintegral := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  rw [gaussianXiPoleTopHorizontalIntegral]
  calc
    ‖∫ x : ℝ in 1 - c..c,
        gaussianXiPolePairIntegrand a ((x : ℂ) + T * I)‖ ≤
        (2 * Real.exp (a * (c - 1 / 2) ^ 2) *
          (R ^ 4 * Real.exp (-a * R ^ 2))) * |c - (1 - c)| := hintegral
    _ = (2 * (2 * c - 1) * Real.exp (a * (c - 1 / 2) ^ 2)) *
        (gaussianXiHeightScale c n ^ 4 *
          Real.exp (-a * gaussianXiHeightScale c n ^ 2)) := by
      rw [abs_of_pos (by linarith : 0 < c - (1 - c))]
      dsimp only [R]
      ring

/-- Gaussian decay forces the selected pole-pair top edge to vanish. -/
theorem tendsto_gaussianXiPoleTopHorizontalIntegral
    {a c : ℝ} (ha : 0 < a) (hc : 1 < c) :
    Tendsto (gaussianXiPoleTopHorizontalIntegral a c) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n => norm_nonneg _
  · exact Filter.Eventually.of_forall fun n =>
      norm_gaussianXiPoleTopHorizontalIntegral_le ha hc n
  · simpa using
      (tendsto_gaussianXiHeightScale_pow_four_mul_exp_neg_sq
        (a := a) (c := c) ha).const_mul
          (2 * (2 * c - 1) * Real.exp (a * (c - 1 / 2) ^ 2))

/-- The finite pole-pair rectangle identity solved for its selected right vertical edge. -/
theorem gaussianXiPoleRightVerticalIntegral_eq_top_add_residues
    {a c : ℝ} (hc : 1 < c) (n : ℕ) :
    gaussianXiPoleRightVerticalIntegral a c n =
      -I * gaussianXiPoleTopHorizontalIntegral a c n +
        2 * (Real.pi : ℂ) * (Real.exp (a / 4) : ℂ) := by
  have hres := gaussianXiPoleRectangleBoundary_eq_residues (a := a) hc n
  rw [gaussianXiPoleRectangleBoundary_eq_top_right] at hres
  apply mul_left_cancel₀ (show (2 : ℂ) * I ≠ 0 by simp)
  calc
    ((2 : ℂ) * I) * gaussianXiPoleRightVerticalIntegral a c n =
        2 * gaussianXiPoleTopHorizontalIntegral a c n +
          4 * (Real.pi : ℂ) * I * (Real.exp (a / 4) : ℂ) := by
      linear_combination hres
    _ = ((2 : ℂ) * I) *
        (-I * gaussianXiPoleTopHorizontalIntegral a c n +
          2 * (Real.pi : ℂ) * (Real.exp (a / 4) : ℂ)) := by
      ring_nf
      rw [Complex.I_sq]
      ring

/-- The selected right pole-pair integrals converge to the exact two-residue contribution. -/
theorem tendsto_gaussianXiPoleRightVerticalIntegral
    {a c : ℝ} (ha : 0 < a) (hc : 1 < c) :
    Tendsto (gaussianXiPoleRightVerticalIntegral a c) atTop
      (𝓝 (2 * (Real.pi : ℂ) * (Real.exp (a / 4) : ℂ))) := by
  have htop := (tendsto_gaussianXiPoleTopHorizontalIntegral ha hc).const_mul (-I)
  have hconst : Tendsto
      (fun _ : ℕ => 2 * (Real.pi : ℂ) * (Real.exp (a / 4) : ℂ)) atTop
      (𝓝 (2 * (Real.pi : ℂ) * (Real.exp (a / 4) : ℂ))) := tendsto_const_nhds
  have hsum := htop.add hconst
  simpa only [mul_zero, zero_add] using hsum.congr' (Filter.Eventually.of_forall fun n =>
    (gaussianXiPoleRightVerticalIntegral_eq_top_add_residues hc n).symm)

/-- On a right vertical line, distance from a real pole controls the inverse denominator. -/
theorem norm_inv_vertical_sub_real_le
    {c rho y : ℝ} (hcrho : 0 < c - rho) :
    ‖(((c : ℂ) + y * I) - (rho : ℂ))⁻¹‖ ≤ (c - rho)⁻¹ := by
  have hre : (((c : ℂ) + y * I) - (rho : ℂ)).re = c - rho := by simp
  have hnorm : c - rho ≤ ‖((c : ℂ) + y * I) - (rho : ℂ)‖ := by
    calc
      c - rho = |(((c : ℂ) + y * I) - (rho : ℂ)).re| := by
        rw [hre, abs_of_pos hcrho]
      _ ≤ ‖((c : ℂ) + y * I) - (rho : ℂ)‖ := Complex.abs_re_le_norm _
  rw [norm_inv]
  exact (inv_le_inv₀ (lt_of_lt_of_le hcrho hnorm) hcrho).2 hnorm

/-- A fixed right-line pole pair is bounded by a constant times the line Gaussian. -/
theorem norm_gaussianXiPolePairIntegrand_vertical_le
    {a c : ℝ} (hc : 1 < c) (y : ℝ) :
    ‖gaussianXiPolePairIntegrand a ((c : ℂ) + y * I)‖ ≤
      Real.exp (a * (c - 1 / 2) ^ 2) * (c⁻¹ + (c - 1)⁻¹) *
        Real.exp (-a * y ^ 2) := by
  unfold gaussianXiPolePairIntegrand
  simp only [sub_zero, div_eq_mul_inv]
  calc
    ‖riemannXiGaussianWeight a ((c : ℂ) + y * I) * ((c : ℂ) + y * I)⁻¹ +
        riemannXiGaussianWeight a ((c : ℂ) + y * I) *
          ((c : ℂ) + y * I - 1)⁻¹‖ ≤
        ‖riemannXiGaussianWeight a ((c : ℂ) + y * I) *
          ((c : ℂ) + y * I)⁻¹‖ +
        ‖riemannXiGaussianWeight a ((c : ℂ) + y * I) *
          ((c : ℂ) + y * I - 1)⁻¹‖ := norm_add_le _ _
    _ = ‖riemannXiGaussianWeight a ((c : ℂ) + y * I)‖ *
          ‖((c : ℂ) + y * I)⁻¹‖ +
        ‖riemannXiGaussianWeight a ((c : ℂ) + y * I)‖ *
          ‖((c : ℂ) + y * I - 1)⁻¹‖ := by rw [norm_mul, norm_mul]
    _ ≤ ‖riemannXiGaussianWeight a ((c : ℂ) + y * I)‖ * c⁻¹ +
        ‖riemannXiGaussianWeight a ((c : ℂ) + y * I)‖ * (c - 1)⁻¹ := by
      gcongr
      · simpa using norm_inv_vertical_sub_real_le (rho := 0) (y := y) (by linarith)
      · simpa using norm_inv_vertical_sub_real_le (rho := 1) (y := y) (by linarith)
    _ = ‖riemannXiGaussianWeight a ((c : ℂ) + y * I)‖ *
        (c⁻¹ + (c - 1)⁻¹) := by ring
    _ = Real.exp (a * (c - 1 / 2) ^ 2) * (c⁻¹ + (c - 1)⁻¹) *
        Real.exp (-a * y ^ 2) := by
      rw [norm_riemannXiGaussianWeight]
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
        add_zero, add_im, mul_im, mul_one, zero_add]
      simp only [sub_self, add_zero]
      have hsplit :
          Real.exp (a * ((c - 1 / 2) ^ 2 - y ^ 2)) =
            Real.exp (a * (c - 1 / 2) ^ 2) * Real.exp (-a * y ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hsplit]
      ring

/-- The elementary pole pair is absolutely integrable on every Euler-product right line. -/
theorem integrable_gaussianXiPolePair
    {a c : ℝ} (ha : 0 < a) (hc : 1 < c) :
    Integrable (fun y : ℝ => gaussianXiPolePairIntegrand a ((c : ℂ) + y * I)) := by
  have hweightContinuous : Continuous (fun y : ℝ =>
      riemannXiGaussianWeight a ((c : ℂ) + y * I)) := by
    unfold riemannXiGaussianWeight
    fun_prop
  have hcontinuous : Continuous (fun y : ℝ =>
      gaussianXiPolePairIntegrand a ((c : ℂ) + y * I)) := by
    unfold gaussianXiPolePairIntegrand
    apply Continuous.add
    · apply Continuous.div hweightContinuous (by fun_prop)
      intro y hzero
      have hre := congrArg Complex.re hzero
      simp at hre
      linarith
    · apply Continuous.div hweightContinuous (by fun_prop)
      intro y hzero
      have hre := congrArg Complex.re hzero
      simp at hre
      linarith
  refine MeasureTheory.Integrable.mono'
    ((integrable_exp_neg_mul_sq ha).const_mul
      (Real.exp (a * (c - 1 / 2) ^ 2) * (c⁻¹ + (c - 1)⁻¹)))
    hcontinuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  simpa only [mul_assoc] using norm_gaussianXiPolePairIntegrand_vertical_le
    (a := a) hc y

/-- The full-line Gaussian pole pair is the exact contribution of the residues at zero and one. -/
theorem integral_gaussianXiPolePair_eq
    {a c : ℝ} (ha : 0 < a) (hc : 1 < c) :
    (∫ y : ℝ, gaussianXiPolePairIntegrand a ((c : ℂ) + y * I)) =
      2 * (Real.pi : ℂ) * (Real.exp (a / 4) : ℂ) := by
  have hfull := intervalIntegral_tendsto_integral
    (integrable_gaussianXiPolePair ha hc)
    (tendsto_neg_atTop_atBot.comp (tendsto_gaussianXiSelectedHeight c))
    (tendsto_gaussianXiSelectedHeight c)
  have hfull' : Tendsto (gaussianXiPoleRightVerticalIntegral a c) atTop
      (𝓝 (∫ y : ℝ, gaussianXiPolePairIntegrand a ((c : ℂ) + y * I))) := by
    change Tendsto
      (fun n : ℕ => ∫ y : ℝ in
        -gaussianXiSelectedHeight c n..gaussianXiSelectedHeight c n,
          gaussianXiPolePairIntegrand a ((c : ℂ) + y * I)) atTop
      (𝓝 (∫ y : ℝ, gaussianXiPolePairIntegrand a ((c : ℂ) + y * I)))
    simpa only [Function.comp_apply] using hfull
  exact tendsto_nhds_unique hfull' (tendsto_gaussianXiPoleRightVerticalIntegral ha hc)

/-- Every integrable function is recovered along the campaign's selected symmetric heights. -/
theorem tendsto_selectedGaussianXiSymmetricIntervalIntegral
    {c : ℝ} {f : ℝ → ℂ} (hf : Integrable f) :
    Tendsto
      (fun n : ℕ => ∫ y : ℝ in
        -gaussianXiSelectedHeight c n..gaussianXiSelectedHeight c n, f y)
      atTop (𝓝 (∫ y : ℝ, f y)) := by
  have hlim := intervalIntegral_tendsto_integral hf
    (tendsto_neg_atTop_atBot.comp (tendsto_gaussianXiSelectedHeight c))
    (tendsto_gaussianXiSelectedHeight c)
  simpa only [Function.comp_apply] using hlim

/-- On every selected finite right edge, the xi logarithmic derivative splits into its pole,
real-place, and von-Mangoldt terms with the exact explicit-formula signs. -/
theorem gaussianXiRightVerticalIntegral_eq_arithmetic_truncations
    {a c : ℝ} (ha : 0 < a) (hc : 1 < c) (n : ℕ) :
    gaussianXiRightVerticalIntegral a c n =
      gaussianXiPoleRightVerticalIntegral a c n +
        (∫ y : ℝ in -gaussianXiSelectedHeight c n..gaussianXiSelectedHeight c n,
          riemannXiGaussianWeight a ((c : ℂ) + y * I) *
            logDeriv Gammaℝ ((c : ℂ) + y * I)) -
        (∫ y : ℝ in -gaussianXiSelectedHeight c n..gaussianXiSelectedHeight c n,
          riemannXiGaussianWeight a ((c : ℂ) + y * I) *
            L ↗ArithmeticFunction.vonMangoldt ((c : ℂ) + y * I)) := by
  let T : ℝ := gaussianXiSelectedHeight c n
  have hpole : IntervalIntegrable (fun y : ℝ =>
      gaussianXiPolePairIntegrand a ((c : ℂ) + y * I)) volume (-T) T :=
    (integrable_gaussianXiPolePair ha hc).intervalIntegrable
  have harch : IntervalIntegrable (fun y : ℝ =>
      riemannXiGaussianWeight a ((c : ℂ) + y * I) *
        logDeriv Gammaℝ ((c : ℂ) + y * I)) volume (-T) T :=
    (integrable_gaussianXiArchimedean ha hc).intervalIntegrable
  have hprime : IntervalIntegrable (fun y : ℝ =>
      riemannXiGaussianWeight a ((c : ℂ) + y * I) *
        L ↗ArithmeticFunction.vonMangoldt ((c : ℂ) + y * I)) volume (-T) T :=
    (integrable_gaussianXi_mul_vonMangoldtLSeries ha hc).intervalIntegrable
  have hpoint (y : ℝ) :
      riemannXiGaussianWeight a ((c : ℂ) + y * I) *
          logDeriv riemannXi ((c : ℂ) + y * I) =
        gaussianXiPolePairIntegrand a ((c : ℂ) + y * I) +
          riemannXiGaussianWeight a ((c : ℂ) + y * I) *
            logDeriv Gammaℝ ((c : ℂ) + y * I) -
          riemannXiGaussianWeight a ((c : ℂ) + y * I) *
            L ↗ArithmeticFunction.vonMangoldt ((c : ℂ) + y * I) := by
    rw [logDeriv_riemannXi_eq_poles_archimedean_sub_vonMangoldt
      (by simpa using hc)]
    unfold gaussianXiPolePairIntegrand
    simp only [sub_zero, div_eq_mul_inv]
    ring
  rw [gaussianXiRightVerticalIntegral, gaussianXiPoleRightVerticalIntegral]
  change
    (∫ y : ℝ in -T..T,
      riemannXiGaussianWeight a ((c : ℂ) + y * I) *
        logDeriv riemannXi ((c : ℂ) + y * I)) = _
  calc
    (∫ y : ℝ in -T..T,
      riemannXiGaussianWeight a ((c : ℂ) + y * I) *
        logDeriv riemannXi ((c : ℂ) + y * I)) =
        ∫ y : ℝ in -T..T,
          gaussianXiPolePairIntegrand a ((c : ℂ) + y * I) +
            riemannXiGaussianWeight a ((c : ℂ) + y * I) *
              logDeriv Gammaℝ ((c : ℂ) + y * I) -
            riemannXiGaussianWeight a ((c : ℂ) + y * I) *
              L ↗ArithmeticFunction.vonMangoldt ((c : ℂ) + y * I) := by
      apply intervalIntegral.integral_congr
      intro y _hy
      exact hpoint y
    _ = (∫ y : ℝ in -T..T,
          gaussianXiPolePairIntegrand a ((c : ℂ) + y * I)) +
        (∫ y : ℝ in -T..T,
          riemannXiGaussianWeight a ((c : ℂ) + y * I) *
            logDeriv Gammaℝ ((c : ℂ) + y * I)) -
        (∫ y : ℝ in -T..T,
          riemannXiGaussianWeight a ((c : ℂ) + y * I) *
            L ↗ArithmeticFunction.vonMangoldt ((c : ℂ) + y * I)) := by
      rw [intervalIntegral.integral_sub (hpole.add harch) hprime,
        intervalIntegral.integral_add hpole harch]

/-- The selected archimedean truncations converge to the registered full-line real-place term. -/
theorem tendsto_selectedGaussianXiArchimedeanIntegral
    {a c : ℝ} (ha : 0 < a) (hc : 1 < c) :
    Tendsto
      (fun n : ℕ => ∫ y : ℝ in
        -gaussianXiSelectedHeight c n..gaussianXiSelectedHeight c n,
          riemannXiGaussianWeight a ((c : ℂ) + y * I) *
            logDeriv Gammaℝ ((c : ℂ) + y * I))
      atTop (𝓝 (gaussianXiArchimedeanIntegral a c)) := by
  simpa only [gaussianXiArchimedeanIntegral] using
    tendsto_selectedGaussianXiSymmetricIntervalIntegral
      (integrable_gaussianXiArchimedean ha hc)

/-- The selected prime truncations converge to the explicit Gaussian von-Mangoldt series. -/
theorem tendsto_selectedGaussianXiPrimeIntegral
    {a c : ℝ} (ha : 0 < a) (hc : 1 < c) :
    Tendsto
      (fun n : ℕ => ∫ y : ℝ in
        -gaussianXiSelectedHeight c n..gaussianXiSelectedHeight c n,
          riemannXiGaussianWeight a ((c : ℂ) + y * I) *
            L ↗ArithmeticFunction.vonMangoldt ((c : ℂ) + y * I))
      atTop (𝓝 (∑' n : ℕ, gaussianVonMangoldtWeight a n)) := by
  rw [tsum_gaussianVonMangoldtWeight_eq_integral ha hc]
  exact tendsto_selectedGaussianXiSymmetricIntervalIntegral
    (integrable_gaussianXi_mul_vonMangoldtLSeries ha hc)

/-- The fixed centered-Gaussian Weil explicit formula, with absolute multiplicity-bearing xi
zeros, both elementary poles, the real Gamma factor, and all von-Mangoldt prime powers. -/
theorem gaussianXi_arithmetic_explicit_formula
    {a c : ℝ} (ha : 0 < a) (hc : 1 < c) :
    (Real.pi : ℂ) *
        ∑' p : RiemannXiDivisorZeroIndex,
          riemannXiGaussianWeight a (riemannXiDivisorZeroValue p) =
      2 * (Real.pi : ℂ) * Real.exp (a / 4) +
        gaussianXiArchimedeanIntegral a c -
          ∑' n : ℕ, gaussianVonMangoldtWeight a n := by
  have hpole := tendsto_gaussianXiPoleRightVerticalIntegral ha hc
  have harch := tendsto_selectedGaussianXiArchimedeanIntegral ha hc
  have hprime := tendsto_selectedGaussianXiPrimeIntegral ha hc
  have harithmetic := (hpole.add harch).sub hprime
  have hright : Tendsto (gaussianXiRightVerticalIntegral a c) atTop
      (𝓝 (2 * (Real.pi : ℂ) * (Real.exp (a / 4) : ℂ) +
        gaussianXiArchimedeanIntegral a c -
          ∑' n : ℕ, gaussianVonMangoldtWeight a n)) := by
    apply harithmetic.congr'
    exact Filter.Eventually.of_forall fun n =>
      (gaussianXiRightVerticalIntegral_eq_arithmetic_truncations ha hc n).symm
  exact tendsto_nhds_unique (tendsto_gaussianXiRightVerticalIntegral ha hc) hright

end

end LeanLab.Riemann
