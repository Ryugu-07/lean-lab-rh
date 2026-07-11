import LeanLab.Riemann.BalazardSaias
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.LSeries.Dirichlet

set_option linter.style.header false

/-!
# A source-specific truncated Perron formula

This module formalizes the Mobius specialization of Titchmarsh Lemma 3.12 used in the proof of
Theorem 14.25(A), with the quantitative uniformity needed before the Balazard-Saias contour shift.
-/

noncomputable section

open Filter MeasureTheory Set Topology
open scoped ArithmeticFunction.Moebius LSeries.notation Interval

namespace LeanLab.Riemann

/-- The meromorphic integrand underlying Perron's inversion kernel. -/
def perronIntegrand (a : ℝ) (w : ℂ) : ℂ := Complex.exp (w * a) / w

/-- Cauchy--Goursat on a rectangle contained in the open right half-plane. -/
theorem perronIntegrand_boundary_rect_eq_zero
    {a c R T : ℝ} (hc : 0 < c) (hcR : c ≤ R) :
    (∫ x : ℝ in c..R, perronIntegrand a (x + (-T) * Complex.I)) -
        (∫ x : ℝ in c..R, perronIntegrand a (x + T * Complex.I)) +
      Complex.I * (∫ t : ℝ in -T..T, perronIntegrand a (R + t * Complex.I)) -
      Complex.I * (∫ t : ℝ in -T..T, perronIntegrand a (c + t * Complex.I)) = 0 := by
  let z : ℂ := Complex.mk c (-T)
  let w : ℂ := Complex.mk R T
  have hdiff : DifferentiableOn ℂ (perronIntegrand a)
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) := by
    intro q hq
    have hqre : c ≤ q.re := by
      rw [Complex.mem_reProdIm] at hq
      simpa only [z, w, min_eq_left hcR] using hq.1.1
    have hq0 : q ≠ 0 := Complex.ne_zero_of_re_pos (hc.trans_le hqre)
    unfold perronIntegrand
    exact (((differentiableAt_id.mul_const (a : ℂ)).cexp).div differentiableAt_id hq0)
      |>.differentiableWithinAt
  have hboundary := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (perronIntegrand a) z w hdiff
  simpa only [z, w, Complex.ofReal_neg, smul_eq_mul] using hboundary

/-- Solving the right-half-plane rectangle identity for its left vertical side. -/
theorem perronIntegrand_vertical_eq_right_add_horizontals
    {a c R T : ℝ} (hc : 0 < c) (hcR : c ≤ R) :
    (∫ t : ℝ in -T..T, perronIntegrand a (c + t * Complex.I)) =
      (∫ t : ℝ in -T..T, perronIntegrand a (R + t * Complex.I)) +
        Complex.I *
          ((∫ x : ℝ in c..R, perronIntegrand a (x + T * Complex.I)) -
            ∫ x : ℝ in c..R, perronIntegrand a (x + (-T) * Complex.I)) := by
  have hboundary := perronIntegrand_boundary_rect_eq_zero (a := a) (T := T) hc hcR
  apply mul_left_cancel₀ Complex.I_ne_zero
  rw [mul_add, ← mul_assoc, Complex.I_mul_I, neg_one_mul, neg_sub]
  linear_combination -hboundary

/-- A horizontal-line pointwise bound for the Perron integrand. -/
theorem norm_perronIntegrand_add_mul_I_le
    {a x t : ℝ} (ht : t ≠ 0) :
    ‖perronIntegrand a (x + t * Complex.I)‖ ≤ Real.exp (a * x) / |t| := by
  have hden : |t| ≤ ‖(x : ℂ) + t * Complex.I‖ := by
    simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, zero_add, add_zero, mul_one, mul_zero, sub_zero] using
      Complex.abs_im_le_norm ((x : ℂ) + t * Complex.I)
  rw [perronIntegrand, norm_div, Complex.norm_exp]
  have hre : ((((x : ℂ) + t * Complex.I) * (a : ℂ)).re) = a * x := by
    simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, sub_zero,
      add_zero, mul_one]
    ring
  rw [hre]
  exact div_le_div_of_nonneg_left (Real.exp_nonneg _) (abs_pos.mpr ht) hden

/-- The elementary antiderivative needed to estimate Perron's horizontal contour sides. -/
theorem integral_exp_mul_real {a c R : ℝ} (ha : a ≠ 0) :
    (∫ x : ℝ in c..R, Real.exp (a * x)) =
      (Real.exp (a * R) - Real.exp (a * c)) / a := by
  calc
    (∫ x : ℝ in c..R, Real.exp (a * x)) =
        a⁻¹ * (a * ∫ x : ℝ in c..R, Real.exp (a * x)) := by field_simp
    _ = a⁻¹ * ∫ x : ℝ in a * c..a * R, Real.exp x := by
      rw [intervalIntegral.mul_integral_comp_mul_left]
    _ = (Real.exp (a * R) - Real.exp (a * c)) / a := by
      rw [integral_exp]
      field_simp

/-- A horizontal side of the right-half-plane Perron rectangle has a uniform exponential bound. -/
theorem norm_perronIntegrand_horizontal_integral_le_abs
    {a c R t : ℝ} (ha : a < 0) (hcR : c ≤ R) (ht : t ≠ 0) :
    ‖∫ x : ℝ in c..R, perronIntegrand a (x + t * Complex.I)‖ ≤
      Real.exp (a * c) / (|t| * (-a)) := by
  have hbound :
      ‖∫ x : ℝ in c..R, perronIntegrand a (x + t * Complex.I)‖ ≤
        ∫ x : ℝ in c..R, Real.exp (a * x) / |t| := by
    apply intervalIntegral.norm_integral_le_of_norm_le hcR
    · filter_upwards with x hx
      exact norm_perronIntegrand_add_mul_I_le (a := a) (x := x) ht
    · apply Continuous.intervalIntegrable
      fun_prop
  rw [intervalIntegral.integral_div, integral_exp_mul_real ha.ne] at hbound
  have hexp : Real.exp (a * R) ≤ Real.exp (a * c) := by
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hcR ha.le)
  calc
    ‖∫ x : ℝ in c..R, perronIntegrand a (x + t * Complex.I)‖ ≤
        (Real.exp (a * R) - Real.exp (a * c)) / a / |t| := hbound
    _ = (Real.exp (a * c) - Real.exp (a * R)) / (|t| * (-a)) := by
      field_simp
      ring
    _ ≤ Real.exp (a * c) / (|t| * (-a)) := by
      apply div_le_div_of_nonneg_right
      · linarith [Real.exp_nonneg (a * R)]
      · exact mul_nonneg (abs_nonneg t) (neg_nonneg.mpr ha.le)

/-- The positive-height specialization of the horizontal Perron bound. -/
theorem norm_perronIntegrand_horizontal_integral_le
    {a c R T : ℝ} (ha : a < 0) (hcR : c ≤ R) (hT : 0 < T) :
    ‖∫ x : ℝ in c..R, perronIntegrand a (x + T * Complex.I)‖ ≤
      Real.exp (a * c) / (T * (-a)) := by
  simpa [abs_of_pos hT] using
    norm_perronIntegrand_horizontal_integral_le_abs ha hcR hT.ne'

/-- A pointwise bound on the remote vertical side of the Perron rectangle. -/
theorem norm_perronIntegrand_vertical_le
    {a R t : ℝ} (hR : 0 < R) :
    ‖perronIntegrand a (R + t * Complex.I)‖ ≤ Real.exp (a * R) / R := by
  have hden : R ≤ ‖(R : ℂ) + t * Complex.I‖ := by
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
      abs_of_pos hR] using Complex.abs_re_le_norm ((R : ℂ) + t * Complex.I)
  rw [perronIntegrand, norm_div, Complex.norm_exp]
  have hre : ((((R : ℂ) + t * Complex.I) * (a : ℂ)).re) = a * R := by
    simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, sub_zero, add_zero, mul_one]
    ring
  rw [hre]
  exact div_le_div_of_nonneg_left (Real.exp_nonneg _) hR hden

/-- The remote vertical side is bounded by its length times its pointwise exponential bound. -/
theorem norm_perronIntegrand_vertical_integral_le
    {a R T : ℝ} (hR : 0 < R) (hT : 0 ≤ T) :
    ‖∫ t : ℝ in -T..T, perronIntegrand a (R + t * Complex.I)‖ ≤
      (Real.exp (a * R) / R) * (2 * T) := by
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -T) (b := T)
    (f := fun t : ℝ => perronIntegrand a (R + t * Complex.I))
    (C := Real.exp (a * R) / R) (fun t _ => norm_perronIntegrand_vertical_le hR)
  rw [abs_of_nonneg (by linarith : 0 ≤ T - -T)] at hbound
  convert hbound using 1
  all_goals ring

/-- The remote vertical side vanishes as the rectangle moves to the right when `a < 0`. -/
theorem tendsto_perronIntegrand_vertical_integral_atTop
    {a T : ℝ} (ha : a < 0) (hT : 0 ≤ T) :
    Tendsto (fun R : ℝ => ∫ t : ℝ in -T..T,
      perronIntegrand a (R + t * Complex.I)) atTop (𝓝 0) := by
  have harg : Tendsto (fun R : ℝ => a * R) atTop atBot :=
    tendsto_id.const_mul_atTop_of_neg ha
  have hexp : Tendsto (fun R : ℝ => Real.exp (a * R)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp harg
  have hmajor : Tendsto (fun R : ℝ => Real.exp (a * R) * (2 * T)) atTop (𝓝 0) := by
    simpa using hexp.mul_const (2 * T)
  rw [Metric.tendsto_atTop] at hmajor ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hmajor ε hε
  refine ⟨max N 1, fun R hR => ?_⟩
  have hRN : N ≤ R := (le_max_left N 1).trans hR
  have hR1 : 1 ≤ R := (le_max_right N 1).trans hR
  have hsmall := hN R hRN
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) (by positivity))] at hsmall
  rw [dist_zero_right]
  calc
    ‖∫ t : ℝ in -T..T, perronIntegrand a (R + t * Complex.I)‖ ≤
        (Real.exp (a * R) / R) * (2 * T) :=
      norm_perronIntegrand_vertical_integral_le (zero_lt_one.trans_le hR1) hT
    _ ≤ Real.exp (a * R) * (2 * T) :=
      mul_le_mul_of_nonneg_right (div_le_self (Real.exp_nonneg _) hR1) (by positivity)
    _ < ε := hsmall

/-- Quantitative truncated Perron inversion on the `a < 0` side, where the full kernel is zero. -/
theorem norm_perronIntegrand_vertical_integral_le_of_neg
    {a c T : ℝ} (ha : a < 0) (hc : 0 < c) (hT : 0 < T) :
    ‖∫ t : ℝ in -T..T, perronIntegrand a (c + t * Complex.I)‖ ≤
      2 * (Real.exp (a * c) / (T * (-a))) := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hremote := tendsto_perronIntegrand_vertical_integral_atTop ha hT.le
  rw [Metric.tendsto_atTop] at hremote
  obtain ⟨N, hN⟩ := hremote ε hε
  let R := max N c
  have hNR : N ≤ R := le_max_left _ _
  have hcR : c ≤ R := le_max_right _ _
  have hres : ‖∫ t : ℝ in -T..T, perronIntegrand a (R + t * Complex.I)‖ < ε := by
    simpa only [dist_zero_right] using hN R hNR
  have htop :
      ‖∫ x : ℝ in c..R, perronIntegrand a (x + T * Complex.I)‖ ≤
        Real.exp (a * c) / (T * (-a)) :=
    norm_perronIntegrand_horizontal_integral_le ha hcR hT
  have hbottom :
      ‖∫ x : ℝ in c..R, perronIntegrand a (x + (-T) * Complex.I)‖ ≤
        Real.exp (a * c) / (T * (-a)) := by
    simpa [abs_of_pos hT] using
      norm_perronIntegrand_horizontal_integral_le_abs ha hcR (neg_ne_zero.mpr hT.ne')
  have hrel := perronIntegrand_vertical_eq_right_add_horizontals
    (a := a) (T := T) hc hcR
  rw [hrel]
  calc
    ‖(∫ t : ℝ in -T..T, perronIntegrand a (R + t * Complex.I)) +
        Complex.I *
          ((∫ x : ℝ in c..R, perronIntegrand a (x + T * Complex.I)) -
            ∫ x : ℝ in c..R, perronIntegrand a (x + (-T) * Complex.I))‖ ≤
        ‖∫ t : ℝ in -T..T, perronIntegrand a (R + t * Complex.I)‖ +
          ‖Complex.I *
            ((∫ x : ℝ in c..R, perronIntegrand a (x + T * Complex.I)) -
              ∫ x : ℝ in c..R, perronIntegrand a (x + (-T) * Complex.I))‖ := norm_add_le _ _
    _ = ‖∫ t : ℝ in -T..T, perronIntegrand a (R + t * Complex.I)‖ +
          ‖(∫ x : ℝ in c..R, perronIntegrand a (x + T * Complex.I)) -
            ∫ x : ℝ in c..R, perronIntegrand a (x + (-T) * Complex.I)‖ := by
      rw [norm_mul, Complex.norm_I, one_mul]
    _ ≤ ‖∫ t : ℝ in -T..T, perronIntegrand a (R + t * Complex.I)‖ +
          (‖∫ x : ℝ in c..R, perronIntegrand a (x + T * Complex.I)‖ +
            ‖∫ x : ℝ in c..R, perronIntegrand a (x + (-T) * Complex.I)‖) := by
      gcongr
      exact norm_sub_le _ _
    _ ≤ ε +
          (Real.exp (a * c) / (T * (-a)) + Real.exp (a * c) / (T * (-a))) := by
      exact add_le_add hres.le (add_le_add htop hbottom)
    _ = 2 * (Real.exp (a * c) / (T * (-a))) + ε := by ring

/-- The single-coefficient truncated Perron kernel on the vertical line `Re(w) = c`. -/
def truncatedPerronKernel (c T y : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ *
    ∫ t : ℝ in -T..T,
      Complex.exp (((c : ℂ) + t * Complex.I) * Real.log y) /
        ((c : ℂ) + t * Complex.I)

/-- The source-specialized negative-side Perron kernel bound on `Re(w) = 2`. -/
theorem norm_truncatedPerronKernel_two_le_of_lt_one
    {T y : ℝ} (hy : 0 < y) (hy_one : y < 1) (hT : 0 < T) :
    ‖truncatedPerronKernel 2 T y‖ ≤
      (2 * Real.pi)⁻¹ * (2 * y ^ 2 / (T * (-Real.log y))) := by
  have hlog : Real.log y < 0 := Real.log_neg hy hy_one
  have hint := norm_perronIntegrand_vertical_integral_le_of_neg
    (a := Real.log y) (c := 2) hlog (by norm_num) hT
  have hexp : Real.exp (Real.log y * 2) = y ^ 2 := by
    calc
      Real.exp (Real.log y * 2) = Real.exp (Real.log y + Real.log y) := by ring_nf
      _ = y ^ 2 := by rw [Real.exp_add, Real.exp_log hy]; ring
  have hcoeff : ‖(2 * (Real.pi : ℂ))⁻¹‖ = (2 * Real.pi)⁻¹ := by
    simp [Complex.norm_real, abs_of_pos Real.pi_pos]
  rw [truncatedPerronKernel, norm_mul, hcoeff]
  gcongr
  simp only [perronIntegrand] at hint
  rw [hexp] at hint
  calc
    ‖∫ t : ℝ in -T..T,
        Complex.exp (((2 : ℂ) + t * Complex.I) * Real.log y) /
          ((2 : ℂ) + t * Complex.I)‖ ≤
        2 * (y ^ 2 / (T * (-Real.log y))) := hint
    _ = 2 * y ^ 2 / (T * (-Real.log y)) := by ring

/-- The source-specific Perron integral for the Mobius Dirichlet polynomial, with
`x = N + 1/2` and `c = 2`. -/
def mobiusTruncatedPerronIntegral (N : ℕ) (T : ℝ) (s : ℂ) : ℂ :=
  let x : ℝ := N + 1 / 2
  (2 * (Real.pi : ℂ))⁻¹ *
    ∫ t : ℝ in -T..T,
      (riemannZeta (s + 2 + t * Complex.I))⁻¹ *
        Complex.exp (((2 : ℂ) + t * Complex.I) * Real.log x) /
          ((2 : ℂ) + t * Complex.I)

/-- On its half-plane of absolute convergence, the Mobius L-series is reciprocal zeta. -/
theorem LSeries_moebius_eq_reciprocal_riemannZeta
    {s : ℂ} (hs : 1 < s.re) :
    L ↗ArithmeticFunction.moebius s = (riemannZeta s)⁻¹ := by
  have hprod := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
  have hzeta := riemannZeta_ne_zero_of_one_lt_re hs
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs] at hprod
  rw [inv_eq_one_div, eq_div_iff hzeta]
  simpa [mul_comm] using hprod

/-- The real-parameter integrand in the Perron kernel is continuously differentiable. -/
theorem hasDerivAt_perronOscillation (c a : ℝ) (t : ℝ) :
    HasDerivAt
      (fun u : ℝ => Complex.exp (((c : ℂ) + u * Complex.I) * a))
      (Complex.I * a * Complex.exp (((c : ℂ) + t * Complex.I) * a)) t := by
  have hline : HasDerivAt (fun u : ℝ => (c : ℂ) + u * Complex.I) Complex.I t := by
    have hlineC : HasDerivAt (fun z : ℂ => (c : ℂ) + z * Complex.I) Complex.I (t : ℂ) := by
      simpa using ((hasDerivAt_id (t : ℂ)).mul_const Complex.I).const_add (c : ℂ)
    exact hlineC.comp_ofReal
  convert (hline.mul_const (a : ℂ)).cexp using 1
  all_goals ring

/-- The reciprocal vertical-line factor is continuously differentiable away from `c = 0`. -/
theorem hasDerivAt_perronVerticalInv (c : ℝ) (hc : c ≠ 0) (t : ℝ) :
    HasDerivAt
      (fun u : ℝ => ((c : ℂ) + u * Complex.I)⁻¹)
      (-Complex.I * (((c : ℂ) + t * Complex.I)⁻¹) ^ 2) t := by
  have hne : (c : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] at hre
    exact hc hre
  have hline : HasDerivAt (fun u : ℝ => (c : ℂ) + u * Complex.I) Complex.I t := by
    have hlineC : HasDerivAt (fun z : ℂ => (c : ℂ) + z * Complex.I) Complex.I (t : ℂ) := by
      simpa using ((hasDerivAt_id (t : ℂ)).mul_const Complex.I).const_add (c : ℂ)
    exact hlineC.comp_ofReal
  simpa [Function.comp_def, smul_eq_mul, div_eq_mul_inv, inv_pow, mul_comm] using
    (hasDerivAt_inv hne).scomp t hline

/-- Integration by parts for the truncated Perron kernel. -/
theorem truncatedPerronKernel_integral_eq_boundary_sub
    {c T y : ℝ} (hc : c ≠ 0) (_hT : 0 ≤ T) (hy : 0 < y) (hy_one : y ≠ 1) :
    let a := Real.log y
    ∫ t : ℝ in -T..T,
        Complex.exp (((c : ℂ) + t * Complex.I) * a) /
          ((c : ℂ) + t * Complex.I) =
      (Complex.I * a)⁻¹ *
          (Complex.exp (((c : ℂ) + T * Complex.I) * a) /
              ((c : ℂ) + T * Complex.I) -
            Complex.exp (((c : ℂ) + (-T) * Complex.I) * a) /
              ((c : ℂ) + (-T) * Complex.I)) +
        a⁻¹ * ∫ t : ℝ in -T..T,
          Complex.exp (((c : ℂ) + t * Complex.I) * a) *
            (((c : ℂ) + t * Complex.I)⁻¹) ^ 2 := by
  dsimp only
  let a := Real.log y
  have ha : a ≠ 0 := by
    dsimp only [a]
    exact (Real.log_ne_zero_of_pos_of_ne_one hy hy_one)
  let u : ℝ → ℂ := fun t => Complex.exp (((c : ℂ) + t * Complex.I) * a)
  let v : ℝ → ℂ := fun t => ((c : ℂ) + t * Complex.I)⁻¹
  let u' : ℝ → ℂ := fun t => Complex.I * a * u t
  let v' : ℝ → ℂ := fun t => -Complex.I * (((c : ℂ) + t * Complex.I)⁻¹) ^ 2
  have hu : ∀ t ∈ [[-T, T]], HasDerivAt u (u' t) t := by
    intro t _
    simpa only [u, u', a] using hasDerivAt_perronOscillation c a t
  have hv : ∀ t ∈ [[-T, T]], HasDerivAt v (v' t) t := by
    intro t _
    simpa only [v, v'] using hasDerivAt_perronVerticalInv c hc t
  have hu_int : IntervalIntegrable u' volume (-T) T := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hv_int : IntervalIntegrable v' volume (-T) T := by
    apply Continuous.intervalIntegrable
    have hne : ∀ t : ℝ, (c : ℂ) + t * Complex.I ≠ 0 := by
      intro t h
      have hre := congrArg Complex.re h
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] at hre
      exact hc hre
    fun_prop
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu_int hv_int
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hIa : (Complex.I * (a : ℂ)) ≠ 0 := mul_ne_zero Complex.I_ne_zero haC
  dsimp only [u, v, u', v'] at hparts
  let I₀ : ℂ := ∫ t : ℝ in -T..T,
    Complex.exp (((c : ℂ) + t * Complex.I) * a) * ((c : ℂ) + t * Complex.I)⁻¹
  let J : ℂ := ∫ t : ℝ in -T..T,
    Complex.exp (((c : ℂ) + t * Complex.I) * a) *
      (((c : ℂ) + t * Complex.I)⁻¹) ^ 2
  let B : ℂ :=
    Complex.exp (((c : ℂ) + T * Complex.I) * a) * ((c : ℂ) + T * Complex.I)⁻¹ -
      Complex.exp (((c : ℂ) + (-T) * Complex.I) * a) *
        ((c : ℂ) + (-T) * Complex.I)⁻¹
  have hleft :
      (∫ t : ℝ in -T..T,
          Complex.exp (((c : ℂ) + t * Complex.I) * a) *
            (-Complex.I * (((c : ℂ) + t * Complex.I)⁻¹) ^ 2)) = -Complex.I * J := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  have hright :
      (∫ t : ℝ in -T..T,
          Complex.I * a * Complex.exp (((c : ℂ) + t * Complex.I) * a) *
            ((c : ℂ) + t * Complex.I)⁻¹) = (Complex.I * a) * I₀ := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  rw [hleft, hright] at hparts
  rw [Complex.ofReal_neg] at hparts
  change -Complex.I * J = B - (Complex.I * a) * I₀ at hparts
  change I₀ = (Complex.I * a)⁻¹ * B + (a⁻¹ : ℝ) * J
  calc
    I₀ = (Complex.I * a)⁻¹ * ((Complex.I * a) * I₀) := by field_simp
    _ = (Complex.I * a)⁻¹ * (B + Complex.I * J) := by
      congr 1
      linear_combination hparts
    _ = (Complex.I * a)⁻¹ * B + (a⁻¹ : ℝ) * J := by
      rw [Complex.ofReal_inv]
      field_simp [hIa, haC]

end LeanLab.Riemann
