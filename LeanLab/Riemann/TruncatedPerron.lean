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

/-- Cartesian decomposition of the reciprocal on a horizontal or vertical line. -/
theorem inv_add_mul_I_eq (x t : ℝ) :
    ((x : ℂ) + t * Complex.I)⁻¹ =
      (x / (x ^ 2 + t ^ 2) : ℝ) - (t / (x ^ 2 + t ^ 2) : ℝ) * Complex.I := by
  rw [Complex.inv_def]
  simp [Complex.normSq_apply, div_eq_mul_inv]
  ring

/-- The odd component of a reciprocal vertical-line integral vanishes on a symmetric interval. -/
theorem integral_id_div_sq_add_sq_neg_self (c T : ℝ) :
    (∫ t : ℝ in -T..T, t / (c ^ 2 + t ^ 2)) = 0 := by
  let f : ℝ → ℝ := fun t => t / (c ^ 2 + t ^ 2)
  have hodd : ∀ t : ℝ, f (-t) = -f t := by
    intro t
    dsimp only [f]
    ring
  have hcomp := intervalIntegral.integral_comp_neg (f := f) (a := -T) (b := T)
  have hneg : (∫ t : ℝ in -T..T, f (-t)) = -(∫ t : ℝ in -T..T, f t) := by
    calc
      (∫ t : ℝ in -T..T, f (-t)) = ∫ t : ℝ in -T..T, -f t := by
        apply intervalIntegral.integral_congr
        intro t _
        exact hodd t
      _ = -(∫ t : ℝ in -T..T, f t) := intervalIntegral.integral_neg
  simp only [neg_neg] at hcomp
  have hz : -(∫ t : ℝ in -T..T, f t) = ∫ t : ℝ in -T..T, f t := hneg.symm.trans hcomp
  dsimp only [f] at hz ⊢
  linarith

/-- A vertical reciprocal integral reduces to the elementary real arctangent integral. -/
theorem integral_inv_vertical {c T : ℝ} (hc : c ≠ 0) :
    (∫ t : ℝ in -T..T, ((c : ℂ) + t * Complex.I)⁻¹) =
      (Real.arctan (T / c) - Real.arctan ((-T) / c) : ℝ) := by
  have hden : ∀ t : ℝ, c ^ 2 + t ^ 2 ≠ 0 := by
    intro t h
    have hc2 : 0 < c ^ 2 := sq_pos_of_ne_zero hc
    nlinarith [sq_nonneg t]
  have hrealCont : Continuous (fun t : ℝ => c / (c ^ 2 + t ^ 2)) := by
    apply Continuous.div₀
    · fun_prop
    · fun_prop
    · exact hden
  have himagCont : Continuous (fun t : ℝ => t / (c ^ 2 + t ^ 2)) := by
    apply Continuous.div₀
    · fun_prop
    · fun_prop
    · exact hden
  have hreal : IntervalIntegrable
      (fun t : ℝ => ((c / (c ^ 2 + t ^ 2) : ℝ) : ℂ)) volume (-T) T := by
    apply Continuous.intervalIntegrable
    exact Complex.continuous_ofReal.comp hrealCont
  have himag : IntervalIntegrable
      (fun t : ℝ => ((t / (c ^ 2 + t ^ 2) : ℝ) : ℂ)) volume (-T) T := by
    apply Continuous.intervalIntegrable
    exact Complex.continuous_ofReal.comp himagCont
  rw [show (fun t : ℝ => ((c : ℂ) + t * Complex.I)⁻¹) =
      fun t : ℝ => (c / (c ^ 2 + t ^ 2) : ℝ) -
        (t / (c ^ 2 + t ^ 2) : ℝ) * Complex.I by
      funext t
      exact inv_add_mul_I_eq c t]
  rw [intervalIntegral.integral_sub hreal (himag.mul_const Complex.I)]
  rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_ofReal]
  rw [integral_id_div_sq_add_sq_neg_self]
  simp only [Complex.ofReal_zero, zero_mul, sub_zero]
  exact_mod_cast integral_div_sq_add_sq (a := -T) (b := T) (c := c)

/-- A reciprocal horizontal-line integrand is interval integrable away from height zero. -/
theorem intervalIntegrable_inv_add_mul_I
    {l R t : ℝ} (ht : t ≠ 0) :
    IntervalIntegrable (fun x : ℝ => ((x : ℂ) + t * Complex.I)⁻¹) volume l R := by
  apply Continuous.intervalIntegrable
  apply Continuous.inv₀
  · fun_prop
  · intro x h
    have him := congrArg Complex.im h
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, zero_add, mul_one, mul_zero, Complex.zero_im] at him
    exact ht (by simpa only [add_zero] using him)

/-- The two horizontal reciprocal integrals combine into one real arctangent integral. -/
theorem integral_inv_horizontal_sub
    {l R T : ℝ} (hT : T ≠ 0) :
    (∫ x : ℝ in l..R, ((x : ℂ) + (-T) * Complex.I)⁻¹) -
        (∫ x : ℝ in l..R, ((x : ℂ) + T * Complex.I)⁻¹) =
      (2 * (Real.arctan (R / T) - Real.arctan (l / T)) : ℝ) * Complex.I := by
  have hbottom := intervalIntegrable_inv_add_mul_I (l := l) (R := R) (neg_ne_zero.mpr hT)
  have htop := intervalIntegrable_inv_add_mul_I (l := l) (R := R) hT
  simp only [Complex.ofReal_neg] at hbottom
  rw [← intervalIntegral.integral_sub hbottom htop]
  calc
    (∫ x : ℝ in l..R,
        ((x : ℂ) + (-T) * Complex.I)⁻¹ - ((x : ℂ) + T * Complex.I)⁻¹) =
        ∫ x : ℝ in l..R, (2 * (T / (T ^ 2 + x ^ 2)) : ℝ) * Complex.I := by
      apply intervalIntegral.integral_congr
      intro x _
      simp only
      rw [← Complex.ofReal_neg]
      rw [inv_add_mul_I_eq x (-T), inv_add_mul_I_eq x T]
      push_cast
      ring
    _ = (∫ x : ℝ in l..R, (2 * (T / (T ^ 2 + x ^ 2)) : ℝ)) * Complex.I := by
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal]
    _ = (2 * (Real.arctan (R / T) - Real.arctan (l / T)) : ℝ) * Complex.I := by
      congr 1
      rw [show (fun x : ℝ => 2 * (T / (T ^ 2 + x ^ 2))) =
          fun x : ℝ => 2 * (T / (T ^ 2 + x ^ 2)) by rfl]
      rw [intervalIntegral.integral_const_mul, integral_div_sq_add_sq]

/-- The positively oriented rectangle boundary integral of `w⁻¹` is `2 * pi * I`. -/
theorem integral_inv_boundary_rect_eq_two_pi_mul_I
    {l R T : ℝ} (hl : l < 0) (hR : 0 < R) (hT : 0 < T) :
    (∫ x : ℝ in l..R, ((x : ℂ) + (-T) * Complex.I)⁻¹) -
        (∫ x : ℝ in l..R, ((x : ℂ) + T * Complex.I)⁻¹) +
      Complex.I * (∫ t : ℝ in -T..T, ((R : ℂ) + t * Complex.I)⁻¹) -
      Complex.I * (∫ t : ℝ in -T..T, ((l : ℂ) + t * Complex.I)⁻¹) =
        2 * (Real.pi : ℂ) * Complex.I := by
  have hhor := integral_inv_horizontal_sub (l := l) (R := R) hT.ne'
  have hright := integral_inv_vertical (c := R) (T := T) hR.ne'
  have hleft := integral_inv_vertical (c := l) (T := T) hl.ne
  rw [hhor, hright, hleft]
  have hnegR : (-T) / R = -(T / R) := by ring
  have hnegl : (-T) / l = -(T / l) := by ring
  rw [hnegR, hnegl, Real.arctan_neg, Real.arctan_neg]
  have hRT : 0 < R / T := div_pos hR hT
  have hlT : l / T < 0 := div_neg_of_neg_of_pos hl hT
  have hRinv : (R / T)⁻¹ = T / R := by field_simp
  have hlinv : (l / T)⁻¹ = T / l := by field_simp
  have haright := Real.arctan_inv_of_pos hRT
  have haleft := Real.arctan_inv_of_neg hlT
  rw [hRinv] at haright
  rw [hlinv] at haleft
  rw [haright, haleft]
  push_cast
  ring

/-- The pole-subtracted exponential quotient, defined at zero by its derivative. -/
def perronRemovable (a : ℝ) : ℂ → ℂ :=
  dslope (fun w : ℂ => Complex.exp (w * a)) 0

/-- Away from zero, the removable quotient is `(exp(a*w)-1)/w`. -/
theorem perronRemovable_eq_div {a : ℝ} {w : ℂ} (hw : w ≠ 0) :
    perronRemovable a w = (Complex.exp (w * a) - 1) / w := by
  have hs := sub_smul_dslope (fun z : ℂ => Complex.exp (z * a)) 0 w
  have hmul : w * perronRemovable a w = Complex.exp (w * a) - 1 := by
    simpa only [perronRemovable, sub_zero, smul_eq_mul, Complex.exp_zero, mul_zero, zero_mul,
      Complex.ofReal_zero] using hs
  apply (eq_div_iff hw).2
  simpa only [mul_comm] using hmul

/-- The Perron integrand is the sum of its simple pole and a removable entire function. -/
theorem perronIntegrand_eq_inv_add_removable {a : ℝ} {w : ℂ} (hw : w ≠ 0) :
    perronIntegrand a w = w⁻¹ + perronRemovable a w := by
  rw [perronRemovable_eq_div hw]
  unfold perronIntegrand
  field_simp [hw]
  ring

/-- The pole-subtracted Perron integrand is entire. -/
theorem differentiable_perronRemovable (a : ℝ) : Differentiable ℂ (perronRemovable a) := by
  rw [← differentiableOn_univ, perronRemovable,
    Complex.differentiableOn_dslope (s := Set.univ) (c := (0 : ℂ)) univ_mem]
  fun_prop

/-- Cauchy--Goursat for the removable part on an arbitrary rectangle. -/
theorem perronRemovable_boundary_rect_eq_zero {a l R T : ℝ} :
    (∫ x : ℝ in l..R, perronRemovable a (x + (-T) * Complex.I)) -
        (∫ x : ℝ in l..R, perronRemovable a (x + T * Complex.I)) +
      Complex.I * (∫ t : ℝ in -T..T, perronRemovable a (R + t * Complex.I)) -
      Complex.I * (∫ t : ℝ in -T..T, perronRemovable a (l + t * Complex.I)) = 0 := by
  let z : ℂ := Complex.mk l (-T)
  let w : ℂ := Complex.mk R T
  have hboundary := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (perronRemovable a) z w (differentiable_perronRemovable a).differentiableOn
  simpa only [z, w, Complex.ofReal_neg, smul_eq_mul] using hboundary

/-- The removable part is interval integrable along every affine real line. -/
theorem intervalIntegrable_perronRemovable_comp_affine
    (a : ℝ) (u v : ℂ) (p q : ℝ) :
    IntervalIntegrable (fun t : ℝ => perronRemovable a (u + t * v)) volume p q := by
  apply Continuous.intervalIntegrable
  exact (differentiable_perronRemovable a).continuous.comp
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))

/-- A reciprocal vertical-line integrand is interval integrable when its real part is nonzero. -/
theorem intervalIntegrable_inv_const_add_mul_I
    {c p q : ℝ} (hc : c ≠ 0) :
    IntervalIntegrable (fun t : ℝ => ((c : ℂ) + t * Complex.I)⁻¹) volume p q := by
  apply Continuous.intervalIntegrable
  apply Continuous.inv₀
  · fun_prop
  · intro t h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
      Complex.zero_re] at hre
    exact hc hre

/-- Integral decomposition of the Perron integrand on a nonzero horizontal line. -/
theorem integral_perron_horizontal_eq_inv_add_removable
    {a l R t : ℝ} (ht : t ≠ 0) :
    (∫ x : ℝ in l..R, perronIntegrand a (x + t * Complex.I)) =
      (∫ x : ℝ in l..R, ((x : ℂ) + t * Complex.I)⁻¹) +
        ∫ x : ℝ in l..R, perronRemovable a (x + t * Complex.I) := by
  have hrem : IntervalIntegrable
      (fun x : ℝ => perronRemovable a (x + t * Complex.I)) volume l R := by
    apply Continuous.intervalIntegrable
    exact (differentiable_perronRemovable a).continuous.comp
      (Complex.continuous_ofReal.add (continuous_const.mul continuous_const))
  rw [← intervalIntegral.integral_add (intervalIntegrable_inv_add_mul_I ht)
    hrem]
  apply intervalIntegral.integral_congr
  intro x _
  exact perronIntegrand_eq_inv_add_removable (by
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, zero_add, mul_one, mul_zero, add_zero, Complex.zero_im] at him
    exact ht him)

/-- Integral decomposition of the Perron integrand on a nonzero vertical line. -/
theorem integral_perron_vertical_eq_inv_add_removable
    {a c p q : ℝ} (hc : c ≠ 0) :
    (∫ t : ℝ in p..q, perronIntegrand a (c + t * Complex.I)) =
      (∫ t : ℝ in p..q, ((c : ℂ) + t * Complex.I)⁻¹) +
        ∫ t : ℝ in p..q, perronRemovable a (c + t * Complex.I) := by
  rw [← intervalIntegral.integral_add (intervalIntegrable_inv_const_add_mul_I hc)
    (intervalIntegrable_perronRemovable_comp_affine a c Complex.I p q)]
  apply intervalIntegral.integral_congr
  intro t _
  exact perronIntegrand_eq_inv_add_removable (by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
      Complex.zero_re] at hre
    exact hc hre)

/-- The rectangle boundary of the Perron integrand picks up exactly the residue at zero. -/
theorem perronIntegrand_boundary_rect_eq_two_pi_mul_I
    {a l R T : ℝ} (hl : l < 0) (hR : 0 < R) (hT : 0 < T) :
    (∫ x : ℝ in l..R, perronIntegrand a (x + (-T) * Complex.I)) -
        (∫ x : ℝ in l..R, perronIntegrand a (x + T * Complex.I)) +
      Complex.I * (∫ t : ℝ in -T..T, perronIntegrand a (R + t * Complex.I)) -
      Complex.I * (∫ t : ℝ in -T..T, perronIntegrand a (l + t * Complex.I)) =
        2 * (Real.pi : ℂ) * Complex.I := by
  rw [← Complex.ofReal_neg]
  rw [integral_perron_horizontal_eq_inv_add_removable (a := a) (neg_ne_zero.mpr hT.ne'),
    integral_perron_horizontal_eq_inv_add_removable (a := a) hT.ne',
    integral_perron_vertical_eq_inv_add_removable (a := a) hR.ne',
    integral_perron_vertical_eq_inv_add_removable (a := a) hl.ne]
  simp only [Complex.ofReal_neg]
  have hinv := integral_inv_boundary_rect_eq_two_pi_mul_I hl hR hT
  have hrem := perronRemovable_boundary_rect_eq_zero (a := a) (l := l) (R := R) (T := T)
  linear_combination hinv + hrem

/-- Solve the residue rectangle identity for the right vertical side minus its residue. -/
theorem perronIntegrand_vertical_sub_two_pi_eq_left_add_horizontals
    {a l c T : ℝ} (hl : l < 0) (hc : 0 < c) (hT : 0 < T) :
    (∫ t : ℝ in -T..T, perronIntegrand a (c + t * Complex.I)) -
        (2 * Real.pi : ℝ) =
      (∫ t : ℝ in -T..T, perronIntegrand a (l + t * Complex.I)) +
        Complex.I *
          ((∫ x : ℝ in l..c, perronIntegrand a (x + (-T) * Complex.I)) -
            ∫ x : ℝ in l..c, perronIntegrand a (x + T * Complex.I)) := by
  have hboundary := perronIntegrand_boundary_rect_eq_two_pi_mul_I
    (a := a) hl hc hT
  apply mul_left_cancel₀ Complex.I_ne_zero
  rw [mul_sub, mul_add, ← mul_assoc, Complex.I_mul_I, neg_one_mul]
  push_cast
  linear_combination hboundary

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

/-- A horizontal side extending left from `c` has a uniform bound when `a > 0`. -/
theorem norm_perronIntegrand_horizontal_integral_le_abs_of_pos
    {a l c t : ℝ} (ha : 0 < a) (hlc : l ≤ c) (ht : t ≠ 0) :
    ‖∫ x : ℝ in l..c, perronIntegrand a (x + t * Complex.I)‖ ≤
      Real.exp (a * c) / (|t| * a) := by
  have hbound :
      ‖∫ x : ℝ in l..c, perronIntegrand a (x + t * Complex.I)‖ ≤
        ∫ x : ℝ in l..c, Real.exp (a * x) / |t| := by
    apply intervalIntegral.norm_integral_le_of_norm_le hlc
    · filter_upwards with x hx
      exact norm_perronIntegrand_add_mul_I_le (a := a) (x := x) ht
    · apply Continuous.intervalIntegrable
      fun_prop
  rw [intervalIntegral.integral_div, integral_exp_mul_real ha.ne'] at hbound
  have hexp : Real.exp (a * l) ≤ Real.exp (a * c) := by
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hlc ha.le)
  calc
    ‖∫ x : ℝ in l..c, perronIntegrand a (x + t * Complex.I)‖ ≤
        (Real.exp (a * c) - Real.exp (a * l)) / a / |t| := hbound
    _ = (Real.exp (a * c) - Real.exp (a * l)) / (|t| * a) := by
      field_simp
    _ ≤ Real.exp (a * c) / (|t| * a) := by
      apply div_le_div_of_nonneg_right
      · linarith [Real.exp_nonneg (a * l)]
      · exact mul_nonneg (abs_nonneg t) ha.le

/-- The positive-height specialization of the left-extending horizontal bound. -/
theorem norm_perronIntegrand_horizontal_integral_le_of_pos
    {a l c T : ℝ} (ha : 0 < a) (hlc : l ≤ c) (hT : 0 < T) :
    ‖∫ x : ℝ in l..c, perronIntegrand a (x + T * Complex.I)‖ ≤
      Real.exp (a * c) / (T * a) := by
  simpa [abs_of_pos hT] using
    norm_perronIntegrand_horizontal_integral_le_abs_of_pos ha hlc hT.ne'

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

/-- Pointwise bound on a remote left vertical side when the exponential parameter is positive. -/
theorem norm_perronIntegrand_left_vertical_le
    {a R t : ℝ} (hR : 0 < R) :
    ‖perronIntegrand a (-R + t * Complex.I)‖ ≤ Real.exp (-(a * R)) / R := by
  have hden : R ≤ ‖((-R : ℝ) : ℂ) + t * Complex.I‖ := by
    have him := Complex.abs_re_le_norm (((-R : ℝ) : ℂ) + t * Complex.I)
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
      abs_neg, abs_of_pos hR] using him
  have hden' : R ≤ ‖-(R : ℂ) + t * Complex.I‖ := by
    simpa only [Complex.ofReal_neg] using hden
  rw [perronIntegrand, norm_div, Complex.norm_exp]
  have hre : (((-(R : ℂ) + t * Complex.I) * (a : ℂ)).re) = -(a * R) := by
    simp only [Complex.mul_re, Complex.add_re, Complex.neg_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, sub_zero,
      add_zero, mul_one]
    ring
  rw [hre]
  exact div_le_div_of_nonneg_left (Real.exp_nonneg _) hR hden'

/-- The remote left vertical side is bounded by length times its pointwise exponential bound. -/
theorem norm_perronIntegrand_left_vertical_integral_le
    {a R T : ℝ} (hR : 0 < R) (hT : 0 ≤ T) :
    ‖∫ t : ℝ in -T..T, perronIntegrand a (-R + t * Complex.I)‖ ≤
      (Real.exp (-(a * R)) / R) * (2 * T) := by
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -T) (b := T)
    (f := fun t : ℝ => perronIntegrand a (-R + t * Complex.I))
    (C := Real.exp (-(a * R)) / R) (fun t _ => norm_perronIntegrand_left_vertical_le hR)
  rw [abs_of_nonneg (by linarith : 0 ≤ T - -T)] at hbound
  convert hbound using 1
  all_goals ring

/-- The remote left vertical side vanishes at infinity when `a > 0`. -/
theorem tendsto_perronIntegrand_left_vertical_integral_atTop
    {a T : ℝ} (ha : 0 < a) (hT : 0 ≤ T) :
    Tendsto (fun R : ℝ => ∫ t : ℝ in -T..T,
      perronIntegrand a (-R + t * Complex.I)) atTop (𝓝 0) := by
  have harg : Tendsto (fun R : ℝ => -a * R) atTop atBot :=
    tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos ha)
  have hexp : Tendsto (fun R : ℝ => Real.exp (-(a * R))) atTop (𝓝 0) := by
    convert Real.tendsto_exp_atBot.comp harg using 1
    · funext R
      simp only [Function.comp_apply]
      congr 1
      ring
  have hmajor : Tendsto (fun R : ℝ => Real.exp (-(a * R)) * (2 * T)) atTop (𝓝 0) := by
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
    ‖∫ t : ℝ in -T..T, perronIntegrand a (-R + t * Complex.I)‖ ≤
        (Real.exp (-(a * R)) / R) * (2 * T) :=
      norm_perronIntegrand_left_vertical_integral_le (zero_lt_one.trans_le hR1) hT
    _ ≤ Real.exp (-(a * R)) * (2 * T) :=
      mul_le_mul_of_nonneg_right (div_le_self (Real.exp_nonneg _) hR1) (by positivity)
    _ < ε := hsmall

/-- Quantitative truncated Perron inversion on the `a > 0` side, including the residue one. -/
theorem norm_perronIntegrand_vertical_integral_sub_two_pi_le_of_pos
    {a c T : ℝ} (ha : 0 < a) (hc : 0 < c) (hT : 0 < T) :
    ‖(∫ t : ℝ in -T..T, perronIntegrand a (c + t * Complex.I)) -
        (2 * Real.pi : ℝ)‖ ≤
      2 * (Real.exp (a * c) / (T * a)) := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hremote := tendsto_perronIntegrand_left_vertical_integral_atTop ha hT.le
  rw [Metric.tendsto_atTop] at hremote
  obtain ⟨N, hN⟩ := hremote ε hε
  let R := max N 1
  have hNR : N ≤ R := le_max_left _ _
  have hR1 : 1 ≤ R := le_max_right _ _
  have hRpos : 0 < R := zero_lt_one.trans_le hR1
  have hres : ‖∫ t : ℝ in -T..T, perronIntegrand a (-R + t * Complex.I)‖ < ε := by
    simpa only [dist_zero_right] using hN R hNR
  have hlc : -R ≤ c := by linarith
  have htop :
      ‖∫ x : ℝ in -R..c, perronIntegrand a (x + T * Complex.I)‖ ≤
        Real.exp (a * c) / (T * a) :=
    norm_perronIntegrand_horizontal_integral_le_of_pos ha hlc hT
  have hbottom :
      ‖∫ x : ℝ in -R..c, perronIntegrand a (x + (-T) * Complex.I)‖ ≤
        Real.exp (a * c) / (T * a) := by
    simpa [abs_of_pos hT] using
      norm_perronIntegrand_horizontal_integral_le_abs_of_pos ha hlc
        (neg_ne_zero.mpr hT.ne')
  have hrel := perronIntegrand_vertical_sub_two_pi_eq_left_add_horizontals
    (a := a) (l := -R) (c := c) (T := T) (neg_neg_of_pos hRpos) hc hT
  simp only [Complex.ofReal_neg] at hrel
  rw [hrel]
  calc
    ‖(∫ t : ℝ in -T..T, perronIntegrand a (-R + t * Complex.I)) +
        Complex.I *
          ((∫ x : ℝ in -R..c, perronIntegrand a (x + (-T) * Complex.I)) -
            ∫ x : ℝ in -R..c, perronIntegrand a (x + T * Complex.I))‖ ≤
        ‖∫ t : ℝ in -T..T, perronIntegrand a (-R + t * Complex.I)‖ +
          ‖Complex.I *
            ((∫ x : ℝ in -R..c, perronIntegrand a (x + (-T) * Complex.I)) -
              ∫ x : ℝ in -R..c, perronIntegrand a (x + T * Complex.I))‖ := norm_add_le _ _
    _ = ‖∫ t : ℝ in -T..T, perronIntegrand a (-R + t * Complex.I)‖ +
          ‖(∫ x : ℝ in -R..c, perronIntegrand a (x + (-T) * Complex.I)) -
            ∫ x : ℝ in -R..c, perronIntegrand a (x + T * Complex.I)‖ := by
      rw [norm_mul, Complex.norm_I, one_mul]
    _ ≤ ‖∫ t : ℝ in -T..T, perronIntegrand a (-R + t * Complex.I)‖ +
          (‖∫ x : ℝ in -R..c, perronIntegrand a (x + (-T) * Complex.I)‖ +
            ‖∫ x : ℝ in -R..c, perronIntegrand a (x + T * Complex.I)‖) := by
      gcongr
      exact norm_sub_le _ _
    _ ≤ ε +
          (Real.exp (a * c) / (T * a) + Real.exp (a * c) / (T * a)) := by
      exact add_le_add hres.le (add_le_add hbottom htop)
    _ = 2 * (Real.exp (a * c) / (T * a)) + ε := by ring

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

/-- The source-specialized positive-side Perron kernel bound on `Re(w) = 2`. -/
theorem norm_truncatedPerronKernel_two_sub_one_le_of_one_lt
    {T y : ℝ} (hy_one : 1 < y) (hT : 0 < T) :
    ‖truncatedPerronKernel 2 T y - 1‖ ≤
      (2 * Real.pi)⁻¹ * (2 * y ^ 2 / (T * Real.log y)) := by
  have hy : 0 < y := zero_lt_one.trans hy_one
  have hlog : 0 < Real.log y := Real.log_pos hy_one
  have hint := norm_perronIntegrand_vertical_integral_sub_two_pi_le_of_pos
    (a := Real.log y) (c := 2) hlog (by norm_num) hT
  have hexp : Real.exp (Real.log y * 2) = y ^ 2 := by
    calc
      Real.exp (Real.log y * 2) = Real.exp (Real.log y + Real.log y) := by ring_nf
      _ = y ^ 2 := by rw [Real.exp_add, Real.exp_log hy]; ring
  have hcoeff : ‖(2 * (Real.pi : ℂ))⁻¹‖ = (2 * Real.pi)⁻¹ := by
    simp [Complex.norm_real, abs_of_pos Real.pi_pos]
  have hnormalize :
      truncatedPerronKernel 2 T y - 1 =
        (2 * (Real.pi : ℂ))⁻¹ *
          ((∫ t : ℝ in -T..T,
              Complex.exp (((2 : ℂ) + t * Complex.I) * Real.log y) /
                ((2 : ℂ) + t * Complex.I)) - (2 * Real.pi : ℝ)) := by
    rw [truncatedPerronKernel]
    have hpiC : (2 * (Real.pi : ℂ)) ≠ 0 := by
      exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    rw [show (1 : ℂ) = (2 * (Real.pi : ℂ))⁻¹ * (2 * (Real.pi : ℂ)) by
      exact (inv_mul_cancel₀ hpiC).symm]
    push_cast
    ring
  rw [hnormalize, norm_mul, hcoeff]
  gcongr
  simp only [perronIntegrand] at hint
  rw [hexp] at hint
  calc
    ‖(∫ t : ℝ in -T..T,
        Complex.exp (((2 : ℂ) + t * Complex.I) * Real.log y) /
          ((2 : ℂ) + t * Complex.I)) - (2 * Real.pi : ℝ)‖ ≤
        2 * (y ^ 2 / (T * Real.log y)) := hint
    _ = 2 * y ^ 2 / (T * Real.log y) := by ring

/-- The source-specific Perron integral for the Mobius Dirichlet polynomial, with
`x = N + 1/2` and `c = 2`. -/
def mobiusTruncatedPerronIntegral (N : ℕ) (T : ℝ) (s : ℂ) : ℂ :=
  let x : ℝ := N + 1 / 2
  (2 * (Real.pi : ℂ))⁻¹ *
    ∫ t : ℝ in -T..T,
      (riemannZeta (s + 2 + t * Complex.I))⁻¹ *
        Complex.exp (((2 : ℂ) + t * Complex.I) * Real.log x) /
          ((2 : ℂ) + t * Complex.I)

/-- The `n`th Mobius L-series contribution to the source Perron integrand. -/
def mobiusPerronSeriesTerm (x : ℝ) (s : ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  LSeries.term (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ))
      (s + 2 + t * Complex.I) n *
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

/-- Pointwise, the Mobius Perron terms sum to the reciprocal-zeta Perron integrand. -/
theorem hasSum_mobiusPerronSeriesTerm
    {x : ℝ} {s : ℂ} (hs : 1 / 2 ≤ s.re) (t : ℝ) :
    HasSum (fun n : ℕ => mobiusPerronSeriesTerm x s n t)
      ((riemannZeta (s + 2 + t * Complex.I))⁻¹ *
        Complex.exp (((2 : ℂ) + t * Complex.I) * Real.log x) /
          ((2 : ℂ) + t * Complex.I)) := by
  have hq : 1 < (s + 2 + t * Complex.I).re := by
    norm_num [Complex.add_re, Complex.mul_re]
    linarith
  have hsum : HasSum
      (fun n : ℕ => LSeries.term
        (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ))
        (s + 2 + t * Complex.I) n)
      (riemannZeta (s + 2 + t * Complex.I))⁻¹ := by
    rw [← LSeries_moebius_eq_reciprocal_riemannZeta hq]
    exact (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hq).LSeriesHasSum
  simpa only [mobiusPerronSeriesTerm, mul_div_assoc] using
    (hsum.mul_right
      (Complex.exp (((2 : ℂ) + t * Complex.I) * Real.log x) /
        ((2 : ℂ) + t * Complex.I)))

/-- Uniform norm bound for the source Perron weight on `Re(w)=2`. -/
theorem norm_perronWeight_two_le {x t : ℝ} (hx : 0 < x) :
    ‖Complex.exp (((2 : ℂ) + t * Complex.I) * Real.log x) /
        ((2 : ℂ) + t * Complex.I)‖ ≤ x ^ 2 / 2 := by
  have hden : (2 : ℝ) ≤ ‖(2 : ℂ) + t * Complex.I‖ := by
    have h := Complex.abs_re_le_norm ((2 : ℂ) + t * Complex.I)
    norm_num [Complex.add_re, Complex.mul_re] at h ⊢
    exact h
  rw [norm_div, Complex.norm_exp]
  have hre : (((((2 : ℂ) + t * Complex.I) * (Real.log x : ℂ)).re)) =
      2 * Real.log x := by
    norm_num [Complex.mul_re, Complex.add_re]
  rw [hre]
  have hexp : Real.exp (2 * Real.log x) = x ^ 2 := by
    calc
      Real.exp (2 * Real.log x) = Real.exp (Real.log x + Real.log x) := by ring_nf
      _ = x ^ 2 := by rw [Real.exp_add, Real.exp_log hx]; ring
  rw [hexp]
  exact div_le_div_of_nonneg_left (sq_nonneg x) (by norm_num) hden

/-- A summable, `t`-independent majorant for the Mobius Perron series. -/
def mobiusPerronSeriesBound (x : ℝ) (n : ℕ) : ℝ :=
  (x ^ 2 / 2) *
    ‖LSeries.term (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) (5 / 2 : ℂ) n‖

/-- The source Perron series majorant is summable. -/
theorem summable_mobiusPerronSeriesBound (x : ℝ) :
    Summable (mobiusPerronSeriesBound x) := by
  have hs : LSeriesSummable
      (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) (5 / 2 : ℂ) := by
    apply ArithmeticFunction.LSeriesSummable_moebius_iff.mpr
    norm_num
  exact Summable.mul_left (x ^ 2 / 2) hs.norm

/-- Every source Perron series term is bounded by the fixed `Re=5/2` majorant. -/
theorem norm_mobiusPerronSeriesTerm_le_bound
    {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : 1 / 2 ≤ s.re) (n : ℕ) (t : ℝ) :
    ‖mobiusPerronSeriesTerm x s n t‖ ≤ mobiusPerronSeriesBound x n := by
  have hre : (5 / 2 : ℂ).re ≤ (s + 2 + t * Complex.I).re := by
    norm_num [Complex.add_re, Complex.mul_re]
    linarith
  have hterm := LSeries.norm_term_le_of_re_le_re
    (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) hre n
  have hweight := norm_perronWeight_two_le (x := x) (t := t) hx
  rw [mobiusPerronSeriesTerm, norm_div, norm_mul]
  dsimp only [mobiusPerronSeriesBound]
  calc
    ‖LSeries.term (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ))
          (s + 2 + t * Complex.I) n‖ *
        ‖Complex.exp (((2 : ℂ) + t * Complex.I) * Real.log x)‖ /
          ‖(2 : ℂ) + t * Complex.I‖ =
      ‖LSeries.term (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ))
          (s + 2 + t * Complex.I) n‖ *
        ‖Complex.exp (((2 : ℂ) + t * Complex.I) * Real.log x) /
          ((2 : ℂ) + t * Complex.I)‖ := by rw [norm_div, mul_div_assoc]
    _ ≤ ‖LSeries.term (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ))
          (5 / 2 : ℂ) n‖ * (x ^ 2 / 2) := mul_le_mul hterm hweight (norm_nonneg _) (norm_nonneg _)
    _ = (x ^ 2 / 2) *
        ‖LSeries.term (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ))
          (5 / 2 : ℂ) n‖ := by ring

/-- Each Mobius Perron series term is continuous in the vertical parameter. -/
theorem continuous_mobiusPerronSeriesTerm (x : ℝ) (s : ℂ) (n : ℕ) :
    Continuous (mobiusPerronSeriesTerm x s n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · have heq : mobiusPerronSeriesTerm x s 0 = fun _t : ℝ => 0 := by
      funext t
      simp [mobiusPerronSeriesTerm, LSeries.term]
    rw [heq]
    exact continuous_const
  · have heq : mobiusPerronSeriesTerm x s n = fun t : ℝ =>
        ((ArithmeticFunction.moebius n : ℂ) /
            (n : ℂ) ^ (s + 2 + t * Complex.I)) *
          Complex.exp (((2 : ℂ) + t * Complex.I) * Real.log x) /
            ((2 : ℂ) + t * Complex.I) := by
      funext t
      rw [mobiusPerronSeriesTerm, LSeries.term_of_ne_zero hn]
    rw [heq]
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hpow : Continuous (fun t : ℝ => (n : ℂ) ^ (s + 2 + t * Complex.I)) :=
      (continuous_iff_continuousAt.mpr fun z => continuousAt_const_cpow hnC).comp
        (by fun_prop)
    have hpow_ne : ∀ t : ℝ, (n : ℂ) ^ (s + 2 + t * Complex.I) ≠ 0 := by
      intro t
      exact Complex.cpow_ne_zero_iff.mpr (Or.inl hnC)
    have hcoef : Continuous
        (fun t : ℝ => (ArithmeticFunction.moebius n : ℂ) /
          (n : ℂ) ^ (s + 2 + t * Complex.I)) :=
      continuous_const.div₀ hpow hpow_ne
    have hline_ne : ∀ t : ℝ, (2 : ℂ) + t * Complex.I ≠ 0 := by
      intro t h
      have hre := congrArg Complex.re h
      norm_num [Complex.add_re, Complex.mul_re] at hre
    exact (hcoef.mul (by fun_prop)).div₀ (by fun_prop) hline_ne

/-- Dominated convergence exchanges the absolutely convergent Mobius series and Perron integral. -/
theorem hasSum_integral_mobiusPerronSeriesTerm
    {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : 1 / 2 ≤ s.re) (T : ℝ) :
    HasSum (fun n : ℕ => ∫ t : ℝ in -T..T, mobiusPerronSeriesTerm x s n t)
      (∫ t : ℝ in -T..T,
        (riemannZeta (s + 2 + t * Complex.I))⁻¹ *
          Complex.exp (((2 : ℂ) + t * Complex.I) * Real.log x) /
            ((2 : ℂ) + t * Complex.I)) := by
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n (_t : ℝ) => mobiusPerronSeriesBound x n)
  · intro n
    exact (continuous_mobiusPerronSeriesTerm x s n).aestronglyMeasurable
  · intro n
    filter_upwards with t ht
    exact norm_mobiusPerronSeriesTerm_le_bound hx hs n t
  · filter_upwards with t ht
    exact summable_mobiusPerronSeriesBound x
  · exact (intervalIntegrable_const :
      IntervalIntegrable (fun _t : ℝ => ∑' n : ℕ, mobiusPerronSeriesBound x n)
        volume (-T) T)
  · filter_upwards with t ht
    exact hasSum_mobiusPerronSeriesTerm hs t

/-- For a positive index, a Mobius Perron series term is a Dirichlet coefficient times one
Perron kernel. -/
theorem mobiusPerronSeriesTerm_eq_coefficient_mul_kernel
    {x : ℝ} (hx : 0 < x) {s : ℂ} {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    mobiusPerronSeriesTerm x s n t =
      ((ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-s)) *
        (Complex.exp (((2 : ℂ) + t * Complex.I) * Real.log (x / n)) /
          ((2 : ℂ) + t * Complex.I)) := by
  let w : ℂ := (2 : ℂ) + t * Complex.I
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hncpow : (n : ℂ) ^ w = Complex.exp (w * Real.log n) := by
    rw [Complex.cpow_def_of_ne_zero hnC]
    congr 1
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) by norm_num, ← Complex.ofReal_log hnpos.le]
    ring
  have hlogdiv : Real.log (x / n) = Real.log x - Real.log n := by
    rw [Real.log_div hx.ne' hnpos.ne']
  have hexpdiv :
      Complex.exp (w * Real.log x) / (n : ℂ) ^ w =
        Complex.exp (w * Real.log (x / n)) := by
    rw [hncpow, ← Complex.exp_sub, hlogdiv]
    push_cast
    congr 1
    ring
  rw [mobiusPerronSeriesTerm, LSeries.term_of_ne_zero hn]
  rw [show s + 2 + t * Complex.I = s + w by dsimp only [w]; ring]
  rw [show (2 : ℂ) + t * Complex.I = w by rfl]
  rw [Complex.cpow_add s w hnC, Complex.cpow_neg]
  rw [div_eq_mul_inv] at hexpdiv
  simp only [div_eq_mul_inv]
  change ((ArithmeticFunction.moebius n : ℂ) *
      ((n : ℂ) ^ s * (n : ℂ) ^ w)⁻¹ * Complex.exp (w * Real.log x)) * w⁻¹ =
    ((ArithmeticFunction.moebius n : ℂ) * ((n : ℂ) ^ s)⁻¹) *
      (Complex.exp (w * Real.log (x / n)) * w⁻¹)
  calc
    ((ArithmeticFunction.moebius n : ℂ) *
        ((n : ℂ) ^ s * (n : ℂ) ^ w)⁻¹ * Complex.exp (w * Real.log x)) * w⁻¹ =
      ((ArithmeticFunction.moebius n : ℂ) * ((n : ℂ) ^ s)⁻¹) *
        (Complex.exp (w * Real.log x) * ((n : ℂ) ^ w)⁻¹) * w⁻¹ := by
      rw [mul_inv]
      ring
    _ = ((ArithmeticFunction.moebius n : ℂ) * ((n : ℂ) ^ s)⁻¹) *
        Complex.exp (w * Real.log (x / n)) * w⁻¹ := by rw [hexpdiv]
    _ = ((ArithmeticFunction.moebius n : ℂ) * ((n : ℂ) ^ s)⁻¹) *
        (Complex.exp (w * Real.log (x / n)) * w⁻¹) := by ring

/-- Integrating one positive-index term gives its Dirichlet coefficient times the Perron kernel. -/
theorem normalized_integral_mobiusPerronSeriesTerm_eq
    {x : ℝ} (hx : 0 < x) (s : ℂ) (T : ℝ) (n : ℕ) :
    (2 * (Real.pi : ℂ))⁻¹ *
        (∫ t : ℝ in -T..T, mobiusPerronSeriesTerm x s n t) =
      ((ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-s)) *
        truncatedPerronKernel 2 T (x / n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [mobiusPerronSeriesTerm, LSeries.term]
  · rw [show (fun t : ℝ => mobiusPerronSeriesTerm x s n t) =
        fun t : ℝ =>
          ((ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-s)) *
            (Complex.exp (((2 : ℂ) + t * Complex.I) * Real.log (x / n)) /
              ((2 : ℂ) + t * Complex.I)) by
      funext t
      exact mobiusPerronSeriesTerm_eq_coefficient_mul_kernel hx hn t]
    rw [intervalIntegral.integral_const_mul, truncatedPerronKernel]
    ac_rfl

/-- The normalized source Perron integral is the sum of coefficient-weighted Perron kernels. -/
theorem hasSum_mobiusCoefficient_mul_truncatedPerronKernel
    {x : ℝ} (hx : 0 < x) {s : ℂ} (hs : 1 / 2 ≤ s.re) (T : ℝ) :
    HasSum (fun n : ℕ =>
      ((ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-s)) *
        truncatedPerronKernel 2 T (x / n))
      ((2 * (Real.pi : ℂ))⁻¹ *
        ∫ t : ℝ in -T..T,
          (riemannZeta (s + 2 + t * Complex.I))⁻¹ *
            Complex.exp (((2 : ℂ) + t * Complex.I) * Real.log x) /
              ((2 : ℂ) + t * Complex.I)) := by
  have hsum := (hasSum_integral_mobiusPerronSeriesTerm hx hs T).mul_left
    (2 * (Real.pi : ℂ))⁻¹
  exact HasSum.congr_fun hsum fun n =>
    (normalized_integral_mobiusPerronSeriesTerm_eq hx s T n).symm

/-- Half-integral spacing controls the logarithmic Perron denominator uniformly in the index. -/
theorem inv_abs_log_nat_add_half_div_nat_le
    (N n : ℕ) :
    |Real.log (((N : ℝ) + 1 / 2) / n)|⁻¹ ≤ 3 * n := by
  rcases eq_or_ne n 0 with rfl | hn
  · norm_num
  let x : ℝ := (N : ℝ) + 1 / 2
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hx : 0 < x := by dsimp only [x]; positivity
  by_cases hnN : n ≤ N
  · have hnx : (n : ℝ) < x := by
      have : (n : ℝ) ≤ N := by exact_mod_cast hnN
      dsimp only [x]
      linarith
    have hy : 1 < x / n := (one_lt_div hnpos).mpr hnx
    have hlog : 0 < Real.log (x / n) := Real.log_pos hy
    have hlow := Real.one_sub_inv_le_log_of_pos (div_pos hx hnpos)
    have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hgap : 1 / 2 ≤ x - n := by
      have hcast : (n : ℝ) ≤ N := by exact_mod_cast hnN
      dsimp only [x]
      linarith
    have hprod : 0 ≤ ((n : ℝ) - 1) * (x - n - 1 / 2) :=
      mul_nonneg (sub_nonneg.mpr hn1) (sub_nonneg.mpr hgap)
    have hpoly : x ≤ 3 * n * (x - n) := by nlinarith
    have hfrac : 1 ≤ 3 * n * (1 - (x / n)⁻¹) := by
      rw [inv_div]
      field_simp
      nlinarith
    rw [abs_of_pos hlog]
    rw [show (Real.log (x / n))⁻¹ = 1 * (Real.log (x / n))⁻¹ by ring,
      mul_inv_le_iff₀ hlog]
    nlinarith [mul_le_mul_of_nonneg_left hlow (by positivity : 0 ≤ (3 * n : ℝ))]
  · have hNn : N < n := Nat.lt_of_not_ge hnN
    have hxn : x < (n : ℝ) := by
      have hcast : (N : ℝ) + 1 ≤ n := by exact_mod_cast hNn
      dsimp only [x]
      linarith
    have hypos : 0 < x / n := div_pos hx hnpos
    have hylt : x / n < 1 := (div_lt_one hnpos).mpr hxn
    have hz : 1 < (n : ℝ) / x := (one_lt_div hx).mpr hxn
    have hlogz : 0 < Real.log ((n : ℝ) / x) := Real.log_pos hz
    have hlow := Real.one_sub_inv_le_log_of_pos (div_pos hnpos hx)
    have hgap : 1 / 2 ≤ (n : ℝ) - x := by
      have hcast : (N : ℝ) + 1 ≤ n := by exact_mod_cast hNn
      dsimp only [x]
      linarith
    have hfrac : 1 ≤ 3 * n * (1 - ((n : ℝ) / x)⁻¹) := by
      rw [inv_div]
      field_simp
      nlinarith
    have hloginv : -Real.log (x / n) = Real.log ((n : ℝ) / x) := by
      rw [← Real.log_inv, inv_div]
    rw [abs_of_neg (Real.log_neg hypos hylt), hloginv]
    rw [show (Real.log ((n : ℝ) / x))⁻¹ =
        1 * (Real.log ((n : ℝ) / x))⁻¹ by ring, mul_inv_le_iff₀ hlogz]
    nlinarith [mul_le_mul_of_nonneg_left hlow (by positivity : 0 ≤ (3 * n : ℝ))]

/-- On `Re(s) >= 1/2`, a Mobius Dirichlet coefficient is bounded by `n^(-1/2)`. -/
theorem norm_mobius_mul_nat_cpow_neg_le
    {s : ℂ} (hs : 1 / 2 ≤ s.re) (n : ℕ) :
    ‖(ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-s)‖ ≤
      (n : ℝ) ^ (-1 / 2 : ℝ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · norm_num
  · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
    have hmu : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
    have hpow : (n : ℝ) ^ (-s.re) ≤ (n : ℝ) ^ (-1 / 2 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le hn1
      linarith
    exact (mul_le_mul hmu hpow (Real.rpow_nonneg (by positivity) _) (by norm_num)).trans_eq
      (one_mul _)

/-- Both sides of the half-integral Perron cutoff satisfy one uniform kernel-error bound. -/
theorem norm_half_cutoff_sub_truncatedPerronKernel_le
    (N : ℕ) {T : ℝ} (hT : 0 < T) {n : ℕ} (hn : n ≠ 0) :
    ‖(if n ∈ Finset.Icc 1 N then (1 : ℂ) else 0) -
        truncatedPerronKernel 2 T (((N : ℝ) + 1 / 2) / n)‖ ≤
      (2 * Real.pi)⁻¹ *
        (6 * ((N : ℝ) + 1 / 2) ^ 2 / (T * n)) := by
  let x : ℝ := (N : ℝ) + 1 / 2
  have hx : 0 < x := by dsimp only [x]; positivity
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hInv := inv_abs_log_nat_add_half_div_nat_le N n
  change |Real.log (x / n)|⁻¹ ≤ 3 * n at hInv
  by_cases hnN : n ≤ N
  · have hmem : n ∈ Finset.Icc 1 N :=
      Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hn, hnN⟩
    have hnx : (n : ℝ) < x := by
      have hcast : (n : ℝ) ≤ N := by exact_mod_cast hnN
      dsimp only [x]
      linarith
    have hy : 1 < x / n := (one_lt_div hnpos).mpr hnx
    have hlog : 0 < Real.log (x / n) := Real.log_pos hy
    have hk := norm_truncatedPerronKernel_two_sub_one_le_of_one_lt hy hT
    have hcore :
        2 * (x / n) ^ 2 / (T * Real.log (x / n)) ≤
          6 * x ^ 2 / (T * n) := by
      calc
        2 * (x / n) ^ 2 / (T * Real.log (x / n)) =
            (2 * x ^ 2 / (T * n ^ 2)) * |Real.log (x / n)|⁻¹ := by
          rw [abs_of_pos hlog]
          field_simp
        _ ≤ (2 * x ^ 2 / (T * n ^ 2)) * (3 * n) := by
          exact mul_le_mul_of_nonneg_left hInv (by positivity)
        _ = 6 * x ^ 2 / (T * n) := by
          field_simp
          ring
    simp only [if_pos hmem]
    rw [show (1 : ℂ) - truncatedPerronKernel 2 T (x / n) =
        -(truncatedPerronKernel 2 T (x / n) - 1) by ring, norm_neg]
    exact hk.trans (mul_le_mul_of_nonneg_left hcore (by positivity))
  · have hNn : N < n := Nat.lt_of_not_ge hnN
    have hmem : n ∉ Finset.Icc 1 N := by
      simp only [Finset.mem_Icc, not_and_or]
      exact Or.inr (Nat.not_le.mpr hNn)
    have hxn : x < (n : ℝ) := by
      have hcast : (N : ℝ) + 1 ≤ n := by exact_mod_cast hNn
      dsimp only [x]
      linarith
    have hypos : 0 < x / n := div_pos hx hnpos
    have hylt : x / n < 1 := (div_lt_one hnpos).mpr hxn
    have hlog : Real.log (x / n) < 0 := Real.log_neg hypos hylt
    have hk := norm_truncatedPerronKernel_two_le_of_lt_one hypos hylt hT
    have hcore :
        2 * (x / n) ^ 2 / (T * (-Real.log (x / n))) ≤
          6 * x ^ 2 / (T * n) := by
      calc
        2 * (x / n) ^ 2 / (T * (-Real.log (x / n))) =
            (2 * x ^ 2 / (T * n ^ 2)) * |Real.log (x / n)|⁻¹ := by
          rw [abs_of_neg hlog]
          field_simp
        _ ≤ (2 * x ^ 2 / (T * n ^ 2)) * (3 * n) := by
          exact mul_le_mul_of_nonneg_left hInv (by positivity)
        _ = 6 * x ^ 2 / (T * n) := by
          field_simp
          ring
    simp only [if_neg hmem, zero_sub, norm_neg]
    exact hk.trans (mul_le_mul_of_nonneg_left hcore (by positivity))

/-- The coefficient-level error between the sharp half-integral cutoff and the Perron kernel. -/
def mobiusTruncatedPerronErrorTerm (N : ℕ) (T : ℝ) (s : ℂ) (n : ℕ) : ℂ :=
  ((ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-s)) *
    ((if n ∈ Finset.Icc 1 N then (1 : ℂ) else 0) -
      truncatedPerronKernel 2 T (((N : ℝ) + 1 / 2) / n))

/-- Every coefficient-level error is dominated by a fixed `n^(-3/2)` p-series. -/
theorem norm_mobiusTruncatedPerronErrorTerm_le
    (N : ℕ) {T : ℝ} (hT : 0 < T) {s : ℂ} (hs : 1 / 2 ≤ s.re) (n : ℕ) :
    ‖mobiusTruncatedPerronErrorTerm N T s n‖ ≤
      ((2 * Real.pi)⁻¹ * 6 * (((N : ℝ) + 1 / 2) ^ 2) / T) *
        (n : ℝ) ^ (-3 / 2 : ℝ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [mobiusTruncatedPerronErrorTerm]
  · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hcoeff := norm_mobius_mul_nat_cpow_neg_le hs n
    have hkernel := norm_half_cutoff_sub_truncatedPerronKernel_le N hT hn
    rw [mobiusTruncatedPerronErrorTerm, norm_mul]
    calc
      ‖(ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-s)‖ *
          ‖(if n ∈ Finset.Icc 1 N then (1 : ℂ) else 0) -
            truncatedPerronKernel 2 T (((N : ℝ) + 1 / 2) / n)‖ ≤
        (n : ℝ) ^ (-1 / 2 : ℝ) *
          ((2 * Real.pi)⁻¹ *
            (6 * ((N : ℝ) + 1 / 2) ^ 2 / (T * n))) :=
        mul_le_mul hcoeff hkernel (norm_nonneg _) (Real.rpow_nonneg (by positivity) _)
      _ = ((2 * Real.pi)⁻¹ * 6 * (((N : ℝ) + 1 / 2) ^ 2) / T) *
          (n : ℝ) ^ (-3 / 2 : ℝ) := by
        have hrpow : (n : ℝ) ^ (-3 / 2 : ℝ) =
            (n : ℝ) ^ (-1 / 2 : ℝ) / n := by
          rw [show (-3 / 2 : ℝ) = -1 / 2 - 1 by norm_num,
            Real.rpow_sub_one hnpos.ne']
        rw [hrpow]
        field_simp

/-- The universal p-series used to sum all truncated Perron coefficient errors. -/
theorem summable_nat_rpow_neg_three_halves :
    Summable (fun n : ℕ => (n : ℝ) ^ (-3 / 2 : ℝ)) := by
  exact Real.summable_nat_rpow.mpr (by norm_num)

/-- The coefficient errors sum exactly to the finite Mobius sum minus its Perron integral. -/
theorem hasSum_mobiusTruncatedPerronErrorTerm
    (N : ℕ) (T : ℝ) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    HasSum (mobiusTruncatedPerronErrorTerm N T s)
      (mobiusDirichletPartialSum N s - mobiusTruncatedPerronIntegral N T s) := by
  let x : ℝ := (N : ℝ) + 1 / 2
  have hx : 0 < x := by dsimp only [x]; positivity
  have hfinite : HasSum (fun n : ℕ =>
      ((ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-s)) *
        (if n ∈ Finset.Icc 1 N then (1 : ℂ) else 0))
      (mobiusDirichletPartialSum N s) := by
    rw [mobiusDirichletPartialSum]
    have hraw : HasSum (fun n : ℕ =>
        ((ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-s)) *
          (if n ∈ Finset.Icc 1 N then (1 : ℂ) else 0))
        (∑ n ∈ Finset.Icc 1 N,
          ((ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-s)) *
            (if n ∈ Finset.Icc 1 N then (1 : ℂ) else 0)) := by
      apply hasSum_sum_of_ne_finset_zero
      intro n hnmem
      simp only [if_neg hnmem, mul_zero]
    convert hraw using 1
    apply Finset.sum_congr rfl
    intro n hnmem
    simp [Finset.mem_Icc.mp hnmem]
  have hkernel := hasSum_mobiusCoefficient_mul_truncatedPerronKernel hx hs T
  have hkernel' : HasSum (fun n : ℕ =>
      ((ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-s)) *
        truncatedPerronKernel 2 T (x / n))
      (mobiusTruncatedPerronIntegral N T s) := by
    simpa only [x, mobiusTruncatedPerronIntegral] using hkernel
  have hsub := hfinite.sub hkernel'
  exact HasSum.congr_fun hsub fun n => by
    simp only [mobiusTruncatedPerronErrorTerm]
    ring

/-- Source-specialized Mobius truncated Perron formula with an absolute uniform error constant. -/
theorem exists_mobiusDirichletPartialSum_sub_truncatedPerronIntegral_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (T : ℝ) (s : ℂ),
      2 ≤ N → 1 ≤ T → 1 / 2 ≤ s.re → s.re ≤ 1 →
        ‖mobiusDirichletPartialSum N s - mobiusTruncatedPerronIntegral N T s‖ ≤
          C * ((N : ℝ) + 1) ^ 2 / T := by
  let p : ℕ → ℝ := fun n => (n : ℝ) ^ (-3 / 2 : ℝ)
  let S : ℝ := ∑' n : ℕ, p n
  let D : ℝ := (2 * Real.pi)⁻¹ * 6 * S
  let C : ℝ := D + 1
  have hp : Summable p := summable_nat_rpow_neg_three_halves
  have hS : 0 ≤ S := by
    dsimp only [S, p]
    exact tsum_nonneg fun n => Real.rpow_nonneg (by positivity) _
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  refine ⟨C, by dsimp only [C]; linarith, ?_⟩
  intro N T s hN hT hs _hs1
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  let x : ℝ := (N : ℝ) + 1 / 2
  let A : ℝ := (2 * Real.pi)⁻¹ * 6 * x ^ 2 / T
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hmajor : Summable (fun n : ℕ => A * p n) := Summable.mul_left A hp
  have hnorms : Summable (fun n : ℕ => ‖mobiusTruncatedPerronErrorTerm N T s n‖) :=
    hmajor.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => by
      dsimp only [A, p, x]
      exact norm_mobiusTruncatedPerronErrorTerm_le N hTpos hs n)
  have hsum := hasSum_mobiusTruncatedPerronErrorTerm N T hs
  have hnorm :
      ‖mobiusDirichletPartialSum N s - mobiusTruncatedPerronIntegral N T s‖ ≤
        A * S := by
    calc
      ‖mobiusDirichletPartialSum N s - mobiusTruncatedPerronIntegral N T s‖ =
          ‖∑' n : ℕ, mobiusTruncatedPerronErrorTerm N T s n‖ := by
        rw [hsum.tsum_eq]
      _ ≤ ∑' n : ℕ, ‖mobiusTruncatedPerronErrorTerm N T s n‖ :=
        norm_tsum_le_tsum_norm hnorms
      _ ≤ ∑' n : ℕ, A * p n :=
        hnorms.tsum_mono hmajor fun n => by
          dsimp only [A, p, x]
          exact norm_mobiusTruncatedPerronErrorTerm_le N hTpos hs n
      _ = A * S := by
        rw [hp.tsum_mul_left]
  have hx_sq : x ^ 2 ≤ ((N : ℝ) + 1) ^ 2 := by
    have hx0 : 0 ≤ x := by dsimp only [x]; positivity
    have hxle : x ≤ (N : ℝ) + 1 := by dsimp only [x]; linarith
    nlinarith
  calc
    ‖mobiusDirichletPartialSum N s - mobiusTruncatedPerronIntegral N T s‖ ≤ A * S := hnorm
    _ = D * x ^ 2 / T := by
      dsimp only [A, D]
      ring
    _ ≤ C * ((N : ℝ) + 1) ^ 2 / T := by
      have hDC : D ≤ C := by dsimp only [C]; linarith
      have hC : 0 ≤ C := hD.trans hDC
      apply div_le_div_of_nonneg_right
      · exact mul_le_mul hDC hx_sq (sq_nonneg _) hC
      · exact zero_le_one.trans hT

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
