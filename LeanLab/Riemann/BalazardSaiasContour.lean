import LeanLab.Riemann.ReciprocalZetaSubpower
import LeanLab.Riemann.TruncatedPerron

set_option linter.style.header false

/-!
# The Balazard-Saias contour shift

This module closes the RH-specialized contour argument left after the source-specific truncated
Perron formula. The value at the zeta pole is handled by an explicit entire reciprocal extension;
no residue or contour estimate is assumed as a premise.
-/

noncomputable section

open Filter MeasureTheory Set Topology
open scoped Interval

namespace LeanLab.Riemann

theorem RiemannHypothesis.zetaPoleRemoved_ne_zero_of_half_lt_re
    (hRH : RiemannHypothesis) {s : ℂ} (hs : 1 / 2 < s.re) :
    zetaPoleRemoved s ≠ 0 := by
  by_cases hs_one : s = 1
  · subst s
    simp
  · rw [zetaPoleRemoved_eq hs_one]
    exact mul_ne_zero (sub_ne_zero.mpr hs_one)
      (RiemannHypothesis.riemannZeta_ne_zero_of_half_le_lt_re hRH (by rfl) hs)

theorem RiemannHypothesis.differentiableOn_reciprocalZetaPoleRemoved
    (hRH : RiemannHypothesis) :
    DifferentiableOn ℂ analyticReciprocalRiemannZeta {s : ℂ | 1 / 2 < s.re} := by
  intro s hs
  exact (differentiableAt_id.sub_const 1).div
    differentiable_zetaPoleRemoved.differentiableAt
    (RiemannHypothesis.zetaPoleRemoved_ne_zero_of_half_lt_re hRH hs)
    |>.differentiableWithinAt

theorem RiemannHypothesis.reciprocalZetaPoleRemoved_eq_inv
    (hRH : RiemannHypothesis) {s : ℂ} (hs : 1 / 2 < s.re) (hs_one : s ≠ 1) :
    analyticReciprocalRiemannZeta s = (riemannZeta s)⁻¹ :=
  analyticReciprocalRiemannZeta_eq_inv hs_one
    (RiemannHypothesis.riemannZeta_ne_zero_of_half_le_lt_re hRH (by rfl) hs)

/-- The residue-subtracted part of the shifted reciprocal-zeta Perron integrand. -/
def balazardContourRemovable (s : ℂ) (x : ℝ) (w : ℂ) : ℂ :=
  dslope (fun z : ℂ => analyticReciprocalRiemannZeta (s + z)) 0 w *
    Complex.exp (w * Real.log x)

/-- A globally defined version of the contour integrand on the RH zero-free half-plane. -/
def balazardContourIntegrand (s : ℂ) (x : ℝ) (w : ℂ) : ℂ :=
  analyticReciprocalRiemannZeta s * perronIntegrand (Real.log x) w +
    balazardContourRemovable s x w

theorem balazardContourIntegrand_eq
    {s w : ℂ} {x : ℝ} (hw : w ≠ 0) :
    balazardContourIntegrand s x w =
      analyticReciprocalRiemannZeta (s + w) * Complex.exp (w * Real.log x) / w := by
  have hslope := sub_smul_dslope
    (fun z : ℂ => analyticReciprocalRiemannZeta (s + z)) 0 w
  simp only [sub_zero, smul_eq_mul, add_zero] at hslope
  rw [balazardContourIntegrand, balazardContourRemovable, perronIntegrand]
  field_simp [hw]
  linear_combination hslope

theorem RiemannHypothesis.differentiableOn_balazardContourRemovable
    (hRH : RiemannHypothesis) {s : ℂ} (hs : 1 / 2 < s.re) (x : ℝ) :
    DifferentiableOn ℂ (balazardContourRemovable s x)
      {w : ℂ | 1 / 2 < (s + w).re} := by
  let U : Set ℂ := {w : ℂ | 1 / 2 < (s + w).re}
  have hU_open : IsOpen U := by
    exact isOpen_lt continuous_const
      (Complex.continuous_re.comp (continuous_const.add continuous_id))
  have hzero : (0 : ℂ) ∈ U := by
    change 1 / 2 < (s + 0).re
    simpa using hs
  have hU_nhds : U ∈ 𝓝 (0 : ℂ) := hU_open.mem_nhds hzero
  have hshift : DifferentiableOn ℂ
      (fun w : ℂ => analyticReciprocalRiemannZeta (s + w)) U := by
    apply (RiemannHypothesis.differentiableOn_reciprocalZetaPoleRemoved hRH |>.comp
      ((differentiableOn_const (c := s)).add differentiableOn_id))
    intro w hw
    exact hw
  have hslope : DifferentiableOn ℂ
      (dslope (fun w : ℂ => analyticReciprocalRiemannZeta (s + w)) 0) U :=
    (Complex.differentiableOn_dslope hU_nhds).mpr hshift
  change DifferentiableOn ℂ
    (fun w => dslope (fun z : ℂ => analyticReciprocalRiemannZeta (s + z)) 0 w *
      Complex.exp (w * Real.log x)) U
  exact hslope.mul (((differentiableOn_id.mul_const (Real.log x : ℂ))).cexp)

theorem RiemannHypothesis.intervalIntegrable_balazardContourRemovable_affine
    (hRH : RiemannHypothesis) {s u v : ℂ} {x p q : ℝ} (hs : 1 / 2 < s.re)
    (hmap : ∀ t ∈ Set.uIcc p q, 1 / 2 < (s + (u + t * v)).re) :
    IntervalIntegrable (fun t : ℝ => balazardContourRemovable s x (u + t * v))
      volume p q := by
  apply ContinuousOn.intervalIntegrable
  apply (RiemannHypothesis.differentiableOn_balazardContourRemovable hRH hs x).continuousOn.comp
    (continuousOn_const.add (Complex.continuous_ofReal.continuousOn.mul continuousOn_const))
  intro t ht
  exact hmap t ht

theorem RiemannHypothesis.balazardContourRemovable_boundary_rect_eq_zero
    (hRH : RiemannHypothesis) {s : ℂ} {x l c T : ℝ}
    (hs : 1 / 2 < s.re) (hl : l < 0) (hc : 0 < c)
    (hleft : 1 / 2 < s.re + l) :
    (∫ u : ℝ in l..c,
        balazardContourRemovable s x (u + (-T) * Complex.I)) -
      (∫ u : ℝ in l..c,
        balazardContourRemovable s x (u + T * Complex.I)) +
      Complex.I * (∫ t : ℝ in -T..T,
        balazardContourRemovable s x (c + t * Complex.I)) -
      Complex.I * (∫ t : ℝ in -T..T,
        balazardContourRemovable s x (l + t * Complex.I)) = 0 := by
  let z : ℂ := Complex.mk l (-T)
  let w : ℂ := Complex.mk c T
  have hlc : l ≤ c := (hl.trans hc).le
  have hdiff : DifferentiableOn ℂ (balazardContourRemovable s x)
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) := by
    apply (RiemannHypothesis.differentiableOn_balazardContourRemovable hRH hs x).mono
    intro q hq
    rw [Complex.mem_reProdIm] at hq
    have hqre : l ≤ q.re := by
      simpa only [z, w, min_eq_left hlc] using hq.1.1
    change 1 / 2 < (s + q).re
    simp only [Complex.add_re]
    linarith
  have hboundary := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (balazardContourRemovable s x) z w hdiff
  simpa only [z, w, Complex.ofReal_neg, smul_eq_mul] using hboundary

theorem intervalIntegrable_perronIntegrand_affine
    {a : ℝ} {u v : ℂ} {p q : ℝ}
    (hne : ∀ t ∈ Set.uIcc p q, u + t * v ≠ 0) :
    IntervalIntegrable (fun t : ℝ => perronIntegrand a (u + t * v)) volume p q := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  have hpoint : u + (t : ℂ) * v ≠ 0 := hne t ht
  have hdiff : DifferentiableAt ℂ (perronIntegrand a) (u + (t : ℂ) * v) := by
    unfold perronIntegrand
    exact (((differentiableAt_id.mul_const (a : ℂ)).cexp).div differentiableAt_id hpoint)
  have hline : ContinuousAt (fun y : ℝ => u + (y : ℂ) * v) t := by fun_prop
  have hcomp : ContinuousAt (fun y : ℝ => perronIntegrand a (u + (y : ℂ) * v)) t :=
    hdiff.continuousAt.comp_of_eq hline rfl
  exact hcomp.continuousWithinAt

/-- Exact residue identity for the reciprocal-zeta Perron rectangle. -/
theorem RiemannHypothesis.balazardContourIntegrand_boundary_rect
    (hRH : RiemannHypothesis) {s : ℂ} {x l c T : ℝ}
    (hs : 1 / 2 < s.re) (hl : l < 0) (hc : 0 < c) (hT : 0 < T)
    (hleft : 1 / 2 < s.re + l) :
    (∫ u : ℝ in l..c, balazardContourIntegrand s x (u + (-T) * Complex.I)) -
      (∫ u : ℝ in l..c, balazardContourIntegrand s x (u + T * Complex.I)) +
      Complex.I * (∫ t : ℝ in -T..T,
        balazardContourIntegrand s x (c + t * Complex.I)) -
      Complex.I * (∫ t : ℝ in -T..T,
        balazardContourIntegrand s x (l + t * Complex.I)) =
        analyticReciprocalRiemannZeta s * (2 * (Real.pi : ℂ) * Complex.I) := by
  have hlc : l ≤ c := (hl.trans hc).le
  have hp_bottom : IntervalIntegrable
      (fun u : ℝ => perronIntegrand (Real.log x) (u + (-T) * Complex.I)) volume l c := by
    have h := intervalIntegrable_perronIntegrand_affine
      (a := Real.log x) (u := ((-T : ℝ) : ℂ) * Complex.I) (v := 1)
      (p := l) (q := c) (by
        intro u _ hu
        have him := congrArg Complex.im hu
        simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
          Complex.ofReal_im, Complex.one_re, Complex.one_im, mul_one, mul_zero, add_zero,
          Complex.zero_im] at him
        linarith)
    simpa only [Complex.ofReal_neg, mul_one, add_comm] using h
  have hp_top : IntervalIntegrable
      (fun u : ℝ => perronIntegrand (Real.log x) (u + T * Complex.I)) volume l c := by
    have h := intervalIntegrable_perronIntegrand_affine
      (a := Real.log x) (u := (T : ℂ) * Complex.I) (v := 1)
      (p := l) (q := c) (by
        intro u _ hu
        have him := congrArg Complex.im hu
        simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
          Complex.ofReal_im, Complex.one_re, Complex.one_im, mul_one, mul_zero, add_zero,
          Complex.zero_im] at him
        linarith)
    simpa only [mul_one, add_comm] using h
  have hp_right : IntervalIntegrable
      (fun t : ℝ => perronIntegrand (Real.log x) (c + t * Complex.I)) volume (-T) T := by
    apply intervalIntegrable_perronIntegrand_affine (u := (c : ℂ)) (v := Complex.I)
    intro t _ ht
    have hre := congrArg Complex.re ht
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
      Complex.zero_re] at hre
    exact hc.ne' hre
  have hp_left : IntervalIntegrable
      (fun t : ℝ => perronIntegrand (Real.log x) (l + t * Complex.I)) volume (-T) T := by
    apply intervalIntegrable_perronIntegrand_affine (u := (l : ℂ)) (v := Complex.I)
    intro t _ ht
    have hre := congrArg Complex.re ht
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
      Complex.zero_re] at hre
    exact hl.ne hre
  have hr_bottom : IntervalIntegrable
      (fun u : ℝ => balazardContourRemovable s x (u + (-T) * Complex.I)) volume l c := by
    have h := RiemannHypothesis.intervalIntegrable_balazardContourRemovable_affine hRH hs
      (u := ((-T : ℝ) : ℂ) * Complex.I) (v := 1) (p := l) (q := c) (x := x) (by
        intro u hu
        rw [Set.uIcc_of_le hlc] at hu
        simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
          Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
          Complex.one_re, Complex.one_im, mul_one]
        linarith [hu.1])
    simpa only [Complex.ofReal_neg, mul_one, add_comm] using h
  have hr_top : IntervalIntegrable
      (fun u : ℝ => balazardContourRemovable s x (u + T * Complex.I)) volume l c := by
    have h := RiemannHypothesis.intervalIntegrable_balazardContourRemovable_affine hRH hs
      (u := (T : ℂ) * Complex.I) (v := 1) (p := l) (q := c) (x := x) (by
        intro u hu
        rw [Set.uIcc_of_le hlc] at hu
        simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
          Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
          Complex.one_re, Complex.one_im, mul_one]
        linarith [hu.1])
    simpa only [mul_one, add_comm] using h
  have hr_right : IntervalIntegrable
      (fun t : ℝ => balazardContourRemovable s x (c + t * Complex.I)) volume (-T) T := by
    apply RiemannHypothesis.intervalIntegrable_balazardContourRemovable_affine hRH hs
      (u := (c : ℂ)) (v := Complex.I)
    intro t _
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    linarith
  have hr_left : IntervalIntegrable
      (fun t : ℝ => balazardContourRemovable s x (l + t * Complex.I)) volume (-T) T := by
    apply RiemannHypothesis.intervalIntegrable_balazardContourRemovable_affine hRH hs
      (u := (l : ℂ)) (v := Complex.I)
    intro t _
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    linarith
  have hbottom :
      (∫ u : ℝ in l..c, balazardContourIntegrand s x (u + (-T) * Complex.I)) =
        analyticReciprocalRiemannZeta s *
            (∫ u : ℝ in l..c, perronIntegrand (Real.log x) (u + (-T) * Complex.I)) +
          ∫ u : ℝ in l..c, balazardContourRemovable s x (u + (-T) * Complex.I) := by
    simp_rw [balazardContourIntegrand]
    rw [intervalIntegral.integral_add (hp_bottom.const_mul _) hr_bottom,
      intervalIntegral.integral_const_mul]
  have htop :
      (∫ u : ℝ in l..c, balazardContourIntegrand s x (u + T * Complex.I)) =
        analyticReciprocalRiemannZeta s *
            (∫ u : ℝ in l..c, perronIntegrand (Real.log x) (u + T * Complex.I)) +
          ∫ u : ℝ in l..c, balazardContourRemovable s x (u + T * Complex.I) := by
    simp_rw [balazardContourIntegrand]
    rw [intervalIntegral.integral_add (hp_top.const_mul _) hr_top,
      intervalIntegral.integral_const_mul]
  have hright :
      (∫ t : ℝ in -T..T, balazardContourIntegrand s x (c + t * Complex.I)) =
        analyticReciprocalRiemannZeta s *
            (∫ t : ℝ in -T..T, perronIntegrand (Real.log x) (c + t * Complex.I)) +
          ∫ t : ℝ in -T..T, balazardContourRemovable s x (c + t * Complex.I) := by
    simp_rw [balazardContourIntegrand]
    rw [intervalIntegral.integral_add (hp_right.const_mul _) hr_right,
      intervalIntegral.integral_const_mul]
  have hleft_eq :
      (∫ t : ℝ in -T..T, balazardContourIntegrand s x (l + t * Complex.I)) =
        analyticReciprocalRiemannZeta s *
            (∫ t : ℝ in -T..T, perronIntegrand (Real.log x) (l + t * Complex.I)) +
          ∫ t : ℝ in -T..T, balazardContourRemovable s x (l + t * Complex.I) := by
    simp_rw [balazardContourIntegrand]
    rw [intervalIntegral.integral_add (hp_left.const_mul _) hr_left,
      intervalIntegral.integral_const_mul]
  rw [hbottom, htop, hright, hleft_eq]
  have hp := perronIntegrand_boundary_rect_eq_two_pi_mul_I
    (a := Real.log x) hl hc hT
  have hr := RiemannHypothesis.balazardContourRemovable_boundary_rect_eq_zero
    hRH hs hl hc hleft (x := x) (T := T)
  linear_combination analyticReciprocalRiemannZeta s * hp + hr

theorem RiemannHypothesis.balazardContourIntegrand_vertical_sub_residue
    (hRH : RiemannHypothesis) {s : ℂ} {x l c T : ℝ}
    (hs : 1 / 2 < s.re) (hl : l < 0) (hc : 0 < c) (hT : 0 < T)
    (hleft : 1 / 2 < s.re + l) :
    (∫ t : ℝ in -T..T, balazardContourIntegrand s x (c + t * Complex.I)) -
        (2 * Real.pi : ℝ) * analyticReciprocalRiemannZeta s =
      (∫ t : ℝ in -T..T, balazardContourIntegrand s x (l + t * Complex.I)) +
        Complex.I *
          ((∫ u : ℝ in l..c,
              balazardContourIntegrand s x (u + (-T) * Complex.I)) -
            ∫ u : ℝ in l..c,
              balazardContourIntegrand s x (u + T * Complex.I)) := by
  have hboundary := RiemannHypothesis.balazardContourIntegrand_boundary_rect
    hRH hs hl hc hT hleft (x := x)
  apply mul_left_cancel₀ Complex.I_ne_zero
  simp only [mul_sub, mul_add, ← mul_assoc, Complex.I_mul_I, neg_one_mul, neg_sub]
  push_cast
  linear_combination hboundary

theorem norm_exp_mul_log_eq_rpow {x : ℝ} (hx : 0 < x) (w : ℂ) :
    ‖Complex.exp (w * Real.log x)‖ = x ^ w.re := by
  rw [Complex.norm_exp]
  have hre : (w * (Real.log x : ℂ)).re = w.re * Real.log x := by
    simp [Complex.mul_re]
  rw [hre, Real.rpow_def_of_pos hx]
  congr 1
  ring

theorem norm_add_mul_I_ge_abs_re (b v : ℝ) :
    |b| ≤ ‖(b : ℂ) + v * Complex.I‖ := by
  simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] using
    Complex.abs_re_le_norm ((b : ℂ) + v * Complex.I)

theorem norm_add_mul_I_ge_abs_im (b v : ℝ) :
    |v| ≤ ‖(b : ℂ) + v * Complex.I‖ := by
  simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_re, Complex.I_im, zero_add, mul_one, mul_zero, sub_zero, add_zero] using
    Complex.abs_im_le_norm ((b : ℂ) + v * Complex.I)

theorem RiemannHypothesis.norm_balazardContourIntegrand_le
    (hRH : RiemannHypothesis) {s w : ℂ} {x B : ℝ}
    (hx : 0 < x) (hw : w ≠ 0) (hsw_re : 1 / 2 < (s + w).re)
    (hsw_one : s + w ≠ 1)
    (hrecip : ‖(riemannZeta (s + w))⁻¹‖ ≤ B) :
    ‖balazardContourIntegrand s x w‖ ≤ B * x ^ w.re / ‖w‖ := by
  rw [balazardContourIntegrand_eq hw,
    RiemannHypothesis.reciprocalZetaPoleRemoved_eq_inv hRH hsw_re hsw_one,
    norm_div, norm_mul, norm_exp_mul_log_eq_rpow hx]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hrecip (Real.rpow_nonneg hx.le _)) (norm_nonneg _)

/-- The real majorant left after separating the external height in a vertical contour integral. -/
def verticalPerronMajorant (b q v : ℝ) : ℝ :=
  (1 + |v|) ^ q / ‖(b : ℂ) + v * Complex.I‖

theorem verticalPerronMajorant_even (b q v : ℝ) :
    verticalPerronMajorant b q (-v) = verticalPerronMajorant b q v := by
  have hnorm : ‖(b : ℂ) + (-v) * Complex.I‖ = ‖(b : ℂ) + v * Complex.I‖ := by
    have heq : (b : ℂ) + (-v) * Complex.I = star ((b : ℂ) + v * Complex.I) := by
      apply Complex.ext <;> simp
    rw [heq, norm_star]
  unfold verticalPerronMajorant
  rw [abs_neg]
  push_cast
  rw [hnorm]

theorem continuous_verticalPerronMajorant {b q : ℝ} (hb : b ≠ 0) :
    Continuous (verticalPerronMajorant b q) := by
  unfold verticalPerronMajorant
  apply Continuous.div₀
  · exact (continuous_const.add continuous_abs).rpow_const
      (fun v => Or.inl (by change 1 + |v| ≠ 0; positivity))
  · fun_prop
  · intro v hv
    have hz : (b : ℂ) + v * Complex.I = 0 := norm_eq_zero.mp hv
    have hre := congrArg Complex.re hz
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
      Complex.zero_re] at hre
    exact hb hre

theorem verticalPerronMajorant_le_small
    {b q v : ℝ} (hb : b ≠ 0) (hq : 0 ≤ q) (hv : |v| ≤ 1) :
    verticalPerronMajorant b q v ≤ 2 ^ q / |b| := by
  have hnum : (1 + |v|) ^ q ≤ 2 ^ q :=
    Real.rpow_le_rpow (by positivity) (by linarith [abs_nonneg v]) hq
  have hden : |b| ≤ ‖(b : ℂ) + v * Complex.I‖ := norm_add_mul_I_ge_abs_re b v
  have hbabs : 0 < |b| := abs_pos.mpr hb
  unfold verticalPerronMajorant
  calc
    (1 + |v|) ^ q / ‖(b : ℂ) + v * Complex.I‖ ≤
        2 ^ q / ‖(b : ℂ) + v * Complex.I‖ :=
      div_le_div_of_nonneg_right hnum (norm_nonneg _)
    _ ≤ 2 ^ q / |b| :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg (by norm_num) _) hbabs hden

theorem verticalPerronMajorant_le_large
    {b q v : ℝ} (hq : 0 ≤ q) (hv : 1 ≤ v) :
    verticalPerronMajorant b q v ≤ 2 ^ q * v ^ (q - 1) := by
  have hvpos : 0 < v := zero_lt_one.trans_le hv
  have hvabs : |v| = v := abs_of_pos hvpos
  have hbase : 1 + v ≤ 2 * v := by linarith
  have hpow : (1 + v) ^ q ≤ (2 * v) ^ q :=
    Real.rpow_le_rpow (by positivity) hbase hq
  have hden : v ≤ ‖(b : ℂ) + v * Complex.I‖ := by
    simpa only [abs_of_pos hvpos] using norm_add_mul_I_ge_abs_im b v
  unfold verticalPerronMajorant
  rw [hvabs]
  calc
    (1 + v) ^ q / ‖(b : ℂ) + v * Complex.I‖ ≤ (2 * v) ^ q / v :=
      (div_le_div_of_nonneg_right hpow (norm_nonneg _)).trans
        (div_le_div_of_nonneg_left (Real.rpow_nonneg (by positivity) _) hvpos hden)
    _ = 2 ^ q * v ^ (q - 1) := by
      rw [Real.mul_rpow (by norm_num) hvpos.le, div_eq_mul_inv,
        ← Real.rpow_neg_one]
      calc
        2 ^ q * v ^ q * v ^ (-1 : ℝ) = 2 ^ q * (v ^ q * v ^ (-1 : ℝ)) := by ring
        _ = 2 ^ q * v ^ (q + (-1 : ℝ)) := by rw [← Real.rpow_add hvpos]
        _ = 2 ^ q * v ^ (q - 1) := by ring_nf

theorem integral_verticalPerronMajorant_le
    {b q T : ℝ} (hb : b ≠ 0) (hq : 0 < q) (hT : 1 ≤ T) :
    (∫ v : ℝ in -T..T, verticalPerronMajorant b q v) ≤
      2 * 2 ^ q * (|b|⁻¹ + q⁻¹) * T ^ q := by
  let f : ℝ → ℝ := verticalPerronMajorant b q
  have hf : ∀ a c : ℝ, IntervalIntegrable f volume a c := by
    intro a c
    exact (continuous_verticalPerronMajorant hb).intervalIntegrable a c
  have heven : ∀ v : ℝ, f (-v) = f v := verticalPerronMajorant_even b q
  have hneg : (∫ v : ℝ in -T..0, f v) = ∫ v : ℝ in 0..T, f v := by
    calc
      (∫ v : ℝ in -T..0, f v) = ∫ v : ℝ in -T..0, f (-v) := by
        apply intervalIntegral.integral_congr
        intro v _
        exact (heven v).symm
      _ = ∫ v : ℝ in 0..T, f v := by
        simpa using (intervalIntegral.integral_comp_neg (f := f) (a := -T) (b := 0))
  have hsymm : (∫ v : ℝ in -T..T, f v) = 2 * ∫ v : ℝ in 0..T, f v := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hf (-T) 0) (hf 0 T), hneg]
    ring
  have hsmall : (∫ v : ℝ in 0..1, f v) ≤ 2 ^ q / |b| := by
    calc
      (∫ v : ℝ in 0..1, f v) ≤ ∫ _v : ℝ in 0..1, 2 ^ q / |b| := by
        refine intervalIntegral.integral_mono_on (by norm_num) (hf 0 1) (by simp) ?_
        intro v hv
        exact verticalPerronMajorant_le_small hb hq.le (by
          rw [abs_of_nonneg hv.1]
          exact hv.2)
      _ = 2 ^ q / |b| := by simp
  have hg : IntervalIntegrable (fun v : ℝ => 2 ^ q * v ^ (q - 1)) volume 1 T :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < q - 1)).const_mul _
  have hlarge : (∫ v : ℝ in 1..T, f v) ≤ 2 ^ q * T ^ q / q := by
    calc
      (∫ v : ℝ in 1..T, f v) ≤ ∫ v : ℝ in 1..T, 2 ^ q * v ^ (q - 1) := by
        refine intervalIntegral.integral_mono_on hT (hf 1 T) hg ?_
        intro v hv
        exact verticalPerronMajorant_le_large hq.le hv.1
      _ = 2 ^ q * ((T ^ q - 1 ^ q) / q) := by
        rw [intervalIntegral.integral_const_mul,
          integral_rpow (a := 1) (b := T) (r := q - 1) (Or.inl (by linarith))]
        congr 1
        ring_nf
      _ ≤ 2 ^ q * T ^ q / q := by
        have hqpow : 0 ≤ (2 : ℝ) ^ q := Real.rpow_nonneg (by norm_num) _
        have hTpow : 0 ≤ T ^ q := Real.rpow_nonneg (by linarith) _
        rw [Real.one_rpow]
        calc
          2 ^ q * ((T ^ q - 1) / q) ≤ 2 ^ q * (T ^ q / q) := by
            apply mul_le_mul_of_nonneg_left _ hqpow
            exact (div_le_div_iff_of_pos_right hq).2 (by linarith)
          _ = 2 ^ q * T ^ q / q := by ring
  have hsplit : (∫ v : ℝ in 0..T, f v) =
      (∫ v : ℝ in 0..1, f v) + ∫ v : ℝ in 1..T, f v := by
    exact (intervalIntegral.integral_add_adjacent_intervals (hf 0 1) (hf 1 T)).symm
  have hTq_one : 1 ≤ T ^ q := Real.one_le_rpow hT hq.le
  rw [hsymm, hsplit]
  calc
    2 * ((∫ v : ℝ in 0..1, f v) + ∫ v : ℝ in 1..T, f v) ≤
        2 * (2 ^ q / |b| + 2 ^ q * T ^ q / q) := by
      gcongr
    _ ≤ 2 * 2 ^ q * (|b|⁻¹ + q⁻¹) * T ^ q := by
      have hbabs : 0 < |b| := abs_pos.mpr hb
      have htwoq : 0 ≤ (2 : ℝ) ^ q := Real.rpow_nonneg (by norm_num) _
      rw [div_eq_mul_inv, div_eq_mul_inv]
      nlinarith [inv_pos.mpr hbabs, inv_pos.mpr hq,
        mul_le_mul_of_nonneg_left hTq_one (mul_nonneg htwoq (inv_pos.mpr hbabs).le)]

theorem two_add_abs_add_le_mul (t v : ℝ) :
    2 + |t + v| ≤ (2 + |t|) * (1 + |v|) := by
  calc
    2 + |t + v| ≤ 2 + (|t| + |v|) := by gcongr; exact abs_add_le t v
    _ ≤ (2 + |t|) * (1 + |v|) := by
      nlinarith [abs_nonneg t, abs_nonneg v]

theorem rpow_two_add_abs_add_le
    {q : ℝ} (hq : 0 ≤ q) (t v : ℝ) :
    (2 + |t + v|) ^ q ≤ (2 + |t|) ^ q * (1 + |v|) ^ q := by
  calc
    (2 + |t + v|) ^ q ≤ ((2 + |t|) * (1 + |v|)) ^ q :=
      Real.rpow_le_rpow (by positivity) (two_add_abs_add_le_mul t v) hq
    _ = (2 + |t|) ^ q * (1 + |v|) ^ q := by
      rw [Real.mul_rpow (by positivity) (by positivity)]

theorem RiemannHypothesis.norm_balazard_left_vertical_integral_le
    (hRH : RiemannHypothesis) {s : ℂ} {x b T q C d : ℝ}
    (hx : 0 < x) (hb : b < 0) (hT : 1 ≤ T) (hq : 0 < q)
    (hd : 0 < d) (hd_lt : d < 1 / 2)
    (hline : s.re + b = 1 / 2 + d)
    (hC : 0 ≤ C)
    (hrecip : ∀ z : ℂ, z.re ∈ Set.Icc (1 / 2 + d : ℝ) 3 →
      ‖(riemannZeta z)⁻¹‖ ≤ C * (2 + |z.im|) ^ q) :
    ‖∫ v : ℝ in -T..T,
        balazardContourIntegrand s x (b + v * Complex.I)‖ ≤
      (C * x ^ b * (2 + |s.im|) ^ q) *
        (2 * 2 ^ q * (|b|⁻¹ + q⁻¹) * T ^ q) := by
  have hb0 : b ≠ 0 := hb.ne
  let K : ℝ := C * x ^ b * (2 + |s.im|) ^ q
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hg : IntervalIntegrable (fun v : ℝ => K * verticalPerronMajorant b q v)
      volume (-T) T :=
    ((continuous_verticalPerronMajorant hb0).intervalIntegrable (-T) T).const_mul _
  have hpoint : ∀ v : ℝ,
      ‖balazardContourIntegrand s x (b + v * Complex.I)‖ ≤
        K * verticalPerronMajorant b q v := by
    intro v
    let w : ℂ := (b : ℂ) + v * Complex.I
    let z : ℂ := s + w
    have hw : w ≠ 0 := by
      intro hw0
      have hre := congrArg Complex.re hw0
      simp [w] at hre
      exact hb0 hre
    have hz_re : z.re = 1 / 2 + d := by
      simp only [z, w, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
      exact hline
    have hz_im : z.im = s.im + v := by
      simp [z, w]
    have hz_half : 1 / 2 < z.re := by rw [hz_re]; linarith
    have hz_one : z ≠ 1 := by
      intro hz1
      have hre := congrArg Complex.re hz1
      rw [hz_re] at hre
      simp only [Complex.one_re] at hre
      linarith [hd_lt]
    have hz_mem : z.re ∈ Set.Icc (1 / 2 + d : ℝ) 3 := by
      rw [hz_re]
      constructor
      · exact le_rfl
      · linarith [hd_lt]
    have hraw := RiemannHypothesis.norm_balazardContourIntegrand_le hRH hx hw
      hz_half hz_one (hrecip z hz_mem)
    have hheight := rpow_two_add_abs_add_le hq.le s.im v
    have hxpow : 0 ≤ x ^ b := Real.rpow_nonneg hx.le _
    have hden : 0 ≤ ‖w‖ := norm_nonneg _
    rw [show w.re = b by simp [w], hz_im] at hraw
    calc
      ‖balazardContourIntegrand s x (b + v * Complex.I)‖ =
          ‖balazardContourIntegrand s x w‖ := rfl
      _ ≤ (C * (2 + |s.im + v|) ^ q) * x ^ b / ‖w‖ := hraw
      _ ≤ (C * ((2 + |s.im|) ^ q * (1 + |v|) ^ q)) * x ^ b / ‖w‖ := by
        apply div_le_div_of_nonneg_right _ hden
        gcongr
      _ = K * verticalPerronMajorant b q v := by
        dsimp only [K, verticalPerronMajorant, w]
        ring
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le (show -T ≤ T by linarith)
    (Filter.Eventually.of_forall fun v _ => hpoint v) hg
  rw [intervalIntegral.integral_const_mul] at hnorm
  calc
    ‖∫ v : ℝ in -T..T, balazardContourIntegrand s x (b + v * Complex.I)‖ ≤
        K * ∫ v : ℝ in -T..T, verticalPerronMajorant b q v := hnorm
    _ ≤ K * (2 * 2 ^ q * (|b|⁻¹ + q⁻¹) * T ^ q) :=
      mul_le_mul_of_nonneg_left (integral_verticalPerronMajorant_le hb0 hq hT) hK
    _ = (C * x ^ b * (2 + |s.im|) ^ q) *
        (2 * 2 ^ q * (|b|⁻¹ + q⁻¹) * T ^ q) := rfl

theorem RiemannHypothesis.norm_balazard_horizontal_integral_le
    (hRH : RiemannHypothesis) {s : ℂ} {x b y q C d : ℝ}
    (hx : 1 ≤ x) (hb2 : b ≤ 2) (hy : 0 < |y|) (hzy : s.im + y ≠ 0)
    (hd : 0 < d) (hd_lt : d < 1 / 2)
    (hline : s.re + b = 1 / 2 + d) (hs_top : s.re ≤ 1)
    (hC : 0 ≤ C)
    (hrecip : ∀ z : ℂ, z.re ∈ Set.Icc (1 / 2 + d : ℝ) 3 →
      ‖(riemannZeta z)⁻¹‖ ≤ C * (2 + |z.im|) ^ q) :
    ‖∫ u : ℝ in b..2,
        balazardContourIntegrand s x (u + y * Complex.I)‖ ≤
      (C * (2 + |s.im + y|) ^ q * x ^ (2 : ℝ) / |y|) * |2 - b| := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  let B : ℝ := C * (2 + |s.im + y|) ^ q * x ^ (2 : ℝ) / |y|
  have hpoint : ∀ u ∈ Set.uIcc b 2,
      ‖balazardContourIntegrand s x (u + y * Complex.I)‖ ≤ B := by
    intro u hu
    rw [Set.uIcc_of_le hb2] at hu
    let w : ℂ := (u : ℂ) + y * Complex.I
    let z : ℂ := s + w
    have hw : w ≠ 0 := by
      intro hw0
      have him := congrArg Complex.im hw0
      simp [w] at him
      exact hy.ne' (by simpa [him])
    have hz_re : z.re = s.re + u := by simp [z, w]
    have hz_im : z.im = s.im + y := by simp [z, w]
    have hz_lower : 1 / 2 + d ≤ z.re := by rw [hz_re]; linarith [hu.1]
    have hz_upper : z.re ≤ 3 := by rw [hz_re]; linarith [hu.2]
    have hz_half : 1 / 2 < z.re := lt_of_lt_of_le (by linarith) hz_lower
    have hz_one : z ≠ 1 := by
      intro hz1
      have him := congrArg Complex.im hz1
      rw [hz_im] at him
      simp only [Complex.one_im] at him
      exact hzy him
    have hraw := RiemannHypothesis.norm_balazardContourIntegrand_le hRH hxpos hw
      hz_half hz_one (hrecip z ⟨hz_lower, hz_upper⟩)
    have hxpow : x ^ u ≤ x ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx hu.2
    have hden : |y| ≤ ‖w‖ := by
      simpa only [w] using norm_add_mul_I_ge_abs_im u y
    rw [show w.re = u by simp [w], hz_im] at hraw
    calc
      ‖balazardContourIntegrand s x (u + y * Complex.I)‖ =
          ‖balazardContourIntegrand s x w‖ := rfl
      _ ≤ (C * (2 + |s.im + y|) ^ q) * x ^ u / ‖w‖ := hraw
      _ ≤ (C * (2 + |s.im + y|) ^ q) * x ^ (2 : ℝ) / |y| := by
        have hA : 0 ≤ C * (2 + |s.im + y|) ^ q := by positivity
        calc
          (C * (2 + |s.im + y|) ^ q) * x ^ u / ‖w‖ ≤
              (C * (2 + |s.im + y|) ^ q) * x ^ (2 : ℝ) / ‖w‖ :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hxpow hA) (norm_nonneg _)
          _ ≤ (C * (2 + |s.im + y|) ^ q) * x ^ (2 : ℝ) / |y| :=
            div_le_div_of_nonneg_left (by positivity) hy hden
      _ = B := rfl
  exact intervalIntegral.norm_integral_le_of_norm_le_const
    (fun u hu => hpoint u (Set.uIoc_subset_uIcc hu))

theorem mobiusTruncatedPerronIntegral_eq_balazard_right
    {N : ℕ} {T : ℝ} {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    mobiusTruncatedPerronIntegral N T s =
      (2 * (Real.pi : ℂ))⁻¹ *
        ∫ t : ℝ in -T..T,
          balazardContourIntegrand s ((N : ℝ) + 1 / 2) (2 + t * Complex.I) := by
  rw [mobiusTruncatedPerronIntegral]
  apply congrArg (fun z : ℂ => (2 * (Real.pi : ℂ))⁻¹ * z)
  apply intervalIntegral.integral_congr
  intro t _
  let w : ℂ := (2 : ℂ) + t * Complex.I
  let z : ℂ := s + w
  have hw : w ≠ 0 := by
    intro hw0
    have hre := congrArg Complex.re hw0
    simp [w] at hre
  have hz_re : 1 < z.re := by
    norm_num [z, w, Complex.add_re, Complex.mul_re]
    linarith
  have hz_one : z ≠ 1 := by
    intro hz1
    have hre := congrArg Complex.re hz1
    simp only [Complex.one_re] at hre
    linarith
  symm
  change balazardContourIntegrand s ((N : ℝ) + 1 / 2) w = _
  rw [balazardContourIntegrand_eq hw,
    analyticReciprocalRiemannZeta_eq_inv hz_one
      (riemannZeta_ne_zero_of_one_lt_re hz_re)]
  dsimp only [z, w]
  ring

theorem RiemannHypothesis.norm_mobiusTruncatedPerronIntegral_sub_analyticReciprocal_le
    (hRH : RiemannHypothesis) {N : ℕ} {T : ℝ} {s : ℂ} {b : ℝ}
    (hs : 1 / 2 < s.re) (hb : b < 0) (hT : 0 < T)
    (hleft : 1 / 2 < s.re + b) :
    ‖mobiusTruncatedPerronIntegral N T s - analyticReciprocalRiemannZeta s‖ ≤
      (2 * Real.pi)⁻¹ *
        (‖∫ v : ℝ in -T..T,
            balazardContourIntegrand s ((N : ℝ) + 1 / 2) (b + v * Complex.I)‖ +
          ‖∫ u : ℝ in b..2,
            balazardContourIntegrand s ((N : ℝ) + 1 / 2) (u + (-T) * Complex.I)‖ +
          ‖∫ u : ℝ in b..2,
            balazardContourIntegrand s ((N : ℝ) + 1 / 2) (u + T * Complex.I)‖) := by
  let x : ℝ := (N : ℝ) + 1 / 2
  let k : ℂ := (2 * (Real.pi : ℂ))⁻¹
  let R : ℂ := ∫ v : ℝ in -T..T, balazardContourIntegrand s x (2 + v * Complex.I)
  let L : ℂ := ∫ v : ℝ in -T..T, balazardContourIntegrand s x (b + v * Complex.I)
  let B : ℂ := ∫ u : ℝ in b..2, balazardContourIntegrand s x (u + (-T) * Complex.I)
  let U : ℂ := ∫ u : ℝ in b..2, balazardContourIntegrand s x (u + T * Complex.I)
  have hright : mobiusTruncatedPerronIntegral N T s = k * R := by
    simpa only [x, k, R] using
      (mobiusTruncatedPerronIntegral_eq_balazard_right (N := N) (T := T) (s := s) hs.le)
  have hres : R - (2 * Real.pi : ℝ) * analyticReciprocalRiemannZeta s =
      L + Complex.I * (B - U) := by
    have h := RiemannHypothesis.balazardContourIntegrand_vertical_sub_residue
      hRH hs hb (by norm_num) hT hleft (x := x) (c := 2)
    change R - (2 * Real.pi : ℝ) * analyticReciprocalRiemannZeta s =
      L + Complex.I * (B - U) at h
    exact h
  have hkres : k * ((2 * Real.pi : ℝ) * analyticReciprocalRiemannZeta s) =
      analyticReciprocalRiemannZeta s := by
    dsimp only [k]
    have hpi : (2 * (Real.pi : ℂ)) ≠ 0 :=
      mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    push_cast
    field_simp [hpi]
  have hcoeff : ‖k‖ = (2 * Real.pi)⁻¹ := by
    dsimp only [k]
    simp [Complex.norm_real, abs_of_pos Real.pi_pos]
  rw [hright, ← hkres, ← mul_sub, hres, norm_mul, hcoeff]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    ‖L + Complex.I * (B - U)‖ ≤ ‖L‖ + ‖Complex.I * (B - U)‖ := norm_add_le _ _
    _ = ‖L‖ + ‖B - U‖ := by rw [norm_mul, Complex.norm_I, one_mul]
    _ ≤ ‖L‖ + (‖B‖ + ‖U‖) := by gcongr; exact norm_sub_le B U
    _ = ‖L‖ + ‖B‖ + ‖U‖ := by ring

theorem balazard_left_power_balance
    {δ η q x H b T : ℝ} (hx : 1 ≤ x) (hH : 1 ≤ H)
    (hq : 0 ≤ q) (hqδ : q ≤ δ / 12) (hqη : 2 * q ≤ η)
    (hb : b ≤ -2 * δ / 3) (hT : T = x ^ (3 : ℝ) * H) :
    x ^ b * (1 + H) ^ q * T ^ q ≤
      2 ^ q * x ^ (-δ / 3) * H ^ η := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  have honeH : 1 + H ≤ 2 * H := by linarith
  have hxb : x ^ b ≤ x ^ (-2 * δ / 3) :=
    Real.rpow_le_rpow_of_exponent_le hx hb
  have hheight : (1 + H) ^ q ≤ (2 * H) ^ q :=
    Real.rpow_le_rpow (by positivity) honeH hq
  rw [hT]
  calc
    x ^ b * (1 + H) ^ q * (x ^ (3 : ℝ) * H) ^ q ≤
        x ^ (-2 * δ / 3) * (2 * H) ^ q * (x ^ (3 : ℝ) * H) ^ q := by
      gcongr
    _ = 2 ^ q * x ^ (-2 * δ / 3 + 3 * q) * H ^ (2 * q) := by
      rw [Real.mul_rpow (by norm_num) hHpos.le]
      rw [Real.mul_rpow (Real.rpow_nonneg hxpos.le _) hHpos.le]
      rw [← Real.rpow_mul hxpos.le]
      calc
        x ^ (-2 * δ / 3) * (2 ^ q * H ^ q) * (x ^ (3 * q) * H ^ q) =
            2 ^ q * (x ^ (-2 * δ / 3) * x ^ (3 * q)) * (H ^ q * H ^ q) := by ring
        _ = 2 ^ q * x ^ (-2 * δ / 3 + 3 * q) * H ^ (q + q) := by
          rw [← Real.rpow_add hxpos, ← Real.rpow_add hHpos]
        _ = 2 ^ q * x ^ (-2 * δ / 3 + 3 * q) * H ^ (2 * q) := by ring_nf
    _ ≤ 2 ^ q * x ^ (-δ / 3) * H ^ η := by
      have hxexp : -2 * δ / 3 + 3 * q ≤ -δ / 3 := by linarith
      have hxp := Real.rpow_le_rpow_of_exponent_le hx hxexp
      have hHp := Real.rpow_le_rpow_of_exponent_le hH hqη
      gcongr

theorem balazard_horizontal_power_balance
    {δ η q x H T : ℝ} (hx : 1 ≤ x) (hH : 1 ≤ H)
    (hδ : δ ≤ 1 / 2) (hq : 0 ≤ q) (hqδ : q ≤ δ / 12)
    (hqη : q - 1 ≤ η) (hT : T = x ^ (3 : ℝ) * H) :
    x ^ (2 : ℝ) / T * (3 * T) ^ q ≤
      3 ^ q * x ^ (-δ / 3) * H ^ η := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  have hTpos : 0 < T := by rw [hT]; positivity
  have h3T : (3 * T) ^ q = 3 ^ q * T ^ q :=
    Real.mul_rpow (by norm_num) hTpos.le
  have hcombine : x ^ (2 : ℝ) / T * T ^ q =
      x ^ (2 : ℝ) * T ^ (q - 1) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one]
    calc
      x ^ (2 : ℝ) * T ^ (-1 : ℝ) * T ^ q =
          x ^ (2 : ℝ) * (T ^ (-1 : ℝ) * T ^ q) := by ring
      _ = x ^ (2 : ℝ) * T ^ ((-1 : ℝ) + q) := by rw [← Real.rpow_add hTpos]
      _ = x ^ (2 : ℝ) * T ^ (q - 1) := by ring_nf
  have hxexp : -1 + 3 * q ≤ -δ / 3 := by linarith
  have hxp := Real.rpow_le_rpow_of_exponent_le hx hxexp
  have hHp := Real.rpow_le_rpow_of_exponent_le hH hqη
  calc
    x ^ (2 : ℝ) / T * (3 * T) ^ q =
        3 ^ q * (x ^ (2 : ℝ) / T * T ^ q) := by rw [h3T]; ring
    _ = 3 ^ q * (x ^ (2 : ℝ) * T ^ (q - 1)) := by rw [hcombine]
    _ = 3 ^ q * (x ^ (-1 + 3 * q) * H ^ (q - 1)) := by
      rw [hT, Real.mul_rpow (Real.rpow_nonneg hxpos.le _) hHpos.le,
        ← Real.rpow_mul hxpos.le]
      calc
        3 ^ q * (x ^ (2 : ℝ) * (x ^ (3 * (q - 1)) * H ^ (q - 1))) =
            3 ^ q * ((x ^ (2 : ℝ) * x ^ (3 * (q - 1))) * H ^ (q - 1)) := by ring
        _ = 3 ^ q * (x ^ ((2 : ℝ) + 3 * (q - 1)) * H ^ (q - 1)) := by
          rw [← Real.rpow_add hxpos]
        _ = 3 ^ q * (x ^ (-1 + 3 * q) * H ^ (q - 1)) := by ring_nf
    _ ≤ 3 ^ q * (x ^ (-δ / 3) * H ^ η) := by gcongr
    _ = 3 ^ q * x ^ (-δ / 3) * H ^ η := by ring

theorem balazard_truncation_power_balance
    {δ η n x H T : ℝ} (hn : 1 ≤ n) (hx : x = n + 1 / 2)
    (hH : 1 ≤ H) (hδ : 0 < δ) (hδ_top : δ ≤ 1 / 2) (hη : 0 < η)
    (hT : T = x ^ (3 : ℝ) * H) :
    (n + 1) ^ 2 / T ≤ 4 * n ^ (-δ / 3) * H ^ η := by
  have hxone : 1 ≤ x := by rw [hx]; linarith
  have hsq : (n + 1) ^ 2 ≤ 4 * x ^ (2 : ℝ) := by
    have hlin : n + 1 ≤ 2 * x := by rw [hx]; linarith
    rw [Real.rpow_two]
    nlinarith [sq_nonneg (n + 1), sq_nonneg x]
  have hTpos : 0 < T := by rw [hT]; positivity
  have hcore := balazard_horizontal_power_balance
    hxone hH hδ_top (show (0 : ℝ) ≤ 0 by rfl) (by linarith : (0 : ℝ) ≤ δ / 12)
    (by linarith : (0 : ℝ) - 1 ≤ η) hT
  simp only [Real.rpow_zero, mul_one, one_mul] at hcore
  calc
    (n + 1) ^ 2 / T ≤ (4 * x ^ (2 : ℝ)) / T :=
      div_le_div_of_nonneg_right hsq hTpos.le
    _ = 4 * (x ^ (2 : ℝ) / T) := by ring
    _ ≤ 4 * (x ^ (-δ / 3) * H ^ η) := by gcongr
    _ ≤ 4 * (n ^ (-δ / 3) * H ^ η) := by
      have hnpos : 0 < n := zero_lt_one.trans_le hn
      have hnx : n ≤ x := by rw [hx]; linarith
      have hexp : -δ / 3 ≤ 0 := by linarith
      have hp := Real.rpow_le_rpow_of_nonpos hnpos hnx hexp
      gcongr
    _ = 4 * n ^ (-δ / 3) * H ^ η := by ring

/-- The RH-specialized Balazard--Saias estimate, compiled from the truncated Perron formula,
contour shifting, and the reciprocal-zeta subpower bound. -/
theorem RiemannHypothesis.exists_balazardSaias_specialized_bound_compiled
    (hRH : RiemannHypothesis) {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (s : ℂ),
      2 ≤ N → (1 / 2 : ℝ) + δ ≤ s.re → s.re ≤ 1 →
        ‖mobiusDirichletPartialSum N s - analyticReciprocalRiemannZeta s‖ ≤
          C * (N : ℝ) ^ (-δ / 3) * (1 + |s.im|) ^ η := by
  by_cases hδ_top : δ ≤ 1 / 2
  · let d : ℝ := δ / 3
    let q : ℝ := min (δ / 12) (η / 2)
    have hd : 0 < d := by dsimp only [d]; linarith
    have hd_lt : d < 1 / 2 := by dsimp only [d]; linarith
    have hq : 0 < q := by
      dsimp only [q]
      exact lt_min (by linarith) (by linarith)
    have hqδ : q ≤ δ / 12 := by dsimp only [q]; exact min_le_left _ _
    have hqη : q ≤ η / 2 := by dsimp only [q]; exact min_le_right _ _
    have htwoqη : 2 * q ≤ η := by linarith
    have hqsubη : q - 1 ≤ η := by linarith
    obtain ⟨P, hP, hperron⟩ :=
      exists_mobiusDirichletPartialSum_sub_truncatedPerronIntegral_le
    obtain ⟨Z, hZ, hrecip⟩ :=
      RiemannHypothesis.exists_reciprocalZeta_rpow_bound_two_add
        hRH hd (by dsimp only [d]; linarith) hq
    let K : ℝ := 3 / (2 * δ) + q⁻¹
    let Lc : ℝ := Z * 2 ^ q * (2 * 2 ^ q * K)
    let Hc : ℝ := 3 * Z * 3 ^ q
    let Rc : ℝ := (2 * Real.pi)⁻¹ * (Lc + 2 * Hc)
    let C : ℝ := 4 * P + Rc + 1
    have hK : 0 < K := by dsimp only [K]; positivity
    have hLc : 0 < Lc := by dsimp only [Lc]; positivity
    have hHc : 0 < Hc := by dsimp only [Hc]; positivity
    have hRc : 0 < Rc := by dsimp only [Rc]; positivity
    have hC : 0 < C := by dsimp only [C]; linarith
    refine ⟨C, hC, ?_⟩
    intro N s hN hs_lower hs_top
    let n : ℝ := N
    let x : ℝ := n + 1 / 2
    let H : ℝ := 1 + |s.im|
    let T : ℝ := x ^ (3 : ℝ) * H
    let b : ℝ := 1 / 2 + d - s.re
    have hn : 1 ≤ n := by dsimp only [n]; exact_mod_cast (show 1 ≤ N by omega)
    have hx : 1 ≤ x := by dsimp only [x]; linarith
    have hxpos : 0 < x := zero_lt_one.trans_le hx
    have hH : 1 ≤ H := by dsimp only [H]; linarith [abs_nonneg s.im]
    have hHpos : 0 < H := zero_lt_one.trans_le hH
    have hxpow : 1 ≤ x ^ (3 : ℝ) := Real.one_le_rpow hx (by norm_num)
    have hT_H : H ≤ T := by
      dsimp only [T]
      nlinarith [Real.rpow_nonneg hxpos.le (3 : ℝ)]
    have hT : 1 ≤ T := hH.trans hT_H
    have hTpos : 0 < T := zero_lt_one.trans_le hT
    have hT_im : |s.im| < T := by
      have : |s.im| < H := by dsimp only [H]; linarith
      exact this.trans_le hT_H
    have hs_half : 1 / 2 ≤ s.re := by linarith
    have hs_half_strict : 1 / 2 < s.re := by linarith
    have hline : s.re + b = 1 / 2 + d := by dsimp only [b]; ring
    have hbstrong : b ≤ -2 * δ / 3 := by dsimp only [b, d]; linarith
    have hb : b < 0 := lt_of_le_of_lt hbstrong (by linarith)
    have hb2 : b ≤ 2 := by linarith
    have hleft : 1 / 2 < s.re + b := by rw [hline]; linarith
    have habs_lower : 2 * δ / 3 ≤ |b| := by
      rw [abs_of_neg hb]
      linarith
    have habs_pos : 0 < |b| := abs_pos.mpr hb.ne
    have hinv : |b|⁻¹ ≤ 3 / (2 * δ) := by
      have hbase : 0 < 2 * δ / 3 := by linarith
      have hi := (inv_le_inv₀ habs_pos hbase).2 habs_lower
      calc
        |b|⁻¹ ≤ (2 * δ / 3)⁻¹ := hi
        _ = 3 / (2 * δ) := by field_simp [hδ.ne']
    have hlen : |2 - b| ≤ 3 := by
      rw [abs_of_nonneg (by linarith)]
      dsimp only [b, d]
      linarith
    have hplus_ne : s.im + T ≠ 0 := by
      intro hzero
      have heq : s.im = -T := by linarith
      have habs : |s.im| = T := by rw [heq, abs_neg, abs_of_pos hTpos]
      rw [habs] at hT_im
      exact lt_irrefl T hT_im
    have hminus_ne : s.im + -T ≠ 0 := by
      intro hzero
      have : s.im = T := by linarith
      rw [this, abs_of_pos hTpos] at hT_im
      exact lt_irrefl T hT_im
    have hheight_plus : 2 + |s.im + T| ≤ 3 * T := by
      calc
        2 + |s.im + T| ≤ 2 + (|s.im| + |T|) := by
          gcongr
          exact abs_add_le s.im T
        _ = 2 + |s.im| + T := by rw [abs_of_pos hTpos]; ring
        _ ≤ 3 * T := by
          dsimp only [H] at hT_H
          linarith
    have hheight_minus : 2 + |s.im + -T| ≤ 3 * T := by
      calc
        2 + |s.im + -T| ≤ 2 + (|s.im| + |-T|) := by
          gcongr
          exact abs_add_le s.im (-T)
        _ = 2 + |s.im| + T := by rw [abs_neg, abs_of_pos hTpos]; ring
        _ ≤ 3 * T := by
          dsimp only [H] at hT_H
          linarith
    have hbase_nonneg : 0 ≤ x ^ (-δ / 3) * H ^ η := by positivity
    have hleft_raw := RiemannHypothesis.norm_balazard_left_vertical_integral_le
      hRH hxpos hb hT hq hd hd_lt hline hZ.le hrecip
    have hleft_bal := balazard_left_power_balance hx hH hq.le hqδ htwoqη hbstrong rfl
    have hleft_bound :
        ‖∫ v : ℝ in -T..T,
            balazardContourIntegrand s x (b + v * Complex.I)‖ ≤
          Lc * (x ^ (-δ / 3) * H ^ η) := by
      calc
        ‖∫ v : ℝ in -T..T,
            balazardContourIntegrand s x (b + v * Complex.I)‖ ≤
            (Z * x ^ b * (2 + |s.im|) ^ q) *
              (2 * 2 ^ q * (|b|⁻¹ + q⁻¹) * T ^ q) := hleft_raw
        _ ≤ (Z * x ^ b * (2 + |s.im|) ^ q) *
              (2 * 2 ^ q * K * T ^ q) := by
          have hsum : |b|⁻¹ + q⁻¹ ≤ K := by dsimp only [K]; linarith
          gcongr
        _ = (Z * (2 * 2 ^ q * K)) *
              (x ^ b * (1 + H) ^ q * T ^ q) := by
          dsimp only [H]
          ring
        _ ≤ (Z * (2 * 2 ^ q * K)) *
              (2 ^ q * x ^ (-δ / 3) * H ^ η) := by gcongr
        _ = Lc * (x ^ (-δ / 3) * H ^ η) := by dsimp only [Lc]; ring
    have hhorizontal (y : ℝ) (hyabs : |y| = T) (hyne : s.im + y ≠ 0)
        (hheight : 2 + |s.im + y| ≤ 3 * T) :
        ‖∫ u : ℝ in b..2,
            balazardContourIntegrand s x (u + y * Complex.I)‖ ≤
          Hc * (x ^ (-δ / 3) * H ^ η) := by
      have hy : 0 < |y| := by rw [hyabs]; exact hTpos
      have hraw := RiemannHypothesis.norm_balazard_horizontal_integral_le
        hRH hx hb2 hy hyne hd hd_lt hline hs_top hZ.le hrecip
      have hheight_rpow : (2 + |s.im + y|) ^ q ≤ (3 * T) ^ q :=
        Real.rpow_le_rpow (by positivity) hheight hq.le
      have hbalance := balazard_horizontal_power_balance
        hx hH hδ_top hq.le hqδ hqsubη rfl
      calc
        ‖∫ u : ℝ in b..2,
            balazardContourIntegrand s x (u + y * Complex.I)‖ ≤
            (Z * (2 + |s.im + y|) ^ q * x ^ (2 : ℝ) / |y|) * |2 - b| := hraw
        _ ≤ (Z * (3 * T) ^ q * x ^ (2 : ℝ) / T) * 3 := by
          rw [hyabs]
          gcongr
        _ = (3 * Z) * (x ^ (2 : ℝ) / T * (3 * T) ^ q) := by ring
        _ ≤ (3 * Z) * (3 ^ q * x ^ (-δ / 3) * H ^ η) := by gcongr
        _ = Hc * (x ^ (-δ / 3) * H ^ η) := by dsimp only [Hc]; ring
    have hbottom := hhorizontal (-T) (by rw [abs_neg, abs_of_pos hTpos])
      hminus_ne hheight_minus
    have htop := hhorizontal T (abs_of_pos hTpos) hplus_ne hheight_plus
    have hbottom' :
        ‖∫ u : ℝ in b..2,
            balazardContourIntegrand s x (u + (-T : ℂ) * Complex.I)‖ ≤
          Hc * (x ^ (-δ / 3) * H ^ η) := by
      simpa using hbottom
    have hcontour_raw :=
      RiemannHypothesis.norm_mobiusTruncatedPerronIntegral_sub_analyticReciprocal_le
        hRH (N := N) hs_half_strict hb hTpos hleft
    have hcontour :
        ‖mobiusTruncatedPerronIntegral N T s - analyticReciprocalRiemannZeta s‖ ≤
          Rc * (x ^ (-δ / 3) * H ^ η) := by
      calc
        ‖mobiusTruncatedPerronIntegral N T s - analyticReciprocalRiemannZeta s‖ ≤
            (2 * Real.pi)⁻¹ *
              (‖∫ v : ℝ in -T..T,
                  balazardContourIntegrand s ((N : ℝ) + 1 / 2)
                    (b + v * Complex.I)‖ +
                ‖∫ u : ℝ in b..2,
                  balazardContourIntegrand s ((N : ℝ) + 1 / 2)
                    (u + (-T) * Complex.I)‖ +
                ‖∫ u : ℝ in b..2,
                  balazardContourIntegrand s ((N : ℝ) + 1 / 2)
                    (u + T * Complex.I)‖) := hcontour_raw
        _ ≤ (2 * Real.pi)⁻¹ *
              (Lc * (x ^ (-δ / 3) * H ^ η) +
                Hc * (x ^ (-δ / 3) * H ^ η) +
                Hc * (x ^ (-δ / 3) * H ^ η)) := by
          have hxN : (N : ℝ) + 1 / 2 = x := by rfl
          rw [hxN]
          exact mul_le_mul_of_nonneg_left
            (add_le_add (add_le_add hleft_bound hbottom') htop) (by positivity)
        _ = Rc * (x ^ (-δ / 3) * H ^ η) := by dsimp only [Rc]; ring
    have hperron_raw := hperron N T s hN hT hs_half hs_top
    have htrunc_balance := balazard_truncation_power_balance
      (δ := δ) (η := η) hn (show x = n + 1 / 2 by rfl) hH hδ hδ_top hη rfl
    have hperron_bound :
        ‖mobiusDirichletPartialSum N s - mobiusTruncatedPerronIntegral N T s‖ ≤
          (4 * P) * ((N : ℝ) ^ (-δ / 3) * H ^ η) := by
      calc
        ‖mobiusDirichletPartialSum N s - mobiusTruncatedPerronIntegral N T s‖ ≤
            P * ((N : ℝ) + 1) ^ 2 / T := hperron_raw
        _ ≤ P * (4 * n ^ (-δ / 3) * H ^ η) := by
          rw [mul_div_assoc]
          exact mul_le_mul_of_nonneg_left htrunc_balance hP.le
        _ = (4 * P) * ((N : ℝ) ^ (-δ / 3) * H ^ η) := by
          dsimp only [n]
          ring
    have hxn : (N : ℝ) ≤ x := by dsimp only [x, n]; linarith
    have hnpos : 0 < (N : ℝ) := by positivity
    have hnegative : -δ / 3 ≤ 0 := by linarith
    have hx_to_n : x ^ (-δ / 3) ≤ (N : ℝ) ^ (-δ / 3) :=
      Real.rpow_le_rpow_of_nonpos hnpos hxn hnegative
    have hcontour_bound :
        ‖mobiusTruncatedPerronIntegral N T s - analyticReciprocalRiemannZeta s‖ ≤
          Rc * ((N : ℝ) ^ (-δ / 3) * H ^ η) := by
      calc
        ‖mobiusTruncatedPerronIntegral N T s - analyticReciprocalRiemannZeta s‖ ≤
            Rc * (x ^ (-δ / 3) * H ^ η) := hcontour
        _ ≤ Rc * ((N : ℝ) ^ (-δ / 3) * H ^ η) := by gcongr
    have hnbase_nonneg : 0 ≤ (N : ℝ) ^ (-δ / 3) * H ^ η := by positivity
    calc
      ‖mobiusDirichletPartialSum N s - analyticReciprocalRiemannZeta s‖ ≤
          ‖mobiusDirichletPartialSum N s - mobiusTruncatedPerronIntegral N T s‖ +
            ‖mobiusTruncatedPerronIntegral N T s - analyticReciprocalRiemannZeta s‖ := by
        rw [show mobiusDirichletPartialSum N s - analyticReciprocalRiemannZeta s =
          (mobiusDirichletPartialSum N s - mobiusTruncatedPerronIntegral N T s) +
            (mobiusTruncatedPerronIntegral N T s - analyticReciprocalRiemannZeta s) by ring]
        exact norm_add_le _ _
      _ ≤ (4 * P) * ((N : ℝ) ^ (-δ / 3) * H ^ η) +
          Rc * ((N : ℝ) ^ (-δ / 3) * H ^ η) := add_le_add hperron_bound hcontour_bound
      _ = (4 * P + Rc) * ((N : ℝ) ^ (-δ / 3) * H ^ η) := by ring
      _ ≤ C * ((N : ℝ) ^ (-δ / 3) * H ^ η) := by
        apply mul_le_mul_of_nonneg_right _ hnbase_nonneg
        dsimp only [C]
        linarith
      _ = C * (N : ℝ) ^ (-δ / 3) * H ^ η := by ring
      _ = C * (N : ℝ) ^ (-δ / 3) * (1 + |s.im|) ^ η := rfl
  · refine ⟨1, by norm_num, ?_⟩
    intro N s _ hs_lower hs_top
    exfalso
    have : δ ≤ 1 / 2 := by linarith
    exact hδ_top this

/-- The Burnol transformed-error majorant with the Balazard--Saias premise discharged by the
compiled RH-specialized contour argument. -/
theorem RiemannHypothesis.exists_norm_burnolMobiusTransformedError_le_compiled
    (hRH : RiemannHypothesis) {δ η : ℝ}
    (hδ : 0 < δ) (hδ_top : δ ≤ 1 / 2) (hη : 0 < η) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (t : ℝ), 2 ≤ N →
      ‖burnolMobiusTransformedError δ N t‖ ≤
        K * (N : ℝ) ^ (-δ / 3) *
          ‖baezDuarteVerticalMajorant (3 / 8 + η) t‖ := by
  obtain ⟨A, hA, hquot⟩ := exists_norm_riemannZeta_div_criticalLine_le_rpow
  obtain ⟨B, hB, hmobius⟩ :=
    RiemannHypothesis.exists_balazardSaias_specialized_bound_compiled hRH hδ hη
  refine ⟨A * B, mul_pos hA hB, ?_⟩
  intro N t hN
  let s : ℂ := (1 / 2 : ℂ) + t * Complex.I
  let z : ℂ := s + δ
  let x : ℝ := 1 + |t|
  have hx : 0 < x := by dsimp only [x]; positivity
  have hz_re : z.re = (1 / 2 : ℝ) + δ := by simp [z, s]
  have hz_im : z.im = t := by simp [z, s]
  have hmobius' :
      ‖mobiusDirichletPartialSum N z - analyticReciprocalRiemannZeta z‖ ≤
        B * (N : ℝ) ^ (-δ / 3) * x ^ η := by
    have h := hmobius N z hN (by rw [hz_re]) (by rw [hz_re]; linarith)
    simpa only [hz_im, x] using h
  have hquot' : ‖riemannZeta s / s‖ ≤ A * x ^ (-5 / 8 : ℝ) := by
    simpa only [s, x] using hquot t
  change ‖riemannZeta s / s *
    (mobiusDirichletPartialSum N z - analyticReciprocalRiemannZeta z)‖ ≤ _
  rw [norm_mul]
  calc
    ‖riemannZeta s / s‖ *
        ‖mobiusDirichletPartialSum N z - analyticReciprocalRiemannZeta z‖ ≤
        (A * x ^ (-5 / 8 : ℝ)) *
          (B * (N : ℝ) ^ (-δ / 3) * x ^ η) := by gcongr
    _ = (A * B) * (N : ℝ) ^ (-δ / 3) *
        (x ^ (-5 / 8 : ℝ) * x ^ η) := by ring
    _ = (A * B) * (N : ℝ) ^ (-δ / 3) * x ^ (-5 / 8 + η : ℝ) := by
      rw [← Real.rpow_add hx]
    _ = (A * B) * (N : ℝ) ^ (-δ / 3) *
        ‖baezDuarteVerticalMajorant (3 / 8 + η) t‖ := by
      rw [norm_baezDuarteVerticalMajorant_three_eighths_add]











end LeanLab.Riemann
