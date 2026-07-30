import LeanLab.Riemann.ClassicalZeroDetectorContourShift
import LeanLab.Riemann.LevinsonMontgomeryLeftHalfPlaneWinding
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.Liouville
import Mathlib.NumberTheory.LSeries.Deriv

set_option linter.style.header false

/-!
# Jensen zero counts on the Levinson--Montgomery top edge

This file reconstructs the analytic real-part symmetrizations behind the Jensen step in
Levinson--Montgomery's proof. The derivative is rotated so that its first nonzero Dirichlet
coefficient has a fixed phase.
-/

namespace LeanLab.Riemann

open Complex Filter Function Metric Set
open scoped LSeries.notation Topology

noncomputable section

/-- The fixed center of the source-shaped Jensen discs. -/
def levinsonMontgomeryJensenCenter : ℂ := 20

/-- The inner Jensen radius; its real diameter contains the complete source segment `[0,1]`. -/
def levinsonMontgomeryJensenInnerRadius : ℝ := 20

/-- The outer Jensen radius used for the circle growth estimate. -/
def levinsonMontgomeryJensenOuterRadius : ℝ := 21

/-- Analytic symmetrization whose restriction to the real axis is the real part of
`zeta(x+i*t)`. -/
def levinsonMontgomeryZetaTopSymm (t : ℝ) (z : ℂ) : ℂ :=
  (riemannZeta (z + t * I) + riemannZeta (z - t * I)) / 2

/-- The phase which makes the `n=2` term of `zeta'(z+i*t)` independent of `t`. -/
def levinsonMontgomeryDerivPhase (t : ℝ) : ℂ :=
  Complex.exp ((t * Real.log 2 : ℂ) * I)

@[simp]
theorem norm_levinsonMontgomeryDerivPhase (t : ℝ) :
    ‖levinsonMontgomeryDerivPhase t‖ = 1 := by
  change ‖Complex.exp (((t : ℂ) * (Real.log 2 : ℂ)) * I)‖ = 1
  have hcast :
      (t : ℂ) * (Real.log 2 : ℂ) =
        ((t * Real.log 2 : ℝ) : ℂ) :=
    (Complex.ofReal_mul t (Real.log 2)).symm
  rw [hcast, Complex.norm_exp]
  have hre :
      ((((t * Real.log 2 : ℝ) : ℂ) * I).re) = 0 := by
    simp only [mul_re, ofReal_re, I_re, ofReal_im, I_im,
      mul_zero, zero_mul, sub_zero]
  rw [hre, Real.exp_zero]

/-- The phase-normalized analytic symmetrization for the real part of `zeta'`. -/
def levinsonMontgomeryZetaDerivTopSymm (t : ℝ) (z : ℂ) : ℂ :=
  (levinsonMontgomeryDerivPhase t * deriv riemannZeta (z + t * I) +
      (starRingEnd ℂ) (levinsonMontgomeryDerivPhase t) *
        deriv riemannZeta (z - t * I)) / 2

private theorem riemannZeta_conj_conj :
    ((starRingEnd ℂ) ∘ riemannZeta ∘ (starRingEnd ℂ)) =
      riemannZeta := by
  funext z
  change (starRingEnd ℂ) (riemannZeta ((starRingEnd ℂ) z)) =
    riemannZeta z
  rw [riemannZeta_conj]
  simp

theorem deriv_riemannZeta_conj (s : ℂ) :
    deriv riemannZeta ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (deriv riemannZeta s) := by
  have h :=
    congrFun
      (deriv_conj_conj_eq_self riemannZeta riemannZeta_conj_conj)
      ((starRingEnd ℂ) s)
  simpa [Function.comp_def] using h.symm

private theorem star_real_add_mul_I (x t : ℝ) :
    (starRingEnd ℂ) ((x : ℂ) + t * I) =
      (x : ℂ) - t * I := by
  apply Complex.ext <;> simp

theorem levinsonMontgomeryZetaTopSymm_real
    (t x : ℝ) :
    levinsonMontgomeryZetaTopSymm t x =
      ((riemannZeta (x + t * I)).re : ℂ) := by
  have hminus :
      riemannZeta ((x : ℂ) - t * I) =
        (starRingEnd ℂ) (riemannZeta (x + t * I)) := by
    rw [← star_real_add_mul_I x t, riemannZeta_conj]
  rw [levinsonMontgomeryZetaTopSymm, hminus]
  exact (Complex.re_eq_add_conj _).symm

theorem levinsonMontgomeryZetaDerivTopSymm_real
    (t x : ℝ) :
    levinsonMontgomeryZetaDerivTopSymm t x =
      (((levinsonMontgomeryDerivPhase t *
        deriv riemannZeta (x + t * I)).re : ℝ) : ℂ) := by
  have hminus :
      deriv riemannZeta ((x : ℂ) - t * I) =
        (starRingEnd ℂ) (deriv riemannZeta (x + t * I)) := by
    rw [← star_real_add_mul_I x t, deriv_riemannZeta_conj]
  rw [levinsonMontgomeryZetaDerivTopSymm, hminus]
  rw [← map_mul]
  exact (Complex.re_eq_add_conj _).symm

theorem real_segment_mem_levinsonMontgomeryJensenInnerBall
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (x : ℂ) ∈
      closedBall levinsonMontgomeryJensenCenter
        levinsonMontgomeryJensenInnerRadius := by
  change dist (x : ℂ) (20 : ℂ) ≤ 20
  rw [dist_eq_norm]
  have hcast :
      (x : ℂ) - (20 : ℂ) = ((x - 20 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcast, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonpos]
  · linarith [hx.1, hx.2]
  · linarith [hx.2]

private theorem abs_im_le_outerRadius_of_mem
    {z : ℂ}
    (hz : z ∈
      closedBall levinsonMontgomeryJensenCenter
        levinsonMontgomeryJensenOuterRadius) :
    |z.im| ≤ levinsonMontgomeryJensenOuterRadius := by
  have him :
      |(z - levinsonMontgomeryJensenCenter).im| ≤
        ‖z - levinsonMontgomeryJensenCenter‖ :=
    Complex.abs_im_le_norm _
  have hdist :
      ‖z - levinsonMontgomeryJensenCenter‖ ≤
        levinsonMontgomeryJensenOuterRadius := by
    simpa only [mem_closedBall, dist_eq_norm] using hz
  simpa [levinsonMontgomeryJensenCenter] using him.trans hdist

private theorem z_add_height_ne_one
    {t : ℝ} (ht : 22 ≤ |t|)
    {z : ℂ}
    (hz : z ∈
      closedBall levinsonMontgomeryJensenCenter
        levinsonMontgomeryJensenOuterRadius) :
    z + t * I ≠ 1 := by
  intro h
  have him := congrArg Complex.im h
  have hzIm : z.im = -t := by
    simp only [add_im, mul_im, ofReal_re, I_im, ofReal_im, I_re,
      mul_zero, mul_one, add_zero, one_im] at him
    linarith
  have hbound := abs_im_le_outerRadius_of_mem hz
  rw [hzIm, abs_neg] at hbound
  norm_num [levinsonMontgomeryJensenOuterRadius] at hbound
  linarith

private theorem z_sub_height_ne_one
    {t : ℝ} (ht : 22 ≤ |t|)
    {z : ℂ}
    (hz : z ∈
      closedBall levinsonMontgomeryJensenCenter
        levinsonMontgomeryJensenOuterRadius) :
    z - t * I ≠ 1 := by
  intro h
  have him := congrArg Complex.im h
  have hzIm : z.im = t := by
    simp only [sub_im, mul_im, ofReal_re, I_im, ofReal_im, I_re,
      mul_zero, mul_one, one_im] at him
    linarith
  have hbound := abs_im_le_outerRadius_of_mem hz
  rw [hzIm] at hbound
  norm_num [levinsonMontgomeryJensenOuterRadius] at hbound
  linarith

theorem analyticOnNhd_levinsonMontgomeryZetaTopSymm
    {t : ℝ} (ht : 22 ≤ |t|) :
    AnalyticOnNhd ℂ (levinsonMontgomeryZetaTopSymm t)
      (closedBall levinsonMontgomeryJensenCenter
        levinsonMontgomeryJensenOuterRadius) := by
  intro z hz
  have hplus : z + t * I ≠ 1 :=
    z_add_height_ne_one ht hz
  have hminus : z - t * I ≠ 1 :=
    z_sub_height_ne_one ht hz
  have hinnerPlus :
      AnalyticAt ℂ (fun w : ℂ => w + t * I) z :=
    analyticAt_id.add analyticAt_const
  have hinnerMinus :
      AnalyticAt ℂ (fun w : ℂ => w - t * I) z :=
    analyticAt_id.sub analyticAt_const
  have haPlus :
      AnalyticAt ℂ (fun w : ℂ => riemannZeta (w + t * I)) z := by
    have hout : AnalyticAt ℂ riemannZeta (z + t * I) :=
      analyticOn_riemannZeta (z + t * I) (by simpa using hplus)
    have hcomp :=
      hout.comp (f := fun w : ℂ => w + t * I) hinnerPlus
    exact hcomp.congr (Eventually.of_forall fun _ => rfl)
  have haMinus :
      AnalyticAt ℂ (fun w : ℂ => riemannZeta (w - t * I)) z := by
    have hout : AnalyticAt ℂ riemannZeta (z - t * I) :=
      analyticOn_riemannZeta (z - t * I) (by simpa using hminus)
    have hcomp :=
      hout.comp (f := fun w : ℂ => w - t * I) hinnerMinus
    exact hcomp.congr (Eventually.of_forall fun _ => rfl)
  have hsum :
      AnalyticAt ℂ
        (fun w : ℂ =>
          (riemannZeta (w + t * I) +
            riemannZeta (w - t * I)) / 2) z :=
    (haPlus.add haMinus).div_const
  exact hsum.congr (Eventually.of_forall fun _ => rfl)

theorem analyticOnNhd_levinsonMontgomeryZetaDerivTopSymm
    {t : ℝ} (ht : 22 ≤ |t|) :
    AnalyticOnNhd ℂ (levinsonMontgomeryZetaDerivTopSymm t)
      (closedBall levinsonMontgomeryJensenCenter
        levinsonMontgomeryJensenOuterRadius) := by
  intro z hz
  have hplus : z + t * I ≠ 1 :=
    z_add_height_ne_one ht hz
  have hminus : z - t * I ≠ 1 :=
    z_sub_height_ne_one ht hz
  have hinnerPlus :
      AnalyticAt ℂ (fun w : ℂ => w + t * I) z :=
    analyticAt_id.add analyticAt_const
  have hinnerMinus :
      AnalyticAt ℂ (fun w : ℂ => w - t * I) z :=
    analyticAt_id.sub analyticAt_const
  have haPlus :
      AnalyticAt ℂ (fun w : ℂ => deriv riemannZeta (w + t * I)) z := by
    have hout :
        AnalyticAt ℂ (deriv riemannZeta) (z + t * I) :=
      analyticOnNhd_deriv_riemannZeta (z + t * I)
        (by simpa using hplus)
    have hcomp :=
      hout.comp (f := fun w : ℂ => w + t * I) hinnerPlus
    exact hcomp.congr (Eventually.of_forall fun _ => rfl)
  have haMinus :
      AnalyticAt ℂ (fun w : ℂ => deriv riemannZeta (w - t * I)) z := by
    have hout :
        AnalyticAt ℂ (deriv riemannZeta) (z - t * I) :=
      analyticOnNhd_deriv_riemannZeta (z - t * I)
        (by simpa using hminus)
    have hcomp :=
      hout.comp (f := fun w : ℂ => w - t * I) hinnerMinus
    exact hcomp.congr (Eventually.of_forall fun _ => rfl)
  have hsum :
      AnalyticAt ℂ
        (fun w : ℂ =>
          (levinsonMontgomeryDerivPhase t *
              deriv riemannZeta (w + t * I) +
            (starRingEnd ℂ) (levinsonMontgomeryDerivPhase t) *
              deriv riemannZeta (w - t * I)) / 2) z :=
    ((analyticAt_const.mul haPlus).add
      (analyticAt_const.mul haMinus)).div_const
  exact hsum.congr (Eventually.of_forall fun _ => rfl)

/-- Uniform polynomial growth of the Gamma-cosine factor in the bounded positive strip
needed after applying the zeta functional equation. -/
theorem exists_norm_Gamma_mul_cos_levinsonMontgomeryStrip_le :
    ∃ p : ℝ, 0 < p ∧
      ∀ w : ℂ, 1 / 2 ≤ w.re → w.re ≤ 3 →
        ‖Complex.Gamma w *
            Complex.cos ((Real.pi : ℂ) * w / 2)‖ ≤
          3 * (|w.im| + 2) ^ p := by
  obtain ⟨C, hC, hratio⟩ :=
    exists_norm_Gamma_div_le_rpow_of_re_mem_Icc
      (1 / 2 : ℝ) 3 (by norm_num)
  let p : ℝ := C * (5 / 2)
  refine ⟨p, by dsimp only [p]; positivity, ?_⟩
  intro w hwLower hwUpper
  let z0 : ℂ := ((1 / 2 : ℝ) : ℂ) + w.im * I
  let delta : ℝ := w.re - 1 / 2
  have hdelta : 0 ≤ delta := by
    dsimp only [delta]
    linarith
  have hdeltaUpper : delta ≤ 5 / 2 := by
    dsimp only [delta]
    linarith
  have hwEq : w = z0 + delta := by
    apply Complex.ext
    · simp [z0, delta]
    · simp [z0]
  have hratioBound :
      ‖Complex.Gamma (z0 + delta) / Complex.Gamma z0‖ ≤
        (|w.im| + 2) ^ p := by
    have hsource := hratio z0 delta (by simp [z0])
      (by simpa [z0, delta] using hwUpper) hdelta
    have hbase : 1 ≤ |w.im| + 2 := by linarith [abs_nonneg w.im]
    calc
      ‖Complex.Gamma (z0 + delta) / Complex.Gamma z0‖
          ≤ (|z0.im| + 2) ^ (C * delta) := hsource
      _ = (|w.im| + 2) ^ (C * delta) := by simp [z0]
      _ ≤ (|w.im| + 2) ^ p := by
        apply Real.rpow_le_rpow_of_exponent_le hbase
        dsimp only [p]
        nlinarith
  have hz0Gamma : Complex.Gamma z0 ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    simp [z0]
  have hgamma :
      ‖Complex.Gamma w‖ ≤
        (|w.im| + 2) ^ p *
          (3 * Real.exp (-(Real.pi / 2) * |w.im|)) := by
    calc
      ‖Complex.Gamma w‖ =
          ‖(Complex.Gamma (z0 + delta) / Complex.Gamma z0) *
            Complex.Gamma z0‖ := by
        rw [hwEq, div_mul_cancel₀ _ hz0Gamma]
      _ = ‖Complex.Gamma (z0 + delta) / Complex.Gamma z0‖ *
          ‖Complex.Gamma z0‖ := norm_mul _ _
      _ ≤ (|w.im| + 2) ^ p * ‖Complex.Gamma z0‖ :=
        mul_le_mul_of_nonneg_right hratioBound (norm_nonneg _)
      _ ≤ (|w.im| + 2) ^ p *
          (3 * Real.exp (-(Real.pi / 2) * |w.im|)) := by
        gcongr
        simpa [z0] using norm_Gamma_half_add_mul_I_le_exp_pi w.im
  have hcos :
      ‖Complex.cos ((Real.pi : ℂ) * w / 2)‖ ≤
        Real.exp ((Real.pi / 2) * |w.im|) := by
    have harg :
        (Real.pi : ℂ) * w / 2 =
          ((Real.pi / 2 : ℝ) : ℂ) * w := by
      push_cast
      ring
    refine (norm_complex_cos_le_exp_abs_im _).trans_eq ?_
    congr 1
    rw [harg]
    simp only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.pi / 2)]
  rw [norm_mul]
  calc
    ‖Complex.Gamma w‖ *
          ‖Complex.cos ((Real.pi : ℂ) * w / 2)‖
        ≤ ((|w.im| + 2) ^ p *
            (3 * Real.exp (-(Real.pi / 2) * |w.im|))) *
          Real.exp ((Real.pi / 2) * |w.im|) := by
      gcongr
    _ = 3 * (|w.im| + 2) ^ p *
          (Real.exp (-(Real.pi / 2) * |w.im|) *
            Real.exp ((Real.pi / 2) * |w.im|)) := by ring
    _ = 3 * (|w.im| + 2) ^ p := by
      rw [← Real.exp_add]
      ring_nf
      simp

/-- The actual zeta function has polynomial growth on the complete fixed strip needed for
the Jensen circles and the later Cauchy derivative estimate. -/
theorem exists_norm_riemannZeta_levinsonMontgomeryStrip_le :
    ∃ p : ℝ, 0 < p ∧
      ∀ s : ℂ, -2 ≤ s.re → s.re ≤ 42 → 1 ≤ |s.im| →
        ‖riemannZeta s‖ ≤
          120 * (|s.im| + 2) ^ (p + 1) := by
  obtain ⟨p, hp, hgammaCos⟩ :=
    exists_norm_Gamma_mul_cos_levinsonMontgomeryStrip_le
  refine ⟨p, hp, ?_⟩
  intro s hsLower hsUpper hsIm
  let x : ℝ := |s.im| + 2
  have hxOne : 1 ≤ x := by
    dsimp only [x]
    linarith [abs_nonneg s.im]
  have hxPos : 0 < x := zero_lt_one.trans_le hxOne
  by_cases hsHalf : 1 / 2 ≤ s.re
  · by_cases hsEight : s.re ≤ 8
    · have hzeta :=
        norm_riemannZeta_le_linear_of_re_mem_Icc
          (show s.re ∈ Set.Icc (1 / 2 : ℝ) 8 from
            ⟨hsHalf, hsEight⟩) hsIm
      have hxPow : x ≤ x ^ (p + 1) := by
        calc
          x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
          _ ≤ x ^ (p + 1) :=
            Real.rpow_le_rpow_of_exponent_le hxOne (by linarith)
      calc
        ‖riemannZeta s‖ ≤ 20 * (1 + |s.im|) := hzeta
        _ ≤ 120 * x := by
          dsimp only [x]
          nlinarith [abs_nonneg s.im]
        _ ≤ 120 * x ^ (p + 1) := by gcongr
        _ = 120 * (|s.im| + 2) ^ (p + 1) := rfl
    · have hsThree : 3 ≤ s.re := by linarith
      have hclose :=
        norm_riemannZeta_sub_one_lt_three_fourths_of_three_le_re hsThree
      have hzetaSmall : ‖riemannZeta s‖ < 7 / 4 := by
        calc
          ‖riemannZeta s‖ =
              ‖(riemannZeta s - 1) + 1‖ := by ring_nf
          _ ≤ ‖riemannZeta s - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
          _ < 3 / 4 + 1 := by norm_num; linarith
          _ = 7 / 4 := by norm_num
      have hxPowOne : 1 ≤ x ^ (p + 1) :=
        Real.one_le_rpow hxOne (by linarith)
      calc
        ‖riemannZeta s‖ ≤ 7 / 4 := hzetaSmall.le
        _ ≤ 120 * x ^ (p + 1) := by nlinarith
        _ = 120 * (|s.im| + 2) ^ (p + 1) := rfl
  · have hsLeft : s.re < 1 / 2 := lt_of_not_ge hsHalf
    let w : ℂ := 1 - s
    have hwLower : 1 / 2 ≤ w.re := by
      dsimp only [w]
      simp only [sub_re, one_re]
      linarith
    have hwUpper : w.re ≤ 3 := by
      dsimp only [w]
      simp only [sub_re, one_re]
      linarith
    have hwIm : |w.im| = |s.im| := by
      simp [w]
    have hwImLower : 1 ≤ |w.im| := by simpa [hwIm] using hsIm
    have hwNat : ∀ n : ℕ, w ≠ -n := by
      intro n hn
      have hre := congrArg Complex.re hn
      have hnNonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      simp only [neg_re, natCast_re] at hre
      linarith
    have hwOne : w ≠ 1 := by
      intro hw
      have him := congrArg Complex.im hw
      simp only [w, sub_im, one_im, zero_sub, neg_eq_zero] at him
      rw [him, abs_zero] at hsIm
      norm_num at hsIm
    have hfe :
        riemannZeta s =
          2 * (2 * Real.pi) ^ (-w) * Complex.Gamma w *
            Complex.cos (Real.pi * w / 2) * riemannZeta w := by
      have hsEq : 1 - w = s := by
        dsimp only [w]
        ring
      rw [← hsEq]
      exact riemannZeta_one_sub (s := w) hwNat hwOne
    have hpow :
        ‖(2 * (Real.pi : ℂ)) ^ (-w)‖ ≤ 1 := by
      rw [show (2 : ℂ) * Real.pi = ((2 * Real.pi : ℝ) : ℂ) by
        norm_num]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos
        (mul_pos (by norm_num) Real.pi_pos)]
      apply Real.rpow_le_one_of_one_le_of_nonpos
      · linarith [Real.pi_gt_three]
      · simp only [neg_re]
        linarith
    have hgamma := hgammaCos w hwLower hwUpper
    have hzetaW :
        ‖riemannZeta w‖ ≤ 20 * (1 + |w.im|) := by
      apply norm_riemannZeta_le_linear_of_re_mem_Icc
      · exact ⟨hwLower, hwUpper.trans (by norm_num)⟩
      · exact hwImLower
    rw [hfe]
    calc
      ‖2 * (2 * (Real.pi : ℂ)) ^ (-w) * Complex.Gamma w *
            Complex.cos (Real.pi * w / 2) * riemannZeta w‖
          = 2 * ‖(2 * (Real.pi : ℂ)) ^ (-w)‖ *
              ‖Complex.Gamma w *
                Complex.cos (Real.pi * w / 2)‖ *
              ‖riemannZeta w‖ := by
            norm_num only [norm_mul, norm_ofNat]
            ring
      _ ≤ 2 * 1 * (3 * (|w.im| + 2) ^ p) *
            (20 * (1 + |w.im|)) := by gcongr
      _ ≤ 120 * ((|w.im| + 2) ^ p * (|w.im| + 2)) := by
        nlinarith [abs_nonneg w.im,
          Real.rpow_nonneg (by positivity : 0 ≤ |w.im| + 2) p]
      _ = 120 * (|w.im| + 2) ^ (p + 1) := by
        rw [Real.rpow_add (by positivity : 0 < |w.im| + 2),
          Real.rpow_one]
      _ = 120 * (|s.im| + 2) ^ (p + 1) := by rw [hwIm]

/-- Cauchy's estimate transfers the fixed-strip zeta bound to its actual derivative on the
slightly narrower strip. -/
theorem exists_norm_deriv_riemannZeta_levinsonMontgomeryStrip_le :
    ∃ p : ℝ, 0 < p ∧
      ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 41 → 2 ≤ |s.im| →
        ‖deriv riemannZeta s‖ ≤
          240 * (|s.im| + 3) ^ (p + 1) := by
  obtain ⟨p, hp, hzeta⟩ :=
    exists_norm_riemannZeta_levinsonMontgomeryStrip_le
  refine ⟨p, hp, ?_⟩
  intro s hsLower hsUpper hsIm
  let C : ℝ := 120 * (|s.im| + 3) ^ (p + 1)
  have hbound :
      ∀ u ∈ sphere s (1 / 2 : ℝ), ‖riemannZeta u‖ ≤ C := by
    intro u hu
    have hnorm : ‖u - s‖ = 1 / 2 := by
      simpa only [mem_sphere, dist_eq_norm] using hu
    have hreDisp : |u.re - s.re| ≤ 1 / 2 := by
      calc
        |u.re - s.re| = |(u - s).re| := by simp
        _ ≤ ‖u - s‖ := Complex.abs_re_le_norm _
        _ = 1 / 2 := hnorm
    have himDisp : |u.im - s.im| ≤ 1 / 2 := by
      calc
        |u.im - s.im| = |(u - s).im| := by simp
        _ ≤ ‖u - s‖ := Complex.abs_im_le_norm _
        _ = 1 / 2 := hnorm
    have huLower : -2 ≤ u.re := by
      have hleft := neg_le_of_abs_le hreDisp
      linarith
    have huUpper : u.re ≤ 42 := by
      have hright := le_of_abs_le hreDisp
      linarith
    have huImLower : 1 ≤ |u.im| := by
      have htri : |s.im| ≤ |u.im| + |s.im - u.im| := by
        nth_rewrite 1 [show s.im = u.im + (s.im - u.im) by ring]
        exact abs_add_le _ _
      rw [abs_sub_comm] at htri
      linarith
    have huImUpper : |u.im| + 2 ≤ |s.im| + 3 := by
      have htri : |u.im| ≤ |s.im| + |u.im - s.im| := by
        nth_rewrite 1 [show u.im = s.im + (u.im - s.im) by ring]
        exact abs_add_le _ _
      linarith
    have hsource := hzeta u huLower huUpper huImLower
    have hpow :
        (|u.im| + 2) ^ (p + 1) ≤
          (|s.im| + 3) ^ (p + 1) := by
      apply Real.rpow_le_rpow
      · positivity
      · exact huImUpper
      · linarith
    exact hsource.trans (by
      dsimp only [C]
      gcongr)
  have hdiff :
      DifferentiableOn ℂ riemannZeta
        (closedBall s (1 / 2 : ℝ)) := by
    intro u hu
    have hdist : ‖u - s‖ ≤ 1 / 2 := by
      simpa only [mem_closedBall, dist_eq_norm] using hu
    have himDisp : |u.im - s.im| ≤ 1 / 2 := by
      calc
        |u.im - s.im| = |(u - s).im| := by simp
        _ ≤ ‖u - s‖ := Complex.abs_im_le_norm _
        _ ≤ 1 / 2 := hdist
    have huIm : 0 < |u.im| := by
      have htri : |s.im| ≤ |u.im| + |s.im - u.im| := by
        nth_rewrite 1 [show s.im = u.im + (s.im - u.im) by ring]
        exact abs_add_le _ _
      rw [abs_sub_comm] at htri
      linarith
    apply (differentiableAt_riemannZeta (by
      intro huOne
      have him := congrArg Complex.im huOne
      norm_num at him
      rw [him, abs_zero] at huIm
      exact (lt_irrefl 0) huIm)).differentiableWithinAt
  have hdiffCl :
      DiffContOnCl ℂ riemannZeta (ball s (1 / 2 : ℝ)) :=
    hdiff.diffContOnCl_ball subset_rfl
  have hcauchy :=
    norm_deriv_le_of_forall_mem_sphere_norm_le
      (show (0 : ℝ) < 1 / 2 by norm_num) hdiffCl hbound
  dsimp only [C] at hcauchy ⊢
  norm_num at hcauchy
  linarith

private theorem re_bounds_of_mem_levinsonMontgomeryJensenOuterBall
    {z : ℂ}
    (hz : z ∈
      closedBall levinsonMontgomeryJensenCenter
        levinsonMontgomeryJensenOuterRadius) :
    -1 ≤ z.re ∧ z.re ≤ 41 := by
  have hre :
      |(z - levinsonMontgomeryJensenCenter).re| ≤
        ‖z - levinsonMontgomeryJensenCenter‖ :=
    Complex.abs_re_le_norm _
  have hdist :
      ‖z - levinsonMontgomeryJensenCenter‖ ≤
        levinsonMontgomeryJensenOuterRadius := by
    simpa only [mem_closedBall, dist_eq_norm] using hz
  have hbound : |z.re - 20| ≤ 21 := by
    simpa [levinsonMontgomeryJensenCenter,
      levinsonMontgomeryJensenOuterRadius] using hre.trans hdist
  exact ⟨by
    have := neg_le_of_abs_le hbound
    linarith, by
    have := le_of_abs_le hbound
    linarith⟩

private theorem shifted_height_bounds_of_mem_levinsonMontgomeryJensenOuterBall
    {t : ℝ} (ht : 23 ≤ t)
    {z : ℂ}
    (hz : z ∈
      closedBall levinsonMontgomeryJensenCenter
        levinsonMontgomeryJensenOuterRadius) :
    2 ≤ |(z + t * I).im| ∧
      |(z + t * I).im| + 3 ≤ t + 24 ∧
    2 ≤ |(z - t * I).im| ∧
      |(z - t * I).im| + 3 ≤ t + 24 := by
  have hzIm := abs_im_le_outerRadius_of_mem hz
  norm_num [levinsonMontgomeryJensenOuterRadius] at hzIm
  have hplusLower : t ≤ |z.im + t| + |z.im| := by
    calc
      t = (z.im + t) + (-z.im) := by ring
      _ ≤ |z.im + t| + |-z.im| := le_trans (le_abs_self _) (abs_add_le _ _)
      _ = |z.im + t| + |z.im| := by rw [abs_neg]
  have hplusUpper : |z.im + t| ≤ |z.im| + t := by
    have := abs_add_le z.im t
    simpa [abs_of_nonneg (by linarith : 0 ≤ t)] using this
  have hminusLower : t ≤ |z.im - t| + |z.im| := by
    calc
      t = -(z.im - t) + z.im := by ring
      _ ≤ |-(z.im - t)| + |z.im| :=
        le_trans (le_abs_self _) (abs_add_le _ _)
      _ = |z.im - t| + |z.im| := by rw [abs_neg]
  have hminusUpper : |z.im - t| ≤ |z.im| + t := by
    have := abs_sub z.im t
    simpa [abs_of_nonneg (by linarith : 0 ≤ t)] using this
  simp only [add_im, sub_im, mul_im, ofReal_re, I_im, ofReal_im,
    I_re, mul_zero, mul_one, add_zero] at *
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Polynomial growth of the actual zeta real-part symmetrization on the full outer Jensen
ball. -/
theorem exists_norm_levinsonMontgomeryZetaTopSymm_outer_le :
    ∃ p : ℝ, 0 < p ∧
      ∀ t : ℝ, 23 ≤ t →
        ∀ z ∈
          closedBall levinsonMontgomeryJensenCenter
            levinsonMontgomeryJensenOuterRadius,
          ‖levinsonMontgomeryZetaTopSymm t z‖ ≤
            120 * (t + 24) ^ (p + 1) := by
  obtain ⟨p, hp, hzeta⟩ :=
    exists_norm_riemannZeta_levinsonMontgomeryStrip_le
  refine ⟨p, hp, ?_⟩
  intro t ht z hz
  have hre := re_bounds_of_mem_levinsonMontgomeryJensenOuterBall hz
  have him :=
    shifted_height_bounds_of_mem_levinsonMontgomeryJensenOuterBall ht hz
  have hplus :
      ‖riemannZeta (z + t * I)‖ ≤
        120 * (t + 24) ^ (p + 1) := by
    have hsource := hzeta (z + t * I)
      (by
        simp only [add_re, mul_re, ofReal_re, I_re, ofReal_im, I_im,
          mul_zero, zero_mul, sub_zero, add_zero]
        linarith [hre.1])
      (by
        simp only [add_re, mul_re, ofReal_re, I_re, ofReal_im, I_im,
          mul_zero, zero_mul, sub_zero, add_zero]
        linarith [hre.2])
      (by
        simp only [add_im, mul_im, ofReal_re, I_im, ofReal_im, I_re,
          mul_one, mul_zero, add_zero]
        have himPlus : 2 ≤ |z.im + t| := by
          simpa only [add_im, mul_im, ofReal_re, I_im, ofReal_im,
            I_re, mul_one, mul_zero, add_zero] using him.1
        linarith)
    have hpow :
        (|(z + t * I).im| + 2) ^ (p + 1) ≤
          (t + 24) ^ (p + 1) := by
      apply Real.rpow_le_rpow
      · positivity
      · linarith [him.2.1]
      · linarith
    exact hsource.trans (by gcongr)
  have hminus :
      ‖riemannZeta (z - t * I)‖ ≤
        120 * (t + 24) ^ (p + 1) := by
    have hsource := hzeta (z - t * I)
      (by
        simp only [sub_re, mul_re, ofReal_re, I_re, ofReal_im, I_im,
          mul_zero, zero_mul, sub_zero]
        linarith [hre.1])
      (by
        simp only [sub_re, mul_re, ofReal_re, I_re, ofReal_im, I_im,
          mul_zero, zero_mul, sub_zero]
        linarith [hre.2])
      (by
        simp only [sub_im, mul_im, ofReal_re, I_im, ofReal_im, I_re,
          mul_one, mul_zero]
        have himMinus : 2 ≤ |z.im - t| := by
          simpa only [sub_im, mul_im, ofReal_re, I_im, ofReal_im,
            I_re, mul_one, mul_zero, add_zero] using him.2.2.1
        have hweak : 1 ≤ |z.im - t| := by linarith
        simpa only [add_zero] using hweak)
    have hpow :
        (|(z - t * I).im| + 2) ^ (p + 1) ≤
          (t + 24) ^ (p + 1) := by
      apply Real.rpow_le_rpow
      · positivity
      · linarith [him.2.2.2]
      · linarith
    exact hsource.trans (by gcongr)
  rw [levinsonMontgomeryZetaTopSymm, norm_div]
  norm_num
  calc
    ‖riemannZeta (z + t * I) + riemannZeta (z - t * I)‖ / 2
        ≤ (‖riemannZeta (z + t * I)‖ +
            ‖riemannZeta (z - t * I)‖) / 2 := by
          gcongr
          exact norm_add_le _ _
    _ ≤ 120 * (t + 24) ^ (p + 1) := by linarith

/-- Polynomial growth of the actual phase-normalized zeta-derivative symmetrization on the
full outer Jensen ball. -/
theorem exists_norm_levinsonMontgomeryZetaDerivTopSymm_outer_le :
    ∃ p : ℝ, 0 < p ∧
      ∀ t : ℝ, 23 ≤ t →
        ∀ z ∈
          closedBall levinsonMontgomeryJensenCenter
            levinsonMontgomeryJensenOuterRadius,
          ‖levinsonMontgomeryZetaDerivTopSymm t z‖ ≤
            240 * (t + 24) ^ (p + 1) := by
  obtain ⟨p, hp, hderiv⟩ :=
    exists_norm_deriv_riemannZeta_levinsonMontgomeryStrip_le
  refine ⟨p, hp, ?_⟩
  intro t ht z hz
  have hre := re_bounds_of_mem_levinsonMontgomeryJensenOuterBall hz
  have him :=
    shifted_height_bounds_of_mem_levinsonMontgomeryJensenOuterBall ht hz
  have hplus :
      ‖deriv riemannZeta (z + t * I)‖ ≤
        240 * (t + 24) ^ (p + 1) := by
    have hsource := hderiv (z + t * I)
      (by simpa using hre.1) (by simpa using hre.2) (by simpa using him.1)
    have hpow :
        (|(z + t * I).im| + 3) ^ (p + 1) ≤
          (t + 24) ^ (p + 1) := by
      apply Real.rpow_le_rpow
      · positivity
      · exact him.2.1
      · linarith
    exact hsource.trans (by gcongr)
  have hminus :
      ‖deriv riemannZeta (z - t * I)‖ ≤
        240 * (t + 24) ^ (p + 1) := by
    have hsource := hderiv (z - t * I)
      (by simpa using hre.1) (by simpa using hre.2)
      (by simpa using him.2.2.1)
    have hpow :
        (|(z - t * I).im| + 3) ^ (p + 1) ≤
          (t + 24) ^ (p + 1) := by
      apply Real.rpow_le_rpow
      · positivity
      · exact him.2.2.2
      · linarith
    exact hsource.trans (by gcongr)
  have hphase : ‖levinsonMontgomeryDerivPhase t‖ = 1 :=
    norm_levinsonMontgomeryDerivPhase t
  have hphaseStar :
      ‖(starRingEnd ℂ) (levinsonMontgomeryDerivPhase t)‖ = 1 := by
    rw [RCLike.norm_conj, hphase]
  rw [levinsonMontgomeryZetaDerivTopSymm, norm_div]
  norm_num
  calc
    ‖levinsonMontgomeryDerivPhase t *
          deriv riemannZeta (z + t * I) +
        (starRingEnd ℂ) (levinsonMontgomeryDerivPhase t) *
          deriv riemannZeta (z - t * I)‖ / 2
        ≤ (‖levinsonMontgomeryDerivPhase t‖ *
              ‖deriv riemannZeta (z + t * I)‖ +
            ‖(starRingEnd ℂ) (levinsonMontgomeryDerivPhase t)‖ *
              ‖deriv riemannZeta (z - t * I)‖) / 2 := by
          rw [← norm_mul, ← norm_mul]
          gcongr
          exact norm_add_le _ _
    _ ≤ 240 * (t + 24) ^ (p + 1) := by
      rw [hphase, hphaseStar]
      norm_num
      linarith

/-- The far-right center value of the zeta symmetrization is uniformly separated from zero. -/
theorem one_fourth_le_norm_levinsonMontgomeryZetaTopSymm_center
    (t : ℝ) :
    1 / 4 ≤
      ‖levinsonMontgomeryZetaTopSymm t
        levinsonMontgomeryJensenCenter‖ := by
  let s : ℂ := (20 : ℂ) + t * I
  have hclose :
      ‖riemannZeta s - 1‖ < 3 / 4 :=
    norm_riemannZeta_sub_one_lt_three_fourths_of_three_le_re
      (by norm_num [s])
  have hreError :
      |(riemannZeta s - 1).re| < 3 / 4 :=
    (Complex.abs_re_le_norm _).trans_lt hclose
  have hreLower : 1 / 4 < (riemannZeta s).re := by
    have hneg := neg_lt_of_abs_lt hreError
    simp only [sub_re, one_re] at hneg
    linarith
  change 1 / 4 ≤
    ‖levinsonMontgomeryZetaTopSymm t (((20 : ℝ) : ℂ))‖
  rw [levinsonMontgomeryZetaTopSymm_real]
  rw [Complex.norm_real, Real.norm_eq_abs]
  have hreLower' :
      1 / 4 < (riemannZeta (((20 : ℝ) : ℂ) + t * I)).re := by
    convert hreLower using 1
    norm_num [s]
  rw [abs_of_pos (lt_trans (by norm_num) hreLower')]
  exact hreLower'.le

theorem levinsonMontgomeryZetaTopSymm_center_ne_zero
    (t : ℝ) :
    levinsonMontgomeryZetaTopSymm t
      levinsonMontgomeryJensenCenter ≠ 0 := by
  apply norm_ne_zero_iff.mp
  linarith [one_fourth_le_norm_levinsonMontgomeryZetaTopSymm_center t]

/-- Every source real-part crossing on `[0,1]` is an actual zero of the analytic
symmetrization inside the inner Jensen ball. -/
theorem levinsonMontgomeryZetaTop_crossing_mem_innerBall
    {t x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hzero : (riemannZeta (x + t * I)).re = 0) :
    levinsonMontgomeryZetaTopSymm t x = 0 ∧
      (x : ℂ) ∈
        closedBall levinsonMontgomeryJensenCenter
          levinsonMontgomeryJensenInnerRadius := by
  constructor
  · rw [levinsonMontgomeryZetaTopSymm_real, hzero]
    norm_num
  · exact real_segment_mem_levinsonMontgomeryJensenInnerBall hx

/-- The actual zeta real-part symmetrization has only `O(log t)` zeros, with
multiplicity, in the inner Jensen ball. -/
theorem exists_levinsonMontgomeryZetaTopSymm_sum_divisor_le_log :
    ∃ C T0 : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, T0 ≤ t →
        (((∑ᶠ z, MeromorphicOn.divisor (levinsonMontgomeryZetaTopSymm t)
          (closedBall levinsonMontgomeryJensenCenter
            levinsonMontgomeryJensenInnerRadius) z) : ℤ) : ℝ) ≤
          C * Real.log (t + 2) := by
  obtain ⟨p, hp, houter⟩ :=
    exists_norm_levinsonMontgomeryZetaTopSymm_outer_le
  let d : ℝ := Real.log (21 / 20 : ℝ)
  let C : ℝ := 2 * (p + 2) / d
  refine ⟨C, 23, ?_, ?_⟩
  · have hd : 0 < d := by
      dsimp only [d]
      exact Real.log_pos (by norm_num)
    dsimp only [C]
    positivity
  intro t ht
  let M : ℝ := 120 * (t + 24) ^ (p + 1)
  have htBase : 1 < t + 2 := by linarith
  have htOuterBase : 0 < t + 24 := by linarith
  have hpOne : 0 < p + 1 := by linarith
  have hM : 1 ≤ M := by
    have hpow : 1 ≤ (t + 24) ^ (p + 1) :=
      Real.one_le_rpow (by linarith) hpOne.le
    dsimp only [M]
    nlinarith
  have hanalytic :
      AnalyticOnNhd ℂ (levinsonMontgomeryZetaTopSymm t)
        (closedBall levinsonMontgomeryJensenCenter
          levinsonMontgomeryJensenOuterRadius) :=
    analyticOnNhd_levinsonMontgomeryZetaTopSymm
      (by rw [abs_of_nonneg (by linarith : 0 ≤ t)]; linarith)
  have hanalyticAbs :
      AnalyticOnNhd ℂ (levinsonMontgomeryZetaTopSymm t)
        (closedBall levinsonMontgomeryJensenCenter
          |levinsonMontgomeryJensenOuterRadius|) := by
    simpa only [abs_of_nonneg
      (by norm_num [levinsonMontgomeryJensenOuterRadius] : 0 ≤
        levinsonMontgomeryJensenOuterRadius)] using hanalytic
  have hJensen :
      (((∑ᶠ z, MeromorphicOn.divisor (levinsonMontgomeryZetaTopSymm t)
        (closedBall levinsonMontgomeryJensenCenter
          levinsonMontgomeryJensenInnerRadius) z) : ℤ) : ℝ) ≤
        Real.log
            (M /
              ‖levinsonMontgomeryZetaTopSymm t
                levinsonMontgomeryJensenCenter‖) /
          d := by
    have hsource :=
      hanalyticAbs.sum_divisor_le
        (r := levinsonMontgomeryJensenInnerRadius)
        (R := levinsonMontgomeryJensenOuterRadius)
        (M := M)
        (by norm_num [levinsonMontgomeryJensenInnerRadius])
        (by norm_num [levinsonMontgomeryJensenInnerRadius,
          levinsonMontgomeryJensenOuterRadius])
        hM
        (levinsonMontgomeryZetaTopSymm_center_ne_zero t)
        (fun z hz => houter t ht z
          (sphere_subset_closedBall (by
            simpa only [abs_of_nonneg
              (by norm_num [levinsonMontgomeryJensenOuterRadius] : 0 ≤
                levinsonMontgomeryJensenOuterRadius)] using hz)))
    rw [abs_of_nonneg
      (by norm_num [levinsonMontgomeryJensenInnerRadius] : 0 ≤
        levinsonMontgomeryJensenInnerRadius)] at hsource
    simpa only [levinsonMontgomeryJensenInnerRadius,
      levinsonMontgomeryJensenOuterRadius, d] using hsource
  have hcenter :
      0 < ‖levinsonMontgomeryZetaTopSymm t
        levinsonMontgomeryJensenCenter‖ := by
    have := one_fourth_le_norm_levinsonMontgomeryZetaTopSymm_center t
    linarith
  have hquot :
      M /
          ‖levinsonMontgomeryZetaTopSymm t
            levinsonMontgomeryJensenCenter‖ ≤
        4 * M := by
    rw [div_le_iff₀ hcenter]
    have hcenterLower :=
      one_fourth_le_norm_levinsonMontgomeryZetaTopSymm_center t
    nlinarith [show 0 ≤ M from hM.trans' (by norm_num)]
  have hquotPos :
      0 < M /
        ‖levinsonMontgomeryZetaTopSymm t
          levinsonMontgomeryJensenCenter‖ :=
    div_pos (lt_of_lt_of_le zero_lt_one hM) hcenter
  have hlogQuot :
      Real.log
          (M /
            ‖levinsonMontgomeryZetaTopSymm t
              levinsonMontgomeryJensenCenter‖) ≤
        Real.log (4 * M) :=
    Real.log_le_log hquotPos hquot
  have hshiftSq : t + 24 ≤ (t + 2) ^ 2 := by nlinarith
  have hconstantSq : (480 : ℝ) ≤ (t + 2) ^ 2 := by nlinarith
  have hlogShift :
      Real.log (t + 24) ≤ 2 * Real.log (t + 2) := by
    have hmono := Real.log_le_log htOuterBase hshiftSq
    rw [Real.log_pow] at hmono
    norm_num at hmono
    exact hmono
  have hlogConstant :
      Real.log 480 ≤ 2 * Real.log (t + 2) := by
    have hmono :=
      Real.log_le_log (by norm_num : (0 : ℝ) < 480) hconstantSq
    rw [Real.log_pow] at hmono
    norm_num at hmono
    exact hmono
  have hlogM :
      Real.log (4 * M) ≤
        2 * (p + 2) * Real.log (t + 2) := by
    have hlogBase : 0 < Real.log (t + 2) :=
      Real.log_pos htBase
    calc
      Real.log (4 * M) =
          Real.log 480 + (p + 1) * Real.log (t + 24) := by
        dsimp only [M]
        rw [show 4 * (120 * (t + 24) ^ (p + 1)) =
          480 * (t + 24) ^ (p + 1) by ring]
        rw [Real.log_mul (by norm_num : (480 : ℝ) ≠ 0)
          (Real.rpow_pos_of_pos htOuterBase _).ne',
          Real.log_rpow htOuterBase]
      _ ≤ 2 * Real.log (t + 2) +
          (p + 1) * (2 * Real.log (t + 2)) := by
        gcongr
      _ = 2 * (p + 2) * Real.log (t + 2) := by ring
  have hd : 0 < d := by
    dsimp only [d]
    exact Real.log_pos (by norm_num)
  calc
    (((∑ᶠ z, MeromorphicOn.divisor (levinsonMontgomeryZetaTopSymm t)
        (closedBall levinsonMontgomeryJensenCenter
          levinsonMontgomeryJensenInnerRadius) z) : ℤ) : ℝ)
        ≤ Real.log
            (M /
              ‖levinsonMontgomeryZetaTopSymm t
                levinsonMontgomeryJensenCenter‖) /
          d := hJensen
    _ ≤ (2 * (p + 2) * Real.log (t + 2)) / d := by
      apply div_le_div_of_nonneg_right
      · exact hlogQuot.trans hlogM
      · exact hd.le
    _ = C * Real.log (t + 2) := by
      dsimp only [C]
      field_simp

private def levinsonMontgomeryZetaDerivTail (t : ℝ) : ℂ :=
  ∑' k : ℕ,
    LSeries.term (LSeries.logMul (1 : ℕ → ℂ))
      ((20 : ℂ) + t * I) (k + 3)

private theorem deriv_riemannZeta_twenty_add_mul_I_eq
    (t : ℝ) :
    deriv riemannZeta ((20 : ℂ) + t * I) =
      -(LSeries.term (LSeries.logMul (1 : ℕ → ℂ))
          ((20 : ℂ) + t * I) 2 +
        levinsonMontgomeryZetaDerivTail t) := by
  let s : ℂ := (20 : ℂ) + t * I
  have hsRe : 1 < s.re := by norm_num [s]
  have habscissa :
      LSeries.abscissaOfAbsConv (1 : ℕ → ℂ) < s.re := by
    rw [LSeries.abscissaOfAbsConv_one]
    exact_mod_cast hsRe
  have hsum :
      Summable
        (LSeries.term (LSeries.logMul (1 : ℕ → ℂ)) s) :=
    LSeriesSummable_logMul_of_lt_re habscissa
  have hsplit := hsum.sum_add_tsum_nat_add 3
  have hseries :
      L (LSeries.logMul (1 : ℕ → ℂ)) s =
        LSeries.term (LSeries.logMul (1 : ℕ → ℂ)) s 2 +
          levinsonMontgomeryZetaDerivTail t := by
    rw [show L (LSeries.logMul (1 : ℕ → ℂ)) s =
      ∑' n : ℕ,
        LSeries.term (LSeries.logMul (1 : ℕ → ℂ)) s n by rfl]
    rw [← hsplit]
    unfold levinsonMontgomeryZetaDerivTail
    dsimp only [s]
    congr 1
    norm_num [Finset.sum_range_succ, LSeries.term, LSeries.logMul]
  have hderivEq :
      deriv (L (1 : ℕ → ℂ)) s = deriv riemannZeta s := by
    refine Filter.EventuallyEq.deriv_eq <|
      Filter.eventuallyEq_iff_exists_mem.mpr ?_
    exact ⟨{z : ℂ | 1 < z.re},
      (isOpen_lt continuous_const continuous_re).mem_nhds hsRe,
      fun _ => LSeries_one_eq_riemannZeta⟩
  have hlocal :
      deriv riemannZeta s =
        -(LSeries.term (LSeries.logMul (1 : ℕ → ℂ)) s 2 +
          levinsonMontgomeryZetaDerivTail t) := by
    rw [← hderivEq, LSeries_deriv habscissa, hseries]
  simpa only [s] using hlocal

private theorem levinsonMontgomeryDerivPhase_mul_neg_term_two
    (t : ℝ) :
    levinsonMontgomeryDerivPhase t *
        (-LSeries.term (LSeries.logMul (1 : ℕ → ℂ))
          ((20 : ℂ) + t * I) 2) =
      ((-(Real.log 2) / (2 : ℝ) ^ 20 : ℝ) : ℂ) := by
  have hpowImag :
      (2 : ℂ) ^ ((t : ℂ) * I) =
        levinsonMontgomeryDerivPhase t := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num)]
    rw [levinsonMontgomeryDerivPhase]
    congr 1
    have hlog :
        Complex.log (2 : ℂ) = (Real.log 2 : ℂ) :=
      (Complex.natCast_log (n := 2)).symm
    rw [hlog]
    ring
  have hpow :
      (2 : ℂ) ^ ((20 : ℂ) + t * I) =
        (2 : ℂ) ^ (20 : ℕ) *
          levinsonMontgomeryDerivPhase t := by
    rw [Complex.cpow_add _ _ (by norm_num)]
    have hnat :
        (2 : ℂ) ^ (20 : ℂ) = (2 : ℂ) ^ (20 : ℕ) :=
      Complex.cpow_natCast 2 20
    rw [hnat, hpowImag]
  have hphaseNe : levinsonMontgomeryDerivPhase t ≠ 0 := by
    exact Complex.exp_ne_zero _
  rw [LSeries.term_of_ne_zero (by norm_num)]
  simp only [LSeries.logMul, Pi.one_apply, mul_one]
  have hlog :
      Complex.log ((2 : ℕ) : ℂ) = (Real.log 2 : ℂ) :=
    (Complex.natCast_log (n := 2)).symm
  rw [hlog]
  change levinsonMontgomeryDerivPhase t *
      (-((Real.log 2 : ℂ) /
        (2 : ℂ) ^ ((20 : ℂ) + t * I))) =
    ((-(Real.log 2) / (2 : ℝ) ^ 20 : ℝ) : ℂ)
  rw [hpow]
  field_simp
  push_cast
  ring

private theorem norm_levinsonMontgomeryZetaDerivTail_term_le
    (t : ℝ) (k : ℕ) :
    ‖LSeries.term (LSeries.logMul (1 : ℕ → ℂ))
        ((20 : ℂ) + t * I) (k + 3)‖ ≤
      (1 / (3 : ℝ) ^ 17) *
        (1 / ((k + 1 : ℕ) : ℝ) ^ 2) := by
  let n : ℕ := k + 3
  have hnPos : 0 < n := by omega
  have hnThree : 3 ≤ n := by omega
  have hnRealPos : (0 : ℝ) < n := by exact_mod_cast hnPos
  have hnRealThree : (3 : ℝ) ≤ n := by exact_mod_cast hnThree
  have hlog :
      ‖Complex.log (n : ℂ)‖ ≤ (n : ℝ) := by
    have hsource :=
      Complex.norm_log_natCast_le_rpow_div n
        (show (0 : ℝ) < 1 by norm_num)
    simpa [Real.rpow_one] using hsource
  have hdenom :
      ‖(n : ℂ) ^ ((20 : ℂ) + t * I)‖ =
        (n : ℝ) ^ 20 := by
    rw [Complex.norm_natCast_cpow_of_pos hnPos]
    norm_num
  have hpow17 : (3 : ℝ) ^ 17 ≤ (n : ℝ) ^ 17 :=
    pow_le_pow_left₀ (by norm_num) hnRealThree 17
  have hkOnePos : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  rw [LSeries.term_of_ne_zero (by omega)]
  simp only [LSeries.logMul, Pi.one_apply, mul_one]
  change ‖Complex.log (n : ℂ) /
      (n : ℂ) ^ ((20 : ℂ) + t * I)‖ ≤ _
  rw [norm_div, hdenom]
  calc
    ‖Complex.log (n : ℂ)‖ / (n : ℝ) ^ 20
        ≤ (n : ℝ) / (n : ℝ) ^ 20 := by
          gcongr
    _ = 1 / (n : ℝ) ^ 19 := by
      field_simp
    _ = (1 / (n : ℝ) ^ 17) *
          (1 / (n : ℝ) ^ 2) := by
      field_simp
    _ ≤ (1 / (3 : ℝ) ^ 17) *
          (1 / (n : ℝ) ^ 2) := by
      gcongr
    _ ≤ (1 / (3 : ℝ) ^ 17) *
          (1 / ((k + 1 : ℕ) : ℝ) ^ 2) := by
      gcongr
      dsimp only [n]
      norm_num

private theorem norm_levinsonMontgomeryZetaDerivTail_le
    (t : ℝ) :
    ‖levinsonMontgomeryZetaDerivTail t‖ ≤
      2 / (3 : ℝ) ^ 17 := by
  let s : ℂ := (20 : ℂ) + t * I
  let major : ℕ → ℝ := fun k =>
    (1 / (3 : ℝ) ^ 17) *
      (1 / ((k + 1 : ℕ) : ℝ) ^ 2)
  have hsRe : 1 < s.re := by norm_num [s]
  have habscissa :
      LSeries.abscissaOfAbsConv (1 : ℕ → ℂ) < s.re := by
    rw [LSeries.abscissaOfAbsConv_one]
    exact_mod_cast hsRe
  have hsum :
      Summable
        (LSeries.term (LSeries.logMul (1 : ℕ → ℂ)) s) :=
    LSeriesSummable_logMul_of_lt_re habscissa
  have htailSummable :
      Summable (fun k : ℕ =>
        LSeries.term (LSeries.logMul (1 : ℕ → ℂ)) s (k + 3)) :=
    hsum.comp_injective (fun _ _ h => by omega)
  let g : ℕ → ℝ := fun n => 1 / (n : ℝ) ^ 2
  have hgSummable : Summable g :=
    hasSum_zeta_two.summable
  have hshiftSummable :
      Summable (fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ) ^ 2) := by
    simpa only [g] using
      (summable_nat_add_iff 1).mpr hgSummable
  have hmajorSummable : Summable major := by
    exact hshiftSummable.mul_left _
  have hshiftTsum :
      ∑' k : ℕ, 1 / ((k + 1 : ℕ) : ℝ) ^ 2 =
        Real.pi ^ 2 / 6 := by
    have hsplit := hgSummable.sum_add_tsum_nat_add 1
    rw [hasSum_zeta_two.tsum_eq] at hsplit
    norm_num [g] at hsplit ⊢
    exact hsplit
  have hmajorTsum :
      ∑' k : ℕ, major k =
        (1 / (3 : ℝ) ^ 17) * (Real.pi ^ 2 / 6) := by
    simp only [major, tsum_mul_left, hshiftTsum]
  have hpi : Real.pi ^ 2 / 6 ≤ 2 := by
    nlinarith [Real.pi_pos, Real.pi_le_four,
      Real.pi_lt_d2]
  unfold levinsonMontgomeryZetaDerivTail
  calc
    ‖∑' k : ℕ,
        LSeries.term (LSeries.logMul (1 : ℕ → ℂ))
          ((20 : ℂ) + t * I) (k + 3)‖
        ≤ ∑' k : ℕ,
            ‖LSeries.term (LSeries.logMul (1 : ℕ → ℂ))
              ((20 : ℂ) + t * I) (k + 3)‖ :=
      norm_tsum_le_tsum_norm (by simpa only [s] using htailSummable.norm)
    _ ≤ ∑' k : ℕ, major k := by
      apply Summable.tsum_le_tsum
      · intro k
        exact norm_levinsonMontgomeryZetaDerivTail_term_le t k
      · exact (by simpa only [s] using htailSummable.norm)
      · exact hmajorSummable
    _ = (1 / (3 : ℝ) ^ 17) * (Real.pi ^ 2 / 6) :=
      hmajorTsum
    _ ≤ (1 / (3 : ℝ) ^ 17) * 2 := by gcongr
    _ = 2 / (3 : ℝ) ^ 17 := by ring

private theorem levinsonMontgomeryZetaDerivTail_lt_half_main :
    2 / (3 : ℝ) ^ 17 <
      Real.log 2 / (2 * (2 : ℝ) ^ 20) := by
  norm_num
  nlinarith [Real.log_two_gt_d9]

/-- The phase-normalized derivative symmetrization has a uniform nonzero center value because
the rotated `n=2` Dirichlet term dominates the complete tail. -/
theorem log_two_div_two_pow_twenty_one_le_norm_derivTopSymm_center
    (t : ℝ) :
    Real.log 2 / (2 * (2 : ℝ) ^ 20) ≤
      ‖levinsonMontgomeryZetaDerivTopSymm t
        levinsonMontgomeryJensenCenter‖ := by
  let a : ℝ := Real.log 2 / (2 : ℝ) ^ 20
  let b : ℝ := 2 / (3 : ℝ) ^ 17
  let v : ℂ :=
    levinsonMontgomeryDerivPhase t *
      deriv riemannZeta ((20 : ℂ) + t * I)
  have haPos : 0 < a := by
    dsimp only [a]
    positivity
  have hbNonneg : 0 ≤ b := by
    dsimp only [b]
    positivity
  have hba : b < a / 2 := by
    convert levinsonMontgomeryZetaDerivTail_lt_half_main using 1
    dsimp only [a, b]
    ring
  have hv :
      v =
        ((-a : ℝ) : ℂ) -
          levinsonMontgomeryDerivPhase t *
            levinsonMontgomeryZetaDerivTail t := by
    dsimp only [v]
    rw [deriv_riemannZeta_twenty_add_mul_I_eq]
    calc
      levinsonMontgomeryDerivPhase t *
          -(LSeries.term (LSeries.logMul (1 : ℕ → ℂ))
              ((20 : ℂ) + t * I) 2 +
            levinsonMontgomeryZetaDerivTail t) =
          levinsonMontgomeryDerivPhase t *
              (-LSeries.term (LSeries.logMul (1 : ℕ → ℂ))
                ((20 : ℂ) + t * I) 2) -
            levinsonMontgomeryDerivPhase t *
              levinsonMontgomeryZetaDerivTail t := by ring
      _ = ((-a : ℝ) : ℂ) -
            levinsonMontgomeryDerivPhase t *
              levinsonMontgomeryZetaDerivTail t := by
        rw [levinsonMontgomeryDerivPhase_mul_neg_term_two]
        dsimp only [a]
        push_cast
        ring
  have htailNorm :
      ‖levinsonMontgomeryDerivPhase t *
          levinsonMontgomeryZetaDerivTail t‖ ≤ b := by
    rw [norm_mul, norm_levinsonMontgomeryDerivPhase, one_mul]
    exact norm_levinsonMontgomeryZetaDerivTail_le t
  have htailRe :
      |(levinsonMontgomeryDerivPhase t *
          levinsonMontgomeryZetaDerivTail t).re| ≤ b :=
    (Complex.abs_re_le_norm _).trans htailNorm
  have hvUpper : v.re ≤ -a + b := by
    rw [hv]
    simp only [sub_re, ofReal_re]
    have hneg := neg_le_of_abs_le htailRe
    linarith
  have hvNegHalf : v.re ≤ -(a / 2) := by
    have hstrict : -a + b < -(a / 2) := by linarith
    exact hvUpper.trans hstrict.le
  have hvNeg : v.re < 0 := lt_of_le_of_lt hvNegHalf (by
    have : 0 < a / 2 := by positivity
    linarith)
  have hrealNorm : a / 2 ≤ ‖((v.re : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg hvNeg]
    linarith
  have hsymm :
      levinsonMontgomeryZetaDerivTopSymm t (((20 : ℝ) : ℂ)) =
        ((v.re : ℝ) : ℂ) := by
    rw [levinsonMontgomeryZetaDerivTopSymm_real]
    rfl
  have hsymmComplex :
      levinsonMontgomeryZetaDerivTopSymm t (20 : ℂ) =
        ((v.re : ℝ) : ℂ) := by
    convert hsymm using 1
    norm_num
  rw [levinsonMontgomeryJensenCenter]
  rw [hsymmComplex]
  convert hrealNorm using 1
  dsimp only [a]
  ring

theorem levinsonMontgomeryZetaDerivTopSymm_center_ne_zero
    (t : ℝ) :
    levinsonMontgomeryZetaDerivTopSymm t
      levinsonMontgomeryJensenCenter ≠ 0 := by
  apply norm_ne_zero_iff.mp
  have hlower :=
    log_two_div_two_pow_twenty_one_le_norm_derivTopSymm_center t
  have hpositive :
      0 < Real.log 2 / (2 * (2 : ℝ) ^ 20) := by positivity
  linarith

theorem one_div_four_million_le_norm_derivTopSymm_center
    (t : ℝ) :
    1 / 4000000 ≤
      ‖levinsonMontgomeryZetaDerivTopSymm t
        levinsonMontgomeryJensenCenter‖ := by
  have hmain :=
    log_two_div_two_pow_twenty_one_le_norm_derivTopSymm_center t
  have hnumeric :
      (1 / 4000000 : ℝ) ≤
        Real.log 2 / (2 * (2 : ℝ) ^ 20) := by
    norm_num
    nlinarith [Real.log_two_gt_d9]
  exact hnumeric.trans hmain

theorem levinsonMontgomeryZetaDerivTop_crossing_mem_innerBall
    {t x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hzero :
      (levinsonMontgomeryDerivPhase t *
        deriv riemannZeta (x + t * I)).re = 0) :
    levinsonMontgomeryZetaDerivTopSymm t x = 0 ∧
      (x : ℂ) ∈
        closedBall levinsonMontgomeryJensenCenter
          levinsonMontgomeryJensenInnerRadius := by
  constructor
  · rw [levinsonMontgomeryZetaDerivTopSymm_real, hzero]
    norm_num
  · exact real_segment_mem_levinsonMontgomeryJensenInnerBall hx

/-- The actual phase-normalized zeta-derivative real-part symmetrization has only
`O(log t)` zeros, with multiplicity, in the inner Jensen ball. -/
theorem exists_levinsonMontgomeryZetaDerivTopSymm_sum_divisor_le_log :
    ∃ C T0 : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, T0 ≤ t →
        (((∑ᶠ z,
          MeromorphicOn.divisor
            (levinsonMontgomeryZetaDerivTopSymm t)
            (closedBall levinsonMontgomeryJensenCenter
              levinsonMontgomeryJensenInnerRadius) z) : ℤ) : ℝ) ≤
          C * Real.log (t + 2) := by
  obtain ⟨p, hp, houter⟩ :=
    exists_norm_levinsonMontgomeryZetaDerivTopSymm_outer_le
  let d : ℝ := Real.log (21 / 20 : ℝ)
  let C : ℝ := 2 * (p + 2) / d
  refine ⟨C, 40000, ?_, ?_⟩
  · have hd : 0 < d := by
      dsimp only [d]
      exact Real.log_pos (by norm_num)
    dsimp only [C]
    positivity
  intro t ht
  let M : ℝ := 240 * (t + 24) ^ (p + 1)
  have htBase : 1 < t + 2 := by linarith
  have htOuterBase : 0 < t + 24 := by linarith
  have hpOne : 0 < p + 1 := by linarith
  have hM : 1 ≤ M := by
    have hpow : 1 ≤ (t + 24) ^ (p + 1) :=
      Real.one_le_rpow (by linarith) hpOne.le
    dsimp only [M]
    nlinarith
  have hanalytic :
      AnalyticOnNhd ℂ (levinsonMontgomeryZetaDerivTopSymm t)
        (closedBall levinsonMontgomeryJensenCenter
          levinsonMontgomeryJensenOuterRadius) :=
    analyticOnNhd_levinsonMontgomeryZetaDerivTopSymm
      (by rw [abs_of_nonneg (by linarith : 0 ≤ t)]; linarith)
  have hanalyticAbs :
      AnalyticOnNhd ℂ (levinsonMontgomeryZetaDerivTopSymm t)
        (closedBall levinsonMontgomeryJensenCenter
          |levinsonMontgomeryJensenOuterRadius|) := by
    simpa only [abs_of_nonneg
      (by norm_num [levinsonMontgomeryJensenOuterRadius] : 0 ≤
        levinsonMontgomeryJensenOuterRadius)] using hanalytic
  have hJensen :
      (((∑ᶠ z,
        MeromorphicOn.divisor
          (levinsonMontgomeryZetaDerivTopSymm t)
          (closedBall levinsonMontgomeryJensenCenter
            levinsonMontgomeryJensenInnerRadius) z) : ℤ) : ℝ) ≤
        Real.log
            (M /
              ‖levinsonMontgomeryZetaDerivTopSymm t
                levinsonMontgomeryJensenCenter‖) /
          d := by
    have hsource :=
      hanalyticAbs.sum_divisor_le
        (r := levinsonMontgomeryJensenInnerRadius)
        (R := levinsonMontgomeryJensenOuterRadius)
        (M := M)
        (by norm_num [levinsonMontgomeryJensenInnerRadius])
        (by norm_num [levinsonMontgomeryJensenInnerRadius,
          levinsonMontgomeryJensenOuterRadius])
        hM
        (levinsonMontgomeryZetaDerivTopSymm_center_ne_zero t)
        (fun z hz => houter t (by linarith) z
          (sphere_subset_closedBall (by
            simpa only [abs_of_nonneg
              (by norm_num [levinsonMontgomeryJensenOuterRadius] : 0 ≤
                levinsonMontgomeryJensenOuterRadius)] using hz)))
    rw [abs_of_nonneg
      (by norm_num [levinsonMontgomeryJensenInnerRadius] : 0 ≤
        levinsonMontgomeryJensenInnerRadius)] at hsource
    simpa only [levinsonMontgomeryJensenInnerRadius,
      levinsonMontgomeryJensenOuterRadius, d] using hsource
  have hcenter :
      0 < ‖levinsonMontgomeryZetaDerivTopSymm t
        levinsonMontgomeryJensenCenter‖ := by
    exact norm_pos_iff.mpr
      (levinsonMontgomeryZetaDerivTopSymm_center_ne_zero t)
  have hquot :
      M /
          ‖levinsonMontgomeryZetaDerivTopSymm t
            levinsonMontgomeryJensenCenter‖ ≤
        4000000 * M := by
    rw [div_le_iff₀ hcenter]
    have hcenterLower :=
      one_div_four_million_le_norm_derivTopSymm_center t
    have hfactor :
        1 ≤ 4000000 *
          ‖levinsonMontgomeryZetaDerivTopSymm t
            levinsonMontgomeryJensenCenter‖ := by
      nlinarith
    calc
      M ≤ M * (4000000 *
          ‖levinsonMontgomeryZetaDerivTopSymm t
            levinsonMontgomeryJensenCenter‖) :=
        le_mul_of_one_le_right (by linarith : 0 ≤ M) hfactor
      _ = (4000000 * M) *
          ‖levinsonMontgomeryZetaDerivTopSymm t
            levinsonMontgomeryJensenCenter‖ := by ring
  have hquotPos :
      0 < M /
        ‖levinsonMontgomeryZetaDerivTopSymm t
          levinsonMontgomeryJensenCenter‖ :=
    div_pos (lt_of_lt_of_le zero_lt_one hM) hcenter
  have hlogQuot :
      Real.log
          (M /
            ‖levinsonMontgomeryZetaDerivTopSymm t
              levinsonMontgomeryJensenCenter‖) ≤
        Real.log (4000000 * M) :=
    Real.log_le_log hquotPos hquot
  have hshiftSq : t + 24 ≤ (t + 2) ^ 2 := by nlinarith
  have hconstantSq :
      (960000000 : ℝ) ≤ (t + 2) ^ 2 := by nlinarith
  have hlogShift :
      Real.log (t + 24) ≤ 2 * Real.log (t + 2) := by
    have hmono := Real.log_le_log htOuterBase hshiftSq
    rw [Real.log_pow] at hmono
    norm_num at hmono
    exact hmono
  have hlogConstant :
      Real.log 960000000 ≤ 2 * Real.log (t + 2) := by
    have hmono :=
      Real.log_le_log
        (by norm_num : (0 : ℝ) < 960000000) hconstantSq
    rw [Real.log_pow] at hmono
    norm_num at hmono
    exact hmono
  have hlogM :
      Real.log (4000000 * M) ≤
        2 * (p + 2) * Real.log (t + 2) := by
    have hlogBase : 0 < Real.log (t + 2) :=
      Real.log_pos htBase
    calc
      Real.log (4000000 * M) =
          Real.log 960000000 +
            (p + 1) * Real.log (t + 24) := by
        dsimp only [M]
        rw [show 4000000 * (240 * (t + 24) ^ (p + 1)) =
          960000000 * (t + 24) ^ (p + 1) by ring]
        rw [Real.log_mul
          (by norm_num : (960000000 : ℝ) ≠ 0)
          (Real.rpow_pos_of_pos htOuterBase _).ne',
          Real.log_rpow htOuterBase]
      _ ≤ 2 * Real.log (t + 2) +
          (p + 1) * (2 * Real.log (t + 2)) := by
        gcongr
      _ = 2 * (p + 2) * Real.log (t + 2) := by ring
  have hd : 0 < d := by
    dsimp only [d]
    exact Real.log_pos (by norm_num)
  calc
    (((∑ᶠ z,
      MeromorphicOn.divisor
        (levinsonMontgomeryZetaDerivTopSymm t)
        (closedBall levinsonMontgomeryJensenCenter
          levinsonMontgomeryJensenInnerRadius) z) : ℤ) : ℝ)
        ≤ Real.log
            (M /
              ‖levinsonMontgomeryZetaDerivTopSymm t
                levinsonMontgomeryJensenCenter‖) /
          d := hJensen
    _ ≤ (2 * (p + 2) * Real.log (t + 2)) / d := by
      apply div_le_div_of_nonneg_right
      · exact hlogQuot.trans hlogM
      · exact hd.le
    _ = C * Real.log (t + 2) := by
      dsimp only [C]
      field_simp

private theorem zero_mem_inner_divisor_support
    {f : ℂ → ℂ} {c x : ℂ} {r R : ℝ}
    (hrR : r ≤ R)
    (hanalytic : AnalyticOnNhd ℂ f (closedBall c R))
    (hc : f c ≠ 0)
    (hx : x ∈ closedBall c r)
    (hzero : f x = 0) :
    x ∈ Function.support
      (MeromorphicOn.divisor f (closedBall c r)) := by
  have hxOuter : x ∈ closedBall c R := by
    exact mem_closedBall.mpr ((mem_closedBall.mp hx).trans hrR)
  have hR : 0 ≤ R :=
    le_trans dist_nonneg (mem_closedBall.mp hxOuter)
  have hcOuter : c ∈ closedBall c R := by
    exact mem_closedBall_self hR
  have hcenterOrder : analyticOrderAt f c ≠ ⊤ := by
    rw [analyticOrderAt_eq_zero.mpr (Or.inr hc)]
    exact ENat.zero_ne_top
  have hxOrder :
      analyticOrderAt f x ≠ ⊤ :=
    hanalytic.analyticOrderAt_ne_top_of_isPreconnected
      isPreconnected_closedBall hcOuter hxOuter hcenterOrder
  have hxOrderNe :
      analyticOrderAt f x ≠ 0 :=
    (hanalytic x hxOuter).analyticOrderAt_ne_zero.mpr hzero
  rw [Function.mem_support,
    MeromorphicOn.AnalyticOnNhd.divisor_apply
      (hanalytic.mono (closedBall_subset_closedBall hrR)) hx]
  simp [WithTop.untop₀_eq_zero, hxOrder, hxOrderNe]

theorem levinsonMontgomeryZetaTop_crossing_mem_divisorSupport
    {t x : ℝ} (ht : 23 ≤ t)
    (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hzero : (riemannZeta (x + t * I)).re = 0) :
    (x : ℂ) ∈ Function.support
      (MeromorphicOn.divisor (levinsonMontgomeryZetaTopSymm t)
        (closedBall levinsonMontgomeryJensenCenter
          levinsonMontgomeryJensenInnerRadius)) := by
  obtain ⟨hzeroSymm, hxInner⟩ :=
    levinsonMontgomeryZetaTop_crossing_mem_innerBall hx hzero
  apply zero_mem_inner_divisor_support
    (f := levinsonMontgomeryZetaTopSymm t)
    (r := levinsonMontgomeryJensenInnerRadius)
    (R := levinsonMontgomeryJensenOuterRadius)
  · norm_num [levinsonMontgomeryJensenInnerRadius,
      levinsonMontgomeryJensenOuterRadius]
  · exact analyticOnNhd_levinsonMontgomeryZetaTopSymm
      (by rw [abs_of_nonneg (by linarith : 0 ≤ t)]; linarith)
  · exact levinsonMontgomeryZetaTopSymm_center_ne_zero t
  · exact hxInner
  · exact hzeroSymm

theorem levinsonMontgomeryZetaDerivTop_crossing_mem_divisorSupport
    {t x : ℝ} (ht : 23 ≤ t)
    (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hzero :
      (levinsonMontgomeryDerivPhase t *
        deriv riemannZeta (x + t * I)).re = 0) :
    (x : ℂ) ∈ Function.support
      (MeromorphicOn.divisor
        (levinsonMontgomeryZetaDerivTopSymm t)
        (closedBall levinsonMontgomeryJensenCenter
          levinsonMontgomeryJensenInnerRadius)) := by
  obtain ⟨hzeroSymm, hxInner⟩ :=
    levinsonMontgomeryZetaDerivTop_crossing_mem_innerBall hx hzero
  apply zero_mem_inner_divisor_support
    (f := levinsonMontgomeryZetaDerivTopSymm t)
    (r := levinsonMontgomeryJensenInnerRadius)
    (R := levinsonMontgomeryJensenOuterRadius)
  · norm_num [levinsonMontgomeryJensenInnerRadius,
      levinsonMontgomeryJensenOuterRadius]
  · exact analyticOnNhd_levinsonMontgomeryZetaDerivTopSymm
      (by rw [abs_of_nonneg (by linarith : 0 ≤ t)]; linarith)
  · exact levinsonMontgomeryZetaDerivTopSymm_center_ne_zero t
  · exact hxInner
  · exact hzeroSymm

end

end LeanLab.Riemann
