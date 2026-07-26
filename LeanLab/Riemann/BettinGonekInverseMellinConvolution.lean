import LeanLab.Riemann.BettinGonekJContour
import LeanLab.Riemann.ReciprocalZetaSubpower
import LeanLab.Riemann.ZetaConvexity
import LeanLab.Riemann.ZetaConvexityMidpoint

set_option linter.style.header false

/-!
# Bettin--Gonek inverse Mellin convolution

This module reconstructs equations (2.2)--(2.4) of Bettin and Gonek for the actual auxiliary
factor and real-cutoff mollifier already defined in the project.
-/

namespace LeanLab.Riemann

open Complex Filter MeasureTheory Set Topology
open scoped Interval Topology

noncomputable section

/-- Multiplying by three powers of the source denominator removes exactly the vertical
`(1+|Im(w)+t|)⁻³` decay that is propagated across the fixed strip. -/
def bettinGonekAuxiliaryStripLift
    (rho : ℂ) (t : ℝ) (w : ℂ) : ℂ :=
  bettinGonekAuxiliaryG rho t w * (w + t * Complex.I + 1) ^ 3

/-- The holomorphic integrand whose vertical integral is the Bettin--Gonek inverse Mellin
transform. -/
def bettinGonekInverseMellinIntegrand
    (rho : ℂ) (t u : ℝ) (w : ℂ) : ℂ :=
  bettinGonekAuxiliaryG rho t w * (u : ℂ) ^ (-w)

/-- The source-normalized inverse Mellin integral on the vertical line `Re(w) = sigma`.
Mathematical statements below use it only for positive `u`. -/
def bettinGonekInverseMellinLineIntegral
    (rho : ℂ) (t u sigma : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℝ) *
    ∫ y : ℝ, bettinGonekInverseMellinIntegrand rho t u
      (sigma + y * Complex.I)

/-- The source-normalized inverse Mellin kernel on the real-part-three line. -/
def bettinGonekInverseMellinKernel (rho : ℂ) (t u : ℝ) : ℂ :=
  bettinGonekInverseMellinLineIntegral rho t u 3

/-- A finite Dirichlet-series majorant for zeta on the line `Re(s)=3/2`. -/
def bettinGonekZetaThreeHalvesBound : ℝ :=
  ∑' n : ℕ, 1 / |(n : ℝ) + 1| ^ (3 / 2 : ℝ)

theorem bettinGonekZetaThreeHalvesBound_nonneg :
    0 ≤ bettinGonekZetaThreeHalvesBound := by
  unfold bettinGonekZetaThreeHalvesBound
  exact tsum_nonneg fun _ => by positivity

theorem summable_bettinGonekZetaThreeHalvesMajorant :
    Summable (fun n : ℕ => 1 / |(n : ℝ) + 1| ^ (3 / 2 : ℝ)) := by
  exact (Real.summable_one_div_nat_add_rpow 1 (3 / 2)).2 (by norm_num)

theorem norm_riemannZeta_three_halves_sub_mul_I_le (t : ℝ) :
    ‖riemannZeta ((3 / 2 : ℂ) - t * Complex.I)‖ ≤
      bettinGonekZetaThreeHalvesBound := by
  let s : ℂ := (3 / 2 : ℂ) - t * Complex.I
  have hs : 1 < s.re := by
    norm_num [s, Complex.mul_re]
  have hnorm (n : ℕ) :
      ‖1 / ((n : ℂ) + 1) ^ s‖ =
        1 / |(n : ℝ) + 1| ^ (3 / 2 : ℝ) := by
    rw [show (n : ℂ) + 1 = ((n + 1 : ℕ) : ℂ) by push_cast; rfl]
    rw [norm_div, norm_one,
      Complex.norm_natCast_cpow_of_pos (Nat.succ_pos n)]
    simp only [s, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, mul_zero]
    norm_num
    rw [abs_of_pos (by positivity)]
  have hseries :
      Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) := by
    apply summable_bettinGonekZetaThreeHalvesMajorant.of_norm_bounded
    intro n
    exact (hnorm n).le
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  calc
    ‖∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ s‖
        ≤ ∑' n : ℕ, ‖1 / ((n : ℂ) + 1) ^ s‖ :=
      norm_tsum_le_tsum_norm hseries.norm
    _ = bettinGonekZetaThreeHalvesBound := by
      unfold bettinGonekZetaThreeHalvesBound
      apply tsum_congr
      intro n
      exact hnorm n

theorem norm_riemannZeta_le_three_halves_majorant
    {sigma : ℝ} (hsigma : 3 / 2 ≤ sigma) (t : ℝ) :
    ‖riemannZeta ((sigma : ℂ) + t * Complex.I)‖ ≤
      bettinGonekZetaThreeHalvesBound := by
  let s : ℂ := (sigma : ℂ) + t * Complex.I
  have hs : 1 < s.re := by
    norm_num [s, Complex.mul_re]
    linarith
  have hnorm (n : ℕ) :
      ‖1 / ((n : ℂ) + 1) ^ s‖ =
        1 / |(n : ℝ) + 1| ^ sigma := by
    rw [show (n : ℂ) + 1 = ((n + 1 : ℕ) : ℂ) by push_cast; rfl]
    rw [norm_div, norm_one,
      Complex.norm_natCast_cpow_of_pos (Nat.succ_pos n)]
    simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul,
      sub_zero, add_zero]
    norm_num
    rw [abs_of_pos (by positivity)]
  have hterm (n : ℕ) :
      1 / |(n : ℝ) + 1| ^ sigma ≤
        1 / |(n : ℝ) + 1| ^ (3 / 2 : ℝ) := by
    have hbase : 1 ≤ |(n : ℝ) + 1| := by
      rw [abs_of_pos (by positivity)]
      norm_num
    have hpow :
        |(n : ℝ) + 1| ^ (3 / 2 : ℝ) ≤
          |(n : ℝ) + 1| ^ sigma :=
      Real.rpow_le_rpow_of_exponent_le hbase hsigma
    exact one_div_le_one_div_of_le
      (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hbase) _) hpow
  have hseries :
      Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) := by
    apply summable_bettinGonekZetaThreeHalvesMajorant.of_norm_bounded
    intro n
    exact (hnorm n).le.trans (hterm n)
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  calc
    ‖∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ s‖
        ≤ ∑' n : ℕ, ‖1 / ((n : ℂ) + 1) ^ s‖ :=
      norm_tsum_le_tsum_norm hseries.norm
    _ ≤ ∑' n : ℕ, 1 / |(n : ℝ) + 1| ^ (3 / 2 : ℝ) := by
      apply Summable.tsum_le_tsum
      · intro n
        rw [hnorm]
        exact hterm n
      · exact hseries.norm
      · exact summable_bettinGonekZetaThreeHalvesMajorant
    _ = bettinGonekZetaThreeHalvesBound := rfl

/-- Exact half-line Gamma norm. This is the exponential-cancellation input for the functional
equation at `Re(s)=-1/2`. -/
theorem norm_Gamma_half_sub_mul_I_sq (t : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) - t * Complex.I)‖ ^ 2 =
      Real.pi / Real.cosh (Real.pi * t) := by
  let z : ℂ := (1 / 2 : ℂ) - t * Complex.I
  have hconj : (starRingEnd ℂ) z = 1 - z := by
    apply Complex.ext <;> norm_num [z]
  have hleft :
      Complex.Gamma z * Complex.Gamma (1 - z) =
        ((‖Complex.Gamma z‖ ^ 2 : ℝ) : ℂ) := by
    rw [← hconj, Complex.Gamma_conj, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
  have hsin :
      Complex.sin ((Real.pi : ℂ) * z) =
        (Real.cosh (Real.pi * t) : ℂ) := by
    rw [show (Real.pi : ℂ) * z =
      (Real.pi : ℂ) / 2 - ((Real.pi * t : ℝ) : ℂ) * Complex.I by
        simp only [z]
        push_cast
        ring]
    rw [Complex.sin_pi_div_two_sub, Complex.cos_mul_I,
      ← Complex.ofReal_cosh]
  have hcomplex :
      ((‖Complex.Gamma z‖ ^ 2 : ℝ) : ℂ) =
        ((Real.pi / Real.cosh (Real.pi * t) : ℝ) : ℂ) := by
    calc
      ((‖Complex.Gamma z‖ ^ 2 : ℝ) : ℂ) =
          Complex.Gamma z * Complex.Gamma (1 - z) := hleft.symm
      _ = (Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * z) := by
        rw [Complex.Gamma_mul_Gamma_one_sub]
      _ = ((Real.pi / Real.cosh (Real.pi * t) : ℝ) : ℂ) := by
        rw [hsin]
        push_cast
        rfl
  simpa only [z] using Complex.ofReal_injective hcomplex

/-- Exact trigonometric norm on the reflected line used by the zeta functional equation. -/
theorem norm_cos_pi_three_halves_sub_mul_I_div_two_sq (t : ℝ) :
    ‖Complex.cos ((Real.pi : ℂ) *
        ((3 / 2 : ℂ) - t * Complex.I) / 2)‖ ^ 2 =
      Real.cosh (Real.pi * t) / 2 := by
  have harg :
      (Real.pi : ℂ) * ((3 / 2 : ℂ) - t * Complex.I) / 2 =
        ((3 * Real.pi / 4 : ℝ) : ℂ) -
          ((Real.pi * t / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have hcos :
      Complex.cos ((Real.pi : ℂ) *
          ((3 / 2 : ℂ) - t * Complex.I) / 2) =
        ((Real.cos (3 * Real.pi / 4) *
          Real.cosh (Real.pi * t / 2) : ℝ) : ℂ) +
        ((Real.sin (3 * Real.pi / 4) *
          Real.sinh (Real.pi * t / 2) : ℝ) : ℂ) * Complex.I := by
    rw [harg, show
      ((3 * Real.pi / 4 : ℝ) : ℂ) -
          ((Real.pi * t / 2 : ℝ) : ℂ) * Complex.I =
        ((3 * Real.pi / 4 : ℝ) : ℂ) +
          ((-(Real.pi * t / 2) : ℝ) : ℂ) * Complex.I by
        push_cast
        ring,
      Complex.cos_add_mul_I]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_cosh,
      ← Complex.ofReal_sin, ← Complex.ofReal_sinh]
    rw [Real.cosh_neg, Real.sinh_neg]
    push_cast
    ring
  rw [hcos, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero,
    sub_zero, add_zero, mul_one]
  rw [show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 by ring,
    Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_four,
    Real.sin_pi_div_four]
  have hsqrt : Real.sqrt 2 ^ 2 = 2 := by norm_num
  have hcosh := Real.cosh_two_mul (Real.pi * t / 2)
  rw [show 2 * (Real.pi * t / 2) = Real.pi * t by ring] at hcosh
  nlinarith

/-- The Gamma and cosine factors in the functional equation cancel their exponential growth
exactly on the reflected `Re(s)=3/2` line. -/
theorem norm_Gamma_mul_cos_three_halves_sub_mul_I_sq (t : ℝ) :
    ‖Complex.Gamma ((3 / 2 : ℂ) - t * Complex.I) *
        Complex.cos ((Real.pi : ℂ) *
          ((3 / 2 : ℂ) - t * Complex.I) / 2)‖ ^ 2 =
      Real.pi / 2 * (t ^ 2 + 1 / 4) := by
  let z : ℂ := (1 / 2 : ℂ) - t * Complex.I
  have hz : z ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [z] at hre
  have hnormz : ‖z‖ ^ 2 = t ^ 2 + 1 / 4 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    norm_num [z, Complex.normSq]
    ring
  have hgamma :
      ‖Complex.Gamma ((3 / 2 : ℂ) - t * Complex.I)‖ ^ 2 =
        (t ^ 2 + 1 / 4) *
          (Real.pi / Real.cosh (Real.pi * t)) := by
    rw [show (3 / 2 : ℂ) - t * Complex.I = z + 1 by
      simp only [z]
      ring,
      Complex.Gamma_add_one z hz, norm_mul, mul_pow, hnormz,
      norm_Gamma_half_sub_mul_I_sq]
  rw [norm_mul, mul_pow, hgamma,
    norm_cos_pi_three_halves_sub_mul_I_div_two_sq]
  have hcosh_ne : Real.cosh (Real.pi * t) ≠ 0 :=
    (Real.cosh_pos _).ne'
  field_simp

theorem norm_Gamma_mul_cos_three_halves_sub_mul_I_le (t : ℝ) :
    ‖Complex.Gamma ((3 / 2 : ℂ) - t * Complex.I) *
        Complex.cos ((Real.pi : ℂ) *
          ((3 / 2 : ℂ) - t * Complex.I) / 2)‖ ≤
      2 * (1 + |t|) := by
  refine (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (by norm_num) (by positivity))).mp ?_
  rw [norm_Gamma_mul_cos_three_halves_sub_mul_I_sq]
  have ht_sq : |t| ^ 2 = t ^ 2 := sq_abs t
  have ht_nonneg : 0 ≤ |t| := abs_nonneg t
  nlinarith [Real.pi_le_four]

/-- Functional-equation transport gives a linear zeta bound on `Re(s)=-1/2`. -/
theorem norm_riemannZeta_neg_half_add_mul_I_le (t : ℝ) :
    ‖riemannZeta ((-1 / 2 : ℂ) + t * Complex.I)‖ ≤
      4 * bettinGonekZetaThreeHalvesBound * (1 + |t|) := by
  let s : ℂ := (3 / 2 : ℂ) - t * Complex.I
  have hs_nat : ∀ n : ℕ, s ≠ -n := by
    intro n h
    have hre := congrArg Complex.re h
    norm_num [s] at hre
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hs_one : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [s] at hre
  have hfe :
      riemannZeta ((-1 / 2 : ℂ) + t * Complex.I) =
        2 * (2 * Real.pi) ^ (-s) *
          (Complex.Gamma s *
            Complex.cos ((Real.pi : ℂ) * s / 2)) *
          riemannZeta s := by
    have hsource := riemannZeta_one_sub (s := s) hs_nat hs_one
    calc
      riemannZeta ((-1 / 2 : ℂ) + t * Complex.I) =
          riemannZeta (1 - s) := by
            congr 1
            simp only [s]
            ring
      _ = 2 * (2 * Real.pi) ^ (-s) * Complex.Gamma s *
          Complex.cos ((Real.pi : ℂ) * s / 2) * riemannZeta s := hsource
      _ = 2 * (2 * Real.pi) ^ (-s) *
          (Complex.Gamma s *
            Complex.cos ((Real.pi : ℂ) * s / 2)) *
          riemannZeta s := by ring
  have hpow : ‖(2 * (Real.pi : ℂ)) ^ (-s)‖ ≤ 1 := by
    rw [show (2 : ℂ) * Real.pi = ((2 * Real.pi : ℝ) : ℂ) by norm_num]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos
      (mul_pos (by norm_num) Real.pi_pos)]
    have hbase : (1 : ℝ) ≤ 2 * Real.pi := by
      nlinarith [Real.two_le_pi]
    apply Real.rpow_le_one_of_one_le_of_nonpos hbase
    norm_num [s]
  have hgamma :
      ‖Complex.Gamma s *
          Complex.cos ((Real.pi : ℂ) * s / 2)‖ ≤
        2 * (1 + |t|) := by
    simpa only [s] using
      norm_Gamma_mul_cos_three_halves_sub_mul_I_le t
  have hzeta : ‖riemannZeta s‖ ≤ bettinGonekZetaThreeHalvesBound := by
    simpa only [s] using norm_riemannZeta_three_halves_sub_mul_I_le t
  rw [hfe, norm_mul, norm_mul, norm_mul]
  norm_num
  calc
    2 * ‖(2 * (Real.pi : ℂ)) ^ (-s)‖ *
          (‖Complex.Gamma s‖ *
            ‖Complex.cos ((Real.pi : ℂ) * s / 2)‖) *
        ‖riemannZeta s‖ =
      ‖(2 * (Real.pi : ℂ)) ^ (-s)‖ *
          ‖Complex.Gamma s *
            Complex.cos ((Real.pi : ℂ) * s / 2)‖ *
        ‖riemannZeta s‖ * 2 := by
          rw [norm_mul]
          ring
    _
        ≤ 1 * (2 * (1 + |t|)) *
            bettinGonekZetaThreeHalvesBound * 2 := by
          gcongr
    _ = 4 * bettinGonekZetaThreeHalvesBound * (1 + |t|) := by ring

theorem norm_bettinGonekAuxiliaryG_mul_I_eq {rho : ℂ}
    (hrho : IsNontrivialZero rho) (t y : ℝ) :
    ‖bettinGonekAuxiliaryG rho t (y * Complex.I)‖ =
      ‖((-1 / 2 : ℂ) + (y + t) * Complex.I) - 1‖ *
          ‖riemannZeta ((-1 / 2 : ℂ) + (y + t) * Complex.I)‖ /
        (‖((-1 / 2 : ℂ) + (y + t) * Complex.I) - rho‖ *
          ‖(1 : ℂ) + (y + t) * Complex.I‖ ^ 4) := by
  let s : ℂ := (-1 / 2 : ℂ) + (y + t) * Complex.I
  have hs : bettinGonekShiftedArgument t (y * Complex.I) = s := by
    simp only [bettinGonekShiftedArgument, s]
    ring
  have hs_rho : s ≠ rho := by
    intro h
    have hre := congrArg Complex.re h
    have hrho_pos := nontrivial_zero_re_pos hrho
    norm_num [s, Complex.mul_re] at hre
    linarith
  have hs_one : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [s, Complex.mul_re] at hre
  have hplus : (y : ℂ) * Complex.I + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
  have hpm :
      ‖(y : ℂ) * Complex.I - 1‖ =
        ‖(y : ℂ) * Complex.I + 1‖ := by
    rw [Complex.norm_def, Complex.norm_def]
    congr 1
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.mul_re,
      Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im,
      mul_zero, sub_self, mul_one, zero_sub, Complex.one_re,
      Complex.sub_im, Complex.one_im, sub_zero, Complex.add_re,
      Complex.add_im, zero_add]
    ring
  have hargRho :
      bettinGonekShiftedArgument t (y * Complex.I) ≠ rho := by
    rw [hs]
    exact hs_rho
  have hargOne :
      bettinGonekShiftedArgument t (y * Complex.I) ≠ 1 := by
    rw [hs]
    exact hs_one
  rw [bettinGonekAuxiliaryG_eq_raw hrho t hargRho hargOne]
  unfold bettinGonekAuxiliaryGRaw
  rw [hs]
  simp only [norm_div, norm_mul, norm_pow]
  rw [hpm]
  have hplusNorm : ‖(y : ℂ) * Complex.I + 1‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hplus
  have hsRhoNorm : ‖s - rho‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (sub_ne_zero.mpr hs_rho)
  rw [show (y : ℂ) * Complex.I + t * Complex.I + 1 =
    (1 : ℂ) + (y + t) * Complex.I by
      ring]
  have hlastSource : (1 : ℂ) + (y + t) * Complex.I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
  have hlastSourceNorm :
      ‖(1 : ℂ) + (y + t) * Complex.I‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hlastSource
  change
    ‖(y : ℂ) * Complex.I + 1‖ ^ 2 *
          (‖s - 1‖ * ‖riemannZeta s‖ / ‖s - rho‖) /
        (‖(y : ℂ) * Complex.I + 1‖ ^ 2 *
          ‖(1 : ℂ) + (y + t) * Complex.I‖ ^ 4) =
      ‖s - 1‖ * ‖riemannZeta s‖ /
        (‖s - rho‖ * ‖(1 : ℂ) + (y + t) * Complex.I‖ ^ 4)
  field_simp

theorem bettinGonekSelectedRatio_neg_half_le {rho : ℂ}
    (hrho : IsNontrivialZero rho) (v : ℝ) :
    ‖((-1 / 2 : ℂ) + v * Complex.I) - 1‖ /
        ‖((-1 / 2 : ℂ) + v * Complex.I) - rho‖ ≤
      1 + 2 * ‖rho - 1‖ := by
  let s : ℂ := (-1 / 2 : ℂ) + v * Complex.I
  have hrho_pos := nontrivial_zero_re_pos hrho
  have hden :
      (1 / 2 : ℝ) ≤ ‖s - rho‖ := by
    have hre := Complex.abs_re_le_norm (s - rho)
    have hreValue : (s - rho).re = -1 / 2 - rho.re := by
      norm_num [s, Complex.mul_re]
    rw [hreValue, abs_of_nonpos (by linarith)] at hre
    linarith
  have hden_pos : 0 < ‖s - rho‖ := lt_of_lt_of_le (by norm_num) hden
  have htriangle :
      ‖s - 1‖ ≤ ‖s - rho‖ + ‖rho - 1‖ := by
    rw [show s - 1 = (s - rho) + (rho - 1) by ring]
    exact norm_add_le _ _
  apply (div_le_iff₀ hden_pos).2
  calc
    ‖s - 1‖ ≤ ‖s - rho‖ + ‖rho - 1‖ := htriangle
    _ ≤ (1 + 2 * ‖rho - 1‖) * ‖s - rho‖ := by
      have hrhoNorm : 0 ≤ ‖rho - 1‖ := norm_nonneg _
      nlinarith

theorem norm_one_add_mul_I_sq (v : ℝ) :
    ‖(1 : ℂ) + v * Complex.I‖ ^ 2 = 1 + v ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  norm_num
  ring

theorem norm_ofReal_add_mul_I_sq (a v : ℝ) :
    ‖(a : ℂ) + v * Complex.I‖ ^ 2 = a ^ 2 + v ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  norm_num
  ring

theorem one_add_abs_div_one_add_sq_sq_le (v : ℝ) :
    (1 + |v|) / (1 + v ^ 2) ^ 2 ≤
      4 * ((1 + |v|)⁻¹ ^ (3 : ℕ)) := by
  let a : ℝ := |v|
  have ha : 0 ≤ a := abs_nonneg v
  have ha_sq : a ^ 2 = v ^ 2 := sq_abs v
  have hp : 0 < 1 + a := by positivity
  have hq : 0 < 1 + v ^ 2 := by positivity
  have hquad : (1 + a) ^ 2 ≤ 2 * (1 + v ^ 2) := by
    nlinarith [sq_nonneg (a - 1)]
  have hfour : (1 + a) ^ 4 ≤ 4 * (1 + v ^ 2) ^ 2 := by
    have hsquare := (sq_le_sq₀ (sq_nonneg (1 + a))
      (mul_nonneg (by norm_num) hq.le)).2 hquad
    nlinarith
  change (1 + a) / (1 + v ^ 2) ^ 2 ≤ 4 * ((1 + a)⁻¹ ^ (3 : ℕ))
  rw [inv_pow]
  change (1 + a) / (1 + v ^ 2) ^ 2 ≤ 4 / (1 + a) ^ 3
  apply (div_le_div_iff₀ (pow_pos hq 2) (pow_pos hp 3)).2
  ring_nf at hfour ⊢
  exact hfour

/-- The explicit constant in the real-part-zero auxiliary decay estimate. -/
def bettinGonekAuxiliaryDecayConstant (rho : ℂ) : ℝ :=
  16 * (1 + 2 * ‖rho - 1‖) * bettinGonekZetaThreeHalvesBound

theorem bettinGonekAuxiliaryDecayConstant_nonneg (rho : ℂ) :
    0 ≤ bettinGonekAuxiliaryDecayConstant rho := by
  unfold bettinGonekAuxiliaryDecayConstant
  exact mul_nonneg
    (mul_nonneg (by norm_num) (by positivity))
    bettinGonekZetaThreeHalvesBound_nonneg

/-- A source-strength standalone estimate for `G_t` on the line `Re(w)=0`. The exponent `3`
is stronger than the `5/2` quoted in the paper. -/
theorem norm_bettinGonekAuxiliaryG_mul_I_le {rho : ℂ}
    (hrho : IsNontrivialZero rho) (t y : ℝ) :
    ‖bettinGonekAuxiliaryG rho t (y * Complex.I)‖ ≤
      bettinGonekAuxiliaryDecayConstant rho *
        ((1 + |y + t|)⁻¹ ^ (3 : ℕ)) := by
  let v : ℝ := y + t
  let s : ℂ := (-1 / 2 : ℂ) + v * Complex.I
  have hs_rho : s ≠ rho := by
    intro h
    have hre := congrArg Complex.re h
    have hrho_pos := nontrivial_zero_re_pos hrho
    norm_num [s, Complex.mul_re] at hre
    linarith
  have hden_pos : 0 < ‖s - rho‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hs_rho)
  have hnormLast :
      ‖(1 : ℂ) + v * Complex.I‖ ^ 4 = (1 + v ^ 2) ^ 2 := by
    calc
      ‖(1 : ℂ) + v * Complex.I‖ ^ 4 =
          (‖(1 : ℂ) + v * Complex.I‖ ^ 2) ^ 2 := by ring
      _ = (1 + v ^ 2) ^ 2 := by rw [norm_one_add_mul_I_sq]
  have hratio :
      ‖s - 1‖ / ‖s - rho‖ ≤ 1 + 2 * ‖rho - 1‖ := by
    simpa only [s] using bettinGonekSelectedRatio_neg_half_le hrho v
  have hzeta :
      ‖riemannZeta s‖ ≤
        4 * bettinGonekZetaThreeHalvesBound * (1 + |v|) := by
    simpa only [s] using norm_riemannZeta_neg_half_add_mul_I_le v
  have hkernel :
      (1 + |v|) / (1 + v ^ 2) ^ 2 ≤
        4 * ((1 + |v|)⁻¹ ^ (3 : ℕ)) :=
    one_add_abs_div_one_add_sq_sq_le v
  rw [norm_bettinGonekAuxiliaryG_mul_I_eq hrho t y]
  have hmain :
      ‖s - 1‖ * ‖riemannZeta s‖ /
          (‖s - rho‖ * ‖(1 : ℂ) + v * Complex.I‖ ^ 4) ≤
        bettinGonekAuxiliaryDecayConstant rho *
          ((1 + |v|)⁻¹ ^ (3 : ℕ)) := by
    rw [hnormLast]
    calc
      ‖s - 1‖ * ‖riemannZeta s‖ /
            (‖s - rho‖ * (1 + v ^ 2) ^ 2) =
          (‖s - 1‖ / ‖s - rho‖) *
            ‖riemannZeta s‖ / (1 + v ^ 2) ^ 2 := by
              field_simp
      _ ≤ (1 + 2 * ‖rho - 1‖) *
            (4 * bettinGonekZetaThreeHalvesBound * (1 + |v|)) /
            (1 + v ^ 2) ^ 2 := by
              gcongr
      _ = (4 * (1 + 2 * ‖rho - 1‖) *
            bettinGonekZetaThreeHalvesBound) *
            ((1 + |v|) / (1 + v ^ 2) ^ 2) := by ring
      _ ≤ (4 * (1 + 2 * ‖rho - 1‖) *
            bettinGonekZetaThreeHalvesBound) *
            (4 * ((1 + |v|)⁻¹ ^ (3 : ℕ))) := by
              apply mul_le_mul_of_nonneg_left hkernel
              exact mul_nonneg
                (mul_nonneg (by positivity) (by positivity))
                bettinGonekZetaThreeHalvesBound_nonneg
      _ = bettinGonekAuxiliaryDecayConstant rho *
            ((1 + |v|)⁻¹ ^ (3 : ℕ)) := by
              simp only [bettinGonekAuxiliaryDecayConstant]
              ring
  dsimp only [s, v] at hmain
  push_cast at hmain
  exact hmain

theorem integrable_bettinGonekInverseCubeShift (t : ℝ) :
    Integrable (fun y : ℝ => (1 + |y + t|)⁻¹ ^ (3 : ℕ)) := by
  have hbase :
      Integrable (fun y : ℝ => (1 + ‖y‖) ^ (-(3 : ℝ))) :=
    integrable_one_add_norm (E := ℝ) (μ := volume) (by norm_num)
  have hshift := hbase.comp_add_right t
  apply hshift.congr
  filter_upwards with y
  simp only [Real.norm_eq_abs, Real.rpow_neg_ofNat, zpow_neg,
    inv_pow]
  rfl

theorem continuous_bettinGonekAuxiliaryG_mul_I {rho : ℂ}
    (hrho : IsNontrivialZero rho) (t : ℝ) :
    Continuous (fun y : ℝ =>
      bettinGonekAuxiliaryG rho t (y * Complex.I)) := by
  rw [continuous_iff_continuousAt]
  intro y
  have hopen : IsOpen bettinGonekAuxiliaryDomain := by
    exact isOpen_lt continuous_const Complex.continuous_re
  have hy : (y : ℂ) * Complex.I ∈ bettinGonekAuxiliaryDomain := by
    norm_num [bettinGonekAuxiliaryDomain, Complex.mul_re]
  have hdiff :
      DifferentiableAt ℂ (bettinGonekAuxiliaryG rho t)
        ((y : ℂ) * Complex.I) :=
    (differentiableOn_bettinGonekAuxiliaryG hrho t).differentiableAt
      (hopen.mem_nhds hy)
  have hline : ContinuousAt (fun u : ℝ => (u : ℂ) * Complex.I) y := by
    fun_prop
  exact ContinuousAt.comp' hdiff.continuousAt hline

theorem integrable_bettinGonekAuxiliaryG_mul_I {rho : ℂ}
    (hrho : IsNontrivialZero rho) (t : ℝ) :
    Integrable (fun y : ℝ =>
      bettinGonekAuxiliaryG rho t (y * Complex.I)) := by
  have hmajor :=
    (integrable_bettinGonekInverseCubeShift t).const_mul
      (bettinGonekAuxiliaryDecayConstant rho)
  apply hmajor.mono'
  · exact (continuous_bettinGonekAuxiliaryG_mul_I hrho t).aestronglyMeasurable
  · filter_upwards with y
    exact norm_bettinGonekAuxiliaryG_mul_I_le hrho t y

theorem norm_bettinGonekAuxiliaryG_three_add_mul_I_eq {rho : ℂ}
    (hrho : IsNontrivialZero rho) (t y : ℝ) :
    ‖bettinGonekAuxiliaryG rho t (3 + y * Complex.I)‖ =
      (‖(2 : ℂ) + y * Complex.I‖ ^ 2 /
          ‖(4 : ℂ) + y * Complex.I‖ ^ 2) *
        (‖((5 / 2 : ℂ) + (y + t) * Complex.I) - 1‖ /
          ‖((5 / 2 : ℂ) + (y + t) * Complex.I) - rho‖) *
        ‖riemannZeta ((5 / 2 : ℂ) + (y + t) * Complex.I)‖ /
        ‖(4 : ℂ) + (y + t) * Complex.I‖ ^ 4 := by
  let w : ℂ := 3 + y * Complex.I
  let s : ℂ := (5 / 2 : ℂ) + (y + t) * Complex.I
  have hs : bettinGonekShiftedArgument t w = s := by
    simp only [bettinGonekShiftedArgument, w, s]
    ring
  have hs_rho : s ≠ rho := by
    intro h
    have hre := congrArg Complex.re h
    have hrho_lt := nontrivial_zero_re_lt_one hrho
    norm_num [s, Complex.mul_re] at hre
    linarith
  have hs_one : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [s, Complex.mul_re] at hre
  have hargRho : bettinGonekShiftedArgument t w ≠ rho := by
    rw [hs]
    exact hs_rho
  have hargOne : bettinGonekShiftedArgument t w ≠ 1 := by
    rw [hs]
    exact hs_one
  have hwPlus : (4 : ℂ) + y * Complex.I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
  have hsRho : s - rho ≠ 0 := sub_ne_zero.mpr hs_rho
  have hlast : (4 : ℂ) + (y + t) * Complex.I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
  rw [show (3 : ℂ) + y * Complex.I = w by rfl,
    bettinGonekAuxiliaryG_eq_raw hrho t hargRho hargOne]
  unfold bettinGonekAuxiliaryGRaw
  rw [hs]
  simp only [norm_div, norm_mul, norm_pow]
  rw [show w - 1 = (2 : ℂ) + y * Complex.I by
        simp only [w]
        ring,
      show w + 1 = (4 : ℂ) + y * Complex.I by
        simp only [w]
        ring,
      show w + t * Complex.I + 1 =
        (4 : ℂ) + (y + t) * Complex.I by
        simp only [w]
        ring]
  change
    ‖(2 : ℂ) + y * Complex.I‖ ^ 2 *
          (‖s - 1‖ * ‖riemannZeta s‖ / ‖s - rho‖) /
        (‖(4 : ℂ) + y * Complex.I‖ ^ 2 *
          ‖(4 : ℂ) + (y + t) * Complex.I‖ ^ 4) =
      (‖(2 : ℂ) + y * Complex.I‖ ^ 2 /
          ‖(4 : ℂ) + y * Complex.I‖ ^ 2) *
        (‖s - 1‖ / ‖s - rho‖) * ‖riemannZeta s‖ /
        ‖(4 : ℂ) + (y + t) * Complex.I‖ ^ 4
  have hwPlusNorm : ‖(4 : ℂ) + y * Complex.I‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hwPlus
  have hsRhoNorm : ‖s - rho‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hsRho
  have hlastNorm : ‖(4 : ℂ) + (y + t) * Complex.I‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hlast
  field_simp

theorem bettinGonekOuterRatio_three_le_one (y : ℝ) :
    ‖(2 : ℂ) + y * Complex.I‖ ^ 2 /
        ‖(4 : ℂ) + y * Complex.I‖ ^ 2 ≤ 1 := by
  have hnum :
      ‖(2 : ℂ) + y * Complex.I‖ ^ 2 = 4 + y ^ 2 := by
    convert norm_ofReal_add_mul_I_sq 2 y using 1 <;> norm_num
  have hden :
      ‖(4 : ℂ) + y * Complex.I‖ ^ 2 = 16 + y ^ 2 := by
    convert norm_ofReal_add_mul_I_sq 4 y using 1 <;> norm_num
  rw [hnum, hden, div_le_one (by positivity)]
  norm_num

theorem bettinGonekSelectedRatio_five_halves_le {rho : ℂ}
    (hrho : IsNontrivialZero rho) (v : ℝ) :
    ‖((5 / 2 : ℂ) + v * Complex.I) - 1‖ /
        ‖((5 / 2 : ℂ) + v * Complex.I) - rho‖ ≤
      1 + ‖rho - 1‖ := by
  let s : ℂ := (5 / 2 : ℂ) + v * Complex.I
  have hrho_lt := nontrivial_zero_re_lt_one hrho
  have hden : (1 : ℝ) ≤ ‖s - rho‖ := by
    have hre := Complex.abs_re_le_norm (s - rho)
    have hreValue : (s - rho).re = 5 / 2 - rho.re := by
      norm_num [s, Complex.mul_re]
    rw [hreValue, abs_of_pos (by linarith)] at hre
    linarith
  have hden_pos : 0 < ‖s - rho‖ := lt_of_lt_of_le zero_lt_one hden
  have htriangle :
      ‖s - 1‖ ≤ ‖s - rho‖ + ‖rho - 1‖ := by
    rw [show s - 1 = (s - rho) + (rho - 1) by ring]
    exact norm_add_le _ _
  apply (div_le_iff₀ hden_pos).2
  calc
    ‖s - 1‖ ≤ ‖s - rho‖ + ‖rho - 1‖ := htriangle
    _ ≤ (1 + ‖rho - 1‖) * ‖s - rho‖ := by
      have hrhoNorm : 0 ≤ ‖rho - 1‖ := norm_nonneg _
      nlinarith

theorem one_div_sixteen_add_sq_sq_le (v : ℝ) :
    1 / (16 + v ^ 2) ^ 2 ≤
      4 * ((1 + |v|)⁻¹ ^ (3 : ℕ)) := by
  have hone : 0 < 1 + v ^ 2 := by positivity
  have hsixteen : 0 < 16 + v ^ 2 := by positivity
  calc
    1 / (16 + v ^ 2) ^ 2 ≤ 1 / (1 + v ^ 2) ^ 2 := by
      apply one_div_le_one_div_of_le (pow_pos hone 2)
      gcongr
      linarith
    _ ≤ (1 + |v|) / (1 + v ^ 2) ^ 2 := by
      apply div_le_div_of_nonneg_right
      · linarith [abs_nonneg v]
      · positivity
    _ ≤ 4 * ((1 + |v|)⁻¹ ^ (3 : ℕ)) :=
      one_add_abs_div_one_add_sq_sq_le v

def bettinGonekAuxiliaryRightDecayConstant (rho : ℂ) : ℝ :=
  4 * (1 + ‖rho - 1‖) * bettinGonekZetaThreeHalvesBound

theorem bettinGonekAuxiliaryRightDecayConstant_nonneg (rho : ℂ) :
    0 ≤ bettinGonekAuxiliaryRightDecayConstant rho := by
  unfold bettinGonekAuxiliaryRightDecayConstant
  exact mul_nonneg
    (mul_nonneg (by norm_num) (by positivity))
    bettinGonekZetaThreeHalvesBound_nonneg

theorem norm_bettinGonekAuxiliaryG_three_add_mul_I_le {rho : ℂ}
    (hrho : IsNontrivialZero rho) (t y : ℝ) :
    ‖bettinGonekAuxiliaryG rho t (3 + y * Complex.I)‖ ≤
      bettinGonekAuxiliaryRightDecayConstant rho *
        ((1 + |y + t|)⁻¹ ^ (3 : ℕ)) := by
  let v : ℝ := y + t
  let s : ℂ := (5 / 2 : ℂ) + v * Complex.I
  have houter :
      ‖(2 : ℂ) + y * Complex.I‖ ^ 2 /
          ‖(4 : ℂ) + y * Complex.I‖ ^ 2 ≤ 1 :=
    bettinGonekOuterRatio_three_le_one y
  have hratio :
      ‖s - 1‖ / ‖s - rho‖ ≤ 1 + ‖rho - 1‖ := by
    simpa only [s] using bettinGonekSelectedRatio_five_halves_le hrho v
  have hzeta :
      ‖riemannZeta s‖ ≤ bettinGonekZetaThreeHalvesBound := by
    have h := norm_riemannZeta_le_three_halves_majorant
      (show (3 / 2 : ℝ) ≤ 5 / 2 by norm_num) v
    dsimp only [s]
    convert h using 1
    norm_num
  have hnormLast :
      ‖(4 : ℂ) + v * Complex.I‖ ^ 4 = (16 + v ^ 2) ^ 2 := by
    calc
      ‖(4 : ℂ) + v * Complex.I‖ ^ 4 =
          (‖(4 : ℂ) + v * Complex.I‖ ^ 2) ^ 2 := by ring
      _ = (16 + v ^ 2) ^ 2 := by
        rw [show ‖(4 : ℂ) + v * Complex.I‖ ^ 2 =
          16 + v ^ 2 by
            convert norm_ofReal_add_mul_I_sq 4 v using 1 <;> norm_num]
  have hkernel :
      1 / (16 + v ^ 2) ^ 2 ≤
        4 * ((1 + |v|)⁻¹ ^ (3 : ℕ)) :=
    one_div_sixteen_add_sq_sq_le v
  rw [norm_bettinGonekAuxiliaryG_three_add_mul_I_eq hrho t y]
  have hmain :
      (‖(2 : ℂ) + y * Complex.I‖ ^ 2 /
          ‖(4 : ℂ) + y * Complex.I‖ ^ 2) *
        (‖s - 1‖ / ‖s - rho‖) * ‖riemannZeta s‖ /
          ‖(4 : ℂ) + v * Complex.I‖ ^ 4 ≤
        bettinGonekAuxiliaryRightDecayConstant rho *
          ((1 + |v|)⁻¹ ^ (3 : ℕ)) := by
    rw [hnormLast]
    calc
      (‖(2 : ℂ) + y * Complex.I‖ ^ 2 /
            ‖(4 : ℂ) + y * Complex.I‖ ^ 2) *
          (‖s - 1‖ / ‖s - rho‖) * ‖riemannZeta s‖ /
            (16 + v ^ 2) ^ 2 ≤
        1 * (1 + ‖rho - 1‖) *
          bettinGonekZetaThreeHalvesBound / (16 + v ^ 2) ^ 2 := by
            gcongr
      _ = ((1 + ‖rho - 1‖) *
          bettinGonekZetaThreeHalvesBound) *
          (1 / (16 + v ^ 2) ^ 2) := by ring
      _ ≤ ((1 + ‖rho - 1‖) *
          bettinGonekZetaThreeHalvesBound) *
          (4 * ((1 + |v|)⁻¹ ^ (3 : ℕ))) := by
            apply mul_le_mul_of_nonneg_left hkernel
            exact mul_nonneg (by positivity)
              bettinGonekZetaThreeHalvesBound_nonneg
      _ = bettinGonekAuxiliaryRightDecayConstant rho *
          ((1 + |v|)⁻¹ ^ (3 : ℕ)) := by
            simp only [bettinGonekAuxiliaryRightDecayConstant]
            ring
  dsimp only [s, v] at hmain
  push_cast at hmain
  exact hmain

/-- The common boundary constant for the strip-lifted auxiliary function. -/
def bettinGonekAuxiliaryStripLiftBound (rho : ℂ) : ℝ :=
  max (bettinGonekAuxiliaryDecayConstant rho)
    (64 * bettinGonekAuxiliaryRightDecayConstant rho)

theorem bettinGonekAuxiliaryStripLiftBound_nonneg (rho : ℂ) :
    0 ≤ bettinGonekAuxiliaryStripLiftBound rho := by
  exact (bettinGonekAuxiliaryDecayConstant_nonneg rho).trans
    (le_max_left _ _)

theorem norm_bettinGonekAuxiliaryStripLift_mul_I_le
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t y : ℝ) :
    ‖bettinGonekAuxiliaryStripLift rho t (y * Complex.I)‖ ≤
      bettinGonekAuxiliaryStripLiftBound rho := by
  let v : ℝ := y + t
  let A : ℝ := 1 + |v|
  have hA : 0 < A := by dsimp [A]; positivity
  have hden :
      ‖(y : ℂ) * Complex.I + t * Complex.I + 1‖ ≤ A := by
    rw [show (y : ℂ) * Complex.I + t * Complex.I + 1 =
      (1 : ℂ) + v * Complex.I by
        dsimp [v]
        push_cast
        ring]
    calc
      ‖(1 : ℂ) + v * Complex.I‖ ≤ ‖(1 : ℂ)‖ + ‖(v : ℂ) * Complex.I‖ :=
        norm_add_le _ _
      _ = A := by simp [A, Real.norm_eq_abs]
  have hdenPow :
      ‖((y : ℂ) * Complex.I + t * Complex.I + 1) ^ 3‖ ≤ A ^ 3 := by
    rw [norm_pow]
    gcongr
  have hG := norm_bettinGonekAuxiliaryG_mul_I_le hrho t y
  change ‖bettinGonekAuxiliaryG rho t (y * Complex.I) *
      ((y : ℂ) * Complex.I + t * Complex.I + 1) ^ 3‖ ≤ _
  rw [norm_mul]
  calc
    ‖bettinGonekAuxiliaryG rho t (y * Complex.I)‖ *
          ‖((y : ℂ) * Complex.I + t * Complex.I + 1) ^ 3‖
        ≤ (bettinGonekAuxiliaryDecayConstant rho * A⁻¹ ^ (3 : ℕ)) *
            A ^ 3 := by
          exact mul_le_mul hG hdenPow (norm_nonneg _)
            (mul_nonneg (bettinGonekAuxiliaryDecayConstant_nonneg rho)
              (by positivity))
    _ = bettinGonekAuxiliaryDecayConstant rho := by
      rw [inv_pow]
      field_simp
    _ ≤ bettinGonekAuxiliaryStripLiftBound rho := le_max_left _ _

theorem norm_bettinGonekAuxiliaryStripLift_three_add_mul_I_le
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t y : ℝ) :
    ‖bettinGonekAuxiliaryStripLift rho t (3 + y * Complex.I)‖ ≤
      bettinGonekAuxiliaryStripLiftBound rho := by
  let v : ℝ := y + t
  let A : ℝ := 1 + |v|
  have hA : 0 < A := by dsimp [A]; positivity
  have hden :
      ‖(3 : ℂ) + y * Complex.I + t * Complex.I + 1‖ ≤ 4 * A := by
    rw [show (3 : ℂ) + y * Complex.I + t * Complex.I + 1 =
      (4 : ℂ) + v * Complex.I by
        dsimp [v]
        push_cast
        ring]
    calc
      ‖(4 : ℂ) + v * Complex.I‖ ≤ ‖(4 : ℂ)‖ + ‖(v : ℂ) * Complex.I‖ :=
        norm_add_le _ _
      _ = 4 + |v| := by simp [Real.norm_eq_abs]
      _ ≤ 4 * A := by
        dsimp [A]
        linarith [abs_nonneg v]
  have hdenPow :
      ‖((3 : ℂ) + y * Complex.I + t * Complex.I + 1) ^ 3‖ ≤
        64 * A ^ 3 := by
    rw [norm_pow]
    calc
      ‖(3 : ℂ) + y * Complex.I + t * Complex.I + 1‖ ^ 3 ≤
          (4 * A) ^ 3 := by gcongr
      _ = 64 * A ^ 3 := by ring
  have hG := norm_bettinGonekAuxiliaryG_three_add_mul_I_le hrho t y
  change ‖bettinGonekAuxiliaryG rho t (3 + y * Complex.I) *
      ((3 : ℂ) + y * Complex.I + t * Complex.I + 1) ^ 3‖ ≤ _
  rw [norm_mul]
  calc
    ‖bettinGonekAuxiliaryG rho t (3 + y * Complex.I)‖ *
          ‖((3 : ℂ) + y * Complex.I + t * Complex.I + 1) ^ 3‖
        ≤ (bettinGonekAuxiliaryRightDecayConstant rho * A⁻¹ ^ (3 : ℕ)) *
            (64 * A ^ 3) := by
          exact mul_le_mul hG hdenPow (norm_nonneg _)
            (mul_nonneg (bettinGonekAuxiliaryRightDecayConstant_nonneg rho)
              (by positivity))
    _ = 64 * bettinGonekAuxiliaryRightDecayConstant rho := by
      rw [inv_pow]
      field_simp
    _ ≤ bettinGonekAuxiliaryStripLiftBound rho := le_max_right _ _

theorem diffContOnCl_bettinGonekAuxiliaryStripLift
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ) :
    DiffContOnCl ℂ (bettinGonekAuxiliaryStripLift rho t)
      (Complex.re ⁻¹' Set.Ioo (0 : ℝ) 3) := by
  have hclosure :
      closure (Complex.re ⁻¹' Set.Ioo (0 : ℝ) 3) ⊆
        Complex.re ⁻¹' Set.Icc (0 : ℝ) 3 :=
    closure_minimal
      (preimage_mono Set.Ioo_subset_Icc_self)
      (isClosed_Icc.preimage Complex.continuous_re)
  have hdomain :
      Complex.re ⁻¹' Set.Icc (0 : ℝ) 3 ⊆ bettinGonekAuxiliaryDomain := by
    intro w hw
    change -1 < w.re
    change w.re ∈ Set.Icc (0 : ℝ) 3 at hw
    linarith [hw.1]
  apply DifferentiableOn.diffContOnCl
  exact
    ((differentiableOn_bettinGonekAuxiliaryG hrho t).mul
      (by fun_prop : DifferentiableOn ℂ
        (fun w : ℂ => (w + t * Complex.I + 1) ^ 3)
        bettinGonekAuxiliaryDomain)).mono
      (hclosure.trans hdomain)

theorem bettinGonekCancelledZeta_eq_zetaPoleRemoved_div
    {rho s : ℂ} (hrho : IsNontrivialZero rho) (hs : s ≠ rho) :
    bettinGonekCancelledZeta rho s = zetaPoleRemoved s / (s - rho) := by
  rw [bettinGonekCancelledZeta, dslope_of_ne _ hs, slope_fun_def_field,
    zetaPoleRemoved_eq_zero_of_nontrivialZero hrho]
  simp

theorem bettinGonekAuxiliaryStripLift_eq_reduced
    (rho : ℂ) (t : ℝ) {w : ℂ} (hw : w ∈ bettinGonekAuxiliaryDomain) :
    bettinGonekAuxiliaryStripLift rho t w =
      (w - 1) ^ 2 *
          bettinGonekCancelledZeta rho (bettinGonekShiftedArgument t w) /
        ((w + 1) ^ 2 * (w + t * Complex.I + 1)) := by
  have hplus : w + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    change -1 < w.re at hw
    norm_num at hre
    linarith
  have hshift : w + t * Complex.I + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    change -1 < w.re at hw
    norm_num [Complex.add_re, Complex.mul_re] at hre
    linarith
  unfold bettinGonekAuxiliaryStripLift bettinGonekAuxiliaryG
  field_simp

theorem norm_bettinGonekAuxiliaryStripLift_le_exp_sq_of_large_im
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ)
    {C : ℝ} (hC : 0 < C)
    (hgrowth : ∀ z : ℂ,
      ‖zetaPoleRemoved z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (2 : ℝ)))
    {w : ℂ} (hw : w.re ∈ Set.Icc (0 : ℝ) 3)
    (hwIm : |t| + |rho.im| + 1 ≤ |w.im|) :
    ‖bettinGonekAuxiliaryStripLift rho t w‖ ≤
      Real.exp ((1 + C * (4 + |t|) ^ 2) *
        (2 + |w.im|) ^ (2 : ℝ)) := by
  let s : ℂ := bettinGonekShiftedArgument t w
  let X : ℝ := 2 + |w.im|
  let L : ℝ := 4 + |t|
  have hX : 0 < X := by dsimp [X]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have hdomain : w ∈ bettinGonekAuxiliaryDomain := by
    change -1 < w.re
    linarith [hw.1]
  have hsIm : s.im = w.im + t := by
    simp [s, bettinGonekShiftedArgument]
  have hdiffIm : (s - rho).im = w.im + t - rho.im := by
    rw [Complex.sub_im, hsIm]
  have htriangle :
      |w.im| ≤ |w.im + t - rho.im| + |t| + |rho.im| := by
    calc
      |w.im| = |(w.im + t - rho.im) + (-t) + rho.im| := by ring_nf
      _ ≤ |(w.im + t - rho.im) + (-t)| + |rho.im| := abs_add_le _ _
      _ ≤ (|w.im + t - rho.im| + |-t|) + |rho.im| := by
        gcongr
        exact abs_add_le _ _
      _ = |w.im + t - rho.im| + |t| + |rho.im| := by rw [abs_neg]
  have hselected : 1 ≤ ‖s - rho‖ := by
    calc
      1 ≤ |w.im + t - rho.im| := by linarith
      _ = |(s - rho).im| := by rw [hdiffIm]
      _ ≤ ‖s - rho‖ := Complex.abs_im_le_norm _
  have hsRho : s ≠ rho := by
    exact sub_ne_zero.mp (norm_pos_iff.mp (zero_lt_one.trans_le hselected))
  have hsRe : s.re = w.re - 1 / 2 := by
    simp [s, bettinGonekShiftedArgument]
  have hsReAbs : |s.re| ≤ 5 / 2 := by
    rw [hsRe, abs_le]
    constructor <;> linarith [hw.1, hw.2]
  have hsNorm : ‖s‖ ≤ 5 / 2 + |w.im| + |t| := by
    calc
      ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ ≤ 5 / 2 + |w.im + t| := by
        rw [hsIm]
        linarith
      _ ≤ 5 / 2 + (|w.im| + |t|) := by
        gcongr
        exact abs_add_le _ _
      _ = 5 / 2 + |w.im| + |t| := by ring
  have hsScale : 1 + ‖s‖ ≤ L * X := by
    dsimp [L, X]
    have ht : 0 ≤ |t| := abs_nonneg t
    have hwImNonneg : 0 ≤ |w.im| := abs_nonneg w.im
    nlinarith
  have hsGrowth :
      ‖zetaPoleRemoved s‖ ≤
        Real.exp (C * (L * X) ^ (2 : ℝ)) := by
    calc
      ‖zetaPoleRemoved s‖ ≤
          Real.exp (C * (1 + ‖s‖) ^ (2 : ℝ)) := hgrowth s
      _ ≤ Real.exp (C * (L * X) ^ (2 : ℝ)) := by
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_left _ hC.le
        rw [Real.rpow_two, Real.rpow_two]
        exact (sq_le_sq₀ (by positivity) (by positivity)).2 hsScale
  have hcancelled :
      ‖bettinGonekCancelledZeta rho s‖ ≤
        Real.exp (C * (L * X) ^ (2 : ℝ)) := by
    rw [bettinGonekCancelledZeta_eq_zetaPoleRemoved_div hrho hsRho,
      norm_div]
    exact (div_le_self (norm_nonneg _) hselected).trans hsGrowth
  have hwSub :
      ‖w - 1‖ ≤ X := by
    calc
      ‖w - 1‖ ≤ |(w - 1).re| + |(w - 1).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = |w.re - 1| + |w.im| := by simp
      _ ≤ 2 + |w.im| := by
        gcongr
        rw [abs_le]
        constructor <;> linarith [hw.1, hw.2]
      _ = X := rfl
  have hwPlus : 1 ≤ ‖w + 1‖ := by
    calc
      1 ≤ |(w + 1).re| := by
        rw [show (w + 1).re = w.re + 1 by simp,
          abs_of_nonneg (by linarith [hw.1])]
        linarith [hw.1]
      _ ≤ ‖w + 1‖ := Complex.abs_re_le_norm _
  have hwShift : 1 ≤ ‖w + t * Complex.I + 1‖ := by
    calc
      1 ≤ |(w + t * Complex.I + 1).re| := by
        rw [show (w + t * Complex.I + 1).re = w.re + 1 by
          simp [Complex.mul_re],
          abs_of_nonneg (by linarith [hw.1])]
        linarith [hw.1]
      _ ≤ ‖w + t * Complex.I + 1‖ := Complex.abs_re_le_norm _
  have hden :
      1 ≤ ‖(w + 1) ^ 2 * (w + t * Complex.I + 1)‖ := by
    rw [norm_mul, norm_pow]
    nlinarith [one_le_pow₀ hwPlus (n := 2)]
  rw [bettinGonekAuxiliaryStripLift_eq_reduced rho t hdomain,
    norm_div, norm_mul, norm_pow]
  calc
    ‖w - 1‖ ^ 2 * ‖bettinGonekCancelledZeta rho s‖ /
          ‖(w + 1) ^ 2 * (w + t * Complex.I + 1)‖
        ≤ ‖w - 1‖ ^ 2 * ‖bettinGonekCancelledZeta rho s‖ :=
      div_le_self (by positivity) hden
    _ ≤ X ^ 2 * Real.exp (C * (L * X) ^ (2 : ℝ)) := by
      gcongr
    _ ≤ Real.exp (X ^ 2) * Real.exp (C * (L * X) ^ (2 : ℝ)) := by
      gcongr
      exact (le_add_of_nonneg_left zero_le_one).trans
        (by simpa [add_comm] using Real.add_one_le_exp (X ^ 2))
    _ = Real.exp ((1 + C * L ^ 2) * X ^ (2 : ℝ)) := by
      rw [← Real.exp_add]
      simp only [Real.rpow_two]
      congr 1
      ring
    _ = Real.exp ((1 + C * (4 + |t|) ^ 2) *
          (2 + |w.im|) ^ (2 : ℝ)) := rfl

theorem bettinGonekAuxiliaryStripLift_growth
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ) :
    ∃ c < Real.pi / (3 - 0), ∃ D : ℝ,
      bettinGonekAuxiliaryStripLift rho t =O[
        comap (_root_.abs ∘ Complex.im) atTop ⊓
          Filter.principal (Complex.re ⁻¹' Set.Ioo (0 : ℝ) 3)]
        fun z ↦ Real.exp (D * Real.exp (c * |z.im|)) := by
  obtain ⟨C, hC, hgrowth⟩ := exists_norm_zetaPoleRemoved_le_exp_sq
  let A : ℝ := 1 + C * (4 + |t|) ^ 2
  let K : ℝ := 4 * A
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hK : 0 < K := mul_pos (by norm_num) hA
  have hsmall := (Real.isLittleO_pow_exp_atTop (n := 2)).def (inv_pos.mpr hK)
  have hev_real : ∀ᶠ T : ℝ in atTop,
      A * (2 + T) ^ (2 : ℝ) ≤ Real.exp T := by
    filter_upwards [hsmall, eventually_ge_atTop (2 : ℝ)] with T hsmallT hT
    have hsmallT' : T ^ 2 ≤ K⁻¹ * Real.exp T := by
      simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg T),
        abs_of_pos (Real.exp_pos T)] using hsmallT
    have hKBound : K * T ^ 2 ≤ Real.exp T := by
      calc
        K * T ^ 2 ≤ K * (K⁻¹ * Real.exp T) :=
          mul_le_mul_of_nonneg_left hsmallT' hK.le
        _ = Real.exp T := by field_simp
    have hsq : (2 + T) ^ (2 : ℝ) ≤ 4 * T ^ 2 := by
      rw [Real.rpow_two]
      nlinarith [sq_nonneg T]
    calc
      A * (2 + T) ^ (2 : ℝ) ≤ A * (4 * T ^ 2) :=
        mul_le_mul_of_nonneg_left hsq hA.le
      _ = K * T ^ 2 := by
        dsimp [K]
        ring
      _ ≤ Real.exp T := hKBound
  have hev_complex : ∀ᶠ z : ℂ in comap (_root_.abs ∘ Complex.im) atTop,
      A * (2 + |z.im|) ^ (2 : ℝ) ≤ Real.exp |z.im| :=
    tendsto_comap.eventually hev_real
  have hlarge_real : ∀ᶠ T : ℝ in atTop,
      |t| + |rho.im| + 1 ≤ T :=
    eventually_ge_atTop (|t| + |rho.im| + 1)
  have hlarge_complex : ∀ᶠ z : ℂ in comap (_root_.abs ∘ Complex.im) atTop,
      |t| + |rho.im| + 1 ≤ |z.im| :=
    tendsto_comap.eventually hlarge_real
  refine ⟨1, ?_, 1, ?_⟩
  · norm_num
    nlinarith [Real.pi_gt_three]
  · rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    rw [eventually_inf_principal]
    filter_upwards [hev_complex, hlarge_complex] with z hExp hLarge hz
    have hzClosed : z.re ∈ Set.Icc (0 : ℝ) 3 := ⟨hz.1.le, hz.2.le⟩
    calc
      ‖bettinGonekAuxiliaryStripLift rho t z‖
          ≤ Real.exp (A * (2 + |z.im|) ^ (2 : ℝ)) := by
            simpa only [A] using
              norm_bettinGonekAuxiliaryStripLift_le_exp_sq_of_large_im
                hrho t hC hgrowth hzClosed hLarge
      _ ≤ Real.exp (Real.exp |z.im|) := Real.exp_le_exp.mpr hExp
      _ = 1 * ‖Real.exp (1 * Real.exp (1 * |z.im|))‖ := by
        simp [Real.norm_eq_abs]

theorem norm_bettinGonekAuxiliaryStripLift_le
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ)
    {w : ℂ} (hw : w.re ∈ Set.Icc (0 : ℝ) 3) :
    ‖bettinGonekAuxiliaryStripLift rho t w‖ ≤
      bettinGonekAuxiliaryStripLiftBound rho := by
  apply PhragmenLindelof.vertical_strip
    (a := (0 : ℝ)) (b := (3 : ℝ))
    (diffContOnCl_bettinGonekAuxiliaryStripLift hrho t)
    (bettinGonekAuxiliaryStripLift_growth hrho t)
  · intro z hz
    have hzEq : z = z.im * Complex.I := by
      apply Complex.ext <;> simp [hz]
    rw [hzEq]
    exact norm_bettinGonekAuxiliaryStripLift_mul_I_le hrho t z.im
  · intro z hz
    have hzEq : z = (3 : ℂ) + z.im * Complex.I := by
      apply Complex.ext <;> simp [hz]
    rw [hzEq]
    exact
      norm_bettinGonekAuxiliaryStripLift_three_add_mul_I_le hrho t z.im
  · exact hw.1
  · exact hw.2

theorem norm_bettinGonekAuxiliaryG_fixedStrip_le
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ)
    {a v : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 3) (hv : 1 ≤ |v|) :
    ‖bettinGonekAuxiliaryG rho t
        (a + (v - t) * Complex.I)‖ ≤
      bettinGonekAuxiliaryStripLiftBound rho / |v| ^ 3 := by
  let w : ℂ := a + (v - t) * Complex.I
  let d : ℂ := w + t * Complex.I + 1
  have hwRe : w.re ∈ Set.Icc (0 : ℝ) 3 := by
    simpa [w, Complex.mul_re] using ha
  have hdIm : d.im = v := by
    simp [d, w]
  have hdLower : |v| ≤ ‖d‖ := by
    rw [← hdIm]
    exact Complex.abs_im_le_norm d
  have hdPos : 0 < ‖d‖ ^ 3 := pow_pos
    (zero_lt_one.trans_le (hv.trans hdLower)) 3
  have hdNe : ‖d‖ ≠ 0 :=
    (zero_lt_one.trans_le (hv.trans hdLower)).ne'
  have hvPos : 0 < |v| ^ 3 := pow_pos (zero_lt_one.trans_le hv) 3
  have hdenPow : |v| ^ 3 ≤ ‖d‖ ^ 3 := by gcongr
  have hLift := norm_bettinGonekAuxiliaryStripLift_le hrho t hwRe
  change ‖bettinGonekAuxiliaryG rho t w * d ^ 3‖ ≤
    bettinGonekAuxiliaryStripLiftBound rho at hLift
  rw [norm_mul, norm_pow] at hLift
  calc
    ‖bettinGonekAuxiliaryG rho t w‖
        = (‖bettinGonekAuxiliaryG rho t w‖ * ‖d‖ ^ 3) / ‖d‖ ^ 3 := by
          field_simp [hdNe]
    _ ≤ bettinGonekAuxiliaryStripLiftBound rho / ‖d‖ ^ 3 :=
      div_le_div_of_nonneg_right hLift hdPos.le
    _ ≤ bettinGonekAuxiliaryStripLiftBound rho / |v| ^ 3 :=
      div_le_div_of_nonneg_left
        (bettinGonekAuxiliaryStripLiftBound_nonneg rho) hvPos hdenPow

theorem norm_bettinGonekAuxiliaryG_rightLine_eq
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ)
    {R : ℝ} (hR : 3 ≤ R) (y : ℝ) :
    ‖bettinGonekAuxiliaryG rho t (R + y * Complex.I)‖ =
      (‖((R - 1 : ℝ) : ℂ) + y * Complex.I‖ ^ 2 /
          ‖((R + 1 : ℝ) : ℂ) + y * Complex.I‖ ^ 2) *
        (‖((R - 1 / 2 : ℝ) : ℂ) + (y + t) * Complex.I - 1‖ /
          ‖((R - 1 / 2 : ℝ) : ℂ) + (y + t) * Complex.I - rho‖) *
        ‖riemannZeta
          ((R - 1 / 2 : ℝ) + (y + t) * Complex.I)‖ /
        ‖((R + 1 : ℝ) : ℂ) + (y + t) * Complex.I‖ ^ 4 := by
  let w : ℂ := R + y * Complex.I
  let s : ℂ := (R - 1 / 2 : ℝ) + (y + t) * Complex.I
  have hs : bettinGonekShiftedArgument t w = s := by
    simp only [bettinGonekShiftedArgument, w, s]
    push_cast
    ring
  have hsRho : s ≠ rho := by
    intro h
    have hre := congrArg Complex.re h
    have hrhoLt := nontrivial_zero_re_lt_one hrho
    norm_num [s, Complex.mul_re] at hre
    linarith
  have hsOne : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [s, Complex.mul_re] at hre
    linarith
  have hwPlus : ((R + 1 : ℝ) : ℂ) + y * Complex.I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have hlast :
      ((R + 1 : ℝ) : ℂ) + (y + t) * Complex.I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  rw [show (R : ℂ) + y * Complex.I = w by rfl,
    bettinGonekAuxiliaryG_eq_raw hrho t (by simpa [hs]) (by simpa [hs])]
  unfold bettinGonekAuxiliaryGRaw
  rw [hs]
  simp only [norm_div, norm_mul, norm_pow]
  rw [show w - 1 = ((R - 1 : ℝ) : ℂ) + y * Complex.I by
        simp only [w]
        push_cast
        ring,
      show w + 1 = ((R + 1 : ℝ) : ℂ) + y * Complex.I by
        simp only [w]
        push_cast
        ring,
      show w + t * Complex.I + 1 =
        ((R + 1 : ℝ) : ℂ) + (y + t) * Complex.I by
        simp only [w]
        push_cast
        ring]
  have hwPlusNorm :
      ‖((R + 1 : ℝ) : ℂ) + y * Complex.I‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hwPlus
  have hsRhoNorm : ‖s - rho‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (sub_ne_zero.mpr hsRho)
  have hlastNorm :
      ‖((R + 1 : ℝ) : ℂ) + (y + t) * Complex.I‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hlast
  change
    ‖((R - 1 : ℝ) : ℂ) + y * Complex.I‖ ^ 2 *
          (‖s - 1‖ * ‖riemannZeta s‖ / ‖s - rho‖) /
        (‖((R + 1 : ℝ) : ℂ) + y * Complex.I‖ ^ 2 *
          ‖((R + 1 : ℝ) : ℂ) + (y + t) * Complex.I‖ ^ 4) =
      (‖((R - 1 : ℝ) : ℂ) + y * Complex.I‖ ^ 2 /
          ‖((R + 1 : ℝ) : ℂ) + y * Complex.I‖ ^ 2) *
        (‖s - 1‖ / ‖s - rho‖) * ‖riemannZeta s‖ /
          ‖((R + 1 : ℝ) : ℂ) + (y + t) * Complex.I‖ ^ 4
  field_simp

theorem bettinGonekOuterRatio_rightLine_le_one
    {R y : ℝ} (hR : 0 ≤ R) :
    ‖((R - 1 : ℝ) : ℂ) + y * Complex.I‖ ^ 2 /
        ‖((R + 1 : ℝ) : ℂ) + y * Complex.I‖ ^ 2 ≤ 1 := by
  rw [norm_ofReal_add_mul_I_sq, norm_ofReal_add_mul_I_sq,
    div_le_one (by positivity)]
  nlinarith

theorem bettinGonekSelectedRatio_rightLine_le
    {rho : ℂ} (hrho : IsNontrivialZero rho)
    {R : ℝ} (hR : 3 ≤ R) (v : ℝ) :
    ‖((R - 1 / 2 : ℝ) : ℂ) + v * Complex.I - 1‖ /
        ‖((R - 1 / 2 : ℝ) : ℂ) + v * Complex.I - rho‖ ≤
      1 + ‖rho - 1‖ := by
  let s : ℂ := (R - 1 / 2 : ℝ) + v * Complex.I
  have hrhoLt := nontrivial_zero_re_lt_one hrho
  have hden : 1 ≤ ‖s - rho‖ := by
    have hre := Complex.abs_re_le_norm (s - rho)
    have hreValue : (s - rho).re = R - 1 / 2 - rho.re := by
      norm_num [s, Complex.mul_re]
    rw [hreValue, abs_of_pos (by linarith)] at hre
    linarith
  have hdenPos : 0 < ‖s - rho‖ := zero_lt_one.trans_le hden
  have htriangle : ‖s - 1‖ ≤ ‖s - rho‖ + ‖rho - 1‖ := by
    rw [show s - 1 = (s - rho) + (rho - 1) by ring]
    exact norm_add_le _ _
  apply (div_le_iff₀ hdenPos).2
  calc
    ‖s - 1‖ ≤ ‖s - rho‖ + ‖rho - 1‖ := htriangle
    _ ≤ (1 + ‖rho - 1‖) * ‖s - rho‖ := by
      nlinarith [norm_nonneg (rho - 1)]

theorem norm_bettinGonekAuxiliaryG_rightLine_le
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ)
    {R : ℝ} (hR : 3 ≤ R) (y : ℝ) :
    ‖bettinGonekAuxiliaryG rho t (R + y * Complex.I)‖ ≤
      bettinGonekAuxiliaryRightDecayConstant rho *
        ((1 + |y + t|)⁻¹ ^ (3 : ℕ)) := by
  let v : ℝ := y + t
  let s : ℂ := (R - 1 / 2 : ℝ) + v * Complex.I
  have houter :=
    bettinGonekOuterRatio_rightLine_le_one (y := y) (by linarith : 0 ≤ R)
  have hratio :
      ‖s - 1‖ / ‖s - rho‖ ≤ 1 + ‖rho - 1‖ := by
    simpa only [s] using bettinGonekSelectedRatio_rightLine_le hrho hR v
  have hzeta :
      ‖riemannZeta s‖ ≤ bettinGonekZetaThreeHalvesBound := by
    have h := norm_riemannZeta_le_three_halves_majorant
      (show (3 / 2 : ℝ) ≤ R - 1 / 2 by linarith) v
    simpa only [s] using h
  have hlastLower :
      (16 + v ^ 2) ^ 2 ≤
        ‖((R + 1 : ℝ) : ℂ) + v * Complex.I‖ ^ 4 := by
    have hnorm :
        ‖((R + 1 : ℝ) : ℂ) + v * Complex.I‖ ^ 4 =
          (((R + 1) ^ 2 + v ^ 2) ^ 2) := by
      calc
        ‖((R + 1 : ℝ) : ℂ) + v * Complex.I‖ ^ 4 =
            (‖((R + 1 : ℝ) : ℂ) + v * Complex.I‖ ^ 2) ^ 2 := by ring
        _ = (((R + 1) ^ 2 + v ^ 2) ^ 2) := by
          rw [norm_ofReal_add_mul_I_sq]
    rw [hnorm]
    gcongr
    nlinarith
  have hlastPos : 0 <
      ‖((R + 1 : ℝ) : ℂ) + v * Complex.I‖ ^ 4 := by
    apply pow_pos
    rw [norm_pos_iff]
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have hsixteenPos : 0 < (16 + v ^ 2) ^ 2 := by positivity
  have hkernel :
      1 / ‖((R + 1 : ℝ) : ℂ) + v * Complex.I‖ ^ 4 ≤
        4 * ((1 + |v|)⁻¹ ^ (3 : ℕ)) := by
    exact
      (div_le_div_of_nonneg_left zero_le_one hsixteenPos hlastLower).trans
        (one_div_sixteen_add_sq_sq_le v)
  rw [norm_bettinGonekAuxiliaryG_rightLine_eq hrho t hR y]
  have hmain :
      (‖((R - 1 : ℝ) : ℂ) + y * Complex.I‖ ^ 2 /
          ‖((R + 1 : ℝ) : ℂ) + y * Complex.I‖ ^ 2) *
        (‖s - 1‖ / ‖s - rho‖) * ‖riemannZeta s‖ /
          ‖((R + 1 : ℝ) : ℂ) + v * Complex.I‖ ^ 4 ≤
        bettinGonekAuxiliaryRightDecayConstant rho *
          ((1 + |v|)⁻¹ ^ (3 : ℕ)) := by
    calc
      (‖((R - 1 : ℝ) : ℂ) + y * Complex.I‖ ^ 2 /
            ‖((R + 1 : ℝ) : ℂ) + y * Complex.I‖ ^ 2) *
          (‖s - 1‖ / ‖s - rho‖) * ‖riemannZeta s‖ /
            ‖((R + 1 : ℝ) : ℂ) + v * Complex.I‖ ^ 4
          ≤ 1 * (1 + ‖rho - 1‖) *
              bettinGonekZetaThreeHalvesBound *
              (1 / ‖((R + 1 : ℝ) : ℂ) + v * Complex.I‖ ^ 4) := by
            rw [div_eq_mul_inv, one_div]
            gcongr
      _ ≤ ((1 + ‖rho - 1‖) *
            bettinGonekZetaThreeHalvesBound) *
          (4 * ((1 + |v|)⁻¹ ^ (3 : ℕ))) := by
            simpa only [one_mul, mul_assoc] using
              mul_le_mul_of_nonneg_left hkernel
                (mul_nonneg
                  (by positivity : 0 ≤ 1 + ‖rho - 1‖)
                  bettinGonekZetaThreeHalvesBound_nonneg)
      _ = bettinGonekAuxiliaryRightDecayConstant rho *
          ((1 + |v|)⁻¹ ^ (3 : ℕ)) := by
            simp only [bettinGonekAuxiliaryRightDecayConstant]
            ring
  simpa only [s, v, Complex.ofReal_add] using hmain

theorem norm_bettinGonekInverseMellinIntegrand_fixedStrip_le
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ)
    {u : ℝ} (hu : 0 < u) (huOne : u ≤ 1)
    {a v : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 3) (hv : 1 ≤ |v|) :
    ‖bettinGonekInverseMellinIntegrand rho t u
        (a + (v - t) * Complex.I)‖ ≤
      (bettinGonekAuxiliaryStripLiftBound rho * u ^ (-3 : ℝ)) /
        |v| ^ 3 := by
  have hG := norm_bettinGonekAuxiliaryG_fixedStrip_le hrho t ha hv
  have hpowerNorm :
      ‖(u : ℂ) ^ (-(a + (v - t) * Complex.I))‖ = u ^ (-a : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hu]
    congr 1
    norm_num [Complex.mul_re]
  have hpower :
      u ^ (-a : ℝ) ≤ u ^ (-3 : ℝ) := by
    exact Real.rpow_le_rpow_of_exponent_ge hu huOne (by linarith [ha.2])
  rw [bettinGonekInverseMellinIntegrand, norm_mul, hpowerNorm]
  calc
    ‖bettinGonekAuxiliaryG rho t
          (a + (v - t) * Complex.I)‖ * u ^ (-a)
        ≤ (bettinGonekAuxiliaryStripLiftBound rho / |v| ^ 3) *
            u ^ (-3 : ℝ) := by
          exact mul_le_mul hG hpower (by positivity)
            (div_nonneg (bettinGonekAuxiliaryStripLiftBound_nonneg rho)
              (by positivity))
    _ = (bettinGonekAuxiliaryStripLiftBound rho * u ^ (-3 : ℝ)) /
          |v| ^ 3 := by ring

theorem norm_integral_bettinGonekInverseMellinIntegrand_horizontal_le
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ)
    {u : ℝ} (hu : 0 < u) (huOne : u ≤ 1)
    {v : ℝ} (hv : 1 ≤ |v|) :
    ‖∫ a : ℝ in 0..3,
        bettinGonekInverseMellinIntegrand rho t u
          (a + (v - t) * Complex.I)‖ ≤
      (3 * bettinGonekAuxiliaryStripLiftBound rho * u ^ (-3 : ℝ)) /
        |v| ^ 3 := by
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 3)
    (f := fun a : ℝ =>
      bettinGonekInverseMellinIntegrand rho t u
        (a + (v - t) * Complex.I))
    (C := (bettinGonekAuxiliaryStripLiftBound rho * u ^ (-3 : ℝ)) /
      |v| ^ 3)
    (fun a ha => by
      apply norm_bettinGonekInverseMellinIntegrand_fixedStrip_le
        hrho t hu huOne
      · norm_num at ha
        exact ⟨ha.1.le, ha.2⟩
      · exact hv)
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 - 0)] at hbound
  calc
    ‖∫ a : ℝ in 0..3,
        bettinGonekInverseMellinIntegrand rho t u
          (a + (v - t) * Complex.I)‖
        ≤ ((bettinGonekAuxiliaryStripLiftBound rho * u ^ (-3 : ℝ)) /
            |v| ^ 3) * (3 - 0) := hbound
    _ = (3 * bettinGonekAuxiliaryStripLiftBound rho * u ^ (-3 : ℝ)) /
          |v| ^ 3 := by ring

theorem
    tendsto_integral_bettinGonekInverseMellinIntegrand_horizontal_of_abs_atTop
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ)
    {u : ℝ} (hu : 0 < u) (huOne : u ≤ 1)
    {v : ℝ → ℝ} (hv : Tendsto (fun T => |v T|) atTop atTop) :
    Tendsto
      (fun T : ℝ => ∫ a : ℝ in 0..3,
        bettinGonekInverseMellinIntegrand rho t u
          (a + (v T - t) * Complex.I))
      atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hlarge : ∀ᶠ T : ℝ in atTop, 1 ≤ |v T| :=
    Filter.tendsto_atTop.1 hv 1
  have hbound : ∀ᶠ T : ℝ in atTop,
      ‖∫ a : ℝ in 0..3,
          bettinGonekInverseMellinIntegrand rho t u
            (a + (v T - t) * Complex.I)‖ ≤
        (3 * bettinGonekAuxiliaryStripLiftBound rho * u ^ (-3 : ℝ)) /
          |v T| ^ 3 := by
    filter_upwards [hlarge] with T hT
    exact
      norm_integral_bettinGonekInverseMellinIntegrand_horizontal_le
        hrho t hu huOne hT
  have hpow : Tendsto (fun T : ℝ => |v T| ^ 3) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp hv
  have hinv : Tendsto (fun T : ℝ => (|v T| ^ 3)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hpow
  have hmajor : Tendsto
      (fun T : ℝ =>
        (3 * bettinGonekAuxiliaryStripLiftBound rho * u ^ (-3 : ℝ)) /
          |v T| ^ 3)
      atTop (nhds 0) := by
    have hconst : Tendsto
        (fun _ : ℝ =>
          3 * bettinGonekAuxiliaryStripLiftBound rho * u ^ (-3 : ℝ))
        atTop
        (nhds
          (3 * bettinGonekAuxiliaryStripLiftBound rho * u ^ (-3 : ℝ))) :=
      tendsto_const_nhds
    simpa only [div_eq_mul_inv, mul_zero] using hconst.mul hinv
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound hmajor

theorem tendsto_integral_bettinGonekInverseMellinIntegrand_top_horizontal
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ)
    {u : ℝ} (hu : 0 < u) (huOne : u ≤ 1) :
    Tendsto
      (fun T : ℝ => ∫ a : ℝ in 0..3,
        bettinGonekInverseMellinIntegrand rho t u
          (a + T * Complex.I))
      atTop (nhds 0) := by
  have hv : Tendsto (fun T : ℝ => |T + t|) atTop atTop :=
    tendsto_abs_atTop_atTop.comp
      (tendsto_atTop_add_const_right atTop t tendsto_id)
  simpa only [Complex.ofReal_add, add_sub_cancel_right] using
    tendsto_integral_bettinGonekInverseMellinIntegrand_horizontal_of_abs_atTop
      hrho t hu huOne hv

theorem tendsto_integral_bettinGonekInverseMellinIntegrand_bottom_horizontal
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ)
    {u : ℝ} (hu : 0 < u) (huOne : u ≤ 1) :
    Tendsto
      (fun T : ℝ => ∫ a : ℝ in 0..3,
        bettinGonekInverseMellinIntegrand rho t u
          (a + (-T) * Complex.I))
      atTop (nhds 0) := by
  have hshift : Tendsto (fun T : ℝ => T - t) atTop atTop := by
    simpa only [id_eq, sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-t) tendsto_id
  have hv' : Tendsto (fun T : ℝ => |T - t|) atTop atTop := by
    change Tendsto (abs ∘ fun T : ℝ => T - t) atTop atTop
    exact tendsto_abs_atTop_atTop.comp hshift
  have hv : Tendsto (fun T : ℝ => |t - T|) atTop atTop := by
    simpa only [abs_sub_comm] using hv'
  simpa only [Complex.ofReal_sub, sub_sub_cancel_left] using
    tendsto_integral_bettinGonekInverseMellinIntegrand_horizontal_of_abs_atTop
      hrho t hu huOne hv

theorem continuous_bettinGonekAuxiliaryG_three_add_mul_I {rho : ℂ}
    (hrho : IsNontrivialZero rho) (t : ℝ) :
    Continuous (fun y : ℝ =>
      bettinGonekAuxiliaryG rho t (3 + y * Complex.I)) := by
  rw [continuous_iff_continuousAt]
  intro y
  have hopen : IsOpen bettinGonekAuxiliaryDomain := by
    exact isOpen_lt continuous_const Complex.continuous_re
  have hy : (3 : ℂ) + y * Complex.I ∈ bettinGonekAuxiliaryDomain := by
    norm_num [bettinGonekAuxiliaryDomain, Complex.mul_re]
  have hdiff :
      DifferentiableAt ℂ (bettinGonekAuxiliaryG rho t)
        ((3 : ℂ) + y * Complex.I) :=
    (differentiableOn_bettinGonekAuxiliaryG hrho t).differentiableAt
      (hopen.mem_nhds hy)
  have hline :
      ContinuousAt (fun u : ℝ => (3 : ℂ) + u * Complex.I) y := by
    fun_prop
  exact ContinuousAt.comp' hdiff.continuousAt hline

theorem integrable_bettinGonekAuxiliaryG_three_add_mul_I {rho : ℂ}
    (hrho : IsNontrivialZero rho) (t : ℝ) :
    Integrable (fun y : ℝ =>
      bettinGonekAuxiliaryG rho t (3 + y * Complex.I)) := by
  have hmajor :=
    (integrable_bettinGonekInverseCubeShift t).const_mul
      (bettinGonekAuxiliaryRightDecayConstant rho)
  apply hmajor.mono'
  · exact
      (continuous_bettinGonekAuxiliaryG_three_add_mul_I hrho t).aestronglyMeasurable
  · filter_upwards with y
    exact norm_bettinGonekAuxiliaryG_three_add_mul_I_le hrho t y

theorem norm_bettinGonekInverseMellinPower
    {u : ℝ} (hu : 0 < u) (sigma y : ℝ) :
    ‖(u : ℂ) ^ (-(sigma + y * Complex.I))‖ = u ^ (-sigma : ℝ) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hu]
  congr 1
  simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, mul_zero, zero_mul,
    sub_zero, add_zero]

theorem continuous_bettinGonekInverseMellinPower
    {u : ℝ} (hu : 0 < u) (sigma : ℝ) :
    Continuous (fun y : ℝ => (u : ℂ) ^ (-(sigma + y * Complex.I))) := by
  have hbase : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  exact
    (by fun_prop : Continuous (fun y : ℝ => -(sigma + y * Complex.I))).const_cpow
      (Or.inl hbase)

theorem integrable_bettinGonekInverseMellinIntegrand_zero
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ)
    {u : ℝ} (hu : 0 < u) :
    Integrable (fun y : ℝ =>
      bettinGonekAuxiliaryG rho t (y * Complex.I) *
        (u : ℂ) ^ (-(y * Complex.I))) := by
  have hcontinuous : Continuous (fun y : ℝ =>
      bettinGonekAuxiliaryG rho t (y * Complex.I) *
        (u : ℂ) ^ (-(y * Complex.I))) :=
    (continuous_bettinGonekAuxiliaryG_mul_I hrho t).mul
      (by simpa using continuous_bettinGonekInverseMellinPower hu 0)
  apply (integrable_bettinGonekAuxiliaryG_mul_I hrho t).norm.mono'
  · exact hcontinuous.aestronglyMeasurable
  · filter_upwards with y
    have hpower : ‖(u : ℂ) ^ (-(y * Complex.I))‖ = 1 := by
      simpa using norm_bettinGonekInverseMellinPower hu 0 y
    rw [norm_mul, hpower]
    norm_num

theorem integrable_bettinGonekInverseMellinIntegrand_three
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ)
    {u : ℝ} (hu : 0 < u) :
    Integrable (fun y : ℝ =>
      bettinGonekAuxiliaryG rho t (3 + y * Complex.I) *
        (u : ℂ) ^ (-(3 + y * Complex.I))) := by
  have hcontinuous : Continuous (fun y : ℝ =>
      bettinGonekAuxiliaryG rho t (3 + y * Complex.I) *
        (u : ℂ) ^ (-(3 + y * Complex.I))) :=
    (continuous_bettinGonekAuxiliaryG_three_add_mul_I hrho t).mul
      (continuous_bettinGonekInverseMellinPower hu 3)
  have hmajor :=
    (integrable_bettinGonekAuxiliaryG_three_add_mul_I hrho t).norm.const_mul
      (u ^ (-3 : ℝ))
  apply hmajor.mono'
  · exact hcontinuous.aestronglyMeasurable
  · filter_upwards with y
    have hpower :
        ‖(u : ℂ) ^ (-(3 + y * Complex.I))‖ = u ^ (-3 : ℝ) := by
      simpa using norm_bettinGonekInverseMellinPower hu 3 y
    rw [norm_mul, hpower]
    rw [mul_comm]

theorem integrable_bettinGonekInverseMellinIntegrand_zero'
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ)
    {u : ℝ} (hu : 0 < u) :
    Integrable (fun y : ℝ =>
      bettinGonekInverseMellinIntegrand rho t u (y * Complex.I)) := by
  simpa only [bettinGonekInverseMellinIntegrand] using
    integrable_bettinGonekInverseMellinIntegrand_zero hrho t hu

theorem integrable_bettinGonekInverseMellinIntegrand_three'
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ)
    {u : ℝ} (hu : 0 < u) :
    Integrable (fun y : ℝ =>
      bettinGonekInverseMellinIntegrand rho t u
        (3 + y * Complex.I)) := by
  simpa only [bettinGonekInverseMellinIntegrand] using
    integrable_bettinGonekInverseMellinIntegrand_three hrho t hu

theorem differentiableOn_bettinGonekInverseMellinIntegrand
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ)
    {u : ℝ} (hu : 0 < u) :
    DifferentiableOn ℂ (bettinGonekInverseMellinIntegrand rho t u)
      bettinGonekAuxiliaryDomain := by
  have hbase : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  have hpower : Differentiable ℂ (fun w : ℂ => (u : ℂ) ^ (-w)) :=
    differentiable_id.neg.const_cpow (Or.inl hbase)
  exact
    (differentiableOn_bettinGonekAuxiliaryG hrho t).mul
      hpower.differentiableOn

theorem bettinGonekInverseMellinIntegrand_rectangleBoundaryIntegral
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ)
    {u : ℝ} (hu : 0 < u) (T : ℝ) :
    rectangleBoundaryIntegral
        (bettinGonekInverseMellinIntegrand rho t u) 0 3 (-T) T = 0 := by
  have hrect : [[(0 : ℝ), 3]] ×ℂ [[-T, T]] ⊆
      bettinGonekAuxiliaryDomain := by
    intro w hw
    rw [Complex.mem_reProdIm] at hw
    change -1 < w.re
    have hwRe : 0 ≤ w.re := by
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3)] at hw
      exact hw.1.1
    linarith
  exact rectangleBoundaryIntegral_eq_zero_of_differentiableOn
    ((differentiableOn_bettinGonekInverseMellinIntegrand hrho t hu).mono hrect)

theorem bettinGonekInverseMellinIntegrand_vertical_eq_left_add_horizontals
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ)
    {u : ℝ} (hu : 0 < u) (T : ℝ) :
    (∫ y : ℝ in -T..T,
        bettinGonekInverseMellinIntegrand rho t u
          (3 + y * Complex.I)) =
      (∫ y : ℝ in -T..T,
        bettinGonekInverseMellinIntegrand rho t u
          (y * Complex.I)) +
        Complex.I *
          ((∫ a : ℝ in 0..3,
              bettinGonekInverseMellinIntegrand rho t u
                (a + (-T) * Complex.I)) -
            ∫ a : ℝ in 0..3,
              bettinGonekInverseMellinIntegrand rho t u
                (a + T * Complex.I)) := by
  have hboundary :=
    bettinGonekInverseMellinIntegrand_rectangleBoundaryIntegral hrho t hu T
  rw [rectangleBoundaryIntegral] at hboundary
  simp only [Complex.ofReal_zero, zero_add, Complex.ofReal_neg] at hboundary
  apply mul_left_cancel₀ Complex.I_ne_zero
  rw [mul_add]
  simp only [← mul_assoc, Complex.I_mul_I, neg_one_mul]
  linear_combination hboundary

theorem integral_bettinGonekInverseMellinIntegrand_three_eq_zero
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ)
    {u : ℝ} (hu : 0 < u) (huOne : u ≤ 1) :
    (∫ y : ℝ,
        bettinGonekInverseMellinIntegrand rho t u
          (3 + y * Complex.I)) =
      ∫ y : ℝ,
        bettinGonekInverseMellinIntegrand rho t u
          (y * Complex.I) := by
  have hright := intervalIntegral_tendsto_integral
    (integrable_bettinGonekInverseMellinIntegrand_three' hrho t hu)
    tendsto_neg_atTop_atBot tendsto_id
  have hleft := intervalIntegral_tendsto_integral
    (integrable_bettinGonekInverseMellinIntegrand_zero' hrho t hu)
    tendsto_neg_atTop_atBot tendsto_id
  have hright' : Tendsto
      (fun T : ℝ => ∫ y : ℝ in -T..T,
        bettinGonekInverseMellinIntegrand rho t u
          (3 + y * Complex.I))
      atTop
      (nhds (∫ y : ℝ,
        bettinGonekInverseMellinIntegrand rho t u
          (3 + y * Complex.I))) := by
    simpa only [Function.comp_apply, id_eq] using hright
  have hleft' : Tendsto
      (fun T : ℝ => ∫ y : ℝ in -T..T,
        bettinGonekInverseMellinIntegrand rho t u
          (y * Complex.I))
      atTop
      (nhds (∫ y : ℝ,
        bettinGonekInverseMellinIntegrand rho t u
          (y * Complex.I))) := by
    simpa only [Function.comp_apply, id_eq] using hleft
  have hbottom :=
    tendsto_integral_bettinGonekInverseMellinIntegrand_bottom_horizontal
      hrho t hu huOne
  have htop :=
    tendsto_integral_bettinGonekInverseMellinIntegrand_top_horizontal
      hrho t hu huOne
  have hhoriz : Tendsto
      (fun T : ℝ => Complex.I *
        ((∫ a : ℝ in 0..3,
            bettinGonekInverseMellinIntegrand rho t u
              (a + (-T) * Complex.I)) -
          ∫ a : ℝ in 0..3,
            bettinGonekInverseMellinIntegrand rho t u
              (a + T * Complex.I)))
      atTop (nhds 0) := by
    simpa only [sub_zero, mul_zero] using
      (tendsto_const_nhds.mul (hbottom.sub htop) : Tendsto
        (fun T : ℝ => Complex.I *
          ((∫ a : ℝ in 0..3,
              bettinGonekInverseMellinIntegrand rho t u
                (a + (-T) * Complex.I)) -
            ∫ a : ℝ in 0..3,
              bettinGonekInverseMellinIntegrand rho t u
                (a + T * Complex.I)))
        atTop (nhds (Complex.I * (0 - 0))))
  have hrightLimit : Tendsto
      (fun T : ℝ =>
        (∫ y : ℝ in -T..T,
          bettinGonekInverseMellinIntegrand rho t u
            (y * Complex.I)) +
          Complex.I *
            ((∫ a : ℝ in 0..3,
                bettinGonekInverseMellinIntegrand rho t u
                  (a + (-T) * Complex.I)) -
              ∫ a : ℝ in 0..3,
                bettinGonekInverseMellinIntegrand rho t u
                  (a + T * Complex.I)))
      atTop
      (nhds ((∫ y : ℝ,
        bettinGonekInverseMellinIntegrand rho t u
          (y * Complex.I)) + 0)) :=
    hleft'.add hhoriz
  have hfinite : ∀ᶠ T : ℝ in atTop,
      (∫ y : ℝ in -T..T,
        bettinGonekInverseMellinIntegrand rho t u
          (3 + y * Complex.I)) =
        (∫ y : ℝ in -T..T,
          bettinGonekInverseMellinIntegrand rho t u
            (y * Complex.I)) +
          Complex.I *
            ((∫ a : ℝ in 0..3,
                bettinGonekInverseMellinIntegrand rho t u
                  (a + (-T) * Complex.I)) -
              ∫ a : ℝ in 0..3,
                bettinGonekInverseMellinIntegrand rho t u
                  (a + T * Complex.I)) :=
    Eventually.of_forall fun T =>
      bettinGonekInverseMellinIntegrand_vertical_eq_left_add_horizontals
        hrho t hu T
  have hfiniteSymm := hfinite.mono fun _ h => h.symm
  have hlimits :=
    tendsto_nhds_unique hright' (hrightLimit.congr' hfiniteSymm)
  simpa only [add_zero] using hlimits

theorem bettinGonekInverseMellinLineIntegral_three_eq_zero
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ)
    {u : ℝ} (hu : 0 < u) (huOne : u ≤ 1) :
    bettinGonekInverseMellinLineIntegral rho t u 3 =
      bettinGonekInverseMellinLineIntegral rho t u 0 := by
  have hraw :=
    integral_bettinGonekInverseMellinIntegrand_three_eq_zero
      hrho t hu huOne
  rw [bettinGonekInverseMellinLineIntegral,
    bettinGonekInverseMellinLineIntegral]
  simp only [Complex.ofReal_zero, zero_add]
  congr 1

/-- An explicit `u`-independent majorant for the inverse Mellin kernel on `0 < u ≤ 1`. -/
def bettinGonekInverseMellinBound (rho : ℂ) (t : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    ∫ y : ℝ, bettinGonekAuxiliaryDecayConstant rho *
      ((1 + |y + t|)⁻¹ ^ (3 : ℕ))

theorem bettinGonekInverseMellinBound_nonneg (rho : ℂ) (t : ℝ) :
    0 ≤ bettinGonekInverseMellinBound rho t := by
  apply mul_nonneg
  · positivity
  · exact integral_nonneg fun _ =>
      mul_nonneg (bettinGonekAuxiliaryDecayConstant_nonneg rho) (by positivity)

theorem norm_bettinGonekInverseMellinLineIntegral_zero_le
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ)
    {u : ℝ} (hu : 0 < u) :
    ‖bettinGonekInverseMellinLineIntegral rho t u 0‖ ≤
      bettinGonekInverseMellinBound rho t := by
  let g : ℝ → ℝ := fun y =>
    bettinGonekAuxiliaryDecayConstant rho *
      ((1 + |y + t|)⁻¹ ^ (3 : ℕ))
  have hg : Integrable g :=
    (integrable_bettinGonekInverseCubeShift t).const_mul
      (bettinGonekAuxiliaryDecayConstant rho)
  have hpoint : ∀ y : ℝ,
      ‖bettinGonekInverseMellinIntegrand rho t u
          (y * Complex.I)‖ ≤ g y := by
    intro y
    rw [bettinGonekInverseMellinIntegrand, norm_mul]
    have hpower :
        ‖(u : ℂ) ^ (-(y * Complex.I))‖ = 1 := by
      simpa using norm_bettinGonekInverseMellinPower hu 0 y
    rw [hpower, mul_one]
    exact norm_bettinGonekAuxiliaryG_mul_I_le hrho t y
  have hintegral :
      ‖∫ y : ℝ,
          bettinGonekInverseMellinIntegrand rho t u
            (y * Complex.I)‖ ≤
        ∫ y : ℝ, g y :=
    MeasureTheory.norm_integral_le_of_norm_le hg (ae_of_all _ hpoint)
  rw [bettinGonekInverseMellinLineIntegral]
  simp only [Complex.ofReal_zero, zero_add]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
  exact mul_le_mul_of_nonneg_left hintegral (by positivity)

theorem norm_bettinGonekInverseMellinKernel_le
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ)
    {u : ℝ} (hu : 0 < u) (huOne : u ≤ 1) :
    ‖bettinGonekInverseMellinKernel rho t u‖ ≤
      bettinGonekInverseMellinBound rho t := by
  rw [bettinGonekInverseMellinKernel,
    bettinGonekInverseMellinLineIntegral_three_eq_zero hrho t hu huOne]
  exact norm_bettinGonekInverseMellinLineIntegral_zero_le hrho t hu

theorem continuous_bettinGonekAuxiliaryG_rightLine
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ)
    {R : ℝ} (hR : 3 ≤ R) :
    Continuous (fun y : ℝ =>
      bettinGonekAuxiliaryG rho t (R + y * Complex.I)) := by
  rw [continuous_iff_continuousAt]
  intro y
  have hopen : IsOpen bettinGonekAuxiliaryDomain := by
    exact isOpen_lt continuous_const Complex.continuous_re
  have hy : (R : ℂ) + y * Complex.I ∈ bettinGonekAuxiliaryDomain := by
    change -1 < ((R : ℂ) + y * Complex.I).re
    norm_num [Complex.mul_re]
    linarith
  have hdiff :
      DifferentiableAt ℂ (bettinGonekAuxiliaryG rho t)
        ((R : ℂ) + y * Complex.I) :=
    (differentiableOn_bettinGonekAuxiliaryG hrho t).differentiableAt
      (hopen.mem_nhds hy)
  have hline :
      ContinuousAt (fun q : ℝ => (R : ℂ) + q * Complex.I) y := by
    fun_prop
  exact ContinuousAt.comp' hdiff.continuousAt hline

theorem integrable_bettinGonekAuxiliaryG_rightLine
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ)
    {R : ℝ} (hR : 3 ≤ R) :
    Integrable (fun y : ℝ =>
      bettinGonekAuxiliaryG rho t (R + y * Complex.I)) := by
  have hmajor :=
    (integrable_bettinGonekInverseCubeShift t).const_mul
      (bettinGonekAuxiliaryRightDecayConstant rho)
  apply hmajor.mono'
  · exact
      (continuous_bettinGonekAuxiliaryG_rightLine hrho t hR).aestronglyMeasurable
  · filter_upwards with y
    exact norm_bettinGonekAuxiliaryG_rightLine_le hrho t hR y

theorem integrable_bettinGonekInverseMellinIntegrand_rightLine
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ)
    {u : ℝ} (hu : 0 < u) {R : ℝ} (hR : 3 ≤ R) :
    Integrable (fun y : ℝ =>
      bettinGonekInverseMellinIntegrand rho t u
        (R + y * Complex.I)) := by
  have hcontinuous : Continuous (fun y : ℝ =>
      bettinGonekInverseMellinIntegrand rho t u
        (R + y * Complex.I)) := by
    apply (continuous_bettinGonekAuxiliaryG_rightLine hrho t hR).mul
    simpa only [bettinGonekInverseMellinIntegrand] using
      continuous_bettinGonekInverseMellinPower hu R
  have hmajor :=
    (integrable_bettinGonekAuxiliaryG_rightLine hrho t hR).norm.const_mul
      (u ^ (-R : ℝ))
  apply hmajor.mono'
  · exact hcontinuous.aestronglyMeasurable
  · filter_upwards with y
    rw [bettinGonekInverseMellinIntegrand, norm_mul]
    have hpower :
        ‖(u : ℂ) ^ (-(R + y * Complex.I))‖ = u ^ (-R : ℝ) := by
      simpa using norm_bettinGonekInverseMellinPower hu R y
    rw [hpower, mul_comm]

theorem norm_bettinGonekInverseMellinLineIntegral_rightLine_le
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ)
    {u : ℝ} (hu : 0 < u) {R : ℝ} (hR : 3 ≤ R) :
    ‖bettinGonekInverseMellinLineIntegral rho t u R‖ ≤
      (1 / (2 * Real.pi)) *
        (∫ y : ℝ, bettinGonekAuxiliaryRightDecayConstant rho *
          ((1 + |y + t|)⁻¹ ^ (3 : ℕ))) *
        u ^ (-R : ℝ) := by
  let g : ℝ → ℝ := fun y =>
    bettinGonekAuxiliaryRightDecayConstant rho *
      ((1 + |y + t|)⁻¹ ^ (3 : ℕ)) * u ^ (-R : ℝ)
  have hg : Integrable g :=
    ((integrable_bettinGonekInverseCubeShift t).const_mul
      (bettinGonekAuxiliaryRightDecayConstant rho)).mul_const
        (u ^ (-R : ℝ))
  have hpoint : ∀ y : ℝ,
      ‖bettinGonekInverseMellinIntegrand rho t u
          (R + y * Complex.I)‖ ≤ g y := by
    intro y
    rw [bettinGonekInverseMellinIntegrand, norm_mul]
    have hpower :
        ‖(u : ℂ) ^ (-(R + y * Complex.I))‖ = u ^ (-R : ℝ) := by
      simpa using norm_bettinGonekInverseMellinPower hu R y
    rw [hpower]
    exact mul_le_mul_of_nonneg_right
      (norm_bettinGonekAuxiliaryG_rightLine_le hrho t hR y) (by positivity)
  have hintegral :
      ‖∫ y : ℝ,
          bettinGonekInverseMellinIntegrand rho t u
            (R + y * Complex.I)‖ ≤
        ∫ y : ℝ, g y :=
    MeasureTheory.norm_integral_le_of_norm_le hg (ae_of_all _ hpoint)
  have hfactor :
      (∫ y : ℝ, g y) =
        (∫ y : ℝ, bettinGonekAuxiliaryRightDecayConstant rho *
          ((1 + |y + t|)⁻¹ ^ (3 : ℕ))) * u ^ (-R : ℝ) := by
    rw [integral_mul_const]
  rw [bettinGonekInverseMellinLineIntegral, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
  calc
    (1 / (2 * Real.pi)) *
          ‖∫ y : ℝ,
            bettinGonekInverseMellinIntegrand rho t u
              (R + y * Complex.I)‖
        ≤ (1 / (2 * Real.pi)) * ∫ y : ℝ, g y :=
      mul_le_mul_of_nonneg_left hintegral (by positivity)
    _ = (1 / (2 * Real.pi)) *
          (∫ y : ℝ, bettinGonekAuxiliaryRightDecayConstant rho *
            ((1 + |y + t|)⁻¹ ^ (3 : ℕ))) *
          u ^ (-R : ℝ) := by
            rw [hfactor]
            ring

theorem tendsto_bettinGonekInverseMellinLineIntegral_rightLine
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ)
    {u : ℝ} (hu : 1 < u) :
    Tendsto
      (fun R : ℝ => bettinGonekInverseMellinLineIntegral rho t u R)
      atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have huPos : 0 < u := zero_lt_one.trans hu
  have hbound : ∀ᶠ R : ℝ in atTop,
      ‖bettinGonekInverseMellinLineIntegral rho t u R‖ ≤
        (1 / (2 * Real.pi)) *
          (∫ y : ℝ, bettinGonekAuxiliaryRightDecayConstant rho *
            ((1 + |y + t|)⁻¹ ^ (3 : ℕ))) *
          u ^ (-R : ℝ) := by
    filter_upwards [eventually_ge_atTop (3 : ℝ)] with R hR
    exact
      norm_bettinGonekInverseMellinLineIntegral_rightLine_le
        hrho t huPos hR
  have hpow : Tendsto (fun R : ℝ => u ^ (-R : ℝ)) atTop (nhds 0) := by
    exact (tendsto_rpow_atBot_of_base_gt_one u hu).comp tendsto_neg_atTop_atBot
  have hmajor : Tendsto
      (fun R : ℝ =>
        (1 / (2 * Real.pi)) *
          (∫ y : ℝ, bettinGonekAuxiliaryRightDecayConstant rho *
            ((1 + |y + t|)⁻¹ ^ (3 : ℕ))) *
          u ^ (-R : ℝ))
      atTop (nhds 0) := by
    have hconst : Tendsto
        (fun _ : ℝ =>
          (1 / (2 * Real.pi)) *
            (∫ y : ℝ, bettinGonekAuxiliaryRightDecayConstant rho *
              ((1 + |y + t|)⁻¹ ^ (3 : ℕ))))
        atTop
        (nhds ((1 / (2 * Real.pi)) *
          (∫ y : ℝ, bettinGonekAuxiliaryRightDecayConstant rho *
            ((1 + |y + t|)⁻¹ ^ (3 : ℕ))))) :=
      tendsto_const_nhds
    have h := hconst.mul hpow
    rw [mul_zero] at h
    exact h
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound hmajor

theorem norm_bettinGonekInverseMellinIntegrand_rightStrip_le
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ)
    {u : ℝ} (hu : 1 ≤ u) {R a v : ℝ}
    (ha : a ∈ Set.Icc (3 : ℝ) R) :
    ‖bettinGonekInverseMellinIntegrand rho t u
        (a + (v - t) * Complex.I)‖ ≤
      bettinGonekAuxiliaryRightDecayConstant rho *
        ((1 + |v|)⁻¹ ^ (3 : ℕ)) * u ^ (-3 : ℝ) := by
  have huPos : 0 < u := zero_lt_one.trans_le hu
  have hG :
      ‖bettinGonekAuxiliaryG rho t
          (a + (v - t) * Complex.I)‖ ≤
        bettinGonekAuxiliaryRightDecayConstant rho *
          ((1 + |v|)⁻¹ ^ (3 : ℕ)) := by
    simpa only [Complex.ofReal_sub, sub_add_cancel] using
      norm_bettinGonekAuxiliaryG_rightLine_le hrho t ha.1 (v - t)
  have hpowerNorm :
      ‖(u : ℂ) ^ (-(a + (v - t) * Complex.I))‖ = u ^ (-a : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos huPos]
    congr 1
    norm_num [Complex.mul_re]
  have hpower :
      u ^ (-a : ℝ) ≤ u ^ (-3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hu (by linarith [ha.1])
  rw [bettinGonekInverseMellinIntegrand, norm_mul, hpowerNorm]
  exact mul_le_mul hG hpower (by positivity)
    (mul_nonneg (bettinGonekAuxiliaryRightDecayConstant_nonneg rho)
      (by positivity))

theorem norm_integral_bettinGonekInverseMellinIntegrand_rightHorizontal_le
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ)
    {u : ℝ} (hu : 1 ≤ u) {R v : ℝ} (hR : 3 ≤ R) :
    ‖∫ a : ℝ in 3..R,
        bettinGonekInverseMellinIntegrand rho t u
          (a + (v - t) * Complex.I)‖ ≤
      (R - 3) *
        (bettinGonekAuxiliaryRightDecayConstant rho *
          ((1 + |v|)⁻¹ ^ (3 : ℕ)) * u ^ (-3 : ℝ)) := by
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (3 : ℝ)) (b := R)
    (f := fun a : ℝ =>
      bettinGonekInverseMellinIntegrand rho t u
        (a + (v - t) * Complex.I))
    (C := bettinGonekAuxiliaryRightDecayConstant rho *
      ((1 + |v|)⁻¹ ^ (3 : ℕ)) * u ^ (-3 : ℝ))
    (fun a ha => by
      exact norm_bettinGonekInverseMellinIntegrand_rightStrip_le
        hrho t hu (by
          have ha' := Set.uIoc_subset_uIcc ha
          rw [uIcc_of_le hR] at ha'
          exact ha'))
  rw [abs_of_nonneg (sub_nonneg.mpr hR)] at hbound
  nlinarith

theorem
    tendsto_integral_bettinGonekInverseMellinIntegrand_rightHorizontal_of_abs_atTop
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ)
    {u : ℝ} (hu : 1 ≤ u) {R : ℝ} (hR : 3 ≤ R)
    {v : ℝ → ℝ} (hv : Tendsto (fun T => |v T|) atTop atTop) :
    Tendsto
      (fun T : ℝ => ∫ a : ℝ in 3..R,
        bettinGonekInverseMellinIntegrand rho t u
          (a + (v T - t) * Complex.I))
      atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hadd : Tendsto (fun T : ℝ => 1 + |v T|) atTop atTop :=
    tendsto_atTop_add_const_left atTop 1 hv
  have hinv : Tendsto (fun T : ℝ => (1 + |v T|)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hadd
  have hcube :
      Tendsto (fun T : ℝ => (1 + |v T|)⁻¹ ^ (3 : ℕ))
        atTop (nhds 0) := by
    simpa only [zero_pow (by norm_num : (3 : ℕ) ≠ 0)] using hinv.pow 3
  have hbound : ∀ᶠ T : ℝ in atTop,
      ‖∫ a : ℝ in 3..R,
          bettinGonekInverseMellinIntegrand rho t u
            (a + (v T - t) * Complex.I)‖ ≤
        (R - 3) *
          (bettinGonekAuxiliaryRightDecayConstant rho *
            ((1 + |v T|)⁻¹ ^ (3 : ℕ)) * u ^ (-3 : ℝ)) :=
    Eventually.of_forall fun T =>
      norm_integral_bettinGonekInverseMellinIntegrand_rightHorizontal_le
        hrho t hu hR
  have hmajor : Tendsto
      (fun T : ℝ =>
        (R - 3) *
          (bettinGonekAuxiliaryRightDecayConstant rho *
            ((1 + |v T|)⁻¹ ^ (3 : ℕ)) * u ^ (-3 : ℝ)))
      atTop (nhds 0) := by
    have hconst : Tendsto
        (fun _ : ℝ =>
          (R - 3) * bettinGonekAuxiliaryRightDecayConstant rho)
        atTop
        (nhds ((R - 3) * bettinGonekAuxiliaryRightDecayConstant rho)) :=
      tendsto_const_nhds
    have hright : Tendsto
        (fun _ : ℝ => u ^ (-3 : ℝ)) atTop (nhds (u ^ (-3 : ℝ))) :=
      tendsto_const_nhds
    simpa only [mul_zero, zero_mul, mul_assoc] using
      (hconst.mul hcube).mul hright
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound hmajor

theorem tendsto_integral_bettinGonekInverseMellinIntegrand_rightTop
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ)
    {u : ℝ} (hu : 1 ≤ u) {R : ℝ} (hR : 3 ≤ R) :
    Tendsto
      (fun T : ℝ => ∫ a : ℝ in 3..R,
        bettinGonekInverseMellinIntegrand rho t u
          (a + T * Complex.I))
      atTop (nhds 0) := by
  have hv : Tendsto (fun T : ℝ => |T + t|) atTop atTop :=
    tendsto_abs_atTop_atTop.comp
      (tendsto_atTop_add_const_right atTop t tendsto_id)
  simpa only [Complex.ofReal_add, add_sub_cancel_right] using
    tendsto_integral_bettinGonekInverseMellinIntegrand_rightHorizontal_of_abs_atTop
      hrho t hu hR hv

theorem tendsto_integral_bettinGonekInverseMellinIntegrand_rightBottom
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ)
    {u : ℝ} (hu : 1 ≤ u) {R : ℝ} (hR : 3 ≤ R) :
    Tendsto
      (fun T : ℝ => ∫ a : ℝ in 3..R,
        bettinGonekInverseMellinIntegrand rho t u
          (a + (-T) * Complex.I))
      atTop (nhds 0) := by
  have hshift : Tendsto (fun T : ℝ => T - t) atTop atTop := by
    simpa only [id_eq, sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-t) tendsto_id
  have hv' : Tendsto (fun T : ℝ => |T - t|) atTop atTop :=
    tendsto_abs_atTop_atTop.comp hshift
  have hv : Tendsto (fun T : ℝ => |t - T|) atTop atTop := by
    simpa only [abs_sub_comm] using hv'
  simpa only [Complex.ofReal_sub, sub_sub_cancel_left] using
    tendsto_integral_bettinGonekInverseMellinIntegrand_rightHorizontal_of_abs_atTop
      hrho t hu hR hv

theorem
    bettinGonekInverseMellinIntegrand_rightRectangleBoundaryIntegral
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ)
    {u : ℝ} (hu : 0 < u) {R : ℝ} (hR : 3 ≤ R) (T : ℝ) :
    rectangleBoundaryIntegral
        (bettinGonekInverseMellinIntegrand rho t u) 3 R (-T) T = 0 := by
  have hrect : [[(3 : ℝ), R]] ×ℂ [[-T, T]] ⊆
      bettinGonekAuxiliaryDomain := by
    intro w hw
    rw [Complex.mem_reProdIm] at hw
    change -1 < w.re
    have hwRe : 3 ≤ w.re := by
      rw [uIcc_of_le hR] at hw
      exact hw.1.1
    linarith
  exact rectangleBoundaryIntegral_eq_zero_of_differentiableOn
    ((differentiableOn_bettinGonekInverseMellinIntegrand hrho t hu).mono hrect)

theorem
    bettinGonekInverseMellinIntegrand_rightVertical_eq_left_add_horizontals
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ)
    {u : ℝ} (hu : 0 < u) {R : ℝ} (hR : 3 ≤ R) (T : ℝ) :
    (∫ y : ℝ in -T..T,
        bettinGonekInverseMellinIntegrand rho t u
          (R + y * Complex.I)) =
      (∫ y : ℝ in -T..T,
        bettinGonekInverseMellinIntegrand rho t u
          (3 + y * Complex.I)) +
        Complex.I *
          ((∫ a : ℝ in 3..R,
              bettinGonekInverseMellinIntegrand rho t u
                (a + (-T) * Complex.I)) -
            ∫ a : ℝ in 3..R,
              bettinGonekInverseMellinIntegrand rho t u
                (a + T * Complex.I)) := by
  have hboundary :=
    bettinGonekInverseMellinIntegrand_rightRectangleBoundaryIntegral
      hrho t hu hR T
  rw [rectangleBoundaryIntegral] at hboundary
  simp only [Complex.ofReal_neg] at hboundary
  apply mul_left_cancel₀ Complex.I_ne_zero
  rw [mul_add]
  simp only [← mul_assoc, Complex.I_mul_I, neg_one_mul]
  linear_combination hboundary

theorem integral_bettinGonekInverseMellinIntegrand_three_eq_right
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ)
    {u : ℝ} (hu : 1 ≤ u) {R : ℝ} (hR : 3 ≤ R) :
    (∫ y : ℝ,
        bettinGonekInverseMellinIntegrand rho t u
          (3 + y * Complex.I)) =
      ∫ y : ℝ,
        bettinGonekInverseMellinIntegrand rho t u
          (R + y * Complex.I) := by
  have huPos : 0 < u := zero_lt_one.trans_le hu
  have hright := intervalIntegral_tendsto_integral
    (integrable_bettinGonekInverseMellinIntegrand_rightLine
      hrho t huPos hR)
    tendsto_neg_atTop_atBot tendsto_id
  have hleft := intervalIntegral_tendsto_integral
    (integrable_bettinGonekInverseMellinIntegrand_three' hrho t huPos)
    tendsto_neg_atTop_atBot tendsto_id
  have hright' : Tendsto
      (fun T : ℝ => ∫ y : ℝ in -T..T,
        bettinGonekInverseMellinIntegrand rho t u
          (R + y * Complex.I))
      atTop
      (nhds (∫ y : ℝ,
        bettinGonekInverseMellinIntegrand rho t u
          (R + y * Complex.I))) := by
    simpa only [Function.comp_apply, id_eq] using hright
  have hleft' : Tendsto
      (fun T : ℝ => ∫ y : ℝ in -T..T,
        bettinGonekInverseMellinIntegrand rho t u
          (3 + y * Complex.I))
      atTop
      (nhds (∫ y : ℝ,
        bettinGonekInverseMellinIntegrand rho t u
          (3 + y * Complex.I))) := by
    simpa only [Function.comp_apply, id_eq] using hleft
  have hbottom :=
    tendsto_integral_bettinGonekInverseMellinIntegrand_rightBottom
      hrho t hu hR
  have htop :=
    tendsto_integral_bettinGonekInverseMellinIntegrand_rightTop
      hrho t hu hR
  have hhoriz : Tendsto
      (fun T : ℝ => Complex.I *
        ((∫ a : ℝ in 3..R,
            bettinGonekInverseMellinIntegrand rho t u
              (a + (-T) * Complex.I)) -
          ∫ a : ℝ in 3..R,
            bettinGonekInverseMellinIntegrand rho t u
              (a + T * Complex.I)))
      atTop (nhds 0) := by
    simpa only [sub_zero, mul_zero] using
      (tendsto_const_nhds.mul (hbottom.sub htop) : Tendsto
        (fun T : ℝ => Complex.I *
          ((∫ a : ℝ in 3..R,
              bettinGonekInverseMellinIntegrand rho t u
                (a + (-T) * Complex.I)) -
            ∫ a : ℝ in 3..R,
              bettinGonekInverseMellinIntegrand rho t u
                (a + T * Complex.I)))
        atTop (nhds (Complex.I * (0 - 0))))
  have hleftLimit : Tendsto
      (fun T : ℝ =>
        (∫ y : ℝ in -T..T,
          bettinGonekInverseMellinIntegrand rho t u
            (3 + y * Complex.I)) +
          Complex.I *
            ((∫ a : ℝ in 3..R,
                bettinGonekInverseMellinIntegrand rho t u
                  (a + (-T) * Complex.I)) -
              ∫ a : ℝ in 3..R,
                bettinGonekInverseMellinIntegrand rho t u
                  (a + T * Complex.I)))
      atTop
      (nhds ((∫ y : ℝ,
        bettinGonekInverseMellinIntegrand rho t u
          (3 + y * Complex.I)) + 0)) :=
    hleft'.add hhoriz
  have hfinite : ∀ᶠ T : ℝ in atTop,
      (∫ y : ℝ in -T..T,
        bettinGonekInverseMellinIntegrand rho t u
          (R + y * Complex.I)) =
        (∫ y : ℝ in -T..T,
          bettinGonekInverseMellinIntegrand rho t u
            (3 + y * Complex.I)) +
          Complex.I *
            ((∫ a : ℝ in 3..R,
                bettinGonekInverseMellinIntegrand rho t u
                  (a + (-T) * Complex.I)) -
              ∫ a : ℝ in 3..R,
                bettinGonekInverseMellinIntegrand rho t u
                  (a + T * Complex.I)) :=
    Eventually.of_forall fun T =>
      bettinGonekInverseMellinIntegrand_rightVertical_eq_left_add_horizontals
        hrho t huPos hR T
  have hfiniteSymm := hfinite.mono fun _ h => h.symm
  have hlimits :=
    tendsto_nhds_unique hright' (hleftLimit.congr' hfiniteSymm)
  simpa only [add_zero] using hlimits.symm

theorem bettinGonekInverseMellinLineIntegral_three_eq_right
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ)
    {u : ℝ} (hu : 1 ≤ u) {R : ℝ} (hR : 3 ≤ R) :
    bettinGonekInverseMellinLineIntegral rho t u 3 =
      bettinGonekInverseMellinLineIntegral rho t u R := by
  have hraw :=
    integral_bettinGonekInverseMellinIntegrand_three_eq_right
      hrho t hu hR
  rw [bettinGonekInverseMellinLineIntegral,
    bettinGonekInverseMellinLineIntegral]
  congr 1

theorem bettinGonekInverseMellinKernel_eq_zero
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ)
    {u : ℝ} (hu : 1 < u) :
    bettinGonekInverseMellinKernel rho t u = 0 := by
  have hright :=
    tendsto_bettinGonekInverseMellinLineIntegral_rightLine hrho t hu
  have hconst : Tendsto
      (fun _ : ℝ => bettinGonekInverseMellinLineIntegral rho t u 3)
      atTop
      (nhds (bettinGonekInverseMellinLineIntegral rho t u 3)) :=
    tendsto_const_nhds
  have heq : ∀ᶠ R : ℝ in atTop,
      bettinGonekInverseMellinLineIntegral rho t u 3 =
        bettinGonekInverseMellinLineIntegral rho t u R := by
    filter_upwards [eventually_ge_atTop (3 : ℝ)] with R hR
    exact bettinGonekInverseMellinLineIntegral_three_eq_right
      hrho t hu.le hR
  have heqSymm := heq.mono fun _ h => h.symm
  have hzero :=
    tendsto_nhds_unique hconst (hright.congr' heqSymm)
  rw [bettinGonekInverseMellinKernel]
  exact hzero

/-- The source-specific double integrand used to justify equation `(2.4)` by Bochner Fubini. -/
def bettinGonekInverseMellinConvolutionIntegrand
    (rho : ℂ) (t x : ℝ) (p : ℝ × ℝ) : ℂ :=
  bettinGonekLogMollifier p.1 (farmerCriticalLinePoint t) *
    (bettinGonekAuxiliaryG rho t (3 + p.2 * Complex.I) *
      (p.1 / x : ℂ) ^ (-(3 + p.2 * Complex.I)))

theorem norm_bettinGonekInverseMellinConvolutionIntegrand
    (rho : ℂ) (t : ℝ) {x y : ℝ} (hx : 0 < x) (hy : 1 < y)
    (eta : ℝ) :
    ‖bettinGonekInverseMellinConvolutionIntegrand rho t x (y, eta)‖ =
      x ^ 3 *
        ‖bettinGonekWeightedMollifier t 3 y‖ *
        ‖bettinGonekAuxiliaryG rho t (3 + eta * Complex.I)‖ := by
  have hyPos : 0 < y := zero_lt_one.trans hy
  have hratioPos : 0 < y / x := div_pos hyPos hx
  have hratio :
      (y / x) ^ (-3 : ℝ) = x ^ 3 * y ^ (-3 : ℝ) := by
    rw [Real.rpow_neg_ofNat, Real.rpow_neg_ofNat]
    norm_num [zpow_neg, inv_pow]
    field_simp
  have hbase : (y : ℂ) / (x : ℂ) = ((y / x : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [bettinGonekInverseMellinConvolutionIntegrand]
  rw [norm_mul, norm_mul, hbase,
    Complex.norm_cpow_eq_rpow_re_of_pos hratioPos]
  have hpowerRe :
      (-(3 + eta * Complex.I)).re = (-3 : ℝ) := by
    norm_num [Complex.mul_re]
  rw [hpowerRe, hratio, bettinGonekWeightedMollifier, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hyPos]
  norm_num [Complex.mul_re]
  ring

theorem aestronglyMeasurable_bettinGonekLogMollifier_Ioi
    (t : ℝ) :
    AEStronglyMeasurable
      (fun y : ℝ =>
        bettinGonekLogMollifier y (farmerCriticalLinePoint t))
      (volume.restrict (Set.Ioi (1 : ℝ))) := by
  have hweighted :
      AEStronglyMeasurable
        (bettinGonekWeightedMollifier t 3)
        (volume.restrict (Set.Ioi (1 : ℝ))) :=
    (integrable_bettinGonekWeightedMollifier t
      (show 3 / 2 < (3 : ℂ).re by norm_num)).aestronglyMeasurable.mono_measure
        Measure.restrict_le_self
  have hscaled :
      AEStronglyMeasurable
        (fun y : ℝ =>
          (y : ℂ) ^ (3 : ℕ) * bettinGonekWeightedMollifier t 3 y)
        (volume.restrict (Set.Ioi (1 : ℝ))) :=
    by
      have hpoly :
          AEStronglyMeasurable
            (fun y : ℝ => (y : ℂ) ^ (3 : ℕ))
            (volume.restrict (Set.Ioi (1 : ℝ))) := by
        have hcont : Continuous (fun y : ℝ => (y : ℂ) ^ (3 : ℕ)) := by
          fun_prop
        exact hcont.aestronglyMeasurable.mono_measure Measure.restrict_le_self
      exact hpoly.mul hweighted
  apply hscaled.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hyPos : 0 < y := zero_lt_one.trans hy
  have hyNe : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hyPos.ne'
  rw [bettinGonekWeightedMollifier]
  have hcancel :
      (y : ℂ) ^ (3 : ℕ) * (y : ℂ) ^ (-(3 : ℂ)) = 1 := by
    rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ hyNe]
    norm_num
  rw [← mul_assoc, hcancel, one_mul]

theorem aestronglyMeasurable_bettinGonekInverseMellinConvolutionIntegrand
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ)
    {x : ℝ} (hx : 0 < x) :
    AEStronglyMeasurable
      (bettinGonekInverseMellinConvolutionIntegrand rho t x)
      ((volume.restrict (Set.Ioi (1 : ℝ))).prod volume) := by
  have hM :=
    (aestronglyMeasurable_bettinGonekLogMollifier_Ioi t).comp_fst
      (ν := (volume : Measure ℝ))
  have hG :
      AEStronglyMeasurable
        (fun p : ℝ × ℝ =>
          bettinGonekAuxiliaryG rho t (3 + p.2 * Complex.I))
        ((volume.restrict (Set.Ioi (1 : ℝ))).prod volume) :=
    (by
      exact
        (continuous_bettinGonekAuxiliaryG_three_add_mul_I
          hrho t).aestronglyMeasurable.comp_snd)
  have hpowContinuous : ContinuousOn
      (fun p : ℝ × ℝ =>
        (p.1 / x : ℂ) ^ (-(3 + p.2 * Complex.I)))
      (Set.Ioi (1 : ℝ) ×ˢ Set.univ) := by
    intro p hp
    have hbase :
        ContinuousAt (fun q : ℝ × ℝ => (q.1 / x : ℂ)) p := by
      fun_prop
    have hexponent :
        ContinuousAt (fun q : ℝ × ℝ => -(3 + q.2 * Complex.I)) p := by
      fun_prop
    have hslit : (p.1 / x : ℂ) ∈ Complex.slitPlane := by
      rw [← Complex.ofReal_div]
      exact Complex.ofReal_mem_slitPlane.mpr
        (div_pos (zero_lt_one.trans hp.1) hx)
    exact
      (hbase.cpow hexponent hslit).continuousWithinAt
  have hpow :
      AEStronglyMeasurable
        (fun p : ℝ × ℝ =>
          (p.1 / x : ℂ) ^ (-(3 + p.2 * Complex.I)))
        ((volume.restrict (Set.Ioi (1 : ℝ))).prod volume) := by
    have hrestricted :
        AEStronglyMeasurable
          (fun p : ℝ × ℝ =>
            (p.1 / x : ℂ) ^ (-(3 + p.2 * Complex.I)))
          ((volume.restrict (Set.Ioi (1 : ℝ))).prod
            (volume.restrict Set.univ)) := by
      rw [Measure.prod_restrict]
      exact hpowContinuous.aestronglyMeasurable
        (measurableSet_Ioi.prod MeasurableSet.univ)
    simpa using hrestricted
  exact hM.mul (hG.mul hpow)

theorem integrable_bettinGonekInverseMellinConvolutionIntegrand
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ)
    {x : ℝ} (hx : 0 < x) :
    Integrable (bettinGonekInverseMellinConvolutionIntegrand rho t x)
      ((volume.restrict (Set.Ioi (1 : ℝ))).prod volume) := by
  have hM :
      Integrable
        (fun y : ℝ => x ^ 3 * ‖bettinGonekWeightedMollifier t 3 y‖)
        (volume.restrict (Set.Ioi (1 : ℝ))) := by
    exact
      ((integrable_bettinGonekWeightedMollifier t
        (show 3 / 2 < (3 : ℂ).re by norm_num)).norm.integrableOn).const_mul
        (x ^ 3)
  have hG :
      Integrable
        (fun eta : ℝ =>
          ‖bettinGonekAuxiliaryG rho t (3 + eta * Complex.I)‖) :=
    (integrable_bettinGonekAuxiliaryG_three_add_mul_I hrho t).norm
  have hmajor := hM.mul_prod hG
  apply hmajor.mono'
  · exact
      aestronglyMeasurable_bettinGonekInverseMellinConvolutionIntegrand
        hrho t hx
  · have hy : ∀ᵐ y ∂volume.restrict (Set.Ioi (1 : ℝ)),
        y ∈ Set.Ioi (1 : ℝ) :=
      ae_restrict_mem measurableSet_Ioi
    have hp : ∀ᵐ p : ℝ × ℝ ∂
        ((volume.restrict (Set.Ioi (1 : ℝ))).prod volume),
        p.1 ∈ Set.Ioi (1 : ℝ) :=
      (MeasureTheory.Measure.quasiMeasurePreserving_fst
        (μ := volume.restrict (Set.Ioi (1 : ℝ)))
        (ν := (volume : Measure ℝ))).ae hy
    filter_upwards [hp] with p hp
    exact
      (norm_bettinGonekInverseMellinConvolutionIntegrand rho t hx hp p.2).le

theorem cpow_div_neg_eq_cpow_neg_mul_cpow
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (w : ℂ) :
    (y / x : ℂ) ^ (-w) = (y : ℂ) ^ (-w) * (x : ℂ) ^ w := by
  calc
    (y / x : ℂ) ^ (-w) =
        ((y : ℂ) * ((x⁻¹ : ℝ) : ℂ)) ^ (-w) := by
          rw [← Complex.ofReal_div]
          simp only [div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_inv]
    _ = (y : ℂ) ^ (-w) * (((x⁻¹ : ℝ) : ℂ) ^ (-w)) := by
          rw [Complex.mul_cpow_ofReal_nonneg hy.le (inv_nonneg.mpr hx.le)]
    _ = (y : ℂ) ^ (-w) * (x : ℂ) ^ w := by
          rw [Complex.ofReal_inv, Complex.inv_cpow]
          · rw [Complex.cpow_neg (x : ℂ) w, inv_inv]
          · rw [Complex.arg_ofReal_of_nonneg hx.le]
            exact Real.pi_ne_zero.symm

theorem integral_bettinGonekInverseMellinConvolutionIntegrand_fst
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ)
    {x : ℝ} (hx : 0 < x) (eta : ℝ) :
    ∫ y : ℝ in Set.Ioi 1,
        bettinGonekInverseMellinConvolutionIntegrand rho t x (y, eta) =
      bettinGonekJKernel rho t x (3 + eta * Complex.I) := by
  let w : ℂ := 3 + eta * Complex.I
  calc
    ∫ y : ℝ in Set.Ioi 1,
        bettinGonekInverseMellinConvolutionIntegrand rho t x (y, eta) =
        ∫ y : ℝ in Set.Ioi 1,
          (bettinGonekAuxiliaryG rho t w * (x : ℂ) ^ w) *
            bettinGonekWeightedMollifier t w y := by
              apply setIntegral_congr_fun measurableSet_Ioi
              intro y hy
              simp only [bettinGonekInverseMellinConvolutionIntegrand]
              change
                bettinGonekLogMollifier y (farmerCriticalLinePoint t) *
                    (bettinGonekAuxiliaryG rho t w *
                      (y / x : ℂ) ^ (-w)) =
                  (bettinGonekAuxiliaryG rho t w * (x : ℂ) ^ w) *
                    bettinGonekWeightedMollifier t w y
              rw [cpow_div_neg_eq_cpow_neg_mul_cpow hx
                (zero_lt_one.trans hy) w]
              simp only [bettinGonekWeightedMollifier]
              ring
    _ = (bettinGonekAuxiliaryG rho t w * (x : ℂ) ^ w) *
        bettinGonekH t w := by
          rw [integral_const_mul, bettinGonekH]
    _ = bettinGonekJKernel rho t x w := by
          simpa only [mul_assoc, mul_comm, mul_left_comm] using
            bettinGonekAuxiliary_mul_H_eq_JKernel hrho t x
              (show 3 / 2 < w.re by simp [w])

theorem integral_bettinGonekInverseMellinConvolutionIntegrand_snd
    (rho : ℂ) (t x y : ℝ) :
    ∫ eta : ℝ,
        bettinGonekInverseMellinConvolutionIntegrand rho t x (y, eta) =
      bettinGonekLogMollifier y (farmerCriticalLinePoint t) *
        ∫ eta : ℝ,
          bettinGonekInverseMellinIntegrand rho t (y / x)
            (3 + eta * Complex.I) := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with eta
  simp only [bettinGonekInverseMellinConvolutionIntegrand,
    bettinGonekInverseMellinIntegrand]
  rw [Complex.ofReal_div]

theorem bettinGonekJLineIntegral_three_eq_inverseMellinConvolution
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ)
    {x : ℝ} (hx : 0 < x) :
    bettinGonekJLineIntegral rho t x 3 =
      ∫ y : ℝ in Set.Ioi 1,
        bettinGonekLogMollifier y (farmerCriticalLinePoint t) *
          bettinGonekInverseMellinKernel rho t (y / x) := by
  have hprod :=
    integrable_bettinGonekInverseMellinConvolutionIntegrand hrho t hx
  have hswap :
      (∫ y : ℝ in Set.Ioi 1, ∫ eta : ℝ,
          bettinGonekInverseMellinConvolutionIntegrand rho t x (y, eta)) =
        ∫ eta : ℝ, ∫ y : ℝ in Set.Ioi 1,
          bettinGonekInverseMellinConvolutionIntegrand rho t x (y, eta) := by
    exact integral_integral_swap hprod
  let c : ℂ := (1 / (2 * Real.pi) : ℝ)
  calc
    bettinGonekJLineIntegral rho t x 3 =
        c * ∫ eta : ℝ,
          bettinGonekJKernel rho t x (3 + eta * Complex.I) := by
            rfl
    _ = c * ∫ eta : ℝ, ∫ y : ℝ in Set.Ioi 1,
          bettinGonekInverseMellinConvolutionIntegrand rho t x (y, eta) := by
            have hinter :
                (fun eta : ℝ =>
                    bettinGonekJKernel rho t x (3 + eta * Complex.I)) =ᵐ[volume]
                  fun eta : ℝ => ∫ y : ℝ in Set.Ioi 1,
                    bettinGonekInverseMellinConvolutionIntegrand
                      rho t x (y, eta) :=
              Filter.Eventually.of_forall fun eta =>
                (integral_bettinGonekInverseMellinConvolutionIntegrand_fst
                  hrho t hx eta).symm
            rw [integral_congr_ae hinter]
    _ = c * ∫ y : ℝ in Set.Ioi 1, ∫ eta : ℝ,
          bettinGonekInverseMellinConvolutionIntegrand rho t x (y, eta) := by
            rw [hswap]
    _ = ∫ y : ℝ in Set.Ioi 1,
          bettinGonekLogMollifier y (farmerCriticalLinePoint t) *
            bettinGonekInverseMellinKernel rho t (y / x) := by
            rw [← integral_const_mul]
            apply setIntegral_congr_fun measurableSet_Ioi
            intro y _
            change
              c * (∫ eta : ℝ,
                bettinGonekInverseMellinConvolutionIntegrand rho t x (y, eta)) =
                bettinGonekLogMollifier y (farmerCriticalLinePoint t) *
                  bettinGonekInverseMellinKernel rho t (y / x)
            rw [integral_bettinGonekInverseMellinConvolutionIntegrand_snd,
              bettinGonekInverseMellinKernel,
              bettinGonekInverseMellinLineIntegral]
            simp only [c]
            ring_nf
            congr 2
            funext eta
            congr 1
            norm_num
            ring

theorem normalized_integral_bettinGonekInverseMellinConvolutionIntegrand_snd
    (rho : ℂ) (t x y : ℝ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ eta : ℝ,
          bettinGonekInverseMellinConvolutionIntegrand rho t x (y, eta) =
      bettinGonekLogMollifier y (farmerCriticalLinePoint t) *
        bettinGonekInverseMellinKernel rho t (y / x) := by
  rw [integral_bettinGonekInverseMellinConvolutionIntegrand_snd,
    bettinGonekInverseMellinKernel,
    bettinGonekInverseMellinLineIntegral]
  ring_nf
  congr 2
  funext eta
  congr 1
  norm_num
  ring

theorem integrableOn_bettinGonekInverseMellinConvolution
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ)
    {x : ℝ} (hx : 0 < x) :
    IntegrableOn
      (fun y : ℝ =>
        bettinGonekLogMollifier y (farmerCriticalLinePoint t) *
          bettinGonekInverseMellinKernel rho t (y / x))
      (Set.Ioi 1) := by
  have hprod :=
    integrable_bettinGonekInverseMellinConvolutionIntegrand hrho t hx
  have hiterated :=
    hprod.integral_prod_left.const_mul
      (((1 / (2 * Real.pi) : ℝ) : ℂ))
  exact hiterated.congr
    (Filter.Eventually.of_forall fun y =>
      normalized_integral_bettinGonekInverseMellinConvolutionIntegrand_snd
        rho t x y)

theorem integral_bettinGonekInverseMellinConvolution_eq_Icc
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ)
    {x : ℝ} (hx : 0 < x) (hxOne : 1 ≤ x) :
    (∫ y : ℝ in Set.Ioi 1,
        bettinGonekLogMollifier y (farmerCriticalLinePoint t) *
          bettinGonekInverseMellinKernel rho t (y / x)) =
      ∫ y : ℝ in Set.Icc 1 x,
        bettinGonekLogMollifier y (farmerCriticalLinePoint t) *
          bettinGonekInverseMellinKernel rho t (y / x) := by
  let f : ℝ → ℂ := fun y =>
    bettinGonekLogMollifier y (farmerCriticalLinePoint t) *
      bettinGonekInverseMellinKernel rho t (y / x)
  have hf : IntegrableOn f (Set.Ioi 1) :=
    integrableOn_bettinGonekInverseMellinConvolution hrho t hx
  have hbounded : IntegrableOn f (Set.Ioc 1 x) :=
    hf.mono_set Set.Ioc_subset_Ioi_self
  have htail : IntegrableOn f (Set.Ioi x) :=
    hf.mono_set (Set.Ioi_subset_Ioi hxOne)
  have hsplit :=
    setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
      hbounded htail
  rw [Set.Ioc_union_Ioi_eq_Ioi hxOne] at hsplit
  have htailZero : (∫ y : ℝ in Set.Ioi x, f y) = 0 := by
    calc
      (∫ y : ℝ in Set.Ioi x, f y) =
          ∫ _y : ℝ in Set.Ioi x, (0 : ℂ) := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro y hy
            dsimp only [f]
            rw [bettinGonekInverseMellinKernel_eq_zero hrho t
              ((one_lt_div hx).2 hy), mul_zero]
      _ = 0 := by simp
  calc
    (∫ y : ℝ in Set.Ioi 1,
        bettinGonekLogMollifier y (farmerCriticalLinePoint t) *
          bettinGonekInverseMellinKernel rho t (y / x)) =
        ∫ y : ℝ in Set.Ioi 1, f y := by rfl
    _ = (∫ y : ℝ in Set.Ioc 1 x, f y) +
        ∫ y : ℝ in Set.Ioi x, f y := hsplit
    _ = ∫ y : ℝ in Set.Ioc 1 x, f y := by rw [htailZero, add_zero]
    _ = ∫ y : ℝ in Set.Icc 1 x, f y :=
      integral_Icc_eq_integral_Ioc.symm
    _ = ∫ y : ℝ in Set.Icc 1 x,
        bettinGonekLogMollifier y (farmerCriticalLinePoint t) *
          bettinGonekInverseMellinKernel rho t (y / x) := by rfl

theorem pow_three_mul_bettinGonekWeightedMollifier
    (t : ℝ) {y : ℝ} (hy : 0 < y) :
    (y : ℂ) ^ (3 : ℕ) * bettinGonekWeightedMollifier t 3 y =
      bettinGonekLogMollifier y (farmerCriticalLinePoint t) := by
  have hyNe : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  rw [bettinGonekWeightedMollifier]
  have hcancel :
      (y : ℂ) ^ (3 : ℕ) * (y : ℂ) ^ (-(3 : ℂ)) = 1 := by
    rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ hyNe]
    norm_num
  rw [← mul_assoc, hcancel, one_mul]

theorem integrableOn_norm_bettinGonekLogMollifier_Icc
    (t : ℝ) (x : ℝ) :
    IntegrableOn
      (fun y : ℝ =>
        ‖bettinGonekLogMollifier y (farmerCriticalLinePoint t)‖)
      (Set.Icc 1 x) := by
  rw [integrableOn_Icc_iff_integrableOn_Ioc]
  have hmajor :
      IntegrableOn
        (fun y : ℝ => x ^ 3 * ‖bettinGonekWeightedMollifier t 3 y‖)
        (Set.Ioc 1 x) :=
    ((integrable_bettinGonekWeightedMollifier t
      (show 3 / 2 < (3 : ℂ).re by norm_num)).norm.const_mul
        (x ^ 3)).integrableOn
  have hmeas :
      AEStronglyMeasurable
        (fun y : ℝ =>
          ‖bettinGonekLogMollifier y (farmerCriticalLinePoint t)‖)
        (volume.restrict (Set.Ioc 1 x)) :=
    (aestronglyMeasurable_bettinGonekLogMollifier_Ioi t).norm.mono_measure
      (Measure.restrict_mono Set.Ioc_subset_Ioi_self le_rfl)
  apply hmajor.mono' hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
  have hyPos : 0 < y := zero_lt_one.trans hy.1
  have hpow : y ^ 3 ≤ x ^ 3 :=
    pow_le_pow_left₀ hyPos.le hy.2 3
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  calc
    ‖bettinGonekLogMollifier y (farmerCriticalLinePoint t)‖ =
        ‖(y : ℂ) ^ (3 : ℕ) * bettinGonekWeightedMollifier t 3 y‖ := by
          rw [pow_three_mul_bettinGonekWeightedMollifier t hyPos]
    _ = y ^ 3 * ‖bettinGonekWeightedMollifier t 3 y‖ := by
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos hyPos]
    _ ≤ x ^ 3 * ‖bettinGonekWeightedMollifier t 3 y‖ :=
      mul_le_mul_of_nonneg_right hpow (norm_nonneg _)

theorem norm_bettinGonekJLineIntegral_three_le_inverseMellinBound
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ)
    {x : ℝ} (hx : 2 ≤ x) :
    ‖bettinGonekJLineIntegral rho t x 3‖ ≤
      bettinGonekInverseMellinBound rho t *
        ∫ y : ℝ in Set.Icc 1 x,
          ‖bettinGonekLogMollifier y (farmerCriticalLinePoint t)‖ := by
  have hxPos : 0 < x := by linarith
  have hxOne : 1 ≤ x := by linarith
  let f : ℝ → ℂ := fun y =>
    bettinGonekLogMollifier y (farmerCriticalLinePoint t) *
      bettinGonekInverseMellinKernel rho t (y / x)
  have hfIoi : IntegrableOn f (Set.Ioi 1) :=
    integrableOn_bettinGonekInverseMellinConvolution hrho t hxPos
  have hfIcc : IntegrableOn f (Set.Icc 1 x) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact hfIoi.mono_set Set.Ioc_subset_Ioi_self
  have hM :
      IntegrableOn
        (fun y : ℝ =>
          ‖bettinGonekLogMollifier y (farmerCriticalLinePoint t)‖)
        (Set.Icc 1 x) :=
    integrableOn_norm_bettinGonekLogMollifier_Icc t x
  have hmajor :
      IntegrableOn
        (fun y : ℝ =>
          bettinGonekInverseMellinBound rho t *
            ‖bettinGonekLogMollifier y (farmerCriticalLinePoint t)‖)
        (Set.Icc 1 x) :=
    hM.const_mul (bettinGonekInverseMellinBound rho t)
  have hmono :
      (∫ y : ℝ in Set.Icc 1 x, ‖f y‖) ≤
        ∫ y : ℝ in Set.Icc 1 x,
          bettinGonekInverseMellinBound rho t *
            ‖bettinGonekLogMollifier y (farmerCriticalLinePoint t)‖ := by
    apply setIntegral_mono_on hfIcc.norm hmajor measurableSet_Icc
    intro y hy
    have hyPos : 0 < y := zero_lt_one.trans_le hy.1
    have huPos : 0 < y / x := div_pos hyPos hxPos
    have huOne : y / x ≤ 1 := (div_le_one hxPos).2 hy.2
    have hk := norm_bettinGonekInverseMellinKernel_le
      hrho t huPos huOne
    dsimp only [f]
    rw [norm_mul]
    calc
      ‖bettinGonekLogMollifier y (farmerCriticalLinePoint t)‖ *
          ‖bettinGonekInverseMellinKernel rho t (y / x)‖ ≤
          ‖bettinGonekLogMollifier y (farmerCriticalLinePoint t)‖ *
            bettinGonekInverseMellinBound rho t :=
        mul_le_mul_of_nonneg_left hk (norm_nonneg _)
      _ = bettinGonekInverseMellinBound rho t *
          ‖bettinGonekLogMollifier y (farmerCriticalLinePoint t)‖ :=
        mul_comm _ _
  rw [bettinGonekJLineIntegral_three_eq_inverseMellinConvolution
    hrho t hxPos,
    integral_bettinGonekInverseMellinConvolution_eq_Icc
      hrho t hxPos hxOne]
  change ‖∫ y : ℝ in Set.Icc 1 x, f y‖ ≤ _
  calc
    ‖∫ y : ℝ in Set.Icc 1 x, f y‖ ≤
        ∫ y : ℝ in Set.Icc 1 x, ‖f y‖ :=
      norm_integral_le_integral_norm f
    _ ≤ ∫ y : ℝ in Set.Icc 1 x,
        bettinGonekInverseMellinBound rho t *
          ‖bettinGonekLogMollifier y (farmerCriticalLinePoint t)‖ :=
      hmono
    _ = bettinGonekInverseMellinBound rho t *
        ∫ y : ℝ in Set.Icc 1 x,
          ‖bettinGonekLogMollifier y (farmerCriticalLinePoint t)‖ := by
      rw [integral_const_mul]

/-- The fixed inverse-Mellin endpoint: standalone auxiliary decay, exact support and
boundedness of the inverse transform, the direct Bochner-Fubini convolution, and the source
upper bound for the actual Bettin--Gonek line integral. -/
theorem bettinGonekInverseMellinConvolution_endpoint
    {rho : ℂ} (hrho : IsNontrivialZero rho) (t : ℝ)
    {x : ℝ} (hx : 2 ≤ x) :
    Integrable (fun y : ℝ =>
      bettinGonekAuxiliaryG rho t (y * Complex.I)) ∧
      Integrable (fun y : ℝ =>
        bettinGonekAuxiliaryG rho t (3 + y * Complex.I)) ∧
      (∀ a v : ℝ, a ∈ Set.Icc (0 : ℝ) 3 → 1 ≤ |v| →
        ‖bettinGonekAuxiliaryG rho t
            (a + (v - t) * Complex.I)‖ ≤
          bettinGonekAuxiliaryStripLiftBound rho / |v| ^ 3) ∧
      (∀ R : ℝ, 3 ≤ R →
        Integrable (fun y : ℝ =>
          bettinGonekAuxiliaryG rho t (R + y * Complex.I))) ∧
      Integrable
        (bettinGonekInverseMellinConvolutionIntegrand rho t x)
        ((volume.restrict (Set.Ioi (1 : ℝ))).prod volume) ∧
      (∀ u : ℝ, 1 < u →
        bettinGonekInverseMellinKernel rho t u = 0) ∧
      (∀ u : ℝ, 0 < u → u ≤ 1 →
        ‖bettinGonekInverseMellinKernel rho t u‖ ≤
          bettinGonekInverseMellinBound rho t) ∧
      bettinGonekJLineIntegral rho t x 3 =
        ∫ y : ℝ in Set.Ioi 1,
          bettinGonekLogMollifier y (farmerCriticalLinePoint t) *
            bettinGonekInverseMellinKernel rho t (y / x) ∧
      ‖bettinGonekJLineIntegral rho t x 3‖ ≤
        bettinGonekInverseMellinBound rho t *
          ∫ y : ℝ in Set.Icc 1 x,
            ‖bettinGonekLogMollifier y (farmerCriticalLinePoint t)‖ := by
  have hxPos : 0 < x := by linarith
  exact
    ⟨integrable_bettinGonekAuxiliaryG_mul_I hrho t,
      integrable_bettinGonekAuxiliaryG_three_add_mul_I hrho t,
      fun _ _ ha hv =>
        norm_bettinGonekAuxiliaryG_fixedStrip_le hrho t ha hv,
      fun _ hR => integrable_bettinGonekAuxiliaryG_rightLine hrho t hR,
      integrable_bettinGonekInverseMellinConvolutionIntegrand hrho t hxPos,
      fun _ hu => bettinGonekInverseMellinKernel_eq_zero hrho t hu,
      fun _ hu huOne =>
        norm_bettinGonekInverseMellinKernel_le hrho t hu huOne,
      bettinGonekJLineIntegral_three_eq_inverseMellinConvolution
        hrho t hxPos,
      norm_bettinGonekJLineIntegral_three_le_inverseMellinBound
        hrho t hx⟩

end

end LeanLab.Riemann
