import LeanLab.Riemann.ClassicalZeroDetectorMellin
import LeanLab.Riemann.BaezDuarteZetaRatio
import LeanLab.Riemann.BettinGonekInverseMellinConvolution
import LeanLab.Riemann.WeilCompactLaplaceArithmeticFormula
import Mathlib.Analysis.MellinInversion

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Inverse Mellin formula for the classical zero detector

This module proves Gamma integrability on every positive vertical line, specializes Mathlib's
Mellin inversion theorem to the exponential kernel, and justifies the detector's infinite
sum--vertical-integral exchange on the absolute-convergence half-plane.
-/

open Filter MeasureTheory Set
open scoped BigOperators

namespace LeanLab.Riemann

noncomputable section

private theorem classicalDetector_pow_four_le_cosh (x : ℝ) :
    x ^ 4 ≤ 512 * Real.cosh x := by
  let y := |x| / 4
  have hy : 0 ≤ y := by positivity
  have hyexp : y ≤ Real.exp y := by
    exact (le_add_of_nonneg_right zero_le_one).trans
      (Real.add_one_le_exp y)
  have hpow : y ^ 4 ≤ (Real.exp y) ^ 4 :=
    pow_le_pow_left₀ hy hyexp 4
  have hexp : (Real.exp y) ^ 4 = Real.exp |x| := by
    rw [← Real.exp_nat_mul]
    congr 1
    dsimp [y]
    ring
  have habs : Real.exp |x| ≤ Real.exp x + Real.exp (-x) := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
      exact le_add_of_nonneg_right (Real.exp_nonneg _)
    · rw [abs_of_nonpos hx]
      exact le_add_of_nonneg_left (Real.exp_nonneg _)
  have hcosh : Real.exp x + Real.exp (-x) = 2 * Real.cosh x := by
    rw [Real.cosh_eq]
    ring
  have hy4 : y ^ 4 ≤ 2 * Real.cosh x := by
    rw [hcosh] at habs
    exact hpow.trans (hexp.le.trans habs)
  have hydef : y ^ 4 = |x| ^ 4 / 256 := by
    simp [y]
    ring
  have habspow : |x| ^ 4 = x ^ 4 := by
    exact (by norm_num : Even 4).pow_abs x
  rw [hydef, habspow] at hy4
  linarith

private theorem classicalDetector_verticalIntegrable_Gamma_half :
    Complex.VerticalIntegrable Complex.Gamma (1 / 2 : ℝ) := by
  apply integrable_of_continuous_norm_le_abs_inv_sq (C := 64)
  · rw [continuous_iff_continuousAt]
    intro t
    have hinner :
        ContinuousAt
          (fun y : ℝ => (((1 / 2 : ℝ) : ℂ) + y * Complex.I)) t := by
      fun_prop
    have hgamma :
        ContinuousAt Complex.Gamma
          (((1 / 2 : ℝ) : ℂ) + t * Complex.I) := by
      exact (Complex.differentiableAt_Gamma
        (((1 / 2 : ℝ) : ℂ) + t * Complex.I) (by
          intro n h
          have hre := congrArg Complex.re h
          norm_num at hre
          have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
          linarith)).continuousAt
    have hcomp := ContinuousAt.comp
      (f := fun y : ℝ => (((1 / 2 : ℝ) : ℂ) + y * Complex.I))
      (x := t) hgamma hinner
    simpa [Function.comp_def] using hcomp
  · norm_num
  · intro t ht
    have ht0 : t ≠ 0 := by
      exact abs_ne_zero.mp (ne_of_gt (lt_trans zero_lt_one ht))
    have htAbs0 : |t| ≠ 0 := abs_ne_zero.mpr ht0
    have hsq :
        ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ^ 2 =
          Real.pi / Real.cosh (Real.pi * t) := by
      simpa [Real.cosh_neg] using
        norm_Gamma_half_sub_mul_I_sq (-t)
    have hcoshPos : 0 < Real.cosh (Real.pi * t) :=
      Real.cosh_pos _
    have hpi : (1 : ℝ) ≤ Real.pi := by
      linarith [Real.two_le_pi]
    have hpoly := classicalDetector_pow_four_le_cosh (Real.pi * t)
    have htAbsPos : 0 < |t| := abs_pos.mpr ht0
    have hpi4 : (1 : ℝ) ≤ Real.pi ^ 4 := one_le_pow₀ hpi
    have ht4Nonneg : 0 ≤ |t| ^ 4 := by positivity
    have hpolyAbs :
        |t| ^ 4 ≤ 512 * Real.cosh (Real.pi * t) := by
      calc
        |t| ^ 4 = 1 * |t| ^ 4 := by ring
        _ ≤ Real.pi ^ 4 * |t| ^ 4 :=
          mul_le_mul_of_nonneg_right hpi4 ht4Nonneg
        _ = (Real.pi * t) ^ 4 := by
          rw [mul_pow, (by norm_num : Even 4).pow_abs t]
        _ ≤ 512 * Real.cosh (Real.pi * t) := hpoly
    have hsqBound :
        ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ^ 2 ≤
          2048 * (|t|⁻¹ ^ (4 : ℕ)) := by
      rw [hsq]
      apply (div_le_iff₀ hcoshPos).2
      have hscaled := mul_le_mul_of_nonneg_left hpolyAbs
        (show 0 ≤ |t|⁻¹ ^ (4 : ℕ) by positivity)
      have hinv : |t|⁻¹ ^ (4 : ℕ) * |t| ^ 4 = 1 := by
        field_simp
      rw [hinv] at hscaled
      nlinarith [Real.pi_le_four]
    have hnormNonneg :
        0 ≤ ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ :=
      norm_nonneg _
    have hmajorNonneg : 0 ≤ 64 * |t|⁻¹ ^ (2 : ℕ) := by positivity
    apply (sq_le_sq₀ hnormNonneg hmajorNonneg).mp
    calc
      ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ^ 2
          ≤ 2048 * (|t|⁻¹ ^ (4 : ℕ)) := hsqBound
      _ ≤ (64 * |t|⁻¹ ^ (2 : ℕ)) ^ 2 := by
        have hinvNonneg : 0 ≤ |t|⁻¹ := by positivity
        rw [show |t|⁻¹ ^ (4 : ℕ) =
          (|t|⁻¹ ^ (2 : ℕ)) ^ 2 by ring]
        nlinarith [sq_nonneg (|t|⁻¹ ^ (2 : ℕ))]

private theorem classicalDetector_norm_Gamma_half_le_exp (t : ℝ) :
    ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ≤
      3 * Real.exp (-|t|) := by
  have hsq :
      ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ^ 2 =
        Real.pi / Real.cosh (Real.pi * t) := by
    simpa [Real.cosh_neg] using
      norm_Gamma_half_sub_mul_I_sq (-t)
  have hcoshPos : 0 < Real.cosh (Real.pi * t) :=
    Real.cosh_pos _
  have hexpPos : 0 < Real.exp (Real.pi * |t|) :=
    Real.exp_pos _
  have hcosh :
      Real.exp (Real.pi * |t|) ≤
        2 * Real.cosh (Real.pi * t) := by
    rw [Real.cosh_eq]
    ring_nf
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht]
      exact le_add_of_nonneg_right (Real.exp_nonneg _)
    · rw [abs_of_nonpos ht]
      ring_nf
      exact le_add_of_nonneg_left (Real.exp_nonneg _)
  have hsqExp :
      ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ^ 2 ≤
        8 * Real.exp (-2 * |t|) := by
    rw [hsq]
    calc
      Real.pi / Real.cosh (Real.pi * t) ≤
          (2 * Real.pi) / Real.exp (Real.pi * |t|) := by
        apply (div_le_div_iff₀ hcoshPos hexpPos).2
        nlinarith [Real.pi_pos]
      _ = 2 * Real.pi * Real.exp (-(Real.pi * |t|)) := by
        rw [div_eq_mul_inv, ← Real.exp_neg]
      _ ≤ 8 * Real.exp (-(Real.pi * |t|)) := by
        gcongr
        linarith [Real.pi_le_four]
      _ ≤ 8 * Real.exp (-2 * |t|) := by
        gcongr
        nlinarith [Real.two_le_pi, abs_nonneg t]
  have hnormNonneg :
      0 ≤ ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ :=
    norm_nonneg _
  have hmajorNonneg : 0 ≤ 3 * Real.exp (-|t|) := by positivity
  apply (sq_le_sq₀ hnormNonneg hmajorNonneg).mp
  calc
    ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ^ 2
        ≤ 8 * Real.exp (-2 * |t|) := hsqExp
    _ ≤ (3 * Real.exp (-|t|)) ^ 2 := by
      have hexpSq :
          Real.exp (-|t|) ^ 2 = Real.exp (-2 * |t|) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      rw [mul_pow, hexpSq]
      nlinarith [Real.exp_pos (-2 * |t|)]

private theorem classicalDetector_pow_mul_exp_neg_le_factorial_mul_inv_sq
    (N : ℕ) {x : ℝ} (hx : 0 < x) :
    x ^ N * Real.exp (-x) ≤
      ((N + 2).factorial : ℝ) * x⁻¹ ^ (2 : ℕ) := by
  have hfactorial :
      0 < ((N + 2).factorial : ℝ) := by positivity
  have hseries :=
    Real.pow_div_factorial_le_exp x hx.le (N + 2)
  have hpow :
      x ^ (N + 2) ≤
        ((N + 2).factorial : ℝ) * Real.exp x := by
    simpa [mul_comm] using (div_le_iff₀ hfactorial).mp hseries
  have hscale :
      0 ≤ Real.exp (-x) * x⁻¹ ^ (2 : ℕ) := by positivity
  have hscaled := mul_le_mul_of_nonneg_right hpow hscale
  calc
    x ^ N * Real.exp (-x) =
        x ^ (N + 2) * (Real.exp (-x) * x⁻¹ ^ (2 : ℕ)) := by
      rw [pow_add]
      field_simp
    _ ≤ (((N + 2).factorial : ℝ) * Real.exp x) *
        (Real.exp (-x) * x⁻¹ ^ (2 : ℕ)) := hscaled
    _ = ((N + 2).factorial : ℝ) * x⁻¹ ^ (2 : ℕ) := by
      rw [Real.exp_neg]
      field_simp

private theorem classicalDetector_rpow_mul_norm_Gamma_half_le_inv_sq
    (p : ℝ) :
    ∃ K : ℝ, 0 < K ∧
      ∀ t : ℝ, 1 < |t| →
        (|t| + 2) ^ p *
            ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ≤
          K * |t|⁻¹ ^ (2 : ℕ) := by
  let N := ⌈p⌉₊
  refine ⟨3 ^ (N + 1) * ((N + 2).factorial : ℝ), by positivity, ?_⟩
  intro t ht
  have htPos : 0 < |t| := lt_trans zero_lt_one ht
  have hbaseOne : 1 ≤ |t| + 2 := by linarith
  have hpN : p ≤ (N : ℝ) := by
    exact Nat.le_ceil p
  have hrpow :
      (|t| + 2) ^ p ≤ (|t| + 2) ^ N := by
    calc
      (|t| + 2) ^ p ≤ (|t| + 2) ^ (N : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hbaseOne hpN
      _ = (|t| + 2) ^ N := Real.rpow_natCast _ _
  have hbase :
      |t| + 2 ≤ 3 * |t| := by linarith
  have hpow :
      (|t| + 2) ^ N ≤ 3 ^ N * |t| ^ N := by
    calc
      (|t| + 2) ^ N ≤ (3 * |t|) ^ N :=
        pow_le_pow_left₀ (by positivity) hbase N
      _ = 3 ^ N * |t| ^ N := by rw [mul_pow]
  have hpoly :
      (|t| + 2) ^ p ≤ 3 ^ N * |t| ^ N :=
    hrpow.trans hpow
  calc
    (|t| + 2) ^ p *
          ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ≤
        (|t| + 2) ^ p * (3 * Real.exp (-|t|)) :=
      mul_le_mul_of_nonneg_left (classicalDetector_norm_Gamma_half_le_exp t) (by positivity)
    _ ≤ (3 ^ N * |t| ^ N) * (3 * Real.exp (-|t|)) :=
      mul_le_mul_of_nonneg_right hpoly (by positivity)
    _ = 3 ^ (N + 1) * (|t| ^ N * Real.exp (-|t|)) := by
      rw [pow_succ]
      ring
    _ ≤ 3 ^ (N + 1) *
        (((N + 2).factorial : ℝ) * |t|⁻¹ ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_left
        (classicalDetector_pow_mul_exp_neg_le_factorial_mul_inv_sq N htPos)
        (by positivity)
    _ = (3 ^ (N + 1) * ((N + 2).factorial : ℝ)) *
        |t|⁻¹ ^ (2 : ℕ) := by ring

private theorem classicalDetector_continuous_Gamma_vertical
    {c : ℝ} (hc : 0 < c) :
    Continuous
      (fun t : ℝ => Complex.Gamma ((c : ℂ) + t * Complex.I)) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hinner :
      ContinuousAt (fun y : ℝ => ((c : ℂ) + y * Complex.I)) t := by
    fun_prop
  have hgamma :
      ContinuousAt Complex.Gamma ((c : ℂ) + t * Complex.I) := by
    exact (Complex.differentiableAt_Gamma
      ((c : ℂ) + t * Complex.I) (by
        intro n h
        have hre := congrArg Complex.re h
        norm_num at hre
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith)).continuousAt
  have hcomp := ContinuousAt.comp
    (f := fun y : ℝ => ((c : ℂ) + y * Complex.I))
    (x := t) hgamma hinner
  simpa [Function.comp_def] using hcomp

private theorem classicalDetector_verticalIntegrable_Gamma_of_half_le
    {c : ℝ} (hc : (1 / 2 : ℝ) ≤ c) :
    Complex.VerticalIntegrable Complex.Gamma c := by
  obtain ⟨C, hC, hratio⟩ :=
    exists_norm_Gamma_div_le_rpow_of_re_mem_Icc
      (1 / 2 : ℝ) c (by norm_num)
  let p := C * (c - 1 / 2)
  obtain ⟨K, hK, hmajor⟩ :=
    classicalDetector_rpow_mul_norm_Gamma_half_le_inv_sq p
  apply integrable_of_continuous_norm_le_abs_inv_sq (C := K)
  · exact classicalDetector_continuous_Gamma_vertical (lt_of_lt_of_le (by norm_num) hc)
  · exact hK.le
  · intro t ht
    let z0 : ℂ := ((1 / 2 : ℝ) : ℂ) + t * Complex.I
    let δ : ℝ := c - 1 / 2
    have hδ : 0 ≤ δ := by
      dsimp [δ]
      linarith
    have hz0re : (1 / 2 : ℝ) ≤ z0.re := by
      simp [z0]
    have hzδre : (z0 + δ).re ≤ c := by
      simp [z0, δ]
    have hratioBound :
        ‖Complex.Gamma (z0 + δ) / Complex.Gamma z0‖ ≤
          (|z0.im| + 2) ^ p := by
      have hsource := hratio z0 δ hz0re hzδre hδ
      change
        ‖Complex.Gamma (z0 + δ) / Complex.Gamma z0‖ ≤
          (|z0.im| + 2) ^ p at hsource
      exact hsource
    have hz0Gamma : Complex.Gamma z0 ≠ 0 := by
      apply Complex.Gamma_ne_zero_of_re_pos
      simp [z0]
    have hzδ :
        z0 + δ = (c : ℂ) + t * Complex.I := by
      dsimp [z0, δ]
      push_cast
      ring
    calc
      ‖Complex.Gamma ((c : ℂ) + t * Complex.I)‖ =
          ‖(Complex.Gamma (z0 + δ) / Complex.Gamma z0) *
              Complex.Gamma z0‖ := by
        rw [div_mul_cancel₀ _ hz0Gamma, hzδ]
      _ = ‖Complex.Gamma (z0 + δ) / Complex.Gamma z0‖ *
          ‖Complex.Gamma z0‖ := norm_mul _ _
      _ ≤ (|z0.im| + 2) ^ p * ‖Complex.Gamma z0‖ :=
        mul_le_mul_of_nonneg_right hratioBound (norm_nonneg _)
      _ = (|t| + 2) ^ p *
          ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ := by
        simp [z0]
      _ ≤ K * |t|⁻¹ ^ (2 : ℕ) := hmajor t ht

theorem verticalIntegrable_Gamma_of_pos
    {c : ℝ} (hc : 0 < c) :
    Complex.VerticalIntegrable Complex.Gamma c := by
  by_cases hhalf : (1 / 2 : ℝ) ≤ c
  · exact classicalDetector_verticalIntegrable_Gamma_of_half_le hhalf
  · let d := c + 1
    have hdHalf : (1 / 2 : ℝ) ≤ d := by
      dsimp [d]
      linarith
    have hshift :
        Integrable
          (fun t : ℝ => Complex.Gamma ((d : ℂ) + t * Complex.I)) :=
      classicalDetector_verticalIntegrable_Gamma_of_half_le hdHalf
    have hmajor :
        Integrable
          (fun t : ℝ =>
            (1 / c : ℝ) *
              ‖Complex.Gamma ((d : ℂ) + t * Complex.I)‖) :=
      hshift.norm.const_mul (1 / c : ℝ)
    change
      Integrable
        (fun t : ℝ => Complex.Gamma ((c : ℂ) + t * Complex.I))
    refine hmajor.mono'
      (classicalDetector_continuous_Gamma_vertical hc).aestronglyMeasurable
      (ae_of_all _ fun t => ?_)
    let z : ℂ := (c : ℂ) + t * Complex.I
    have hz : z ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp [z] at hre
      linarith
    have hzNorm : c ≤ ‖z‖ := by
      calc
        c = |z.re| := by simp [z, abs_of_pos hc]
        _ ≤ ‖z‖ := Complex.abs_re_le_norm z
    have hzadd :
        z + 1 = (d : ℂ) + t * Complex.I := by
      dsimp [z, d]
      push_cast
      ring
    have hshiftNorm :
        ‖Complex.Gamma ((d : ℂ) + t * Complex.I)‖ =
          ‖z‖ * ‖Complex.Gamma z‖ := by
      rw [← hzadd, Complex.Gamma_add_one z hz, norm_mul]
    have hmul :
        c * ‖Complex.Gamma z‖ ≤
          ‖Complex.Gamma ((d : ℂ) + t * Complex.I)‖ := by
      rw [hshiftNorm]
      exact mul_le_mul_of_nonneg_right hzNorm (norm_nonneg _)
    have hdiv :
        ‖Complex.Gamma z‖ ≤
          (1 / c) * ‖Complex.Gamma ((d : ℂ) + t * Complex.I)‖ := by
      rw [one_div, inv_mul_eq_div]
      exact (le_div_iff₀ hc).2 (by simpa [mul_comm] using hmul)
    simpa [z] using hdiv

theorem exp_eq_inverseMellin_Gamma
    {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    (Real.exp (-x) : ℂ) =
      (1 / (2 * Real.pi) : ℝ) *
        ∫ t : ℝ,
          (x : ℂ) ^ (-(c + t * Complex.I)) *
            Complex.Gamma (c + t * Complex.I) := by
  let f : ℝ → ℂ := fun u => (Real.exp (-u) : ℂ)
  have hf : MellinConvergent f c := by
    simpa [f, MellinConvergent, smul_eq_mul, mul_comm] using
      (Complex.GammaIntegral_convergent
        (s := (c : ℂ)) (by simpa using hc))
  have hmellin (t : ℝ) :
      mellin f (c + t * Complex.I) =
        Complex.Gamma (c + t * Complex.I) := by
    rw [← Complex.GammaIntegral_eq_mellin]
    exact (Complex.Gamma_eq_integral (by simpa using hc)).symm
  have hmellin_exp (t : ℝ) :
      mellin (fun u : ℝ => (Real.exp (-u) : ℂ))
          (c + t * Complex.I) =
        Complex.Gamma (c + t * Complex.I) := by
    simpa [f] using hmellin t
  have hmellin_cexp (t : ℝ) :
      mellin (fun u : ℝ => Complex.exp (-(u : ℂ)))
          (c + t * Complex.I) =
        Complex.Gamma (c + t * Complex.I) := by
    simpa using hmellin_exp t
  have hvertical :
      Complex.VerticalIntegrable (mellin f) c := by
    have hgamma := verticalIntegrable_Gamma_of_pos hc
    refine hgamma.congr (ae_of_all _ fun t => ?_)
    exact (hmellin t).symm
  have hinversion :=
    mellinInv_mellin_eq c f hx hf hvertical
      (by dsimp [f]; fun_prop)
  simpa [mellinInv, f, smul_eq_mul, hmellin_cexp] using hinversion.symm

private theorem classicalDetector_div_cpow_neg
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (w : ℂ) :
    (((a / b : ℝ) : ℂ) ^ (-w)) =
      (b : ℂ) ^ w * (a : ℂ) ^ (-w) := by
  have hbarg : ((b : ℂ).arg) ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hb.le]
    exact ne_of_lt Real.pi_pos
  rw [div_eq_mul_inv, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg ha (inv_nonneg.mpr hb.le),
    Complex.ofReal_inv, Complex.inv_cpow _ _ hbarg]
  simp only [Complex.cpow_neg, inv_inv]
  ring

private def classicalDetectorInverseMellinLineTerm
    (M : ℕ) (z : ℂ) (Y c : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  let w : ℂ := c + t * Complex.I
  (Y : ℂ) ^ w * Complex.Gamma w *
    LSeries.term (classicalDetectorCoefficient M) (z + w) n

private theorem continuous_classicalDetectorInverseMellinLineTerm
    (M : ℕ) (z : ℂ) {Y c : ℝ} (hY : 0 < Y) (hc : 0 < c)
    (n : ℕ) :
    Continuous (classicalDetectorInverseMellinLineTerm M z Y c n) := by
  by_cases hn : n = 0
  · subst n
    rw [show classicalDetectorInverseMellinLineTerm M z Y c 0 =
      (fun _ : ℝ => 0) by
        funext t
        simp [classicalDetectorInverseMellinLineTerm]]
    fun_prop
  · have hYne : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hYpow :
        Continuous (fun t : ℝ => (Y : ℂ) ^ (c + t * Complex.I)) := by
      rw [continuous_iff_continuousAt]
      intro t
      have hinner :
          ContinuousAt (fun y : ℝ => (c : ℂ) + y * Complex.I) t := by
        fun_prop
      have hcomp := ContinuousAt.comp
        (f := fun y : ℝ => (c : ℂ) + y * Complex.I)
        (x := t) (continuousAt_const_cpow hYne) hinner
      simpa [Function.comp_def] using hcomp
    have hnpow :
        Continuous
          (fun t : ℝ => (n : ℂ) ^ (z + (c + t * Complex.I))) := by
      rw [continuous_iff_continuousAt]
      intro t
      have hinner :
          ContinuousAt
            (fun y : ℝ => z + ((c : ℂ) + y * Complex.I)) t := by
        fun_prop
      have hcomp := ContinuousAt.comp
        (f := fun y : ℝ => z + ((c : ℂ) + y * Complex.I))
        (x := t) (continuousAt_const_cpow hnC) hinner
      simpa [Function.comp_def] using hcomp
    have hterm :
        Continuous
          (fun t : ℝ =>
            LSeries.term (classicalDetectorCoefficient M)
              (z + (c + t * Complex.I)) n) := by
      simp_rw [LSeries.term_of_ne_zero hn]
      exact continuous_const.div hnpow
        (fun _ => Complex.cpow_ne_zero_iff.mpr (Or.inl hnC))
    exact hYpow.mul
      (classicalDetector_continuous_Gamma_vertical hc) |>.mul hterm

private theorem norm_classicalDetectorInverseMellinLineTerm
    (M : ℕ) (z : ℂ) {Y c : ℝ} (hY : 0 < Y)
    (n : ℕ) (t : ℝ) :
    ‖classicalDetectorInverseMellinLineTerm M z Y c n t‖ =
      (Y ^ c) *
        ‖LSeries.term (classicalDetectorCoefficient M) (z + c) n‖ *
          ‖Complex.Gamma (c + t * Complex.I)‖ := by
  have hterm :
      ‖LSeries.term (classicalDetectorCoefficient M)
          (z + (c + t * Complex.I)) n‖ =
        ‖LSeries.term (classicalDetectorCoefficient M) (z + c) n‖ := by
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, mul_zero, Complex.ofReal_im,
      zero_mul, sub_zero, add_zero]
  rw [classicalDetectorInverseMellinLineTerm, norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hY, hterm]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, mul_zero, Complex.ofReal_im,
    zero_mul, sub_zero, add_zero]
  ring

private theorem integrable_classicalDetectorInverseMellinLineTerm
    (M : ℕ) (z : ℂ) {Y c : ℝ} (hY : 0 < Y) (hc : 0 < c)
    (n : ℕ) :
    Integrable (classicalDetectorInverseMellinLineTerm M z Y c n) := by
  have hgamma := (verticalIntegrable_Gamma_of_pos hc).norm
  have hmajor :
      Integrable
        (fun t : ℝ =>
          ((Y ^ c) *
            ‖LSeries.term (classicalDetectorCoefficient M) (z + c) n‖) *
              ‖Complex.Gamma (c + t * Complex.I)‖) :=
    hgamma.const_mul
      ((Y ^ c) *
        ‖LSeries.term (classicalDetectorCoefficient M) (z + c) n‖)
  refine hmajor.mono'
    (continuous_classicalDetectorInverseMellinLineTerm M z hY hc n).aestronglyMeasurable
    (ae_of_all _ fun t => ?_)
  exact le_of_eq (norm_classicalDetectorInverseMellinLineTerm M z hY n t)

private theorem integral_norm_classicalDetectorInverseMellinLineTerm
    (M : ℕ) (z : ℂ) {Y c : ℝ} (hY : 0 < Y) (n : ℕ) :
    (∫ t : ℝ, ‖classicalDetectorInverseMellinLineTerm M z Y c n t‖) =
      ((Y ^ c) *
        ∫ t : ℝ, ‖Complex.Gamma (c + t * Complex.I)‖) *
          ‖LSeries.term (classicalDetectorCoefficient M) (z + c) n‖ := by
  simp_rw [norm_classicalDetectorInverseMellinLineTerm M z hY n]
  rw [MeasureTheory.integral_const_mul]
  ring

private theorem summable_integral_norm_classicalDetectorInverseMellinLineTerm
    (M : ℕ) (z : ℂ) {Y c : ℝ} (hY : 0 < Y)
    (hzc : 1 < (z + c).re) :
    Summable
      (fun n : ℕ =>
        ∫ t : ℝ, ‖classicalDetectorInverseMellinLineTerm M z Y c n t‖) := by
  have hbase :=
    (LSeriesSummable_classicalDetectorCoefficient hzc M).norm
  apply Summable.congr
    (hbase.mul_left
      ((Y ^ c) *
        ∫ t : ℝ, ‖Complex.Gamma (c + t * Complex.I)‖))
  intro n
  rw [integral_norm_classicalDetectorInverseMellinLineTerm M z hY n]

private theorem tsum_classicalDetectorInverseMellinLineTerm_eq_LSeries
    (M : ℕ) (z : ℂ) (Y c t : ℝ) :
    (∑' n : ℕ, classicalDetectorInverseMellinLineTerm M z Y c n t) =
      (Y : ℂ) ^ (c + t * Complex.I) *
        Complex.Gamma (c + t * Complex.I) *
          LSeries (classicalDetectorCoefficient M)
            (z + (c + t * Complex.I)) := by
  simp only [classicalDetectorInverseMellinLineTerm, LSeries, tsum_mul_left]

private theorem tsum_classicalDetectorInverseMellinLineTerm_eq_contourFactor
    (M : ℕ) (z : ℂ) (Y c t : ℝ)
    (hzc : 1 < (z + c).re) :
    (∑' n : ℕ, classicalDetectorInverseMellinLineTerm M z Y c n t) =
      classicalDetectorMellinContourFactor M z Y
        (c + t * Complex.I) := by
  rw [tsum_classicalDetectorInverseMellinLineTerm_eq_LSeries]
  have hline :
      1 < (z + (c + t * Complex.I)).re := by
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, mul_zero, Complex.ofReal_im,
      zero_mul, sub_zero, add_zero] using hzc
  rw [LSeries_classicalDetectorCoefficient_eq hline M]
  simp [classicalDetectorMellinContourFactor]
  ring

private theorem classicalDetectorSmoothedTerm_eq_integral_inverseMellinLineTerm
    (M : ℕ) (z : ℂ) {Y c : ℝ} (hY : 0 < Y) (hc : 0 < c)
    (n : ℕ) :
    classicalDetectorSmoothedTerm M Y z n =
      (1 / (2 * Real.pi) : ℝ) *
        ∫ t : ℝ, classicalDetectorInverseMellinLineTerm M z Y c n t := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [classicalDetectorSmoothedTerm,
      classicalDetectorInverseMellinLineTerm, LSeries.term]
  · have hnPos : 0 < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hn
    have hx : 0 < (n : ℝ) / Y := div_pos hnPos hY
    have hfun :
        classicalDetectorInverseMellinLineTerm M z Y c n =
          (fun t : ℝ =>
            LSeries.term (classicalDetectorCoefficient M) z n *
              ((((n : ℝ) / Y : ℝ) : ℂ) ^
                  (-(c + t * Complex.I)) *
                Complex.Gamma (c + t * Complex.I))) := by
      funext t
      let w : ℂ := c + t * Complex.I
      rw [classicalDetectorInverseMellinLineTerm,
        ← classicalDetectorTerm_div_frequency_cpow M z w n]
      change
        (Y : ℂ) ^ w * Complex.Gamma w *
            (LSeries.term (classicalDetectorCoefficient M) z n /
              (n : ℂ) ^ w) =
          LSeries.term (classicalDetectorCoefficient M) z n *
            (((((n : ℝ) / Y : ℝ) : ℂ) ^ (-w)) *
              Complex.Gamma w)
      rw [classicalDetector_div_cpow_neg hnPos.le hY w, Complex.cpow_neg]
      push_cast
      ring
    have hinversion :=
      exp_eq_inverseMellin_Gamma hc hx
    have hinversionC :
        Complex.exp (-(((n : ℝ) : ℂ) / (Y : ℂ))) =
          ((1 / (2 * Real.pi) : ℝ) *
            ∫ t : ℝ,
              ((((n : ℝ) / Y : ℝ) : ℂ) ^
                  (-(c + t * Complex.I)) *
                Complex.Gamma (c + t * Complex.I))) := by
      simpa using hinversion
    rw [classicalDetectorSmoothedTerm, hfun,
      MeasureTheory.integral_const_mul]
    calc
      LSeries.term (classicalDetectorCoefficient M) z n *
          Complex.exp (-((n : ℝ) / Y)) =
        LSeries.term (classicalDetectorCoefficient M) z n *
          ((1 / (2 * Real.pi) : ℝ) *
            ∫ t : ℝ,
              ((((n : ℝ) / Y : ℝ) : ℂ) ^
                  (-(c + t * Complex.I)) *
                Complex.Gamma (c + t * Complex.I))) := by
            rw [hinversionC]
      _ = (1 / (2 * Real.pi) : ℝ) *
          (LSeries.term (classicalDetectorCoefficient M) z n *
            ∫ t : ℝ,
              ((((n : ℝ) / Y : ℝ) : ℂ) ^
                  (-(c + t * Complex.I)) *
                Complex.Gamma (c + t * Complex.I))) := by
            push_cast
            ring

theorem classicalDetectorInverseMellinLine :
    ClassicalDetectorInverseMellinLine := by
  intro M z Y c hY hc hzc
  have hzc' : 1 < (z + c).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  have hHasSum :=
    MeasureTheory.hasSum_integral_of_summable_integral_norm
      (fun n : ℕ =>
        integrable_classicalDetectorInverseMellinLineTerm M z hY hc n)
      (summable_integral_norm_classicalDetectorInverseMellinLineTerm
        M z hY hzc')
  rw [classicalDetectorSmoothedSeries]
  calc
    (∑' n : ℕ, classicalDetectorSmoothedTerm M Y z n) =
        ∑' n : ℕ,
          (1 / (2 * Real.pi) : ℝ) *
            ∫ t : ℝ,
              classicalDetectorInverseMellinLineTerm M z Y c n t := by
      apply tsum_congr
      intro n
      exact classicalDetectorSmoothedTerm_eq_integral_inverseMellinLineTerm
        M z hY hc n
    _ = (1 / (2 * Real.pi) : ℝ) *
        ∑' n : ℕ,
          ∫ t : ℝ,
            classicalDetectorInverseMellinLineTerm M z Y c n t := tsum_mul_left
    _ = (1 / (2 * Real.pi) : ℝ) *
        ∫ t : ℝ,
          ∑' n : ℕ,
            classicalDetectorInverseMellinLineTerm M z Y c n t := by
      rw [hHasSum.tsum_eq]
    _ = (1 / (2 * Real.pi) : ℝ) *
        ∫ t : ℝ,
          classicalDetectorMellinContourFactor M z Y
            (c + t * Complex.I) := by
      congr 1
      apply MeasureTheory.integral_congr_ae
      exact ae_of_all _ fun t =>
        tsum_classicalDetectorInverseMellinLineTerm_eq_contourFactor
          M z Y c t hzc'
    _ = classicalDetectorMellinLineIntegral M z Y c := by
      rfl

end

end LeanLab.Riemann
