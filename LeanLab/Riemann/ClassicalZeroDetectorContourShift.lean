import LeanLab.Riemann.ClassicalZeroDetectorInverseMellin
import LeanLab.Riemann.HardyComplexAlpha
import LeanLab.Riemann.ReciprocalZetaSubpower
import LeanLab.Riemann.WeilZeroCutoff

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The classical zero-detector contour shift

This module shifts the actual Gamma--Mobius--zeta inverse-Mellin line across the translated
zeta pole. The pole of Gamma at zero is removed by the actual zeta-zero condition; no
simple-zero hypothesis is used.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators Interval

namespace LeanLab.Riemann

/-- The holomorphic numerator left after removing both displayed denominators from the source
contour factor. -/
def classicalDetectorContourWeight
    (M : ℕ) (rho : ℂ) (Y : ℝ) (w : ℂ) : ℂ :=
  (Y : ℂ) ^ w *
    classicalDetectorMollifier M (rho + w) *
    Complex.Gamma (w + 1) *
    dslope zetaPoleRemoved rho (rho + w)

/-- The source contour factor with the canceled Gamma pole filled in and only the translated
zeta pole retained. -/
def classicalDetectorExtendedContourFactor
    (M : ℕ) (rho : ℂ) (Y : ℝ) (w : ℂ) : ℂ :=
  classicalDetectorContourWeight M rho Y w / (w - (1 - rho))

theorem differentiable_classicalDetectorMollifier (M : ℕ) :
    Differentiable ℂ (classicalDetectorMollifier M) := by
  rw [funext (classicalDetectorMollifier_eq_mobiusDirichletPartialSum M)]
  change Differentiable ℂ (fun s : ℂ =>
    ∑ n ∈ Finset.Icc 1 M,
      ((ArithmeticFunction.moebius n : ℤ) : ℂ) * (n : ℂ) ^ (-s))
  apply Differentiable.fun_sum
  intro n hn
  have hn0N : n ≠ 0 := by
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    omega
  have hn0C : (n : ℂ) ≠ 0 := by
    exact_mod_cast hn0N
  exact (differentiable_const
      (c := (((ArithmeticFunction.moebius n : ℤ) : ℂ)))).mul
    (differentiable_id.neg.const_cpow (Or.inl hn0C))

/-- The finite Mobius polynomial is uniformly bounded on the closed half-strip used after the
contour shift. -/
theorem norm_classicalDetectorMollifier_le_nat
    (M : ℕ) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖classicalDetectorMollifier M s‖ ≤ M := by
  rw [classicalDetectorMollifier_eq_mobiusDirichletPartialSum]
  change ‖∑ n ∈ Finset.Icc 1 M,
      ((ArithmeticFunction.moebius n : ℤ) : ℂ) * (n : ℂ) ^ (-s)‖ ≤ M
  calc
    ‖∑ n ∈ Finset.Icc 1 M,
        ((ArithmeticFunction.moebius n : ℤ) : ℂ) * (n : ℂ) ^ (-s)‖
        ≤ ∑ n ∈ Finset.Icc 1 M,
            ‖((ArithmeticFunction.moebius n : ℤ) : ℂ) *
              (n : ℂ) ^ (-s)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 M, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      calc
        ‖((ArithmeticFunction.moebius n : ℤ) : ℂ) * (n : ℂ) ^ (-s)‖
            ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
          simpa only [neg_div] using norm_mobius_mul_nat_cpow_neg_le hs n
        _ ≤ 1 := by
          have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
          exact Real.rpow_le_one_of_one_le_of_nonpos hn1R (by norm_num)
    _ = M := by simp

/-- Positive-strip Gamma ratios transport the exact half-line exponential decay uniformly
across the complete real-part interval needed by the source rectangle. -/
theorem exists_norm_Gamma_add_one_classicalDetectorStrip_le :
    ∃ p : ℝ, 0 < p ∧
      ∀ (x t : ℝ), x ∈ Set.Icc (-1 / 2 : ℝ) 2 →
        ‖Complex.Gamma (((x + 1 : ℝ) : ℂ) + t * Complex.I)‖ ≤
          3 * (|t| + 2) ^ p *
            Real.exp (-(Real.pi / 2) * |t|) := by
  obtain ⟨C, hC, hratio⟩ :=
    exists_norm_Gamma_div_le_rpow_of_re_mem_Icc
      (1 / 2 : ℝ) 3 (by norm_num)
  let p : ℝ := C * (5 / 2)
  have hp : 0 < p := by
    dsimp only [p]
    positivity
  refine ⟨p, hp, ?_⟩
  intro x t hx
  let z0 : ℂ := ((1 / 2 : ℝ) : ℂ) + t * Complex.I
  let δ : ℝ := x + 1 / 2
  have hδ : 0 ≤ δ := by
    dsimp only [δ]
    linarith [hx.1]
  have hδUpper : δ ≤ 5 / 2 := by
    dsimp only [δ]
    linarith [hx.2]
  have hratioRaw :
      ‖Complex.Gamma (z0 + δ) / Complex.Gamma z0‖ ≤
        (|z0.im| + 2) ^ (C * δ) := by
    apply hratio z0 δ
    · simp [z0]
    · norm_num [z0, δ]
      linarith [hx.2]
    · exact hδ
  have hbase : 1 ≤ |t| + 2 := by
    linarith [abs_nonneg t]
  have hexponent : C * δ ≤ p := by
    dsimp only [p]
    exact mul_le_mul_of_nonneg_left hδUpper hC.le
  have hratioBound :
      ‖Complex.Gamma (z0 + δ) / Complex.Gamma z0‖ ≤
        (|t| + 2) ^ p := by
    calc
      ‖Complex.Gamma (z0 + δ) / Complex.Gamma z0‖
          ≤ (|z0.im| + 2) ^ (C * δ) := hratioRaw
      _ = (|t| + 2) ^ (C * δ) := by simp [z0]
      _ ≤ (|t| + 2) ^ p :=
        Real.rpow_le_rpow_of_exponent_le hbase hexponent
  have hz0Gamma : Complex.Gamma z0 ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    simp [z0]
  have hshift : z0 + δ = (((x + 1 : ℝ) : ℂ) + t * Complex.I) := by
    dsimp only [z0, δ]
    push_cast
    ring
  calc
    ‖Complex.Gamma (((x + 1 : ℝ) : ℂ) + t * Complex.I)‖
        = ‖Complex.Gamma (z0 + δ)‖ := by rw [hshift]
    _ = ‖Complex.Gamma (z0 + δ) / Complex.Gamma z0‖ *
          ‖Complex.Gamma z0‖ := by
      rw [← norm_mul, div_mul_cancel₀ _ hz0Gamma]
    _ ≤ (|t| + 2) ^ p *
          ‖Complex.Gamma z0‖ :=
      mul_le_mul_of_nonneg_right hratioBound (norm_nonneg _)
    _ ≤ (|t| + 2) ^ p *
          (3 * Real.exp (-(Real.pi / 2) * |t|)) := by
      gcongr
      simpa only [z0] using norm_Gamma_half_add_mul_I_le_exp_pi t
    _ = 3 * (|t| + 2) ^ p *
          Real.exp (-(Real.pi / 2) * |t|) := by ring

/-- The positive smoothing power is uniformly bounded across the finite horizontal side. -/
theorem norm_classicalDetector_cpow_le
    {rho : ℂ} {Y : ℝ} (hY : 0 < Y)
    {x : ℝ} (hx : x ∈ Set.Icc (1 / 2 - rho.re) 2) (t : ℝ) :
    ‖(Y : ℂ) ^ (((x : ℂ) + t * Complex.I))‖ ≤
      max (Y ^ (1 / 2 - rho.re)) (Y ^ (2 : ℝ)) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hY]
  have hre : (((x : ℂ) + t * Complex.I)).re = x := by
    simp [Complex.mul_re]
  rw [hre]
  rcases le_total Y 1 with hYOne | hOneY
  · exact (Real.rpow_le_rpow_of_exponent_ge hY hYOne hx.1).trans
      (le_max_left _ _)
  · exact (Real.rpow_le_rpow_of_exponent_le hOneY hx.2).trans
      (le_max_right _ _)

/-- Polynomial zeta growth is uniform on every horizontal side of the source rectangle once
the height dominates the fixed ordinate of the selected zero. -/
theorem norm_riemannZeta_classicalDetector_horizontal_le
    {rho : ℂ} (hrho : IsNontrivialZero rho)
    {x T : ℝ} (hx : x ∈ Set.Icc (1 / 2 - rho.re) 2)
    (hT : 1 + |rho.im| ≤ |T|) :
    ‖riemannZeta (rho + ((x : ℂ) + T * Complex.I))‖ ≤
      20 * (1 + |rho.im|) * (|T| + 2) := by
  let s : ℂ := rho + ((x : ℂ) + T * Complex.I)
  have hsRe : s.re = rho.re + x := by
    simp [s, Complex.mul_re]
  have hsIm : s.im = rho.im + T := by
    simp [s, Complex.mul_im]
  have hre : s.re ∈ Set.Icc (1 / 2 : ℝ) 8 := by
    rw [hsRe]
    constructor
    · linarith [hx.1]
    · linarith [hx.2, nontrivial_zero_re_lt_one hrho]
  have htriangle : |T| ≤ |rho.im + T| + |rho.im| := by
    calc
      |T| = |(rho.im + T) + (-rho.im)| := by ring_nf
      _ ≤ |rho.im + T| + |-rho.im| := abs_add_le _ _
      _ = |rho.im + T| + |rho.im| := by rw [abs_neg]
  have him : 1 ≤ |s.im| := by
    rw [hsIm]
    linarith
  have hsource := norm_riemannZeta_le_linear_of_re_mem_Icc hre him
  have himUpper : 1 + |s.im| ≤
      (1 + |rho.im|) * (|T| + 2) := by
    rw [hsIm]
    have hadd := abs_add_le rho.im T
    nlinarith [abs_nonneg rho.im, abs_nonneg T]
  calc
    ‖riemannZeta (rho + ((x : ℂ) + T * Complex.I))‖ =
        ‖riemannZeta s‖ := rfl
    _ ≤ 20 * (1 + |s.im|) := hsource
    _ ≤ 20 * ((1 + |rho.im|) * (|T| + 2)) := by
      gcongr
    _ = 20 * (1 + |rho.im|) * (|T| + 2) := by ring

/-- Gamma recurrence moves the slightly negative shifted strip into the positive strip without
losing the uniform exponential decay at large height. -/
theorem exists_norm_Gamma_classicalDetectorStrip_le :
    ∃ p : ℝ, 0 < p ∧
      ∀ {rho : ℂ}, IsNontrivialZero rho →
        ∀ (x T : ℝ), x ∈ Set.Icc (1 / 2 - rho.re) 2 → 1 ≤ |T| →
          ‖Complex.Gamma (((x : ℂ) + T * Complex.I))‖ ≤
            3 * (|T| + 2) ^ p *
              Real.exp (-(Real.pi / 2) * |T|) := by
  obtain ⟨p, hp, hstrip⟩ :=
    exists_norm_Gamma_add_one_classicalDetectorStrip_le
  refine ⟨p, hp, ?_⟩
  intro rho hrho x T hx hT
  let w : ℂ := (x : ℂ) + T * Complex.I
  have hxLower : -1 / 2 ≤ x := by
    linarith [hx.1, nontrivial_zero_re_lt_one hrho]
  have hxStrip : x ∈ Set.Icc (-1 / 2 : ℝ) 2 :=
    ⟨hxLower, hx.2⟩
  have hwNorm : 1 ≤ ‖w‖ := by
    calc
      1 ≤ |T| := hT
      _ = |w.im| := by simp [w, Complex.mul_im]
      _ ≤ ‖w‖ := Complex.abs_im_le_norm w
  have hw : w ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans_le hwNorm)
  have hrec :
      ‖Complex.Gamma (w + 1)‖ =
        ‖w‖ * ‖Complex.Gamma w‖ := by
    rw [Complex.Gamma_add_one w hw, norm_mul]
  have hGammaLe :
      ‖Complex.Gamma w‖ ≤ ‖Complex.Gamma (w + 1)‖ := by
    rw [hrec]
    exact le_mul_of_one_le_left (norm_nonneg _) hwNorm
  have hshift : w + 1 = (((x + 1 : ℝ) : ℂ) + T * Complex.I) := by
    dsimp only [w]
    push_cast
    ring
  calc
    ‖Complex.Gamma (((x : ℂ) + T * Complex.I))‖ =
        ‖Complex.Gamma w‖ := rfl
    _ ≤ ‖Complex.Gamma (w + 1)‖ := hGammaLe
    _ = ‖Complex.Gamma (((x + 1 : ℝ) : ℂ) + T * Complex.I)‖ := by
      rw [hshift]
    _ ≤ 3 * (|T| + 2) ^ p *
          Real.exp (-(Real.pi / 2) * |T|) :=
      hstrip x T hxStrip

/-- A fixed nonnegative constant collecting the finite smoothing and arithmetic factors on the
source horizontal strip. -/
def classicalDetectorHorizontalBound (M : ℕ) (rho : ℂ) (Y : ℝ) : ℝ :=
  60 * (M : ℝ) * (1 + |rho.im|) *
    max (Y ^ (1 / 2 - rho.re)) (Y ^ (2 : ℝ))

theorem classicalDetectorHorizontalBound_nonneg
    (M : ℕ) (rho : ℂ) {Y : ℝ} (hY : 0 < Y) :
    0 ≤ classicalDetectorHorizontalBound M rho Y := by
  dsimp only [classicalDetectorHorizontalBound]
  positivity

/-- The actual Gamma--Mobius--zeta factor has polynomial-times-exponential decay uniformly
across the complete horizontal side of the shifted rectangle. -/
theorem exists_norm_classicalDetectorMellinContourFactor_horizontal_le
    (M : ℕ) {rho : ℂ} (hrho : IsNontrivialZero rho) {Y : ℝ} (hY : 0 < Y) :
    ∃ p : ℝ, 0 < p ∧
      ∀ (x T : ℝ), x ∈ Set.Icc (1 / 2 - rho.re) 2 →
        1 + |rho.im| ≤ |T| →
        ‖classicalDetectorMellinContourFactor M rho Y
          ((x : ℂ) + T * Complex.I)‖ ≤
          classicalDetectorHorizontalBound M rho Y *
            (|T| + 2) ^ p *
            Real.exp (-(Real.pi / 2) * |T|) := by
  obtain ⟨q, hq, hgamma⟩ :=
    exists_norm_Gamma_classicalDetectorStrip_le
  let p : ℝ := q + 1
  have hp : 0 < p := by
    dsimp only [p]
    linarith
  refine ⟨p, hp, ?_⟩
  intro x T hx hT
  let w : ℂ := (x : ℂ) + T * Complex.I
  have hpower :
      ‖(Y : ℂ) ^ w‖ ≤
        max (Y ^ (1 / 2 - rho.re)) (Y ^ (2 : ℝ)) := by
    exact norm_classicalDetector_cpow_le hY hx T
  have hgamma' :
      ‖Complex.Gamma w‖ ≤
        3 * (|T| + 2) ^ q *
          Real.exp (-(Real.pi / 2) * |T|) := by
    exact hgamma hrho x T hx (by linarith [abs_nonneg rho.im])
  have hmollifier :
      ‖classicalDetectorMollifier M (rho + w)‖ ≤ M := by
    apply norm_classicalDetectorMollifier_le_nat
    dsimp only [w]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    linarith [hx.1]
  have hzeta :
      ‖riemannZeta (rho + w)‖ ≤
        20 * (1 + |rho.im|) * (|T| + 2) := by
    exact norm_riemannZeta_classicalDetector_horizontal_le hrho hx hT
  have hbasePos : 0 < |T| + 2 := by positivity
  rw [classicalDetectorMellinContourFactor]
  simp only [norm_mul]
  calc
    ‖(Y : ℂ) ^ w‖ * ‖Complex.Gamma w‖ *
          ‖classicalDetectorMollifier M (rho + w)‖ *
          ‖riemannZeta (rho + w)‖
        ≤ max (Y ^ (1 / 2 - rho.re)) (Y ^ (2 : ℝ)) *
            (3 * (|T| + 2) ^ q *
              Real.exp (-(Real.pi / 2) * |T|)) *
            (M : ℝ) *
            (20 * (1 + |rho.im|) * (|T| + 2)) := by
          gcongr
    _ = classicalDetectorHorizontalBound M rho Y *
          (|T| + 2) ^ p *
          Real.exp (-(Real.pi / 2) * |T|) := by
      rw [show p = q + 1 by rfl, Real.rpow_add hbasePos,
        Real.rpow_one]
      dsimp only [classicalDetectorHorizontalBound]
      ring

/-- A translated polynomial times a negative exponential still tends to zero. -/
theorem tendsto_add_two_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (p a : ℝ) (ha : 0 < a) :
    Tendsto
      (fun u : ℝ => (u + 2) ^ p * Real.exp (-a * u))
      atTop (nhds 0) := by
  have hshift : Tendsto (fun u : ℝ => u + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_id
  have hcore :
      Tendsto
        (fun u : ℝ =>
          (u + 2) ^ p * Real.exp (-a * (u + 2)))
        atTop (nhds 0) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p a ha).comp hshift
  have hscaled :=
    (tendsto_const_nhds :
      Tendsto (fun _ : ℝ => Real.exp (2 * a)) atTop
        (nhds (Real.exp (2 * a)))).mul hcore
  convert hscaled using 1
  · funext u
    have hexp :
        Real.exp (-a * u) =
          Real.exp (2 * a) * Real.exp (-a * (u + 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp]
    ring
  · simp

/-- The horizontal interval integral inherits the uniform actual-factor majorant. -/
theorem exists_norm_integral_classicalDetectorMellinContourFactor_horizontal_le
    (M : ℕ) {rho : ℂ} (hrho : IsNontrivialZero rho) {Y : ℝ} (hY : 0 < Y) :
    ∃ p : ℝ, 0 < p ∧
      ∀ T : ℝ, 1 + |rho.im| ≤ |T| →
        ‖∫ x : ℝ in (1 / 2 - rho.re)..2,
          classicalDetectorMellinContourFactor M rho Y
            ((x : ℂ) + T * Complex.I)‖ ≤
          (3 / 2 + rho.re) *
            classicalDetectorHorizontalBound M rho Y *
            (|T| + 2) ^ p *
            Real.exp (-(Real.pi / 2) * |T|) := by
  obtain ⟨p, hp, hfactor⟩ :=
    exists_norm_classicalDetectorMellinContourFactor_horizontal_le
      M hrho hY
  refine ⟨p, hp, ?_⟩
  intro T hT
  have hleftRight : 1 / 2 - rho.re ≤ (2 : ℝ) := by
    linarith [nontrivial_zero_re_pos hrho]
  let C : ℝ :=
    classicalDetectorHorizontalBound M rho Y *
      (|T| + 2) ^ p *
      Real.exp (-(Real.pi / 2) * |T|)
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (1 / 2 - rho.re : ℝ)) (b := 2)
    (f := fun x : ℝ =>
      classicalDetectorMellinContourFactor M rho Y
        ((x : ℂ) + T * Complex.I))
    (C := C)
    (fun x hx => by
      apply hfactor x T
      · have hx' := Set.uIoc_subset_uIcc hx
        rw [uIcc_of_le hleftRight] at hx'
        exact hx'
      · exact hT)
  rw [abs_of_nonneg (sub_nonneg.mpr hleftRight)] at hbound
  calc
    ‖∫ x : ℝ in (1 / 2 - rho.re)..2,
        classicalDetectorMellinContourFactor M rho Y
          ((x : ℂ) + T * Complex.I)‖
        ≤ C * (2 - (1 / 2 - rho.re)) := hbound
    _ = (3 / 2 + rho.re) *
          classicalDetectorHorizontalBound M rho Y *
          (|T| + 2) ^ p *
          Real.exp (-(Real.pi / 2) * |T|) := by
      dsimp only [C]
      ring

/-- Any pair of horizontal heights escaping in absolute value gives a vanishing source edge. -/
theorem
    tendsto_integral_classicalDetectorMellinContourFactor_horizontal_of_abs_atTop
    (M : ℕ) {rho : ℂ} (hrho : IsNontrivialZero rho) {Y : ℝ} (hY : 0 < Y)
    {v : ℝ → ℝ} (hv : Tendsto (fun T => |v T|) atTop atTop) :
    Tendsto
      (fun T : ℝ => ∫ x : ℝ in (1 / 2 - rho.re)..2,
        classicalDetectorMellinContourFactor M rho Y
          ((x : ℂ) + v T * Complex.I))
      atTop (nhds 0) := by
  obtain ⟨p, hp, hboundRaw⟩ :=
    exists_norm_integral_classicalDetectorMellinContourFactor_horizontal_le
      M hrho hY
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hlarge : ∀ᶠ T : ℝ in atTop, 1 + |rho.im| ≤ |v T| :=
    Filter.tendsto_atTop.1 hv (1 + |rho.im|)
  have hbound : ∀ᶠ T : ℝ in atTop,
      ‖∫ x : ℝ in (1 / 2 - rho.re)..2,
          classicalDetectorMellinContourFactor M rho Y
            ((x : ℂ) + v T * Complex.I)‖ ≤
        (3 / 2 + rho.re) *
          classicalDetectorHorizontalBound M rho Y *
          (|v T| + 2) ^ p *
          Real.exp (-(Real.pi / 2) * |v T|) := by
    filter_upwards [hlarge] with T hT
    exact hboundRaw (v T) hT
  have hdecay :
      Tendsto
        (fun u : ℝ =>
          (u + 2) ^ p * Real.exp (-(Real.pi / 2) * u))
        atTop (nhds 0) := by
    apply tendsto_add_two_rpow_mul_exp_neg_mul_atTop_nhds_zero
    positivity
  have hmajor :
      Tendsto
        (fun T : ℝ =>
          (3 / 2 + rho.re) *
            classicalDetectorHorizontalBound M rho Y *
            (|v T| + 2) ^ p *
            Real.exp (-(Real.pi / 2) * |v T|))
        atTop (nhds 0) := by
    have hconst : Tendsto
        (fun _ : ℝ =>
          (3 / 2 + rho.re) *
            classicalDetectorHorizontalBound M rho Y)
        atTop
        (nhds ((3 / 2 + rho.re) *
          classicalDetectorHorizontalBound M rho Y)) :=
      tendsto_const_nhds
    simpa only [Function.comp_apply, mul_zero, mul_assoc] using
      hconst.mul (hdecay.comp hv)
  exact squeeze_zero'
    (Eventually.of_forall fun _ => norm_nonneg _) hbound hmajor

theorem tendsto_integral_classicalDetectorMellinContourFactor_top
    (M : ℕ) {rho : ℂ} (hrho : IsNontrivialZero rho) {Y : ℝ} (hY : 0 < Y) :
    Tendsto
      (fun T : ℝ => ∫ x : ℝ in (1 / 2 - rho.re)..2,
        classicalDetectorMellinContourFactor M rho Y
          ((x : ℂ) + T * Complex.I))
      atTop (nhds 0) := by
  exact
    tendsto_integral_classicalDetectorMellinContourFactor_horizontal_of_abs_atTop
      M hrho hY tendsto_abs_atTop_atTop

theorem tendsto_integral_classicalDetectorMellinContourFactor_bottom
    (M : ℕ) {rho : ℂ} (hrho : IsNontrivialZero rho) {Y : ℝ} (hY : 0 < Y) :
    Tendsto
      (fun T : ℝ => ∫ x : ℝ in (1 / 2 - rho.re)..2,
        classicalDetectorMellinContourFactor M rho Y
          ((x : ℂ) + (-T) * Complex.I))
      atTop (nhds 0) := by
  have hv : Tendsto (fun T : ℝ => |-T|) atTop atTop := by
    simpa only [abs_neg] using tendsto_abs_atTop_atTop
  have h :=
    tendsto_integral_classicalDetectorMellinContourFactor_horizontal_of_abs_atTop
      (v := fun T : ℝ => -T) M hrho hY hv
  convert h using 1
  push_cast
  rfl

/-- A continuous function with inverse-square decay outside an arbitrary fixed compact interval
is integrable. -/
theorem integrable_of_continuous_norm_le_abs_inv_sq_of_large
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → E} (hg : Continuous g) (R : ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x : ℝ, R < |x| → ‖g x‖ ≤ C * (|x|⁻¹ ^ (2 : ℕ))) :
    Integrable g := by
  let j : ℝ → ℝ := fun x => (1 + |x|)⁻¹ ^ (2 : ℕ)
  have hjRaw : Integrable (fun x : ℝ => (1 + ‖x‖) ^ (-(2 : ℝ))) := by
    exact integrable_one_add_norm (by norm_num)
  have hj : Integrable j := by
    apply hjRaw.congr
    filter_upwards [] with x
    have hxpos : 0 < 1 + |x| := by positivity
    simp only [j, Real.norm_eq_abs, Real.rpow_neg hxpos.le, inv_pow]
    congr 1
    exact Real.rpow_natCast _ _
  let S : ℝ := max R 1
  have hlarge : ∀ᶠ x : ℝ in cocompact ℝ, S < |x| := by
    filter_upwards [(isCompact_closedBall (0 : ℝ) S).compl_mem_cocompact] with x hx
    simpa [Metric.mem_closedBall, Real.dist_eq] using hx
  have hO : g =O[cocompact ℝ] j := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨4 * C, ?_⟩
    filter_upwards [hlarge] with x hx
    have hxR : R < |x| := (le_max_left R 1).trans_lt hx
    have hxOne : 1 < |x| := (le_max_right R 1).trans_lt hx
    have hx0 : 0 < |x| := lt_trans zero_lt_one hxOne
    have hsum : 1 + |x| ≤ 2 * |x| := by linarith
    have hinvSum : (2 * |x|)⁻¹ ≤ (1 + |x|)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le (by positivity) hsum
    have hsq : |x|⁻¹ ^ (2 : ℕ) ≤
        4 * ((1 + |x|)⁻¹ ^ (2 : ℕ)) := by
      calc
        |x|⁻¹ ^ (2 : ℕ) =
            4 * ((2 * |x|)⁻¹ ^ (2 : ℕ)) := by
          field_simp [hx0.ne']
          ring
        _ ≤ 4 * ((1 + |x|)⁻¹ ^ (2 : ℕ)) := by gcongr
    calc
      ‖g x‖ ≤ C * (|x|⁻¹ ^ (2 : ℕ)) := hbound x hxR
      _ ≤ C * (4 * ((1 + |x|)⁻¹ ^ (2 : ℕ))) := by gcongr
      _ = (4 * C) * ‖j x‖ := by
        rw [Real.norm_of_nonneg]
        · dsimp only [j]
          ring
        · positivity
  exact hg.locallyIntegrable.integrable_of_isBigO_cocompact
    hO (hj.integrableAtFilter (cocompact ℝ))

theorem classicalDetector_pow_mul_exp_neg_le_factorial_mul_inv_sq
    (N : ℕ) {x : ℝ} (hx : 0 < x) :
    x ^ N * Real.exp (-x) ≤
      ((N + 2).factorial : ℝ) * x⁻¹ ^ (2 : ℕ) := by
  have hfactorial : 0 < ((N + 2).factorial : ℝ) := by positivity
  have hseries := Real.pow_div_factorial_le_exp x hx.le (N + 2)
  have hpow :
      x ^ (N + 2) ≤ ((N + 2).factorial : ℝ) * Real.exp x := by
    simpa [mul_comm] using (div_le_iff₀ hfactorial).mp hseries
  have hscale : 0 ≤ Real.exp (-x) * x⁻¹ ^ (2 : ℕ) := by positivity
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

/-- Every real power loss in the horizontal estimate is absorbed by the exact exponential
Gamma decay, with an inverse-square remainder suitable for Bochner integrability. -/
theorem exists_classicalDetector_add_two_rpow_mul_exp_neg_le_inv_sq
    (p : ℝ) :
    ∃ K : ℝ, 0 < K ∧
      ∀ t : ℝ, 1 < |t| →
        (|t| + 2) ^ p * Real.exp (-|t|) ≤
          K * |t|⁻¹ ^ (2 : ℕ) := by
  let N := ⌈p⌉₊
  refine ⟨3 ^ N * ((N + 2).factorial : ℝ), by positivity, ?_⟩
  intro t ht
  have htPos : 0 < |t| := lt_trans zero_lt_one ht
  have hbaseOne : 1 ≤ |t| + 2 := by linarith
  have hpN : p ≤ (N : ℝ) := Nat.le_ceil p
  have hrpow :
      (|t| + 2) ^ p ≤ (|t| + 2) ^ N := by
    calc
      (|t| + 2) ^ p ≤ (|t| + 2) ^ (N : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hbaseOne hpN
      _ = (|t| + 2) ^ N := Real.rpow_natCast _ _
  have hbase : |t| + 2 ≤ 3 * |t| := by linarith
  have hpow :
      (|t| + 2) ^ N ≤ 3 ^ N * |t| ^ N := by
    calc
      (|t| + 2) ^ N ≤ (3 * |t|) ^ N :=
        pow_le_pow_left₀ (by positivity) hbase N
      _ = 3 ^ N * |t| ^ N := by rw [mul_pow]
  calc
    (|t| + 2) ^ p * Real.exp (-|t|)
        ≤ (3 ^ N * |t| ^ N) * Real.exp (-|t|) := by
      gcongr
      exact hrpow.trans hpow
    _ = 3 ^ N * (|t| ^ N * Real.exp (-|t|)) := by ring
    _ ≤ 3 ^ N *
        (((N + 2).factorial : ℝ) * |t|⁻¹ ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_left
        (classicalDetector_pow_mul_exp_neg_le_factorial_mul_inv_sq N htPos)
        (by positivity)
    _ = (3 ^ N * ((N + 2).factorial : ℝ)) *
        |t|⁻¹ ^ (2 : ℕ) := by ring

/-- Away from the only Gamma and zeta pole real parts in the selected strip, the actual contour
factor is continuous on a complete vertical line. -/
theorem continuous_classicalDetectorMellinContourFactor_vertical
    (M : ℕ) (rho : ℂ) {Y x : ℝ} (hY : 0 < Y)
    (hxLower : -1 < x) (hxZero : x ≠ 0)
    (hsOne : rho.re + x ≠ 1) :
    Continuous (fun t : ℝ =>
      classicalDetectorMellinContourFactor M rho Y
        ((x : ℂ) + t * Complex.I)) := by
  let line : ℝ → ℂ := fun t => (x : ℂ) + t * Complex.I
  have hline : Continuous line := by
    dsimp only [line]
    fun_prop
  have hYne : (Y : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hY.ne'
  have hpower : Continuous (fun t : ℝ => (Y : ℂ) ^ line t) :=
    (continuous_iff_continuousAt.mpr fun _ =>
      continuousAt_const_cpow hYne).comp hline
  have hgamma : Continuous (fun t : ℝ => Complex.Gamma (line t)) := by
    rw [continuous_iff_continuousAt]
    intro t
    have harg : ∀ n : ℕ, line t ≠ -(n : ℂ) := by
      intro n hzero
      have hre := congrArg Complex.re hzero
      have hre' : x = -(n : ℝ) := by
        simpa [line, Complex.mul_re] using hre
      rcases eq_or_ne n 0 with rfl | hn
      · norm_num at hre'
        exact hxZero hre'
      · have hn1 : (1 : ℝ) ≤ n := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
        linarith [hre']
    exact (Complex.differentiableAt_Gamma (line t) harg).continuousAt.comp
      hline.continuousAt
  have hmollifier : Continuous (fun t : ℝ =>
      classicalDetectorMollifier M (rho + line t)) :=
    (continuous_classicalDetectorMollifier M).comp
      (continuous_const.add hline)
  have hzeta : Continuous (fun t : ℝ => riemannZeta (rho + line t)) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hargOne : rho + line t ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      simp only [line, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
        sub_zero, add_zero, Complex.one_re] at hre
      exact hsOne hre
    have hzetaAt : ContinuousAt riemannZeta (rho + line t) :=
      (differentiableAt_riemannZeta hargOne).continuousAt
    have hshift : ContinuousAt (fun z : ℂ => rho + z) (line t) := by
      fun_prop
    have hzetaShift :
        ContinuousAt (fun z : ℂ => riemannZeta (rho + z)) (line t) :=
      hzetaAt.comp hshift
    exact hzetaShift.comp hline.continuousAt
  change Continuous (fun t : ℝ =>
    (Y : ℂ) ^ line t * Complex.Gamma (line t) *
      classicalDetectorMollifier M (rho + line t) *
      riemannZeta (rho + line t))
  exact ((hpower.mul hgamma).mul hmollifier).mul hzeta

/-- The horizontal decay estimate also proves actual Bochner integrability on every
pole-avoiding vertical line in the selected strip. -/
theorem integrable_classicalDetectorMellinContourFactor_vertical
    (M : ℕ) {rho : ℂ} (hrho : IsNontrivialZero rho)
    {Y x : ℝ} (hY : 0 < Y)
    (hx : x ∈ Set.Icc (1 / 2 - rho.re) 2)
    (hxLower : -1 < x) (hxZero : x ≠ 0)
    (hsOne : rho.re + x ≠ 1) :
    Integrable (fun t : ℝ =>
      classicalDetectorMellinContourFactor M rho Y
        ((x : ℂ) + t * Complex.I)) := by
  obtain ⟨p, hp, hfactor⟩ :=
    exists_norm_classicalDetectorMellinContourFactor_horizontal_le
      M hrho hY
  obtain ⟨K, hK, hpoly⟩ :=
    exists_classicalDetector_add_two_rpow_mul_exp_neg_le_inv_sq p
  let C : ℝ := classicalDetectorHorizontalBound M rho Y * K
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg
      (classicalDetectorHorizontalBound_nonneg M rho hY) hK.le
  apply integrable_of_continuous_norm_le_abs_inv_sq_of_large
    (continuous_classicalDetectorMellinContourFactor_vertical
      M rho hY hxLower hxZero hsOne)
    (1 + |rho.im|) hC
  intro t ht
  have htOne : 1 < |t| := by
    linarith [abs_nonneg rho.im]
  have hraw := hfactor x t hx ht.le
  have hexp :
      Real.exp (-(Real.pi / 2) * |t|) ≤ Real.exp (-|t|) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.two_le_pi, abs_nonneg t]
  calc
    ‖classicalDetectorMellinContourFactor M rho Y
        ((x : ℂ) + t * Complex.I)‖
        ≤ classicalDetectorHorizontalBound M rho Y *
          (|t| + 2) ^ p *
          Real.exp (-(Real.pi / 2) * |t|) := hraw
    _ ≤ classicalDetectorHorizontalBound M rho Y *
          ((|t| + 2) ^ p * Real.exp (-|t|)) := by
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _
        (classicalDetectorHorizontalBound_nonneg M rho hY)
      exact mul_le_mul_of_nonneg_left hexp
        (Real.rpow_nonneg (by positivity) p)
    _ ≤ classicalDetectorHorizontalBound M rho Y *
          (K * |t|⁻¹ ^ (2 : ℕ)) := by
      exact mul_le_mul_of_nonneg_left (hpoly t htOne)
        (classicalDetectorHorizontalBound_nonneg M rho hY)
    _ = C * (|t|⁻¹ ^ (2 : ℕ)) := by
      dsimp only [C]
      ring

theorem integrable_classicalDetectorMellinContourFactor_right
    (M : ℕ) {rho : ℂ} (hrho : IsNontrivialZero rho)
    {Y : ℝ} (hY : 0 < Y) :
    Integrable (fun t : ℝ =>
      classicalDetectorMellinContourFactor M rho Y
        (2 + t * Complex.I)) := by
  apply integrable_classicalDetectorMellinContourFactor_vertical
    M hrho hY (x := 2)
  · exact ⟨by linarith [nontrivial_zero_re_pos hrho], le_rfl⟩
  · norm_num
  · norm_num
  · linarith [nontrivial_zero_re_pos hrho]

theorem integrable_classicalDetectorMellinContourFactor_left
    (M : ℕ) {rho : ℂ} (hrho : IsNontrivialZero rho)
    (hbeta : 1 / 2 < rho.re) {Y : ℝ} (hY : 0 < Y) :
    Integrable (fun t : ℝ =>
      classicalDetectorMellinContourFactor M rho Y
        ((1 / 2 - rho.re : ℝ) + t * Complex.I)) := by
  apply integrable_classicalDetectorMellinContourFactor_vertical
    M hrho hY (x := 1 / 2 - rho.re)
  · exact ⟨le_rfl, by linarith [nontrivial_zero_re_pos hrho]⟩
  · linarith [nontrivial_zero_re_lt_one hrho]
  · linarith
  · norm_num

/-- The source numerator is holomorphic throughout the half-plane containing the shifted
rectangle. -/
theorem differentiableOn_classicalDetectorContourWeight
    (M : ℕ) (rho : ℂ) {Y : ℝ} (hY : 0 < Y) :
    DifferentiableOn ℂ (classicalDetectorContourWeight M rho Y)
      {w : ℂ | -1 < w.re} := by
  intro w hw
  change -1 < w.re at hw
  have hYne : (Y : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hY.ne'
  have hpow : DifferentiableAt ℂ (fun z : ℂ => (Y : ℂ) ^ z) w :=
    differentiableAt_id.const_cpow (Or.inl hYne)
  have hmollifier : DifferentiableAt ℂ
      (fun z : ℂ => classicalDetectorMollifier M (rho + z)) w :=
    (differentiable_classicalDetectorMollifier M (rho + w)).comp w (by fun_prop)
  have hgammaArg : ∀ n : ℕ, w + 1 ≠ -(n : ℂ) := by
    intro n hzero
    have hre := congrArg Complex.re hzero
    norm_num [Complex.add_re] at hre
    linarith [hw]
  have hgamma : DifferentiableAt ℂ
      (fun z : ℂ => Complex.Gamma (z + 1)) w :=
    (Complex.differentiableAt_Gamma (w + 1) hgammaArg).comp w (by fun_prop)
  have hcancelled : DifferentiableAt ℂ
      (fun z : ℂ => dslope zetaPoleRemoved rho (rho + z)) w := by
    exact (differentiable_bettinGonekCancelledZeta rho (rho + w)).comp w (by fun_prop)
  change DifferentiableWithinAt ℂ
    (fun z : ℂ =>
      (Y : ℂ) ^ z *
        classicalDetectorMollifier M (rho + z) *
        Complex.Gamma (z + 1) *
        dslope zetaPoleRemoved rho (rho + z))
    {z : ℂ | -1 < z.re} w
  exact (((hpow.mul hmollifier).mul hgamma).mul hcancelled).differentiableWithinAt

/-- Away from the canceled Gamma pole and the retained translated-zeta pole, the weighted
Cauchy kernel is exactly the source Gamma--Mobius--zeta contour factor. -/
theorem classicalDetectorContourWeight_div_eq_contourFactor
    (M : ℕ) {rho w : ℂ} (hrho : IsNontrivialZero rho)
    {Y : ℝ} (hwZero : w ≠ 0) (hwPole : w ≠ 1 - rho) :
    classicalDetectorContourWeight M rho Y w / (w - (1 - rho)) =
      classicalDetectorMellinContourFactor M rho Y w := by
  have hargRho : rho + w ≠ rho := by
    intro h
    apply hwZero
    linear_combination h
  have hargOne : rho + w ≠ 1 := by
    intro h
    apply hwPole
    linear_combination h
  have hcancelled :=
    bettinGonekCancelledZeta_eq_source hrho hargRho hargOne
  change dslope zetaPoleRemoved rho (rho + w) =
      ((rho + w) - 1) * riemannZeta (rho + w) /
        ((rho + w) - rho) at hcancelled
  rw [classicalDetectorContourWeight, classicalDetectorMellinContourFactor,
    hcancelled, Complex.Gamma_add_one w hwZero]
  have hdenZero : rho + w - rho = w := by ring
  have hdenPole : rho + w - 1 = w - (1 - rho) := by ring
  rw [hdenZero, hdenPole]
  field_simp [hwZero, sub_ne_zero.mpr hwPole]

theorem classicalDetectorExtendedContourFactor_eq_contourFactor
    (M : ℕ) {rho w : ℂ} (hrho : IsNontrivialZero rho)
    {Y : ℝ} (hwZero : w ≠ 0) (hwPole : w ≠ 1 - rho) :
    classicalDetectorExtendedContourFactor M rho Y w =
      classicalDetectorMellinContourFactor M rho Y w := by
  exact classicalDetectorContourWeight_div_eq_contourFactor
    M hrho hwZero hwPole

/-- The value of the holomorphic numerator at the retained pole is the source residue. -/
theorem classicalDetectorContourWeight_translatedZetaPole
    (M : ℕ) {rho : ℂ} (hrho : IsNontrivialZero rho) {Y : ℝ} :
    classicalDetectorContourWeight M rho Y (1 - rho) =
      (Y : ℂ) ^ (1 - rho) * Complex.Gamma (1 - rho) *
        classicalDetectorMollifier M 1 := by
  have hrhoOne : rho ≠ 1 := hrho.2.2
  have hpoleZero : 1 - rho ≠ 0 := sub_ne_zero.mpr hrhoOne.symm
  have hcenter : rho + (1 - rho) = 1 := by ring
  have hslope :
      dslope zetaPoleRemoved rho 1 = (1 - rho)⁻¹ := by
    rw [dslope_of_ne _ hrhoOne.symm, slope_fun_def_field]
    change (zetaPoleRemoved 1 - zetaPoleRemoved rho) / (1 - rho) =
      (1 - rho)⁻¹
    rw [
      zetaPoleRemoved_one, zetaPoleRemoved_eq_zero_of_nontrivialZero hrho]
    simp only [sub_zero, one_div]
  rw [classicalDetectorContourWeight, hcenter, hslope,
    Complex.Gamma_add_one (1 - rho) hpoleZero]
  field_simp [hpoleZero]

/-- The finite source rectangle contains exactly the translated zeta pole. -/
theorem rectangleBoundaryIntegral_classicalDetectorExtendedContourFactor
    (M : ℕ) {rho : ℂ} (hrho : IsNontrivialZero rho)
    {Y T : ℝ} (hY : 0 < Y) (hT : |(1 - rho).im| < T) :
    rectangleBoundaryIntegral
        (classicalDetectorExtendedContourFactor M rho Y)
        (1 / 2 - rho.re) 2 (-T) T =
      2 * (Real.pi : ℂ) * Complex.I *
        ((Y : ℂ) ^ (1 - rho) * Complex.Gamma (1 - rho) *
          classicalDetectorMollifier M 1) := by
  have hrhoPos := nontrivial_zero_re_pos hrho
  have hrhoLt := nontrivial_zero_re_lt_one hrho
  have hleftRight : 1 / 2 - rho.re ≤ (2 : ℝ) := by
    linarith
  have hrect :
      [[(1 / 2 - rho.re : ℝ), 2]] ×ℂ [[-T, T]] ⊆
        {w : ℂ | -1 < w.re} := by
    intro w hw
    rw [Complex.mem_reProdIm] at hw
    rw [uIcc_of_le hleftRight] at hw
    change -1 < w.re
    linarith [hw.1.1]
  have hbottom : -T < (1 - rho).im := by
    linarith [neg_abs_le (1 - rho).im]
  have htop : (1 - rho).im < T := by
    linarith [le_abs_self (1 - rho).im]
  have hboundary :=
    rectangleBoundaryIntegral_weighted_cauchyKernel_of_differentiableOn
      (isOpen_lt continuous_const Complex.continuous_re)
      (differentiableOn_classicalDetectorContourWeight M rho hY)
      hrect
      (rho := 1 - rho)
      (l := 1 / 2 - rho.re) (r := 2) (b := -T) (t := T)
      (by norm_num [Complex.sub_re])
      (by norm_num [Complex.sub_re]; linarith)
      hbottom htop
  change rectangleBoundaryIntegral
      (fun z => classicalDetectorContourWeight M rho Y z / (z - (1 - rho)))
      (1 / 2 - rho.re) 2 (-T) T = _
  rw [classicalDetectorContourWeight_translatedZetaPole M hrho] at hboundary
  exact hboundary

/-- The finite source rectangle solved for its right vertical side, with every extended
boundary value replaced by the actual Gamma--Mobius--zeta factor. -/
theorem classicalDetectorMellinContourFactor_vertical_eq_left_add_residue_horizontals
    (M : ℕ) {rho : ℂ} (hrho : IsNontrivialZero rho)
    (hbeta : 1 / 2 < rho.re) {Y : ℝ} (hY : 0 < Y)
    {T : ℝ} (hT : 1 + |rho.im| < T) :
    (∫ t : ℝ in -T..T,
        classicalDetectorMellinContourFactor M rho Y
          (2 + t * Complex.I)) =
      (2 * (Real.pi : ℂ)) *
          ((Y : ℂ) ^ (1 - rho) * Complex.Gamma (1 - rho) *
            classicalDetectorMollifier M 1) +
        (∫ t : ℝ in -T..T,
          classicalDetectorMellinContourFactor M rho Y
            ((1 / 2 - rho.re : ℝ) + t * Complex.I)) +
        Complex.I *
          ((∫ x : ℝ in (1 / 2 - rho.re)..2,
              classicalDetectorMellinContourFactor M rho Y
                ((x : ℂ) + (-T) * Complex.I)) -
            ∫ x : ℝ in (1 / 2 - rho.re)..2,
              classicalDetectorMellinContourFactor M rho Y
                ((x : ℂ) + T * Complex.I)) := by
  have hTPos : 0 < T := by
    linarith [abs_nonneg rho.im]
  have hpoleIm : |(1 - rho).im| = |rho.im| := by
    simp
  have hboundary :=
    rectangleBoundaryIntegral_classicalDetectorExtendedContourFactor
      M hrho hY (T := T) (by rw [hpoleIm]; linarith)
  have hbottom :
      (∫ x : ℝ in (1 / 2 - rho.re)..2,
          classicalDetectorExtendedContourFactor M rho Y
            ((x : ℂ) + (-T) * Complex.I)) =
        ∫ x : ℝ in (1 / 2 - rho.re)..2,
          classicalDetectorMellinContourFactor M rho Y
            ((x : ℂ) + (-T) * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro x _
    apply classicalDetectorExtendedContourFactor_eq_contourFactor M hrho
    · intro hzero
      have him := congrArg Complex.im hzero
      norm_num [Complex.mul_im] at him
      linarith
    · intro hpole
      have him := congrArg Complex.im hpole
      norm_num [Complex.mul_im, Complex.sub_im] at him
      linarith [le_abs_self rho.im]
  have htop :
      (∫ x : ℝ in (1 / 2 - rho.re)..2,
          classicalDetectorExtendedContourFactor M rho Y
            ((x : ℂ) + T * Complex.I)) =
        ∫ x : ℝ in (1 / 2 - rho.re)..2,
          classicalDetectorMellinContourFactor M rho Y
            ((x : ℂ) + T * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro x _
    apply classicalDetectorExtendedContourFactor_eq_contourFactor M hrho
    · intro hzero
      have him := congrArg Complex.im hzero
      norm_num [Complex.mul_im] at him
      linarith
    · intro hpole
      have him := congrArg Complex.im hpole
      norm_num [Complex.mul_im, Complex.sub_im] at him
      linarith [neg_abs_le rho.im]
  have hright :
      (∫ t : ℝ in -T..T,
          classicalDetectorExtendedContourFactor M rho Y
            (2 + t * Complex.I)) =
        ∫ t : ℝ in -T..T,
          classicalDetectorMellinContourFactor M rho Y
            (2 + t * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro t _
    apply classicalDetectorExtendedContourFactor_eq_contourFactor M hrho
    · intro hzero
      have hre := congrArg Complex.re hzero
      norm_num [Complex.mul_re] at hre
    · intro hpole
      have hre := congrArg Complex.re hpole
      norm_num [Complex.mul_re, Complex.sub_re] at hre
      linarith [nontrivial_zero_re_pos hrho]
  have hleft :
      (∫ t : ℝ in -T..T,
          classicalDetectorExtendedContourFactor M rho Y
            ((1 / 2 - rho.re : ℝ) + t * Complex.I)) =
        ∫ t : ℝ in -T..T,
          classicalDetectorMellinContourFactor M rho Y
            ((1 / 2 - rho.re : ℝ) + t * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro t _
    apply classicalDetectorExtendedContourFactor_eq_contourFactor M hrho
    · intro hzero
      have hre := congrArg Complex.re hzero
      norm_num [Complex.mul_re] at hre
      linarith
    · intro hpole
      have hre := congrArg Complex.re hpole
      norm_num [Complex.mul_re, Complex.sub_re] at hre
  have hleftNorm :
      (∫ t : ℝ in -T..T,
          classicalDetectorMellinContourFactor M rho Y
            ((1 / 2 - rho.re : ℝ) + t * Complex.I)) =
        ∫ t : ℝ in -T..T,
          classicalDetectorMellinContourFactor M rho Y
            ((1 / 2 : ℂ) - (rho.re : ℂ) + t * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro t _
    have harg :
        (((1 / 2 - rho.re : ℝ) : ℂ) + t * Complex.I) =
          (1 / 2 : ℂ) - (rho.re : ℂ) + t * Complex.I := by
      push_cast
      ring
    change classicalDetectorMellinContourFactor M rho Y
        (((1 / 2 - rho.re : ℝ) : ℂ) + t * Complex.I) =
      classicalDetectorMellinContourFactor M rho Y
        ((1 / 2 : ℂ) - (rho.re : ℂ) + t * Complex.I)
    rw [harg]
  rw [rectangleBoundaryIntegral] at hboundary
  push_cast at hboundary
  push_cast at hleft
  rw [hbottom, htop, hright, hleft] at hboundary
  rw [hleftNorm]
  apply mul_left_cancel₀ Complex.I_ne_zero
  rw [mul_add, mul_add]
  simp only [← mul_assoc, Complex.I_mul_I, neg_one_mul]
  linear_combination hboundary

/-- Sending the two horizontal sides to infinity gives the literal unnormalized source
vertical-line identity. -/
theorem integral_classicalDetectorMellinContourFactor_right_eq_residue_add_left
    (M : ℕ) {rho : ℂ} (hrho : IsNontrivialZero rho)
    (hbeta : 1 / 2 < rho.re) {Y : ℝ} (hY : 0 < Y) :
    (∫ t : ℝ,
        classicalDetectorMellinContourFactor M rho Y
          (2 + t * Complex.I)) =
      (2 * (Real.pi : ℂ)) *
          ((Y : ℂ) ^ (1 - rho) * Complex.Gamma (1 - rho) *
            classicalDetectorMollifier M 1) +
        ∫ t : ℝ,
          classicalDetectorMellinContourFactor M rho Y
            ((1 / 2 - rho.re : ℝ) + t * Complex.I) := by
  have hright := intervalIntegral_tendsto_integral
    (integrable_classicalDetectorMellinContourFactor_right M hrho hY)
    tendsto_neg_atTop_atBot tendsto_id
  have hleft := intervalIntegral_tendsto_integral
    (integrable_classicalDetectorMellinContourFactor_left M hrho hbeta hY)
    tendsto_neg_atTop_atBot tendsto_id
  have hbottom :=
    tendsto_integral_classicalDetectorMellinContourFactor_bottom M hrho hY
  have htop :=
    tendsto_integral_classicalDetectorMellinContourFactor_top M hrho hY
  let R : ℂ :=
    (2 * (Real.pi : ℂ)) *
      ((Y : ℂ) ^ (1 - rho) * Complex.Gamma (1 - rho) *
        classicalDetectorMollifier M 1)
  have hright' :
      Tendsto
        (fun T : ℝ => ∫ t : ℝ in -T..T,
          classicalDetectorMellinContourFactor M rho Y
            (2 + t * Complex.I))
        atTop
        (nhds (∫ t : ℝ,
          classicalDetectorMellinContourFactor M rho Y
            (2 + t * Complex.I))) := by
    simpa only [Function.comp_apply, id_eq] using hright
  have hleft' :
      Tendsto
        (fun T : ℝ => ∫ t : ℝ in -T..T,
          classicalDetectorMellinContourFactor M rho Y
            ((1 / 2 - rho.re : ℝ) + t * Complex.I))
        atTop
        (nhds (∫ t : ℝ,
          classicalDetectorMellinContourFactor M rho Y
            ((1 / 2 - rho.re : ℝ) + t * Complex.I))) := by
    simpa only [Function.comp_apply, id_eq] using hleft
  have hhoriz :
      Tendsto
        (fun T : ℝ => Complex.I *
          ((∫ x : ℝ in (1 / 2 - rho.re)..2,
              classicalDetectorMellinContourFactor M rho Y
                ((x : ℂ) + (-T) * Complex.I)) -
            ∫ x : ℝ in (1 / 2 - rho.re)..2,
              classicalDetectorMellinContourFactor M rho Y
                ((x : ℂ) + T * Complex.I)))
        atTop (nhds 0) := by
    simpa only [sub_zero, mul_zero] using
      (tendsto_const_nhds.mul (hbottom.sub htop) :
        Tendsto
          (fun T : ℝ => Complex.I *
            ((∫ x : ℝ in (1 / 2 - rho.re)..2,
                classicalDetectorMellinContourFactor M rho Y
                  ((x : ℂ) + (-T) * Complex.I)) -
              ∫ x : ℝ in (1 / 2 - rho.re)..2,
                classicalDetectorMellinContourFactor M rho Y
                  ((x : ℂ) + T * Complex.I)))
          atTop (nhds (Complex.I * (0 - 0))))
  have hRleft :
      Tendsto
        (fun T : ℝ =>
          R +
            (∫ t : ℝ in -T..T,
              classicalDetectorMellinContourFactor M rho Y
                ((1 / 2 - rho.re : ℝ) + t * Complex.I)) +
            Complex.I *
              ((∫ x : ℝ in (1 / 2 - rho.re)..2,
                  classicalDetectorMellinContourFactor M rho Y
                    ((x : ℂ) + (-T) * Complex.I)) -
                ∫ x : ℝ in (1 / 2 - rho.re)..2,
                  classicalDetectorMellinContourFactor M rho Y
                    ((x : ℂ) + T * Complex.I)))
        atTop
        (nhds (R +
          (∫ t : ℝ,
            classicalDetectorMellinContourFactor M rho Y
              ((1 / 2 - rho.re : ℝ) + t * Complex.I)) + 0)) := by
    exact (tendsto_const_nhds.add hleft').add hhoriz
  have hfinite : ∀ᶠ T : ℝ in atTop,
      (∫ t : ℝ in -T..T,
          classicalDetectorMellinContourFactor M rho Y
            (2 + t * Complex.I)) =
        R +
          (∫ t : ℝ in -T..T,
            classicalDetectorMellinContourFactor M rho Y
              ((1 / 2 - rho.re : ℝ) + t * Complex.I)) +
          Complex.I *
            ((∫ x : ℝ in (1 / 2 - rho.re)..2,
                classicalDetectorMellinContourFactor M rho Y
                  ((x : ℂ) + (-T) * Complex.I)) -
              ∫ x : ℝ in (1 / 2 - rho.re)..2,
                classicalDetectorMellinContourFactor M rho Y
                  ((x : ℂ) + T * Complex.I)) := by
    filter_upwards [eventually_gt_atTop (1 + |rho.im|)] with T hT
    exact
      classicalDetectorMellinContourFactor_vertical_eq_left_add_residue_horizontals
        M hrho hbeta hY hT
  have hfiniteSymm := hfinite.mono fun _ h => h.symm
  have hlimits :=
    tendsto_nhds_unique hright' (hRleft.congr' hfiniteSymm)
  simpa only [R, add_zero] using hlimits

/-- The normalized inverse-Mellin line shifts by exactly the retained source residue. -/
theorem classicalDetectorMellinLineIntegral_two_eq_residue_add_shifted
    (M : ℕ) {rho : ℂ} (hrho : IsNontrivialZero rho)
    (hbeta : 1 / 2 < rho.re) {Y : ℝ} (hY : 0 < Y) :
    classicalDetectorMellinLineIntegral M rho Y 2 =
      (Y : ℂ) ^ (1 - rho) * Complex.Gamma (1 - rho) *
          classicalDetectorMollifier M 1 +
        classicalDetectorMellinLineIntegral M rho Y (1 / 2 - rho.re) := by
  have hraw :=
    integral_classicalDetectorMellinContourFactor_right_eq_residue_add_left
      M hrho hbeta hY
  rw [classicalDetectorMellinLineIntegral,
    classicalDetectorMellinLineIntegral]
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ,
        classicalDetectorMellinContourFactor M rho Y
          (2 + t * Complex.I)) =
    (Y : ℂ) ^ (1 - rho) * Complex.Gamma (1 - rho) *
        classicalDetectorMollifier M 1 +
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ,
          classicalDetectorMellinContourFactor M rho Y
            ((1 / 2 - rho.re : ℝ) + t * Complex.I)
  rw [hraw]
  rw [mul_add]
  have hscale :
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (2 * (Real.pi : ℂ))) = 1 := by
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [← mul_assoc, hscale, one_mul]

/-- Maynard--Pratt Appendix C's shifted inverse-Mellin identity for the actual smoothed
truncated-Mobius detector. -/
theorem classicalDetectorSmoothedSeries_eq_residue_add_shifted
    (M : ℕ) {rho : ℂ} (hrho : IsNontrivialZero rho)
    (hbeta : 1 / 2 < rho.re) {Y : ℝ} (hY : 0 < Y) :
    classicalDetectorSmoothedSeries M Y rho =
      (Y : ℂ) ^ (1 - rho) * Complex.Gamma (1 - rho) *
          classicalDetectorMollifier M 1 +
        classicalDetectorMellinLineIntegral M rho Y (1 / 2 - rho.re) := by
  have hinverse :=
    classicalDetectorInverseMellinLine M rho Y 2 hY (by norm_num)
      (by linarith [nontrivial_zero_re_pos hrho])
  rw [hinverse,
    classicalDetectorMellinLineIntegral_two_eq_residue_add_shifted
      M hrho hbeta hY]

/-- The divisor-sum detector coefficient has the elementary linear bound needed to recover
absolute convergence after exponential smoothing outside the initial Dirichlet half-plane. -/
theorem norm_classicalDetectorCoefficient_le_nat (M n : ℕ) :
    ‖classicalDetectorCoefficient M n‖ ≤ n := by
  rw [classicalDetectorCoefficient_eq_divisorSum]
  calc
    ‖∑ d ∈ n.divisors,
        if d ≤ M then ((ArithmeticFunction.moebius d : ℤ) : ℂ) else 0‖
        ≤ ∑ d ∈ n.divisors,
            ‖if d ≤ M then
              ((ArithmeticFunction.moebius d : ℤ) : ℂ) else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _d ∈ n.divisors, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d _
      split_ifs
      · rw [Complex.norm_intCast]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
      · norm_num
    _ = n.divisors.card := by simp
    _ ≤ n := by exact_mod_cast Nat.card_divisors_le_self n

theorem norm_classicalDetectorSmoothedTerm_le
    (M : ℕ) {z : ℂ} (hz : 0 < z.re) (Y : ℝ) (n : ℕ) :
    ‖classicalDetectorSmoothedTerm M Y z n‖ ≤
      (n : ℝ) * Real.exp (-((n : ℝ) / Y)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [classicalDetectorSmoothedTerm, LSeries.term]
  · have hn1N : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1N
    have hden : 1 ≤ (n : ℝ) ^ z.re :=
      Real.one_le_rpow hn1 hz.le
    have hterm :
        ‖LSeries.term (classicalDetectorCoefficient M) z n‖ ≤ n := by
      rw [LSeries.norm_term_eq, if_neg hn]
      exact (div_le_self (norm_nonneg _) hden).trans
        (norm_classicalDetectorCoefficient_le_nat M n)
    rw [classicalDetectorSmoothedTerm, norm_mul, Complex.norm_exp]
    norm_num
    exact mul_le_mul_of_nonneg_right hterm (Real.exp_nonneg _)

/-- Exponential smoothing makes the actual detector series absolutely summable at every point
with positive real part, including every nontrivial zeta zero. -/
theorem summable_classicalDetectorSmoothedTerm_of_re_pos
    (M : ℕ) {z : ℂ} (hz : 0 < z.re) {Y : ℝ} (hY : 0 < Y) :
    Summable (classicalDetectorSmoothedTerm M Y z) := by
  have hr : 0 < 1 / Y := one_div_pos.mpr hY
  have hmajor :=
    Real.summable_pow_mul_exp_neg_nat_mul 1 hr
  refine hmajor.of_norm_bounded ?_
  intro n
  have hbound :=
    norm_classicalDetectorSmoothedTerm_le M hz Y n
  have hexp :
      -((n : ℝ) / Y) = -(1 / Y) * n := by
    field_simp
  simpa only [pow_one, hexp] using hbound

theorem classicalDetectorSmoothedSeries_eq_head_add_tail_of_re_pos
    {M : ℕ} (hM : 1 ≤ M) {z : ℂ} (hz : 0 < z.re)
    {Y : ℝ} (hY : 0 < Y) :
    classicalDetectorSmoothedSeries M Y z =
      Complex.exp (-(1 / Y : ℝ)) +
        ∑' n : ℕ, classicalDetectorSmoothedTerm M Y z (n + (M + 1)) := by
  let f := classicalDetectorSmoothedTerm M Y z
  have hf : Summable f :=
    summable_classicalDetectorSmoothedTerm_of_re_pos M hz hY
  have hhead :
      (∑ n ∈ Finset.range (M + 1), f n) =
        Complex.exp (-(1 / Y : ℝ)) := by
    rw [Finset.sum_eq_single 1]
    · exact classicalDetectorSmoothedTerm_one hM Y z
    · intro n hn hn1
      have hnlt : n < M + 1 := Finset.mem_range.mp hn
      rcases eq_or_ne n 0 with rfl | hn0
      · simp [f, classicalDetectorSmoothedTerm, LSeries.term]
      · exact classicalDetectorSmoothedTerm_eq_zero
          (by omega) (by omega) Y z
    · intro hnot
      have hmem : 1 ∈ Finset.range (M + 1) :=
        Finset.mem_range.mpr (by omega)
      exact (hnot hmem).elim
  have hsplit := hf.sum_add_tsum_nat_add (M + 1)
  rw [classicalDetectorSmoothedSeries]
  calc
    (∑' n : ℕ, f n) =
        (∑ n ∈ Finset.range (M + 1), f n) +
          ∑' n : ℕ, f (n + (M + 1)) := hsplit.symm
    _ = _ := by rw [hhead]

/-- The exact coefficient-gap identity immediately preceding the source's dyadic split. -/
theorem classicalDetectorCoefficientGap_shifted_identity
    {M : ℕ} (hM : 1 ≤ M) {rho : ℂ} (hrho : IsNontrivialZero rho)
    (hbeta : 1 / 2 < rho.re) {Y : ℝ} (hY : 0 < Y) :
    (1 : ℂ) + (Complex.exp (-(1 / Y : ℝ)) - 1) +
        (∑' n : ℕ,
          classicalDetectorSmoothedTerm M Y rho (n + (M + 1))) =
      (Y : ℂ) ^ (1 - rho) * Complex.Gamma (1 - rho) *
          classicalDetectorMollifier M 1 +
        classicalDetectorMellinLineIntegral M rho Y (1 / 2 - rho.re) := by
  have hhead :=
    classicalDetectorSmoothedSeries_eq_head_add_tail_of_re_pos
      hM (nontrivial_zero_re_pos hrho) hY
  have hshift :=
    classicalDetectorSmoothedSeries_eq_residue_add_shifted
      M hrho hbeta hY
  linear_combination hhead.symm + hshift

/-- Aggregate source certificate for the first contour-shift edge in the classical
zero-density detector. -/
structure ClassicalDetectorContourShiftCertificate : Prop where
  shiftedLine :
    ∀ (M : ℕ) {rho : ℂ}, IsNontrivialZero rho →
      1 / 2 < rho.re →
      ∀ {Y : ℝ}, 0 < Y →
        classicalDetectorMellinLineIntegral M rho Y 2 =
          (Y : ℂ) ^ (1 - rho) * Complex.Gamma (1 - rho) *
              classicalDetectorMollifier M 1 +
            classicalDetectorMellinLineIntegral M rho Y (1 / 2 - rho.re)
  coefficientGap :
    ∀ {M : ℕ}, 1 ≤ M →
      ∀ {rho : ℂ}, IsNontrivialZero rho →
        1 / 2 < rho.re →
        ∀ {Y : ℝ}, 0 < Y →
          (1 : ℂ) + (Complex.exp (-(1 / Y : ℝ)) - 1) +
              (∑' n : ℕ,
                classicalDetectorSmoothedTerm M Y rho (n + (M + 1))) =
            (Y : ℂ) ^ (1 - rho) * Complex.Gamma (1 - rho) *
                classicalDetectorMollifier M 1 +
              classicalDetectorMellinLineIntegral M rho Y (1 / 2 - rho.re)

theorem classicalDetectorContourShift_endpoint :
    ClassicalDetectorContourShiftCertificate where
  shiftedLine := fun M _ hrho hbeta _ hY =>
    classicalDetectorMellinLineIntegral_two_eq_residue_add_shifted
      M hrho hbeta hY
  coefficientGap := fun hM _ hrho hbeta _ hY =>
    classicalDetectorCoefficientGap_shifted_identity
      hM hrho hbeta hY

end LeanLab.Riemann
