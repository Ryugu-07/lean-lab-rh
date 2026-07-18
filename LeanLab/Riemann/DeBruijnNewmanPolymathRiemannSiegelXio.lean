import LeanLab.Riemann.DeBruijnNewmanPolymathRiemannSiegelSum
import LeanLab.Riemann.ComplexLaplaceGamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.Prod

set_option linter.style.header false

/-!
# The Titchmarsh contour behind the Riemann--Siegel identity

This file reconstructs the source contour argument in Titchmarsh (2.10.1)--(2.10.6). The fixed
endpoint is the Polymath equation `(xio)`; the declarations below start with the actual auxiliary
contour `Phi(a)` and its source-oriented Gaussian core.
-/

open Complex Filter MeasureTheory Real Set Topology
open scoped ComplexConjugate

namespace LeanLab.Riemann

noncomputable section

/-- Titchmarsh's `pi/4` contour direction. -/
def deBruijnNewmanTitchmarshPhiDirection : ℂ :=
  Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)

/-- The source line `w = -pi + exp(pi*i/4) v`, which crosses the imaginary axis at `pi*i`. -/
def deBruijnNewmanTitchmarshPhiLine (v : ℝ) : ℂ :=
  -(Real.pi : ℂ) + deBruijnNewmanTitchmarshPhiDirection * v

/-- The exponential in Titchmarsh's auxiliary integral `(2.10.1)`. -/
def deBruijnNewmanTitchmarshPhiExponent (a w : ℂ) : ℂ :=
  Complex.I * w ^ 2 / (4 * Real.pi) + a * w

/-- The denominator in Titchmarsh's auxiliary integral `(2.10.1)`. -/
def deBruijnNewmanTitchmarshPhiDenominator (w : ℂ) : ℂ :=
  Complex.exp w - 1

/-- Reciprocal denominator along Titchmarsh's source line. -/
def deBruijnNewmanTitchmarshPhiDenominatorInverse (v : ℝ) : ℂ :=
  (deBruijnNewmanTitchmarshPhiDenominator
    (deBruijnNewmanTitchmarshPhiLine v))⁻¹

/-- Titchmarsh's auxiliary contour integrand, including the line Jacobian. -/
def deBruijnNewmanTitchmarshPhiLineIntegrand (a : ℂ) (v : ℝ) : ℂ :=
  Complex.exp
      (deBruijnNewmanTitchmarshPhiExponent a
        (deBruijnNewmanTitchmarshPhiLine v)) /
    deBruijnNewmanTitchmarshPhiDenominator
      (deBruijnNewmanTitchmarshPhiLine v) *
    deBruijnNewmanTitchmarshPhiDirection

/-- The actual auxiliary contour `Phi(a)` from Titchmarsh `(2.10.1)`. -/
def deBruijnNewmanTitchmarshPhi (a : ℂ) : ℂ :=
  ∫ v : ℝ, deBruijnNewmanTitchmarshPhiLineIntegrand a v

/-- The denominator-free Gaussian obtained when subtracting `Phi(a)` from `Phi(a+1)`. -/
def deBruijnNewmanTitchmarshPhiGaussianLineIntegrand (a : ℂ) (v : ℝ) : ℂ :=
  Complex.exp
      (deBruijnNewmanTitchmarshPhiExponent a
        (deBruijnNewmanTitchmarshPhiLine v)) *
    deBruijnNewmanTitchmarshPhiDirection

@[simp] theorem deBruijnNewmanTitchmarshPhiDirection_sq :
    deBruijnNewmanTitchmarshPhiDirection ^ 2 = Complex.I := by
  rw [deBruijnNewmanTitchmarshPhiDirection, ← Complex.exp_nat_mul]
  change Complex.exp
      ((2 : ℂ) * (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)) = Complex.I
  have harg :
      (2 : ℂ) * (((Real.pi / 4 : ℝ) : ℂ) * Complex.I) =
        (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp

@[simp] theorem norm_deBruijnNewmanTitchmarshPhiDirection :
    ‖deBruijnNewmanTitchmarshPhiDirection‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

@[simp] theorem deBruijnNewmanTitchmarshPhiDirection_re :
    deBruijnNewmanTitchmarshPhiDirection.re = Real.sqrt 2 / 2 := by
  rw [deBruijnNewmanTitchmarshPhiDirection, Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_four, Real.sin_pi_div_four]
  simp

@[simp] theorem deBruijnNewmanTitchmarshPhiDirection_im :
    deBruijnNewmanTitchmarshPhiDirection.im = Real.sqrt 2 / 2 := by
  rw [deBruijnNewmanTitchmarshPhiDirection, Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_four, Real.sin_pi_div_four]
  simp

@[simp] theorem deBruijnNewmanTitchmarshPhiLine_re (v : ℝ) :
    (deBruijnNewmanTitchmarshPhiLine v).re =
      -Real.pi + (Real.sqrt 2 / 2) * v := by
  rw [deBruijnNewmanTitchmarshPhiLine]
  simp

@[simp] theorem deBruijnNewmanTitchmarshPhiLine_im (v : ℝ) :
    (deBruijnNewmanTitchmarshPhiLine v).im =
      (Real.sqrt 2 / 2) * v := by
  rw [deBruijnNewmanTitchmarshPhiLine]
  simp

/-- The selected source line crosses the imaginary axis at `pi*i`. -/
theorem deBruijnNewmanTitchmarshPhiLine_im_eq_re_add_pi (v : ℝ) :
    (deBruijnNewmanTitchmarshPhiLine v).im =
      (deBruijnNewmanTitchmarshPhiLine v).re + Real.pi := by
  rw [deBruijnNewmanTitchmarshPhiLine_re, deBruijnNewmanTitchmarshPhiLine_im]
  ring

/-- Titchmarsh's source line avoids every zero `2*pi*i*n` of `exp(w)-1`. -/
theorem deBruijnNewmanTitchmarshPhiDenominator_ne_zero (v : ℝ) :
    deBruijnNewmanTitchmarshPhiDenominator
      (deBruijnNewmanTitchmarshPhiLine v) ≠ 0 := by
  intro hzero
  have hexp : Complex.exp (deBruijnNewmanTitchmarshPhiLine v) = 1 := by
    exact sub_eq_zero.mp hzero
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp
  have hre := congrArg Complex.re hn
  have him := congrArg Complex.im hn
  have hreR : ((n : ℂ) * (2 * Real.pi * Complex.I)).re = 0 := by
    simp
  have himR : ((n : ℂ) * (2 * Real.pi * Complex.I)).im =
      (n : ℝ) * (2 * Real.pi) := by
    simp
  rw [deBruijnNewmanTitchmarshPhiLine_re, hreR] at hre
  rw [deBruijnNewmanTitchmarshPhiLine_im, himR] at him
  have hcross : (Real.sqrt 2 / 2) * v = Real.pi := by linarith
  have hpi : Real.pi = (n : ℝ) * (2 * Real.pi) := by linarith
  have hmul : Real.pi * 1 = Real.pi * (2 * (n : ℝ)) := by
    calc
      Real.pi * 1 = Real.pi := by ring
      _ = (n : ℝ) * (2 * Real.pi) := hpi
      _ = Real.pi * (2 * (n : ℝ)) := by ring
  have hparityR : (1 : ℝ) = 2 * (n : ℝ) :=
    mul_left_cancel₀ Real.pi_ne_zero hmul
  have hparityZ : (1 : ℤ) = 2 * n := by exact_mod_cast hparityR
  omega

/-- The reciprocal source denominator is continuous on the full parameter line. -/
theorem continuous_deBruijnNewmanTitchmarshPhiDenominatorInverse :
    Continuous deBruijnNewmanTitchmarshPhiDenominatorInverse := by
  unfold deBruijnNewmanTitchmarshPhiDenominatorInverse
  apply Continuous.inv₀
  · unfold deBruijnNewmanTitchmarshPhiDenominator
    unfold deBruijnNewmanTitchmarshPhiLine
    fun_prop
  · exact fun v ↦ deBruijnNewmanTitchmarshPhiDenominator_ne_zero v

/-- The source exponential tends to zero at the negative end of the slanted line. -/
theorem tendsto_deBruijnNewmanTitchmarshPhiLine_exp_atBot :
    Tendsto
      (fun v : ℝ ↦ Complex.exp (deBruijnNewmanTitchmarshPhiLine v))
      atBot (𝓝 0) := by
  have hq : 0 < Real.sqrt 2 / 2 := by positivity
  have hre : Tendsto
      (fun v : ℝ ↦ (deBruijnNewmanTitchmarshPhiLine v).re) atBot atBot := by
    simp_rw [deBruijnNewmanTitchmarshPhiLine_re]
    exact tendsto_atBot_add_const_left atBot (-Real.pi)
      ((tendsto_const_mul_atBot_of_pos hq).2 tendsto_id)
  apply Complex.tendsto_exp_comap_re_atBot.comp
  exact tendsto_comap_iff.2 hre

/-- After reversing the line, its exponential tends to zero at the positive end. -/
theorem tendsto_deBruijnNewmanTitchmarshPhiLine_neg_exp_atTop :
    Tendsto
      (fun v : ℝ ↦ Complex.exp (-deBruijnNewmanTitchmarshPhiLine v))
      atTop (𝓝 0) := by
  have hq : 0 < Real.sqrt 2 / 2 := by positivity
  have hre : Tendsto
      (fun v : ℝ ↦ (-deBruijnNewmanTitchmarshPhiLine v).re) atTop atBot := by
    simp_rw [Complex.neg_re, deBruijnNewmanTitchmarshPhiLine_re]
    convert tendsto_atBot_add_const_left atTop Real.pi
      (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr hq)) using 1
    funext v
    dsimp
    ring
  apply Complex.tendsto_exp_comap_re_atBot.comp
  exact tendsto_comap_iff.2 hre

/-- Algebraic form of the reciprocal denominator adapted to the positive end of the line. -/
theorem deBruijnNewmanTitchmarshPhiDenominatorInverse_eq (v : ℝ) :
    deBruijnNewmanTitchmarshPhiDenominatorInverse v =
      Complex.exp (-deBruijnNewmanTitchmarshPhiLine v) /
        (1 - Complex.exp (-deBruijnNewmanTitchmarshPhiLine v)) := by
  have hden := deBruijnNewmanTitchmarshPhiDenominator_ne_zero v
  have hexp : Complex.exp (deBruijnNewmanTitchmarshPhiLine v) ≠ 0 :=
    Complex.exp_ne_zero _
  unfold deBruijnNewmanTitchmarshPhiDenominatorInverse
  unfold deBruijnNewmanTitchmarshPhiDenominator
  rw [Complex.exp_neg]
  field_simp

/-- The reciprocal denominator approaches `-1` at the negative end. -/
theorem tendsto_deBruijnNewmanTitchmarshPhiDenominatorInverse_atBot :
    Tendsto deBruijnNewmanTitchmarshPhiDenominatorInverse atBot (𝓝 (-1)) := by
  have hden : Tendsto
      (fun v : ℝ ↦ deBruijnNewmanTitchmarshPhiDenominator
        (deBruijnNewmanTitchmarshPhiLine v)) atBot (𝓝 (-1)) := by
    unfold deBruijnNewmanTitchmarshPhiDenominator
    convert tendsto_deBruijnNewmanTitchmarshPhiLine_exp_atBot.sub
      tendsto_const_nhds using 1 <;> norm_num
  unfold deBruijnNewmanTitchmarshPhiDenominatorInverse
  convert hden.inv₀ (by norm_num) using 1 <;> norm_num

/-- The reciprocal denominator approaches zero at the positive end. -/
theorem tendsto_deBruijnNewmanTitchmarshPhiDenominatorInverse_atTop :
    Tendsto deBruijnNewmanTitchmarshPhiDenominatorInverse atTop (𝓝 0) := by
  have hzero := tendsto_deBruijnNewmanTitchmarshPhiLine_neg_exp_atTop
  have hquot : Tendsto
      (fun v : ℝ ↦ Complex.exp (-deBruijnNewmanTitchmarshPhiLine v) /
        (1 - Complex.exp (-deBruijnNewmanTitchmarshPhiLine v)))
      atTop (𝓝 (0 / (1 - 0))) :=
    hzero.div (tendsto_const_nhds.sub hzero) (by norm_num)
  simpa only [← deBruijnNewmanTitchmarshPhiDenominatorInverse_eq,
    sub_zero, zero_div] using hquot

/-- The reciprocal denominator has bounded range on Titchmarsh's full source line. -/
theorem isBounded_range_deBruijnNewmanTitchmarshPhiDenominatorInverse :
    Bornology.IsBounded
      (range deBruijnNewmanTitchmarshPhiDenominatorInverse) := by
  obtain ⟨s, hs, hsBound⟩ := Metric.exists_isBounded_image_of_tendsto
    tendsto_deBruijnNewmanTitchmarshPhiDenominatorInverse_atBot
  obtain ⟨t, ht, htBound⟩ := Metric.exists_isBounded_image_of_tendsto
    tendsto_deBruijnNewmanTitchmarshPhiDenominatorInverse_atTop
  obtain ⟨A, hA⟩ := mem_atBot_sets.mp hs
  obtain ⟨B, hB⟩ := mem_atTop_sets.mp ht
  have hmid : Bornology.IsBounded
      (deBruijnNewmanTitchmarshPhiDenominatorInverse '' Icc A B) :=
    (isCompact_Icc.image
      continuous_deBruijnNewmanTitchmarshPhiDenominatorInverse).isBounded
  apply ((hsBound.union htBound).union hmid).subset
  rintro y ⟨v, rfl⟩
  by_cases hvA : v ≤ A
  · exact Or.inl (Or.inl ⟨v, hA v hvA, rfl⟩)
  by_cases hvB : B ≤ v
  · exact Or.inl (Or.inr ⟨v, hB v hvB, rfl⟩)
  · exact Or.inr ⟨v, ⟨le_of_not_ge hvA, le_of_not_ge hvB⟩, rfl⟩

/-- A positive uniform bound for the reciprocal denominator on the source line. -/
theorem exists_pos_norm_deBruijnNewmanTitchmarshPhiDenominatorInverse_le :
    ∃ C > 0, ∀ v : ℝ,
      ‖deBruijnNewmanTitchmarshPhiDenominatorInverse v‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ :=
    isBounded_range_deBruijnNewmanTitchmarshPhiDenominatorInverse.exists_pos_norm_le
  exact ⟨C, hC, fun v ↦ hbound _ ⟨v, rfl⟩⟩

/-- The actual auxiliary integrand is continuous on the full parameter line. -/
theorem continuous_deBruijnNewmanTitchmarshPhiLineIntegrand (a : ℂ) :
    Continuous (deBruijnNewmanTitchmarshPhiLineIntegrand a) := by
  have hline : Continuous deBruijnNewmanTitchmarshPhiLine := by
    unfold deBruijnNewmanTitchmarshPhiLine
    fun_prop
  have hnum : Continuous (fun v : ℝ ↦ Complex.exp
      (deBruijnNewmanTitchmarshPhiExponent a
        (deBruijnNewmanTitchmarshPhiLine v))) := by
    unfold deBruijnNewmanTitchmarshPhiExponent
    fun_prop
  have hden : Continuous (fun v : ℝ ↦
      deBruijnNewmanTitchmarshPhiDenominator
        (deBruijnNewmanTitchmarshPhiLine v)) := by
    unfold deBruijnNewmanTitchmarshPhiDenominator
    fun_prop
  unfold deBruijnNewmanTitchmarshPhiLineIntegrand
  exact (hnum.div hden deBruijnNewmanTitchmarshPhiDenominator_ne_zero).mul continuous_const

/-- Exact quadratic normal form after parameterizing Titchmarsh's source line. -/
theorem deBruijnNewmanTitchmarshPhiExponent_line_eq (a : ℂ) (v : ℝ) :
    deBruijnNewmanTitchmarshPhiExponent a
        (deBruijnNewmanTitchmarshPhiLine v) =
      ((-(1 / (4 * Real.pi)) : ℝ) : ℂ) * v ^ 2 +
        (deBruijnNewmanTitchmarshPhiDirection *
          (a - Complex.I / 2)) * v +
        (Complex.I * Real.pi / 4 - Real.pi * a) := by
  rw [deBruijnNewmanTitchmarshPhiExponent, deBruijnNewmanTitchmarshPhiLine]
  rw [show
    (-(Real.pi : ℂ) + deBruijnNewmanTitchmarshPhiDirection * v) ^ 2 =
      (Real.pi : ℂ) ^ 2 -
        2 * Real.pi * deBruijnNewmanTitchmarshPhiDirection * v +
        Complex.I * v ^ 2 by
      rw [add_sq]
      simp only [mul_pow, deBruijnNewmanTitchmarshPhiDirection_sq]
      ring]
  push_cast
  field_simp [Real.pi_ne_zero]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The denominator-free source Gaussian is absolutely integrable for every complex parameter. -/
theorem integrable_deBruijnNewmanTitchmarshPhiGaussianLineIntegrand (a : ℂ) :
    Integrable (deBruijnNewmanTitchmarshPhiGaussianLineIntegrand a) := by
  unfold deBruijnNewmanTitchmarshPhiGaussianLineIntegrand
  simp_rw [deBruijnNewmanTitchmarshPhiExponent_line_eq]
  apply Integrable.mul_const
  apply integrable_cexp_quadratic'
  simpa only [Complex.ofReal_re] using
    (neg_lt_zero.mpr (one_div_pos.mpr (mul_pos (by norm_num) Real.pi_pos)))

/-- The actual source integrand is bounded by a constant multiple of its Gaussian core. -/
theorem norm_deBruijnNewmanTitchmarshPhiLineIntegrand_le
    (a : ℂ) {C : ℝ}
    (hC : ∀ v : ℝ,
      ‖deBruijnNewmanTitchmarshPhiDenominatorInverse v‖ ≤ C)
    (v : ℝ) :
    ‖deBruijnNewmanTitchmarshPhiLineIntegrand a v‖ ≤
      C * ‖deBruijnNewmanTitchmarshPhiGaussianLineIntegrand a v‖ := by
  have heq : deBruijnNewmanTitchmarshPhiLineIntegrand a v =
      deBruijnNewmanTitchmarshPhiGaussianLineIntegrand a v *
        deBruijnNewmanTitchmarshPhiDenominatorInverse v := by
    unfold deBruijnNewmanTitchmarshPhiLineIntegrand
    unfold deBruijnNewmanTitchmarshPhiGaussianLineIntegrand
    unfold deBruijnNewmanTitchmarshPhiDenominatorInverse
    rw [div_eq_mul_inv]
    ring
  rw [heq, norm_mul]
  calc
    ‖deBruijnNewmanTitchmarshPhiGaussianLineIntegrand a v‖ *
          ‖deBruijnNewmanTitchmarshPhiDenominatorInverse v‖ ≤
        ‖deBruijnNewmanTitchmarshPhiGaussianLineIntegrand a v‖ * C :=
      mul_le_mul_of_nonneg_left (hC v) (norm_nonneg _)
    _ = C * ‖deBruijnNewmanTitchmarshPhiGaussianLineIntegrand a v‖ := by ring

/-- Absolute integrability of Titchmarsh's actual auxiliary contour `(2.10.1)`. -/
theorem integrable_deBruijnNewmanTitchmarshPhiLineIntegrand (a : ℂ) :
    Integrable (deBruijnNewmanTitchmarshPhiLineIntegrand a) := by
  obtain ⟨C, _hCpos, hC⟩ :=
    exists_pos_norm_deBruijnNewmanTitchmarshPhiDenominatorInverse_le
  have hmajor : Integrable (fun v : ℝ ↦
      C * ‖deBruijnNewmanTitchmarshPhiGaussianLineIntegrand a v‖) :=
    (integrable_deBruijnNewmanTitchmarshPhiGaussianLineIntegrand a).norm.const_mul C
  refine hmajor.mono'
    (continuous_deBruijnNewmanTitchmarshPhiLineIntegrand a).aestronglyMeasurable ?_
  exact ae_of_all _ fun v ↦
    norm_deBruijnNewmanTitchmarshPhiLineIntegrand_le a hC v

/-- Pointwise denominator cancellation behind Titchmarsh's first difference equation. -/
theorem deBruijnNewmanTitchmarshPhiLineIntegrand_add_one_sub (a : ℂ) (v : ℝ) :
    deBruijnNewmanTitchmarshPhiLineIntegrand (a + 1) v -
        deBruijnNewmanTitchmarshPhiLineIntegrand a v =
      deBruijnNewmanTitchmarshPhiGaussianLineIntegrand a v := by
  have hexponent :
      deBruijnNewmanTitchmarshPhiExponent (a + 1)
          (deBruijnNewmanTitchmarshPhiLine v) =
        deBruijnNewmanTitchmarshPhiExponent a
            (deBruijnNewmanTitchmarshPhiLine v) +
          deBruijnNewmanTitchmarshPhiLine v := by
    unfold deBruijnNewmanTitchmarshPhiExponent
    ring
  unfold deBruijnNewmanTitchmarshPhiLineIntegrand
  unfold deBruijnNewmanTitchmarshPhiGaussianLineIntegrand
  rw [hexponent, Complex.exp_add]
  have hden := deBruijnNewmanTitchmarshPhiDenominator_ne_zero v
  unfold deBruijnNewmanTitchmarshPhiDenominator at hden ⊢
  field_simp

/-- Exact Gaussian evaluation in Titchmarsh `(2.10.2)`, including the contour orientation. -/
theorem integral_deBruijnNewmanTitchmarshPhiGaussianLineIntegrand (a : ℂ) :
    ∫ v : ℝ, deBruijnNewmanTitchmarshPhiGaussianLineIntegrand a v =
      2 * Real.pi *
        Complex.exp (Complex.I * Real.pi * (a ^ 2 + 1 / 4)) := by
  unfold deBruijnNewmanTitchmarshPhiGaussianLineIntegrand
  simp_rw [deBruijnNewmanTitchmarshPhiExponent_line_eq]
  rw [MeasureTheory.integral_mul_const]
  rw [integral_cexp_quadratic (by
    simpa only [Complex.ofReal_re] using
      (neg_lt_zero.mpr (one_div_pos.mpr (mul_pos (by norm_num) Real.pi_pos))))]
  have hroot :
      (((Real.pi : ℂ) / -(((-(1 / (4 * Real.pi)) : ℝ) : ℂ))) ^ (1 / 2 : ℂ)) =
        (2 * Real.pi : ℝ) := by
    have hpos : 0 ≤ 4 * Real.pi ^ 2 := by positivity
    rw [show (Real.pi : ℂ) / -(((-(1 / (4 * Real.pi)) : ℝ) : ℂ)) =
        ((4 * Real.pi ^ 2 : ℝ) : ℂ) by
      push_cast
      field_simp [Real.pi_ne_zero]]
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
    calc
      ((4 * Real.pi ^ 2 : ℝ) : ℂ) ^ ((1 / 2 : ℝ) : ℂ) =
          (((4 * Real.pi ^ 2) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
            exact (Complex.ofReal_cpow hpos (1 / 2 : ℝ)).symm
      _ = (Real.sqrt (4 * Real.pi ^ 2) : ℝ) := by rw [Real.sqrt_eq_rpow]
      _ = (2 * Real.pi : ℝ) := by
        rw [show 4 * Real.pi ^ 2 = (2 * Real.pi) ^ 2 by ring,
          Real.sqrt_sq_eq_abs, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  rw [hroot]
  have hexponent :
      Complex.I * Real.pi / 4 - Real.pi * a -
          (deBruijnNewmanTitchmarshPhiDirection * (a - Complex.I / 2)) ^ 2 /
            (4 * (((-(1 / (4 * Real.pi)) : ℝ) : ℂ))) =
        Complex.I * Real.pi * a ^ 2 := by
    rw [mul_pow, deBruijnNewmanTitchmarshPhiDirection_sq]
    push_cast
    field_simp [Real.pi_ne_zero]
    ring_nf
    rw [Complex.I_sq]
    rw [show Complex.I ^ 3 = -Complex.I by
      rw [pow_succ, Complex.I_sq]
      ring]
    ring
  rw [hexponent]
  rw [show deBruijnNewmanTitchmarshPhiDirection =
      Complex.exp (Complex.I * Real.pi / 4) by
    rw [deBruijnNewmanTitchmarshPhiDirection]
    congr 1
    push_cast
    ring]
  push_cast
  rw [mul_assoc, ← Complex.exp_add]
  congr 1
  ring

/-- Titchmarsh's exact first difference equation `(2.10.2)`. -/
theorem deBruijnNewmanTitchmarshPhi_add_one_sub (a : ℂ) :
    deBruijnNewmanTitchmarshPhi (a + 1) -
        deBruijnNewmanTitchmarshPhi a =
      2 * Real.pi *
        Complex.exp (Complex.I * Real.pi * (a ^ 2 + 1 / 4)) := by
  unfold deBruijnNewmanTitchmarshPhi
  rw [← integral_sub
    (integrable_deBruijnNewmanTitchmarshPhiLineIntegrand (a + 1))
    (integrable_deBruijnNewmanTitchmarshPhiLineIntegrand a)]
  simp_rw [deBruijnNewmanTitchmarshPhiLineIntegrand_add_one_sub]
  exact integral_deBruijnNewmanTitchmarshPhiGaussianLineIntegrand a

/-- Half the perpendicular separation of `L` and `L - 2*pi*i` after rotating the contour. -/
def deBruijnNewmanTitchmarshPhiRotatedHalfWidth : ℝ :=
  Real.pi * Real.sqrt 2 / 2

/-- Pull the source plane back by the `pi/4` contour direction, centered at the crossed pole. -/
def deBruijnNewmanTitchmarshPhiPullbackPoint (z : ℂ) : ℂ :=
  deBruijnNewmanTitchmarshPhiDirection * z

/-- The source denominator in the rotated coordinate. -/
def deBruijnNewmanTitchmarshPhiPullbackDenominator (z : ℂ) : ℂ :=
  deBruijnNewmanTitchmarshPhiDenominator
    (deBruijnNewmanTitchmarshPhiPullbackPoint z)

/-- The source numerator, including the Jacobian, in the rotated coordinate. -/
def deBruijnNewmanTitchmarshPhiPullbackNumerator (a z : ℂ) : ℂ :=
  Complex.exp (deBruijnNewmanTitchmarshPhiExponent a
      (deBruijnNewmanTitchmarshPhiPullbackPoint z)) *
    deBruijnNewmanTitchmarshPhiDirection

/-- The pulled-back Titchmarsh kernel, including the complex Jacobian. -/
def deBruijnNewmanTitchmarshPhiPullbackKernel (a z : ℂ) : ℂ :=
  deBruijnNewmanTitchmarshPhiPullbackNumerator a z /
    deBruijnNewmanTitchmarshPhiPullbackDenominator z

/-- An open rotated band containing the finite contour and only the crossed pole. -/
def deBruijnNewmanTitchmarshPhiPullbackBand : Set ℂ :=
  {z | |z.im| < Real.pi}

theorem deBruijnNewmanTitchmarshPhiRotatedHalfWidth_pos :
    0 < deBruijnNewmanTitchmarshPhiRotatedHalfWidth := by
  rw [deBruijnNewmanTitchmarshPhiRotatedHalfWidth]
  positivity

theorem deBruijnNewmanTitchmarshPhiRotatedHalfWidth_lt_pi :
    deBruijnNewmanTitchmarshPhiRotatedHalfWidth < Real.pi := by
  have hsqrt : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  rw [deBruijnNewmanTitchmarshPhiRotatedHalfWidth]
  nlinarith [Real.pi_pos]

theorem isOpen_deBruijnNewmanTitchmarshPhiPullbackBand :
    IsOpen deBruijnNewmanTitchmarshPhiPullbackBand := by
  exact isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const

theorem zero_mem_deBruijnNewmanTitchmarshPhiPullbackBand :
    (0 : ℂ) ∈ deBruijnNewmanTitchmarshPhiPullbackBand := by
  rw [deBruijnNewmanTitchmarshPhiPullbackBand]
  simpa using Real.pi_pos

theorem deBruijnNewmanTitchmarshPhiPullbackBand_mem_nhds :
    deBruijnNewmanTitchmarshPhiPullbackBand ∈ 𝓝 (0 : ℂ) :=
  isOpen_deBruijnNewmanTitchmarshPhiPullbackBand.mem_nhds
    zero_mem_deBruijnNewmanTitchmarshPhiPullbackBand

@[simp] theorem deBruijnNewmanTitchmarshPhiPullbackPoint_zero :
    deBruijnNewmanTitchmarshPhiPullbackPoint 0 = 0 := by
  simp [deBruijnNewmanTitchmarshPhiPullbackPoint]

@[simp] theorem deBruijnNewmanTitchmarshPhiPullbackPoint_re (z : ℂ) :
    (deBruijnNewmanTitchmarshPhiPullbackPoint z).re =
      (Real.sqrt 2 / 2) * (z.re - z.im) := by
  rw [deBruijnNewmanTitchmarshPhiPullbackPoint]
  simp only [Complex.mul_re, deBruijnNewmanTitchmarshPhiDirection_re,
    deBruijnNewmanTitchmarshPhiDirection_im]
  ring

@[simp] theorem deBruijnNewmanTitchmarshPhiPullbackPoint_im (z : ℂ) :
    (deBruijnNewmanTitchmarshPhiPullbackPoint z).im =
      (Real.sqrt 2 / 2) * (z.re + z.im) := by
  rw [deBruijnNewmanTitchmarshPhiPullbackPoint]
  simp only [Complex.mul_im, deBruijnNewmanTitchmarshPhiDirection_re,
    deBruijnNewmanTitchmarshPhiDirection_im]
  ring

/-- Inside the rotated band, the transformed denominator vanishes only at the origin. -/
theorem deBruijnNewmanTitchmarshPhiPullbackDenominator_ne_zero_of_ne
    {z : ℂ} (hz : z ∈ deBruijnNewmanTitchmarshPhiPullbackBand) (hz0 : z ≠ 0) :
    deBruijnNewmanTitchmarshPhiPullbackDenominator z ≠ 0 := by
  intro hzero
  have hexp : Complex.exp (deBruijnNewmanTitchmarshPhiPullbackPoint z) = 1 := by
    exact sub_eq_zero.mp hzero
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp
  have hre := congrArg Complex.re hn
  have him := congrArg Complex.im hn
  have hreR : ((n : ℂ) * (2 * Real.pi * Complex.I)).re = 0 := by simp
  have himR : ((n : ℂ) * (2 * Real.pi * Complex.I)).im =
      (n : ℝ) * (2 * Real.pi) := by simp
  rw [deBruijnNewmanTitchmarshPhiPullbackPoint_re, hreR] at hre
  rw [deBruijnNewmanTitchmarshPhiPullbackPoint_im, himR] at him
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hcoord : z.re = z.im := by
    have hcoeff : Real.sqrt 2 / 2 ≠ 0 := by positivity
    exact sub_eq_zero.mp ((mul_eq_zero.mp hre).resolve_left hcoeff)
  rw [deBruijnNewmanTitchmarshPhiPullbackBand] at hz
  simp only [Set.mem_setOf_eq] at hz
  have hzim := abs_lt.mp hz
  have him' : Real.sqrt 2 * z.im = (n : ℝ) * (2 * Real.pi) := by
    rw [hcoord] at him
    nlinarith
  have hlowMul := mul_lt_mul_of_pos_left hzim.1 hsqrt
  have huppMul := mul_lt_mul_of_pos_left hzim.2 hsqrt
  have hsqrtLt : Real.sqrt 2 < 2 := by nlinarith
  have hnLowR : (-1 : ℝ) < n := by
    nlinarith [him', Real.pi_pos]
  have hnUppR : (n : ℝ) < 1 := by
    nlinarith [him', Real.pi_pos]
  have hnLowZ : (-1 : ℤ) < n := by exact_mod_cast hnLowR
  have hnUppZ : n < (1 : ℤ) := by exact_mod_cast hnUppR
  have hn : n = 0 := by omega
  rw [hn] at him'
  norm_num at him'
  have hzim0 : z.im = 0 := him'
  have hzre0 : z.re = 0 := by rw [hcoord, hzim0]
  apply hz0
  exact Complex.ext hzre0 hzim0

theorem deBruijnNewmanTitchmarshPhiDirection_ne_zero :
    deBruijnNewmanTitchmarshPhiDirection ≠ 0 := by
  intro hzero
  have := congrArg norm hzero
  simp at this

theorem hasDerivAt_deBruijnNewmanTitchmarshPhiPullbackPoint (z : ℂ) :
    HasDerivAt deBruijnNewmanTitchmarshPhiPullbackPoint
      deBruijnNewmanTitchmarshPhiDirection z := by
  unfold deBruijnNewmanTitchmarshPhiPullbackPoint
  simpa only [id_eq, mul_one] using
    (hasDerivAt_id z).const_mul deBruijnNewmanTitchmarshPhiDirection

theorem hasDerivAt_deBruijnNewmanTitchmarshPhiPullbackDenominator (z : ℂ) :
    HasDerivAt deBruijnNewmanTitchmarshPhiPullbackDenominator
      (Complex.exp (deBruijnNewmanTitchmarshPhiPullbackPoint z) *
        deBruijnNewmanTitchmarshPhiDirection) z := by
  unfold deBruijnNewmanTitchmarshPhiPullbackDenominator
  unfold deBruijnNewmanTitchmarshPhiDenominator
  exact ((Complex.hasDerivAt_exp _).comp z
    (hasDerivAt_deBruijnNewmanTitchmarshPhiPullbackPoint z)).sub_const 1

@[simp] theorem deBruijnNewmanTitchmarshPhiPullbackDenominator_zero :
    deBruijnNewmanTitchmarshPhiPullbackDenominator 0 = 0 := by
  simp [deBruijnNewmanTitchmarshPhiPullbackDenominator,
    deBruijnNewmanTitchmarshPhiDenominator]

theorem deriv_deBruijnNewmanTitchmarshPhiPullbackDenominator_zero :
    deriv deBruijnNewmanTitchmarshPhiPullbackDenominator 0 =
      deBruijnNewmanTitchmarshPhiDirection := by
  simpa using
    (hasDerivAt_deBruijnNewmanTitchmarshPhiPullbackDenominator 0).deriv

/-- The divided denominator has no zero in the full rotated band, including at the pole. -/
theorem dslope_deBruijnNewmanTitchmarshPhiPullbackDenominator_ne_zero
    {z : ℂ} (hz : z ∈ deBruijnNewmanTitchmarshPhiPullbackBand) :
    dslope deBruijnNewmanTitchmarshPhiPullbackDenominator 0 z ≠ 0 := by
  by_cases hz0 : z = 0
  · subst z
    rw [dslope_same, deriv_deBruijnNewmanTitchmarshPhiPullbackDenominator_zero]
    exact deBruijnNewmanTitchmarshPhiDirection_ne_zero
  · intro hslope
    have hrel := sub_smul_dslope
      deBruijnNewmanTitchmarshPhiPullbackDenominator 0 z
    have hzero : deBruijnNewmanTitchmarshPhiPullbackDenominator z = 0 := by
      simpa [hslope] using hrel.symm
    exact deBruijnNewmanTitchmarshPhiPullbackDenominator_ne_zero_of_ne hz hz0 hzero

/-- The analytic numerator divided by the denominator's removable first slope. -/
def deBruijnNewmanTitchmarshPhiPullbackCore (a z : ℂ) : ℂ :=
  deBruijnNewmanTitchmarshPhiPullbackNumerator a z /
    dslope deBruijnNewmanTitchmarshPhiPullbackDenominator 0 z

/-- The pole-subtracted pullback kernel, with its value at the pole supplied by `dslope`. -/
def deBruijnNewmanTitchmarshPhiPullbackRemovable (a z : ℂ) : ℂ :=
  dslope (deBruijnNewmanTitchmarshPhiPullbackCore a) 0 z

theorem differentiableOn_deBruijnNewmanTitchmarshPhiPullbackNumerator (a : ℂ) :
    DifferentiableOn ℂ (deBruijnNewmanTitchmarshPhiPullbackNumerator a)
      deBruijnNewmanTitchmarshPhiPullbackBand := by
  intro z _
  unfold deBruijnNewmanTitchmarshPhiPullbackNumerator
  unfold deBruijnNewmanTitchmarshPhiExponent
  have hp : DifferentiableAt ℂ deBruijnNewmanTitchmarshPhiPullbackPoint z :=
    (hasDerivAt_deBruijnNewmanTitchmarshPhiPullbackPoint z).differentiableAt
  exact (by fun_prop : DifferentiableAt ℂ
    (fun z : ℂ ↦ Complex.exp
      (Complex.I * deBruijnNewmanTitchmarshPhiPullbackPoint z ^ 2 /
          (4 * Real.pi) + a * deBruijnNewmanTitchmarshPhiPullbackPoint z) *
        deBruijnNewmanTitchmarshPhiDirection) z).differentiableWithinAt

theorem differentiableOn_deBruijnNewmanTitchmarshPhiPullbackDenominator :
    DifferentiableOn ℂ deBruijnNewmanTitchmarshPhiPullbackDenominator
      deBruijnNewmanTitchmarshPhiPullbackBand :=
  fun z _ ↦ (hasDerivAt_deBruijnNewmanTitchmarshPhiPullbackDenominator z).differentiableAt
    |>.differentiableWithinAt

theorem differentiableOn_deBruijnNewmanTitchmarshPhiPullbackCore (a : ℂ) :
    DifferentiableOn ℂ (deBruijnNewmanTitchmarshPhiPullbackCore a)
      deBruijnNewmanTitchmarshPhiPullbackBand := by
  have hdenSlope : DifferentiableOn ℂ
      (dslope deBruijnNewmanTitchmarshPhiPullbackDenominator 0)
      deBruijnNewmanTitchmarshPhiPullbackBand :=
    (Complex.differentiableOn_dslope
      deBruijnNewmanTitchmarshPhiPullbackBand_mem_nhds).mpr
      differentiableOn_deBruijnNewmanTitchmarshPhiPullbackDenominator
  exact (differentiableOn_deBruijnNewmanTitchmarshPhiPullbackNumerator a).div
    hdenSlope fun _ hz ↦
      dslope_deBruijnNewmanTitchmarshPhiPullbackDenominator_ne_zero hz

/-- The explicitly pole-subtracted pullback kernel is holomorphic throughout the band. -/
theorem differentiableOn_deBruijnNewmanTitchmarshPhiPullbackRemovable (a : ℂ) :
    DifferentiableOn ℂ (deBruijnNewmanTitchmarshPhiPullbackRemovable a)
      deBruijnNewmanTitchmarshPhiPullbackBand := by
  change DifferentiableOn ℂ
    (dslope (deBruijnNewmanTitchmarshPhiPullbackCore a) 0)
      deBruijnNewmanTitchmarshPhiPullbackBand
  rw [Complex.differentiableOn_dslope
    deBruijnNewmanTitchmarshPhiPullbackBand_mem_nhds]
  exact differentiableOn_deBruijnNewmanTitchmarshPhiPullbackCore a

@[simp] theorem deBruijnNewmanTitchmarshPhiPullbackCore_zero (a : ℂ) :
    deBruijnNewmanTitchmarshPhiPullbackCore a 0 = 1 := by
  rw [deBruijnNewmanTitchmarshPhiPullbackCore,
    deBruijnNewmanTitchmarshPhiPullbackNumerator,
    deBruijnNewmanTitchmarshPhiPullbackPoint_zero, dslope_same,
    deriv_deBruijnNewmanTitchmarshPhiPullbackDenominator_zero]
  simp [deBruijnNewmanTitchmarshPhiExponent,
    deBruijnNewmanTitchmarshPhiDirection_ne_zero]

theorem deBruijnNewmanTitchmarshPhiPullbackCore_eq_mul_kernel
    (a : ℂ) {z : ℂ} (hz : z ∈ deBruijnNewmanTitchmarshPhiPullbackBand)
    (hz0 : z ≠ 0) :
    deBruijnNewmanTitchmarshPhiPullbackCore a z =
      z * deBruijnNewmanTitchmarshPhiPullbackKernel a z := by
  have hden := deBruijnNewmanTitchmarshPhiPullbackDenominator_ne_zero_of_ne hz hz0
  change
    deBruijnNewmanTitchmarshPhiPullbackNumerator a z /
        dslope deBruijnNewmanTitchmarshPhiPullbackDenominator 0 z =
      z * (deBruijnNewmanTitchmarshPhiPullbackNumerator a z /
        deBruijnNewmanTitchmarshPhiPullbackDenominator z)
  rw [dslope_of_ne _ hz0]
  simp only [slope, sub_zero, vsub_eq_sub, smul_eq_mul,
    deBruijnNewmanTitchmarshPhiPullbackDenominator_zero]
  field_simp [hz0, hden]

/-- Away from the crossed pole, the pulled-back kernel is `1/z` plus a holomorphic remainder. -/
theorem deBruijnNewmanTitchmarshPhiPullbackKernel_eq_inv_add_removable
    (a : ℂ) {z : ℂ} (hz : z ∈ deBruijnNewmanTitchmarshPhiPullbackBand)
    (hz0 : z ≠ 0) :
    deBruijnNewmanTitchmarshPhiPullbackKernel a z =
      z⁻¹ + deBruijnNewmanTitchmarshPhiPullbackRemovable a z := by
  have hcore := deBruijnNewmanTitchmarshPhiPullbackCore_eq_mul_kernel a hz hz0
  have hslope := sub_smul_dslope
    (deBruijnNewmanTitchmarshPhiPullbackCore a) 0 z
  rw [deBruijnNewmanTitchmarshPhiPullbackCore_zero] at hslope
  simp only [sub_zero, smul_eq_mul] at hslope
  change z * deBruijnNewmanTitchmarshPhiPullbackRemovable a z =
      deBruijnNewmanTitchmarshPhiPullbackCore a z - 1 at hslope
  rw [hcore] at hslope
  have hsub :
      (deBruijnNewmanTitchmarshPhiPullbackKernel a z -
          deBruijnNewmanTitchmarshPhiPullbackRemovable a z) * z = 1 := by
    calc
      (deBruijnNewmanTitchmarshPhiPullbackKernel a z -
          deBruijnNewmanTitchmarshPhiPullbackRemovable a z) * z =
          z * deBruijnNewmanTitchmarshPhiPullbackKernel a z -
            z * deBruijnNewmanTitchmarshPhiPullbackRemovable a z := by ring
      _ = 1 := by rw [hslope]; ring
  have heq :
      deBruijnNewmanTitchmarshPhiPullbackKernel a z -
          deBruijnNewmanTitchmarshPhiPullbackRemovable a z = z⁻¹ := by
    rw [← one_div]
    exact (eq_div_iff hz0).2 hsub
  linear_combination heq

open scoped Interval

theorem intervalIntegrable_deBruijnNewmanTitchmarshPhiPullbackRemovable_affine
    (a u v : ℂ) (p q : ℝ)
    (hmap : ∀ t ∈ Set.uIcc p q,
      u + (t : ℂ) * v ∈ deBruijnNewmanTitchmarshPhiPullbackBand) :
    IntervalIntegrable
      (fun t : ℝ ↦ deBruijnNewmanTitchmarshPhiPullbackRemovable a
        (u + (t : ℂ) * v)) volume p q := by
  apply ContinuousOn.intervalIntegrable
  apply (differentiableOn_deBruijnNewmanTitchmarshPhiPullbackRemovable a).continuousOn.comp
    (continuousOn_const.add (Complex.continuous_ofReal.continuousOn.mul continuousOn_const))
  exact hmap

/-- Integrate the exact pole decomposition along an affine segment in the rotated band. -/
theorem integral_deBruijnNewmanTitchmarshPhiPullbackKernel_affine_eq
    (a u v : ℂ) (p q : ℝ)
    (hmap : ∀ t ∈ Set.uIcc p q,
      u + (t : ℂ) * v ∈ deBruijnNewmanTitchmarshPhiPullbackBand)
    (hne : ∀ t ∈ Set.uIcc p q, u + (t : ℂ) * v ≠ 0) :
    (∫ t : ℝ in p..q,
        deBruijnNewmanTitchmarshPhiPullbackKernel a (u + (t : ℂ) * v)) =
      (∫ t : ℝ in p..q, (u + (t : ℂ) * v)⁻¹) +
        ∫ t : ℝ in p..q,
          deBruijnNewmanTitchmarshPhiPullbackRemovable a (u + (t : ℂ) * v) := by
  have hinv := intervalIntegrable_inv_affine u v p q hne
  have hrem := intervalIntegrable_deBruijnNewmanTitchmarshPhiPullbackRemovable_affine
    a u v p q hmap
  calc
    (∫ t : ℝ in p..q,
        deBruijnNewmanTitchmarshPhiPullbackKernel a (u + (t : ℂ) * v)) =
        ∫ t : ℝ in p..q,
          ((u + (t : ℂ) * v)⁻¹ +
            deBruijnNewmanTitchmarshPhiPullbackRemovable a
              (u + (t : ℂ) * v)) := by
                apply intervalIntegral.integral_congr
                intro t ht
                exact deBruijnNewmanTitchmarshPhiPullbackKernel_eq_inv_add_removable
                  a (hmap t ht) (hne t ht)
    _ = (∫ t : ℝ in p..q, (u + (t : ℂ) * v)⁻¹) +
        ∫ t : ℝ in p..q,
          deBruijnNewmanTitchmarshPhiPullbackRemovable a
            (u + (t : ℂ) * v) := by
              rw [intervalIntegral.integral_add hinv hrem]

/-- Cauchy--Goursat for the removable pullback on the finite rotated rectangle. -/
theorem deBruijnNewmanTitchmarshPhiPullbackRemovable_boundary_rect_eq_zero
    (a : ℂ) (l R : ℝ) :
    (∫ x : ℝ in l..R,
        deBruijnNewmanTitchmarshPhiPullbackRemovable a
          (x + (-deBruijnNewmanTitchmarshPhiRotatedHalfWidth) * Complex.I)) -
      (∫ x : ℝ in l..R,
        deBruijnNewmanTitchmarshPhiPullbackRemovable a
          (x + deBruijnNewmanTitchmarshPhiRotatedHalfWidth * Complex.I)) +
      Complex.I * (∫ t : ℝ in
          -deBruijnNewmanTitchmarshPhiRotatedHalfWidth..
            deBruijnNewmanTitchmarshPhiRotatedHalfWidth,
        deBruijnNewmanTitchmarshPhiPullbackRemovable a (R + t * Complex.I)) -
      Complex.I * (∫ t : ℝ in
          -deBruijnNewmanTitchmarshPhiRotatedHalfWidth..
            deBruijnNewmanTitchmarshPhiRotatedHalfWidth,
        deBruijnNewmanTitchmarshPhiPullbackRemovable a (l + t * Complex.I)) = 0 := by
  let z : ℂ := Complex.mk l (-deBruijnNewmanTitchmarshPhiRotatedHalfWidth)
  let w : ℂ := Complex.mk R deBruijnNewmanTitchmarshPhiRotatedHalfWidth
  have hdiff : DifferentiableOn ℂ
      (deBruijnNewmanTitchmarshPhiPullbackRemovable a)
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) := by
    apply (differentiableOn_deBruijnNewmanTitchmarshPhiPullbackRemovable a).mono
    intro q hq
    rw [Complex.mem_reProdIm] at hq
    rw [deBruijnNewmanTitchmarshPhiPullbackBand]
    simp only [Set.mem_setOf_eq]
    have hh := deBruijnNewmanTitchmarshPhiRotatedHalfWidth_pos
    have hlt := deBruijnNewmanTitchmarshPhiRotatedHalfWidth_lt_pi
    have him : -deBruijnNewmanTitchmarshPhiRotatedHalfWidth ≤ q.im ∧
        q.im ≤ deBruijnNewmanTitchmarshPhiRotatedHalfWidth := by
      have him' := hq.2
      rw [uIcc_of_le (neg_le_self hh.le)] at him'
      simpa only [z, w, Set.mem_Icc] using him'
    rw [abs_lt]
    constructor <;> linarith
  have hboundary := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (deBruijnNewmanTitchmarshPhiPullbackRemovable a) z w hdiff
  simpa only [z, w, Complex.ofReal_neg, smul_eq_mul] using hboundary

/-- The finite rotated rectangle crosses exactly the pole at zero, of residue one. -/
theorem deBruijnNewmanTitchmarshPhiPullbackKernel_boundary_rect
    (a : ℂ) {l R : ℝ} (hl : l < 0) (hR : 0 < R) :
    (∫ x : ℝ in l..R,
        deBruijnNewmanTitchmarshPhiPullbackKernel a
          (x + (-deBruijnNewmanTitchmarshPhiRotatedHalfWidth) * Complex.I)) -
      (∫ x : ℝ in l..R,
        deBruijnNewmanTitchmarshPhiPullbackKernel a
          (x + deBruijnNewmanTitchmarshPhiRotatedHalfWidth * Complex.I)) +
      Complex.I * (∫ t : ℝ in
          -deBruijnNewmanTitchmarshPhiRotatedHalfWidth..
            deBruijnNewmanTitchmarshPhiRotatedHalfWidth,
        deBruijnNewmanTitchmarshPhiPullbackKernel a (R + t * Complex.I)) -
      Complex.I * (∫ t : ℝ in
          -deBruijnNewmanTitchmarshPhiRotatedHalfWidth..
            deBruijnNewmanTitchmarshPhiRotatedHalfWidth,
        deBruijnNewmanTitchmarshPhiPullbackKernel a (l + t * Complex.I)) =
      2 * (Real.pi : ℂ) * Complex.I := by
  let h := deBruijnNewmanTitchmarshPhiRotatedHalfWidth
  have hh : 0 < h := deBruijnNewmanTitchmarshPhiRotatedHalfWidth_pos
  have hha : h < Real.pi := deBruijnNewmanTitchmarshPhiRotatedHalfWidth_lt_pi
  have hhorizontal (y : ℝ) (hy : |y| = h) :
      ∀ x ∈ Set.uIcc l R,
        (y : ℂ) * Complex.I + (x : ℂ) * 1 ∈
          deBruijnNewmanTitchmarshPhiPullbackBand := by
    intro x _
    rw [deBruijnNewmanTitchmarshPhiPullbackBand]
    simp only [Set.mem_setOf_eq, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.ofReal_im, mul_one, add_zero]
    simpa [hy] using hha
  have hvertical (c : ℝ) :
      ∀ t ∈ Set.uIcc (-h) h,
        (c : ℂ) + (t : ℂ) * Complex.I ∈
          deBruijnNewmanTitchmarshPhiPullbackBand := by
    intro t ht
    rw [deBruijnNewmanTitchmarshPhiPullbackBand]
    simp only [Set.mem_setOf_eq, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, mul_one, zero_add]
    rw [uIcc_of_le (neg_le_self hh.le)] at ht
    rw [abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  have hbottom_ne : ∀ x ∈ Set.uIcc l R,
      ((-h : ℝ) : ℂ) * Complex.I + (x : ℂ) * 1 ≠ 0 := by
    intro x _ hzero
    have him := congrArg Complex.im hzero
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.ofReal_im, mul_one, add_zero, Complex.zero_im] at him
    linarith
  have htop_ne : ∀ x ∈ Set.uIcc l R,
      (h : ℂ) * Complex.I + (x : ℂ) * 1 ≠ 0 := by
    intro x _ hzero
    have him := congrArg Complex.im hzero
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.ofReal_im, mul_one, add_zero, Complex.zero_im] at him
    linarith
  have hright_ne : ∀ t ∈ Set.uIcc (-h) h,
      (R : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
    intro t _ hzero
    have hre := congrArg Complex.re hzero
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
      Complex.zero_re] at hre
    linarith
  have hleft_ne : ∀ t ∈ Set.uIcc (-h) h,
      (l : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
    intro t _ hzero
    have hre := congrArg Complex.re hzero
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
      Complex.zero_re] at hre
    linarith
  have hbottom := integral_deBruijnNewmanTitchmarshPhiPullbackKernel_affine_eq
    a (((-h : ℝ) : ℂ) * Complex.I) 1 l R
      (hhorizontal (-h) (by simp [h, hh.le])) hbottom_ne
  have htop := integral_deBruijnNewmanTitchmarshPhiPullbackKernel_affine_eq
    a ((h : ℂ) * Complex.I) 1 l R (hhorizontal h (abs_of_pos hh)) htop_ne
  have hright := integral_deBruijnNewmanTitchmarshPhiPullbackKernel_affine_eq
    a R Complex.I (-h) h (hvertical R) hright_ne
  have hleft := integral_deBruijnNewmanTitchmarshPhiPullbackKernel_affine_eq
    a l Complex.I (-h) h (hvertical l) hleft_ne
  have hrem := deBruijnNewmanTitchmarshPhiPullbackRemovable_boundary_rect_eq_zero a l R
  have hinv := integral_inv_boundary_rect_eq_two_pi_mul_I hl hR hh
  change
    (∫ x : ℝ in l..R,
        deBruijnNewmanTitchmarshPhiPullbackKernel a (x + (-h) * Complex.I)) -
      (∫ x : ℝ in l..R,
        deBruijnNewmanTitchmarshPhiPullbackKernel a (x + h * Complex.I)) +
      Complex.I * (∫ t : ℝ in -h..h,
        deBruijnNewmanTitchmarshPhiPullbackKernel a (R + t * Complex.I)) -
      Complex.I * (∫ t : ℝ in -h..h,
        deBruijnNewmanTitchmarshPhiPullbackKernel a (l + t * Complex.I)) = _
  have hbottom' :
      (∫ x : ℝ in l..R,
        deBruijnNewmanTitchmarshPhiPullbackKernel a (x + (-h) * Complex.I)) =
        (∫ x : ℝ in l..R, (x + (-h) * Complex.I)⁻¹) +
          ∫ x : ℝ in l..R,
            deBruijnNewmanTitchmarshPhiPullbackRemovable a (x + (-h) * Complex.I) := by
    simpa only [h, one_mul, mul_one, Complex.ofReal_neg, add_comm] using hbottom
  have htop' :
      (∫ x : ℝ in l..R,
        deBruijnNewmanTitchmarshPhiPullbackKernel a (x + h * Complex.I)) =
        (∫ x : ℝ in l..R, (x + h * Complex.I)⁻¹) +
          ∫ x : ℝ in l..R,
            deBruijnNewmanTitchmarshPhiPullbackRemovable a (x + h * Complex.I) := by
    simpa only [h, one_mul, mul_one, add_comm] using htop
  have hright' :
      (∫ t : ℝ in -h..h,
        deBruijnNewmanTitchmarshPhiPullbackKernel a (R + t * Complex.I)) =
        (∫ t : ℝ in -h..h, (R + t * Complex.I)⁻¹) +
          ∫ t : ℝ in -h..h,
            deBruijnNewmanTitchmarshPhiPullbackRemovable a (R + t * Complex.I) := by
    simpa only [h] using hright
  have hleft' :
      (∫ t : ℝ in -h..h,
        deBruijnNewmanTitchmarshPhiPullbackKernel a (l + t * Complex.I)) =
        (∫ t : ℝ in -h..h, (l + t * Complex.I)⁻¹) +
          ∫ t : ℝ in -h..h,
            deBruijnNewmanTitchmarshPhiPullbackRemovable a (l + t * Complex.I) := by
    simpa only [h] using hleft
  rw [hbottom', htop', hright', hleft']
  have hrem' :
      (∫ x : ℝ in l..R,
          deBruijnNewmanTitchmarshPhiPullbackRemovable a (x + (-h) * Complex.I)) -
        (∫ x : ℝ in l..R,
          deBruijnNewmanTitchmarshPhiPullbackRemovable a (x + h * Complex.I)) +
        Complex.I * (∫ t : ℝ in -h..h,
          deBruijnNewmanTitchmarshPhiPullbackRemovable a (R + t * Complex.I)) -
        Complex.I * (∫ t : ℝ in -h..h,
          deBruijnNewmanTitchmarshPhiPullbackRemovable a (l + t * Complex.I)) = 0 := by
    simpa only [h] using hrem
  have hinv' :
      (∫ x : ℝ in l..R, (x + (-h) * Complex.I)⁻¹) -
        (∫ x : ℝ in l..R, (x + h * Complex.I)⁻¹) +
        Complex.I * (∫ t : ℝ in -h..h, (R + t * Complex.I)⁻¹) -
        Complex.I * (∫ t : ℝ in -h..h, (l + t * Complex.I)⁻¹) =
          2 * (Real.pi : ℂ) * Complex.I := by
    simpa only [h] using hinv
  linear_combination hinv' + hrem'

theorem deBruijnNewmanTitchmarshPhiDirection_top_offset :
    deBruijnNewmanTitchmarshPhiDirection *
        (deBruijnNewmanTitchmarshPhiRotatedHalfWidth * Complex.I) =
      -(Real.pi : ℂ) + deBruijnNewmanTitchmarshPhiDirection *
        deBruijnNewmanTitchmarshPhiRotatedHalfWidth := by
  have hsqrtSq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;>
    simp [deBruijnNewmanTitchmarshPhiRotatedHalfWidth] <;>
    ring_nf <;>
    rw [hsqrtSq] <;>
    ring

theorem deBruijnNewmanTitchmarshPhiDirection_bottom_offset :
    deBruijnNewmanTitchmarshPhiDirection *
        ((-deBruijnNewmanTitchmarshPhiRotatedHalfWidth) * Complex.I) =
      -(Real.pi : ℂ) + 3 * deBruijnNewmanTitchmarshPhiDirection *
          deBruijnNewmanTitchmarshPhiRotatedHalfWidth -
        2 * Real.pi * Complex.I := by
  have hsqrtSq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;>
    simp [deBruijnNewmanTitchmarshPhiRotatedHalfWidth] <;>
    ring_nf <;>
    rw [hsqrtSq] <;>
    ring

theorem deBruijnNewmanTitchmarshPhiPullbackPoint_top (x : ℝ) :
    deBruijnNewmanTitchmarshPhiPullbackPoint
        (x + deBruijnNewmanTitchmarshPhiRotatedHalfWidth * Complex.I) =
      deBruijnNewmanTitchmarshPhiLine
        (x + deBruijnNewmanTitchmarshPhiRotatedHalfWidth) := by
  rw [deBruijnNewmanTitchmarshPhiPullbackPoint,
    deBruijnNewmanTitchmarshPhiLine]
  push_cast
  rw [mul_add, deBruijnNewmanTitchmarshPhiDirection_top_offset]
  ring

theorem deBruijnNewmanTitchmarshPhiPullbackPoint_bottom (x : ℝ) :
    deBruijnNewmanTitchmarshPhiPullbackPoint
        (x + (-deBruijnNewmanTitchmarshPhiRotatedHalfWidth) * Complex.I) =
      deBruijnNewmanTitchmarshPhiLine
          (x + 3 * deBruijnNewmanTitchmarshPhiRotatedHalfWidth) -
        2 * Real.pi * Complex.I := by
  rw [deBruijnNewmanTitchmarshPhiPullbackPoint,
    deBruijnNewmanTitchmarshPhiLine]
  push_cast
  rw [mul_add, deBruijnNewmanTitchmarshPhiDirection_bottom_offset]
  ring

theorem deBruijnNewmanTitchmarshPhiDenominator_sub_two_pi_mul_I (w : ℂ) :
    deBruijnNewmanTitchmarshPhiDenominator
        (w - 2 * Real.pi * Complex.I) =
      deBruijnNewmanTitchmarshPhiDenominator w := by
  unfold deBruijnNewmanTitchmarshPhiDenominator
  have hshift : w - 2 * Real.pi * Complex.I =
      w + ((-1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [hshift, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I]
  ring

theorem deBruijnNewmanTitchmarshPhiExponent_sub_two_pi_mul_I (a w : ℂ) :
    deBruijnNewmanTitchmarshPhiExponent a
        (w - 2 * Real.pi * Complex.I) =
      deBruijnNewmanTitchmarshPhiExponent (a + 1) w +
        (-2 * Real.pi * Complex.I * a) - Real.pi * Complex.I := by
  unfold deBruijnNewmanTitchmarshPhiExponent
  push_cast
  field_simp [Real.pi_ne_zero]
  ring_nf
  rw [Complex.I_sq]
  rw [show Complex.I ^ 3 = -Complex.I by
    rw [pow_succ, Complex.I_sq]
    ring]
  ring

theorem deBruijnNewmanTitchmarshPhiPullbackKernel_top (a : ℂ) (x : ℝ) :
    deBruijnNewmanTitchmarshPhiPullbackKernel a
        (x + deBruijnNewmanTitchmarshPhiRotatedHalfWidth * Complex.I) =
      deBruijnNewmanTitchmarshPhiLineIntegrand a
        (x + deBruijnNewmanTitchmarshPhiRotatedHalfWidth) := by
  rw [deBruijnNewmanTitchmarshPhiPullbackKernel,
    deBruijnNewmanTitchmarshPhiPullbackNumerator,
    deBruijnNewmanTitchmarshPhiPullbackDenominator,
    deBruijnNewmanTitchmarshPhiLineIntegrand,
    deBruijnNewmanTitchmarshPhiPullbackPoint_top]
  ring

theorem deBruijnNewmanTitchmarshPhiPullbackKernel_bottom (a : ℂ) (x : ℝ) :
    deBruijnNewmanTitchmarshPhiPullbackKernel a
        (x + (-deBruijnNewmanTitchmarshPhiRotatedHalfWidth) * Complex.I) =
      -Complex.exp (-2 * Real.pi * Complex.I * a) *
        deBruijnNewmanTitchmarshPhiLineIntegrand (a + 1)
          (x + 3 * deBruijnNewmanTitchmarshPhiRotatedHalfWidth) := by
  rw [deBruijnNewmanTitchmarshPhiPullbackKernel,
    deBruijnNewmanTitchmarshPhiPullbackNumerator,
    deBruijnNewmanTitchmarshPhiPullbackDenominator,
    deBruijnNewmanTitchmarshPhiPullbackPoint_bottom,
    deBruijnNewmanTitchmarshPhiLineIntegrand,
    deBruijnNewmanTitchmarshPhiDenominator_sub_two_pi_mul_I,
    deBruijnNewmanTitchmarshPhiExponent_sub_two_pi_mul_I]
  rw [show deBruijnNewmanTitchmarshPhiExponent (a + 1)
        (deBruijnNewmanTitchmarshPhiLine
          (x + 3 * deBruijnNewmanTitchmarshPhiRotatedHalfWidth)) +
        (-2 * Real.pi * Complex.I * a) - Real.pi * Complex.I =
      deBruijnNewmanTitchmarshPhiExponent (a + 1)
          (deBruijnNewmanTitchmarshPhiLine
            (x + 3 * deBruijnNewmanTitchmarshPhiRotatedHalfWidth)) +
        (-2 * Real.pi * Complex.I * a) +
          (-(Real.pi * Complex.I)) by ring]
  rw [Complex.exp_add, Complex.exp_add, Complex.exp_neg_pi_mul_I]
  ring

/-- The right short side of the finite rotated Titchmarsh rectangle. -/
def deBruijnNewmanTitchmarshPhiRightEndIntegral (a : ℂ) (T : ℝ) : ℂ :=
  Complex.I * (∫ t : ℝ in
      -deBruijnNewmanTitchmarshPhiRotatedHalfWidth..
        deBruijnNewmanTitchmarshPhiRotatedHalfWidth,
    deBruijnNewmanTitchmarshPhiPullbackKernel a (T + t * Complex.I))

/-- The left short side of the finite rotated Titchmarsh rectangle. -/
def deBruijnNewmanTitchmarshPhiLeftEndIntegral (a : ℂ) (T : ℝ) : ℂ :=
  Complex.I * (∫ t : ℝ in
      -deBruijnNewmanTitchmarshPhiRotatedHalfWidth..
        deBruijnNewmanTitchmarshPhiRotatedHalfWidth,
    deBruijnNewmanTitchmarshPhiPullbackKernel a (-T + t * Complex.I))

/-- Exact finite one-pole shift between `L - 2*pi*i` and `L`. -/
theorem deBruijnNewmanTitchmarshPhi_finite_parallel_shift
    (a : ℂ) {T : ℝ} (hT : 0 < T) :
    -Complex.exp (-2 * Real.pi * Complex.I * a) *
        (∫ v : ℝ in
          3 * deBruijnNewmanTitchmarshPhiRotatedHalfWidth - T..
            3 * deBruijnNewmanTitchmarshPhiRotatedHalfWidth + T,
          deBruijnNewmanTitchmarshPhiLineIntegrand (a + 1) v) -
      (∫ v : ℝ in
        deBruijnNewmanTitchmarshPhiRotatedHalfWidth - T..
          deBruijnNewmanTitchmarshPhiRotatedHalfWidth + T,
        deBruijnNewmanTitchmarshPhiLineIntegrand a v) +
      deBruijnNewmanTitchmarshPhiRightEndIntegral a T -
      deBruijnNewmanTitchmarshPhiLeftEndIntegral a T =
        2 * (Real.pi : ℂ) * Complex.I := by
  let h := deBruijnNewmanTitchmarshPhiRotatedHalfWidth
  have hboundary := deBruijnNewmanTitchmarshPhiPullbackKernel_boundary_rect
    a (neg_lt_zero.mpr hT) hT
  have hbottom :
      (∫ x : ℝ in -T..T,
        deBruijnNewmanTitchmarshPhiPullbackKernel a (x + (-h) * Complex.I)) =
      -Complex.exp (-2 * Real.pi * Complex.I * a) *
        (∫ v : ℝ in 3 * h - T..3 * h + T,
          deBruijnNewmanTitchmarshPhiLineIntegrand (a + 1) v) := by
    rw [show (fun x : ℝ ↦
        deBruijnNewmanTitchmarshPhiPullbackKernel a (x + (-h) * Complex.I)) =
      fun x : ℝ ↦ -Complex.exp (-2 * Real.pi * Complex.I * a) *
        deBruijnNewmanTitchmarshPhiLineIntegrand (a + 1) (x + 3 * h) by
          funext x
          simpa only [h] using deBruijnNewmanTitchmarshPhiPullbackKernel_bottom a x]
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_comp_add_right]
    congr 1 <;> ring
  have htop :
      (∫ x : ℝ in -T..T,
        deBruijnNewmanTitchmarshPhiPullbackKernel a (x + h * Complex.I)) =
      ∫ v : ℝ in h - T..h + T,
        deBruijnNewmanTitchmarshPhiLineIntegrand a v := by
    rw [show (fun x : ℝ ↦
        deBruijnNewmanTitchmarshPhiPullbackKernel a (x + h * Complex.I)) =
      fun x : ℝ ↦ deBruijnNewmanTitchmarshPhiLineIntegrand a (x + h) by
          funext x
          simpa only [h] using deBruijnNewmanTitchmarshPhiPullbackKernel_top a x]
    rw [intervalIntegral.integral_comp_add_right]
    congr 1 <;> ring
  have hboundary' :
    (∫ x : ℝ in -T..T,
        deBruijnNewmanTitchmarshPhiPullbackKernel a (x + (-h) * Complex.I)) -
      (∫ x : ℝ in -T..T,
        deBruijnNewmanTitchmarshPhiPullbackKernel a (x + h * Complex.I)) +
      Complex.I * (∫ t : ℝ in -h..h,
        deBruijnNewmanTitchmarshPhiPullbackKernel a (T + t * Complex.I)) -
      Complex.I * (∫ t : ℝ in -h..h,
        deBruijnNewmanTitchmarshPhiPullbackKernel a (-T + t * Complex.I)) =
      2 * (Real.pi : ℂ) * Complex.I
      := by
        simpa only [h, Complex.ofReal_neg] using hboundary
  rw [hbottom, htop] at hboundary'
  simpa only [h, deBruijnNewmanTitchmarshPhiRightEndIntegral,
    deBruijnNewmanTitchmarshPhiLeftEndIntegral] using hboundary'

/-- Exact quadratic exponent in the rotated coordinate. -/
theorem deBruijnNewmanTitchmarshPhiExponent_pullback_eq (a z : ℂ) :
    deBruijnNewmanTitchmarshPhiExponent a
        (deBruijnNewmanTitchmarshPhiPullbackPoint z) =
      ((-(1 / (4 * Real.pi)) : ℝ) : ℂ) * z ^ 2 +
        (a * deBruijnNewmanTitchmarshPhiDirection) * z := by
  rw [deBruijnNewmanTitchmarshPhiExponent,
    deBruijnNewmanTitchmarshPhiPullbackPoint, mul_pow,
    deBruijnNewmanTitchmarshPhiDirection_sq]
  push_cast
  field_simp [Real.pi_ne_zero]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Exact real part of the exponent on a vertical short side. -/
theorem deBruijnNewmanTitchmarshPhiExponent_pullback_re
    (a : ℂ) (x t : ℝ) :
    (deBruijnNewmanTitchmarshPhiExponent a
        (deBruijnNewmanTitchmarshPhiPullbackPoint (x + t * Complex.I))).re =
      -(x ^ 2) / (4 * Real.pi) + t ^ 2 / (4 * Real.pi) +
        (a * deBruijnNewmanTitchmarshPhiDirection).re * x -
        (a * deBruijnNewmanTitchmarshPhiDirection).im * t := by
  rw [deBruijnNewmanTitchmarshPhiExponent_pullback_eq]
  simp [pow_two, Complex.I_sq]
  ring

theorem deBruijnNewmanTitchmarshPhiSqrtTwo_one_le :
    1 ≤ Real.sqrt 2 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]

/-- A coarse uniform lower bound for the denominator on either distant short side. -/
theorem one_half_le_norm_deBruijnNewmanTitchmarshPhiPullbackDenominator_side
    (x t : ℝ) (hx : 6 ≤ |x|)
    (ht : |t| ≤ deBruijnNewmanTitchmarshPhiRotatedHalfWidth) :
    (1 / 2 : ℝ) ≤
      ‖deBruijnNewmanTitchmarshPhiPullbackDenominator (x + t * Complex.I)‖ := by
  have hh4 : deBruijnNewmanTitchmarshPhiRotatedHalfWidth < 4 :=
    deBruijnNewmanTitchmarshPhiRotatedHalfWidth_lt_pi.trans Real.pi_lt_four
  have hq : (1 / 2 : ℝ) ≤ Real.sqrt 2 / 2 := by
    linarith [deBruijnNewmanTitchmarshPhiSqrtTwo_one_le]
  have hq0 : 0 ≤ Real.sqrt 2 / 2 := by positivity
  have htLower : -deBruijnNewmanTitchmarshPhiRotatedHalfWidth ≤ t :=
    (abs_le.mp ht).1
  have htUpper : t ≤ deBruijnNewmanTitchmarshPhiRotatedHalfWidth :=
    (abs_le.mp ht).2
  unfold deBruijnNewmanTitchmarshPhiPullbackDenominator
  unfold deBruijnNewmanTitchmarshPhiDenominator
  by_cases hx0 : 0 ≤ x
  · have hx6 : 6 ≤ x := by simpa [abs_of_nonneg hx0] using hx
    have hxt : 2 ≤ x - t := by linarith
    have hprod : (1 : ℝ) ≤ (Real.sqrt 2 / 2) * (x - t) := by
      nlinarith [mul_le_mul hq hxt (by norm_num : (0 : ℝ) ≤ 2) hq0]
    have hre : 1 ≤ (deBruijnNewmanTitchmarshPhiPullbackPoint
        (x + t * Complex.I)).re := by
      rw [deBruijnNewmanTitchmarshPhiPullbackPoint_re]
      simpa using hprod
    have hnormExp : 2 ≤ ‖Complex.exp
        (deBruijnNewmanTitchmarshPhiPullbackPoint (x + t * Complex.I))‖ := by
      rw [Complex.norm_exp]
      exact (by linarith : (2 : ℝ) ≤
        (deBruijnNewmanTitchmarshPhiPullbackPoint (x + t * Complex.I)).re + 1)
        |>.trans (Real.add_one_le_exp _)
    have hdiff := norm_sub_norm_le
      (Complex.exp (deBruijnNewmanTitchmarshPhiPullbackPoint
        (x + t * Complex.I))) (1 : ℂ)
    norm_num at hdiff
    linarith
  · have hxNonpos : x ≤ 0 := le_of_not_ge hx0
    have hx6 : x ≤ -6 := by
      rw [abs_of_nonpos hxNonpos] at hx
      linarith
    have htx : 2 ≤ t - x := by linarith
    have hprod : (1 : ℝ) ≤ (Real.sqrt 2 / 2) * (t - x) := by
      nlinarith [mul_le_mul hq htx (by norm_num : (0 : ℝ) ≤ 2) hq0]
    have hre : (deBruijnNewmanTitchmarshPhiPullbackPoint
        (x + t * Complex.I)).re ≤ -1 := by
      rw [deBruijnNewmanTitchmarshPhiPullbackPoint_re]
      simp
      nlinarith
    have hexpNegOne : Real.exp (-1) ≤ (1 / 2 : ℝ) := by
      rw [Real.exp_neg]
      have htwo : (2 : ℝ) ≤ Real.exp 1 := by
        simpa only [one_add_one_eq_two] using Real.add_one_le_exp (1 : ℝ)
      simpa only [one_div] using
        (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) htwo)
    have hnormExp : ‖Complex.exp
        (deBruijnNewmanTitchmarshPhiPullbackPoint (x + t * Complex.I))‖ ≤
        (1 / 2 : ℝ) := by
      rw [Complex.norm_exp]
      exact (Real.exp_le_exp.mpr hre).trans hexpNegOne
    have hdiff := norm_sub_norm_le (1 : ℂ)
      (Complex.exp (deBruijnNewmanTitchmarshPhiPullbackPoint
        (x + t * Complex.I)))
    rw [norm_one, norm_sub_rev] at hdiff
    linarith

def deBruijnNewmanTitchmarshPhiSideLinearRate (a : ℂ) : ℝ :=
  |(a * deBruijnNewmanTitchmarshPhiDirection).re|

def deBruijnNewmanTitchmarshPhiSideMajorantConstant (a : ℂ) : ℝ :=
  deBruijnNewmanTitchmarshPhiRotatedHalfWidth ^ 2 / (4 * Real.pi) +
    |(a * deBruijnNewmanTitchmarshPhiDirection).im| *
      deBruijnNewmanTitchmarshPhiRotatedHalfWidth +
    2 * Real.pi * deBruijnNewmanTitchmarshPhiSideLinearRate a ^ 2

def deBruijnNewmanTitchmarshPhiSideMajorant (a : ℂ) (x : ℝ) : ℝ :=
  2 * Real.exp (deBruijnNewmanTitchmarshPhiSideMajorantConstant a) *
    Real.exp (-(1 / (8 * Real.pi)) * x ^ 2)

theorem deBruijnNewmanTitchmarshPhiSideLinearRate_mul_abs_le
    (a : ℂ) (x : ℝ) :
    deBruijnNewmanTitchmarshPhiSideLinearRate a * |x| ≤
      x ^ 2 / (8 * Real.pi) +
        2 * Real.pi * deBruijnNewmanTitchmarshPhiSideLinearRate a ^ 2 := by
  let B := deBruijnNewmanTitchmarshPhiSideLinearRate a
  have hden : 0 < 8 * Real.pi := by positivity
  have hsq : 0 ≤ (|x| - 4 * Real.pi * B) ^ 2 := sq_nonneg _
  have hrewrite :
      x ^ 2 / (8 * Real.pi) + 2 * Real.pi * B ^ 2 =
        (x ^ 2 + 16 * Real.pi ^ 2 * B ^ 2) / (8 * Real.pi) := by
    field_simp
    ring
  change B * |x| ≤ _
  rw [hrewrite, le_div_iff₀ hden]
  nlinarith [sq_abs x]

theorem deBruijnNewmanTitchmarshPhiExponent_pullback_re_le_side
    (a : ℂ) (x t : ℝ)
    (ht : |t| ≤ deBruijnNewmanTitchmarshPhiRotatedHalfWidth) :
    (deBruijnNewmanTitchmarshPhiExponent a
        (deBruijnNewmanTitchmarshPhiPullbackPoint (x + t * Complex.I))).re ≤
      -(1 / (8 * Real.pi)) * x ^ 2 +
        deBruijnNewmanTitchmarshPhiSideMajorantConstant a := by
  let h := deBruijnNewmanTitchmarshPhiRotatedHalfWidth
  let c := a * deBruijnNewmanTitchmarshPhiDirection
  let B := deBruijnNewmanTitchmarshPhiSideLinearRate a
  have hh : 0 < h := deBruijnNewmanTitchmarshPhiRotatedHalfWidth_pos
  have htSq : t ^ 2 ≤ h ^ 2 :=
    sq_le_sq.mpr (by simpa [abs_of_pos hh] using ht)
  have htDiv : t ^ 2 / (4 * Real.pi) ≤ h ^ 2 / (4 * Real.pi) :=
    div_le_div_of_nonneg_right htSq (by positivity)
  have hxTerm : c.re * x ≤ B * |x| := by
    calc
      c.re * x ≤ |c.re * x| := le_abs_self _
      _ = |c.re| * |x| := abs_mul _ _
      _ = B * |x| := by rfl
  have htTerm : -c.im * t ≤ |c.im| * h := by
    calc
      -c.im * t ≤ |-c.im * t| := le_abs_self _
      _ = |c.im| * |t| := by rw [abs_mul, abs_neg]
      _ ≤ |c.im| * h := mul_le_mul_of_nonneg_left ht (abs_nonneg _)
  have hlinear := deBruijnNewmanTitchmarshPhiSideLinearRate_mul_abs_le a x
  rw [deBruijnNewmanTitchmarshPhiExponent_pullback_re]
  calc
    -(x ^ 2) / (4 * Real.pi) + t ^ 2 / (4 * Real.pi) + c.re * x - c.im * t ≤
        -(x ^ 2) / (4 * Real.pi) + h ^ 2 / (4 * Real.pi) +
          B * |x| + |c.im| * h := by linarith
    _ ≤ -(x ^ 2) / (4 * Real.pi) + h ^ 2 / (4 * Real.pi) +
          (x ^ 2 / (8 * Real.pi) + 2 * Real.pi * B ^ 2) + |c.im| * h := by
      linarith
    _ = -(1 / (8 * Real.pi)) * x ^ 2 +
        deBruijnNewmanTitchmarshPhiSideMajorantConstant a := by
      dsimp [h, c, B]
      rw [deBruijnNewmanTitchmarshPhiSideMajorantConstant,
        deBruijnNewmanTitchmarshPhiSideLinearRate]
      field_simp [Real.pi_ne_zero]
      ring

/-- Uniform pure Gaussian domination on either fixed-length short side. -/
theorem norm_deBruijnNewmanTitchmarshPhiPullbackKernel_le_sideMajorant
    (a : ℂ) (x t : ℝ) (hx : 6 ≤ |x|)
    (ht : |t| ≤ deBruijnNewmanTitchmarshPhiRotatedHalfWidth) :
    ‖deBruijnNewmanTitchmarshPhiPullbackKernel a (x + t * Complex.I)‖ ≤
      deBruijnNewmanTitchmarshPhiSideMajorant a x := by
  have hden := one_half_le_norm_deBruijnNewmanTitchmarshPhiPullbackDenominator_side
    x t hx ht
  have hexponent := deBruijnNewmanTitchmarshPhiExponent_pullback_re_le_side a x t ht
  rw [deBruijnNewmanTitchmarshPhiPullbackKernel,
    deBruijnNewmanTitchmarshPhiPullbackNumerator, norm_div, norm_mul,
    Complex.norm_exp, norm_deBruijnNewmanTitchmarshPhiDirection, mul_one]
  calc
    Real.exp
          (deBruijnNewmanTitchmarshPhiExponent a
            (deBruijnNewmanTitchmarshPhiPullbackPoint (x + t * Complex.I))).re /
        ‖deBruijnNewmanTitchmarshPhiPullbackDenominator (x + t * Complex.I)‖ ≤
      Real.exp
          (deBruijnNewmanTitchmarshPhiExponent a
            (deBruijnNewmanTitchmarshPhiPullbackPoint (x + t * Complex.I))).re /
        (1 / 2 : ℝ) := by
          exact div_le_div_of_nonneg_left (Real.exp_nonneg _) (by norm_num) hden
    _ = 2 * Real.exp
        (deBruijnNewmanTitchmarshPhiExponent a
          (deBruijnNewmanTitchmarshPhiPullbackPoint (x + t * Complex.I))).re := by ring
    _ ≤ 2 * Real.exp (-(1 / (8 * Real.pi)) * x ^ 2 +
        deBruijnNewmanTitchmarshPhiSideMajorantConstant a) := by
      gcongr
    _ = deBruijnNewmanTitchmarshPhiSideMajorant a x := by
      rw [deBruijnNewmanTitchmarshPhiSideMajorant, Real.exp_add]
      ring

theorem norm_deBruijnNewmanTitchmarshPhi_shortSideIntegral_le
    (a : ℂ) (x : ℝ) (hx : 6 ≤ |x|) :
    ‖Complex.I * (∫ t : ℝ in
        -deBruijnNewmanTitchmarshPhiRotatedHalfWidth..
          deBruijnNewmanTitchmarshPhiRotatedHalfWidth,
      deBruijnNewmanTitchmarshPhiPullbackKernel a (x + t * Complex.I))‖ ≤
      deBruijnNewmanTitchmarshPhiSideMajorant a x *
        (2 * deBruijnNewmanTitchmarshPhiRotatedHalfWidth) := by
  rw [norm_mul, norm_I, one_mul]
  calc
    ‖∫ t : ℝ in
        -deBruijnNewmanTitchmarshPhiRotatedHalfWidth..
          deBruijnNewmanTitchmarshPhiRotatedHalfWidth,
      deBruijnNewmanTitchmarshPhiPullbackKernel a (x + t * Complex.I)‖ ≤
        deBruijnNewmanTitchmarshPhiSideMajorant a x *
          |deBruijnNewmanTitchmarshPhiRotatedHalfWidth -
            (-deBruijnNewmanTitchmarshPhiRotatedHalfWidth)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      apply norm_deBruijnNewmanTitchmarshPhiPullbackKernel_le_sideMajorant a x t hx
      have htu := uIoc_subset_uIcc ht
      rw [uIcc_of_le
        (neg_le_self deBruijnNewmanTitchmarshPhiRotatedHalfWidth_pos.le)] at htu
      rw [abs_le]
      exact htu
    _ = deBruijnNewmanTitchmarshPhiSideMajorant a x *
        (2 * deBruijnNewmanTitchmarshPhiRotatedHalfWidth) := by
      have hh := deBruijnNewmanTitchmarshPhiRotatedHalfWidth_pos
      rw [abs_of_pos (by linarith :
        0 < deBruijnNewmanTitchmarshPhiRotatedHalfWidth -
          (-deBruijnNewmanTitchmarshPhiRotatedHalfWidth))]
      ring

theorem tendsto_deBruijnNewmanTitchmarshPhiSideMajorant_atTop (a : ℂ) :
    Tendsto (deBruijnNewmanTitchmarshPhiSideMajorant a) atTop (𝓝 0) := by
  have hsq : Tendsto (fun x : ℝ ↦ x ^ 2) atTop atTop := by
    simp only [pow_two]
    exact tendsto_id.atTop_mul_atTop₀ tendsto_id
  have hcoef : -(1 / (8 * Real.pi)) < 0 :=
    neg_lt_zero.mpr (by positivity)
  have hneg : Tendsto (fun x : ℝ ↦ -(1 / (8 * Real.pi)) * x ^ 2)
      atTop atBot := hsq.const_mul_atTop_of_neg hcoef
  change Tendsto (fun x : ℝ ↦
    (2 * Real.exp (deBruijnNewmanTitchmarshPhiSideMajorantConstant a)) *
      Real.exp (-(1 / (8 * Real.pi)) * x ^ 2)) atTop (𝓝 0)
  simpa only [Function.comp_apply, mul_zero] using
    (Real.tendsto_exp_atBot.comp hneg).const_mul
      (2 * Real.exp (deBruijnNewmanTitchmarshPhiSideMajorantConstant a))

theorem deBruijnNewmanTitchmarshPhiSideMajorant_neg (a : ℂ) (x : ℝ) :
    deBruijnNewmanTitchmarshPhiSideMajorant a (-x) =
      deBruijnNewmanTitchmarshPhiSideMajorant a x := by
  unfold deBruijnNewmanTitchmarshPhiSideMajorant
  rw [neg_sq]

theorem tendsto_deBruijnNewmanTitchmarshPhiRightEndIntegral (a : ℂ) :
    Tendsto (deBruijnNewmanTitchmarshPhiRightEndIntegral a) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero'
    (g := fun T : ℝ ↦ deBruijnNewmanTitchmarshPhiSideMajorant a T *
      (2 * deBruijnNewmanTitchmarshPhiRotatedHalfWidth)) ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun _ ↦ norm_nonneg _
  · filter_upwards [eventually_ge_atTop (6 : ℝ)] with T hT
    have hT0 : 0 ≤ T := by linarith
    unfold deBruijnNewmanTitchmarshPhiRightEndIntegral
    exact norm_deBruijnNewmanTitchmarshPhi_shortSideIntegral_le a T (by
      simpa [abs_of_nonneg hT0] using hT)
  · simpa only [zero_mul] using
      (tendsto_deBruijnNewmanTitchmarshPhiSideMajorant_atTop a).mul_const
        (2 * deBruijnNewmanTitchmarshPhiRotatedHalfWidth)

theorem tendsto_deBruijnNewmanTitchmarshPhiLeftEndIntegral (a : ℂ) :
    Tendsto (deBruijnNewmanTitchmarshPhiLeftEndIntegral a) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero'
    (g := fun T : ℝ ↦ deBruijnNewmanTitchmarshPhiSideMajorant a T *
      (2 * deBruijnNewmanTitchmarshPhiRotatedHalfWidth)) ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun _ ↦ norm_nonneg _
  · filter_upwards [eventually_ge_atTop (6 : ℝ)] with T hT
    have hT0 : 0 ≤ T := by linarith
    unfold deBruijnNewmanTitchmarshPhiLeftEndIntegral
    have hbound := norm_deBruijnNewmanTitchmarshPhi_shortSideIntegral_le a (-T) (by
      rw [abs_neg, abs_of_nonneg hT0]
      exact hT)
    rw [deBruijnNewmanTitchmarshPhiSideMajorant_neg] at hbound
    simpa only [Complex.ofReal_neg] using hbound
  · simpa only [zero_mul] using
      (tendsto_deBruijnNewmanTitchmarshPhiSideMajorant_atTop a).mul_const
        (2 * deBruijnNewmanTitchmarshPhiRotatedHalfWidth)

theorem tendsto_deBruijnNewmanTitchmarshPhi_staggeredIntervalIntegral
    (a : ℂ) (c : ℝ) :
    Tendsto
      (fun T : ℝ ↦ ∫ v : ℝ in c - T..c + T,
        deBruijnNewmanTitchmarshPhiLineIntegrand a v)
      atTop (𝓝 (deBruijnNewmanTitchmarshPhi a)) := by
  have hlower : Tendsto (fun T : ℝ ↦ c - T) atTop atBot := by
    refine tendsto_atBot.2 fun b ↦ ?_
    exact (eventually_ge_atTop (c - b)).mono fun T hT ↦ by linarith
  have hupper : Tendsto (fun T : ℝ ↦ c + T) atTop atTop := by
    refine tendsto_atTop.2 fun b ↦ ?_
    exact (eventually_ge_atTop (b - c)).mono fun T hT ↦ by linarith
  have hlim := intervalIntegral_tendsto_integral
    (integrable_deBruijnNewmanTitchmarshPhiLineIntegrand a) hlower hupper
  simpa only [deBruijnNewmanTitchmarshPhi] using hlim

/-- Titchmarsh's exact one-residue relation `(2.10.3)`. -/
theorem deBruijnNewmanTitchmarshPhi_one_residue (a : ℂ) :
    -Complex.exp (-2 * Real.pi * Complex.I * a) *
        deBruijnNewmanTitchmarshPhi (a + 1) -
      deBruijnNewmanTitchmarshPhi a =
        2 * (Real.pi : ℂ) * Complex.I := by
  let F : ℝ → ℂ := fun T ↦
    -Complex.exp (-2 * Real.pi * Complex.I * a) *
        (∫ v : ℝ in
          3 * deBruijnNewmanTitchmarshPhiRotatedHalfWidth - T..
            3 * deBruijnNewmanTitchmarshPhiRotatedHalfWidth + T,
          deBruijnNewmanTitchmarshPhiLineIntegrand (a + 1) v) -
      (∫ v : ℝ in
        deBruijnNewmanTitchmarshPhiRotatedHalfWidth - T..
          deBruijnNewmanTitchmarshPhiRotatedHalfWidth + T,
        deBruijnNewmanTitchmarshPhiLineIntegrand a v) +
      deBruijnNewmanTitchmarshPhiRightEndIntegral a T -
      deBruijnNewmanTitchmarshPhiLeftEndIntegral a T
  have hlimit : Tendsto F atTop
      (𝓝 (-Complex.exp (-2 * Real.pi * Complex.I * a) *
          deBruijnNewmanTitchmarshPhi (a + 1) -
        deBruijnNewmanTitchmarshPhi a)) := by
    simpa only [F, add_zero, sub_zero] using
      ((((tendsto_deBruijnNewmanTitchmarshPhi_staggeredIntervalIntegral
          (a + 1) (3 * deBruijnNewmanTitchmarshPhiRotatedHalfWidth)).const_mul
            (-Complex.exp (-2 * Real.pi * Complex.I * a))).sub
        (tendsto_deBruijnNewmanTitchmarshPhi_staggeredIntervalIntegral
          a deBruijnNewmanTitchmarshPhiRotatedHalfWidth)).add
            (tendsto_deBruijnNewmanTitchmarshPhiRightEndIntegral a)).sub
              (tendsto_deBruijnNewmanTitchmarshPhiLeftEndIntegral a)
  have hfinite : ∀ᶠ T : ℝ in atTop,
      F T = 2 * (Real.pi : ℂ) * Complex.I := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact deBruijnNewmanTitchmarshPhi_finite_parallel_shift a hT
  have hconstant : Tendsto F atTop
      (𝓝 (2 * (Real.pi : ℂ) * Complex.I)) := by
    apply tendsto_const_nhds.congr'
    exact hfinite.mono fun T hT ↦ hT.symm
  exact tendsto_nhds_unique hlimit hconstant

/-- Titchmarsh `(2.10.4)` after eliminating `Phi(a+1)`, without dividing by a possible zero. -/
theorem deBruijnNewmanTitchmarshPhi_eliminated (a : ℂ) :
    (1 + Complex.exp (-2 * Real.pi * Complex.I * a)) *
        deBruijnNewmanTitchmarshPhi a =
      -(2 * (Real.pi : ℂ) * Complex.I +
        Complex.exp (-2 * Real.pi * Complex.I * a) *
          (2 * Real.pi *
            Complex.exp (Complex.I * Real.pi * (a ^ 2 + 1 / 4)))) := by
  have hdiff := deBruijnNewmanTitchmarshPhi_add_one_sub a
  have hresidue := deBruijnNewmanTitchmarshPhi_one_residue a
  linear_combination
    -hresidue - Complex.exp (-2 * Real.pi * Complex.I * a) * hdiff

/-- Titchmarsh's specialization `a = 1/2 + i*z/(2*pi)`. -/
def deBruijnNewmanTitchmarshPhiMellinParameter (z : ℂ) : ℂ :=
  1 / 2 + Complex.I * z / (2 * Real.pi)

/-- The quadratic exponential remaining after the Mellin specialization. -/
def deBruijnNewmanTitchmarshPhiMellinQuadratic (z : ℂ) : ℂ :=
  z / 2 - Complex.I * z ^ 2 / (4 * Real.pi)

theorem deBruijnNewmanTitchmarshPhiMellinParameter_exp (z : ℂ) :
    Complex.exp (-2 * Real.pi * Complex.I *
        deBruijnNewmanTitchmarshPhiMellinParameter z) =
      -Complex.exp z := by
  have hexponent :
      -2 * Real.pi * Complex.I *
          deBruijnNewmanTitchmarshPhiMellinParameter z =
        z - Real.pi * Complex.I := by
    rw [deBruijnNewmanTitchmarshPhiMellinParameter]
    push_cast
    field_simp [Real.pi_ne_zero]
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hexponent]
  rw [show z - Real.pi * Complex.I = z + (-(Real.pi * Complex.I)) by ring,
    Complex.exp_add, Complex.exp_neg_pi_mul_I]
  ring

theorem deBruijnNewmanTitchmarshPhiMellinParameter_phase (z : ℂ) :
    Complex.I * Real.pi *
        (deBruijnNewmanTitchmarshPhiMellinParameter z ^ 2 + 1 / 4) =
      (deBruijnNewmanTitchmarshPhiMellinQuadratic z - z) +
        Real.pi * Complex.I / 2 := by
  rw [deBruijnNewmanTitchmarshPhiMellinParameter,
    deBruijnNewmanTitchmarshPhiMellinQuadratic]
  push_cast
  field_simp [Real.pi_ne_zero]
  ring_nf
  rw [Complex.I_sq]
  rw [show Complex.I ^ 3 = -Complex.I by
    rw [pow_succ, Complex.I_sq]
    ring]
  ring

/-- Specialized cross-multiplied form of Titchmarsh `(2.10.4)`. -/
theorem deBruijnNewmanTitchmarshPhi_mellin_specialization (z : ℂ) :
    deBruijnNewmanTitchmarshPhiDenominator z *
        deBruijnNewmanTitchmarshPhi
          (deBruijnNewmanTitchmarshPhiMellinParameter z) =
      2 * (Real.pi : ℂ) * Complex.I *
        (1 - Complex.exp (deBruijnNewmanTitchmarshPhiMellinQuadratic z)) := by
  have helim := deBruijnNewmanTitchmarshPhi_eliminated
    (deBruijnNewmanTitchmarshPhiMellinParameter z)
  rw [deBruijnNewmanTitchmarshPhiMellinParameter_exp] at helim
  rw [deBruijnNewmanTitchmarshPhiMellinParameter_phase,
    Complex.exp_add] at helim
  have hhalf : Complex.exp (Real.pi * Complex.I / 2) = Complex.I := by
    rw [show Real.pi * Complex.I / 2 =
      ((Real.pi / 2 : ℝ) : ℂ) * Complex.I by
        push_cast
        ring]
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp
  rw [hhalf] at helim
  have hcancel : Complex.exp z *
      Complex.exp (deBruijnNewmanTitchmarshPhiMellinQuadratic z - z) =
      Complex.exp (deBruijnNewmanTitchmarshPhiMellinQuadratic z) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hfactor :
      (-Complex.exp z) *
          (2 * Real.pi *
            (Complex.exp (deBruijnNewmanTitchmarshPhiMellinQuadratic z - z) *
              Complex.I)) =
        -2 * Real.pi * Complex.I *
          Complex.exp (deBruijnNewmanTitchmarshPhiMellinQuadratic z) := by
    calc
      (-Complex.exp z) *
          (2 * Real.pi *
            (Complex.exp (deBruijnNewmanTitchmarshPhiMellinQuadratic z - z) *
              Complex.I)) =
          -2 * Real.pi * Complex.I *
            (Complex.exp z *
              Complex.exp (deBruijnNewmanTitchmarshPhiMellinQuadratic z - z)) := by ring
      _ = -2 * Real.pi * Complex.I *
          Complex.exp (deBruijnNewmanTitchmarshPhiMellinQuadratic z) := by rw [hcancel]
  rw [hfactor] at helim
  unfold deBruijnNewmanTitchmarshPhiDenominator
  linear_combination -helim

/-- The source Mellin ray `arg z = -pi/4`. -/
def deBruijnNewmanTitchmarshMellinRayDirection : ℂ :=
  starRingEnd ℂ deBruijnNewmanTitchmarshPhiDirection

@[simp] theorem deBruijnNewmanTitchmarshMellinRayDirection_re :
    deBruijnNewmanTitchmarshMellinRayDirection.re = Real.sqrt 2 / 2 := by
  simp [deBruijnNewmanTitchmarshMellinRayDirection]

@[simp] theorem deBruijnNewmanTitchmarshMellinRayDirection_im :
    deBruijnNewmanTitchmarshMellinRayDirection.im = -(Real.sqrt 2 / 2) := by
  simp [deBruijnNewmanTitchmarshMellinRayDirection]

@[simp] theorem norm_deBruijnNewmanTitchmarshMellinRayDirection :
    ‖deBruijnNewmanTitchmarshMellinRayDirection‖ = 1 := by
  simp [deBruijnNewmanTitchmarshMellinRayDirection]

/-- The complex Laplace rate produced by a point of the Titchmarsh `w` contour. -/
def deBruijnNewmanTitchmarshMellinRate (v : ℝ) : ℂ :=
  -Complex.I * deBruijnNewmanTitchmarshMellinRayDirection *
      deBruijnNewmanTitchmarshPhiLine v / (2 * Real.pi)

/-- Every inner Mellin integral has the same strictly positive real decay rate. -/
@[simp] theorem deBruijnNewmanTitchmarshMellinRate_re (v : ℝ) :
    (deBruijnNewmanTitchmarshMellinRate v).re = Real.sqrt 2 / 4 := by
  rw [deBruijnNewmanTitchmarshMellinRate]
  have hden : (2 : ℂ) * Real.pi = (((2 * Real.pi : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [hden]
  rw [Complex.div_ofReal_re]
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.I_re, Complex.I_im, deBruijnNewmanTitchmarshMellinRayDirection_re,
    deBruijnNewmanTitchmarshMellinRayDirection_im,
    deBruijnNewmanTitchmarshPhiLine_re, deBruijnNewmanTitchmarshPhiLine_im,
    Complex.ofReal_re, Complex.ofReal_im]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

theorem deBruijnNewmanTitchmarshMellinRate_re_pos (v : ℝ) :
    0 < (deBruijnNewmanTitchmarshMellinRate v).re := by
  rw [deBruijnNewmanTitchmarshMellinRate_re]
  positivity

/-- Exact conversion of the specialized coupling exponential to a right-half-plane Laplace
kernel on the source Mellin ray. -/
theorem deBruijnNewmanTitchmarshMellin_coupling (v r : ℝ) :
    Complex.I *
          (deBruijnNewmanTitchmarshMellinRayDirection * r) *
          deBruijnNewmanTitchmarshPhiLine v / (2 * Real.pi) =
      -deBruijnNewmanTitchmarshMellinRate v * r := by
  rw [deBruijnNewmanTitchmarshMellinRate]
  ring

/-- The inner slanted-ray Mellin integral, evaluated by the complex-rate Laplace--Gamma bridge. -/
theorem deBruijnNewmanTitchmarshMellin_inner_integral
    {s : ℂ} (hs : 0 < s.re) (v : ℝ) :
    (∫ r : ℝ in Ioi 0,
        (r : ℂ) ^ (s - 1) *
          Complex.exp
            (Complex.I *
                (deBruijnNewmanTitchmarshMellinRayDirection * r) *
                deBruijnNewmanTitchmarshPhiLine v / (2 * Real.pi))) =
      deBruijnNewmanTitchmarshMellinRate v ^ (-s) * Complex.Gamma s := by
  have hlaplace := deBruijnNewmanComplexLaplace_eq hs
    (deBruijnNewmanTitchmarshMellinRate_re_pos v)
  calc
    (∫ r : ℝ in Ioi 0,
        (r : ℂ) ^ (s - 1) *
          Complex.exp
            (Complex.I *
                (deBruijnNewmanTitchmarshMellinRayDirection * r) *
                deBruijnNewmanTitchmarshPhiLine v / (2 * Real.pi))) =
        ∫ r : ℝ in Ioi 0,
          deBruijnNewmanComplexLaplaceIntegrand s
            (deBruijnNewmanTitchmarshMellinRate v) r := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro r _
      rw [deBruijnNewmanComplexLaplaceIntegrand]
      change (r : ℂ) ^ (s - 1) *
          Complex.exp
            (Complex.I *
                (deBruijnNewmanTitchmarshMellinRayDirection * r) *
                deBruijnNewmanTitchmarshPhiLine v / (2 * Real.pi)) =
        (r : ℂ) ^ (s - 1) *
          Complex.exp (-deBruijnNewmanTitchmarshMellinRate v * r)
      rw [deBruijnNewmanTitchmarshMellin_coupling]
    _ = deBruijnNewmanTitchmarshMellinRate v ^ (-s) * Complex.Gamma s := hlaplace

/-- The normalized two-variable integrand used for the Mellin/Fubini step.  The omitted constant
ray-power factor is restored separately when this is identified with the actual slanted contour. -/
def deBruijnNewmanTitchmarshMellinFubiniIntegrand (s : ℂ) (p : ℝ × ℝ) : ℂ :=
  deBruijnNewmanComplexLaplaceIntegrand s
      (deBruijnNewmanTitchmarshMellinRate p.2) p.1 *
    deBruijnNewmanTitchmarshPhiLineIntegrand (1 / 2) p.2

/-- Pointwise identification of the normalized Fubini integrand with the specialized `Phi`
integrand before exchanging the two integrations. -/
theorem deBruijnNewmanTitchmarshMellinFubiniIntegrand_eq
    (s : ℂ) (r v : ℝ) :
    deBruijnNewmanTitchmarshMellinFubiniIntegrand s (r, v) =
      (r : ℂ) ^ (s - 1) *
        deBruijnNewmanTitchmarshPhiLineIntegrand
          (deBruijnNewmanTitchmarshPhiMellinParameter
            (deBruijnNewmanTitchmarshMellinRayDirection * r)) v := by
  unfold deBruijnNewmanTitchmarshMellinFubiniIntegrand
  simp only [Prod.fst, Prod.snd]
  unfold deBruijnNewmanComplexLaplaceIntegrand
  rw [← deBruijnNewmanTitchmarshMellin_coupling]
  unfold deBruijnNewmanTitchmarshPhiLineIntegrand
  have hexponent :
      Complex.I *
            (deBruijnNewmanTitchmarshMellinRayDirection * r) *
            deBruijnNewmanTitchmarshPhiLine v / (2 * Real.pi) +
          deBruijnNewmanTitchmarshPhiExponent (1 / 2)
            (deBruijnNewmanTitchmarshPhiLine v) =
        deBruijnNewmanTitchmarshPhiExponent
          (deBruijnNewmanTitchmarshPhiMellinParameter
            (deBruijnNewmanTitchmarshMellinRayDirection * r))
          (deBruijnNewmanTitchmarshPhiLine v) := by
    unfold deBruijnNewmanTitchmarshPhiExponent
    rw [deBruijnNewmanTitchmarshPhiMellinParameter]
    field_simp [Real.pi_ne_zero]
    ring
  have hexp :
      Complex.exp
            (Complex.I *
              (deBruijnNewmanTitchmarshMellinRayDirection * r) *
              deBruijnNewmanTitchmarshPhiLine v / (2 * Real.pi)) *
          Complex.exp
            (deBruijnNewmanTitchmarshPhiExponent (1 / 2)
              (deBruijnNewmanTitchmarshPhiLine v)) =
        Complex.exp
          (deBruijnNewmanTitchmarshPhiExponent
            (deBruijnNewmanTitchmarshPhiMellinParameter
              (deBruijnNewmanTitchmarshMellinRayDirection * r))
            (deBruijnNewmanTitchmarshPhiLine v)) := by
    rw [← Complex.exp_add, hexponent]
  calc
    (r : ℂ) ^ (s - 1) *
          Complex.exp
            (Complex.I *
              (deBruijnNewmanTitchmarshMellinRayDirection * r) *
              deBruijnNewmanTitchmarshPhiLine v / (2 * Real.pi)) *
        (Complex.exp
              (deBruijnNewmanTitchmarshPhiExponent (1 / 2)
                (deBruijnNewmanTitchmarshPhiLine v)) /
            deBruijnNewmanTitchmarshPhiDenominator
              (deBruijnNewmanTitchmarshPhiLine v) *
          deBruijnNewmanTitchmarshPhiDirection) =
        (r : ℂ) ^ (s - 1) *
          (Complex.exp
              (Complex.I *
                (deBruijnNewmanTitchmarshMellinRayDirection * r) *
                deBruijnNewmanTitchmarshPhiLine v / (2 * Real.pi)) *
            Complex.exp
              (deBruijnNewmanTitchmarshPhiExponent (1 / 2)
                (deBruijnNewmanTitchmarshPhiLine v))) /
          deBruijnNewmanTitchmarshPhiDenominator
            (deBruijnNewmanTitchmarshPhiLine v) *
          deBruijnNewmanTitchmarshPhiDirection := by ring
    _ = (r : ℂ) ^ (s - 1) *
          Complex.exp
            (deBruijnNewmanTitchmarshPhiExponent
              (deBruijnNewmanTitchmarshPhiMellinParameter
                (deBruijnNewmanTitchmarshMellinRayDirection * r))
              (deBruijnNewmanTitchmarshPhiLine v)) /
          deBruijnNewmanTitchmarshPhiDenominator
            (deBruijnNewmanTitchmarshPhiLine v) *
          deBruijnNewmanTitchmarshPhiDirection := by rw [hexp]
    _ = (r : ℂ) ^ (s - 1) *
        (Complex.exp
              (deBruijnNewmanTitchmarshPhiExponent
                (deBruijnNewmanTitchmarshPhiMellinParameter
                  (deBruijnNewmanTitchmarshMellinRayDirection * r))
                (deBruijnNewmanTitchmarshPhiLine v)) /
            deBruijnNewmanTitchmarshPhiDenominator
              (deBruijnNewmanTitchmarshPhiLine v) *
          deBruijnNewmanTitchmarshPhiDirection) := by ring

theorem deBruijnNewmanTitchmarshMellinFubini_outer (s : ℂ) (r : ℝ) :
    (∫ v : ℝ,
        deBruijnNewmanTitchmarshMellinFubiniIntegrand s (r, v)) =
      (r : ℂ) ^ (s - 1) *
        deBruijnNewmanTitchmarshPhi
          (deBruijnNewmanTitchmarshPhiMellinParameter
            (deBruijnNewmanTitchmarshMellinRayDirection * r)) := by
  rw [deBruijnNewmanTitchmarshPhi, ← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun v =>
    deBruijnNewmanTitchmarshMellinFubiniIntegrand_eq s r v

theorem deBruijnNewmanTitchmarshMellinRay_denominator_ne_zero
    {r : ℝ} (hr : 0 < r) :
    deBruijnNewmanTitchmarshPhiDenominator
      (deBruijnNewmanTitchmarshMellinRayDirection * r) ≠ 0 := by
  intro hzero
  have hexp :
      Complex.exp (deBruijnNewmanTitchmarshMellinRayDirection * r) = 1 :=
    sub_eq_zero.mp hzero
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp
  have hre := congrArg Complex.re hn
  have hrhs : ((n : ℂ) * (2 * Real.pi * Complex.I)).re = 0 := by simp
  rw [hrhs] at hre
  simp only [Complex.mul_re, deBruijnNewmanTitchmarshMellinRayDirection_re,
    deBruijnNewmanTitchmarshMellinRayDirection_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero] at hre
  have hsqrt : Real.sqrt 2 / 2 ≠ 0 := by positivity
  exact hr.ne' ((mul_eq_zero.mp hre).resolve_left hsqrt)

theorem deBruijnNewmanTitchmarshPhi_mellin_specialization_div
    {r : ℝ} (hr : 0 < r) :
    deBruijnNewmanTitchmarshPhi
        (deBruijnNewmanTitchmarshPhiMellinParameter
          (deBruijnNewmanTitchmarshMellinRayDirection * r)) =
      (2 * (Real.pi : ℂ) * Complex.I *
        (1 - Complex.exp
          (deBruijnNewmanTitchmarshPhiMellinQuadratic
            (deBruijnNewmanTitchmarshMellinRayDirection * r)))) /
        deBruijnNewmanTitchmarshPhiDenominator
          (deBruijnNewmanTitchmarshMellinRayDirection * r) := by
  apply (eq_div_iff (deBruijnNewmanTitchmarshMellinRay_denominator_ne_zero hr)).2
  rw [mul_comm]
  exact deBruijnNewmanTitchmarshPhi_mellin_specialization
    (deBruijnNewmanTitchmarshMellinRayDirection * r)

/-- The combined zeta-minus-remainder integrand on the normalized Mellin ray. -/
def deBruijnNewmanTitchmarshMellinDifferenceIntegrand (s : ℂ) (r : ℝ) : ℂ :=
  (r : ℂ) ^ (s - 1) *
    (1 - Complex.exp
      (deBruijnNewmanTitchmarshPhiMellinQuadratic
        (deBruijnNewmanTitchmarshMellinRayDirection * r))) /
    deBruijnNewmanTitchmarshPhiDenominator
      (deBruijnNewmanTitchmarshMellinRayDirection * r)

theorem deBruijnNewmanTitchmarshMellin_specialization_integral (s : ℂ) :
    (∫ r : ℝ in Ioi 0,
        (r : ℂ) ^ (s - 1) *
          deBruijnNewmanTitchmarshPhi
            (deBruijnNewmanTitchmarshPhiMellinParameter
              (deBruijnNewmanTitchmarshMellinRayDirection * r))) =
      2 * (Real.pi : ℂ) * Complex.I *
        ∫ r : ℝ in Ioi 0,
          deBruijnNewmanTitchmarshMellinDifferenceIntegrand s r := by
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  apply (ae_restrict_iff' measurableSet_Ioi).mpr
  filter_upwards with r hr
  rw [deBruijnNewmanTitchmarshPhi_mellin_specialization_div hr]
  unfold deBruijnNewmanTitchmarshMellinDifferenceIntegrand
  ring

theorem aestronglyMeasurable_deBruijnNewmanTitchmarshMellinFubiniIntegrand
    (s : ℂ) :
    AEStronglyMeasurable
      (deBruijnNewmanTitchmarshMellinFubiniIntegrand s)
      ((volume.restrict (Ioi 0)).prod volume) := by
  rw [Measure.restrict_prod_eq_prod_univ]
  apply ContinuousOn.aestronglyMeasurable _ (measurableSet_Ioi.prod MeasurableSet.univ)
  apply continuousOn_of_forall_continuousAt
  intro p hp
  have hp0 : 0 < p.1 := hp.1
  unfold deBruijnNewmanTitchmarshMellinFubiniIntegrand
  apply ContinuousAt.mul
  · unfold deBruijnNewmanComplexLaplaceIntegrand
    apply ContinuousAt.mul
    · exact (continuousAt_ofReal_cpow_const p.1 (s - 1) (Or.inr hp0.ne')).comp
        continuousAt_fst
    · apply ContinuousAt.cexp
      have hline : Continuous deBruijnNewmanTitchmarshPhiLine := by
        unfold deBruijnNewmanTitchmarshPhiLine
        fun_prop
      have hrate : ContinuousAt
          (fun q : ℝ × ℝ => deBruijnNewmanTitchmarshMellinRate q.2) p := by
        unfold deBruijnNewmanTitchmarshMellinRate
        exact (((continuousAt_const.mul continuousAt_const).mul
          (hline.continuousAt.comp continuousAt_snd)).div_const _)
      exact hrate.neg.mul (continuous_ofReal.continuousAt.comp continuousAt_fst)
  · exact (continuous_deBruijnNewmanTitchmarshPhiLineIntegrand (1 / 2)).continuousAt.comp
      continuousAt_snd

/-- Absolute convergence on the Mellin ray times the Titchmarsh line. -/
theorem integrable_deBruijnNewmanTitchmarshMellinFubiniIntegrand
    {s : ℂ} (hs : 0 < s.re) :
    Integrable
      (deBruijnNewmanTitchmarshMellinFubiniIntegrand s)
      ((volume.restrict (Ioi 0)).prod volume) := by
  let k₀ : ℂ := (Real.sqrt 2 / 4 : ℝ)
  have hk₀ : 0 < k₀.re := by
    simp only [k₀, Complex.ofReal_re]
    positivity
  have hr := integrableOn_deBruijnNewmanComplexLaplaceIntegrand hs hk₀
  have hv := integrable_deBruijnNewmanTitchmarshPhiLineIntegrand (1 / 2)
  have hsep : Integrable
      (fun p : ℝ × ℝ =>
        deBruijnNewmanComplexLaplaceIntegrand s k₀ p.1 *
          deBruijnNewmanTitchmarshPhiLineIntegrand (1 / 2) p.2)
      ((volume.restrict (Ioi 0)).prod volume) := hr.mul_prod hv
  apply hsep.congr'
    (aestronglyMeasurable_deBruijnNewmanTitchmarshMellinFubiniIntegrand s)
  have hmem : ∀ᵐ p : ℝ × ℝ ∂(volume.restrict (Ioi 0)).prod volume,
      p.1 ∈ Ioi 0 := by
    rw [Measure.ae_prod_iff_ae_ae (measurableSet_Ioi.preimage measurable_fst)]
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr0
    exact Filter.Eventually.of_forall fun _ => hr0
  apply hmem.mono
  intro p hp0
  unfold deBruijnNewmanTitchmarshMellinFubiniIntegrand
  simp only [norm_mul]
  congr 1
  unfold deBruijnNewmanComplexLaplaceIntegrand k₀
  simp only [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hp0,
    Complex.norm_exp, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero,
    deBruijnNewmanTitchmarshMellinRate_re]

/-- The normalized double integral can be exchanged without any conditional-convergence step. -/
theorem deBruijnNewmanTitchmarshMellin_integral_swap
    {s : ℂ} (hs : 0 < s.re) :
    (∫ r : ℝ in Ioi 0, ∫ v : ℝ,
        deBruijnNewmanTitchmarshMellinFubiniIntegrand s (r, v)) =
      ∫ v : ℝ, ∫ r : ℝ in Ioi 0,
        deBruijnNewmanTitchmarshMellinFubiniIntegrand s (r, v) := by
  exact MeasureTheory.integral_integral_swap
    (integrable_deBruijnNewmanTitchmarshMellinFubiniIntegrand hs)

theorem deBruijnNewmanTitchmarshMellinFubini_inner
    {s : ℂ} (hs : 0 < s.re) (v : ℝ) :
    (∫ r : ℝ in Ioi 0,
        deBruijnNewmanTitchmarshMellinFubiniIntegrand s (r, v)) =
      (deBruijnNewmanTitchmarshMellinRate v ^ (-s) * Complex.Gamma s) *
        deBruijnNewmanTitchmarshPhiLineIntegrand (1 / 2) v := by
  unfold deBruijnNewmanTitchmarshMellinFubiniIntegrand
  simp only [Prod.fst, Prod.snd]
  rw [MeasureTheory.integral_mul_const]
  rw [deBruijnNewmanComplexLaplace_eq hs
    (deBruijnNewmanTitchmarshMellinRate_re_pos v)]

/-- Fubini followed by the exact complex Laplace--Gamma evaluation. -/
theorem deBruijnNewmanTitchmarshMellin_fubini_gamma
    {s : ℂ} (hs : 0 < s.re) :
    (∫ r : ℝ in Ioi 0, ∫ v : ℝ,
        deBruijnNewmanTitchmarshMellinFubiniIntegrand s (r, v)) =
      ∫ v : ℝ,
        (deBruijnNewmanTitchmarshMellinRate v ^ (-s) * Complex.Gamma s) *
          deBruijnNewmanTitchmarshPhiLineIntegrand (1 / 2) v := by
  rw [deBruijnNewmanTitchmarshMellin_integral_swap hs]
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun v =>
    deBruijnNewmanTitchmarshMellinFubini_inner hs v

/-- Titchmarsh's Mellin/Fubini bridge before separating the zeta and quadratic-remainder terms. -/
theorem deBruijnNewmanTitchmarshMellin_master
    {s : ℂ} (hs : 0 < s.re) :
    (∫ v : ℝ,
        (deBruijnNewmanTitchmarshMellinRate v ^ (-s) * Complex.Gamma s) *
          deBruijnNewmanTitchmarshPhiLineIntegrand (1 / 2) v) =
      2 * (Real.pi : ℂ) * Complex.I *
        ∫ r : ℝ in Ioi 0,
          deBruijnNewmanTitchmarshMellinDifferenceIntegrand s r := by
  calc
    (∫ v : ℝ,
        (deBruijnNewmanTitchmarshMellinRate v ^ (-s) * Complex.Gamma s) *
          deBruijnNewmanTitchmarshPhiLineIntegrand (1 / 2) v) =
        ∫ r : ℝ in Ioi 0, ∫ v : ℝ,
          deBruijnNewmanTitchmarshMellinFubiniIntegrand s (r, v) :=
      (deBruijnNewmanTitchmarshMellin_fubini_gamma hs).symm
    _ = ∫ r : ℝ in Ioi 0,
          (r : ℂ) ^ (s - 1) *
            deBruijnNewmanTitchmarshPhi
              (deBruijnNewmanTitchmarshPhiMellinParameter
                (deBruijnNewmanTitchmarshMellinRayDirection * r)) := by
      apply MeasureTheory.integral_congr_ae
      apply (ae_restrict_iff' measurableSet_Ioi).mpr
      exact Filter.Eventually.of_forall fun r _ =>
        deBruijnNewmanTitchmarshMellinFubini_outer s r
    _ = 2 * (Real.pi : ℂ) * Complex.I *
          ∫ r : ℝ in Ioi 0,
            deBruijnNewmanTitchmarshMellinDifferenceIntegrand s r :=
      deBruijnNewmanTitchmarshMellin_specialization_integral s

/-- The `n + 1` complex Laplace rate in the geometric expansion on the Mellin ray. -/
def deBruijnNewmanTitchmarshMellinZetaRate (n : ℕ) : ℂ :=
  (n + 1 : ℂ) * deBruijnNewmanTitchmarshMellinRayDirection

@[simp] theorem deBruijnNewmanTitchmarshMellinZetaRate_re (n : ℕ) :
    (deBruijnNewmanTitchmarshMellinZetaRate n).re =
      (n + 1 : ℝ) * (Real.sqrt 2 / 2) := by
  simp [deBruijnNewmanTitchmarshMellinZetaRate, Complex.mul_re]

theorem deBruijnNewmanTitchmarshMellinZetaRate_re_pos (n : ℕ) :
    0 < (deBruijnNewmanTitchmarshMellinZetaRate n).re := by
  rw [deBruijnNewmanTitchmarshMellinZetaRate_re]
  positivity

/-- One summand in the geometric-series expansion of the zeta branch. -/
def deBruijnNewmanTitchmarshMellinZetaSeriesTerm
    (s : ℂ) (n : ℕ) (r : ℝ) : ℂ :=
  deBruijnNewmanComplexLaplaceIntegrand s
    (deBruijnNewmanTitchmarshMellinZetaRate n) r

/-- The normalized zeta kernel on the source Mellin ray. -/
def deBruijnNewmanTitchmarshMellinZetaIntegrand (s : ℂ) (r : ℝ) : ℂ :=
  (r : ℂ) ^ (s - 1) /
    deBruijnNewmanTitchmarshPhiDenominator
      (deBruijnNewmanTitchmarshMellinRayDirection * r)

/-- Pointwise geometric expansion of the normalized zeta kernel. -/
theorem hasSum_deBruijnNewmanTitchmarshMellinZetaSeriesTerm
    (s : ℂ) {r : ℝ} (hr : 0 < r) :
    HasSum (fun n : ℕ =>
      deBruijnNewmanTitchmarshMellinZetaSeriesTerm s n r)
      (deBruijnNewmanTitchmarshMellinZetaIntegrand s r) := by
  let q := Complex.exp
    (-deBruijnNewmanTitchmarshMellinRayDirection * (r : ℂ))
  have hq : ‖q‖ < 1 := by
    rw [Complex.norm_exp]
    apply Real.exp_lt_one_iff.mpr
    simp only [q, Complex.mul_re, Complex.neg_re,
      deBruijnNewmanTitchmarshMellinRayDirection_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    have hsqrt : 0 < Real.sqrt 2 / 2 := by positivity
    nlinarith
  convert! (hasSum_geometric_of_norm_lt_one hq).mul_left
      ((r : ℂ) ^ (s - 1) * q) using 1 with n
  · funext n
    unfold deBruijnNewmanTitchmarshMellinZetaSeriesTerm
    unfold deBruijnNewmanComplexLaplaceIntegrand
    change (r : ℂ) ^ (s - 1) *
        Complex.exp
          (-deBruijnNewmanTitchmarshMellinZetaRate n * (r : ℂ)) =
      ((r : ℂ) ^ (s - 1) * q) * q ^ n
    rw [← Complex.exp_nat_mul]
    simp only [q]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    simp only [deBruijnNewmanTitchmarshMellinZetaRate]
    push_cast
    ring
  · unfold deBruijnNewmanTitchmarshMellinZetaIntegrand
    unfold deBruijnNewmanTitchmarshPhiDenominator
    simp only [q]
    rw [neg_mul, Complex.exp_neg]
    field_simp [Complex.exp_ne_zero]

theorem integrableOn_deBruijnNewmanTitchmarshMellinZetaSeriesTerm
    {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    IntegrableOn
      (deBruijnNewmanTitchmarshMellinZetaSeriesTerm s n) (Ioi 0) := by
  unfold deBruijnNewmanTitchmarshMellinZetaSeriesTerm
  exact integrableOn_deBruijnNewmanComplexLaplaceIntegrand hs
    (deBruijnNewmanTitchmarshMellinZetaRate_re_pos n)

theorem integral_deBruijnNewmanTitchmarshMellinZetaSeriesTerm
    {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    (∫ r : ℝ in Ioi 0,
        deBruijnNewmanTitchmarshMellinZetaSeriesTerm s n r) =
      deBruijnNewmanTitchmarshMellinZetaRate n ^ (-s) *
        Complex.Gamma s := by
  unfold deBruijnNewmanTitchmarshMellinZetaSeriesTerm
  exact deBruijnNewmanComplexLaplace_eq hs
    (deBruijnNewmanTitchmarshMellinZetaRate_re_pos n)

theorem integral_norm_deBruijnNewmanTitchmarshMellinZetaSeriesTerm
    {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    (∫ r : ℝ in Ioi 0,
        ‖deBruijnNewmanTitchmarshMellinZetaSeriesTerm s n r‖) =
      (1 / (deBruijnNewmanTitchmarshMellinZetaRate n).re) ^ s.re *
        Real.Gamma s.re := by
  calc
    (∫ r : ℝ in Ioi 0,
        ‖deBruijnNewmanTitchmarshMellinZetaSeriesTerm s n r‖) =
        ∫ r : ℝ in Ioi 0,
          r ^ (s.re - 1) *
            Real.exp
              (-((deBruijnNewmanTitchmarshMellinZetaRate n).re * r)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      unfold deBruijnNewmanTitchmarshMellinZetaSeriesTerm
      unfold deBruijnNewmanComplexLaplaceIntegrand
      change ‖(r : ℂ) ^ (s - 1) *
          Complex.exp
            (-deBruijnNewmanTitchmarshMellinZetaRate n * (r : ℂ))‖ =
        r ^ (s.re - 1) *
          Real.exp
            (-((deBruijnNewmanTitchmarshMellinZetaRate n).re * r))
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hr,
        Complex.norm_exp]
      simp only [Complex.sub_re, Complex.one_re, Complex.mul_re,
        Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero]
      ring
    _ = (1 / (deBruijnNewmanTitchmarshMellinZetaRate n).re) ^ s.re *
          Real.Gamma s.re :=
      Real.integral_rpow_mul_exp_neg_mul_Ioi hs
        (deBruijnNewmanTitchmarshMellinZetaRate_re_pos n)

/-- The series of termwise `L¹` norms converges in the Dirichlet half-plane. -/
theorem summable_integral_norm_deBruijnNewmanTitchmarshMellinZetaSeriesTerm
    {s : ℂ} (hs : 1 < s.re) :
    Summable fun n : ℕ =>
      ∫ r : ℝ in Ioi 0,
        ‖deBruijnNewmanTitchmarshMellinZetaSeriesTerm s n r‖ := by
  have hbase0 : Summable fun n : ℕ => (((n : ℝ) ^ s.re)⁻¹) :=
    Real.summable_nat_rpow_inv.mpr hs
  have hbase : Summable fun n : ℕ => ((((n + 1 : ℕ) : ℝ) ^ s.re)⁻¹) :=
    (summable_nat_add_iff 1).mpr hbase0
  have hscaled := hbase.mul_left
    (((Real.sqrt 2 / 2) ^ s.re)⁻¹ * Real.Gamma s.re)
  refine hscaled.congr (fun n => ?_)
  rw [integral_norm_deBruijnNewmanTitchmarshMellinZetaSeriesTerm
    (zero_lt_one.trans hs), deBruijnNewmanTitchmarshMellinZetaRate_re]
  have hn : 0 ≤ (n + 1 : ℝ) := by positivity
  have hc : 0 ≤ Real.sqrt 2 / 2 := by positivity
  rw [one_div, Real.inv_rpow (mul_nonneg hn hc), Real.mul_rpow hn hc,
    mul_inv_rev]
  ring
  norm_num [Nat.cast_add, Nat.cast_one, add_comm]

/-- Termwise integration of the geometric expansion is justified by absolute convergence. -/
theorem hasSum_integral_deBruijnNewmanTitchmarshMellinZetaSeriesTerm
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ =>
      ∫ r : ℝ in Ioi 0,
        deBruijnNewmanTitchmarshMellinZetaSeriesTerm s n r)
      (∫ r : ℝ in Ioi 0,
        deBruijnNewmanTitchmarshMellinZetaIntegrand s r) := by
  have hsum := MeasureTheory.hasSum_integral_of_summable_integral_norm
    (μ := volume.restrict (Ioi 0))
    (F := fun n : ℕ =>
      deBruijnNewmanTitchmarshMellinZetaSeriesTerm s n)
    (fun n =>
      integrableOn_deBruijnNewmanTitchmarshMellinZetaSeriesTerm
        (zero_lt_one.trans hs) n)
    (summable_integral_norm_deBruijnNewmanTitchmarshMellinZetaSeriesTerm hs)
  have hpoint : ∀ᵐ r : ℝ ∂volume.restrict (Ioi 0),
      (∑' n : ℕ,
        deBruijnNewmanTitchmarshMellinZetaSeriesTerm s n r) =
          deBruijnNewmanTitchmarshMellinZetaIntegrand s r := by
    apply (ae_restrict_iff' measurableSet_Ioi).mpr
    filter_upwards with r hr
    exact
      (hasSum_deBruijnNewmanTitchmarshMellinZetaSeriesTerm s hr).tsum_eq
  rw [MeasureTheory.integral_congr_ae hpoint] at hsum
  exact hsum

/-- The zeta branch of Titchmarsh's slanted Mellin integral in its Dirichlet half-plane. -/
theorem deBruijnNewmanTitchmarshMellinZetaIntegral_eq
    {s : ℂ} (hs : 1 < s.re) :
    (∫ r : ℝ in Ioi 0,
        deBruijnNewmanTitchmarshMellinZetaIntegrand s r) =
      deBruijnNewmanTitchmarshMellinRayDirection ^ (-s) *
        Complex.Gamma s * riemannZeta s := by
  have he : deBruijnNewmanTitchmarshMellinRayDirection ≠ 0 := by
    intro he0
    have hnorm := norm_deBruijnNewmanTitchmarshMellinRayDirection
    rw [he0, norm_zero] at hnorm
    norm_num at hnorm
  have hterm (n : ℕ) :
      deBruijnNewmanTitchmarshMellinZetaRate n ^ (-s) *
          Complex.Gamma s =
        (deBruijnNewmanTitchmarshMellinRayDirection ^ (-s) *
            Complex.Gamma s) *
          (1 / ((n : ℂ) + 1) ^ s) := by
    unfold deBruijnNewmanTitchmarshMellinZetaRate
    have hncast : (n + 1 : ℂ) = (((n + 1 : ℝ) : ℂ)) := by
      norm_num
    rw [hncast,
      deBruijnNewman_cpow_ofReal_mul (by positivity) he,
      Complex.cpow_neg]
    norm_num [Nat.cast_add, Nat.cast_one, one_div]
    ring
  calc
    (∫ r : ℝ in Ioi 0,
        deBruijnNewmanTitchmarshMellinZetaIntegrand s r) =
        ∑' n : ℕ,
          ∫ r : ℝ in Ioi 0,
            deBruijnNewmanTitchmarshMellinZetaSeriesTerm s n r :=
      (hasSum_integral_deBruijnNewmanTitchmarshMellinZetaSeriesTerm hs).tsum_eq.symm
    _ = ∑' n : ℕ,
          deBruijnNewmanTitchmarshMellinZetaRate n ^ (-s) *
            Complex.Gamma s := by
      apply tsum_congr
      exact integral_deBruijnNewmanTitchmarshMellinZetaSeriesTerm
        (zero_lt_one.trans hs)
    _ = ∑' n : ℕ,
          (deBruijnNewmanTitchmarshMellinRayDirection ^ (-s) *
              Complex.Gamma s) *
            (1 / ((n : ℂ) + 1) ^ s) := tsum_congr hterm
    _ = (deBruijnNewmanTitchmarshMellinRayDirection ^ (-s) *
            Complex.Gamma s) *
          ∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ s := tsum_mul_left
    _ = deBruijnNewmanTitchmarshMellinRayDirection ^ (-s) *
          Complex.Gamma s * riemannZeta s := by
      rw [← zeta_eq_tsum_one_div_nat_add_one_cpow hs]

/-- Squaring the Mellin-ray direction rotates by `-pi/2`. -/
@[simp] theorem deBruijnNewmanTitchmarshMellinRayDirection_sq :
    deBruijnNewmanTitchmarshMellinRayDirection ^ 2 = -Complex.I := by
  change (starRingEnd ℂ deBruijnNewmanTitchmarshPhiDirection) ^ 2 = -Complex.I
  rw [← map_pow, deBruijnNewmanTitchmarshPhiDirection_sq]
  simp

/-- The quadratic exponent becomes a real Gaussian correction plus the ray-linear term. -/
theorem deBruijnNewmanTitchmarshPhiMellinQuadratic_ray (r : ℝ) :
    deBruijnNewmanTitchmarshPhiMellinQuadratic
        (deBruijnNewmanTitchmarshMellinRayDirection * r) =
      deBruijnNewmanTitchmarshMellinRayDirection * r / 2 -
        ((r ^ 2 / (4 * Real.pi) : ℝ) : ℂ) := by
  rw [deBruijnNewmanTitchmarshPhiMellinQuadratic, mul_pow,
    deBruijnNewmanTitchmarshMellinRayDirection_sq]
  push_cast
  field_simp [Real.pi_ne_zero]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Exact real part of the quadratic exponent on Titchmarsh's Mellin ray. -/
@[simp] theorem deBruijnNewmanTitchmarshPhiMellinQuadratic_ray_re (r : ℝ) :
    (deBruijnNewmanTitchmarshPhiMellinQuadratic
      (deBruijnNewmanTitchmarshMellinRayDirection * r)).re =
      Real.sqrt 2 / 4 * r - r ^ 2 / (4 * Real.pi) := by
  rw [deBruijnNewmanTitchmarshPhiMellinQuadratic_ray]
  simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.mul_re,
    deBruijnNewmanTitchmarshMellinRayDirection_re,
    deBruijnNewmanTitchmarshMellinRayDirection_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  ring

/-- The exponential denominator grows at least linearly along the Mellin ray. -/
theorem deBruijnNewmanTitchmarshMellinRay_mul_le_norm_denominator
    {r : ℝ} (hr : 0 ≤ r) :
    Real.sqrt 2 / 2 * r ≤
      ‖deBruijnNewmanTitchmarshPhiDenominator
        (deBruijnNewmanTitchmarshMellinRayDirection * r)‖ := by
  have hreverse := norm_sub_norm_le
    (Complex.exp (deBruijnNewmanTitchmarshMellinRayDirection * (r : ℂ)))
    (1 : ℂ)
  have hexp := Real.add_one_le_exp (Real.sqrt 2 / 2 * r)
  rw [Complex.norm_exp] at hreverse
  simp only [Complex.mul_re,
    deBruijnNewmanTitchmarshMellinRayDirection_re,
    deBruijnNewmanTitchmarshMellinRayDirection_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, norm_one] at hreverse
  unfold deBruijnNewmanTitchmarshPhiDenominator
  linarith

/-- The quadratic remainder separated from the zeta kernel. -/
def deBruijnNewmanTitchmarshMellinRemainderIntegrand
    (s : ℂ) (r : ℝ) : ℂ :=
  (r : ℂ) ^ (s - 1) *
      Complex.exp
        (deBruijnNewmanTitchmarshPhiMellinQuadratic
          (deBruijnNewmanTitchmarshMellinRayDirection * r)) /
    deBruijnNewmanTitchmarshPhiDenominator
      (deBruijnNewmanTitchmarshMellinRayDirection * r)

/-- An explicit integrable Gaussian majorant for the quadratic remainder. -/
def deBruijnNewmanTitchmarshMellinRemainderMajorant
    (s : ℂ) (r : ℝ) : ℝ :=
  (1 / (Real.sqrt 2 / 2) * Real.exp (Real.pi / 4)) *
    (r ^ (s.re - 2) * Real.exp (-(1 / (8 * Real.pi)) * r ^ 2))

theorem deBruijnNewmanTitchmarshPhiMellinQuadratic_ray_re_le (r : ℝ) :
    (deBruijnNewmanTitchmarshPhiMellinQuadratic
        (deBruijnNewmanTitchmarshMellinRayDirection * r)).re ≤
      -(1 / (8 * Real.pi)) * r ^ 2 + Real.pi / 4 := by
  rw [deBruijnNewmanTitchmarshPhiMellinQuadratic_ray_re]
  have hscale : 0 < 8 * Real.pi := by positivity
  apply (mul_le_mul_iff_of_pos_left hscale).mp
  field_simp [Real.pi_ne_zero]
  nlinarith [sq_nonneg (r - Real.sqrt 2 * Real.pi), Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]

theorem integrableOn_deBruijnNewmanTitchmarshMellinRemainderMajorant
    {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn
      (deBruijnNewmanTitchmarshMellinRemainderMajorant s) (Ioi 0) := by
  have hbase := integrableOn_rpow_mul_exp_neg_mul_sq
    (b := 1 / (8 * Real.pi)) (by positivity)
    (s := s.re - 2) (by linarith)
  exact hbase.const_mul
    (1 / (Real.sqrt 2 / 2) * Real.exp (Real.pi / 4))

theorem norm_deBruijnNewmanTitchmarshMellinRemainderIntegrand_le_majorant
    (s : ℂ) {r : ℝ} (hr : 0 < r) :
    ‖deBruijnNewmanTitchmarshMellinRemainderIntegrand s r‖ ≤
      deBruijnNewmanTitchmarshMellinRemainderMajorant s r := by
  have hc : 0 < Real.sqrt 2 / 2 := by positivity
  have hcr : 0 < Real.sqrt 2 / 2 * r := mul_pos hc hr
  have hden :=
    deBruijnNewmanTitchmarshMellinRay_mul_le_norm_denominator hr.le
  have hquad :=
    deBruijnNewmanTitchmarshPhiMellinQuadratic_ray_re_le r
  unfold deBruijnNewmanTitchmarshMellinRemainderIntegrand
  rw [norm_div, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hr, Complex.norm_exp]
  simp only [Complex.sub_re, Complex.one_re]
  calc
    r ^ (s.re - 1) *
          Real.exp
            (deBruijnNewmanTitchmarshPhiMellinQuadratic
              (deBruijnNewmanTitchmarshMellinRayDirection * ↑r)).re /
        ‖deBruijnNewmanTitchmarshPhiDenominator
          (deBruijnNewmanTitchmarshMellinRayDirection * ↑r)‖ ≤
        r ^ (s.re - 1) *
            Real.exp
              (deBruijnNewmanTitchmarshPhiMellinQuadratic
                (deBruijnNewmanTitchmarshMellinRayDirection * ↑r)).re /
          (Real.sqrt 2 / 2 * r) := by
      exact div_le_div_of_nonneg_left
        (mul_nonneg (Real.rpow_nonneg hr.le _) (Real.exp_nonneg _)) hcr hden
    _ ≤ r ^ (s.re - 1) *
            Real.exp (-(1 / (8 * Real.pi)) * r ^ 2 + Real.pi / 4) /
          (Real.sqrt 2 / 2 * r) := by
      gcongr
    _ = deBruijnNewmanTitchmarshMellinRemainderMajorant s r := by
      unfold deBruijnNewmanTitchmarshMellinRemainderMajorant
      rw [Real.exp_add]
      rw [show s.re - 2 = (s.re - 1) - 1 by ring,
        Real.rpow_sub hr, Real.rpow_one]
      field_simp [hr.ne', hc.ne']
      rw [← Real.rpow_two, ← Real.rpow_add hr]
      ring

theorem continuousOn_deBruijnNewmanTitchmarshMellinRemainderIntegrand
    (s : ℂ) :
    ContinuousOn
      (deBruijnNewmanTitchmarshMellinRemainderIntegrand s) (Ioi 0) := by
  apply continuousOn_of_forall_continuousAt
  intro r hr
  unfold deBruijnNewmanTitchmarshMellinRemainderIntegrand
  apply ContinuousAt.div
  · apply ContinuousAt.mul
    · exact Complex.continuousAt_ofReal_cpow_const r (s - 1) (Or.inr hr.ne')
    · apply ContinuousAt.cexp
      unfold deBruijnNewmanTitchmarshPhiMellinQuadratic
      fun_prop
  · unfold deBruijnNewmanTitchmarshPhiDenominator
    fun_prop
  · exact deBruijnNewmanTitchmarshMellinRay_denominator_ne_zero hr

theorem integrableOn_deBruijnNewmanTitchmarshMellinRemainderIntegrand
    {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn
      (deBruijnNewmanTitchmarshMellinRemainderIntegrand s) (Ioi 0) := by
  refine Integrable.mono'
    (integrableOn_deBruijnNewmanTitchmarshMellinRemainderMajorant hs)
    ((continuousOn_deBruijnNewmanTitchmarshMellinRemainderIntegrand s).aestronglyMeasurable
      measurableSet_Ioi) ?_
  apply (ae_restrict_iff' measurableSet_Ioi).mpr
  filter_upwards with r hr
  exact norm_deBruijnNewmanTitchmarshMellinRemainderIntegrand_le_majorant s hr

theorem deBruijnNewmanTitchmarshMellinDifferenceIntegrand_eq
    (s : ℂ) (r : ℝ) :
    deBruijnNewmanTitchmarshMellinDifferenceIntegrand s r =
      deBruijnNewmanTitchmarshMellinZetaIntegrand s r -
        deBruijnNewmanTitchmarshMellinRemainderIntegrand s r := by
  unfold deBruijnNewmanTitchmarshMellinDifferenceIntegrand
  unfold deBruijnNewmanTitchmarshMellinZetaIntegrand
  unfold deBruijnNewmanTitchmarshMellinRemainderIntegrand
  ring

theorem integrableOn_deBruijnNewmanTitchmarshMellinDifferenceIntegrand
    {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn
      (deBruijnNewmanTitchmarshMellinDifferenceIntegrand s) (Ioi 0) := by
  have houter :=
    (integrable_deBruijnNewmanTitchmarshMellinFubiniIntegrand hs).integral_prod_left
  have hphi : IntegrableOn
      (fun r : ℝ =>
        (r : ℂ) ^ (s - 1) *
          deBruijnNewmanTitchmarshPhi
            (deBruijnNewmanTitchmarshPhiMellinParameter
              (deBruijnNewmanTitchmarshMellinRayDirection * r)))
      (Ioi 0) := by
    exact houter.congr (Filter.Eventually.of_forall fun r =>
      deBruijnNewmanTitchmarshMellinFubini_outer s r)
  have hconstDiff : IntegrableOn
      (fun r : ℝ =>
        (2 * (Real.pi : ℂ) * Complex.I) *
          deBruijnNewmanTitchmarshMellinDifferenceIntegrand s r)
      (Ioi 0) := by
    apply hphi.congr
    apply (ae_restrict_iff' measurableSet_Ioi).mpr
    filter_upwards with r hr
    rw [deBruijnNewmanTitchmarshPhi_mellin_specialization_div hr]
    unfold deBruijnNewmanTitchmarshMellinDifferenceIntegrand
    ring
  have hconst : IsUnit (2 * (Real.pi : ℂ) * Complex.I) := by
    rw [isUnit_iff_ne_zero]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  exact (integrable_const_mul_iff hconst
    (deBruijnNewmanTitchmarshMellinDifferenceIntegrand s)).mp hconstDiff

theorem integrableOn_deBruijnNewmanTitchmarshMellinZetaIntegrand
    {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn
      (deBruijnNewmanTitchmarshMellinZetaIntegrand s) (Ioi 0) := by
  have hsum :=
    (integrableOn_deBruijnNewmanTitchmarshMellinDifferenceIntegrand
        (zero_lt_one.trans hs)).add
      (integrableOn_deBruijnNewmanTitchmarshMellinRemainderIntegrand hs)
  apply hsum.congr
  exact Filter.Eventually.of_forall fun r => by
    change deBruijnNewmanTitchmarshMellinDifferenceIntegrand s r +
        deBruijnNewmanTitchmarshMellinRemainderIntegrand s r =
      deBruijnNewmanTitchmarshMellinZetaIntegrand s r
    rw [deBruijnNewmanTitchmarshMellinDifferenceIntegrand_eq]
    ring

theorem deBruijnNewmanTitchmarshMellinDifferenceIntegral_eq
    {s : ℂ} (hs : 1 < s.re) :
    (∫ r : ℝ in Ioi 0,
        deBruijnNewmanTitchmarshMellinDifferenceIntegrand s r) =
      (∫ r : ℝ in Ioi 0,
        deBruijnNewmanTitchmarshMellinZetaIntegrand s r) -
      ∫ r : ℝ in Ioi 0,
        deBruijnNewmanTitchmarshMellinRemainderIntegrand s r := by
  rw [← integral_sub
    (integrableOn_deBruijnNewmanTitchmarshMellinZetaIntegrand hs)
    (integrableOn_deBruijnNewmanTitchmarshMellinRemainderIntegrand hs)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun r =>
    deBruijnNewmanTitchmarshMellinDifferenceIntegrand_eq s r

/-- Titchmarsh's master bridge with the zeta and quadratic-remainder branches separated. -/
theorem deBruijnNewmanTitchmarshMellin_master_separated
    {s : ℂ} (hs : 1 < s.re) :
    (∫ v : ℝ,
        (deBruijnNewmanTitchmarshMellinRate v ^ (-s) * Complex.Gamma s) *
          deBruijnNewmanTitchmarshPhiLineIntegrand (1 / 2) v) =
      2 * (Real.pi : ℂ) * Complex.I *
        (deBruijnNewmanTitchmarshMellinRayDirection ^ (-s) *
            Complex.Gamma s * riemannZeta s -
          ∫ r : ℝ in Ioi 0,
            deBruijnNewmanTitchmarshMellinRemainderIntegrand s r) := by
  rw [deBruijnNewmanTitchmarshMellin_master (zero_lt_one.trans hs)]
  rw [deBruijnNewmanTitchmarshMellinDifferenceIntegral_eq hs]
  rw [deBruijnNewmanTitchmarshMellinZetaIntegral_eq hs]

/-- The actual quadratic-remainder integrand on the slanted source ray, including its Jacobian. -/
def deBruijnNewmanTitchmarshMellinRemainderRayIntegrand
    (s : ℂ) (r : ℝ) : ℂ :=
  (deBruijnNewmanTitchmarshMellinRayDirection * r) ^ (s - 1) *
      Complex.exp
        (deBruijnNewmanTitchmarshPhiMellinQuadratic
          (deBruijnNewmanTitchmarshMellinRayDirection * r)) /
    deBruijnNewmanTitchmarshPhiDenominator
      (deBruijnNewmanTitchmarshMellinRayDirection * r) *
    deBruijnNewmanTitchmarshMellinRayDirection

theorem deBruijnNewmanTitchmarshMellinRemainderRayIntegrand_eq
    (s : ℂ) {r : ℝ} (hr : 0 < r) :
    deBruijnNewmanTitchmarshMellinRemainderRayIntegrand s r =
      deBruijnNewmanTitchmarshMellinRayDirection ^ s *
        deBruijnNewmanTitchmarshMellinRemainderIntegrand s r := by
  have he : deBruijnNewmanTitchmarshMellinRayDirection ≠ 0 := by
    intro he0
    have hnorm := norm_deBruijnNewmanTitchmarshMellinRayDirection
    rw [he0, norm_zero] at hnorm
    norm_num at hnorm
  have hepow :
      deBruijnNewmanTitchmarshMellinRayDirection ^ (s - 1) *
          deBruijnNewmanTitchmarshMellinRayDirection =
        deBruijnNewmanTitchmarshMellinRayDirection ^ s := by
    conv_lhs =>
      rhs
      rw [← Complex.cpow_one deBruijnNewmanTitchmarshMellinRayDirection]
    rw [← Complex.cpow_add _ _ he]
    congr 1
    ring
  unfold deBruijnNewmanTitchmarshMellinRemainderRayIntegrand
  unfold deBruijnNewmanTitchmarshMellinRemainderIntegrand
  rw [mul_comm deBruijnNewmanTitchmarshMellinRayDirection (r : ℂ)]
  rw [deBruijnNewman_cpow_ofReal_mul hr he]
  rw [← hepow]
  ring

theorem deBruijnNewmanTitchmarshMellinRemainderRayIntegral_eq
    {s : ℂ} (hs : 1 < s.re) :
    (∫ r : ℝ in Ioi 0,
        deBruijnNewmanTitchmarshMellinRemainderRayIntegrand s r) =
      deBruijnNewmanTitchmarshMellinRayDirection ^ s *
        ∫ r : ℝ in Ioi 0,
          deBruijnNewmanTitchmarshMellinRemainderIntegrand s r := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply (ae_restrict_iff' measurableSet_Ioi).mpr
  filter_upwards with r hr
  exact deBruijnNewmanTitchmarshMellinRemainderRayIntegrand_eq s hr

/-- The source-form Mellin identity immediately before Titchmarsh's ray-to-line deformation. -/
theorem deBruijnNewmanTitchmarshMellin_source_before_deformation
    {s : ℂ} (hs : 1 < s.re) :
    deBruijnNewmanTitchmarshMellinRayDirection ^ s *
        (∫ v : ℝ,
          (deBruijnNewmanTitchmarshMellinRate v ^ (-s) * Complex.Gamma s) *
            deBruijnNewmanTitchmarshPhiLineIntegrand (1 / 2) v) =
      2 * (Real.pi : ℂ) * Complex.I *
        (Complex.Gamma s * riemannZeta s -
          ∫ r : ℝ in Ioi 0,
            deBruijnNewmanTitchmarshMellinRemainderRayIntegrand s r) := by
  rw [deBruijnNewmanTitchmarshMellin_master_separated hs]
  rw [deBruijnNewmanTitchmarshMellinRemainderRayIntegral_eq hs]
  have he : deBruijnNewmanTitchmarshMellinRayDirection ≠ 0 := by
    intro he0
    have hnorm := norm_deBruijnNewmanTitchmarshMellinRayDirection
    rw [he0, norm_zero] at hnorm
    norm_num at hnorm
  have hepow : deBruijnNewmanTitchmarshMellinRayDirection ^ s ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl he)
  rw [Complex.cpow_neg]
  field_simp [hepow]

/-- The reflection of Titchmarsh's line `L` in the real axis, with its reflected orientation. -/
def deBruijnNewmanTitchmarshPhiReflectedLine (v : ℝ) : ℂ :=
  -(Real.pi : ℂ) + deBruijnNewmanTitchmarshMellinRayDirection * v

theorem deBruijnNewmanTitchmarshPhiReflectedLine_eq_star (v : ℝ) :
    deBruijnNewmanTitchmarshPhiReflectedLine v =
      starRingEnd ℂ (deBruijnNewmanTitchmarshPhiLine v) := by
  simp [deBruijnNewmanTitchmarshPhiReflectedLine,
    deBruijnNewmanTitchmarshPhiLine,
    deBruijnNewmanTitchmarshMellinRayDirection]

@[simp] theorem deBruijnNewmanTitchmarshPhiReflectedLine_re (v : ℝ) :
    (deBruijnNewmanTitchmarshPhiReflectedLine v).re =
      -Real.pi + (Real.sqrt 2 / 2) * v := by
  rw [deBruijnNewmanTitchmarshPhiReflectedLine]
  simp

@[simp] theorem deBruijnNewmanTitchmarshPhiReflectedLine_im (v : ℝ) :
    (deBruijnNewmanTitchmarshPhiReflectedLine v).im =
      -(Real.sqrt 2 / 2) * v := by
  rw [deBruijnNewmanTitchmarshPhiReflectedLine]
  simp

/-- The reflected Titchmarsh direction is `i` times the fixed Riemann--Siegel direction. -/
theorem deBruijnNewmanTitchmarshMellinRayDirection_eq_I_mul_riemannSiegelDirection :
    deBruijnNewmanTitchmarshMellinRayDirection =
      Complex.I * deBruijnNewmanRiemannSiegelDirection := by
  apply Complex.ext
  · simp [Complex.mul_re]
  · simp [Complex.mul_im]

theorem deBruijnNewmanTitchmarshMellinRayDirection_mul_pi_sqrt_two :
    deBruijnNewmanTitchmarshMellinRayDirection *
        ((Real.pi * Real.sqrt 2 : ℝ) : ℂ) =
      (Real.pi : ℂ) - (Real.pi : ℂ) * Complex.I := by
  have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  apply Complex.ext
  · simp only [Complex.mul_re,
      deBruijnNewmanTitchmarshMellinRayDirection_re,
      deBruijnNewmanTitchmarshMellinRayDirection_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      Complex.sub_re, Complex.I_re, Complex.I_im]
    calc
      Real.sqrt 2 / 2 * (Real.pi * Real.sqrt 2) =
          Real.pi * (Real.sqrt 2 * Real.sqrt 2) / 2 := by ring
      _ = Real.pi := by rw [hsqrt]; ring
    ring
  · simp only [Complex.mul_im,
      deBruijnNewmanTitchmarshMellinRayDirection_re,
      deBruijnNewmanTitchmarshMellinRayDirection_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add,
      Complex.sub_im, Complex.I_re, Complex.I_im]
    calc
      -(Real.sqrt 2 / 2) * (Real.pi * Real.sqrt 2) =
          -(Real.pi * (Real.sqrt 2 * Real.sqrt 2) / 2) := by ring
      _ = -Real.pi := by rw [hsqrt]; ring
    ring

/-- The exact affine map from the reflected Titchmarsh line to the `N=0`
Riemann--Siegel line. Its negative real slope records the orientation reversal. -/
theorem deBruijnNewmanTitchmarshPhiReflectedLine_affine_riemannSiegelLine
    (v : ℝ) :
    deBruijnNewmanTitchmarshPhiReflectedLine
        (Real.pi * Real.sqrt 2 - 2 * Real.pi * v) =
      -2 * (Real.pi : ℂ) * Complex.I *
        deBruijnNewmanRiemannSiegelLine 0 v := by
  rw [deBruijnNewmanTitchmarshPhiReflectedLine]
  rw [deBruijnNewmanRiemannSiegelLine]
  simp only [Nat.cast_zero, zero_add]
  have hscale :=
    deBruijnNewmanTitchmarshMellinRayDirection_mul_pi_sqrt_two
  have hdir :=
    deBruijnNewmanTitchmarshMellinRayDirection_eq_I_mul_riemannSiegelDirection
  push_cast at hscale ⊢
  rw [mul_sub, hscale, hdir]
  ring

/-- Under `z = -2*pi*i*w`, the reflected Titchmarsh quadratic is the
Riemann--Siegel quadratic together with the cancelling linear exponential. -/
theorem deBruijnNewmanTitchmarshPhiMellinQuadratic_neg_two_pi_I_mul
    (w : ℂ) :
    deBruijnNewmanTitchmarshPhiMellinQuadratic
        (-2 * (Real.pi : ℂ) * Complex.I * w) =
      Complex.I * Real.pi * w ^ 2 - (Real.pi : ℂ) * Complex.I * w := by
  rw [deBruijnNewmanTitchmarshPhiMellinQuadratic]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  ring_nf
  simp [Complex.I_sq]

/-- The denominator conversion used in Titchmarsh `(2.10.6)`. -/
theorem deBruijnNewmanTitchmarshPhiDenominator_neg_two_pi_I_mul
    (w : ℂ) :
    deBruijnNewmanTitchmarshPhiDenominator
        (-2 * (Real.pi : ℂ) * Complex.I * w) =
      -Complex.exp (-((Real.pi : ℂ) * Complex.I * w)) *
        deBruijnNewmanRiemannSiegelDenominator w := by
  let a : ℂ := Complex.exp (-((Real.pi : ℂ) * Complex.I * w))
  let b : ℂ := Complex.exp ((Real.pi : ℂ) * Complex.I * w)
  have hexp :
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * w) = a * a := by
    rw [show -2 * (Real.pi : ℂ) * Complex.I * w =
        -((Real.pi : ℂ) * Complex.I * w) +
          -((Real.pi : ℂ) * Complex.I * w) by ring]
    rw [Complex.exp_add]
  have hab : a * b = 1 := by
    rw [← Complex.exp_add]
    change Complex.exp
      (-((Real.pi : ℂ) * Complex.I * w) +
        (Real.pi : ℂ) * Complex.I * w) = 1
    rw [neg_add_cancel, Complex.exp_zero]
  unfold deBruijnNewmanTitchmarshPhiDenominator
  unfold deBruijnNewmanRiemannSiegelDenominator
  rw [show -((Real.pi : ℂ) * Complex.I) * w =
      -((Real.pi : ℂ) * Complex.I * w) by ring]
  change Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * w) - 1 =
    -a * (b - a)
  rw [hexp]
  linear_combination hab

/-- The branch-free exponential quotient is exactly the Riemann--Siegel quotient.
The complex-power branch is deliberately not folded into this theorem. -/
theorem deBruijnNewmanTitchmarshPhiQuadraticQuotient_neg_two_pi_I_mul
    {w : ℂ} (hw : deBruijnNewmanRiemannSiegelDenominator w ≠ 0) :
    Complex.exp
          (deBruijnNewmanTitchmarshPhiMellinQuadratic
            (-2 * (Real.pi : ℂ) * Complex.I * w)) /
        deBruijnNewmanTitchmarshPhiDenominator
          (-2 * (Real.pi : ℂ) * Complex.I * w) =
      -Complex.exp (Complex.I * Real.pi * w ^ 2) /
        deBruijnNewmanRiemannSiegelDenominator w := by
  rw [deBruijnNewmanTitchmarshPhiMellinQuadratic_neg_two_pi_I_mul]
  rw [deBruijnNewmanTitchmarshPhiDenominator_neg_two_pi_I_mul]
  rw [Complex.exp_sub]
  have hexp :
      Complex.exp (-((Real.pi : ℂ) * Complex.I * w)) ≠ 0 :=
    Complex.exp_ne_zero _
  field_simp [hexp, hw]
  rw [← Complex.exp_add]
  simp

theorem deBruijnNewmanTitchmarshPhiQuadraticQuotient_reflectedLine_affine
    (v : ℝ) :
    Complex.exp
          (deBruijnNewmanTitchmarshPhiMellinQuadratic
            (deBruijnNewmanTitchmarshPhiReflectedLine
              (Real.pi * Real.sqrt 2 - 2 * Real.pi * v))) /
        deBruijnNewmanTitchmarshPhiDenominator
          (deBruijnNewmanTitchmarshPhiReflectedLine
            (Real.pi * Real.sqrt 2 - 2 * Real.pi * v)) =
      -Complex.exp
          (Complex.I * Real.pi *
            deBruijnNewmanRiemannSiegelLine 0 v ^ 2) /
        deBruijnNewmanRiemannSiegelDenominator
          (deBruijnNewmanRiemannSiegelLine 0 v) := by
  rw [deBruijnNewmanTitchmarshPhiReflectedLine_affine_riemannSiegelLine]
  exact deBruijnNewmanTitchmarshPhiQuadraticQuotient_neg_two_pi_I_mul
    (deBruijnNewmanRiemannSiegelDenominator_ne_zero 0 v)

/-- Titchmarsh's power on the reflected line, made explicit by transport through
`z = -2*pi*i*w`. This is the continuous contour branch used in `(2.10.6)`; it must not be
replaced by the principal power of `z` across the whole reflected line. -/
def deBruijnNewmanTitchmarshPhiReflectedLinePower (s : ℂ) (v : ℝ) : ℂ :=
  (-2 * (Real.pi : ℂ) * Complex.I) ^ (s - 1) *
    deBruijnNewmanRiemannSiegelLine 0
      ((Real.pi * Real.sqrt 2 - v) / (2 * Real.pi)) ^ (s - 1)

theorem deBruijnNewmanTitchmarshPhiReflectedLinePower_affine
    (s : ℂ) (v : ℝ) :
    deBruijnNewmanTitchmarshPhiReflectedLinePower s
        (Real.pi * Real.sqrt 2 - 2 * Real.pi * v) =
      (-2 * (Real.pi : ℂ) * Complex.I) ^ (s - 1) *
        deBruijnNewmanRiemannSiegelLine 0 v ^ (s - 1) := by
  unfold deBruijnNewmanTitchmarshPhiReflectedLinePower
  congr 2
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- The reflected-line remainder from Titchmarsh `(2.10.6)`, with the transported power branch
and reflected line Jacobian both explicit. -/
def deBruijnNewmanTitchmarshPhiReflectedLineRemainderIntegrand
    (s : ℂ) (v : ℝ) : ℂ :=
  deBruijnNewmanTitchmarshPhiReflectedLinePower s v *
      Complex.exp
        (deBruijnNewmanTitchmarshPhiMellinQuadratic
          (deBruijnNewmanTitchmarshPhiReflectedLine v)) /
    deBruijnNewmanTitchmarshPhiDenominator
      (deBruijnNewmanTitchmarshPhiReflectedLine v) *
    deBruijnNewmanTitchmarshMellinRayDirection

/-- After the exact orientation-reversing affine map, the reflected Titchmarsh integrand is a
scalar multiple of the actual `R_(0,0)` line integrand at parameter `1-s`. -/
theorem deBruijnNewmanTitchmarshPhiReflectedLineRemainderIntegrand_affine
    (s : ℂ) (v : ℝ) :
    deBruijnNewmanTitchmarshPhiReflectedLineRemainderIntegrand s
        (Real.pi * Real.sqrt 2 - 2 * Real.pi * v) =
      -Complex.I * (-2 * (Real.pi : ℂ) * Complex.I) ^ (s - 1) *
        deBruijnNewmanRiemannSiegelLineIntegrand 0 (1 - s) v := by
  unfold deBruijnNewmanTitchmarshPhiReflectedLineRemainderIntegrand
  rw [deBruijnNewmanTitchmarshPhiReflectedLinePower_affine]
  have hquot :=
    deBruijnNewmanTitchmarshPhiQuadraticQuotient_reflectedLine_affine v
  rw [div_eq_mul_inv] at hquot ⊢
  calc
    _ = (-2 * (Real.pi : ℂ) * Complex.I) ^ (s - 1) *
          deBruijnNewmanRiemannSiegelLine 0 v ^ (s - 1) *
          (Complex.exp
              (deBruijnNewmanTitchmarshPhiMellinQuadratic
                (deBruijnNewmanTitchmarshPhiReflectedLine
                  (Real.pi * Real.sqrt 2 - 2 * Real.pi * v))) *
            (deBruijnNewmanTitchmarshPhiDenominator
              (deBruijnNewmanTitchmarshPhiReflectedLine
                (Real.pi * Real.sqrt 2 - 2 * Real.pi * v)))⁻¹) *
          deBruijnNewmanTitchmarshMellinRayDirection := by ring
    _ = (-2 * (Real.pi : ℂ) * Complex.I) ^ (s - 1) *
          deBruijnNewmanRiemannSiegelLine 0 v ^ (s - 1) *
          (-Complex.exp
              (Complex.I * Real.pi *
                deBruijnNewmanRiemannSiegelLine 0 v ^ 2) /
            deBruijnNewmanRiemannSiegelDenominator
              (deBruijnNewmanRiemannSiegelLine 0 v)) *
          deBruijnNewmanTitchmarshMellinRayDirection := by rw [hquot]
    _ = -Complex.I * (-2 * (Real.pi : ℂ) * Complex.I) ^ (s - 1) *
          deBruijnNewmanRiemannSiegelLineIntegrand 0 (1 - s) v := by
      rw [deBruijnNewmanTitchmarshMellinRayDirection_eq_I_mul_riemannSiegelDirection]
      unfold deBruijnNewmanRiemannSiegelLineIntegrand
      unfold deBruijnNewmanRiemannSiegelKernel
      unfold deBruijnNewmanRiemannSiegelNumerator
      have hexponent : -(1 - s) = s - 1 := by ring
      rw [hexponent]
      ring

/-- The whole-line Lebesgue substitution behind the reflected contour parameter change. The
absolute Jacobian is `2*pi`; contour orientation is already carried by the complex line factors. -/
theorem integral_comp_titchmarsh_reflected_affine (f : ℝ → ℂ) :
    (∫ v : ℝ, f (Real.pi * Real.sqrt 2 - 2 * Real.pi * v)) =
      (2 * Real.pi)⁻¹ • ∫ u : ℝ, f u := by
  have h := Measure.integral_comp_mul_left
    (fun u : ℝ ↦ f (Real.pi * Real.sqrt 2 + u)) (-2 * Real.pi)
  rw [integral_add_left_eq_self] at h
  have htwoPi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have habs : |(-2 * Real.pi)⁻¹| = (2 * Real.pi)⁻¹ := by
    rw [show -2 * Real.pi = -(2 * Real.pi) by ring]
    rw [inv_neg, abs_neg, abs_of_pos (inv_pos.mpr htwoPi)]
  rw [habs] at h
  convert h using 1 <;> congr 1 <;> funext v <;> congr 1 <;> ring

/-- The full reflected-line remainder integral with Titchmarsh's transported power branch. -/
def deBruijnNewmanTitchmarshPhiReflectedLineRemainderIntegral (s : ℂ) : ℂ :=
  ∫ v : ℝ, deBruijnNewmanTitchmarshPhiReflectedLineRemainderIntegrand s v

theorem integrable_deBruijnNewmanTitchmarshPhiReflectedLineRemainderIntegrand
    (s : ℂ) :
    Integrable (deBruijnNewmanTitchmarshPhiReflectedLineRemainderIntegrand s) := by
  let f := deBruijnNewmanTitchmarshPhiReflectedLineRemainderIntegrand s
  let c : ℂ := -Complex.I * (-2 * (Real.pi : ℂ) * Complex.I) ^ (s - 1)
  have hbase : Integrable
      (fun v : ℝ ↦ c * deBruijnNewmanRiemannSiegelLineIntegrand 0 (1 - s) v) :=
    (integrable_deBruijnNewmanRiemannSiegelLineIntegrand 0 (1 - s)).const_mul c
  have haffine : Integrable
      (fun v : ℝ ↦ f (Real.pi * Real.sqrt 2 - 2 * Real.pi * v)) := by
    apply hbase.congr
    exact Filter.Eventually.of_forall fun v ↦ by
      change c * deBruijnNewmanRiemannSiegelLineIntegrand 0 (1 - s) v =
        f (Real.pi * Real.sqrt 2 - 2 * Real.pi * v)
      exact
        (deBruijnNewmanTitchmarshPhiReflectedLineRemainderIntegrand_affine s v).symm
  let p : ℝ := Real.pi * Real.sqrt 2
  let a : ℝ := -(2 * Real.pi)⁻¹
  have ha : a ≠ 0 := by
    unfold a
    exact neg_ne_zero.mpr (inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero))
  have hrecover : Integrable
      (fun u : ℝ ↦
        (fun v : ℝ ↦ f (p - 2 * Real.pi * v))
          (p / (2 * Real.pi) + a * u)) := by
    have hshift := haffine.comp_add_left (p / (2 * Real.pi))
    exact hshift.comp_mul_left' ha
  apply hrecover.congr
  exact Filter.Eventually.of_forall fun u ↦ by
    change f (p - 2 * Real.pi * (p / (2 * Real.pi) + a * u)) = f u
    congr 1
    unfold p a
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    ring

/-- Exact conversion of Titchmarsh's reflected line to the raw `R_(0,0)` integral. -/
theorem deBruijnNewmanTitchmarshPhiReflectedLineRemainderIntegral_eq
    (s : ℂ) :
    deBruijnNewmanTitchmarshPhiReflectedLineRemainderIntegral s =
      -2 * (Real.pi : ℂ) * Complex.I *
        (-2 * (Real.pi : ℂ) * Complex.I) ^ (s - 1) *
        deBruijnNewmanRiemannSiegelRawIntegral 0 (1 - s) := by
  have hchange := integral_comp_titchmarsh_reflected_affine
    (deBruijnNewmanTitchmarshPhiReflectedLineRemainderIntegrand s)
  have haffine :
      (∫ v : ℝ,
          deBruijnNewmanTitchmarshPhiReflectedLineRemainderIntegrand s
            (Real.pi * Real.sqrt 2 - 2 * Real.pi * v)) =
        -Complex.I * (-2 * (Real.pi : ℂ) * Complex.I) ^ (s - 1) *
          deBruijnNewmanRiemannSiegelRawIntegral 0 (1 - s) := by
    rw [deBruijnNewmanRiemannSiegelRawIntegral]
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun v ↦
      deBruijnNewmanTitchmarshPhiReflectedLineRemainderIntegrand_affine s v
  rw [haffine] at hchange
  unfold deBruijnNewmanTitchmarshPhiReflectedLineRemainderIntegral
  change
    -Complex.I * (-2 * (Real.pi : ℂ) * Complex.I) ^ (s - 1) *
        deBruijnNewmanRiemannSiegelRawIntegral 0 (1 - s) =
      (((2 * Real.pi)⁻¹ : ℝ) : ℂ) *
        (∫ v : ℝ, deBruijnNewmanTitchmarshPhiReflectedLineRemainderIntegrand s v)
    at hchange
  have htwoPi : (2 * Real.pi : ℂ) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hcast : ((((2 * Real.pi)⁻¹ : ℝ) : ℂ)) =
      (2 * (Real.pi : ℂ))⁻¹ := by
    push_cast
    rfl
  rw [hcast] at hchange
  have hclear := congrArg (fun z : ℂ ↦ (2 * (Real.pi : ℂ)) * z) hchange
  field_simp [htwoPi] at hclear
  have hbase : -(2 * (Real.pi : ℂ) * Complex.I) =
      -2 * (Real.pi : ℂ) * Complex.I := by ring
  rw [hbase] at hclear
  calc
    _ = -(2 * (Real.pi : ℂ) * Complex.I *
        (-2 * (Real.pi : ℂ) * Complex.I) ^ (s - 1) *
          deBruijnNewmanRiemannSiegelRawIntegral 0 (1 - s)) := hclear.symm
    _ = _ := by ring

/-- The real-linear coordinate constant on every line parallel to the transformed
Titchmarsh contour. -/
def deBruijnNewmanTitchmarshMellinWProjection (w : ℂ) : ℝ :=
  w.im - w.re

/-- The open convex band between the transformed origin line and the next integer-pole line. -/
def deBruijnNewmanTitchmarshMellinWBand : Set ℂ :=
  {w | -1 < deBruijnNewmanTitchmarshMellinWProjection w ∧
    deBruijnNewmanTitchmarshMellinWProjection w < 0}

theorem convex_deBruijnNewmanTitchmarshMellinWBand :
    Convex ℝ deBruijnNewmanTitchmarshMellinWBand := by
  rw [deBruijnNewmanTitchmarshMellinWBand]
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  unfold deBruijnNewmanTitchmarshMellinWProjection at hx hy ⊢
  have hre : (a • x + b • y).re = a * x.re + b * y.re := by simp
  have him : (a • x + b • y).im = a * x.im + b * y.im := by simp
  rw [hre, him]
  by_cases ha0 : a = 0
  · subst a
    have hb1 : b = 1 := by linarith
    subst b
    simpa using hy
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    constructor
    · have hxmul := mul_lt_mul_of_pos_left hx.1 hapos
      have hymul := mul_le_mul_of_nonneg_left (le_of_lt hy.1) hb
      calc
        -1 = a * (-1) + b * (-1) := by linarith
        _ < a * (x.im - x.re) + b * (y.im - y.re) :=
          add_lt_add_of_lt_of_le hxmul hymul
        _ = a * x.im + b * y.im - (a * x.re + b * y.re) := by ring
    · have hxmul := mul_lt_mul_of_pos_left hx.2 hapos
      have hymul := mul_le_mul_of_nonneg_left (le_of_lt hy.2) hb
      calc
        a * x.im + b * y.im - (a * x.re + b * y.re) =
            a * (x.im - x.re) + b * (y.im - y.re) := by ring
        _ < a * 0 + b * 0 := add_lt_add_of_lt_of_le hxmul hymul
        _ = 0 := by ring

theorem isOpen_deBruijnNewmanTitchmarshMellinWBand :
    IsOpen deBruijnNewmanTitchmarshMellinWBand := by
  have hp : Continuous deBruijnNewmanTitchmarshMellinWProjection := by
    unfold deBruijnNewmanTitchmarshMellinWProjection
    fun_prop
  exact (isOpen_lt continuous_const hp).inter (isOpen_lt hp continuous_const)

theorem deBruijnNewmanTitchmarshMellinWBand_mem_slitPlane
    {w : ℂ} (hw : w ∈ deBruijnNewmanTitchmarshMellinWBand) :
    w ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases him : w.im = 0
  · left
    rw [deBruijnNewmanTitchmarshMellinWBand] at hw
    simp only [Set.mem_setOf_eq, deBruijnNewmanTitchmarshMellinWProjection,
      him, zero_sub] at hw
    linarith
  · exact Or.inr him

theorem deBruijnNewmanTitchmarshMellinWBand_denominator_ne_zero
    {w : ℂ} (hw : w ∈ deBruijnNewmanTitchmarshMellinWBand) :
    deBruijnNewmanRiemannSiegelDenominator w ≠ 0 := by
  intro hzero
  obtain ⟨n, hn⟩ :=
    exists_int_of_deBruijnNewmanRiemannSiegelDenominator_eq_zero hzero
  rw [deBruijnNewmanTitchmarshMellinWBand] at hw
  simp only [Set.mem_setOf_eq, deBruijnNewmanTitchmarshMellinWProjection] at hw
  have hre := congrArg Complex.re hn
  have him := congrArg Complex.im hn
  simp only [Complex.intCast_re] at hre
  simp only [Complex.intCast_im] at him
  have hnposR : 0 < (n : ℝ) := by linarith
  have hnltR : (n : ℝ) < 1 := by linarith
  have hnpos : (0 : ℤ) < n := by exact_mod_cast hnposR
  have hnlt : n < (1 : ℤ) := by exact_mod_cast hnltR
  omega

theorem differentiableOn_deBruijnNewmanRiemannSiegelKernel_mellinWBand
    (s : ℂ) :
    DifferentiableOn ℂ (deBruijnNewmanRiemannSiegelKernel (1 - s))
      deBruijnNewmanTitchmarshMellinWBand := by
  intro w hw
  unfold deBruijnNewmanRiemannSiegelKernel
  unfold deBruijnNewmanRiemannSiegelNumerator
  unfold deBruijnNewmanRiemannSiegelDenominator
  have hpow : DifferentiableAt ℂ (fun z : ℂ ↦ z ^ (-(1 - s))) w :=
    differentiableAt_id.cpow_const
      (deBruijnNewmanTitchmarshMellinWBand_mem_slitPlane hw)
  have hnum : DifferentiableAt ℂ
      (fun z : ℂ ↦ z ^ (-(1 - s)) * Complex.exp (Complex.I * Real.pi * z ^ 2)) w := by
    fun_prop
  have hden : DifferentiableAt ℂ
      (fun z : ℂ ↦
        Complex.exp (((Real.pi : ℂ) * Complex.I) * z) -
          Complex.exp (-((Real.pi : ℂ) * Complex.I) * z)) w := by
    fun_prop
  exact (hnum.div hden
    (deBruijnNewmanTitchmarshMellinWBand_denominator_ne_zero hw)).differentiableWithinAt

/-- On the pole-free Mellin band, the Riemann--Siegel kernel has a complex primitive. -/
theorem exists_deBruijnNewmanRiemannSiegelKernel_mellinWBand_primitive
    (s : ℂ) :
    ∃ G : ℂ → ℂ, ∀ w ∈ deBruijnNewmanTitchmarshMellinWBand,
      HasDerivAt G (deBruijnNewmanRiemannSiegelKernel (1 - s) w) w := by
  obtain ⟨G, hG⟩ :=
    convex_deBruijnNewmanTitchmarshMellinWBand.exists_forall_hasDerivWithinAt
      (differentiableOn_deBruijnNewmanRiemannSiegelKernel_mellinWBand s)
  refine ⟨G, fun w hw ↦ ?_⟩
  exact (hG w hw).hasDerivAt
    (isOpen_deBruijnNewmanTitchmarshMellinWBand.mem_nhds hw)

/-- The transformed line corresponding to the source line `z = -c + exp(-pi*i/4) v`. -/
def deBruijnNewmanTitchmarshMellinWLine (c x : ℝ) : ℂ :=
  deBruijnNewmanTitchmarshPhiDirection * x -
    Complex.I * ((c / (2 * Real.pi) : ℝ) : ℂ)

@[simp] theorem deBruijnNewmanTitchmarshMellinWLine_projection (c x : ℝ) :
    deBruijnNewmanTitchmarshMellinWProjection
        (deBruijnNewmanTitchmarshMellinWLine c x) =
      -(c / (2 * Real.pi)) := by
  unfold deBruijnNewmanTitchmarshMellinWProjection
  unfold deBruijnNewmanTitchmarshMellinWLine
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    deBruijnNewmanTitchmarshPhiDirection_re,
    deBruijnNewmanTitchmarshPhiDirection_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

@[simp] theorem deBruijnNewmanTitchmarshMellinWLine_re (c x : ℝ) :
    (deBruijnNewmanTitchmarshMellinWLine c x).re =
      (Real.sqrt 2 / 2) * x := by
  unfold deBruijnNewmanTitchmarshMellinWLine
  simp only [Complex.sub_re, Complex.mul_re,
    deBruijnNewmanTitchmarshPhiDirection_re,
    deBruijnNewmanTitchmarshPhiDirection_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

@[simp] theorem deBruijnNewmanTitchmarshMellinWLine_im (c x : ℝ) :
    (deBruijnNewmanTitchmarshMellinWLine c x).im =
      (Real.sqrt 2 / 2) * x - c / (2 * Real.pi) := by
  unfold deBruijnNewmanTitchmarshMellinWLine
  simp only [Complex.sub_im, Complex.mul_im,
    deBruijnNewmanTitchmarshPhiDirection_re,
    deBruijnNewmanTitchmarshPhiDirection_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

theorem deBruijnNewmanTitchmarshMellinWLine_mem_band
    {c : ℝ} (hc : 0 < c) (hc2pi : c < 2 * Real.pi) (x : ℝ) :
    deBruijnNewmanTitchmarshMellinWLine c x ∈
      deBruijnNewmanTitchmarshMellinWBand := by
  rw [deBruijnNewmanTitchmarshMellinWBand]
  simp only [Set.mem_setOf_eq,
    deBruijnNewmanTitchmarshMellinWLine_projection]
  have htwoPi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  constructor
  · apply (neg_lt_neg_iff.mpr ?_)
    exact (div_lt_one htwoPi).mpr hc2pi
  · exact neg_neg_of_pos (div_pos hc htwoPi)

theorem deBruijnNewmanTitchmarshMellinWLine_norm_lower
    {c q : ℝ} (hc : 0 < c) (hcq : c ≤ q) (x : ℝ) :
    c / (4 * Real.pi) ≤
      ‖deBruijnNewmanTitchmarshMellinWLine q x‖ := by
  let w := deBruijnNewmanTitchmarshMellinWLine q x
  have hq : 0 < q := hc.trans_le hcq
  have hproj : |w.im - w.re| = q / (2 * Real.pi) := by
    change |deBruijnNewmanTitchmarshMellinWProjection w| = _
    rw [deBruijnNewmanTitchmarshMellinWLine_projection]
    rw [abs_neg, abs_of_pos (div_pos hq (by positivity : 0 < 2 * Real.pi))]
  have hprojNorm : |w.im - w.re| ≤ 2 * ‖w‖ := by
    calc
      |w.im - w.re| ≤ |w.im| + |w.re| := abs_sub _ _
      _ ≤ ‖w‖ + ‖w‖ :=
        add_le_add (Complex.abs_im_le_norm w) (Complex.abs_re_le_norm w)
      _ = 2 * ‖w‖ := by ring
  have hcdiv : c / (4 * Real.pi) ≤ q / (4 * Real.pi) := by
    exact div_le_div_of_nonneg_right hcq (by positivity : 0 ≤ 4 * Real.pi)
  calc
    c / (4 * Real.pi) ≤ q / (4 * Real.pi) := hcdiv
    _ = (q / (2 * Real.pi)) / 2 := by ring
    _ = |w.im - w.re| / 2 := by rw [hproj]
    _ ≤ ‖w‖ := (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr (by linarith)

theorem deBruijnNewmanTitchmarshMellinWLine_norm_upper
    {q : ℝ} (hq : 0 < q) (hq2pi : q < 2 * Real.pi) (x : ℝ) :
    ‖deBruijnNewmanTitchmarshMellinWLine q x‖ ≤ |x| + 1 := by
  rw [deBruijnNewmanTitchmarshMellinWLine]
  calc
    ‖deBruijnNewmanTitchmarshPhiDirection * (x : ℂ) -
        Complex.I * ((q / (2 * Real.pi) : ℝ) : ℂ)‖ ≤
        ‖deBruijnNewmanTitchmarshPhiDirection * (x : ℂ)‖ +
          ‖Complex.I * ((q / (2 * Real.pi) : ℝ) : ℂ)‖ := norm_sub_le _ _
    _ = |x| + q / (2 * Real.pi) := by
      rw [norm_mul, norm_deBruijnNewmanTitchmarshPhiDirection, one_mul,
        norm_mul, norm_I, one_mul, norm_real, norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos (div_pos hq (by positivity : 0 < 2 * Real.pi))]
    _ ≤ |x| + 1 := by
      gcongr
      exact (div_lt_one (by positivity : 0 < 2 * Real.pi)).mpr hq2pi |>.le

theorem two_le_norm_deBruijnNewmanRiemannSiegelDenominator_mellinWLine
    {q : ℝ} (hq : 0 < q) (hq2pi : q < 2 * Real.pi)
    {x : ℝ} (hx : 6 ≤ |x|) :
    2 ≤ ‖deBruijnNewmanRiemannSiegelDenominator
      (deBruijnNewmanTitchmarshMellinWLine q x)‖ := by
  apply two_le_norm_deBruijnNewmanRiemannSiegelDenominator_of_im
  rw [deBruijnNewmanTitchmarshMellinWLine_im, abs_mul,
    abs_of_pos Real.pi_pos]
  have hsqrt : (1 / 2 : ℝ) ≤ Real.sqrt 2 / 2 := by
    have hsqrtOne : 1 ≤ Real.sqrt 2 :=
      deBruijnNewmanRiemannSiegelSqrtTwo_one_le
    linarith
  have hcoeff : 0 ≤ Real.sqrt 2 / 2 := by positivity
  have hqdiv : 0 < q / (2 * Real.pi) := div_pos hq (by positivity)
  have hqdivOne : q / (2 * Real.pi) < 1 :=
    (div_lt_one (by positivity : 0 < 2 * Real.pi)).mpr hq2pi
  have htriangle := abs_add_le
    ((Real.sqrt 2 / 2) * x - q / (2 * Real.pi)) (q / (2 * Real.pi))
  rw [show (Real.sqrt 2 / 2) * x - q / (2 * Real.pi) + q / (2 * Real.pi) =
      (Real.sqrt 2 / 2) * x by ring,
    abs_mul, abs_of_nonneg hcoeff, abs_of_pos hqdiv] at htriangle
  have hlarge : 3 ≤ (Real.sqrt 2 / 2) * |x| := by
    nlinarith [mul_le_mul hsqrt hx (by norm_num : (0 : ℝ) ≤ 6) hcoeff]
  have him : 1 ≤ |(Real.sqrt 2 / 2) * x - q / (2 * Real.pi)| := by
    linarith
  nlinarith [Real.pi_gt_three]

theorem abs_log_norm_deBruijnNewmanTitchmarshMellinWLine_le
    {c q : ℝ} (hc : 0 < c) (hcq : c ≤ q) (hq2pi : q < 2 * Real.pi)
    (x : ℝ) :
    |Real.log ‖deBruijnNewmanTitchmarshMellinWLine q x‖| ≤
      |x| + 1 + (c / (4 * Real.pi))⁻¹ := by
  let w := deBruijnNewmanTitchmarshMellinWLine q x
  let delta := c / (4 * Real.pi)
  have hq : 0 < q := hc.trans_le hcq
  have hdelta : 0 < delta := div_pos hc (by positivity)
  have hlower : delta ≤ ‖w‖ :=
    deBruijnNewmanTitchmarshMellinWLine_norm_lower hc hcq x
  have hnorm : 0 < ‖w‖ := hdelta.trans_le hlower
  have hupper : ‖w‖ ≤ |x| + 1 :=
    deBruijnNewmanTitchmarshMellinWLine_norm_upper hq hq2pi x
  have hinv : ‖w‖⁻¹ ≤ delta⁻¹ :=
    (inv_le_inv₀ hnorm hdelta).mpr hlower
  have hdeltaInv : 0 ≤ delta⁻¹ := (inv_pos.mpr hdelta).le
  change |Real.log ‖w‖| ≤ |x| + 1 + delta⁻¹
  rw [abs_le]
  constructor
  · have hlog := Real.neg_inv_le_log hnorm.le
    linarith
  · have hlog := Real.log_le_self hnorm.le
    linarith

theorem norm_cpow_deBruijnNewmanTitchmarshMellinWLine_le
    (s : ℂ) {c q : ℝ} (hc : 0 < c) (hcq : c ≤ q)
    (hq2pi : q < 2 * Real.pi) (x : ℝ) :
    ‖deBruijnNewmanTitchmarshMellinWLine q x ^ (s - 1)‖ ≤
      Real.exp
        (|(s - 1).re| * (|x| + 1 + (c / (4 * Real.pi))⁻¹) +
          |(s - 1).im| * Real.pi) := by
  let w := deBruijnNewmanTitchmarshMellinWLine q x
  have hwNorm : 0 < ‖w‖ := by
    exact (div_pos hc (by positivity : 0 < 4 * Real.pi)).trans_le
      (deBruijnNewmanTitchmarshMellinWLine_norm_lower hc hcq x)
  have hw : w ≠ 0 := norm_pos_iff.mp hwNorm
  rw [Complex.cpow_def_of_ne_zero hw, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hlog := abs_log_norm_deBruijnNewmanTitchmarshMellinWLine_le
    hc hcq hq2pi x
  have harg := Complex.abs_arg_le_pi w
  rw [Complex.mul_re, Complex.log_re, Complex.log_im]
  calc
    Real.log ‖w‖ * (s - 1).re - w.arg * (s - 1).im ≤
        |Real.log ‖w‖ * (s - 1).re| + |w.arg * (s - 1).im| :=
      add_le_add (le_abs_self _) (neg_le_abs _)
    _ = |(s - 1).re| * |Real.log ‖w‖| + |(s - 1).im| * |w.arg| := by
      rw [abs_mul, abs_mul]
      ring
    _ ≤ |(s - 1).re| * (|x| + 1 + (c / (4 * Real.pi))⁻¹) +
          |(s - 1).im| * Real.pi :=
      add_le_add (mul_le_mul_of_nonneg_left hlog (abs_nonneg _))
        (mul_le_mul_of_nonneg_left harg (abs_nonneg _))

theorem deBruijnNewmanTitchmarshMellinWLine_gaussianExponent_re
    (q x : ℝ) :
    (Complex.I * Real.pi *
        deBruijnNewmanTitchmarshMellinWLine q x ^ 2).re =
      -Real.pi * x ^ 2 + (Real.sqrt 2 / 2) * q * x := by
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, mul_zero, sub_zero,
    deBruijnNewmanTitchmarshMellinWLine_re,
    deBruijnNewmanTitchmarshMellinWLine_im]
  have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by positivity)
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring_nf at hsqrt ⊢
  rw [hsqrt]
  ring

theorem norm_exp_deBruijnNewmanTitchmarshMellinWLine_gaussian
    (q x : ℝ) :
    ‖Complex.exp (Complex.I * Real.pi *
        deBruijnNewmanTitchmarshMellinWLine q x ^ 2)‖ =
      Real.exp (-Real.pi * x ^ 2 + (Real.sqrt 2 / 2) * q * x) := by
  rw [Complex.norm_exp,
    deBruijnNewmanTitchmarshMellinWLine_gaussianExponent_re]

def deBruijnNewmanTitchmarshMellinWSideLinearRate (s : ℂ) (d : ℝ) : ℝ :=
  |(s - 1).re| + d

def deBruijnNewmanTitchmarshMellinWSideMajorantConstant
    (s : ℂ) (c d : ℝ) : ℝ :=
  |(s - 1).re| * (1 + (c / (4 * Real.pi))⁻¹) +
    |(s - 1).im| * Real.pi +
    deBruijnNewmanTitchmarshMellinWSideLinearRate s d ^ 2 / (2 * Real.pi)

def deBruijnNewmanTitchmarshMellinWSideMajorant
    (s : ℂ) (c d x : ℝ) : ℝ :=
  (1 / 2) *
    Real.exp (deBruijnNewmanTitchmarshMellinWSideMajorantConstant s c d) *
    Real.exp (-(Real.pi / 2) * x ^ 2)

theorem deBruijnNewmanTitchmarshMellinWSideLinearRate_mul_abs_le
    (s : ℂ) (d x : ℝ) :
    deBruijnNewmanTitchmarshMellinWSideLinearRate s d * |x| ≤
      Real.pi / 2 * x ^ 2 +
        deBruijnNewmanTitchmarshMellinWSideLinearRate s d ^ 2 /
          (2 * Real.pi) := by
  let C := deBruijnNewmanTitchmarshMellinWSideLinearRate s d
  have hpi : 0 < 2 * Real.pi := by positivity
  have hsq : 0 ≤ (Real.pi * |x| - C) ^ 2 := sq_nonneg _
  have hrewrite :
      Real.pi / 2 * x ^ 2 + C ^ 2 / (2 * Real.pi) =
        (Real.pi ^ 2 * x ^ 2 + C ^ 2) / (2 * Real.pi) := by
    field_simp
  change C * |x| ≤ _
  rw [hrewrite, le_div_iff₀ hpi]
  nlinarith [sq_abs x]

theorem deBruijnNewmanTitchmarshMellinWLine_gaussianLinear_le
    {q d : ℝ} (hq : 0 < q) (hqd : q ≤ d) (x : ℝ) :
    (Real.sqrt 2 / 2) * q * x ≤ d * |x| := by
  have hcoeff0 : 0 ≤ Real.sqrt 2 / 2 := by positivity
  have hcoeff1 : Real.sqrt 2 / 2 ≤ 1 := by
    linarith [deBruijnNewmanRiemannSiegelSqrtTwo_le_two]
  have hleft : (Real.sqrt 2 / 2) * q * x ≤
      (Real.sqrt 2 / 2) * q * |x| :=
    mul_le_mul_of_nonneg_left (le_abs_self x) (mul_nonneg hcoeff0 hq.le)
  have hcoeffq : (Real.sqrt 2 / 2) * q ≤ d := by
    calc
      (Real.sqrt 2 / 2) * q ≤ 1 * q :=
        mul_le_mul_of_nonneg_right hcoeff1 hq.le
      _ = q := one_mul q
      _ ≤ d := hqd
  exact hleft.trans (mul_le_mul_of_nonneg_right hcoeffq (abs_nonneg x))

theorem norm_deBruijnNewmanRiemannSiegelKernel_mellinWLine_le_premajorant
    (s : ℂ) {c q : ℝ} (hc : 0 < c) (hcq : c ≤ q)
    (hq2pi : q < 2 * Real.pi) {x : ℝ} (hx : 6 ≤ |x|) :
    ‖deBruijnNewmanRiemannSiegelKernel (1 - s)
        (deBruijnNewmanTitchmarshMellinWLine q x)‖ ≤
      (1 / 2) * Real.exp
        (|(s - 1).re| * (|x| + 1 + (c / (4 * Real.pi))⁻¹) +
          |(s - 1).im| * Real.pi +
          (-Real.pi * x ^ 2 + (Real.sqrt 2 / 2) * q * x)) := by
  let w := deBruijnNewmanTitchmarshMellinWLine q x
  have hq : 0 < q := hc.trans_le hcq
  have hpow := norm_cpow_deBruijnNewmanTitchmarshMellinWLine_le
    s hc hcq hq2pi x
  have hden := two_le_norm_deBruijnNewmanRiemannSiegelDenominator_mellinWLine
    hq hq2pi hx
  have hdenPos : 0 < ‖deBruijnNewmanRiemannSiegelDenominator w‖ :=
    lt_of_lt_of_le (by norm_num) hden
  have hexponent : -(1 - s) = s - 1 := by ring
  rw [deBruijnNewmanRiemannSiegelKernel,
    deBruijnNewmanRiemannSiegelNumerator, hexponent, norm_div, norm_mul,
    norm_exp_deBruijnNewmanTitchmarshMellinWLine_gaussian]
  calc
    ‖w ^ (s - 1)‖ *
          Real.exp (-Real.pi * x ^ 2 + (Real.sqrt 2 / 2) * q * x) /
        ‖deBruijnNewmanRiemannSiegelDenominator w‖ ≤
        (Real.exp
            (|(s - 1).re| * (|x| + 1 + (c / (4 * Real.pi))⁻¹) +
              |(s - 1).im| * Real.pi) *
          Real.exp (-Real.pi * x ^ 2 + (Real.sqrt 2 / 2) * q * x)) /
            ‖deBruijnNewmanRiemannSiegelDenominator w‖ := by
      apply div_le_div_of_nonneg_right
      · exact mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _)
      · exact hdenPos.le
    _ ≤ (Real.exp
            (|(s - 1).re| * (|x| + 1 + (c / (4 * Real.pi))⁻¹) +
              |(s - 1).im| * Real.pi) *
          Real.exp (-Real.pi * x ^ 2 + (Real.sqrt 2 / 2) * q * x)) / 2 := by
      exact div_le_div_of_nonneg_left
        (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)) (by norm_num) hden
    _ = (1 / 2) * Real.exp
        (|(s - 1).re| * (|x| + 1 + (c / (4 * Real.pi))⁻¹) +
          |(s - 1).im| * Real.pi +
          (-Real.pi * x ^ 2 + (Real.sqrt 2 / 2) * q * x)) := by
      conv_rhs => rw [Real.exp_add]
      ring

theorem norm_deBruijnNewmanRiemannSiegelKernel_mellinWLine_le_sideMajorant
    (s : ℂ) {c q d : ℝ} (hc : 0 < c) (hcq : c ≤ q) (hqd : q ≤ d)
    (hd2pi : d < 2 * Real.pi) {x : ℝ} (hx : 6 ≤ |x|) :
    ‖deBruijnNewmanRiemannSiegelKernel (1 - s)
        (deBruijnNewmanTitchmarshMellinWLine q x)‖ ≤
      deBruijnNewmanTitchmarshMellinWSideMajorant s c d x := by
  have hq2pi : q < 2 * Real.pi := hqd.trans_lt hd2pi
  have hpre :=
    norm_deBruijnNewmanRiemannSiegelKernel_mellinWLine_le_premajorant
      s hc hcq hq2pi hx
  have hq : 0 < q := hc.trans_le hcq
  have hqlinear :=
    deBruijnNewmanTitchmarshMellinWLine_gaussianLinear_le hq hqd x
  have hlinear :=
    deBruijnNewmanTitchmarshMellinWSideLinearRate_mul_abs_le s d x
  apply hpre.trans
  rw [deBruijnNewmanTitchmarshMellinWSideMajorant]
  conv_rhs => rw [mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
  simp only [deBruijnNewmanTitchmarshMellinWSideMajorantConstant,
    deBruijnNewmanTitchmarshMellinWSideLinearRate] at hlinear ⊢
  nlinarith

theorem hasDerivAt_deBruijnNewmanTitchmarshMellinWLine (c x : ℝ) :
    HasDerivAt (deBruijnNewmanTitchmarshMellinWLine c)
      deBruijnNewmanTitchmarshPhiDirection x := by
  have hscale : HasDerivAt
      (fun y : ℝ ↦ deBruijnNewmanTitchmarshPhiDirection * (y : ℂ))
      deBruijnNewmanTitchmarshPhiDirection x := by
    simpa only [id_eq, Complex.ofReal_one, mul_one] using
      (hasDerivAt_id x).ofReal_comp.const_mul
        deBruijnNewmanTitchmarshPhiDirection
  simpa only [deBruijnNewmanTitchmarshMellinWLine] using!
    hscale.sub_const
      (Complex.I * ((c / (2 * Real.pi) : ℝ) : ℂ))

/-- A finite segment of any parallel line in the Mellin band is evaluated by one primitive. -/
theorem intervalIntegral_deBruijnNewmanRiemannSiegelKernel_mellinWLine_eq_sub
    {s : ℂ} {G : ℂ → ℂ}
    (hG : ∀ w ∈ deBruijnNewmanTitchmarshMellinWBand,
      HasDerivAt G (deBruijnNewmanRiemannSiegelKernel (1 - s) w) w)
    {c : ℝ} (hc : 0 < c) (hc2pi : c < 2 * Real.pi) (a b : ℝ) :
    (∫ x in a..b,
        deBruijnNewmanRiemannSiegelKernel (1 - s)
            (deBruijnNewmanTitchmarshMellinWLine c x) *
          deBruijnNewmanTitchmarshPhiDirection) =
      G (deBruijnNewmanTitchmarshMellinWLine c b) -
        G (deBruijnNewmanTitchmarshMellinWLine c a) := by
  have hderiv : ∀ x : ℝ, HasDerivAt
      (fun y : ℝ ↦ G (deBruijnNewmanTitchmarshMellinWLine c y))
      (deBruijnNewmanRiemannSiegelKernel (1 - s)
          (deBruijnNewmanTitchmarshMellinWLine c x) *
        deBruijnNewmanTitchmarshPhiDirection) x := by
    intro x
    have hcomp :=
      (hG _ (deBruijnNewmanTitchmarshMellinWLine_mem_band hc hc2pi x)).scomp x
        (hasDerivAt_deBruijnNewmanTitchmarshMellinWLine c x)
    simpa only [Function.comp_apply, smul_eq_mul, mul_comm] using! hcomp
  have hcont : Continuous
      (fun x : ℝ ↦
        deBruijnNewmanRiemannSiegelKernel (1 - s)
            (deBruijnNewmanTitchmarshMellinWLine c x) *
          deBruijnNewmanTitchmarshPhiDirection) := by
    rw [continuous_iff_continuousAt]
    intro x
    apply ContinuousAt.mul ?_ continuousAt_const
    exact ((differentiableOn_deBruijnNewmanRiemannSiegelKernel_mellinWBand s _
      (deBruijnNewmanTitchmarshMellinWLine_mem_band hc hc2pi x)).differentiableAt
        (isOpen_deBruijnNewmanTitchmarshMellinWBand.mem_nhds
          (deBruijnNewmanTitchmarshMellinWLine_mem_band hc hc2pi x))).continuousAt.comp
            (hasDerivAt_deBruijnNewmanTitchmarshMellinWLine c x).continuousAt
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ ↦ hderiv x) (hcont.intervalIntegrable a b)

theorem hasDerivAt_deBruijnNewmanTitchmarshMellinWLine_left (c x : ℝ) :
    HasDerivAt (fun q : ℝ ↦ deBruijnNewmanTitchmarshMellinWLine q x)
      (-Complex.I * ((((2 * Real.pi)⁻¹ : ℝ)) : ℂ)) c := by
  have hdivReal : HasDerivAt (fun q : ℝ ↦ q / (2 * Real.pi))
      (1 / (2 * Real.pi)) c :=
    (hasDerivAt_id c).div_const (2 * Real.pi)
  have hdivComplex : HasDerivAt
      (fun q : ℝ ↦ ((q / (2 * Real.pi) : ℝ) : ℂ))
      (((1 / (2 * Real.pi) : ℝ) : ℂ)) c := by
    simpa only [Function.comp_apply] using hdivReal.ofReal_comp
  have himul := hdivComplex.const_mul Complex.I
  have hconst : HasDerivAt
      (fun _q : ℝ ↦ deBruijnNewmanTitchmarshPhiDirection * (x : ℂ)) 0 c :=
    hasDerivAt_const c _
  have h := hconst.sub himul
  have hcoeff :
      0 - Complex.I * (((1 / (2 * Real.pi) : ℝ) : ℂ)) =
        -Complex.I * ((((2 * Real.pi)⁻¹ : ℝ)) : ℂ) := by
    rw [one_div]
    ring
  rw [hcoeff] at h
  simpa only [deBruijnNewmanTitchmarshMellinWLine, Pi.sub_apply] using! h

/-- A finite transverse segment in the Mellin band is evaluated by the same primitive. -/
theorem intervalIntegral_deBruijnNewmanRiemannSiegelKernel_mellinWLine_left_eq_sub
    {s : ℂ} {G : ℂ → ℂ}
    (hG : ∀ w ∈ deBruijnNewmanTitchmarshMellinWBand,
      HasDerivAt G (deBruijnNewmanRiemannSiegelKernel (1 - s) w) w)
    {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) (hd2pi : d < 2 * Real.pi) (x : ℝ) :
    (∫ q in c..d,
        deBruijnNewmanRiemannSiegelKernel (1 - s)
            (deBruijnNewmanTitchmarshMellinWLine q x) *
          (-Complex.I * ((((2 * Real.pi)⁻¹ : ℝ)) : ℂ))) =
      G (deBruijnNewmanTitchmarshMellinWLine d x) -
        G (deBruijnNewmanTitchmarshMellinWLine c x) := by
  have hqBounds {q : ℝ} (hq : q ∈ Set.uIcc c d) :
      0 < q ∧ q < 2 * Real.pi := by
    rw [uIcc_of_le hcd] at hq
    exact ⟨hc.trans_le hq.1, hq.2.trans_lt hd2pi⟩
  have hderiv : ∀ q ∈ Set.uIcc c d, HasDerivAt
      (fun r : ℝ ↦ G (deBruijnNewmanTitchmarshMellinWLine r x))
      (deBruijnNewmanRiemannSiegelKernel (1 - s)
          (deBruijnNewmanTitchmarshMellinWLine q x) *
        (-Complex.I * ((((2 * Real.pi)⁻¹ : ℝ)) : ℂ))) q := by
    intro q hq
    obtain ⟨hq0, hq2pi⟩ := hqBounds hq
    have hcomp :=
      (hG _ (deBruijnNewmanTitchmarshMellinWLine_mem_band hq0 hq2pi x)).scomp q
        (hasDerivAt_deBruijnNewmanTitchmarshMellinWLine_left q x)
    simpa only [Function.comp_apply, smul_eq_mul, mul_comm] using! hcomp
  have hcont : ContinuousOn
      (fun q : ℝ ↦
        deBruijnNewmanRiemannSiegelKernel (1 - s)
            (deBruijnNewmanTitchmarshMellinWLine q x) *
          (-Complex.I * ((((2 * Real.pi)⁻¹ : ℝ)) : ℂ))) (Set.Icc c d) := by
    intro q hq
    have hqu : q ∈ Set.uIcc c d := by simpa [uIcc_of_le hcd] using hq
    obtain ⟨hq0, hq2pi⟩ := hqBounds hqu
    apply (ContinuousAt.mul ?_ continuousAt_const).continuousWithinAt
    exact ((differentiableOn_deBruijnNewmanRiemannSiegelKernel_mellinWBand s _
      (deBruijnNewmanTitchmarshMellinWLine_mem_band hq0 hq2pi x)).differentiableAt
        (isOpen_deBruijnNewmanTitchmarshMellinWBand.mem_nhds
          (deBruijnNewmanTitchmarshMellinWLine_mem_band hq0 hq2pi x))).continuousAt.comp_of_eq
            (hasDerivAt_deBruijnNewmanTitchmarshMellinWLine_left q x).continuousAt rfl
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    hderiv (hcont.intervalIntegrable_of_Icc hcd)

/-- Exact finite pole-free deformation between two transformed Titchmarsh lines. -/
theorem deBruijnNewmanRiemannSiegelKernel_mellinWLine_finite_shift
    (s : ℂ) {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d)
    (hd2pi : d < 2 * Real.pi) (R : ℝ) :
    (∫ x in -R..R,
        deBruijnNewmanRiemannSiegelKernel (1 - s)
            (deBruijnNewmanTitchmarshMellinWLine d x) *
          deBruijnNewmanTitchmarshPhiDirection) -
      (∫ x in -R..R,
        deBruijnNewmanRiemannSiegelKernel (1 - s)
            (deBruijnNewmanTitchmarshMellinWLine c x) *
          deBruijnNewmanTitchmarshPhiDirection) =
      (∫ q in c..d,
        deBruijnNewmanRiemannSiegelKernel (1 - s)
            (deBruijnNewmanTitchmarshMellinWLine q R) *
          (-Complex.I * ((((2 * Real.pi)⁻¹ : ℝ)) : ℂ))) -
      (∫ q in c..d,
        deBruijnNewmanRiemannSiegelKernel (1 - s)
            (deBruijnNewmanTitchmarshMellinWLine q (-R)) *
          (-Complex.I * ((((2 * Real.pi)⁻¹ : ℝ)) : ℂ))) := by
  obtain ⟨G, hG⟩ :=
    exists_deBruijnNewmanRiemannSiegelKernel_mellinWBand_primitive s
  have hd : 0 < d := hc.trans_le hcd
  have hc2pi : c < 2 * Real.pi := lt_of_le_of_lt hcd hd2pi
  rw [intervalIntegral_deBruijnNewmanRiemannSiegelKernel_mellinWLine_eq_sub
      hG hd hd2pi,
    intervalIntegral_deBruijnNewmanRiemannSiegelKernel_mellinWLine_eq_sub
      hG hc hc2pi,
    intervalIntegral_deBruijnNewmanRiemannSiegelKernel_mellinWLine_left_eq_sub
      hG hc hcd hd2pi,
    intervalIntegral_deBruijnNewmanRiemannSiegelKernel_mellinWLine_left_eq_sub
      hG hc hcd hd2pi]
  ring

/-- The transverse short side at horizontal parameter `x`. -/
def deBruijnNewmanRiemannSiegelKernelMellinWEndIntegral
    (s : ℂ) (c d x : ℝ) : ℂ :=
  ∫ q in c..d,
    deBruijnNewmanRiemannSiegelKernel (1 - s)
        (deBruijnNewmanTitchmarshMellinWLine q x) *
      (-Complex.I * ((((2 * Real.pi)⁻¹ : ℝ)) : ℂ))

theorem norm_deBruijnNewmanRiemannSiegelKernelMellinWEndIntegral_le
    (s : ℂ) {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d)
    (hd2pi : d < 2 * Real.pi) {x : ℝ} (hx : 6 ≤ |x|) :
    ‖deBruijnNewmanRiemannSiegelKernelMellinWEndIntegral s c d x‖ ≤
      deBruijnNewmanTitchmarshMellinWSideMajorant s c d x *
        ‖-Complex.I * ((((2 * Real.pi)⁻¹ : ℝ)) : ℂ)‖ * |d - c| := by
  unfold deBruijnNewmanRiemannSiegelKernelMellinWEndIntegral
  calc
    ‖∫ q in c..d,
        deBruijnNewmanRiemannSiegelKernel (1 - s)
            (deBruijnNewmanTitchmarshMellinWLine q x) *
          (-Complex.I * ((((2 * Real.pi)⁻¹ : ℝ)) : ℂ))‖ ≤
        (deBruijnNewmanTitchmarshMellinWSideMajorant s c d x *
          ‖-Complex.I * ((((2 * Real.pi)⁻¹ : ℝ)) : ℂ)‖) * |d - c| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro q hq
      have hqu := uIoc_subset_uIcc hq
      rw [uIcc_of_le hcd] at hqu
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (norm_deBruijnNewmanRiemannSiegelKernel_mellinWLine_le_sideMajorant
          s hc hqu.1 hqu.2 hd2pi hx) (norm_nonneg _)
    _ = _ := by ring

theorem tendsto_deBruijnNewmanTitchmarshMellinWSideMajorant
    (s : ℂ) (c d : ℝ) :
    Tendsto (deBruijnNewmanTitchmarshMellinWSideMajorant s c d)
      atTop (nhds 0) := by
  rw [show deBruijnNewmanTitchmarshMellinWSideMajorant s c d =
      fun x : ℝ ↦
        ((1 / 2) *
          Real.exp (deBruijnNewmanTitchmarshMellinWSideMajorantConstant s c d)) *
          Real.exp (-(Real.pi / 2) * x ^ 2) by
    funext x
    rfl]
  have hsq : Tendsto (fun x : ℝ ↦ x ^ 2) atTop atTop := by
    simp only [pow_two]
    exact tendsto_id.atTop_mul_atTop₀ tendsto_id
  have hcoef : -(Real.pi / 2) < 0 :=
    neg_lt_zero.mpr (div_pos Real.pi_pos (by norm_num))
  have hneg : Tendsto (fun x : ℝ ↦ -(Real.pi / 2) * x ^ 2) atTop atBot :=
    hsq.const_mul_atTop_of_neg hcoef
  simpa only [Function.comp_apply, mul_zero] using
    (Real.tendsto_exp_atBot.comp hneg).const_mul
      ((1 / 2) *
        Real.exp (deBruijnNewmanTitchmarshMellinWSideMajorantConstant s c d))

theorem tendsto_deBruijnNewmanTitchmarshMellinWSideMajorant_neg
    (s : ℂ) (c d : ℝ) :
    Tendsto (fun x : ℝ ↦
      deBruijnNewmanTitchmarshMellinWSideMajorant s c d (-x))
      atTop (nhds 0) := by
  have hlim := tendsto_deBruijnNewmanTitchmarshMellinWSideMajorant s c d
  apply hlim.congr'
  exact Filter.Eventually.of_forall fun x ↦ by
    change deBruijnNewmanTitchmarshMellinWSideMajorant s c d x =
      deBruijnNewmanTitchmarshMellinWSideMajorant s c d (-x)
    unfold deBruijnNewmanTitchmarshMellinWSideMajorant
    rw [show (-x) ^ 2 = x ^ 2 by ring]

theorem tendsto_deBruijnNewmanRiemannSiegelKernelMellinWEndIntegral
    (s : ℂ) {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d)
    (hd2pi : d < 2 * Real.pi) :
    Tendsto (deBruijnNewmanRiemannSiegelKernelMellinWEndIntegral s c d)
      atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero'
    (g := fun x : ℝ ↦
      deBruijnNewmanTitchmarshMellinWSideMajorant s c d x *
        ‖-Complex.I * ((((2 * Real.pi)⁻¹ : ℝ)) : ℂ)‖ * |d - c|) ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun _ ↦ norm_nonneg _
  · filter_upwards [eventually_ge_atTop 6] with x hx
    exact norm_deBruijnNewmanRiemannSiegelKernelMellinWEndIntegral_le
      s hc hcd hd2pi (by simpa [abs_of_nonneg (by linarith : 0 ≤ x)] using hx)
  · simpa only [zero_mul] using
      ((tendsto_deBruijnNewmanTitchmarshMellinWSideMajorant s c d).mul_const
        ‖-Complex.I * ((((2 * Real.pi)⁻¹ : ℝ)) : ℂ)‖).mul_const |d - c|

theorem tendsto_deBruijnNewmanRiemannSiegelKernelMellinWEndIntegral_neg
    (s : ℂ) {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d)
    (hd2pi : d < 2 * Real.pi) :
    Tendsto (fun x : ℝ ↦
      deBruijnNewmanRiemannSiegelKernelMellinWEndIntegral s c d (-x))
      atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero'
    (g := fun x : ℝ ↦
      deBruijnNewmanTitchmarshMellinWSideMajorant s c d (-x) *
        ‖-Complex.I * ((((2 * Real.pi)⁻¹ : ℝ)) : ℂ)‖ * |d - c|) ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun _ ↦ norm_nonneg _
  · filter_upwards [eventually_ge_atTop 6] with x hx
    exact norm_deBruijnNewmanRiemannSiegelKernelMellinWEndIntegral_le
      s hc hcd hd2pi (by simpa only [abs_neg] using
        (show 6 ≤ |x| by simpa [abs_of_nonneg (by linarith : 0 ≤ x)] using hx))
  · simpa only [zero_mul] using
      ((tendsto_deBruijnNewmanTitchmarshMellinWSideMajorant_neg s c d).mul_const
        ‖-Complex.I * ((((2 * Real.pi)⁻¹ : ℝ)) : ℂ)‖).mul_const |d - c|

/-- The Riemann--Siegel kernel with the Jacobian of a transformed Titchmarsh line. -/
def deBruijnNewmanRiemannSiegelKernelMellinWLineIntegrand
    (s : ℂ) (c x : ℝ) : ℂ :=
  deBruijnNewmanRiemannSiegelKernel (1 - s)
      (deBruijnNewmanTitchmarshMellinWLine c x) *
    deBruijnNewmanTitchmarshPhiDirection

def deBruijnNewmanRiemannSiegelKernelMellinWLineIntegral
    (s : ℂ) (c : ℝ) : ℂ :=
  ∫ x : ℝ, deBruijnNewmanRiemannSiegelKernelMellinWLineIntegrand s c x

theorem continuous_deBruijnNewmanRiemannSiegelKernelMellinWLineIntegrand
    (s : ℂ) {c : ℝ} (hc : 0 < c) (hc2pi : c < 2 * Real.pi) :
    Continuous (deBruijnNewmanRiemannSiegelKernelMellinWLineIntegrand s c) := by
  rw [continuous_iff_continuousAt]
  intro x
  unfold deBruijnNewmanRiemannSiegelKernelMellinWLineIntegrand
  apply ContinuousAt.mul ?_ continuousAt_const
  exact ((differentiableOn_deBruijnNewmanRiemannSiegelKernel_mellinWBand s _
    (deBruijnNewmanTitchmarshMellinWLine_mem_band hc hc2pi x)).differentiableAt
      (isOpen_deBruijnNewmanTitchmarshMellinWBand.mem_nhds
        (deBruijnNewmanTitchmarshMellinWLine_mem_band hc hc2pi x))).continuousAt.comp
          (hasDerivAt_deBruijnNewmanTitchmarshMellinWLine c x).continuousAt

theorem integrable_deBruijnNewmanTitchmarshMellinWSideMajorant
    (s : ℂ) (c d : ℝ) :
    Integrable (deBruijnNewmanTitchmarshMellinWSideMajorant s c d) := by
  have hgauss : Integrable (fun x : ℝ ↦
      Real.exp (-(Real.pi / 2) * x ^ 2)) :=
    integrable_exp_neg_mul_sq (by positivity)
  change Integrable (fun x : ℝ ↦
    ((1 / 2) *
      Real.exp (deBruijnNewmanTitchmarshMellinWSideMajorantConstant s c d)) *
      Real.exp (-(Real.pi / 2) * x ^ 2))
  exact hgauss.const_mul
    ((1 / 2) *
      Real.exp (deBruijnNewmanTitchmarshMellinWSideMajorantConstant s c d))

theorem integrable_deBruijnNewmanRiemannSiegelKernelMellinWLineIntegrand
    (s : ℂ) {c : ℝ} (hc : 0 < c) (hc2pi : c < 2 * Real.pi) :
    Integrable (deBruijnNewmanRiemannSiegelKernelMellinWLineIntegrand s c) := by
  let f := deBruijnNewmanRiemannSiegelKernelMellinWLineIntegrand s c
  let M := deBruijnNewmanTitchmarshMellinWSideMajorant s c c
  have hfcont : Continuous f :=
    continuous_deBruijnNewmanRiemannSiegelKernelMellinWLineIntegrand s hc hc2pi
  have hlocalOn : IntegrableOn (fun x : ℝ ↦ ‖f x‖) (Set.Icc (-6) 6) :=
    hfcont.norm.integrableOn_Icc
  have hlocal : Integrable (fun x : ℝ ↦
      (Set.Icc (-6) 6).indicator (fun y ↦ ‖f y‖) x) :=
    hlocalOn.integrable_indicator measurableSet_Icc
  have hmajor : Integrable (fun x : ℝ ↦
      M x + (Set.Icc (-6) 6).indicator (fun y ↦ ‖f y‖) x) :=
    (integrable_deBruijnNewmanTitchmarshMellinWSideMajorant s c c).add hlocal
  refine Integrable.mono' hmajor hfcont.aestronglyMeasurable ?_
  exact ae_of_all _ fun x ↦ by
    by_cases hxmem : x ∈ Set.Icc (-6) 6
    · rw [Set.indicator_of_mem hxmem]
      have hM : 0 ≤ M x := by
        unfold M deBruijnNewmanTitchmarshMellinWSideMajorant
        positivity
      exact le_add_of_nonneg_left hM
    · rw [Set.indicator_of_notMem hxmem, add_zero]
      have hx : 6 ≤ |x| := by
        by_contra hnot
        have habs : |x| < 6 := lt_of_not_ge hnot
        apply hxmem
        constructor
        · linarith [neg_abs_le x]
        · linarith [le_abs_self x]
      have hkernel :=
        norm_deBruijnNewmanRiemannSiegelKernel_mellinWLine_le_sideMajorant
          s hc le_rfl le_rfl hc2pi hx
      simpa only [f, M, deBruijnNewmanRiemannSiegelKernelMellinWLineIntegrand,
        norm_mul, norm_deBruijnNewmanTitchmarshPhiDirection, mul_one] using hkernel

theorem tendsto_deBruijnNewmanRiemannSiegelKernelMellinWLine_symmetricIntegral
    (s : ℂ) {c : ℝ} (hc : 0 < c) (hc2pi : c < 2 * Real.pi) :
    Tendsto (fun T : ℝ ↦
      ∫ x in -T..T,
        deBruijnNewmanRiemannSiegelKernelMellinWLineIntegrand s c x)
      atTop (nhds (deBruijnNewmanRiemannSiegelKernelMellinWLineIntegral s c)) := by
  have hlim := intervalIntegral_tendsto_integral
    (integrable_deBruijnNewmanRiemannSiegelKernelMellinWLineIntegrand
      s hc hc2pi) tendsto_neg_atTop_atBot tendsto_id
  simpa only [deBruijnNewmanRiemannSiegelKernelMellinWLineIntegral, id_eq] using hlim

/-- Pole-free infinite contour deformation inside the Mellin band. -/
theorem deBruijnNewmanRiemannSiegelKernelMellinWLineIntegral_eq
    (s : ℂ) {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d)
    (hd2pi : d < 2 * Real.pi) :
    deBruijnNewmanRiemannSiegelKernelMellinWLineIntegral s d =
      deBruijnNewmanRiemannSiegelKernelMellinWLineIntegral s c := by
  let F : ℝ → ℂ := fun T ↦
    (∫ x in -T..T,
        deBruijnNewmanRiemannSiegelKernelMellinWLineIntegrand s d x) -
      (∫ x in -T..T,
        deBruijnNewmanRiemannSiegelKernelMellinWLineIntegrand s c x) -
      deBruijnNewmanRiemannSiegelKernelMellinWEndIntegral s c d T +
      deBruijnNewmanRiemannSiegelKernelMellinWEndIntegral s c d (-T)
  have hd : 0 < d := hc.trans_le hcd
  have hc2pi : c < 2 * Real.pi := hcd.trans_lt hd2pi
  have hlimit : Tendsto F atTop
      (nhds (deBruijnNewmanRiemannSiegelKernelMellinWLineIntegral s d -
        deBruijnNewmanRiemannSiegelKernelMellinWLineIntegral s c - 0 + 0)) := by
    exact (((tendsto_deBruijnNewmanRiemannSiegelKernelMellinWLine_symmetricIntegral
      s hd hd2pi).sub
        (tendsto_deBruijnNewmanRiemannSiegelKernelMellinWLine_symmetricIntegral
          s hc hc2pi)).sub
            (tendsto_deBruijnNewmanRiemannSiegelKernelMellinWEndIntegral
              s hc hcd hd2pi)).add
                (tendsto_deBruijnNewmanRiemannSiegelKernelMellinWEndIntegral_neg
                  s hc hcd hd2pi)
  have hfinite : ∀ T : ℝ, F T = 0 := by
    intro T
    have hshift := deBruijnNewmanRiemannSiegelKernel_mellinWLine_finite_shift
      s hc hcd hd2pi T
    unfold F deBruijnNewmanRiemannSiegelKernelMellinWLineIntegrand
      deBruijnNewmanRiemannSiegelKernelMellinWEndIntegral
    linear_combination hshift
  have hconstant : Tendsto F atTop (nhds 0) := by
    apply tendsto_const_nhds.congr'
    exact Filter.Eventually.of_forall fun T ↦ (hfinite T).symm
  have heq := tendsto_nhds_unique hlimit hconstant
  linear_combination heq

theorem deBruijnNewmanTitchmarshPhiDirection_eq_neg_riemannSiegelDirection :
    deBruijnNewmanTitchmarshPhiDirection =
      -deBruijnNewmanRiemannSiegelDirection := by
  apply Complex.ext
  · simp
  · simp

/-- The central transformed line is the oppositely parameterized `N = 0`
Riemann--Siegel line. -/
theorem deBruijnNewmanTitchmarshMellinWLine_pi_eq_riemannSiegelLine
    (x : ℝ) :
    deBruijnNewmanTitchmarshMellinWLine Real.pi x =
      deBruijnNewmanRiemannSiegelLine 0 (Real.sqrt 2 / 2 - x) := by
  apply Complex.ext
  · simp only [deBruijnNewmanTitchmarshMellinWLine_re,
      deBruijnNewmanRiemannSiegelLine_re, Nat.cast_zero, zero_add]
    have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by positivity)
    field_simp
    nlinarith
  · simp only [deBruijnNewmanTitchmarshMellinWLine_im,
      deBruijnNewmanRiemannSiegelLine_im, Nat.cast_zero, zero_add]
    have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by positivity)
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    nlinarith

theorem deBruijnNewmanRiemannSiegelKernelMellinWLineIntegrand_pi
    (s : ℂ) (x : ℝ) :
    deBruijnNewmanRiemannSiegelKernelMellinWLineIntegrand s Real.pi x =
      -deBruijnNewmanRiemannSiegelLineIntegrand 0 (1 - s)
        (Real.sqrt 2 / 2 - x) := by
  unfold deBruijnNewmanRiemannSiegelKernelMellinWLineIntegrand
  unfold deBruijnNewmanRiemannSiegelLineIntegrand
  rw [deBruijnNewmanTitchmarshMellinWLine_pi_eq_riemannSiegelLine,
    deBruijnNewmanTitchmarshPhiDirection_eq_neg_riemannSiegelDirection]
  ring

theorem integral_comp_deBruijnNewmanRiemannSiegel_reflect
    (f : ℝ → ℂ) (a : ℝ) :
    (∫ x : ℝ, f (a - x)) = ∫ x : ℝ, f x := by
  calc
    (∫ x : ℝ, f (a - x)) = ∫ x : ℝ, (fun y ↦ f (a + y)) (-x) := by
      rfl
    _ = ∫ x : ℝ, f (a + x) :=
      integral_neg_eq_self (fun y : ℝ ↦ f (a + y)) volume
    _ = ∫ x : ℝ, f x := integral_add_left_eq_self f a

/-- Exact `c = pi` endpoint of the pole-free Mellin deformation. -/
theorem deBruijnNewmanRiemannSiegelKernelMellinWLineIntegral_pi
    (s : ℂ) :
    deBruijnNewmanRiemannSiegelKernelMellinWLineIntegral s Real.pi =
      -deBruijnNewmanRiemannSiegelRawIntegral 0 (1 - s) := by
  unfold deBruijnNewmanRiemannSiegelKernelMellinWLineIntegral
  rw [show (∫ x : ℝ,
      deBruijnNewmanRiemannSiegelKernelMellinWLineIntegrand s Real.pi x) =
      ∫ x : ℝ,
        -deBruijnNewmanRiemannSiegelLineIntegrand 0 (1 - s)
          (Real.sqrt 2 / 2 - x) by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x ↦
      deBruijnNewmanRiemannSiegelKernelMellinWLineIntegrand_pi s x]
  rw [integral_neg,
    integral_comp_deBruijnNewmanRiemannSiegel_reflect
      (deBruijnNewmanRiemannSiegelLineIntegrand 0 (1 - s)) (Real.sqrt 2 / 2)]
  rfl

/-- The zero-filled kernel used to take the `c ↓0+` boundary limit. For `Re s > 2`, the
factor `w^(s-2)` removes the denominator's simple zero at the origin continuously. -/
def deBruijnNewmanRiemannSiegelMellinWKernelExtension (s w : ℂ) : ℂ :=
  w ^ (s - 2) * Complex.exp (Complex.I * Real.pi * w ^ 2) /
    dslope deBruijnNewmanRiemannSiegelDenominator 0 w

theorem dslope_deBruijnNewmanRiemannSiegelDenominator_zero :
    dslope deBruijnNewmanRiemannSiegelDenominator 0 0 =
      2 * (Real.pi : ℂ) * Complex.I := by
  rw [dslope_same]
  simpa using deriv_deBruijnNewmanRiemannSiegelDenominator_natCast 0

theorem dslope_deBruijnNewmanRiemannSiegelDenominator_ne_zero_at_zero :
    dslope deBruijnNewmanRiemannSiegelDenominator 0 0 ≠ 0 := by
  rw [dslope_deBruijnNewmanRiemannSiegelDenominator_zero]
  exact mul_ne_zero
    (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    Complex.I_ne_zero

theorem continuousAt_deBruijnNewmanRiemannSiegelMellinWKernelExtension_zero
    {s : ℂ} (hs : 2 < s.re) :
    ContinuousAt (deBruijnNewmanRiemannSiegelMellinWKernelExtension s) 0 := by
  have hpow : ContinuousAt (fun w : ℂ ↦ w ^ (s - 2)) 0 := by
    apply Complex.continuousAt_cpow_const_of_re_pos
    · exact Or.inl (by norm_num)
    · change 0 < s.re - 2
      linarith
  have hexp : ContinuousAt
      (fun w : ℂ ↦ Complex.exp (Complex.I * Real.pi * w ^ 2)) 0 := by
    fun_prop
  have hdslope : ContinuousAt
      (dslope deBruijnNewmanRiemannSiegelDenominator 0) 0 :=
    continuousAt_dslope_same.mpr
      (hasDerivAt_deBruijnNewmanRiemannSiegelDenominator 0).differentiableAt
  exact (hpow.mul hexp).div hdslope
    dslope_deBruijnNewmanRiemannSiegelDenominator_ne_zero_at_zero

theorem continuousAt_deBruijnNewmanRiemannSiegelMellinWKernelExtension_of_ne
    (s : ℂ) {w : ℂ} (hw : w ≠ 0) (hwSlit : w ∈ Complex.slitPlane)
    (hden : deBruijnNewmanRiemannSiegelDenominator w ≠ 0) :
    ContinuousAt (deBruijnNewmanRiemannSiegelMellinWKernelExtension s) w := by
  have hpow : ContinuousAt (fun z : ℂ ↦ z ^ (s - 2)) w :=
    continuousAt_cpow_const hwSlit
  have hexp : ContinuousAt
      (fun z : ℂ ↦ Complex.exp (Complex.I * Real.pi * z ^ 2)) w := by
    fun_prop
  have hdslope : ContinuousAt
      (dslope deBruijnNewmanRiemannSiegelDenominator 0) w :=
    (continuousAt_dslope_of_ne hw).mpr
      (hasDerivAt_deBruijnNewmanRiemannSiegelDenominator w).continuousAt
  have hrelation := sub_smul_dslope
    deBruijnNewmanRiemannSiegelDenominator 0 w
  have hD0 : deBruijnNewmanRiemannSiegelDenominator 0 = 0 := by
    simpa using deBruijnNewmanRiemannSiegelDenominator_natCast 0
  simp only [sub_zero, smul_eq_mul] at hrelation
  rw [hD0, sub_zero] at hrelation
  have hdslopeNe : dslope deBruijnNewmanRiemannSiegelDenominator 0 w ≠ 0 := by
    intro hzero
    apply hden
    rw [← hrelation, hzero, mul_zero]
  exact (hpow.mul hexp).div hdslope hdslopeNe

theorem deBruijnNewmanRiemannSiegelMellinWKernelExtension_eq_kernel
    (s : ℂ) {w : ℂ} (hw : w ≠ 0)
    (hden : deBruijnNewmanRiemannSiegelDenominator w ≠ 0) :
    deBruijnNewmanRiemannSiegelMellinWKernelExtension s w =
      deBruijnNewmanRiemannSiegelKernel (1 - s) w := by
  have hrelation := sub_smul_dslope
    deBruijnNewmanRiemannSiegelDenominator 0 w
  have hD0 : deBruijnNewmanRiemannSiegelDenominator 0 = 0 := by
    simpa using deBruijnNewmanRiemannSiegelDenominator_natCast 0
  simp only [sub_zero, smul_eq_mul] at hrelation
  rw [hD0, sub_zero] at hrelation
  have hdslopeNe : dslope deBruijnNewmanRiemannSiegelDenominator 0 w ≠ 0 := by
    intro hzero
    apply hden
    rw [← hrelation, hzero, mul_zero]
  have hpow : w ^ (s - 2) * w = w ^ (s - 1) := by
    calc
      w ^ (s - 2) * w = w ^ (s - 2) * w ^ (1 : ℂ) := by
        rw [Complex.cpow_one]
      _ = w ^ ((s - 2) + 1) := by rw [Complex.cpow_add _ _ hw]
      _ = w ^ (s - 1) := by ring_nf
  unfold deBruijnNewmanRiemannSiegelMellinWKernelExtension
  unfold deBruijnNewmanRiemannSiegelKernel
  unfold deBruijnNewmanRiemannSiegelNumerator
  have hexponent : -(1 - s) = s - 1 := by ring
  rw [hexponent, ← hrelation]
  field_simp [hw, hdslopeNe]
  rw [hpow]

theorem deBruijnNewmanTitchmarshMellinWLine_eq_zero_iff (q x : ℝ) :
    deBruijnNewmanTitchmarshMellinWLine q x = 0 ↔ q = 0 ∧ x = 0 := by
  constructor
  · intro hzero
    have hre := congrArg Complex.re hzero
    have him := congrArg Complex.im hzero
    simp only [deBruijnNewmanTitchmarshMellinWLine_re, Complex.zero_re] at hre
    simp only [deBruijnNewmanTitchmarshMellinWLine_im, Complex.zero_im] at him
    have hsqrt : Real.sqrt 2 / 2 ≠ 0 := by positivity
    have hx : x = 0 := (mul_eq_zero.mp hre).resolve_left hsqrt
    subst x
    have hqdiv : q / (2 * Real.pi) = 0 := by linarith
    have hden : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    exact ⟨(div_eq_zero_iff.mp hqdiv).resolve_right hden, rfl⟩
  · rintro ⟨rfl, rfl⟩
    simp [deBruijnNewmanTitchmarshMellinWLine]

theorem deBruijnNewmanTitchmarshMellinWLine_mem_slitPlane_of_nonnegative
    {q x : ℝ} (hq : 0 ≤ q)
    (hw : deBruijnNewmanTitchmarshMellinWLine q x ≠ 0) :
    deBruijnNewmanTitchmarshMellinWLine q x ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases him : (deBruijnNewmanTitchmarshMellinWLine q x).im = 0
  · left
    have him' : (Real.sqrt 2 / 2) * x - q / (2 * Real.pi) = 0 := by
      simpa only [deBruijnNewmanTitchmarshMellinWLine_im] using him
    have hqne : q ≠ 0 := by
      intro hqzero
      apply hw
      rw [deBruijnNewmanTitchmarshMellinWLine_eq_zero_iff]
      refine ⟨hqzero, ?_⟩
      rw [hqzero, zero_div, sub_zero] at him'
      exact (mul_eq_zero.mp him').resolve_left (by positivity)
    have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hqne)
    rw [deBruijnNewmanTitchmarshMellinWLine_re]
    have hqdiv : 0 < q / (2 * Real.pi) := div_pos hqpos (by positivity)
    linarith
  · exact Or.inr him

theorem deBruijnNewmanTitchmarshMellinWLine_denominator_ne_zero_of_nonnegative
    {q x : ℝ} (hq : 0 ≤ q) (hq2pi : q < 2 * Real.pi)
    (hw : deBruijnNewmanTitchmarshMellinWLine q x ≠ 0) :
    deBruijnNewmanRiemannSiegelDenominator
        (deBruijnNewmanTitchmarshMellinWLine q x) ≠ 0 := by
  by_cases hqzero : q = 0
  · intro hzero
    obtain ⟨n, hn⟩ :=
      exists_int_of_deBruijnNewmanRiemannSiegelDenominator_eq_zero hzero
    have him := congrArg Complex.im hn
    simp only [deBruijnNewmanTitchmarshMellinWLine_im, hqzero, zero_div,
      sub_zero, Complex.intCast_im] at him
    have hx : x = 0 := (mul_eq_zero.mp him).resolve_left (by positivity)
    exact hw ((deBruijnNewmanTitchmarshMellinWLine_eq_zero_iff q x).mpr
      ⟨hqzero, hx⟩)
  · exact deBruijnNewmanTitchmarshMellinWBand_denominator_ne_zero
      (deBruijnNewmanTitchmarshMellinWLine_mem_band
        (lt_of_le_of_ne hq (Ne.symm hqzero)) hq2pi x)

/-- The zero-filled boundary family, including the transformed line Jacobian. -/
def deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand
    (s : ℂ) (q x : ℝ) : ℂ :=
  deBruijnNewmanRiemannSiegelMellinWKernelExtension s
      (deBruijnNewmanTitchmarshMellinWLine q x) *
    deBruijnNewmanTitchmarshPhiDirection

theorem continuousAt_deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand
    {s : ℂ} (hs : 2 < s.re) {q x : ℝ} (hq : 0 ≤ q)
    (hqpi : q ≤ Real.pi) :
    ContinuousAt
      (fun p : ℝ × ℝ ↦
        deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand
          s p.1 p.2) (q, x) := by
  let w := deBruijnNewmanTitchmarshMellinWLine q x
  have hwLine : ContinuousAt
      (fun p : ℝ × ℝ ↦ deBruijnNewmanTitchmarshMellinWLine p.1 p.2) (q, x) := by
    unfold deBruijnNewmanTitchmarshMellinWLine
    fun_prop
  have hExtension : ContinuousAt
      (deBruijnNewmanRiemannSiegelMellinWKernelExtension s) w := by
    by_cases hw : w = 0
    · simpa only [hw] using
        continuousAt_deBruijnNewmanRiemannSiegelMellinWKernelExtension_zero hs
    · have hq2pi : q < 2 * Real.pi := by
        nlinarith [Real.pi_pos]
      exact continuousAt_deBruijnNewmanRiemannSiegelMellinWKernelExtension_of_ne
        s hw
          (deBruijnNewmanTitchmarshMellinWLine_mem_slitPlane_of_nonnegative hq hw)
          (deBruijnNewmanTitchmarshMellinWLine_denominator_ne_zero_of_nonnegative
            hq hq2pi hw)
  unfold deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand
  exact (hExtension.comp_of_eq hwLine rfl).mul continuousAt_const

theorem continuousOn_deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand
    {s : ℂ} (hs : 2 < s.re) :
    ContinuousOn
      (fun p : ℝ × ℝ ↦
        deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand
          s p.1 p.2)
      (Set.Icc (0 : ℝ) Real.pi ×ˢ Set.Icc (-6 : ℝ) 6) := by
  intro p hp
  exact
    (continuousAt_deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand
      hs hp.1.1 hp.1.2).continuousWithinAt

theorem exists_local_bound_deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand
    {s : ℂ} (hs : 2 < s.re) :
    ∃ B : ℝ, 0 < B ∧ ∀ q ∈ Set.Icc (0 : ℝ) Real.pi,
      ∀ x ∈ Set.Icc (-6 : ℝ) 6,
        ‖deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand s q x‖ ≤ B := by
  let K := Set.Icc (0 : ℝ) Real.pi ×ˢ Set.Icc (-6 : ℝ) 6
  let f : ℝ × ℝ → ℂ := fun p ↦
    deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand s p.1 p.2
  have hnormContinuous : ContinuousOn (fun p : ℝ × ℝ ↦ ‖f p‖) K :=
    (continuousOn_deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand
      hs).norm
  obtain ⟨B₀, hB₀⟩ := bddAbove_def.mp
    (IsCompact.bddAbove_image (K := K) (isCompact_Icc.prod isCompact_Icc)
      hnormContinuous)
  let B : ℝ := |B₀| + 1
  have hB : 0 < B := by dsimp only [B]; linarith [abs_nonneg B₀]
  refine ⟨B, hB, ?_⟩
  intro q hq x hx
  calc
    ‖deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand s q x‖ ≤
        B₀ := hB₀ _ ⟨(q, x), ⟨hq, hx⟩, rfl⟩
    _ ≤ |B₀| := le_abs_self B₀
    _ ≤ B := by simp [B]

theorem three_le_norm_deBruijnNewmanTitchmarshMellinWLine_of_large
    (q : ℝ) {x : ℝ} (hx : 6 ≤ |x|) :
    3 ≤ ‖deBruijnNewmanTitchmarshMellinWLine q x‖ := by
  have hsqrt : (1 / 2 : ℝ) ≤ Real.sqrt 2 / 2 := by
    linarith [deBruijnNewmanRiemannSiegelSqrtTwo_one_le]
  have hcoeff : 0 ≤ Real.sqrt 2 / 2 := by positivity
  calc
    3 ≤ (Real.sqrt 2 / 2) * |x| := by
      nlinarith [mul_le_mul hsqrt hx (by norm_num : (0 : ℝ) ≤ 6) hcoeff]
    _ = |(deBruijnNewmanTitchmarshMellinWLine q x).re| := by
      rw [deBruijnNewmanTitchmarshMellinWLine_re, abs_mul,
        abs_of_nonneg hcoeff]
    _ ≤ ‖deBruijnNewmanTitchmarshMellinWLine q x‖ :=
      Complex.abs_re_le_norm _

theorem abs_log_norm_deBruijnNewmanTitchmarshMellinWLine_le_of_large
    {q : ℝ} (hq : 0 < q) (hq2pi : q < 2 * Real.pi)
    {x : ℝ} (hx : 6 ≤ |x|) :
    |Real.log ‖deBruijnNewmanTitchmarshMellinWLine q x‖| ≤ |x| + 1 := by
  let w := deBruijnNewmanTitchmarshMellinWLine q x
  have hlower : 3 ≤ ‖w‖ :=
    three_le_norm_deBruijnNewmanTitchmarshMellinWLine_of_large q hx
  have hnorm : 0 < ‖w‖ := by linarith
  have hlogNonnegative : 0 ≤ Real.log ‖w‖ :=
    Real.log_nonneg (by linarith)
  rw [abs_of_nonneg hlogNonnegative]
  exact (Real.log_le_self hnorm.le).trans
    (deBruijnNewmanTitchmarshMellinWLine_norm_upper hq hq2pi x)

theorem norm_cpow_deBruijnNewmanTitchmarshMellinWLine_le_of_large
    (s : ℂ) {q : ℝ} (hq : 0 < q) (hq2pi : q < 2 * Real.pi)
    {x : ℝ} (hx : 6 ≤ |x|) :
    ‖deBruijnNewmanTitchmarshMellinWLine q x ^ (s - 1)‖ ≤
      Real.exp
        (|(s - 1).re| * (|x| + 1) + |(s - 1).im| * Real.pi) := by
  let w := deBruijnNewmanTitchmarshMellinWLine q x
  have hwNorm : 0 < ‖w‖ := by
    linarith [three_le_norm_deBruijnNewmanTitchmarshMellinWLine_of_large q hx]
  have hw : w ≠ 0 := norm_pos_iff.mp hwNorm
  rw [Complex.cpow_def_of_ne_zero hw, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hlog :=
    abs_log_norm_deBruijnNewmanTitchmarshMellinWLine_le_of_large hq hq2pi hx
  have harg := Complex.abs_arg_le_pi w
  rw [Complex.mul_re, Complex.log_re, Complex.log_im]
  calc
    Real.log ‖w‖ * (s - 1).re - w.arg * (s - 1).im ≤
        |Real.log ‖w‖ * (s - 1).re| + |w.arg * (s - 1).im| :=
      add_le_add (le_abs_self _) (neg_le_abs _)
    _ = |(s - 1).re| * |Real.log ‖w‖| + |(s - 1).im| * |w.arg| := by
      rw [abs_mul, abs_mul]
      ring
    _ ≤ |(s - 1).re| * (|x| + 1) + |(s - 1).im| * Real.pi :=
      add_le_add (mul_le_mul_of_nonneg_left hlog (abs_nonneg _))
        (mul_le_mul_of_nonneg_left harg (abs_nonneg _))

def deBruijnNewmanTitchmarshMellinWBoundaryTailLinearRate (s : ℂ) : ℝ :=
  |(s - 1).re| + Real.pi

def deBruijnNewmanTitchmarshMellinWBoundaryTailMajorantConstant
    (s : ℂ) : ℝ :=
  |(s - 1).re| + |(s - 1).im| * Real.pi +
    deBruijnNewmanTitchmarshMellinWBoundaryTailLinearRate s ^ 2 /
      (2 * Real.pi)

def deBruijnNewmanTitchmarshMellinWBoundaryTailMajorant
  (s : ℂ) (x : ℝ) : ℝ :=
  (1 / 2) *
    Real.exp (deBruijnNewmanTitchmarshMellinWBoundaryTailMajorantConstant s) *
    Real.exp (-(Real.pi / 2) * x ^ 2)

theorem deBruijnNewmanTitchmarshMellinWBoundaryTailLinearRate_mul_abs_le
    (s : ℂ) (x : ℝ) :
    deBruijnNewmanTitchmarshMellinWBoundaryTailLinearRate s * |x| ≤
      Real.pi / 2 * x ^ 2 +
        deBruijnNewmanTitchmarshMellinWBoundaryTailLinearRate s ^ 2 /
          (2 * Real.pi) := by
  simpa only [deBruijnNewmanTitchmarshMellinWBoundaryTailLinearRate,
    deBruijnNewmanTitchmarshMellinWSideLinearRate] using
    deBruijnNewmanTitchmarshMellinWSideLinearRate_mul_abs_le s Real.pi x

theorem norm_deBruijnNewmanRiemannSiegelKernel_mellinWLine_le_boundaryTailMajorant
    (s : ℂ) {q : ℝ} (hq : 0 < q) (hqpi : q ≤ Real.pi)
    {x : ℝ} (hx : 6 ≤ |x|) :
    ‖deBruijnNewmanRiemannSiegelKernel (1 - s)
        (deBruijnNewmanTitchmarshMellinWLine q x)‖ ≤
      deBruijnNewmanTitchmarshMellinWBoundaryTailMajorant s x := by
  let w := deBruijnNewmanTitchmarshMellinWLine q x
  have hq2pi : q < 2 * Real.pi := by nlinarith [Real.pi_pos]
  have hpow := norm_cpow_deBruijnNewmanTitchmarshMellinWLine_le_of_large
    s hq hq2pi hx
  have hden := two_le_norm_deBruijnNewmanRiemannSiegelDenominator_mellinWLine
    hq hq2pi hx
  have hdenPos : 0 < ‖deBruijnNewmanRiemannSiegelDenominator w‖ :=
    lt_of_lt_of_le (by norm_num) hden
  have hqlinear :=
    deBruijnNewmanTitchmarshMellinWLine_gaussianLinear_le hq hqpi x
  have hlinear :=
    deBruijnNewmanTitchmarshMellinWBoundaryTailLinearRate_mul_abs_le s x
  have hexponent : -(1 - s) = s - 1 := by ring
  rw [deBruijnNewmanRiemannSiegelKernel,
    deBruijnNewmanRiemannSiegelNumerator, hexponent, norm_div, norm_mul,
    norm_exp_deBruijnNewmanTitchmarshMellinWLine_gaussian]
  calc
    ‖w ^ (s - 1)‖ *
          Real.exp (-Real.pi * x ^ 2 + (Real.sqrt 2 / 2) * q * x) /
        ‖deBruijnNewmanRiemannSiegelDenominator w‖ ≤
        (Real.exp
            (|(s - 1).re| * (|x| + 1) + |(s - 1).im| * Real.pi) *
          Real.exp (-Real.pi * x ^ 2 + (Real.sqrt 2 / 2) * q * x)) /
            ‖deBruijnNewmanRiemannSiegelDenominator w‖ := by
      apply div_le_div_of_nonneg_right
      · exact mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _)
      · exact hdenPos.le
    _ ≤ (Real.exp
            (|(s - 1).re| * (|x| + 1) + |(s - 1).im| * Real.pi) *
          Real.exp (-Real.pi * x ^ 2 + (Real.sqrt 2 / 2) * q * x)) / 2 := by
      exact div_le_div_of_nonneg_left
        (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)) (by norm_num) hden
    _ ≤ deBruijnNewmanTitchmarshMellinWBoundaryTailMajorant s x := by
      rw [deBruijnNewmanTitchmarshMellinWBoundaryTailMajorant]
      conv_lhs => rw [div_eq_mul_inv, ← Real.exp_add]
      conv_rhs => rw [mul_assoc, ← Real.exp_add]
      rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
      conv_lhs => rw [mul_comm]
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
      simp only [deBruijnNewmanTitchmarshMellinWBoundaryTailMajorantConstant,
        deBruijnNewmanTitchmarshMellinWBoundaryTailLinearRate] at hlinear ⊢
      nlinarith

theorem integrable_deBruijnNewmanTitchmarshMellinWBoundaryTailMajorant
    (s : ℂ) :
    Integrable (deBruijnNewmanTitchmarshMellinWBoundaryTailMajorant s) := by
  have hgauss : Integrable (fun x : ℝ ↦
      Real.exp (-(Real.pi / 2) * x ^ 2)) :=
    integrable_exp_neg_mul_sq (by positivity)
  change Integrable (fun x : ℝ ↦
    ((1 / 2) *
      Real.exp (deBruijnNewmanTitchmarshMellinWBoundaryTailMajorantConstant s)) *
      Real.exp (-(Real.pi / 2) * x ^ 2))
  exact hgauss.const_mul
    ((1 / 2) *
      Real.exp (deBruijnNewmanTitchmarshMellinWBoundaryTailMajorantConstant s))

theorem deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand_eq
    (s : ℂ) {q : ℝ} (hq : 0 < q) (hq2pi : q < 2 * Real.pi) (x : ℝ) :
    deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand s q x =
      deBruijnNewmanRiemannSiegelKernelMellinWLineIntegrand s q x := by
  have hw : deBruijnNewmanTitchmarshMellinWLine q x ≠ 0 := by
    intro hzero
    exact hq.ne'
      ((deBruijnNewmanTitchmarshMellinWLine_eq_zero_iff q x).mp hzero).1
  unfold deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand
  unfold deBruijnNewmanRiemannSiegelKernelMellinWLineIntegrand
  rw [deBruijnNewmanRiemannSiegelMellinWKernelExtension_eq_kernel s hw
    (deBruijnNewmanTitchmarshMellinWLine_denominator_ne_zero_of_nonnegative
      hq.le hq2pi hw)]

theorem norm_deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand_le_tail
    (s : ℂ) {q : ℝ} (hq : 0 < q) (hqpi : q ≤ Real.pi)
    {x : ℝ} (hx : 6 ≤ |x|) :
    ‖deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand s q x‖ ≤
      deBruijnNewmanTitchmarshMellinWBoundaryTailMajorant s x := by
  have hq2pi : q < 2 * Real.pi := by nlinarith [Real.pi_pos]
  rw [deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand_eq
    s hq hq2pi x]
  simpa only [deBruijnNewmanRiemannSiegelKernelMellinWLineIntegrand,
    norm_mul, norm_deBruijnNewmanTitchmarshPhiDirection, mul_one] using
      norm_deBruijnNewmanRiemannSiegelKernel_mellinWLine_le_boundaryTailMajorant
        s hq hqpi hx

theorem tendsto_deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand_zero
    {s : ℂ} (hs : 2 < s.re) (x : ℝ) :
    Tendsto
      (fun q : ℝ ↦
        deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand s q x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand s 0 x)) := by
  have hpair : ContinuousAt (fun q : ℝ ↦ (q, x)) 0 := by fun_prop
  have hfull :=
    (continuousAt_deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand
      hs (q := 0) (x := x) (by norm_num) Real.pi_pos.le).comp_of_eq hpair rfl
  exact hfull.mono_left inf_le_left

def deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegral
    (s : ℂ) (q : ℝ) : ℂ :=
  ∫ x : ℝ,
    deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand s q x

/-- Dominated convergence across the simple zero at the boundary of the pole-free band. -/
theorem tendsto_deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegral_zero
    {s : ℂ} (hs : 2 < s.re) :
    Tendsto
      (deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegral s)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        (deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegral s 0)) := by
  obtain ⟨B, hBpos, hB⟩ :=
    exists_local_bound_deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand
      hs
  let bound : ℝ → ℝ := fun x ↦
    deBruijnNewmanTitchmarshMellinWBoundaryTailMajorant s x +
      (Set.Icc (-6 : ℝ) 6).indicator (fun _ ↦ B) x
  have hlocalOn : IntegrableOn (fun _ : ℝ ↦ B) (Set.Icc (-6 : ℝ) 6) :=
    continuous_const.integrableOn_Icc
  have hlocal : Integrable
      ((Set.Icc (-6 : ℝ) 6).indicator (fun _ ↦ B)) :=
    hlocalOn.integrable_indicator measurableSet_Icc
  have hboundIntegrable : Integrable bound :=
    (integrable_deBruijnNewmanTitchmarshMellinWBoundaryTailMajorant s).add hlocal
  unfold deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegral
  apply tendsto_integral_filter_of_dominated_convergence bound
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds Real.pi_pos)] with
      q (hq : 0 < q) (hqpi : q < Real.pi)
    have hq2pi : q < 2 * Real.pi := by nlinarith [Real.pi_pos]
    apply
      (continuous_deBruijnNewmanRiemannSiegelKernelMellinWLineIntegrand
        s hq hq2pi).aestronglyMeasurable.congr
    exact ae_of_all _ fun x ↦
      (deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand_eq
        s hq hq2pi x).symm
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds Real.pi_pos)] with
      q (hq : 0 < q) (hqpi : q < Real.pi)
    exact ae_of_all _ fun x ↦ by
      by_cases hxmem : x ∈ Set.Icc (-6 : ℝ) 6
      · have hlocalBound := hB q ⟨hq.le, hqpi.le⟩ x hxmem
        change ‖deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand
            s q x‖ ≤
          deBruijnNewmanTitchmarshMellinWBoundaryTailMajorant s x +
            (Set.Icc (-6 : ℝ) 6).indicator (fun _ ↦ B) x
        rw [Set.indicator_of_mem hxmem]
        exact hlocalBound.trans (le_add_of_nonneg_left (by
          unfold deBruijnNewmanTitchmarshMellinWBoundaryTailMajorant
          positivity))
      · have hx : 6 ≤ |x| := by
          by_contra hnot
          have habs : |x| < 6 := lt_of_not_ge hnot
          apply hxmem
          constructor
          · linarith [neg_abs_le x]
          · linarith [le_abs_self x]
        change ‖deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand
            s q x‖ ≤
          deBruijnNewmanTitchmarshMellinWBoundaryTailMajorant s x +
            (Set.Icc (-6 : ℝ) 6).indicator (fun _ ↦ B) x
        rw [Set.indicator_of_notMem hxmem, add_zero]
        exact
          norm_deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand_le_tail
            s hq hqpi.le hx
  · exact hboundIntegrable
  · exact ae_of_all _ fun x ↦
      tendsto_deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand_zero
        hs x

theorem deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegral_eq
    (s : ℂ) {q : ℝ} (hq : 0 < q) (hq2pi : q < 2 * Real.pi) :
    deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegral s q =
      deBruijnNewmanRiemannSiegelKernelMellinWLineIntegral s q := by
  unfold deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegral
  unfold deBruijnNewmanRiemannSiegelKernelMellinWLineIntegral
  apply integral_congr_ae
  exact ae_of_all _ fun x ↦
    deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand_eq
      s hq hq2pi x

/-- The boundary line obtained from `c ↓0+` is the reflected `R₀` contour. -/
theorem deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegral_zero_eq_raw
    {s : ℂ} (hs : 2 < s.re) :
    deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegral s 0 =
      -deBruijnNewmanRiemannSiegelRawIntegral 0 (1 - s) := by
  have hlimit :=
    tendsto_deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegral_zero hs
  have hconstant : Tendsto
      (deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegral s)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (-deBruijnNewmanRiemannSiegelRawIntegral 0 (1 - s))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds Real.pi_pos)] with
      q (hq : 0 < q) (hqpi : q < Real.pi)
    have hq2pi : q < 2 * Real.pi := by nlinarith [Real.pi_pos]
    have hpi2pi : Real.pi < 2 * Real.pi := by nlinarith [Real.pi_pos]
    have hdeform := deBruijnNewmanRiemannSiegelKernelMellinWLineIntegral_eq
      s hq hqpi.le hpi2pi
    symm
    calc
      deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegral s q =
          deBruijnNewmanRiemannSiegelKernelMellinWLineIntegral s q :=
        deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegral_eq
          s hq hq2pi
      _ = deBruijnNewmanRiemannSiegelKernelMellinWLineIntegral s Real.pi :=
        hdeform.symm
      _ = -deBruijnNewmanRiemannSiegelRawIntegral 0 (1 - s) :=
        deBruijnNewmanRiemannSiegelKernelMellinWLineIntegral_pi s
  exact tendsto_nhds_unique hlimit hconstant

theorem neg_deBruijnNewmanTitchmarshPhiDirection_cpow (a : ℂ) :
    (-deBruijnNewmanTitchmarshPhiDirection) ^ a =
      Complex.exp (-((Real.pi : ℂ) * Complex.I) * a) *
        deBruijnNewmanTitchmarshPhiDirection ^ a := by
  let z : ℂ := (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)
  have hphi : deBruijnNewmanTitchmarshPhiDirection ≠ 0 := by
    intro hzero
    have hnorm := norm_deBruijnNewmanTitchmarshPhiDirection
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm
  have hneg :
      -deBruijnNewmanTitchmarshPhiDirection =
        Complex.exp (z - (Real.pi : ℂ) * Complex.I) := by
    rw [deBruijnNewmanTitchmarshPhiDirection]
    exact (Complex.exp_sub_pi_mul_I z).symm
  rw [hneg, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp]
  · rw [deBruijnNewmanTitchmarshPhiDirection,
      Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _), Complex.log_exp,
      ← Complex.exp_add]
    congr 1
    unfold z
    ring
    · simp
      nlinarith [Real.pi_pos]
    · simp
      nlinarith [Real.pi_pos]
  · unfold z
    simp
    nlinarith [Real.pi_pos]
  · unfold z
    simp
    nlinarith [Real.pi_pos]

theorem deBruijnNewmanRiemannSiegelDenominator_neg (w : ℂ) :
    deBruijnNewmanRiemannSiegelDenominator (-w) =
      -deBruijnNewmanRiemannSiegelDenominator w := by
  unfold deBruijnNewmanRiemannSiegelDenominator
  rw [show ((Real.pi : ℂ) * Complex.I) * (-w) =
      -(((Real.pi : ℂ) * Complex.I) * w) by ring]
  rw [show -((Real.pi : ℂ) * Complex.I) * (-w) =
      ((Real.pi : ℂ) * Complex.I) * w by ring]
  ring

/-- The negative boundary ray carries the principal-branch multiplier `exp (-pi*i*s)`. -/
theorem deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand_neg
    (s : ℂ) {r : ℝ} (hr : 0 < r) :
    deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand s 0 (-r) =
      Complex.exp (-((Real.pi : ℂ) * Complex.I) * s) *
        deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand s 0 r := by
  let w := deBruijnNewmanTitchmarshMellinWLine 0 r
  have hw : w ≠ 0 := by
    intro hzero
    exact hr.ne'
      ((deBruijnNewmanTitchmarshMellinWLine_eq_zero_iff 0 r).mp hzero).2
  have hwNeg : deBruijnNewmanTitchmarshMellinWLine 0 (-r) = -w := by
    unfold w deBruijnNewmanTitchmarshMellinWLine
    push_cast
    ring
  have hden : deBruijnNewmanRiemannSiegelDenominator w ≠ 0 :=
    deBruijnNewmanTitchmarshMellinWLine_denominator_ne_zero_of_nonnegative
      (q := 0) (x := r) (by norm_num) (by positivity) hw
  have hpow : (-w) ^ (s - 1) =
      Complex.exp (-((Real.pi : ℂ) * Complex.I) * (s - 1)) *
        w ^ (s - 1) := by
    have hphi : deBruijnNewmanTitchmarshPhiDirection ≠ 0 := by
      intro hzero
      have hnorm := norm_deBruijnNewmanTitchmarshPhiDirection
      rw [hzero, norm_zero] at hnorm
      norm_num at hnorm
    have hnegphi : -deBruijnNewmanTitchmarshPhiDirection ≠ 0 :=
      neg_ne_zero.mpr hphi
    have hwPos : w = (r : ℂ) * deBruijnNewmanTitchmarshPhiDirection := by
      unfold w deBruijnNewmanTitchmarshMellinWLine
      push_cast
      ring
    rw [hwPos]
    rw [show -((r : ℂ) * deBruijnNewmanTitchmarshPhiDirection) =
        (r : ℂ) * (-deBruijnNewmanTitchmarshPhiDirection) by ring]
    rw [deBruijnNewman_cpow_ofReal_mul hr hnegphi,
      deBruijnNewman_cpow_ofReal_mul hr hphi,
      neg_deBruijnNewmanTitchmarshPhiDirection_cpow]
    ring
  have hfactor :
      -Complex.exp (-(((Real.pi : ℂ) * Complex.I) * (s - 1))) =
        Complex.exp (-(((Real.pi : ℂ) * Complex.I) * s)) := by
    rw [show -(((Real.pi : ℂ) * Complex.I) * (s - 1)) =
        -(((Real.pi : ℂ) * Complex.I) * s) +
          (Real.pi : ℂ) * Complex.I by ring,
      Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  have hwNegNe : -w ≠ 0 := neg_ne_zero.mpr hw
  unfold deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand
  rw [hwNeg]
  rw [deBruijnNewmanRiemannSiegelMellinWKernelExtension_eq_kernel
      s hwNegNe (by
        rw [deBruijnNewmanRiemannSiegelDenominator_neg]
        exact neg_ne_zero.mpr hden),
    deBruijnNewmanRiemannSiegelMellinWKernelExtension_eq_kernel s hw hden]
  unfold deBruijnNewmanRiemannSiegelKernel
  unfold deBruijnNewmanRiemannSiegelNumerator
  have hexponent : -(1 - s) = s - 1 := by ring
  rw [hexponent, hpow, deBruijnNewmanRiemannSiegelDenominator_neg]
  rw [show (-w) ^ 2 = w ^ 2 by ring]
  field_simp [hden]
  calc
    -(Complex.exp (-(((Real.pi : ℂ) * Complex.I) * (s - 1))) *
          w ^ (s - 1) * deBruijnNewmanTitchmarshPhiDirection) =
        (-Complex.exp (-(((Real.pi : ℂ) * Complex.I) * (s - 1)))) *
          (w ^ (s - 1) * deBruijnNewmanTitchmarshPhiDirection) := by ring
    _ = Complex.exp (-(((Real.pi : ℂ) * Complex.I) * s)) *
          (w ^ (s - 1) * deBruijnNewmanTitchmarshPhiDirection) := by rw [hfactor]
    _ = w ^ (s - 1) * deBruijnNewmanTitchmarshPhiDirection *
          Complex.exp (-(((Real.pi : ℂ) * Complex.I) * s)) := by ring

theorem deBruijnNewmanTitchmarshMellinRay_scaled_eq_mellinWBoundary
    (r : ℝ) :
    deBruijnNewmanTitchmarshMellinRayDirection * ((2 * Real.pi * r : ℝ) : ℂ) =
      -2 * (Real.pi : ℂ) * Complex.I *
        deBruijnNewmanTitchmarshMellinWLine 0 r := by
  have hdir : deBruijnNewmanTitchmarshMellinRayDirection =
      -Complex.I * deBruijnNewmanTitchmarshPhiDirection := by
    rw [deBruijnNewmanTitchmarshMellinRayDirection_eq_I_mul_riemannSiegelDirection,
      deBruijnNewmanTitchmarshPhiDirection_eq_neg_riemannSiegelDirection]
    ring
  rw [hdir]
  unfold deBruijnNewmanTitchmarshMellinWLine
  push_cast
  ring

/-- Exact positive-ray scaling, with all principal-power direction factors exposed. -/
theorem deBruijnNewmanTitchmarshMellinRemainderRayIntegrand_scaled
    (s : ℂ) {r : ℝ} (hr : 0 < r) :
    deBruijnNewmanTitchmarshPhiDirection ^ s *
        deBruijnNewmanTitchmarshMellinRemainderRayIntegrand s
          (2 * Real.pi * r) =
      -((2 * Real.pi : ℝ) : ℂ) ^ (s - 1) *
        deBruijnNewmanTitchmarshMellinRayDirection ^ s *
        deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand s 0 r := by
  let w := deBruijnNewmanTitchmarshMellinWLine 0 r
  let z := deBruijnNewmanTitchmarshMellinRayDirection *
    ((2 * Real.pi * r : ℝ) : ℂ)
  have hscale : 0 < 2 * Real.pi * r := mul_pos (by positivity) hr
  have hphi : deBruijnNewmanTitchmarshPhiDirection ≠ 0 := by
    intro hzero
    have hnorm := norm_deBruijnNewmanTitchmarshPhiDirection
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm
  have hray : deBruijnNewmanTitchmarshMellinRayDirection ≠ 0 := by
    intro hzero
    have hnorm := norm_deBruijnNewmanTitchmarshMellinRayDirection
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm
  have hw : w ≠ 0 := by
    intro hzero
    exact hr.ne'
      ((deBruijnNewmanTitchmarshMellinWLine_eq_zero_iff 0 r).mp hzero).2
  have hden : deBruijnNewmanRiemannSiegelDenominator w ≠ 0 :=
    deBruijnNewmanTitchmarshMellinWLine_denominator_ne_zero_of_nonnegative
      (q := 0) (x := r) (by norm_num) (by positivity) hw
  have hz : z = -2 * (Real.pi : ℂ) * Complex.I * w := by
    exact deBruijnNewmanTitchmarshMellinRay_scaled_eq_mellinWBoundary r
  have hquot :
      Complex.exp (deBruijnNewmanTitchmarshPhiMellinQuadratic z) /
          deBruijnNewmanTitchmarshPhiDenominator z =
        -Complex.exp (Complex.I * Real.pi * w ^ 2) /
          deBruijnNewmanRiemannSiegelDenominator w := by
    rw [hz]
    exact deBruijnNewmanTitchmarshPhiQuadraticQuotient_neg_two_pi_I_mul hden
  have hzpow : z ^ (s - 1) =
      ((2 * Real.pi : ℝ) : ℂ) ^ (s - 1) *
        (r : ℂ) ^ (s - 1) *
        deBruijnNewmanTitchmarshMellinRayDirection ^ (s - 1) := by
    calc
      z ^ (s - 1) =
          (((2 * Real.pi * r : ℝ) : ℂ) *
            deBruijnNewmanTitchmarshMellinRayDirection) ^ (s - 1) := by
        unfold z
        congr 1
        ring
      _ = ((2 * Real.pi * r : ℝ) : ℂ) ^ (s - 1) *
          deBruijnNewmanTitchmarshMellinRayDirection ^ (s - 1) :=
        deBruijnNewman_cpow_ofReal_mul hscale hray
      _ = ((2 * Real.pi : ℝ) : ℂ) ^ (s - 1) *
          (r : ℂ) ^ (s - 1) *
          deBruijnNewmanTitchmarshMellinRayDirection ^ (s - 1) := by
        rw [show ((2 * Real.pi * r : ℝ) : ℂ) =
            ((2 * Real.pi : ℝ) : ℂ) * (r : ℂ) by push_cast; ring,
          Complex.mul_cpow_ofReal_nonneg (by positivity) hr.le]
  have hwpow : w ^ (s - 1) =
      (r : ℂ) ^ (s - 1) *
        deBruijnNewmanTitchmarshPhiDirection ^ (s - 1) := by
    rw [show w = (r : ℂ) * deBruijnNewmanTitchmarshPhiDirection by
      unfold w deBruijnNewmanTitchmarshMellinWLine
      push_cast
      ring]
    exact deBruijnNewman_cpow_ofReal_mul hr hphi
  have hphiPow : deBruijnNewmanTitchmarshPhiDirection ^ (s - 1) *
      deBruijnNewmanTitchmarshPhiDirection =
        deBruijnNewmanTitchmarshPhiDirection ^ s := by
    conv_lhs => rhs; rw [← Complex.cpow_one deBruijnNewmanTitchmarshPhiDirection]
    rw [← Complex.cpow_add _ _ hphi]
    congr 1
    ring
  have hrayPow : deBruijnNewmanTitchmarshMellinRayDirection ^ (s - 1) *
      deBruijnNewmanTitchmarshMellinRayDirection =
        deBruijnNewmanTitchmarshMellinRayDirection ^ s := by
    conv_lhs => rhs; rw [← Complex.cpow_one deBruijnNewmanTitchmarshMellinRayDirection]
    rw [← Complex.cpow_add _ _ hray]
    congr 1
    ring
  unfold deBruijnNewmanTitchmarshMellinRemainderRayIntegrand
  rw [show deBruijnNewmanTitchmarshMellinRayDirection *
      ((2 * Real.pi * r : ℝ) : ℂ) = z by rfl]
  rw [show z ^ (s - 1) *
        Complex.exp (deBruijnNewmanTitchmarshPhiMellinQuadratic z) /
          deBruijnNewmanTitchmarshPhiDenominator z *
          deBruijnNewmanTitchmarshMellinRayDirection =
      z ^ (s - 1) *
        (Complex.exp (deBruijnNewmanTitchmarshPhiMellinQuadratic z) /
          deBruijnNewmanTitchmarshPhiDenominator z) *
        deBruijnNewmanTitchmarshMellinRayDirection by ring]
  rw [hquot, hzpow]
  unfold deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand
  rw [deBruijnNewmanRiemannSiegelMellinWKernelExtension_eq_kernel s hw hden]
  unfold deBruijnNewmanRiemannSiegelKernel
  unfold deBruijnNewmanRiemannSiegelNumerator
  have hexponent : -(1 - s) = s - 1 := by ring
  rw [hexponent, hwpow, ← hphiPow, ← hrayPow]
  field_simp [hden]

/-- The uniform tail estimate survives at the zero-filled boundary `q = 0`. -/
theorem norm_deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand_zero_le_tail
    {s : ℂ} (hs : 2 < s.re) {x : ℝ} (hx : 6 ≤ |x|) :
    ‖deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand s 0 x‖ ≤
      deBruijnNewmanTitchmarshMellinWBoundaryTailMajorant s x := by
  have hlimit :=
    (tendsto_deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand_zero
      hs x).norm
  apply le_of_tendsto hlimit
  filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds Real.pi_pos)] with
      q (hq : 0 < q) (hqpi : q < Real.pi)
  exact
    norm_deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand_le_tail
      s hq hqpi.le hx

/-- Absolute integrability of the zero-filled boundary line. -/
theorem integrable_deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand_zero
    {s : ℂ} (hs : 2 < s.re) :
    Integrable
      (deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand s 0) := by
  obtain ⟨B, hBpos, hB⟩ :=
    exists_local_bound_deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand
      hs
  let bound : ℝ → ℝ := fun x ↦
    deBruijnNewmanTitchmarshMellinWBoundaryTailMajorant s x +
      (Set.Icc (-6 : ℝ) 6).indicator (fun _ ↦ B) x
  have hlocalOn : IntegrableOn (fun _ : ℝ ↦ B) (Set.Icc (-6 : ℝ) 6) :=
    continuous_const.integrableOn_Icc
  have hlocal : Integrable
      ((Set.Icc (-6 : ℝ) 6).indicator (fun _ ↦ B)) :=
    hlocalOn.integrable_indicator measurableSet_Icc
  have hboundIntegrable : Integrable bound :=
    (integrable_deBruijnNewmanTitchmarshMellinWBoundaryTailMajorant s).add hlocal
  have hcontinuous : Continuous
      (deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand s 0) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have hfull :=
      continuousAt_deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand
        hs (q := 0) (x := x) (by norm_num) Real.pi_pos.le
    have hcomp := hfull.comp (Continuous.prodMk_right (0 : ℝ)).continuousAt
    change ContinuousAt
      (fun y : ℝ ↦
        deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand s 0 y) x at hcomp
    change ContinuousAt
      (fun y : ℝ ↦
        deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand s 0 y) x
    exact hcomp
  refine Integrable.mono' hboundIntegrable hcontinuous.aestronglyMeasurable ?_
  exact ae_of_all _ fun x ↦ by
    by_cases hxmem : x ∈ Set.Icc (-6 : ℝ) 6
    · have hlocalBound := hB 0 ⟨by norm_num, Real.pi_pos.le⟩ x hxmem
      change ‖deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand
          s 0 x‖ ≤
        deBruijnNewmanTitchmarshMellinWBoundaryTailMajorant s x +
          (Set.Icc (-6 : ℝ) 6).indicator (fun _ ↦ B) x
      rw [Set.indicator_of_mem hxmem]
      exact hlocalBound.trans (le_add_of_nonneg_left (by
        unfold deBruijnNewmanTitchmarshMellinWBoundaryTailMajorant
        positivity))
    · have hx : 6 ≤ |x| := by
        by_contra hnot
        have habs : |x| < 6 := lt_of_not_ge hnot
        apply hxmem
        constructor
        · linarith [neg_abs_le x]
        · linarith [le_abs_self x]
      change ‖deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand
          s 0 x‖ ≤
        deBruijnNewmanTitchmarshMellinWBoundaryTailMajorant s x +
          (Set.Icc (-6 : ℝ) 6).indicator (fun _ ↦ B) x
      rw [Set.indicator_of_notMem hxmem, add_zero]
      exact
        norm_deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand_zero_le_tail
          hs hx

/-- The principal-branch phase joins the two boundary half-lines. -/
theorem deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegral_zero_eq_phase_mul_Ioi
    {s : ℂ} (hs : 2 < s.re) :
    deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegral s 0 =
      (1 + Complex.exp (-(((Real.pi : ℂ) * Complex.I) * s))) *
        ∫ r : ℝ in Ioi 0,
          deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand s 0 r := by
  let f : ℝ → ℂ := fun x ↦
    deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand s 0 x
  have hfull : Integrable f :=
    integrable_deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand_zero hs
  have hnegative :
      (∫ x : ℝ in Iic 0, f x) =
        Complex.exp (-(((Real.pi : ℂ) * Complex.I) * s)) *
          ∫ r : ℝ in Ioi 0, f r := by
    calc
      (∫ x : ℝ in Iic 0, f x) = ∫ r : ℝ in Ioi 0, f (-r) := by
        symm
        simpa only [neg_zero] using integral_comp_neg_Ioi 0 f
      _ = ∫ r : ℝ in Ioi 0,
          Complex.exp (-(((Real.pi : ℂ) * Complex.I) * s)) * f r := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        dsimp only [f]
        rw [deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand_neg
          s hr]
        ring
      _ = Complex.exp (-(((Real.pi : ℂ) * Complex.I) * s)) *
          ∫ r : ℝ in Ioi 0, f r := by
        rw [integral_const_mul]
  unfold deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegral
  change (∫ x : ℝ, f x) = _
  rw [← integral_add_compl measurableSet_Ioi hfull, compl_Ioi, hnegative]
  ring

/-- The source remainder ray, rescaled by `2π`, is the positive boundary half-line. -/
theorem deBruijnNewmanTitchmarshMellinRemainderRayIntegral_scaled_eq_boundary_Ioi
    (s : ℂ) :
    deBruijnNewmanTitchmarshPhiDirection ^ s *
        (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
          ∫ r : ℝ in Ioi 0,
            deBruijnNewmanTitchmarshMellinRemainderRayIntegrand s r) =
      -((2 * Real.pi : ℝ) : ℂ) ^ (s - 1) *
        deBruijnNewmanTitchmarshMellinRayDirection ^ s *
          ∫ r : ℝ in Ioi 0,
            deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand s 0 r := by
  have hscaled :
      deBruijnNewmanTitchmarshPhiDirection ^ s *
          (∫ r : ℝ in Ioi 0,
            deBruijnNewmanTitchmarshMellinRemainderRayIntegrand s
              (2 * Real.pi * r)) =
        -((2 * Real.pi : ℝ) : ℂ) ^ (s - 1) *
          deBruijnNewmanTitchmarshMellinRayDirection ^ s *
            ∫ r : ℝ in Ioi 0,
              deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand
                s 0 r := by
    rw [← integral_const_mul, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    exact deBruijnNewmanTitchmarshMellinRemainderRayIntegrand_scaled s hr
  have hsub := integral_comp_mul_left_Ioi
    (deBruijnNewmanTitchmarshMellinRemainderRayIntegrand s) 0
    (show 0 < 2 * Real.pi by positivity)
  simp only [mul_zero] at hsub
  have hsub' :
      (∫ r : ℝ in Ioi 0,
        deBruijnNewmanTitchmarshMellinRemainderRayIntegrand s
          (2 * Real.pi * r)) =
        (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
          ∫ r : ℝ in Ioi 0,
            deBruijnNewmanTitchmarshMellinRemainderRayIntegrand s r) := by
    simpa only [Complex.real_smul, Complex.ofReal_inv] using hsub
  rwa [hsub'] at hscaled

/-- Branch-aware identification of the source remainder with the reflected `R₀` term. -/
theorem deBruijnNewmanTitchmarshMellinRemainderRayIntegral_phase_scaled_eq_raw
    {s : ℂ} (hs : 2 < s.re) :
    (1 + Complex.exp (-(((Real.pi : ℂ) * Complex.I) * s))) *
        deBruijnNewmanTitchmarshPhiDirection ^ s *
          (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
            ∫ r : ℝ in Ioi 0,
              deBruijnNewmanTitchmarshMellinRemainderRayIntegrand s r) =
      ((2 * Real.pi : ℝ) : ℂ) ^ (s - 1) *
        deBruijnNewmanTitchmarshMellinRayDirection ^ s *
          deBruijnNewmanRiemannSiegelRawIntegral 0 (1 - s) := by
  have hscaled :=
    deBruijnNewmanTitchmarshMellinRemainderRayIntegral_scaled_eq_boundary_Ioi s
  have hphase :=
    deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegral_zero_eq_phase_mul_Ioi
      hs
  have hraw :=
    deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegral_zero_eq_raw hs
  calc
    (1 + Complex.exp (-(((Real.pi : ℂ) * Complex.I) * s))) *
          deBruijnNewmanTitchmarshPhiDirection ^ s *
            (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
              ∫ r : ℝ in Ioi 0,
                deBruijnNewmanTitchmarshMellinRemainderRayIntegrand s r) =
        (1 + Complex.exp (-(((Real.pi : ℂ) * Complex.I) * s))) *
          (deBruijnNewmanTitchmarshPhiDirection ^ s *
            (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
              ∫ r : ℝ in Ioi 0,
                deBruijnNewmanTitchmarshMellinRemainderRayIntegrand s r)) := by ring
    _ = (1 + Complex.exp (-(((Real.pi : ℂ) * Complex.I) * s))) *
          (-((2 * Real.pi : ℝ) : ℂ) ^ (s - 1) *
            deBruijnNewmanTitchmarshMellinRayDirection ^ s *
              ∫ r : ℝ in Ioi 0,
                deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegrand
                  s 0 r) := by rw [hscaled]
    _ = -((2 * Real.pi : ℝ) : ℂ) ^ (s - 1) *
          deBruijnNewmanTitchmarshMellinRayDirection ^ s *
            deBruijnNewmanRiemannSiegelMellinWKernelExtensionLineIntegral s 0 := by
      rw [hphase]
      ring
    _ = -((2 * Real.pi : ℝ) : ℂ) ^ (s - 1) *
          deBruijnNewmanTitchmarshMellinRayDirection ^ s *
            (-deBruijnNewmanRiemannSiegelRawIntegral 0 (1 - s)) := by rw [hraw]
    _ = ((2 * Real.pi : ℝ) : ℂ) ^ (s - 1) *
          deBruijnNewmanTitchmarshMellinRayDirection ^ s *
            deBruijnNewmanRiemannSiegelRawIntegral 0 (1 - s) := by ring

theorem deBruijnNewmanTitchmarshMellinRayDirection_arg :
    Complex.arg deBruijnNewmanTitchmarshMellinRayDirection = -Real.pi / 4 := by
  rw [deBruijnNewmanTitchmarshMellinRayDirection,
    deBruijnNewmanTitchmarshPhiDirection]
  change Complex.arg
    (conj (Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I))) = _
  rw [← Complex.exp_conj]
  simp only [map_mul, conj_ofReal, conj_I, mul_neg, Complex.arg_exp]
  have him : (-(↑(Real.pi / 4) * Complex.I)).im = -Real.pi / 4 := by
    simp
    ring
  rw [him]
  apply (toIocMod_eq_self Real.two_pi_pos).mpr
  constructor <;> linarith [Real.pi_pos]

/-- On the source affine parameter, the Laplace rate is the rotated conjugate
Riemann--Siegel coordinate. -/
theorem deBruijnNewmanTitchmarshMellinRate_reflected_affine (v : ℝ) :
    deBruijnNewmanTitchmarshMellinRate
        (Real.pi * Real.sqrt 2 - 2 * Real.pi * v) =
      deBruijnNewmanTitchmarshMellinRayDirection *
        starRingEnd ℂ (deBruijnNewmanRiemannSiegelLine 0 v) := by
  have href :=
    deBruijnNewmanTitchmarshPhiReflectedLine_affine_riemannSiegelLine v
  have hstar := congrArg (starRingEnd ℂ) href
  rw [deBruijnNewmanTitchmarshPhiReflectedLine_eq_star] at hstar
  change conj (conj
      (deBruijnNewmanTitchmarshPhiLine
        (Real.pi * Real.sqrt 2 - 2 * Real.pi * v))) =
    conj (-2 * (Real.pi : ℂ) * Complex.I *
      deBruijnNewmanRiemannSiegelLine 0 v) at hstar
  simp only [conj_conj, map_neg, map_mul, map_ofNat, conj_ofReal, conj_I] at hstar
  have hline :
      deBruijnNewmanTitchmarshPhiLine
          (Real.pi * Real.sqrt 2 - 2 * Real.pi * v) =
        2 * (Real.pi : ℂ) * Complex.I *
          starRingEnd ℂ (deBruijnNewmanRiemannSiegelLine 0 v) := by
    calc
      _ = -2 * (Real.pi : ℂ) * (-Complex.I) *
          starRingEnd ℂ (deBruijnNewmanRiemannSiegelLine 0 v) := hstar
      _ = _ := by ring
  unfold deBruijnNewmanTitchmarshMellinRate
  rw [hline]
  have hpi : (Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hpi]
  rw [Complex.I_sq]
  ring

theorem deBruijnNewmanRiemannSiegelLine_star_arg_lower (v : ℝ) :
    -(Real.pi / 2) <
      Complex.arg (starRingEnd ℂ (deBruijnNewmanRiemannSiegelLine 0 v)) := by
  rw [Complex.neg_pi_div_two_lt_arg_iff]
  simp only [conj_re, conj_im, deBruijnNewmanRiemannSiegelLine_re,
    deBruijnNewmanRiemannSiegelLine_im, Nat.cast_zero, zero_add]
  by_cases hv : 0 ≤ v
  · right
    have hsqrt : 0 ≤ Real.sqrt 2 / 2 := by positivity
    have hmul := mul_nonneg hsqrt hv
    nlinarith
  · left
    have hvneg : v < 0 := lt_of_not_ge hv
    have hsqrt : 0 < Real.sqrt 2 / 2 := by positivity
    have hmul : (Real.sqrt 2 / 2) * v < 0 :=
      mul_neg_of_pos_of_neg hsqrt hvneg
    linarith

/-- The principal logarithm splits along the rotated conjugate diagonal line. -/
theorem deBruijnNewmanTitchmarshMellinRayDirection_mul_star_riemannSiegelLine_log
    (v : ℝ) :
    Complex.log
        (deBruijnNewmanTitchmarshMellinRayDirection *
          starRingEnd ℂ (deBruijnNewmanRiemannSiegelLine 0 v)) =
      Complex.log deBruijnNewmanTitchmarshMellinRayDirection +
        Complex.log (starRingEnd ℂ (deBruijnNewmanRiemannSiegelLine 0 v)) := by
  have hray : deBruijnNewmanTitchmarshMellinRayDirection ≠ 0 := by
    intro hzero
    have hnorm := norm_deBruijnNewmanTitchmarshMellinRayDirection
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm
  have hw : deBruijnNewmanRiemannSiegelLine 0 v ≠ 0 :=
    (Complex.mem_slitPlane_iff_arg.mp
      (deBruijnNewmanRiemannSiegelLine_mem_slitPlane 0 v)).2
  have hc : starRingEnd ℂ (deBruijnNewmanRiemannSiegelLine 0 v) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).2 hw
  apply Complex.log_mul hray hc
  constructor
  · rw [deBruijnNewmanTitchmarshMellinRayDirection_arg]
    linarith [deBruijnNewmanRiemannSiegelLine_star_arg_lower v, Real.pi_pos]
  · rw [deBruijnNewmanTitchmarshMellinRayDirection_arg]
    linarith [Complex.arg_le_pi
      (starRingEnd ℂ (deBruijnNewmanRiemannSiegelLine 0 v)), Real.pi_pos]

/-- Exact cancellation of the source direction power against the affine Laplace rate. -/
theorem deBruijnNewmanTitchmarshMellinRate_cpow_cancel_affine
    (s : ℂ) (v : ℝ) :
    deBruijnNewmanTitchmarshMellinRayDirection ^ s *
        deBruijnNewmanTitchmarshMellinRate
          (Real.pi * Real.sqrt 2 - 2 * Real.pi * v) ^ (-s) =
      starRingEnd ℂ (deBruijnNewmanRiemannSiegelLine 0 v) ^ (-s) := by
  let d := deBruijnNewmanTitchmarshMellinRayDirection
  let c := starRingEnd ℂ (deBruijnNewmanRiemannSiegelLine 0 v)
  have hrate : deBruijnNewmanTitchmarshMellinRate
      (Real.pi * Real.sqrt 2 - 2 * Real.pi * v) = d * c := by
    dsimp only [d, c]
    exact deBruijnNewmanTitchmarshMellinRate_reflected_affine v
  have hd : d ≠ 0 := by
    dsimp only [d]
    intro hzero
    have hnorm := norm_deBruijnNewmanTitchmarshMellinRayDirection
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm
  have hw : deBruijnNewmanRiemannSiegelLine 0 v ≠ 0 :=
    (Complex.mem_slitPlane_iff_arg.mp
      (deBruijnNewmanRiemannSiegelLine_mem_slitPlane 0 v)).2
  have hc : c ≠ 0 := (map_ne_zero (starRingEnd ℂ)).2 hw
  have hlog : Complex.log (d * c) = Complex.log d + Complex.log c := by
    dsimp only [d, c]
    exact
      deBruijnNewmanTitchmarshMellinRayDirection_mul_star_riemannSiegelLine_log v
  rw [hrate]
  rw [Complex.cpow_def_of_ne_zero hd,
    Complex.cpow_def_of_ne_zero (mul_ne_zero hd hc),
    Complex.cpow_def_of_ne_zero hc, hlog]
  rw [← Complex.exp_add]
  congr 1
  ring

theorem deBruijnNewmanTitchmarshPhiExponent_star_mellinQuadratic (z : ℂ) :
    starRingEnd ℂ
        (deBruijnNewmanTitchmarshPhiMellinQuadratic (starRingEnd ℂ z)) =
      deBruijnNewmanTitchmarshPhiExponent (1 / 2) z := by
  unfold deBruijnNewmanTitchmarshPhiMellinQuadratic
  unfold deBruijnNewmanTitchmarshPhiExponent
  simp only [map_sub, map_div₀, map_mul, map_pow, map_ofNat, conj_I,
    conj_ofReal, conj_conj]
  ring

theorem deBruijnNewmanTitchmarshPhiDenominator_star (z : ℂ) :
    starRingEnd ℂ
        (deBruijnNewmanTitchmarshPhiDenominator (starRingEnd ℂ z)) =
      deBruijnNewmanTitchmarshPhiDenominator z := by
  unfold deBruijnNewmanTitchmarshPhiDenominator
  rw [map_sub, map_one]
  rw [← Complex.exp_conj]
  rw [conj_conj]

/-- The original source-line Gaussian quotient is the conjugate reflected quotient. -/
theorem deBruijnNewmanTitchmarshPhiQuadraticQuotient_sourceLine_affine
    (v : ℝ) :
    Complex.exp
          (deBruijnNewmanTitchmarshPhiExponent (1 / 2)
            (deBruijnNewmanTitchmarshPhiLine
              (Real.pi * Real.sqrt 2 - 2 * Real.pi * v))) /
        deBruijnNewmanTitchmarshPhiDenominator
          (deBruijnNewmanTitchmarshPhiLine
            (Real.pi * Real.sqrt 2 - 2 * Real.pi * v)) =
      -starRingEnd ℂ
        (Complex.exp (Complex.I * Real.pi *
              deBruijnNewmanRiemannSiegelLine 0 v ^ 2) /
          deBruijnNewmanRiemannSiegelDenominator
            (deBruijnNewmanRiemannSiegelLine 0 v)) := by
  have hquot :=
    deBruijnNewmanTitchmarshPhiQuadraticQuotient_reflectedLine_affine v
  have hstar := congrArg (starRingEnd ℂ) hquot
  rw [deBruijnNewmanTitchmarshPhiReflectedLine_eq_star] at hstar
  simp only [map_div₀, map_neg] at hstar
  rw [← Complex.exp_conj] at hstar
  rw [deBruijnNewmanTitchmarshPhiExponent_star_mellinQuadratic] at hstar
  rw [deBruijnNewmanTitchmarshPhiDenominator_star] at hstar
  calc
    _ = -(starRingEnd ℂ)
          (Complex.exp (Complex.I * Real.pi *
            deBruijnNewmanRiemannSiegelLine 0 v ^ 2)) /
        (starRingEnd ℂ)
          (deBruijnNewmanRiemannSiegelDenominator
            (deBruijnNewmanRiemannSiegelLine 0 v)) := hstar
    _ = _ := by
      rw [map_div₀]
      ring

theorem deBruijnNewmanTitchmarshPhiDirection_eq_I_mul_mellinRayDirection :
    deBruijnNewmanTitchmarshPhiDirection =
      Complex.I * deBruijnNewmanTitchmarshMellinRayDirection := by
  rw [deBruijnNewmanTitchmarshPhiDirection_eq_neg_riemannSiegelDirection,
    deBruijnNewmanTitchmarshMellinRayDirection_eq_I_mul_riemannSiegelDirection]
  rw [← mul_assoc, Complex.I_mul_I]
  ring

theorem deBruijnNewmanRiemannSiegelLine_star_cpow_neg (s : ℂ) (v : ℝ) :
    starRingEnd ℂ (deBruijnNewmanRiemannSiegelLine 0 v) ^ (-s) =
      starRingEnd ℂ
        (deBruijnNewmanRiemannSiegelLine 0 v ^
          (-(starRingEnd ℂ s))) := by
  have harg : Complex.arg (deBruijnNewmanRiemannSiegelLine 0 v) ≠ Real.pi :=
    Complex.slitPlane_arg_ne_pi
      (deBruijnNewmanRiemannSiegelLine_mem_slitPlane 0 v)
  have hconj := Complex.conj_cpow
    (deBruijnNewmanRiemannSiegelLine 0 v) (-s) harg
  simpa only [map_neg] using hconj

/-- Pointwise conversion of the original `L` term to the Schwarz-reflected
Riemann--Siegel integrand. -/
theorem deBruijnNewmanTitchmarshMellinSourceLineIntegrand_affine
    (s : ℂ) (v : ℝ) :
    deBruijnNewmanTitchmarshMellinRayDirection ^ s *
        ((deBruijnNewmanTitchmarshMellinRate
            (Real.pi * Real.sqrt 2 - 2 * Real.pi * v) ^ (-s) *
              Complex.Gamma s) *
          deBruijnNewmanTitchmarshPhiLineIntegrand (1 / 2)
            (Real.pi * Real.sqrt 2 - 2 * Real.pi * v)) =
      Complex.I * Complex.Gamma s *
        starRingEnd ℂ
          (deBruijnNewmanRiemannSiegelLineIntegrand 0
            (starRingEnd ℂ s) v) := by
  let w := deBruijnNewmanRiemannSiegelLine 0 v
  let q := Complex.exp (Complex.I * Real.pi * w ^ 2) /
    deBruijnNewmanRiemannSiegelDenominator w
  have hpower := deBruijnNewmanTitchmarshMellinRate_cpow_cancel_affine s v
  have hquot :=
    deBruijnNewmanTitchmarshPhiQuadraticQuotient_sourceLine_affine v
  have hstarPower : starRingEnd ℂ w ^ (-s) =
      starRingEnd ℂ (w ^ (-(starRingEnd ℂ s))) := by
    dsimp only [w]
    exact deBruijnNewmanRiemannSiegelLine_star_cpow_neg s v
  have hdRS : deBruijnNewmanRiemannSiegelDirection =
      -deBruijnNewmanTitchmarshPhiDirection := by
    linear_combination
      deBruijnNewmanTitchmarshPhiDirection_eq_neg_riemannSiegelDirection
  have hstarDirection :
      starRingEnd ℂ deBruijnNewmanRiemannSiegelDirection =
        -deBruijnNewmanTitchmarshMellinRayDirection := by
    rw [hdRS, map_neg]
    rfl
  unfold deBruijnNewmanTitchmarshPhiLineIntegrand
  change deBruijnNewmanTitchmarshMellinRayDirection ^ s *
      ((deBruijnNewmanTitchmarshMellinRate
          (Real.pi * Real.sqrt 2 - 2 * Real.pi * v) ^ (-s) *
        Complex.Gamma s) *
        (Complex.exp
            (deBruijnNewmanTitchmarshPhiExponent (1 / 2)
              (deBruijnNewmanTitchmarshPhiLine
                (Real.pi * Real.sqrt 2 - 2 * Real.pi * v))) /
          deBruijnNewmanTitchmarshPhiDenominator
            (deBruijnNewmanTitchmarshPhiLine
              (Real.pi * Real.sqrt 2 - 2 * Real.pi * v)) *
          deBruijnNewmanTitchmarshPhiDirection)) = _
  calc
    _ = (deBruijnNewmanTitchmarshMellinRayDirection ^ s *
          deBruijnNewmanTitchmarshMellinRate
            (Real.pi * Real.sqrt 2 - 2 * Real.pi * v) ^ (-s)) *
        Complex.Gamma s *
          (Complex.exp
              (deBruijnNewmanTitchmarshPhiExponent (1 / 2)
                (deBruijnNewmanTitchmarshPhiLine
                  (Real.pi * Real.sqrt 2 - 2 * Real.pi * v))) /
            deBruijnNewmanTitchmarshPhiDenominator
              (deBruijnNewmanTitchmarshPhiLine
                (Real.pi * Real.sqrt 2 - 2 * Real.pi * v))) *
          deBruijnNewmanTitchmarshPhiDirection := by ring
    _ = starRingEnd ℂ w ^ (-s) * Complex.Gamma s *
          (-starRingEnd ℂ q) * deBruijnNewmanTitchmarshPhiDirection := by
      rw [hpower]
      dsimp only [q, w]
      rw [hquot]
    _ = Complex.I * Complex.Gamma s *
        starRingEnd ℂ
          ((w ^ (-(starRingEnd ℂ s)) * q) *
            deBruijnNewmanRiemannSiegelDirection) := by
      rw [map_mul, map_mul, hstarPower, hstarDirection,
        deBruijnNewmanTitchmarshPhiDirection_eq_I_mul_mellinRayDirection]
      ring
    _ = Complex.I * Complex.Gamma s *
        starRingEnd ℂ
          (deBruijnNewmanRiemannSiegelLineIntegrand 0
            (starRingEnd ℂ s) v) := by
      congr 3
      unfold deBruijnNewmanRiemannSiegelKernel
      unfold deBruijnNewmanRiemannSiegelNumerator
      dsimp only [q, w]
      ring

/-- The original `L` term is the Schwarz-reflected raw Riemann--Siegel integral. -/
theorem deBruijnNewmanTitchmarshMellinSourceLineIntegral_eq_reflect_raw
    (s : ℂ) :
    deBruijnNewmanTitchmarshMellinRayDirection ^ s *
        (∫ v : ℝ,
          (deBruijnNewmanTitchmarshMellinRate v ^ (-s) * Complex.Gamma s) *
            deBruijnNewmanTitchmarshPhiLineIntegrand (1 / 2) v) =
      2 * (Real.pi : ℂ) * Complex.I * Complex.Gamma s *
        deBruijnNewmanRiemannSiegelReflect
          (deBruijnNewmanRiemannSiegelRawIntegral 0) s := by
  let f : ℝ → ℂ := fun v ↦
    (deBruijnNewmanTitchmarshMellinRate v ^ (-s) * Complex.Gamma s) *
      deBruijnNewmanTitchmarshPhiLineIntegrand (1 / 2) v
  have hchange := integral_comp_titchmarsh_reflected_affine f
  have haffine :
      deBruijnNewmanTitchmarshMellinRayDirection ^ s *
          (∫ v : ℝ, f (Real.pi * Real.sqrt 2 - 2 * Real.pi * v)) =
        Complex.I * Complex.Gamma s *
          deBruijnNewmanRiemannSiegelReflect
            (deBruijnNewmanRiemannSiegelRawIntegral 0) s := by
    rw [← integral_const_mul]
    calc
      (∫ v : ℝ,
          deBruijnNewmanTitchmarshMellinRayDirection ^ s *
            f (Real.pi * Real.sqrt 2 - 2 * Real.pi * v)) =
          ∫ v : ℝ,
            Complex.I * Complex.Gamma s *
              starRingEnd ℂ
                (deBruijnNewmanRiemannSiegelLineIntegrand 0
                  (starRingEnd ℂ s) v) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun v ↦ by
          dsimp only [f]
          exact deBruijnNewmanTitchmarshMellinSourceLineIntegrand_affine s v
      _ = Complex.I * Complex.Gamma s *
          ∫ v : ℝ,
            starRingEnd ℂ
              (deBruijnNewmanRiemannSiegelLineIntegrand 0
                (starRingEnd ℂ s) v) := by
        rw [integral_const_mul]
      _ = Complex.I * Complex.Gamma s *
          deBruijnNewmanRiemannSiegelReflect
            (deBruijnNewmanRiemannSiegelRawIntegral 0) s := by
        rw [integral_conj]
        rfl
  change (∫ v : ℝ, f (Real.pi * Real.sqrt 2 - 2 * Real.pi * v)) =
    (2 * Real.pi)⁻¹ • ∫ v : ℝ, f v at hchange
  change deBruijnNewmanTitchmarshMellinRayDirection ^ s *
      (∫ v : ℝ, f v) = _
  calc
    deBruijnNewmanTitchmarshMellinRayDirection ^ s *
        (∫ v : ℝ, f v) =
      (2 * (Real.pi : ℂ)) *
        (deBruijnNewmanTitchmarshMellinRayDirection ^ s *
          ∫ v : ℝ, f (Real.pi * Real.sqrt 2 - 2 * Real.pi * v)) := by
      rw [hchange]
      simp only [Complex.real_smul, Complex.ofReal_inv]
      have htwoPi : (2 * (Real.pi : ℂ)) ≠ 0 :=
        mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
      field_simp [htwoPi]
      push_cast
      ring
    _ = (2 * (Real.pi : ℂ)) *
        (Complex.I * Complex.Gamma s *
          deBruijnNewmanRiemannSiegelReflect
            (deBruijnNewmanRiemannSiegelRawIntegral 0) s) := by rw [haffine]
    _ = 2 * (Real.pi : ℂ) * Complex.I * Complex.Gamma s *
        deBruijnNewmanRiemannSiegelReflect
          (deBruijnNewmanRiemannSiegelRawIntegral 0) s := by ring

/-- Titchmarsh `(2.10.6)` on the initial half-plane, with both contour terms explicit. -/
theorem deBruijnNewmanTitchmarshMellin_two_contours
    {s : ℂ} (hs : 1 < s.re) :
    Complex.Gamma s *
        deBruijnNewmanRiemannSiegelReflect
          (deBruijnNewmanRiemannSiegelRawIntegral 0) s =
      Complex.Gamma s * riemannZeta s -
        ∫ r : ℝ in Ioi 0,
          deBruijnNewmanTitchmarshMellinRemainderRayIntegrand s r := by
  have hsource := deBruijnNewmanTitchmarshMellin_source_before_deformation hs
  rw [deBruijnNewmanTitchmarshMellinSourceLineIntegral_eq_reflect_raw] at hsource
  have hconst : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  exact mul_left_cancel₀ hconst (by
    calc
      (2 * (Real.pi : ℂ) * Complex.I) *
          (Complex.Gamma s *
            deBruijnNewmanRiemannSiegelReflect
              (deBruijnNewmanRiemannSiegelRawIntegral 0) s) =
        2 * (Real.pi : ℂ) * Complex.I * Complex.Gamma s *
          deBruijnNewmanRiemannSiegelReflect
            (deBruijnNewmanRiemannSiegelRawIntegral 0) s := by ring
      _ = 2 * (Real.pi : ℂ) * Complex.I *
          (Complex.Gamma s * riemannZeta s -
            ∫ r : ℝ in Ioi 0,
              deBruijnNewmanTitchmarshMellinRemainderRayIntegrand s r) := hsource
      _ = (2 * (Real.pi : ℂ) * Complex.I) *
          (Complex.Gamma s * riemannZeta s -
            ∫ r : ℝ in Ioi 0,
              deBruijnNewmanTitchmarshMellinRemainderRayIntegrand s r) := by ring)

end

end LeanLab.Riemann
