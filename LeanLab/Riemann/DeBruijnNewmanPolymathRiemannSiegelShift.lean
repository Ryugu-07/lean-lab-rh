import LeanLab.Riemann.DeBruijnNewmanPolymathRiemannSiegelContour
import LeanLab.Riemann.TruncatedPerron
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

set_option linter.style.header false

/-!
# The adjacent Riemann--Siegel contour shift

This file attacks the single-pole shift between adjacent source contours. The complex-linear
coordinate `w = (N+1) + d*z` turns a suitably staggered finite truncation into an axis-aligned
rectangle and turns the crossed principal part into `c / z`.
-/

open Complex Filter MeasureTheory Real Set Topology
open scoped Interval

namespace LeanLab.Riemann

noncomputable section

/-- Half the perpendicular separation of adjacent source lines in the rotated coordinate. -/
def deBruijnNewmanRiemannSiegelRotatedHalfWidth : ℝ := Real.sqrt 2 / 4

/-- The parameter stagger between the two long sides of the rotated rectangle. -/
def deBruijnNewmanRiemannSiegelParameterStagger : ℝ := Real.sqrt 2 / 2

/-- Pull the source plane back through the complex-linear coordinate centered at the crossed
pole. -/
def deBruijnNewmanRiemannSiegelPullbackPoint (N : ℕ) (z : ℂ) : ℂ :=
  (N + 1 : ℕ) + deBruijnNewmanRiemannSiegelDirection * z

/-- The source denominator in the rotated coordinate. -/
def deBruijnNewmanRiemannSiegelPullbackDenominator (N : ℕ) (z : ℂ) : ℂ :=
  deBruijnNewmanRiemannSiegelDenominator
    (deBruijnNewmanRiemannSiegelPullbackPoint N z)

/-- The source numerator, including the Jacobian, in the rotated coordinate. -/
def deBruijnNewmanRiemannSiegelPullbackNumerator (N : ℕ) (s z : ℂ) : ℂ :=
  deBruijnNewmanRiemannSiegelNumerator s
      (deBruijnNewmanRiemannSiegelPullbackPoint N z) *
    deBruijnNewmanRiemannSiegelDirection

/-- The pulled-back raw kernel, including the complex Jacobian. -/
def deBruijnNewmanRiemannSiegelPullbackKernel (N : ℕ) (s z : ℂ) : ℂ :=
  deBruijnNewmanRiemannSiegelKernel s
      (deBruijnNewmanRiemannSiegelPullbackPoint N z) *
    deBruijnNewmanRiemannSiegelDirection

/-- The open horizontal band containing only the crossed denominator zero. -/
def deBruijnNewmanRiemannSiegelPullbackBand : Set ℂ :=
  {z | |z.im| < deBruijnNewmanRiemannSiegelParameterStagger}

theorem deBruijnNewmanRiemannSiegelRotatedHalfWidth_pos :
    0 < deBruijnNewmanRiemannSiegelRotatedHalfWidth := by
  rw [deBruijnNewmanRiemannSiegelRotatedHalfWidth]
  positivity

theorem deBruijnNewmanRiemannSiegelParameterStagger_eq_two_mul_halfWidth :
    deBruijnNewmanRiemannSiegelParameterStagger =
      2 * deBruijnNewmanRiemannSiegelRotatedHalfWidth := by
  rw [deBruijnNewmanRiemannSiegelParameterStagger,
    deBruijnNewmanRiemannSiegelRotatedHalfWidth]
  ring

theorem isOpen_deBruijnNewmanRiemannSiegelPullbackBand :
    IsOpen deBruijnNewmanRiemannSiegelPullbackBand := by
  exact isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const

theorem zero_mem_deBruijnNewmanRiemannSiegelPullbackBand :
    (0 : ℂ) ∈ deBruijnNewmanRiemannSiegelPullbackBand := by
  rw [deBruijnNewmanRiemannSiegelPullbackBand]
  simp only [Complex.zero_im, abs_zero, Set.mem_setOf_eq]
  rw [deBruijnNewmanRiemannSiegelParameterStagger]
  positivity

theorem deBruijnNewmanRiemannSiegelPullbackBand_mem_nhds :
    deBruijnNewmanRiemannSiegelPullbackBand ∈ 𝓝 (0 : ℂ) :=
  isOpen_deBruijnNewmanRiemannSiegelPullbackBand.mem_nhds
    zero_mem_deBruijnNewmanRiemannSiegelPullbackBand

@[simp] theorem deBruijnNewmanRiemannSiegelPullbackPoint_zero (N : ℕ) :
    deBruijnNewmanRiemannSiegelPullbackPoint N 0 = (N + 1 : ℕ) := by
  simp [deBruijnNewmanRiemannSiegelPullbackPoint]

@[simp] theorem deBruijnNewmanRiemannSiegelPullbackPoint_re (N : ℕ) (z : ℂ) :
    (deBruijnNewmanRiemannSiegelPullbackPoint N z).re =
      (N + 1 : ℕ) - (Real.sqrt 2 / 2) * z.re + (Real.sqrt 2 / 2) * z.im := by
  rw [deBruijnNewmanRiemannSiegelPullbackPoint]
  simp only [Complex.add_re, Complex.natCast_re, Complex.mul_re,
    deBruijnNewmanRiemannSiegelDirection_re,
    deBruijnNewmanRiemannSiegelDirection_im]
  ring

@[simp] theorem deBruijnNewmanRiemannSiegelPullbackPoint_im (N : ℕ) (z : ℂ) :
    (deBruijnNewmanRiemannSiegelPullbackPoint N z).im =
      -(Real.sqrt 2 / 2) * (z.re + z.im) := by
  rw [deBruijnNewmanRiemannSiegelPullbackPoint]
  simp only [Complex.add_im, Complex.natCast_im, Complex.mul_im,
    deBruijnNewmanRiemannSiegelDirection_re,
    deBruijnNewmanRiemannSiegelDirection_im, zero_add]
  ring

/-- Every zero of the source denominator is an integral point. -/
theorem exists_int_of_deBruijnNewmanRiemannSiegelDenominator_eq_zero
    {w : ℂ} (hw : deBruijnNewmanRiemannSiegelDenominator w = 0) :
    ∃ n : ℤ, w = n := by
  have hexp :
      Complex.exp (((Real.pi : ℂ) * Complex.I) * w) =
        Complex.exp (-((Real.pi : ℂ) * Complex.I) * w) :=
    sub_eq_zero.mp hw
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
  have hfactor : (2 * (Real.pi : ℂ) * Complex.I) * (w - (n : ℂ)) = 0 := by
    calc
      (2 * (Real.pi : ℂ) * Complex.I) * (w - (n : ℂ)) =
          (((Real.pi : ℂ) * Complex.I) * w) -
            (-((Real.pi : ℂ) * Complex.I) * w +
              (n : ℂ) * (2 * Real.pi * Complex.I)) := by ring
      _ = 0 := by rw [← hn]; ring
  have hp : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  exact ⟨n, sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left hp)⟩

/-- The pulled-back source point stays in the principal-power slit plane throughout the band. -/
theorem deBruijnNewmanRiemannSiegelPullbackPoint_mem_slitPlane
    (N : ℕ) {z : ℂ} (hz : z ∈ deBruijnNewmanRiemannSiegelPullbackBand) :
    deBruijnNewmanRiemannSiegelPullbackPoint N z ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases him : (deBruijnNewmanRiemannSiegelPullbackPoint N z).im = 0
  · left
    rw [deBruijnNewmanRiemannSiegelPullbackPoint_im] at him
    rw [deBruijnNewmanRiemannSiegelPullbackPoint_re]
    rw [deBruijnNewmanRiemannSiegelPullbackBand] at hz
    simp only [Set.mem_setOf_eq] at hz
    have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hcoord : z.re = -z.im := by
      have hcoeff : -(Real.sqrt 2 / 2) ≠ 0 := by
        exact neg_ne_zero.mpr (div_ne_zero hsqrt.ne' (by norm_num))
      have := (mul_eq_zero.mp him).resolve_left hcoeff
      linarith
    have hzlower : -(Real.sqrt 2 / 2) < z.im := by
      rw [deBruijnNewmanRiemannSiegelParameterStagger] at hz
      exact (abs_lt.mp hz).1
    have hzlower_mul := mul_lt_mul_of_pos_left hzlower hsqrt
    have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
    have hterm : -(1 : ℝ) < Real.sqrt 2 * z.im := by
      nlinarith [hzlower_mul]
    have hbase : (1 : ℝ) ≤ (N + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
    have hrewrite :
        (N + 1 : ℕ) - (Real.sqrt 2 / 2) * (-z.im) +
            (Real.sqrt 2 / 2) * z.im =
          (N + 1 : ℕ) + Real.sqrt 2 * z.im := by ring
    rw [hcoord]
    rw [hrewrite]
    linarith
  · exact Or.inr him

/-- Inside the open pullback band, the transformed denominator vanishes only at the origin. -/
theorem deBruijnNewmanRiemannSiegelPullbackDenominator_ne_zero_of_ne
    (N : ℕ) {z : ℂ} (hz : z ∈ deBruijnNewmanRiemannSiegelPullbackBand) (hz0 : z ≠ 0) :
    deBruijnNewmanRiemannSiegelPullbackDenominator N z ≠ 0 := by
  intro hzero
  obtain ⟨n, hn⟩ := exists_int_of_deBruijnNewmanRiemannSiegelDenominator_eq_zero hzero
  have him := congrArg Complex.im hn
  have hre := congrArg Complex.re hn
  rw [deBruijnNewmanRiemannSiegelPullbackPoint_im] at him
  rw [deBruijnNewmanRiemannSiegelPullbackPoint_re] at hre
  simp only [Complex.intCast_im] at him
  simp only [Complex.intCast_re] at hre
  rw [deBruijnNewmanRiemannSiegelPullbackBand] at hz
  simp only [Set.mem_setOf_eq] at hz
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hcoord : z.re = -z.im := by
    have hcoeff : -(Real.sqrt 2 / 2) ≠ 0 := by
      exact neg_ne_zero.mpr (div_ne_zero hsqrt.ne' (by norm_num))
    have := (mul_eq_zero.mp him).resolve_left hcoeff
    linarith
  have him_bound : |(n : ℝ) - (N + 1 : ℕ)| < 1 := by
    have hzlower : -(Real.sqrt 2 / 2) < z.im := by
      rw [deBruijnNewmanRiemannSiegelParameterStagger] at hz
      exact (abs_lt.mp hz).1
    have hzupper : z.im < Real.sqrt 2 / 2 := by
      rw [deBruijnNewmanRiemannSiegelParameterStagger] at hz
      exact (abs_lt.mp hz).2
    have hzlower_mul := mul_lt_mul_of_pos_left hzlower hsqrt
    have hzupper_mul := mul_lt_mul_of_pos_left hzupper hsqrt
    rw [abs_lt]
    constructor <;> nlinarith [hzlower_mul, hzupper_mul]
  have hn_eq : n = (N + 1 : ℕ) := by
    have hn_lower : -(1 : ℤ) < n - (N + 1 : ℕ) := by
      exact_mod_cast (abs_lt.mp him_bound |>.1)
    have hn_upper : n - (N + 1 : ℕ) < 1 := by
      exact_mod_cast (abs_lt.mp him_bound |>.2)
    omega
  subst n
  norm_num at hre
  rw [hcoord] at hre
  have hprod : Real.sqrt 2 * z.im = 0 := by nlinarith
  have hzim : z.im = 0 := (mul_eq_zero.mp hprod).resolve_left hsqrt.ne'
  have hzre : z.re = 0 := by linarith
  apply hz0
  apply Complex.ext <;> simp [hzre, hzim]

theorem hasDerivAt_deBruijnNewmanRiemannSiegelPullbackPoint (N : ℕ) (z : ℂ) :
    HasDerivAt (deBruijnNewmanRiemannSiegelPullbackPoint N)
      deBruijnNewmanRiemannSiegelDirection z := by
  unfold deBruijnNewmanRiemannSiegelPullbackPoint
  convert! ((hasDerivAt_id z).const_mul deBruijnNewmanRiemannSiegelDirection).const_add
    (((N + 1 : ℕ) : ℂ))
  simp

theorem hasDerivAt_deBruijnNewmanRiemannSiegelPullbackDenominator (N : ℕ) (z : ℂ) :
    HasDerivAt (deBruijnNewmanRiemannSiegelPullbackDenominator N)
      ((Complex.exp (((Real.pi : ℂ) * Complex.I) *
            deBruijnNewmanRiemannSiegelPullbackPoint N z) *
          ((Real.pi : ℂ) * Complex.I) -
        Complex.exp (-((Real.pi : ℂ) * Complex.I) *
            deBruijnNewmanRiemannSiegelPullbackPoint N z) *
          (-((Real.pi : ℂ) * Complex.I))) *
        deBruijnNewmanRiemannSiegelDirection) z := by
  unfold deBruijnNewmanRiemannSiegelPullbackDenominator
  exact (hasDerivAt_deBruijnNewmanRiemannSiegelDenominator
      (deBruijnNewmanRiemannSiegelPullbackPoint N z)).comp z
    (hasDerivAt_deBruijnNewmanRiemannSiegelPullbackPoint N z)

theorem deriv_deBruijnNewmanRiemannSiegelPullbackDenominator_zero (N : ℕ) :
    deriv (deBruijnNewmanRiemannSiegelPullbackDenominator N) 0 =
      deriv deBruijnNewmanRiemannSiegelDenominator (N + 1 : ℕ) *
        deBruijnNewmanRiemannSiegelDirection := by
  calc
    deriv (deBruijnNewmanRiemannSiegelPullbackDenominator N) 0 =
        (Complex.exp (((Real.pi : ℂ) * Complex.I) * (N + 1 : ℕ)) *
              ((Real.pi : ℂ) * Complex.I) -
            Complex.exp (-((Real.pi : ℂ) * Complex.I) * (N + 1 : ℕ)) *
              (-((Real.pi : ℂ) * Complex.I))) *
          deBruijnNewmanRiemannSiegelDirection := by
            simpa using
              (hasDerivAt_deBruijnNewmanRiemannSiegelPullbackDenominator N 0).deriv
    _ = deriv deBruijnNewmanRiemannSiegelDenominator (N + 1 : ℕ) *
        deBruijnNewmanRiemannSiegelDirection := by
          rw [(hasDerivAt_deBruijnNewmanRiemannSiegelDenominator (N + 1 : ℕ)).deriv]

@[simp] theorem deBruijnNewmanRiemannSiegelPullbackDenominator_zero (N : ℕ) :
    deBruijnNewmanRiemannSiegelPullbackDenominator N 0 = 0 := by
  rw [deBruijnNewmanRiemannSiegelPullbackDenominator,
    deBruijnNewmanRiemannSiegelPullbackPoint_zero]
  exact deBruijnNewmanRiemannSiegelDenominator_natCast (N + 1)

theorem deBruijnNewmanRiemannSiegelDirection_ne_zero :
    deBruijnNewmanRiemannSiegelDirection ≠ 0 := by
  intro h
  have := congrArg norm h
  simp at this

/-- The divided denominator has no zero in the full pullback band, including at the crossed pole. -/
theorem dslope_deBruijnNewmanRiemannSiegelPullbackDenominator_ne_zero
    (N : ℕ) {z : ℂ} (hz : z ∈ deBruijnNewmanRiemannSiegelPullbackBand) :
    dslope (deBruijnNewmanRiemannSiegelPullbackDenominator N) 0 z ≠ 0 := by
  by_cases hz0 : z = 0
  · subst z
    rw [dslope_same, deriv_deBruijnNewmanRiemannSiegelPullbackDenominator_zero,
      deriv_deBruijnNewmanRiemannSiegelDenominator_natCast]
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
          Complex.I_ne_zero)
        (pow_ne_zero _ (by norm_num)))
      deBruijnNewmanRiemannSiegelDirection_ne_zero
  · intro hslope
    have hrel := sub_smul_dslope
      (deBruijnNewmanRiemannSiegelPullbackDenominator N) 0 z
    have hzero : deBruijnNewmanRiemannSiegelPullbackDenominator N z = 0 := by
      simpa [hslope] using hrel.symm
    exact deBruijnNewmanRiemannSiegelPullbackDenominator_ne_zero_of_ne N hz hz0 hzero

/-- The analytic numerator divided by the denominator's removable first slope. -/
def deBruijnNewmanRiemannSiegelPullbackCore (N : ℕ) (s z : ℂ) : ℂ :=
  deBruijnNewmanRiemannSiegelPullbackNumerator N s z /
    dslope (deBruijnNewmanRiemannSiegelPullbackDenominator N) 0 z

/-- The pole-subtracted pullback kernel, with its value at the pole supplied by `dslope`. -/
def deBruijnNewmanRiemannSiegelPullbackRemovable (N : ℕ) (s z : ℂ) : ℂ :=
  dslope (deBruijnNewmanRiemannSiegelPullbackCore N s) 0 z

theorem differentiableOn_deBruijnNewmanRiemannSiegelPullbackPoint (N : ℕ) :
    DifferentiableOn ℂ (deBruijnNewmanRiemannSiegelPullbackPoint N)
      deBruijnNewmanRiemannSiegelPullbackBand :=
  fun z _ ↦ (hasDerivAt_deBruijnNewmanRiemannSiegelPullbackPoint N z).differentiableAt
    |>.differentiableWithinAt

theorem differentiableOn_deBruijnNewmanRiemannSiegelPullbackNumerator (N : ℕ) (s : ℂ) :
    DifferentiableOn ℂ (deBruijnNewmanRiemannSiegelPullbackNumerator N s)
      deBruijnNewmanRiemannSiegelPullbackBand := by
  have hpull := differentiableOn_deBruijnNewmanRiemannSiegelPullbackPoint N
  have hpow : DifferentiableOn ℂ
      (fun z ↦ deBruijnNewmanRiemannSiegelPullbackPoint N z ^ (-s))
      deBruijnNewmanRiemannSiegelPullbackBand :=
    hpull.cpow_const fun _ hz ↦
      deBruijnNewmanRiemannSiegelPullbackPoint_mem_slitPlane N hz
  have hexp : DifferentiableOn ℂ
      (fun z ↦ Complex.exp
        (Complex.I * Real.pi * deBruijnNewmanRiemannSiegelPullbackPoint N z ^ 2))
      deBruijnNewmanRiemannSiegelPullbackBand := by
    fun_prop
  exact (hpow.mul hexp).mul_const deBruijnNewmanRiemannSiegelDirection

theorem differentiableOn_deBruijnNewmanRiemannSiegelPullbackDenominator (N : ℕ) :
    DifferentiableOn ℂ (deBruijnNewmanRiemannSiegelPullbackDenominator N)
      deBruijnNewmanRiemannSiegelPullbackBand :=
  fun z _ ↦ (hasDerivAt_deBruijnNewmanRiemannSiegelPullbackDenominator N z).differentiableAt
    |>.differentiableWithinAt

theorem differentiableOn_deBruijnNewmanRiemannSiegelPullbackCore (N : ℕ) (s : ℂ) :
    DifferentiableOn ℂ (deBruijnNewmanRiemannSiegelPullbackCore N s)
      deBruijnNewmanRiemannSiegelPullbackBand := by
  have hdenSlope : DifferentiableOn ℂ
      (dslope (deBruijnNewmanRiemannSiegelPullbackDenominator N) 0)
      deBruijnNewmanRiemannSiegelPullbackBand :=
    (Complex.differentiableOn_dslope
      deBruijnNewmanRiemannSiegelPullbackBand_mem_nhds).mpr
      (differentiableOn_deBruijnNewmanRiemannSiegelPullbackDenominator N)
  exact (differentiableOn_deBruijnNewmanRiemannSiegelPullbackNumerator N s).div
    hdenSlope fun z hz ↦
      dslope_deBruijnNewmanRiemannSiegelPullbackDenominator_ne_zero N hz

/-- The explicitly pole-subtracted pullback kernel is holomorphic throughout the band. -/
theorem differentiableOn_deBruijnNewmanRiemannSiegelPullbackRemovable (N : ℕ) (s : ℂ) :
    DifferentiableOn ℂ (deBruijnNewmanRiemannSiegelPullbackRemovable N s)
      deBruijnNewmanRiemannSiegelPullbackBand := by
  change DifferentiableOn ℂ
    (dslope (deBruijnNewmanRiemannSiegelPullbackCore N s) 0)
      deBruijnNewmanRiemannSiegelPullbackBand
  rw [Complex.differentiableOn_dslope
    deBruijnNewmanRiemannSiegelPullbackBand_mem_nhds]
  exact differentiableOn_deBruijnNewmanRiemannSiegelPullbackCore N s

@[simp] theorem deBruijnNewmanRiemannSiegelPullbackCore_zero (N : ℕ) (s : ℂ) :
    deBruijnNewmanRiemannSiegelPullbackCore N s 0 =
      ((N + 1 : ℕ) : ℂ) ^ (-s) / (2 * (Real.pi : ℂ) * Complex.I) := by
  rw [deBruijnNewmanRiemannSiegelPullbackCore,
    deBruijnNewmanRiemannSiegelPullbackNumerator,
    deBruijnNewmanRiemannSiegelPullbackPoint_zero, dslope_same,
    deriv_deBruijnNewmanRiemannSiegelPullbackDenominator_zero]
  calc
    (deBruijnNewmanRiemannSiegelNumerator s (N + 1 : ℕ) *
          deBruijnNewmanRiemannSiegelDirection) /
        (deriv deBruijnNewmanRiemannSiegelDenominator (N + 1 : ℕ) *
          deBruijnNewmanRiemannSiegelDirection) =
        deBruijnNewmanRiemannSiegelNumerator s (N + 1 : ℕ) /
          deriv deBruijnNewmanRiemannSiegelDenominator (N + 1 : ℕ) := by
            field_simp [deBruijnNewmanRiemannSiegelDirection_ne_zero]
    _ = ((N + 1 : ℕ) : ℂ) ^ (-s) / (2 * (Real.pi : ℂ) * Complex.I) :=
      deBruijnNewmanRiemannSiegel_residueCoefficient (Nat.succ_pos N) s

theorem deBruijnNewmanRiemannSiegelPullbackCore_eq_mul_kernel
    (N : ℕ) (s : ℂ) {z : ℂ} (hz : z ∈ deBruijnNewmanRiemannSiegelPullbackBand)
    (hz0 : z ≠ 0) :
    deBruijnNewmanRiemannSiegelPullbackCore N s z =
      z * deBruijnNewmanRiemannSiegelPullbackKernel N s z := by
  have hden := deBruijnNewmanRiemannSiegelPullbackDenominator_ne_zero_of_ne N hz hz0
  change
    (deBruijnNewmanRiemannSiegelNumerator s
          (deBruijnNewmanRiemannSiegelPullbackPoint N z) *
        deBruijnNewmanRiemannSiegelDirection) /
      dslope (deBruijnNewmanRiemannSiegelPullbackDenominator N) 0 z =
    z * ((deBruijnNewmanRiemannSiegelNumerator s
          (deBruijnNewmanRiemannSiegelPullbackPoint N z) /
        deBruijnNewmanRiemannSiegelPullbackDenominator N z) *
      deBruijnNewmanRiemannSiegelDirection)
  rw [dslope_of_ne _ hz0]
  simp only [slope, sub_zero, vsub_eq_sub, smul_eq_mul,
    deBruijnNewmanRiemannSiegelPullbackDenominator_zero]
  field_simp [hz0, hden]

/-- Away from the crossed pole, the pulled-back raw kernel is its exact principal part plus the
holomorphic removable remainder. -/
theorem deBruijnNewmanRiemannSiegelPullbackKernel_eq_principalPart_add_removable
    (N : ℕ) (s : ℂ) {z : ℂ} (hz : z ∈ deBruijnNewmanRiemannSiegelPullbackBand)
    (hz0 : z ≠ 0) :
    deBruijnNewmanRiemannSiegelPullbackKernel N s z =
      (((N + 1 : ℕ) : ℂ) ^ (-s) / (2 * (Real.pi : ℂ) * Complex.I)) / z +
        deBruijnNewmanRiemannSiegelPullbackRemovable N s z := by
  have hcore := deBruijnNewmanRiemannSiegelPullbackCore_eq_mul_kernel N s hz hz0
  have hslope := sub_smul_dslope
    (deBruijnNewmanRiemannSiegelPullbackCore N s) 0 z
  rw [deBruijnNewmanRiemannSiegelPullbackCore_zero] at hslope
  simp only [sub_zero, smul_eq_mul] at hslope
  let c : ℂ := ((N + 1 : ℕ) : ℂ) ^ (-s) / (2 * (Real.pi : ℂ) * Complex.I)
  change z * deBruijnNewmanRiemannSiegelPullbackRemovable N s z =
      deBruijnNewmanRiemannSiegelPullbackCore N s z -
        c at hslope
  rw [hcore] at hslope
  have hsub :
      (deBruijnNewmanRiemannSiegelPullbackKernel N s z -
          deBruijnNewmanRiemannSiegelPullbackRemovable N s z) * z = c := by
    calc
      (deBruijnNewmanRiemannSiegelPullbackKernel N s z -
          deBruijnNewmanRiemannSiegelPullbackRemovable N s z) * z =
          z * deBruijnNewmanRiemannSiegelPullbackKernel N s z -
            z * deBruijnNewmanRiemannSiegelPullbackRemovable N s z := by ring
      _ = c := by rw [hslope]; ring
  have heq :
      deBruijnNewmanRiemannSiegelPullbackKernel N s z -
          deBruijnNewmanRiemannSiegelPullbackRemovable N s z = c / z :=
    (eq_div_iff hz0).2 hsub
  dsimp [c] at heq ⊢
  linear_combination heq

theorem deBruijnNewmanRiemannSiegelRotatedHalfWidth_lt_parameterStagger :
    deBruijnNewmanRiemannSiegelRotatedHalfWidth <
      deBruijnNewmanRiemannSiegelParameterStagger := by
  rw [deBruijnNewmanRiemannSiegelRotatedHalfWidth,
    deBruijnNewmanRiemannSiegelParameterStagger]
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  linarith

theorem intervalIntegrable_deBruijnNewmanRiemannSiegelPullbackRemovable_affine
    (N : ℕ) (s u v : ℂ) (p q : ℝ)
    (hmap : ∀ t ∈ Set.uIcc p q,
      u + (t : ℂ) * v ∈ deBruijnNewmanRiemannSiegelPullbackBand) :
    IntervalIntegrable
      (fun t : ℝ ↦ deBruijnNewmanRiemannSiegelPullbackRemovable N s
        (u + (t : ℂ) * v)) volume p q := by
  apply ContinuousOn.intervalIntegrable
  apply (differentiableOn_deBruijnNewmanRiemannSiegelPullbackRemovable N s).continuousOn.comp
    (continuousOn_const.add (Complex.continuous_ofReal.continuousOn.mul continuousOn_const))
  exact hmap

theorem intervalIntegrable_inv_affine
    (u v : ℂ) (p q : ℝ)
    (hne : ∀ t ∈ Set.uIcc p q, u + (t : ℂ) * v ≠ 0) :
    IntervalIntegrable (fun t : ℝ ↦ (u + (t : ℂ) * v)⁻¹) volume p q := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.inv₀
  · exact continuousOn_const.add
      (Complex.continuous_ofReal.continuousOn.mul continuousOn_const)
  · exact hne

/-- Integrate the exact pole decomposition along any affine segment contained in the pullback
band and avoiding the crossed pole. -/
theorem integral_deBruijnNewmanRiemannSiegelPullbackKernel_affine_eq
    (N : ℕ) (s u v : ℂ) (p q : ℝ)
    (hmap : ∀ t ∈ Set.uIcc p q,
      u + (t : ℂ) * v ∈ deBruijnNewmanRiemannSiegelPullbackBand)
    (hne : ∀ t ∈ Set.uIcc p q, u + (t : ℂ) * v ≠ 0) :
    (∫ t : ℝ in p..q,
        deBruijnNewmanRiemannSiegelPullbackKernel N s (u + (t : ℂ) * v)) =
      (((N + 1 : ℕ) : ℂ) ^ (-s) / (2 * (Real.pi : ℂ) * Complex.I)) *
          (∫ t : ℝ in p..q, (u + (t : ℂ) * v)⁻¹) +
        ∫ t : ℝ in p..q,
          deBruijnNewmanRiemannSiegelPullbackRemovable N s (u + (t : ℂ) * v) := by
  have hinv := intervalIntegrable_inv_affine u v p q hne
  have hrem :=
    intervalIntegrable_deBruijnNewmanRiemannSiegelPullbackRemovable_affine N s u v p q hmap
  calc
    (∫ t : ℝ in p..q,
        deBruijnNewmanRiemannSiegelPullbackKernel N s (u + (t : ℂ) * v)) =
        ∫ t : ℝ in p..q,
          ((((N + 1 : ℕ) : ℂ) ^ (-s) / (2 * (Real.pi : ℂ) * Complex.I)) *
              (u + (t : ℂ) * v)⁻¹ +
            deBruijnNewmanRiemannSiegelPullbackRemovable N s (u + (t : ℂ) * v)) := by
              apply intervalIntegral.integral_congr
              intro t ht
              change deBruijnNewmanRiemannSiegelPullbackKernel N s (u + (t : ℂ) * v) =
                (((N + 1 : ℕ) : ℂ) ^ (-s) / (2 * (Real.pi : ℂ) * Complex.I)) *
                    (u + (t : ℂ) * v)⁻¹ +
                  deBruijnNewmanRiemannSiegelPullbackRemovable N s (u + (t : ℂ) * v)
              rw [deBruijnNewmanRiemannSiegelPullbackKernel_eq_principalPart_add_removable
                N s (hmap t ht) (hne t ht)]
              ring
    _ = (∫ t : ℝ in p..q,
          (((N + 1 : ℕ) : ℂ) ^ (-s) / (2 * (Real.pi : ℂ) * Complex.I)) *
            (u + (t : ℂ) * v)⁻¹) +
        ∫ t : ℝ in p..q,
          deBruijnNewmanRiemannSiegelPullbackRemovable N s (u + (t : ℂ) * v) := by
            rw [intervalIntegral.integral_add
              (hinv.const_mul
                (((N + 1 : ℕ) : ℂ) ^ (-s) / (2 * (Real.pi : ℂ) * Complex.I))) hrem]
    _ = (((N + 1 : ℕ) : ℂ) ^ (-s) / (2 * (Real.pi : ℂ) * Complex.I)) *
          (∫ t : ℝ in p..q, (u + (t : ℂ) * v)⁻¹) +
        ∫ t : ℝ in p..q,
          deBruijnNewmanRiemannSiegelPullbackRemovable N s (u + (t : ℂ) * v) := by
            rw [intervalIntegral.integral_const_mul]

/-- Cauchy--Goursat for the removable pullback on the finite rotated rectangle. -/
theorem deBruijnNewmanRiemannSiegelPullbackRemovable_boundary_rect_eq_zero
    (N : ℕ) (s : ℂ) (l R : ℝ) :
    (∫ x : ℝ in l..R,
        deBruijnNewmanRiemannSiegelPullbackRemovable N s
          (x + (-deBruijnNewmanRiemannSiegelRotatedHalfWidth) * Complex.I)) -
      (∫ x : ℝ in l..R,
        deBruijnNewmanRiemannSiegelPullbackRemovable N s
          (x + deBruijnNewmanRiemannSiegelRotatedHalfWidth * Complex.I)) +
      Complex.I * (∫ t : ℝ in
          -deBruijnNewmanRiemannSiegelRotatedHalfWidth..
            deBruijnNewmanRiemannSiegelRotatedHalfWidth,
        deBruijnNewmanRiemannSiegelPullbackRemovable N s (R + t * Complex.I)) -
      Complex.I * (∫ t : ℝ in
          -deBruijnNewmanRiemannSiegelRotatedHalfWidth..
            deBruijnNewmanRiemannSiegelRotatedHalfWidth,
        deBruijnNewmanRiemannSiegelPullbackRemovable N s (l + t * Complex.I)) = 0 := by
  let z : ℂ := Complex.mk l (-deBruijnNewmanRiemannSiegelRotatedHalfWidth)
  let w : ℂ := Complex.mk R deBruijnNewmanRiemannSiegelRotatedHalfWidth
  have hdiff : DifferentiableOn ℂ
      (deBruijnNewmanRiemannSiegelPullbackRemovable N s)
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]]) := by
    apply (differentiableOn_deBruijnNewmanRiemannSiegelPullbackRemovable N s).mono
    intro q hq
    rw [Complex.mem_reProdIm] at hq
    rw [deBruijnNewmanRiemannSiegelPullbackBand]
    simp only [Set.mem_setOf_eq]
    have hhalf := deBruijnNewmanRiemannSiegelRotatedHalfWidth_pos
    have hlt := deBruijnNewmanRiemannSiegelRotatedHalfWidth_lt_parameterStagger
    have him : -deBruijnNewmanRiemannSiegelRotatedHalfWidth ≤ q.im ∧
        q.im ≤ deBruijnNewmanRiemannSiegelRotatedHalfWidth := by
      have him' := hq.2
      rw [uIcc_of_le (neg_le_self hhalf.le)] at him'
      simpa only [z, w, Set.mem_Icc] using him'
    rw [abs_lt]
    constructor <;> linarith
  have hboundary := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (deBruijnNewmanRiemannSiegelPullbackRemovable N s) z w hdiff
  simpa only [z, w, Complex.ofReal_neg, smul_eq_mul] using hboundary

/-- The finite rotated rectangle crosses exactly one source pole and therefore has the exact raw
residue `(N+1)^(-s)`. -/
theorem deBruijnNewmanRiemannSiegelPullbackKernel_boundary_rect
    (N : ℕ) (s : ℂ) {l R : ℝ} (hl : l < 0) (hR : 0 < R) :
    (∫ x : ℝ in l..R,
        deBruijnNewmanRiemannSiegelPullbackKernel N s
          (x + (-deBruijnNewmanRiemannSiegelRotatedHalfWidth) * Complex.I)) -
      (∫ x : ℝ in l..R,
        deBruijnNewmanRiemannSiegelPullbackKernel N s
          (x + deBruijnNewmanRiemannSiegelRotatedHalfWidth * Complex.I)) +
      Complex.I * (∫ t : ℝ in
          -deBruijnNewmanRiemannSiegelRotatedHalfWidth..
            deBruijnNewmanRiemannSiegelRotatedHalfWidth,
        deBruijnNewmanRiemannSiegelPullbackKernel N s (R + t * Complex.I)) -
      Complex.I * (∫ t : ℝ in
          -deBruijnNewmanRiemannSiegelRotatedHalfWidth..
            deBruijnNewmanRiemannSiegelRotatedHalfWidth,
        deBruijnNewmanRiemannSiegelPullbackKernel N s (l + t * Complex.I)) =
      ((N + 1 : ℕ) : ℂ) ^ (-s) := by
  let h := deBruijnNewmanRiemannSiegelRotatedHalfWidth
  have hh : 0 < h := deBruijnNewmanRiemannSiegelRotatedHalfWidth_pos
  have hha : h < deBruijnNewmanRiemannSiegelParameterStagger :=
    deBruijnNewmanRiemannSiegelRotatedHalfWidth_lt_parameterStagger
  have hhorizontal (y : ℝ) (hy : |y| = h) :
      ∀ x ∈ Set.uIcc l R,
        (y : ℂ) * Complex.I + (x : ℂ) * 1 ∈
          deBruijnNewmanRiemannSiegelPullbackBand := by
    intro x _
    rw [deBruijnNewmanRiemannSiegelPullbackBand]
    simp only [Set.mem_setOf_eq, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.ofReal_im, mul_one, add_zero]
    simpa [hy] using hha
  have hvertical (c : ℝ) :
      ∀ t ∈ Set.uIcc (-h) h,
        (c : ℂ) + (t : ℂ) * Complex.I ∈
          deBruijnNewmanRiemannSiegelPullbackBand := by
    intro t ht
    rw [deBruijnNewmanRiemannSiegelPullbackBand]
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
  have hbottom := integral_deBruijnNewmanRiemannSiegelPullbackKernel_affine_eq
    N s (((-h : ℝ) : ℂ) * Complex.I) 1 l R (hhorizontal (-h) (by simp [h, hh.le]))
      hbottom_ne
  have htop := integral_deBruijnNewmanRiemannSiegelPullbackKernel_affine_eq
    N s ((h : ℂ) * Complex.I) 1 l R (hhorizontal h (abs_of_pos hh)) htop_ne
  have hright := integral_deBruijnNewmanRiemannSiegelPullbackKernel_affine_eq
    N s R Complex.I (-h) h (hvertical R) hright_ne
  have hleft := integral_deBruijnNewmanRiemannSiegelPullbackKernel_affine_eq
    N s l Complex.I (-h) h (hvertical l) hleft_ne
  have hrem := deBruijnNewmanRiemannSiegelPullbackRemovable_boundary_rect_eq_zero N s l R
  have hinv := integral_inv_boundary_rect_eq_two_pi_mul_I hl hR hh
  let c : ℂ := ((N + 1 : ℕ) : ℂ) ^ (-s) / (2 * (Real.pi : ℂ) * Complex.I)
  change
    (∫ x : ℝ in l..R,
        deBruijnNewmanRiemannSiegelPullbackKernel N s (x + (-h) * Complex.I)) -
      (∫ x : ℝ in l..R,
        deBruijnNewmanRiemannSiegelPullbackKernel N s (x + h * Complex.I)) +
      Complex.I * (∫ t : ℝ in -h..h,
        deBruijnNewmanRiemannSiegelPullbackKernel N s (R + t * Complex.I)) -
      Complex.I * (∫ t : ℝ in -h..h,
        deBruijnNewmanRiemannSiegelPullbackKernel N s (l + t * Complex.I)) = _
  have hbottom' :
      (∫ x : ℝ in l..R,
        deBruijnNewmanRiemannSiegelPullbackKernel N s (x + (-h) * Complex.I)) =
        c * (∫ x : ℝ in l..R, (x + (-h) * Complex.I)⁻¹) +
          ∫ x : ℝ in l..R,
            deBruijnNewmanRiemannSiegelPullbackRemovable N s (x + (-h) * Complex.I) := by
    simpa only [h, c, one_mul, mul_one, Complex.ofReal_neg, add_comm] using hbottom
  have htop' :
      (∫ x : ℝ in l..R,
        deBruijnNewmanRiemannSiegelPullbackKernel N s (x + h * Complex.I)) =
        c * (∫ x : ℝ in l..R, (x + h * Complex.I)⁻¹) +
          ∫ x : ℝ in l..R,
            deBruijnNewmanRiemannSiegelPullbackRemovable N s (x + h * Complex.I) := by
    simpa only [h, c, one_mul, mul_one, add_comm] using htop
  have hright' :
      (∫ t : ℝ in -h..h,
        deBruijnNewmanRiemannSiegelPullbackKernel N s (R + t * Complex.I)) =
        c * (∫ t : ℝ in -h..h, (R + t * Complex.I)⁻¹) +
          ∫ t : ℝ in -h..h,
            deBruijnNewmanRiemannSiegelPullbackRemovable N s (R + t * Complex.I) := by
    simpa only [c] using hright
  have hleft' :
      (∫ t : ℝ in -h..h,
        deBruijnNewmanRiemannSiegelPullbackKernel N s (l + t * Complex.I)) =
        c * (∫ t : ℝ in -h..h, (l + t * Complex.I)⁻¹) +
          ∫ t : ℝ in -h..h,
            deBruijnNewmanRiemannSiegelPullbackRemovable N s (l + t * Complex.I) := by
    simpa only [c] using hleft
  rw [hbottom', htop', hright', hleft']
  have hrem' :
      (∫ x : ℝ in l..R,
          deBruijnNewmanRiemannSiegelPullbackRemovable N s (x + (-h) * Complex.I)) -
        (∫ x : ℝ in l..R,
          deBruijnNewmanRiemannSiegelPullbackRemovable N s (x + h * Complex.I)) +
        Complex.I * (∫ t : ℝ in -h..h,
          deBruijnNewmanRiemannSiegelPullbackRemovable N s (R + t * Complex.I)) -
        Complex.I * (∫ t : ℝ in -h..h,
          deBruijnNewmanRiemannSiegelPullbackRemovable N s (l + t * Complex.I)) = 0 := by
    simpa only [h] using hrem
  have hinv' :
      (∫ x : ℝ in l..R, (x + (-h) * Complex.I)⁻¹) -
        (∫ x : ℝ in l..R, (x + h * Complex.I)⁻¹) +
        Complex.I * (∫ t : ℝ in -h..h, (R + t * Complex.I)⁻¹) -
        Complex.I * (∫ t : ℝ in -h..h, (l + t * Complex.I)⁻¹) =
          2 * (Real.pi : ℂ) * Complex.I := by
    simpa only [h] using hinv
  have hc : c * (2 * (Real.pi : ℂ) * Complex.I) = ((N + 1 : ℕ) : ℂ) ^ (-s) := by
    dsimp [c]
    field_simp [Complex.I_ne_zero, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  calc
    ((c * ∫ x : ℝ in l..R, (x + (-h) * Complex.I)⁻¹) +
              ∫ x : ℝ in l..R,
                deBruijnNewmanRiemannSiegelPullbackRemovable N s (x + (-h) * Complex.I)) -
            ((c * ∫ x : ℝ in l..R, (x + h * Complex.I)⁻¹) +
              ∫ x : ℝ in l..R,
                deBruijnNewmanRiemannSiegelPullbackRemovable N s (x + h * Complex.I)) +
          Complex.I * ((c * ∫ t : ℝ in -h..h, (R + t * Complex.I)⁻¹) +
            ∫ t : ℝ in -h..h,
              deBruijnNewmanRiemannSiegelPullbackRemovable N s (R + t * Complex.I)) -
        Complex.I * ((c * ∫ t : ℝ in -h..h, (l + t * Complex.I)⁻¹) +
          ∫ t : ℝ in -h..h,
            deBruijnNewmanRiemannSiegelPullbackRemovable N s (l + t * Complex.I)) =
        c * ((∫ x : ℝ in l..R, (x + (-h) * Complex.I)⁻¹) -
            (∫ x : ℝ in l..R, (x + h * Complex.I)⁻¹) +
            Complex.I * (∫ t : ℝ in -h..h, (R + t * Complex.I)⁻¹) -
            Complex.I * (∫ t : ℝ in -h..h, (l + t * Complex.I)⁻¹)) +
          ((∫ x : ℝ in l..R,
              deBruijnNewmanRiemannSiegelPullbackRemovable N s (x + (-h) * Complex.I)) -
            (∫ x : ℝ in l..R,
              deBruijnNewmanRiemannSiegelPullbackRemovable N s (x + h * Complex.I)) +
            Complex.I * (∫ t : ℝ in -h..h,
              deBruijnNewmanRiemannSiegelPullbackRemovable N s (R + t * Complex.I)) -
            Complex.I * (∫ t : ℝ in -h..h,
              deBruijnNewmanRiemannSiegelPullbackRemovable N s (l + t * Complex.I))) := by ring
    _ = c * (2 * (Real.pi : ℂ) * Complex.I) + 0 := by rw [hinv', hrem']
    _ = ((N + 1 : ℕ) : ℂ) ^ (-s) := by rw [hc, add_zero]

theorem deBruijnNewmanRiemannSiegelPullbackPoint_bottom (N : ℕ) (x : ℝ) :
    deBruijnNewmanRiemannSiegelPullbackPoint N
        (x + (-deBruijnNewmanRiemannSiegelRotatedHalfWidth) * Complex.I) =
      deBruijnNewmanRiemannSiegelLine N
        (x - deBruijnNewmanRiemannSiegelRotatedHalfWidth) := by
  let h := deBruijnNewmanRiemannSiegelRotatedHalfWidth
  change deBruijnNewmanRiemannSiegelPullbackPoint N (x + (-h) * Complex.I) =
    deBruijnNewmanRiemannSiegelLine N (x - h)
  have hzre :
      ((x : ℂ) + -(h : ℂ) * Complex.I).re = x := by simp
  have hzim :
      ((x : ℂ) + -(h : ℂ) * Complex.I).im = -h := by simp
  apply Complex.ext
  · rw [deBruijnNewmanRiemannSiegelPullbackPoint_re,
      deBruijnNewmanRiemannSiegelLine_re, hzre, hzim]
    dsimp [h]
    rw [deBruijnNewmanRiemannSiegelRotatedHalfWidth]
    have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
    push_cast
    nlinarith
  · rw [deBruijnNewmanRiemannSiegelPullbackPoint_im,
      deBruijnNewmanRiemannSiegelLine_im, hzre, hzim]
    ring

theorem deBruijnNewmanRiemannSiegelPullbackPoint_top (N : ℕ) (x : ℝ) :
    deBruijnNewmanRiemannSiegelPullbackPoint N
        (x + deBruijnNewmanRiemannSiegelRotatedHalfWidth * Complex.I) =
      deBruijnNewmanRiemannSiegelLine (N + 1)
        (x + deBruijnNewmanRiemannSiegelRotatedHalfWidth) := by
  let h := deBruijnNewmanRiemannSiegelRotatedHalfWidth
  change deBruijnNewmanRiemannSiegelPullbackPoint N (x + h * Complex.I) =
    deBruijnNewmanRiemannSiegelLine (N + 1) (x + h)
  have hzre : ((x : ℂ) + (h : ℂ) * Complex.I).re = x := by simp
  have hzim : ((x : ℂ) + (h : ℂ) * Complex.I).im = h := by simp
  apply Complex.ext
  · rw [deBruijnNewmanRiemannSiegelPullbackPoint_re,
      deBruijnNewmanRiemannSiegelLine_re, hzre, hzim]
    dsimp [h]
    rw [deBruijnNewmanRiemannSiegelRotatedHalfWidth]
    have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
    push_cast
    nlinarith
  · rw [deBruijnNewmanRiemannSiegelPullbackPoint_im,
      deBruijnNewmanRiemannSiegelLine_im, hzre, hzim]

theorem deBruijnNewmanRiemannSiegelPullbackKernel_bottom (N : ℕ) (s : ℂ) (x : ℝ) :
    deBruijnNewmanRiemannSiegelPullbackKernel N s
        (x + (-deBruijnNewmanRiemannSiegelRotatedHalfWidth) * Complex.I) =
      deBruijnNewmanRiemannSiegelLineIntegrand N s
        (x - deBruijnNewmanRiemannSiegelRotatedHalfWidth) := by
  rw [deBruijnNewmanRiemannSiegelPullbackKernel,
    deBruijnNewmanRiemannSiegelLineIntegrand,
    deBruijnNewmanRiemannSiegelPullbackPoint_bottom]

theorem deBruijnNewmanRiemannSiegelPullbackKernel_top (N : ℕ) (s : ℂ) (x : ℝ) :
    deBruijnNewmanRiemannSiegelPullbackKernel N s
        (x + deBruijnNewmanRiemannSiegelRotatedHalfWidth * Complex.I) =
      deBruijnNewmanRiemannSiegelLineIntegrand (N + 1) s
        (x + deBruijnNewmanRiemannSiegelRotatedHalfWidth) := by
  rw [deBruijnNewmanRiemannSiegelPullbackKernel,
    deBruijnNewmanRiemannSiegelLineIntegrand,
    deBruijnNewmanRiemannSiegelPullbackPoint_top]

/-- The two fixed-length short sides of the rotated finite rectangle. -/
def deBruijnNewmanRiemannSiegelRightEndIntegral (N : ℕ) (s : ℂ) (T : ℝ) : ℂ :=
  Complex.I * (∫ t : ℝ in
      -deBruijnNewmanRiemannSiegelRotatedHalfWidth..
        deBruijnNewmanRiemannSiegelRotatedHalfWidth,
    deBruijnNewmanRiemannSiegelPullbackKernel N s
      (deBruijnNewmanRiemannSiegelRotatedHalfWidth + T + t * Complex.I))

def deBruijnNewmanRiemannSiegelLeftEndIntegral (N : ℕ) (s : ℂ) (T : ℝ) : ℂ :=
  Complex.I * (∫ t : ℝ in
      -deBruijnNewmanRiemannSiegelRotatedHalfWidth..
        deBruijnNewmanRiemannSiegelRotatedHalfWidth,
    deBruijnNewmanRiemannSiegelPullbackKernel N s
      (deBruijnNewmanRiemannSiegelRotatedHalfWidth - T + t * Complex.I))

/-- Exact one-pole identity at finite truncation. The upper source line is staggered by
`sqrt(2)/2`, which makes the finite contour a true rectangle after complex rotation. -/
theorem deBruijnNewmanRiemannSiegel_finite_adjacent_shift
    (N : ℕ) (s : ℂ) {T : ℝ}
    (hT : deBruijnNewmanRiemannSiegelRotatedHalfWidth < T) :
    (∫ v : ℝ in -T..T, deBruijnNewmanRiemannSiegelLineIntegrand N s v) -
      (∫ v : ℝ in
        deBruijnNewmanRiemannSiegelParameterStagger - T..
          deBruijnNewmanRiemannSiegelParameterStagger + T,
        deBruijnNewmanRiemannSiegelLineIntegrand (N + 1) s v) +
      deBruijnNewmanRiemannSiegelRightEndIntegral N s T -
      deBruijnNewmanRiemannSiegelLeftEndIntegral N s T =
        ((N + 1 : ℕ) : ℂ) ^ (-s) := by
  let h := deBruijnNewmanRiemannSiegelRotatedHalfWidth
  have hl : h - T < 0 := sub_neg.mpr hT
  have hR : 0 < h + T := by
    have hh := deBruijnNewmanRiemannSiegelRotatedHalfWidth_pos
    linarith
  have hboundary := deBruijnNewmanRiemannSiegelPullbackKernel_boundary_rect
    N s hl hR
  have hbottom :
      (∫ x : ℝ in h - T..h + T,
        deBruijnNewmanRiemannSiegelPullbackKernel N s (x + (-h) * Complex.I)) =
      ∫ v : ℝ in -T..T, deBruijnNewmanRiemannSiegelLineIntegrand N s v := by
    rw [show (fun x : ℝ ↦
        deBruijnNewmanRiemannSiegelPullbackKernel N s (x + (-h) * Complex.I)) =
      fun x : ℝ ↦ deBruijnNewmanRiemannSiegelLineIntegrand N s (x - h) by
        funext x
        simpa only [h] using deBruijnNewmanRiemannSiegelPullbackKernel_bottom N s x]
    rw [intervalIntegral.integral_comp_sub_right]
    congr 1 <;> ring
  have htop :
      (∫ x : ℝ in h - T..h + T,
        deBruijnNewmanRiemannSiegelPullbackKernel N s (x + h * Complex.I)) =
      ∫ v : ℝ in
          deBruijnNewmanRiemannSiegelParameterStagger - T..
            deBruijnNewmanRiemannSiegelParameterStagger + T,
        deBruijnNewmanRiemannSiegelLineIntegrand (N + 1) s v := by
    rw [show (fun x : ℝ ↦
        deBruijnNewmanRiemannSiegelPullbackKernel N s (x + h * Complex.I)) =
      fun x : ℝ ↦ deBruijnNewmanRiemannSiegelLineIntegrand (N + 1) s (x + h) by
        funext x
        simpa only [h] using deBruijnNewmanRiemannSiegelPullbackKernel_top N s x]
    rw [intervalIntegral.integral_comp_add_right]
    rw [deBruijnNewmanRiemannSiegelParameterStagger_eq_two_mul_halfWidth]
    simp only [h]
    congr 1 <;> ring
  change
    (∫ v : ℝ in -T..T, deBruijnNewmanRiemannSiegelLineIntegrand N s v) -
      (∫ v : ℝ in
        deBruijnNewmanRiemannSiegelParameterStagger - T..
          deBruijnNewmanRiemannSiegelParameterStagger + T,
        deBruijnNewmanRiemannSiegelLineIntegrand (N + 1) s v) +
      Complex.I * (∫ t : ℝ in -h..h,
        deBruijnNewmanRiemannSiegelPullbackKernel N s (h + T + t * Complex.I)) -
      Complex.I * (∫ t : ℝ in -h..h,
        deBruijnNewmanRiemannSiegelPullbackKernel N s (h - T + t * Complex.I)) = _
  push_cast at hboundary
  simpa only [hbottom, htop, h, Nat.cast_add, Nat.cast_one] using hboundary

theorem deBruijnNewmanRiemannSiegelSqrtTwo_one_le :
    1 ≤ Real.sqrt 2 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]

theorem deBruijnNewmanRiemannSiegelSqrtTwo_le_two :
    Real.sqrt 2 ≤ 2 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]

theorem deBruijnNewmanRiemannSiegelRotatedHalfWidth_le_one_half :
    deBruijnNewmanRiemannSiegelRotatedHalfWidth ≤ 1 / 2 := by
  rw [deBruijnNewmanRiemannSiegelRotatedHalfWidth]
  linarith [deBruijnNewmanRiemannSiegelSqrtTwo_le_two]

/-- The imaginary part alone gives a lower bound for the norm of the complex sine. -/
theorem abs_sinh_im_le_norm_complex_sin (z : ℂ) :
    |Real.sinh z.im| ≤ ‖Complex.sin z‖ := by
  rw [← sq_le_sq₀ (abs_nonneg _) (norm_nonneg _),
    ← Complex.normSq_eq_norm_sq, normSq_complex_sin]
  have htrig := Real.sin_sq_add_cos_sq z.re
  have hcosh := Real.cosh_sq z.im
  have hsin : 0 ≤ Real.sin z.re ^ 2 := sq_nonneg _
  rw [sq_abs]
  nlinarith [sq_nonneg (Real.sinh z.im)]

/-- Once the imaginary part has modulus at least `1/pi`, the source denominator has norm at
least two. This coarse constant is enough for the short-edge Gaussian estimate. -/
theorem two_le_norm_deBruijnNewmanRiemannSiegelDenominator_of_im
    {w : ℂ} (hw : 1 ≤ |Real.pi * w.im|) :
    2 ≤ ‖deBruijnNewmanRiemannSiegelDenominator w‖ := by
  rw [deBruijnNewmanRiemannSiegelDenominator_eq, norm_mul, norm_mul]
  norm_num
  have hsinh : 1 ≤ |Real.sinh (((Real.pi : ℂ) * w).im)| := by
    calc
      1 ≤ |Real.pi * w.im| := hw
      _ ≤ Real.sinh |Real.pi * w.im| :=
        Real.self_le_sinh_iff.mpr (abs_nonneg _)
      _ = |Real.sinh (((Real.pi : ℂ) * w).im)| := by
        rw [← Real.abs_sinh]
        simp [Complex.mul_im]
  exact hsinh.trans (abs_sinh_im_le_norm_complex_sin ((Real.pi : ℂ) * w))

/-- Exact real exponent of the Gaussian numerator on a vertical short side in pullback
coordinates. -/
theorem deBruijnNewmanRiemannSiegelPullback_gaussianExponent_re
    (N : ℕ) (x t : ℝ) :
    (Complex.I * Real.pi *
        deBruijnNewmanRiemannSiegelPullbackPoint N (x + t * Complex.I) ^ 2).re =
      -Real.pi * x ^ 2 + Real.pi * t ^ 2 +
        Real.sqrt 2 * Real.pi * (N + 1) * (x + t) := by
  have hzre : ((x : ℂ) + (t : ℂ) * Complex.I).re = x := by simp
  have hzim : ((x : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, mul_zero, sub_zero]
  rw [deBruijnNewmanRiemannSiegelPullbackPoint_re,
    deBruijnNewmanRiemannSiegelPullbackPoint_im, hzre, hzim]
  have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by positivity)
  push_cast
  ring_nf at hsqrt ⊢
  rw [hsqrt]
  ring

theorem norm_deBruijnNewmanRiemannSiegelPullbackPoint_le
    (N : ℕ) (x t : ℝ) :
    ‖deBruijnNewmanRiemannSiegelPullbackPoint N (x + t * Complex.I)‖ ≤
      (N + 1 : ℕ) + |x| + |t| := by
  rw [deBruijnNewmanRiemannSiegelPullbackPoint]
  calc
    ‖((N + 1 : ℕ) : ℂ) +
        deBruijnNewmanRiemannSiegelDirection * ((x : ℂ) + t * Complex.I)‖ ≤
        ‖((N + 1 : ℕ) : ℂ)‖ +
          ‖deBruijnNewmanRiemannSiegelDirection * ((x : ℂ) + t * Complex.I)‖ :=
      norm_add_le _ _
    _ = (N + 1 : ℕ) + ‖(x : ℂ) + t * Complex.I‖ := by
      rw [norm_mul, norm_deBruijnNewmanRiemannSiegelDirection, one_mul,
        Complex.norm_natCast]
    _ ≤ (N + 1 : ℕ) + (‖(x : ℂ)‖ + ‖(t : ℂ) * Complex.I‖) := by
      gcongr
      exact norm_add_le _ _
    _ = (N + 1 : ℕ) + |x| + |t| := by
      simp only [norm_real, norm_mul, norm_I, mul_one, Real.norm_eq_abs]
      ring

theorem one_le_norm_deBruijnNewmanRiemannSiegelPullbackPoint
    (N : ℕ) (x t : ℝ) (hx : (N : ℝ) + 2 ≤ |x|) :
    1 ≤ ‖deBruijnNewmanRiemannSiegelPullbackPoint N (x + t * Complex.I)‖ := by
  have hz : |x| ≤ ‖(x : ℂ) + t * Complex.I‖ := by
    simpa using Complex.abs_re_le_norm ((x : ℂ) + t * Complex.I)
  have hbound :
      ‖(x : ℂ) + t * Complex.I‖ - (N + 1 : ℕ) ≤
        ‖deBruijnNewmanRiemannSiegelPullbackPoint N (x + t * Complex.I)‖ := by
    calc
      ‖(x : ℂ) + t * Complex.I‖ - (N + 1 : ℕ) =
          ‖deBruijnNewmanRiemannSiegelDirection * ((x : ℂ) + t * Complex.I)‖ -
            ‖-((N + 1 : ℕ) : ℂ)‖ := by
              rw [norm_mul, norm_deBruijnNewmanRiemannSiegelDirection, one_mul,
                norm_neg, Complex.norm_natCast]
      _ ≤ ‖deBruijnNewmanRiemannSiegelDirection * ((x : ℂ) + t * Complex.I) -
            (-((N + 1 : ℕ) : ℂ))‖ := norm_sub_norm_le _ _
      _ = ‖deBruijnNewmanRiemannSiegelPullbackPoint N (x + t * Complex.I)‖ := by
        congr 1
        rw [deBruijnNewmanRiemannSiegelPullbackPoint]
        ring
  have hx' : 1 ≤ |x| - (N + 1 : ℕ) := by
    push_cast
    linarith
  exact hx'.trans ((sub_le_sub_right hz _).trans hbound)

theorem two_le_norm_deBruijnNewmanRiemannSiegelPullbackDenominator_side
    (N : ℕ) (x t : ℝ) (hx : 6 ≤ |x|)
    (ht : |t| ≤ deBruijnNewmanRiemannSiegelRotatedHalfWidth) :
    2 ≤ ‖deBruijnNewmanRiemannSiegelPullbackDenominator N (x + t * Complex.I)‖ := by
  change 2 ≤ ‖deBruijnNewmanRiemannSiegelDenominator
    (deBruijnNewmanRiemannSiegelPullbackPoint N (x + t * Complex.I))‖
  apply two_le_norm_deBruijnNewmanRiemannSiegelDenominator_of_im
  rw [deBruijnNewmanRiemannSiegelPullbackPoint_im]
  have hhalf := deBruijnNewmanRiemannSiegelRotatedHalfWidth_le_one_half
  have hsqrt := deBruijnNewmanRiemannSiegelSqrtTwo_one_le
  have hpi := Real.pi_gt_three
  have hxt : |x| - |t| ≤ |x + t| := by
    have htriangle := abs_add_le (x + t) (-t)
    rw [show x + t + -t = x by ring, abs_neg] at htriangle
    linarith
  have hzre : ((x : ℂ) + (t : ℂ) * Complex.I).re = x := by simp
  have hzim : ((x : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
  rw [hzre, hzim]
  change 1 ≤ |Real.pi * (-(Real.sqrt 2 / 2) * (x + t))|
  rw [abs_mul, abs_mul, abs_neg]
  have hsqrt_nonneg := Real.sqrt_nonneg 2
  have hpi_nonneg := Real.pi_pos.le
  rw [abs_of_nonneg hpi_nonneg, abs_of_nonneg (div_nonneg hsqrt_nonneg (by norm_num))]
  have hxtLower : (11 / 2 : ℝ) ≤ |x + t| := by linarith
  have haLower : (1 / 2 : ℝ) ≤ Real.sqrt 2 / 2 := by linarith
  have hproduct : (11 / 4 : ℝ) ≤ (Real.sqrt 2 / 2) * |x + t| := by
    nlinarith [mul_le_mul haLower hxtLower (by norm_num : (0 : ℝ) ≤ 11 / 2)
      (by positivity : (0 : ℝ) ≤ Real.sqrt 2 / 2)]
  have hpiProduct : 3 * ((Real.sqrt 2 / 2) * |x + t|) ≤
      Real.pi * ((Real.sqrt 2 / 2) * |x + t|) := by
    exact mul_le_mul_of_nonneg_right hpi.le (mul_nonneg (by positivity) (abs_nonneg _))
  nlinarith

theorem norm_cpow_neg_deBruijnNewmanRiemannSiegelPullbackPoint_le
    (N : ℕ) (s : ℂ) (x t : ℝ) (hx : (N : ℝ) + 2 ≤ |x|)
    (ht : |t| ≤ deBruijnNewmanRiemannSiegelRotatedHalfWidth) :
    ‖deBruijnNewmanRiemannSiegelPullbackPoint N (x + t * Complex.I) ^ (-s)‖ ≤
      Real.exp
        (|s.re| * ((N + 1 : ℕ) + |x| +
            deBruijnNewmanRiemannSiegelRotatedHalfWidth) +
          |s.im| * Real.pi) := by
  let w := deBruijnNewmanRiemannSiegelPullbackPoint N (x + t * Complex.I)
  have hwNorm : 1 ≤ ‖w‖ :=
    one_le_norm_deBruijnNewmanRiemannSiegelPullbackPoint N x t hx
  have hw : w ≠ 0 := by
    intro hw
    rw [hw, norm_zero] at hwNorm
    norm_num at hwNorm
  have hwUpper : ‖w‖ ≤
      (N + 1 : ℕ) + |x| + deBruijnNewmanRiemannSiegelRotatedHalfWidth := by
    exact (norm_deBruijnNewmanRiemannSiegelPullbackPoint_le N x t).trans (by
      gcongr)
  have hlog : |Real.log ‖w‖| ≤
      (N + 1 : ℕ) + |x| + deBruijnNewmanRiemannSiegelRotatedHalfWidth := by
    rw [abs_of_nonneg (Real.log_nonneg hwNorm)]
    exact (Real.log_le_self (norm_nonneg w)).trans hwUpper
  rw [Complex.cpow_def_of_ne_zero hw, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have harg := Complex.abs_arg_le_pi w
  rw [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.log_re, Complex.log_im]
  calc
    Real.log ‖w‖ * -s.re - w.arg * -s.im =
        (-s.re) * Real.log ‖w‖ + s.im * w.arg := by ring
    _ ≤ |(-s.re) * Real.log ‖w‖| + |s.im * w.arg| :=
      add_le_add (le_abs_self _) (le_abs_self _)
    _ = |s.re| * |Real.log ‖w‖| + |s.im| * |w.arg| := by
      rw [abs_mul, abs_mul, abs_neg]
    _ ≤ |s.re| * ((N + 1 : ℕ) + |x| +
          deBruijnNewmanRiemannSiegelRotatedHalfWidth) + |s.im| * Real.pi :=
      add_le_add (mul_le_mul_of_nonneg_left hlog (abs_nonneg _))
        (mul_le_mul_of_nonneg_left harg (abs_nonneg _))

def deBruijnNewmanRiemannSiegelSideLinearRate (N : ℕ) (s : ℂ) : ℝ :=
  |s.re| + Real.sqrt 2 * Real.pi * (N + 1)

def deBruijnNewmanRiemannSiegelSideMajorantConstant (N : ℕ) (s : ℂ) : ℝ :=
  |s.re| * ((N + 1 : ℕ) + deBruijnNewmanRiemannSiegelRotatedHalfWidth) +
    |s.im| * Real.pi +
    Real.pi * deBruijnNewmanRiemannSiegelRotatedHalfWidth ^ 2 +
    Real.sqrt 2 * Real.pi * (N + 1) *
      deBruijnNewmanRiemannSiegelRotatedHalfWidth +
    deBruijnNewmanRiemannSiegelSideLinearRate N s ^ 2 / (2 * Real.pi)

def deBruijnNewmanRiemannSiegelSideMajorant (N : ℕ) (s : ℂ) (x : ℝ) : ℝ :=
  (1 / 2) * Real.exp (deBruijnNewmanRiemannSiegelSideMajorantConstant N s) *
    Real.exp (-(Real.pi / 2) * x ^ 2)

theorem deBruijnNewmanRiemannSiegelSideLinearRate_mul_abs_le
    (N : ℕ) (s : ℂ) (x : ℝ) :
    deBruijnNewmanRiemannSiegelSideLinearRate N s * |x| ≤
      Real.pi / 2 * x ^ 2 +
        deBruijnNewmanRiemannSiegelSideLinearRate N s ^ 2 / (2 * Real.pi) := by
  let C := deBruijnNewmanRiemannSiegelSideLinearRate N s
  have hpi : 0 < 2 * Real.pi := by positivity
  have hsq : 0 ≤ (Real.pi * |x| - C) ^ 2 := sq_nonneg _
  have hrewrite :
      Real.pi / 2 * x ^ 2 + C ^ 2 / (2 * Real.pi) =
        (Real.pi ^ 2 * x ^ 2 + C ^ 2) / (2 * Real.pi) := by
    field_simp
  rw [hrewrite, le_div_iff₀ hpi]
  nlinarith [sq_abs x]

theorem norm_deBruijnNewmanRiemannSiegelPullbackKernel_le_premajorant
    (N : ℕ) (s : ℂ) (x t : ℝ) (hxN : (N : ℝ) + 2 ≤ |x|) (hx6 : 6 ≤ |x|)
    (ht : |t| ≤ deBruijnNewmanRiemannSiegelRotatedHalfWidth) :
    ‖deBruijnNewmanRiemannSiegelPullbackKernel N s (x + t * Complex.I)‖ ≤
      (1 / 2) * Real.exp
        (|s.re| * ((N + 1 : ℕ) + |x| +
            deBruijnNewmanRiemannSiegelRotatedHalfWidth) +
          |s.im| * Real.pi +
          (-Real.pi * x ^ 2 + Real.pi * t ^ 2 +
            Real.sqrt 2 * Real.pi * (N + 1) * (x + t))) := by
  let w := deBruijnNewmanRiemannSiegelPullbackPoint N (x + t * Complex.I)
  have hpow := norm_cpow_neg_deBruijnNewmanRiemannSiegelPullbackPoint_le
    N s x t hxN ht
  have hden := two_le_norm_deBruijnNewmanRiemannSiegelPullbackDenominator_side N x t hx6 ht
  have hdenPos : 0 < ‖deBruijnNewmanRiemannSiegelPullbackDenominator N
      (x + t * Complex.I)‖ := lt_of_lt_of_le (by norm_num) hden
  rw [deBruijnNewmanRiemannSiegelPullbackKernel,
    deBruijnNewmanRiemannSiegelKernel, deBruijnNewmanRiemannSiegelNumerator,
    norm_mul, norm_deBruijnNewmanRiemannSiegelDirection, mul_one, norm_div, norm_mul,
    Complex.norm_exp, deBruijnNewmanRiemannSiegelPullback_gaussianExponent_re]
  change
    ‖w ^ (-s)‖ *
          Real.exp (-Real.pi * x ^ 2 + Real.pi * t ^ 2 +
            Real.sqrt 2 * Real.pi * (N + 1) * (x + t)) /
        ‖deBruijnNewmanRiemannSiegelPullbackDenominator N (x + t * Complex.I)‖ ≤ _
  calc
    ‖w ^ (-s)‖ *
          Real.exp (-Real.pi * x ^ 2 + Real.pi * t ^ 2 +
            Real.sqrt 2 * Real.pi * (N + 1) * (x + t)) /
        ‖deBruijnNewmanRiemannSiegelPullbackDenominator N (x + t * Complex.I)‖ ≤
        (Real.exp
            (|s.re| * ((N + 1 : ℕ) + |x| +
                deBruijnNewmanRiemannSiegelRotatedHalfWidth) +
              |s.im| * Real.pi) *
          Real.exp (-Real.pi * x ^ 2 + Real.pi * t ^ 2 +
            Real.sqrt 2 * Real.pi * (N + 1) * (x + t))) /
          ‖deBruijnNewmanRiemannSiegelPullbackDenominator N
            (x + t * Complex.I)‖ := by
              apply div_le_div_of_nonneg_right
              · exact mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _)
              · exact hdenPos.le
    _ ≤ (Real.exp
            (|s.re| * ((N + 1 : ℕ) + |x| +
                deBruijnNewmanRiemannSiegelRotatedHalfWidth) +
              |s.im| * Real.pi) *
          Real.exp (-Real.pi * x ^ 2 + Real.pi * t ^ 2 +
            Real.sqrt 2 * Real.pi * (N + 1) * (x + t))) / 2 := by
              exact div_le_div_of_nonneg_left
                (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)) (by norm_num) hden
    _ = (1 / 2) * Real.exp
        (|s.re| * ((N + 1 : ℕ) + |x| +
            deBruijnNewmanRiemannSiegelRotatedHalfWidth) +
          |s.im| * Real.pi +
          (-Real.pi * x ^ 2 + Real.pi * t ^ 2 +
            Real.sqrt 2 * Real.pi * (N + 1) * (x + t))) := by
              conv_rhs => rw [Real.exp_add]
              ring

/-- Uniform pure Gaussian domination on either fixed-length short side. -/
theorem norm_deBruijnNewmanRiemannSiegelPullbackKernel_le_sideMajorant
    (N : ℕ) (s : ℂ) (x t : ℝ) (hxN : (N : ℝ) + 2 ≤ |x|) (hx6 : 6 ≤ |x|)
    (ht : |t| ≤ deBruijnNewmanRiemannSiegelRotatedHalfWidth) :
    ‖deBruijnNewmanRiemannSiegelPullbackKernel N s (x + t * Complex.I)‖ ≤
      deBruijnNewmanRiemannSiegelSideMajorant N s x := by
  have hpre := norm_deBruijnNewmanRiemannSiegelPullbackKernel_le_premajorant
    N s x t hxN hx6 ht
  have htSq : t ^ 2 ≤ deBruijnNewmanRiemannSiegelRotatedHalfWidth ^ 2 :=
    sq_le_sq.mpr (by
      simpa [abs_of_pos deBruijnNewmanRiemannSiegelRotatedHalfWidth_pos] using ht)
  have htUpper : t ≤ deBruijnNewmanRiemannSiegelRotatedHalfWidth :=
    (le_abs_self t).trans ht
  have hxUpper : x ≤ |x| := le_abs_self x
  have hcoef : 0 ≤ Real.sqrt 2 * Real.pi * (N + 1) := by positivity
  have hlinear := deBruijnNewmanRiemannSiegelSideLinearRate_mul_abs_le N s x
  apply hpre.trans
  rw [deBruijnNewmanRiemannSiegelSideMajorant]
  conv_rhs => rw [mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
  simp only [deBruijnNewmanRiemannSiegelSideMajorantConstant,
    deBruijnNewmanRiemannSiegelSideLinearRate] at hlinear ⊢
  have hxTerm :
      Real.sqrt 2 * Real.pi * (N + 1) * x ≤
        Real.sqrt 2 * Real.pi * (N + 1) * |x| :=
    mul_le_mul_of_nonneg_left hxUpper hcoef
  have htTerm :
      Real.sqrt 2 * Real.pi * (N + 1) * t ≤
        Real.sqrt 2 * Real.pi * (N + 1) *
          deBruijnNewmanRiemannSiegelRotatedHalfWidth :=
    mul_le_mul_of_nonneg_left htUpper hcoef
  have htSqTerm : Real.pi * t ^ 2 ≤
      Real.pi * deBruijnNewmanRiemannSiegelRotatedHalfWidth ^ 2 :=
    mul_le_mul_of_nonneg_left htSq Real.pi_pos.le
  nlinarith

theorem norm_deBruijnNewmanRiemannSiegelPullbackKernel_shortSideIntegral_le
    (N : ℕ) (s : ℂ) (x : ℝ) (hxN : (N : ℝ) + 2 ≤ |x|) (hx6 : 6 ≤ |x|) :
    ‖Complex.I * (∫ t : ℝ in
        -deBruijnNewmanRiemannSiegelRotatedHalfWidth..
          deBruijnNewmanRiemannSiegelRotatedHalfWidth,
      deBruijnNewmanRiemannSiegelPullbackKernel N s (x + t * Complex.I))‖ ≤
      deBruijnNewmanRiemannSiegelSideMajorant N s x *
        (2 * deBruijnNewmanRiemannSiegelRotatedHalfWidth) := by
  rw [norm_mul, norm_I, one_mul]
  calc
    ‖∫ t : ℝ in
        -deBruijnNewmanRiemannSiegelRotatedHalfWidth..
          deBruijnNewmanRiemannSiegelRotatedHalfWidth,
      deBruijnNewmanRiemannSiegelPullbackKernel N s (x + t * Complex.I)‖ ≤
        deBruijnNewmanRiemannSiegelSideMajorant N s x *
          |deBruijnNewmanRiemannSiegelRotatedHalfWidth -
            (-deBruijnNewmanRiemannSiegelRotatedHalfWidth)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      apply norm_deBruijnNewmanRiemannSiegelPullbackKernel_le_sideMajorant N s x t hxN hx6
      have htu := uIoc_subset_uIcc ht
      rw [uIcc_of_le (neg_le_self deBruijnNewmanRiemannSiegelRotatedHalfWidth_pos.le)] at htu
      rw [abs_le]
      exact htu
    _ = deBruijnNewmanRiemannSiegelSideMajorant N s x *
          (2 * deBruijnNewmanRiemannSiegelRotatedHalfWidth) := by
      have hh := deBruijnNewmanRiemannSiegelRotatedHalfWidth_pos
      rw [abs_of_pos (by linarith :
        0 < deBruijnNewmanRiemannSiegelRotatedHalfWidth -
          (-deBruijnNewmanRiemannSiegelRotatedHalfWidth))]
      ring

theorem tendsto_deBruijnNewmanRiemannSiegelSideMajorant_add
    (N : ℕ) (s : ℂ) (c : ℝ) :
    Tendsto (fun T : ℝ ↦
      deBruijnNewmanRiemannSiegelSideMajorant N s (c + T)) atTop (𝓝 0) := by
  rw [show (fun T : ℝ ↦ deBruijnNewmanRiemannSiegelSideMajorant N s (c + T)) =
      fun T : ℝ ↦
        ((1 / 2) * Real.exp (deBruijnNewmanRiemannSiegelSideMajorantConstant N s)) *
          Real.exp (-(Real.pi / 2) * (c + T) ^ 2) by
    funext T
    rfl]
  have hshift : Tendsto (fun T : ℝ ↦ c + T) atTop atTop :=
    tendsto_atTop_add_const_left atTop c tendsto_id
  have hsq : Tendsto (fun T : ℝ ↦ (c + T) ^ 2) atTop atTop := by
    simp only [pow_two]
    exact hshift.atTop_mul_atTop₀ hshift
  have hcoef : -(Real.pi / 2) < 0 :=
    neg_lt_zero.mpr (div_pos Real.pi_pos (by norm_num))
  have hneg : Tendsto (fun T : ℝ ↦ -(Real.pi / 2) * (c + T) ^ 2) atTop atBot :=
    hsq.const_mul_atTop_of_neg hcoef
  simpa only [Function.comp_apply, mul_zero] using
    (Real.tendsto_exp_atBot.comp hneg).const_mul
      ((1 / 2) * Real.exp (deBruijnNewmanRiemannSiegelSideMajorantConstant N s))

theorem tendsto_deBruijnNewmanRiemannSiegelSideMajorant_sub
    (N : ℕ) (s : ℂ) (c : ℝ) :
    Tendsto (fun T : ℝ ↦
      deBruijnNewmanRiemannSiegelSideMajorant N s (c - T)) atTop (𝓝 0) := by
  have hlim := tendsto_deBruijnNewmanRiemannSiegelSideMajorant_add N s (-c)
  apply hlim.congr'
  exact Filter.Eventually.of_forall fun T ↦ by
    dsimp only
    unfold deBruijnNewmanRiemannSiegelSideMajorant
    rw [show (-c + T) ^ 2 = (c - T) ^ 2 by ring]

/-- The right short side vanishes in the infinite-height limit. -/
theorem tendsto_deBruijnNewmanRiemannSiegelRightEndIntegral
    (N : ℕ) (s : ℂ) :
    Tendsto (deBruijnNewmanRiemannSiegelRightEndIntegral N s) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero'
    (g := fun T : ℝ ↦
      deBruijnNewmanRiemannSiegelSideMajorant N s
          (deBruijnNewmanRiemannSiegelRotatedHalfWidth + T) *
        (2 * deBruijnNewmanRiemannSiegelRotatedHalfWidth)) ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun _ ↦ norm_nonneg _
  · filter_upwards [eventually_ge_atTop
        (max 6 ((N : ℝ) + 2))] with T hT
    have hh := deBruijnNewmanRiemannSiegelRotatedHalfWidth_pos
    have hxPos : 0 < deBruijnNewmanRiemannSiegelRotatedHalfWidth + T := by
      have : 0 ≤ T := le_trans (by norm_num) (le_trans (le_max_left _ _) hT)
      linarith
    have hxN : (N : ℝ) + 2 ≤
        |deBruijnNewmanRiemannSiegelRotatedHalfWidth + T| := by
      rw [abs_of_pos hxPos]
      exact (le_max_right _ _).trans hT |>.trans (le_add_of_nonneg_left hh.le)
    have hx6 : 6 ≤ |deBruijnNewmanRiemannSiegelRotatedHalfWidth + T| := by
      rw [abs_of_pos hxPos]
      exact (le_max_left _ _).trans hT |>.trans (le_add_of_nonneg_left hh.le)
    unfold deBruijnNewmanRiemannSiegelRightEndIntegral
    have hbound := norm_deBruijnNewmanRiemannSiegelPullbackKernel_shortSideIntegral_le
      N s _ hxN hx6
    push_cast at hbound
    exact hbound
  · simpa only [zero_mul] using
      (tendsto_deBruijnNewmanRiemannSiegelSideMajorant_add N s
        deBruijnNewmanRiemannSiegelRotatedHalfWidth).mul_const
          (2 * deBruijnNewmanRiemannSiegelRotatedHalfWidth)

/-- The left short side vanishes in the infinite-height limit. -/
theorem tendsto_deBruijnNewmanRiemannSiegelLeftEndIntegral
    (N : ℕ) (s : ℂ) :
    Tendsto (deBruijnNewmanRiemannSiegelLeftEndIntegral N s) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero'
    (g := fun T : ℝ ↦
      deBruijnNewmanRiemannSiegelSideMajorant N s
          (deBruijnNewmanRiemannSiegelRotatedHalfWidth - T) *
        (2 * deBruijnNewmanRiemannSiegelRotatedHalfWidth)) ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun _ ↦ norm_nonneg _
  · filter_upwards [eventually_ge_atTop
        (max 7 ((N : ℝ) + 3))] with T hT
    have hhPos := deBruijnNewmanRiemannSiegelRotatedHalfWidth_pos
    have hhUpper := deBruijnNewmanRiemannSiegelRotatedHalfWidth_le_one_half
    have hT7 : 7 ≤ T := (le_max_left _ _).trans hT
    have hTN : (N : ℝ) + 3 ≤ T := (le_max_right _ _).trans hT
    have hxNonpos : deBruijnNewmanRiemannSiegelRotatedHalfWidth - T ≤ 0 := by linarith
    have hxN : (N : ℝ) + 2 ≤
        |deBruijnNewmanRiemannSiegelRotatedHalfWidth - T| := by
      rw [abs_of_nonpos hxNonpos]
      linarith
    have hx6 : 6 ≤ |deBruijnNewmanRiemannSiegelRotatedHalfWidth - T| := by
      rw [abs_of_nonpos hxNonpos]
      linarith
    unfold deBruijnNewmanRiemannSiegelLeftEndIntegral
    have hbound := norm_deBruijnNewmanRiemannSiegelPullbackKernel_shortSideIntegral_le
      N s _ hxN hx6
    push_cast at hbound
    exact hbound
  · simpa only [zero_mul] using
      (tendsto_deBruijnNewmanRiemannSiegelSideMajorant_sub N s
        deBruijnNewmanRiemannSiegelRotatedHalfWidth).mul_const
          (2 * deBruijnNewmanRiemannSiegelRotatedHalfWidth)

theorem tendsto_deBruijnNewmanRiemannSiegel_symmetricIntervalIntegral
    (N : ℕ) (s : ℂ) :
    Tendsto
      (fun T : ℝ ↦ ∫ v : ℝ in -T..T,
        deBruijnNewmanRiemannSiegelLineIntegrand N s v)
      atTop (𝓝 (deBruijnNewmanRiemannSiegelRawIntegral N s)) := by
  have hlim := intervalIntegral_tendsto_integral
    (integrable_deBruijnNewmanRiemannSiegelLineIntegrand N s)
    tendsto_neg_atTop_atBot tendsto_id
  simpa only [deBruijnNewmanRiemannSiegelRawIntegral, id_eq] using hlim

theorem tendsto_deBruijnNewmanRiemannSiegel_staggeredIntervalIntegral
    (N : ℕ) (s : ℂ) :
    Tendsto
      (fun T : ℝ ↦ ∫ v : ℝ in
        deBruijnNewmanRiemannSiegelParameterStagger - T..
          deBruijnNewmanRiemannSiegelParameterStagger + T,
        deBruijnNewmanRiemannSiegelLineIntegrand N s v)
      atTop (𝓝 (deBruijnNewmanRiemannSiegelRawIntegral N s)) := by
  have hlower : Tendsto
      (fun T : ℝ ↦ deBruijnNewmanRiemannSiegelParameterStagger - T)
      atTop atBot := by
    refine tendsto_atBot.2 fun b ↦ ?_
    exact (eventually_ge_atTop
      (deBruijnNewmanRiemannSiegelParameterStagger - b)).mono fun T hT ↦ by
        linarith
  have hupper : Tendsto
      (fun T : ℝ ↦ deBruijnNewmanRiemannSiegelParameterStagger + T)
      atTop atTop := by
    refine tendsto_atTop.2 fun b ↦ ?_
    exact (eventually_ge_atTop
      (b - deBruijnNewmanRiemannSiegelParameterStagger)).mono fun T hT ↦ by
        linarith
  have hlim := intervalIntegral_tendsto_integral
    (integrable_deBruijnNewmanRiemannSiegelLineIntegrand N s) hlower hupper
  simpa only [deBruijnNewmanRiemannSiegelRawIntegral] using hlim

/-- Exact adjacent shift of the actual infinite Riemann--Siegel source integrals. This is the
infinite-contour endpoint: the crossed pole contributes precisely `(N+1)^(-s)`. -/
theorem deBruijnNewmanRiemannSiegelRawIntegral_adjacent_shift
    (N : ℕ) (s : ℂ) :
    deBruijnNewmanRiemannSiegelRawIntegral N s =
      ((N + 1 : ℕ) : ℂ) ^ (-s) +
        deBruijnNewmanRiemannSiegelRawIntegral (N + 1) s := by
  let F : ℝ → ℂ := fun T ↦
    (∫ v : ℝ in -T..T, deBruijnNewmanRiemannSiegelLineIntegrand N s v) -
      (∫ v : ℝ in
        deBruijnNewmanRiemannSiegelParameterStagger - T..
          deBruijnNewmanRiemannSiegelParameterStagger + T,
        deBruijnNewmanRiemannSiegelLineIntegrand (N + 1) s v) +
      deBruijnNewmanRiemannSiegelRightEndIntegral N s T -
      deBruijnNewmanRiemannSiegelLeftEndIntegral N s T
  have hlimit : Tendsto F atTop
      (𝓝 (deBruijnNewmanRiemannSiegelRawIntegral N s -
        deBruijnNewmanRiemannSiegelRawIntegral (N + 1) s + 0 - 0)) := by
    exact (((tendsto_deBruijnNewmanRiemannSiegel_symmetricIntervalIntegral N s).sub
      (tendsto_deBruijnNewmanRiemannSiegel_staggeredIntervalIntegral (N + 1) s)).add
        (tendsto_deBruijnNewmanRiemannSiegelRightEndIntegral N s)).sub
          (tendsto_deBruijnNewmanRiemannSiegelLeftEndIntegral N s)
  have hfinite : ∀ᶠ T : ℝ in atTop,
      F T = ((N + 1 : ℕ) : ℂ) ^ (-s) := by
    filter_upwards [eventually_gt_atTop
      deBruijnNewmanRiemannSiegelRotatedHalfWidth] with T hT
    exact deBruijnNewmanRiemannSiegel_finite_adjacent_shift N s hT
  have hconstant : Tendsto F atTop (𝓝 (((N + 1 : ℕ) : ℂ) ^ (-s))) := by
    apply tendsto_const_nhds.congr'
    exact hfinite.mono fun T hT ↦ hT.symm
  have heq := tendsto_nhds_unique hlimit hconstant
  linear_combination heq

end

end LeanLab.Riemann
