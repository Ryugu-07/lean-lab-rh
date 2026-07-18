import LeanLab.Riemann.DeBruijnNewmanPolymathHeatKernel
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

set_option linter.style.header false

/-!
# The fixed Riemann--Siegel diagonal contour

This file starts the source-faithful contour formalization used between equations `(xio)` and
`(htz-expand)` in the Polymath de Bruijn--Newman upper-bound paper. The line through
`N + 1 / 2` has the fixed orientation `exp (5 * pi * I / 4)`.
-/

open Complex Filter MeasureTheory Real Set Topology

namespace LeanLab.Riemann

noncomputable section

/-- The source orientation of every `N swarrow N+1` contour. -/
def deBruijnNewmanRiemannSiegelDirection : ℂ :=
  Complex.exp (((5 * Real.pi / 4 : ℝ) : ℂ) * Complex.I)

/-- The fixed midpoint parameterization of the source contour `N swarrow N+1`. -/
def deBruijnNewmanRiemannSiegelLine (N : ℕ) (v : ℝ) : ℂ :=
  (N : ℂ) + 1 / 2 + deBruijnNewmanRiemannSiegelDirection * v

/-- The source direction has the explicit south-west unit-vector coordinates. -/
theorem deBruijnNewmanRiemannSiegelDirection_eq :
    deBruijnNewmanRiemannSiegelDirection =
      (-(Real.sqrt 2 / 2) : ℝ) + (-(Real.sqrt 2 / 2) : ℝ) * Complex.I := by
  rw [deBruijnNewmanRiemannSiegelDirection, Complex.exp_mul_I]
  have hangle : (5 * Real.pi / 4 : ℝ) = Real.pi / 4 + Real.pi := by ring
  rw [hangle, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_add_pi,
    Real.sin_add_pi, Real.cos_pi_div_four, Real.sin_pi_div_four]

@[simp] theorem deBruijnNewmanRiemannSiegelDirection_re :
    deBruijnNewmanRiemannSiegelDirection.re = -(Real.sqrt 2 / 2) := by
  rw [deBruijnNewmanRiemannSiegelDirection_eq]
  simp

@[simp] theorem deBruijnNewmanRiemannSiegelDirection_im :
    deBruijnNewmanRiemannSiegelDirection.im = -(Real.sqrt 2 / 2) := by
  rw [deBruijnNewmanRiemannSiegelDirection_eq]
  simp

/-- Squaring the fixed direction gives `i`, the source of Gaussian contour decay. -/
@[simp] theorem deBruijnNewmanRiemannSiegelDirection_sq :
    deBruijnNewmanRiemannSiegelDirection ^ 2 = Complex.I := by
  rw [deBruijnNewmanRiemannSiegelDirection, ← Complex.exp_nat_mul]
  change Complex.exp ((2 : ℂ) * (((5 * Real.pi / 4 : ℝ) : ℂ) * Complex.I)) = Complex.I
  have harg : (2 : ℂ) * (((5 * Real.pi / 4 : ℝ) : ℂ) * Complex.I) =
      (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) + ((2 * Real.pi : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.exp_add, Complex.exp_mul_I, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp

@[simp] theorem norm_deBruijnNewmanRiemannSiegelDirection :
    ‖deBruijnNewmanRiemannSiegelDirection‖ = 1 := by
  change ‖Complex.exp (((5 * Real.pi / 4 : ℝ) : ℂ) * Complex.I)‖ = 1
  exact Complex.norm_exp_ofReal_mul_I _

@[simp] theorem deBruijnNewmanRiemannSiegelLine_re (N : ℕ) (v : ℝ) :
    (deBruijnNewmanRiemannSiegelLine N v).re =
      N + 1 / 2 - (Real.sqrt 2 / 2) * v := by
  rw [deBruijnNewmanRiemannSiegelLine]
  simp
  ring

@[simp] theorem deBruijnNewmanRiemannSiegelLine_im (N : ℕ) (v : ℝ) :
    (deBruijnNewmanRiemannSiegelLine N v).im = -(Real.sqrt 2 / 2) * v := by
  rw [deBruijnNewmanRiemannSiegelLine]
  simp

/-- Every fixed midpoint line avoids the principal logarithm branch cut. -/
theorem deBruijnNewmanRiemannSiegelLine_mem_slitPlane (N : ℕ) (v : ℝ) :
    deBruijnNewmanRiemannSiegelLine N v ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases hv : v = 0
  · left
    subst v
    simp
    positivity
  · right
    rw [deBruijnNewmanRiemannSiegelLine_im]
    apply mul_ne_zero
    · exact neg_ne_zero.mpr (div_ne_zero (Real.sqrt_ne_zero'.mpr (by norm_num)) (by norm_num))
    · exact hv

/-- The real and imaginary coordinates on the fixed line differ by its positive half-integer
crossing point. -/
theorem deBruijnNewmanRiemannSiegelLine_re_eq (N : ℕ) (v : ℝ) :
    (deBruijnNewmanRiemannSiegelLine N v).re =
      N + 1 / 2 + (deBruijnNewmanRiemannSiegelLine N v).im := by
  rw [deBruijnNewmanRiemannSiegelLine_re, deBruijnNewmanRiemannSiegelLine_im]
  ring

/-- A half-integer midpoint line cannot pass through an integer pole. -/
theorem deBruijnNewmanRiemannSiegelLine_ne_intCast (N : ℕ) (v : ℝ) (n : ℤ) :
    deBruijnNewmanRiemannSiegelLine N v ≠ (n : ℂ) := by
  intro h
  have him := congrArg Complex.im h
  simp only [deBruijnNewmanRiemannSiegelLine_im, Complex.intCast_im] at him
  have hcoeff : -(Real.sqrt 2 / 2) ≠ 0 :=
    neg_ne_zero.mpr (div_ne_zero (Real.sqrt_ne_zero'.mpr (by norm_num)) (by norm_num))
  have hv : v = 0 := (mul_eq_zero.mp him).resolve_left hcoeff
  subst v
  have hre := congrArg Complex.re h
  simp only [deBruijnNewmanRiemannSiegelLine_re, mul_zero, sub_zero, Complex.intCast_re] at hre
  have hparityR : 2 * (N : ℝ) + 1 = 2 * (n : ℝ) := by linarith
  have hparityZ : 2 * (N : ℤ) + 1 = 2 * n := by exact_mod_cast hparityR
  omega

/-- The denominator in the source Riemann--Siegel kernel. -/
def deBruijnNewmanRiemannSiegelDenominator (w : ℂ) : ℂ :=
  Complex.exp (((Real.pi : ℂ) * Complex.I) * w) -
    Complex.exp (-((Real.pi : ℂ) * Complex.I) * w)

/-- The source kernel before multiplication by the completed-zeta prefactor. -/
def deBruijnNewmanRiemannSiegelNumerator (s w : ℂ) : ℂ :=
  w ^ (-s) * Complex.exp (Complex.I * Real.pi * w ^ 2)

/-- The source kernel before multiplication by the completed-zeta prefactor. -/
def deBruijnNewmanRiemannSiegelKernel (s w : ℂ) : ℂ :=
  deBruijnNewmanRiemannSiegelNumerator s w /
    deBruijnNewmanRiemannSiegelDenominator w

/-- The parameterized integrand on the fixed source line. -/
def deBruijnNewmanRiemannSiegelLineIntegrand (N : ℕ) (s : ℂ) (v : ℝ) : ℂ :=
  deBruijnNewmanRiemannSiegelKernel s (deBruijnNewmanRiemannSiegelLine N v) *
    deBruijnNewmanRiemannSiegelDirection

/-- The raw infinite diagonal integral crossing `(N,N+1)`. -/
def deBruijnNewmanRiemannSiegelRawIntegral (N : ℕ) (s : ℂ) : ℂ :=
  ∫ v : ℝ, deBruijnNewmanRiemannSiegelLineIntegrand N s v

/-- The exact completed-zeta prefactor used by Polymath in `R_(0,N)`. -/
def deBruijnNewmanRiemannSiegelPrefactor (s : ℂ) : ℂ :=
  (1 / 8) * (s * (s - 1) / 2) * (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2)

/-- The source remainder `R_(0,N)`. -/
def deBruijnNewmanRiemannSiegelR0N (N : ℕ) (s : ℂ) : ℂ :=
  deBruijnNewmanRiemannSiegelPrefactor s *
    deBruijnNewmanRiemannSiegelRawIntegral N s

/-- The source residue term `r_(0,n)`. -/
def deBruijnNewmanRiemannSiegelR0Term (n : ℕ) (s : ℂ) : ℂ :=
  deBruijnNewmanRiemannSiegelPrefactor s * (n : ℂ) ^ (-s)

/-- Schwarz reflection in the convention used by the Polymath paper. -/
def deBruijnNewmanRiemannSiegelReflect (F : ℂ → ℂ) (s : ℂ) : ℂ :=
  (starRingEnd ℂ) (F ((starRingEnd ℂ) s))

/-- The source denominator has no zero on a fixed half-integer midpoint line. -/
theorem deBruijnNewmanRiemannSiegelDenominator_ne_zero (N : ℕ) (v : ℝ) :
    deBruijnNewmanRiemannSiegelDenominator
      (deBruijnNewmanRiemannSiegelLine N v) ≠ 0 := by
  intro hzero
  let w := deBruijnNewmanRiemannSiegelLine N v
  have hexp :
      Complex.exp (((Real.pi : ℂ) * Complex.I) * w) =
        Complex.exp (-((Real.pi : ℂ) * Complex.I) * w) := by
    exact sub_eq_zero.mp hzero
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
  have hfactor :
      (2 * (Real.pi : ℂ) * Complex.I) * (w - (n : ℂ)) = 0 := by
    calc
      (2 * (Real.pi : ℂ) * Complex.I) * (w - (n : ℂ)) =
          (((Real.pi : ℂ) * Complex.I) * w) -
            (-((Real.pi : ℂ) * Complex.I) * w + (n : ℂ) * (2 * Real.pi * Complex.I)) := by
              ring
      _ = 0 := by rw [← hn]; ring
  have hp : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  have hw : w = (n : ℂ) := sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left hp)
  exact deBruijnNewmanRiemannSiegelLine_ne_intCast N v n hw

/-- The exponential difference is exactly `2 i sin(pi w)`. -/
theorem deBruijnNewmanRiemannSiegelDenominator_eq (w : ℂ) :
    deBruijnNewmanRiemannSiegelDenominator w =
      2 * Complex.sin ((Real.pi : ℂ) * w) * Complex.I := by
  have hpos : ((Real.pi : ℂ) * Complex.I) * w = ((Real.pi : ℂ) * w) * Complex.I := by ring
  have hneg : -((Real.pi : ℂ) * Complex.I) * w = -((Real.pi : ℂ) * w) * Complex.I := by ring
  rw [deBruijnNewmanRiemannSiegelDenominator, hpos, hneg, Complex.two_sin]
  let a := Complex.exp (((Real.pi : ℂ) * w) * Complex.I)
  let b := Complex.exp (-((Real.pi : ℂ) * w) * Complex.I)
  change a - b = (b - a) * Complex.I * Complex.I
  calc
    a - b = -(b - a) := by ring
    _ = (b - a) * (-1) := by ring
    _ = (b - a) * (Complex.I * Complex.I) := by rw [Complex.I_mul_I]
    _ = (b - a) * Complex.I * Complex.I := by ring

/-- Derivative of the source denominator. -/
theorem hasDerivAt_deBruijnNewmanRiemannSiegelDenominator (w : ℂ) :
    HasDerivAt deBruijnNewmanRiemannSiegelDenominator
      (Complex.exp (((Real.pi : ℂ) * Complex.I) * w) * ((Real.pi : ℂ) * Complex.I) -
        Complex.exp (-((Real.pi : ℂ) * Complex.I) * w) *
          (-((Real.pi : ℂ) * Complex.I))) w := by
  let a : ℂ := (Real.pi : ℂ) * Complex.I
  have hpos : HasDerivAt (fun z : ℂ ↦ a * z) a w := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id w).const_mul a
  have hneg : HasDerivAt (fun z : ℂ ↦ (-a) * z) (-a) w := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id w).const_mul (-a)
  change HasDerivAt
    ((fun z : ℂ ↦ Complex.exp (a * z)) - fun z : ℂ ↦ Complex.exp ((-a) * z)) _ w
  exact hpos.cexp.sub hneg.cexp

/-- The exponential at an integral multiple of `pi*i`. -/
theorem exp_pi_mul_I_mul_natCast (n : ℕ) :
    Complex.exp (((Real.pi : ℂ) * Complex.I) * n) = (-1 : ℂ) ^ n := by
  have harg : ((Real.pi : ℂ) * Complex.I) * n = n * ((Real.pi : ℂ) * Complex.I) := by ring
  rw [harg, Complex.exp_nat_mul, Complex.exp_pi_mul_I]

/-- Squaring a natural exponent does not change the corresponding sign. -/
theorem neg_one_pow_sq (n : ℕ) : (-1 : ℂ) ^ (n ^ 2) = (-1 : ℂ) ^ n := by
  apply neg_one_pow_congr
  simp [Nat.even_pow]

/-- Value of the source numerator at a positive integer pole. -/
theorem deBruijnNewmanRiemannSiegelNumerator_natCast
    (n : ℕ) (s : ℂ) :
    deBruijnNewmanRiemannSiegelNumerator s n =
      (n : ℂ) ^ (-s) * (-1 : ℂ) ^ n := by
  rw [deBruijnNewmanRiemannSiegelNumerator]
  congr 1
  have harg : Complex.I * Real.pi * (n : ℂ) ^ 2 =
      ((Real.pi : ℂ) * Complex.I) * (n ^ 2 : ℕ) := by
    push_cast
    ring
  rw [harg, exp_pi_mul_I_mul_natCast, neg_one_pow_sq]

/-- The source denominator vanishes at every natural integer. -/
@[simp] theorem deBruijnNewmanRiemannSiegelDenominator_natCast (n : ℕ) :
    deBruijnNewmanRiemannSiegelDenominator n = 0 := by
  have hneg :
      Complex.exp (-((Real.pi : ℂ) * Complex.I) * n) =
        Complex.exp (((Real.pi : ℂ) * Complex.I) * n) := by
    rw [Complex.exp_eq_exp_iff_exists_int]
    exact ⟨-(n : ℤ), by push_cast; ring⟩
  rw [deBruijnNewmanRiemannSiegelDenominator,
    exp_pi_mul_I_mul_natCast, hneg, exp_pi_mul_I_mul_natCast, sub_self]

/-- The derivative at a natural pole has the exact sign and normalization `2*pi*i`. -/
theorem deriv_deBruijnNewmanRiemannSiegelDenominator_natCast (n : ℕ) :
    deriv deBruijnNewmanRiemannSiegelDenominator n =
      2 * (Real.pi : ℂ) * Complex.I * (-1 : ℂ) ^ n := by
  rw [(hasDerivAt_deBruijnNewmanRiemannSiegelDenominator n).deriv]
  have hpos := exp_pi_mul_I_mul_natCast n
  have hneg : Complex.exp (-((Real.pi : ℂ) * Complex.I) * n) = (-1 : ℂ) ^ n := by
    calc
      Complex.exp (-((Real.pi : ℂ) * Complex.I) * n) =
          Complex.exp (((Real.pi : ℂ) * Complex.I) * n) := by
            rw [Complex.exp_eq_exp_iff_exists_int]
            exact ⟨-(n : ℤ), by push_cast; ring⟩
      _ = (-1 : ℂ) ^ n := hpos
  rw [hpos, hneg]
  ring

/-- The local residue coefficient of the raw kernel is exactly `n^(-s)/(2*pi*i)`. -/
theorem deBruijnNewmanRiemannSiegel_residueCoefficient
    {n : ℕ} (_hn : 0 < n) (s : ℂ) :
    deBruijnNewmanRiemannSiegelNumerator s n /
        deriv deBruijnNewmanRiemannSiegelDenominator n =
      (n : ℂ) ^ (-s) / (2 * (Real.pi : ℂ) * Complex.I) := by
  rw [deBruijnNewmanRiemannSiegelNumerator_natCast n,
    deriv_deBruijnNewmanRiemannSiegelDenominator_natCast]
  have hsign : (-1 : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hpiI : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  field_simp

/-- Kernel-level residue limit at each positive integer pole. This is the local analytic input
for the finite contour shift; no residue theorem is assumed. -/
theorem tendsto_sub_mul_deBruijnNewmanRiemannSiegelKernel
    {n : ℕ} (hn : 0 < n) (s : ℂ) :
    Tendsto
      (fun w : ℂ ↦ (w - n) * deBruijnNewmanRiemannSiegelKernel s w)
      (𝓝[≠] (n : ℂ))
      (𝓝 ((n : ℂ) ^ (-s) / (2 * (Real.pi : ℂ) * Complex.I))) := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hnSlit : (n : ℂ) ∈ Complex.slitPlane := Complex.natCast_mem_slitPlane.mpr hn0
  have hnum : ContinuousAt (deBruijnNewmanRiemannSiegelNumerator s) n := by
    apply (continuousAt_cpow_const hnSlit).mul
    fun_prop
  have hden := hasDerivAt_deBruijnNewmanRiemannSiegelDenominator (n : ℂ)
  have hderiv : deriv deBruijnNewmanRiemannSiegelDenominator n ≠ 0 := by
    rw [deriv_deBruijnNewmanRiemannSiegelDenominator_natCast]
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
        Complex.I_ne_zero)
      (pow_ne_zero _ (by norm_num))
  have hcoef :
      Complex.exp (((Real.pi : ℂ) * Complex.I) * n) * ((Real.pi : ℂ) * Complex.I) -
          Complex.exp (-((Real.pi : ℂ) * Complex.I) * n) *
            (-((Real.pi : ℂ) * Complex.I)) ≠ 0 := by
    rw [← hden.deriv]
    exact hderiv
  have htendsto := hnum.tendsto.mono_left nhdsWithin_le_nhds |>.div
    hden.tendsto_slope hcoef
  rw [← hden.deriv] at htendsto
  rw [deBruijnNewmanRiemannSiegel_residueCoefficient hn s] at htendsto
  apply htendsto.congr'
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hwn : w ≠ (n : ℂ) := hw
  change deBruijnNewmanRiemannSiegelNumerator s w /
      slope deBruijnNewmanRiemannSiegelDenominator (n : ℂ) w =
    (w - n) * (deBruijnNewmanRiemannSiegelNumerator s w /
      deBruijnNewmanRiemannSiegelDenominator w)
  rw [slope_def_field,
    deBruijnNewmanRiemannSiegelDenominator_natCast, sub_zero]
  field_simp

/-- The raw kernel has the exact residue `n^(-s)/(2*pi*i)` at every positive integer. -/
theorem deBruijnNewmanRiemannSiegelKernel_hasResidue
    {n : ℕ} (hn : 0 < n) (s : ℂ) :
    Tendsto
      (fun w : ℂ ↦ (w - n) * deBruijnNewmanRiemannSiegelKernel s w)
      (𝓝[≠] (n : ℂ))
      (𝓝 ((n : ℂ) ^ (-s) / (2 * (Real.pi : ℂ) * Complex.I))) :=
  tendsto_sub_mul_deBruijnNewmanRiemannSiegelKernel hn s

/-- Real-coordinate norm-square formula for the complex sine. -/
theorem normSq_complex_sin (z : ℂ) :
    Complex.normSq (Complex.sin z) =
      (Real.sin z.re * Real.cosh z.im) ^ 2 +
        (Real.cos z.re * Real.sinh z.im) ^ 2 := by
  rw [Complex.sin_eq]
  rw [← Complex.ofReal_sin, ← Complex.ofReal_cosh, ← Complex.ofReal_cos,
    ← Complex.ofReal_sinh]
  simp [Complex.normSq_apply, pow_two, Complex.sin_ofReal_re, Complex.cos_ofReal_re,
    Complex.cosh_ofReal_re, Complex.sinh_ofReal_re]

/-- On the source line, `sin(pi w)` has norm at least one. -/
theorem one_le_norm_sin_pi_mul_riemannSiegelLine (N : ℕ) (v : ℝ) :
    1 ≤ ‖Complex.sin ((Real.pi : ℂ) * deBruijnNewmanRiemannSiegelLine N v)‖ := by
  rw [← one_le_sq_iff₀ (norm_nonneg _), ← Complex.normSq_eq_norm_sq,
    normSq_complex_sin]
  let u : ℝ := Real.pi * (deBruijnNewmanRiemannSiegelLine N v).im
  have hre : (((Real.pi : ℂ) * deBruijnNewmanRiemannSiegelLine N v).re) =
      (u + N * Real.pi) + Real.pi / 2 := by
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, u]
    rw [deBruijnNewmanRiemannSiegelLine_re_eq]
    ring
  have him : (((Real.pi : ℂ) * deBruijnNewmanRiemannSiegelLine N v).im) = u := by
    simp [u, Complex.mul_im]
  rw [hre, him, Real.sin_add_pi_div_two, Real.cos_add_pi_div_two,
    Real.cos_add_nat_mul_pi, Real.sin_add_nat_mul_pi]
  have habs : |Real.sin u| ≤ |Real.sinh u| := by
    calc
      |Real.sin u| ≤ |u| := Real.abs_sin_le_abs
      _ ≤ Real.sinh |u| := Real.self_le_sinh_iff.mpr (abs_nonneg u)
      _ = |Real.sinh u| := (Real.abs_sinh u).symm
  have hsq : Real.sin u ^ 2 ≤ Real.sinh u ^ 2 := by
    exact sq_le_sq.mpr habs
  have htrig := Real.sin_sq_add_cos_sq u
  have htrig' : Real.cos u ^ 2 + Real.sin u ^ 2 = 1 := by nlinarith
  have hcosh := Real.cosh_sq u
  have hsign : ((-1 : ℝ) ^ N) ^ 2 = 1 := by rw [← pow_mul]; simp
  simp only [mul_pow, neg_sq, hsign, one_mul]
  calc
    1 = Real.sin u ^ 2 + Real.cos u ^ 2 := htrig.symm
    _ ≤ Real.sinh u ^ 2 + Real.cos u ^ 2 := by linarith
    _ = (Real.cos u ^ 2 + Real.sin u ^ 2) * Real.sinh u ^ 2 +
        Real.cos u ^ 2 := by rw [htrig']; ring
    _ = Real.cos u ^ 2 * (Real.sinh u ^ 2 + 1) +
        Real.sin u ^ 2 * Real.sinh u ^ 2 := by ring
    _ = Real.cos u ^ 2 * Real.cosh u ^ 2 +
        Real.sin u ^ 2 * Real.sinh u ^ 2 := by rw [hcosh]

/-- The source denominator has the uniform quantitative lower bound `2`. -/
theorem two_le_norm_deBruijnNewmanRiemannSiegelDenominator (N : ℕ) (v : ℝ) :
    2 ≤ ‖deBruijnNewmanRiemannSiegelDenominator
      (deBruijnNewmanRiemannSiegelLine N v)‖ := by
  rw [deBruijnNewmanRiemannSiegelDenominator_eq, norm_mul, norm_mul]
  norm_num
  exact one_le_norm_sin_pi_mul_riemannSiegelLine N v

/-- A coarse global upper bound for the distance along a fixed source line. -/
theorem norm_deBruijnNewmanRiemannSiegelLine_le (N : ℕ) (v : ℝ) :
    ‖deBruijnNewmanRiemannSiegelLine N v‖ ≤ N + 1 / 2 + |v| := by
  calc
    ‖deBruijnNewmanRiemannSiegelLine N v‖ =
        ‖((N : ℂ) + 1 / 2) + deBruijnNewmanRiemannSiegelDirection * v‖ := rfl
    _ ≤ ‖(N : ℂ) + 1 / 2‖ + ‖deBruijnNewmanRiemannSiegelDirection * (v : ℂ)‖ :=
      norm_add_le _ _
    _ = N + 1 / 2 + |v| := by
      rw [norm_mul, norm_deBruijnNewmanRiemannSiegelDirection]
      simp only [one_mul]
      have hmid : (N : ℂ) + 1 / 2 = (((N : ℝ) + 1 / 2 : ℝ) : ℂ) := by norm_num
      rw [hmid, norm_real, norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ N + 1 / 2)]

/-- Every source line stays a uniform positive distance from the origin. The coarse constant
`1/4` is enough to control the principal logarithm globally. -/
theorem one_div_four_le_norm_deBruijnNewmanRiemannSiegelLine (N : ℕ) (v : ℝ) :
    (1 / 4 : ℝ) ≤ ‖deBruijnNewmanRiemannSiegelLine N v‖ := by
  let w := deBruijnNewmanRiemannSiegelLine N v
  let a : ℝ := N + 1 / 2
  have ha : (1 / 2 : ℝ) ≤ a := by simp [a]
  have hre : w.re = a + w.im := by
    simpa [w, a] using deBruijnNewmanRiemannSiegelLine_re_eq N v
  have hnormsq : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hquad : 0 ≤ (a + 2 * w.im) ^ 2 := sq_nonneg _
  have hsquare : (1 / 4 : ℝ) ^ 2 ≤ ‖w‖ ^ 2 := by
    rw [hnormsq, hre]
    nlinarith [sq_nonneg a]
  nlinarith [norm_nonneg w]

/-- The principal logarithm grows at most linearly along every fixed source line. -/
theorem abs_log_norm_deBruijnNewmanRiemannSiegelLine_le (N : ℕ) (v : ℝ) :
    |Real.log ‖deBruijnNewmanRiemannSiegelLine N v‖| ≤
      N + 1 / 2 + |v| + 4 := by
  let x := ‖deBruijnNewmanRiemannSiegelLine N v‖
  have hxLower : (1 / 4 : ℝ) ≤ x :=
    one_div_four_le_norm_deBruijnNewmanRiemannSiegelLine N v
  have hx : 0 < x := lt_of_lt_of_le (by norm_num) hxLower
  have hxUpper : x ≤ N + 1 / 2 + |v| :=
    norm_deBruijnNewmanRiemannSiegelLine_le N v
  have hinv : x⁻¹ ≤ 4 := by
    rw [inv_le_iff_one_le_mul₀' hx]
    nlinarith
  rw [abs_le]
  constructor
  · have hlog := Real.neg_inv_le_log hx.le
    linarith
  · have hlog := Real.log_le_self hx.le
    linarith

/-- The principal complex power contributes at most a linear exponential along the line. -/
theorem norm_cpow_neg_deBruijnNewmanRiemannSiegelLine_le (N : ℕ) (s : ℂ) (v : ℝ) :
    ‖deBruijnNewmanRiemannSiegelLine N v ^ (-s)‖ ≤
      Real.exp
        (|s.re| * (N + 1 / 2 + |v| + 4) + |s.im| * Real.pi) := by
  let w := deBruijnNewmanRiemannSiegelLine N v
  have hw : w ≠ 0 := Complex.slitPlane_ne_zero
    (deBruijnNewmanRiemannSiegelLine_mem_slitPlane N v)
  rw [Complex.cpow_def_of_ne_zero hw, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hlog := abs_log_norm_deBruijnNewmanRiemannSiegelLine_le N v
  have harg := Complex.abs_arg_le_pi w
  rw [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.log_re, Complex.log_im]
  calc
    Real.log ‖w‖ * -s.re - w.arg * -s.im =
        (-s.re) * Real.log ‖w‖ + s.im * w.arg := by ring
    _ ≤ |(-s.re) * Real.log ‖w‖| + |s.im * w.arg| :=
      add_le_add (le_abs_self _) (le_abs_self _)
    _ = |s.re| * |Real.log ‖w‖| + |s.im| * |w.arg| := by
      rw [abs_mul, abs_mul, abs_neg]
    _ ≤ |s.re| * (N + 1 / 2 + |v| + 4) + |s.im| * Real.pi :=
      add_le_add (mul_le_mul_of_nonneg_left hlog (abs_nonneg _))
        (mul_le_mul_of_nonneg_left harg (abs_nonneg _))

/-- The exponential numerator has an exact shifted-Gaussian real exponent on the source line. -/
theorem deBruijnNewmanRiemannSiegel_gaussianExponent_re (N : ℕ) (v : ℝ) :
    (Complex.I * Real.pi * deBruijnNewmanRiemannSiegelLine N v ^ 2).re =
      -Real.pi * v ^ 2 + Real.sqrt 2 * Real.pi * (N + 1 / 2) * v := by
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, mul_zero, sub_zero]
  rw [deBruijnNewmanRiemannSiegelLine_re, deBruijnNewmanRiemannSiegelLine_im]
  have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by positivity)
  ring_nf at hsqrt ⊢
  rw [hsqrt]
  ring

/-- Norm of the oscillatory exponential on the fixed line, before completing the square. -/
theorem norm_exp_deBruijnNewmanRiemannSiegel_gaussian (N : ℕ) (v : ℝ) :
    ‖Complex.exp
      (Complex.I * Real.pi * deBruijnNewmanRiemannSiegelLine N v ^ 2)‖ =
      Real.exp
        (-Real.pi * v ^ 2 + Real.sqrt 2 * Real.pi * (N + 1 / 2) * v) := by
  rw [Complex.norm_exp, deBruijnNewmanRiemannSiegel_gaussianExponent_re]

/-- Linear rate in the global Gaussian majorant. -/
def deBruijnNewmanRiemannSiegelLinearRate (N : ℕ) (s : ℂ) : ℝ :=
  |s.re| + Real.sqrt 2 * Real.pi * (N + 1 / 2)

/-- Constant term obtained after completing the square in the global majorant. -/
def deBruijnNewmanRiemannSiegelMajorantConstant (N : ℕ) (s : ℂ) : ℝ :=
  |s.re| * (N + 1 / 2 + 4) + |s.im| * Real.pi +
    deBruijnNewmanRiemannSiegelLinearRate N s ^ 2 / (2 * Real.pi)

/-- A pure Gaussian majorant for the fixed-line source integrand. -/
def deBruijnNewmanRiemannSiegelMajorant (N : ℕ) (s : ℂ) (v : ℝ) : ℝ :=
  (1 / 2) * Real.exp (deBruijnNewmanRiemannSiegelMajorantConstant N s) *
    Real.exp (-(Real.pi / 2) * v ^ 2)

/-- First pointwise estimate: retain the exact shifted Gaussian and the global complex-power
bound, while using the denominator lower bound `2`. -/
theorem norm_deBruijnNewmanRiemannSiegelLineIntegrand_le_premajorant
    (N : ℕ) (s : ℂ) (v : ℝ) :
    ‖deBruijnNewmanRiemannSiegelLineIntegrand N s v‖ ≤
      (1 / 2) * Real.exp
        (|s.re| * (N + 1 / 2 + |v| + 4) + |s.im| * Real.pi +
          (-Real.pi * v ^ 2 + Real.sqrt 2 * Real.pi * (N + 1 / 2) * v)) := by
  let w := deBruijnNewmanRiemannSiegelLine N v
  have hpow := norm_cpow_neg_deBruijnNewmanRiemannSiegelLine_le N s v
  have hden := two_le_norm_deBruijnNewmanRiemannSiegelDenominator N v
  have hdenPos : 0 < ‖deBruijnNewmanRiemannSiegelDenominator w‖ :=
    lt_of_lt_of_le (by norm_num) hden
  rw [deBruijnNewmanRiemannSiegelLineIntegrand, deBruijnNewmanRiemannSiegelKernel,
    deBruijnNewmanRiemannSiegelNumerator,
    norm_mul, norm_deBruijnNewmanRiemannSiegelDirection, mul_one, norm_div, norm_mul,
    norm_exp_deBruijnNewmanRiemannSiegel_gaussian]
  calc
    ‖w ^ (-s)‖ *
          Real.exp (-Real.pi * v ^ 2 + Real.sqrt 2 * Real.pi * (N + 1 / 2) * v) /
        ‖deBruijnNewmanRiemannSiegelDenominator w‖ ≤
        (Real.exp (|s.re| * (N + 1 / 2 + |v| + 4) + |s.im| * Real.pi) *
          Real.exp (-Real.pi * v ^ 2 + Real.sqrt 2 * Real.pi * (N + 1 / 2) * v)) /
            ‖deBruijnNewmanRiemannSiegelDenominator w‖ := by
              apply div_le_div_of_nonneg_right
              · exact mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _)
              · exact hdenPos.le
    _ ≤ (Real.exp (|s.re| * (N + 1 / 2 + |v| + 4) + |s.im| * Real.pi) *
          Real.exp (-Real.pi * v ^ 2 + Real.sqrt 2 * Real.pi * (N + 1 / 2) * v)) / 2 := by
            exact div_le_div_of_nonneg_left (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
              (by norm_num) hden
    _ = (1 / 2) * Real.exp
        (|s.re| * (N + 1 / 2 + |v| + 4) + |s.im| * Real.pi +
          (-Real.pi * v ^ 2 + Real.sqrt 2 * Real.pi * (N + 1 / 2) * v)) := by
            conv_rhs => rw [Real.exp_add]
            ring

/-- Completion-of-the-square estimate for the absolute-value linear term. -/
theorem deBruijnNewmanRiemannSiegelLinearRate_mul_abs_le (N : ℕ) (s : ℂ) (v : ℝ) :
    deBruijnNewmanRiemannSiegelLinearRate N s * |v| ≤
      Real.pi / 2 * v ^ 2 +
        deBruijnNewmanRiemannSiegelLinearRate N s ^ 2 / (2 * Real.pi) := by
  let C := deBruijnNewmanRiemannSiegelLinearRate N s
  have hpi : 0 < 2 * Real.pi := by positivity
  have hsq : 0 ≤ (Real.pi * |v| - C) ^ 2 := sq_nonneg _
  have hrewrite :
      Real.pi / 2 * v ^ 2 + C ^ 2 / (2 * Real.pi) =
        (Real.pi ^ 2 * v ^ 2 + C ^ 2) / (2 * Real.pi) := by
    field_simp
  rw [hrewrite, le_div_iff₀ hpi]
  nlinarith [sq_abs v]

/-- The source integrand is globally dominated by a pure integrable Gaussian. -/
theorem norm_deBruijnNewmanRiemannSiegelLineIntegrand_le_majorant
    (N : ℕ) (s : ℂ) (v : ℝ) :
    ‖deBruijnNewmanRiemannSiegelLineIntegrand N s v‖ ≤
      deBruijnNewmanRiemannSiegelMajorant N s v := by
  have hpre := norm_deBruijnNewmanRiemannSiegelLineIntegrand_le_premajorant N s v
  have hv : v ≤ |v| := le_abs_self v
  have hsqrt : 0 ≤ Real.sqrt 2 * Real.pi * (N + 1 / 2) := by positivity
  have hlinear := deBruijnNewmanRiemannSiegelLinearRate_mul_abs_le N s v
  apply hpre.trans
  rw [deBruijnNewmanRiemannSiegelMajorant]
  conv_rhs => rw [mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
  simp only [deBruijnNewmanRiemannSiegelMajorantConstant,
    deBruijnNewmanRiemannSiegelLinearRate] at hlinear ⊢
  have hshift :
      Real.sqrt 2 * Real.pi * (N + 1 / 2) * v ≤
        Real.sqrt 2 * Real.pi * (N + 1 / 2) * |v| :=
    mul_le_mul_of_nonneg_left hv hsqrt
  nlinarith

/-- The fixed-line source integrand is continuous. This also records that principal `cpow` is
used only where the line lies in the slit plane. -/
theorem continuous_deBruijnNewmanRiemannSiegelLineIntegrand (N : ℕ) (s : ℂ) :
    Continuous (deBruijnNewmanRiemannSiegelLineIntegrand N s) := by
  have hline : Continuous (deBruijnNewmanRiemannSiegelLine N) := by
    unfold deBruijnNewmanRiemannSiegelLine
    fun_prop
  have hpow : Continuous (fun v : ℝ ↦ deBruijnNewmanRiemannSiegelLine N v ^ (-s)) :=
    continuous_iff_continuousAt.mpr fun v ↦
      (continuousAt_cpow_const
        (deBruijnNewmanRiemannSiegelLine_mem_slitPlane N v)).comp hline.continuousAt
  have hexp : Continuous (fun v : ℝ ↦
      Complex.exp (Complex.I * Real.pi * deBruijnNewmanRiemannSiegelLine N v ^ 2)) := by
    fun_prop
  have hden : Continuous (fun v : ℝ ↦
      deBruijnNewmanRiemannSiegelDenominator (deBruijnNewmanRiemannSiegelLine N v)) := by
    unfold deBruijnNewmanRiemannSiegelDenominator
    fun_prop
  have hquot : Continuous (fun v : ℝ ↦
      deBruijnNewmanRiemannSiegelKernel s (deBruijnNewmanRiemannSiegelLine N v)) := by
    apply (hpow.mul hexp).div hden
    exact deBruijnNewmanRiemannSiegelDenominator_ne_zero N
  exact hquot.mul continuous_const

/-- The pure Gaussian majorant is integrable on the full real line. -/
theorem integrable_deBruijnNewmanRiemannSiegelMajorant (N : ℕ) (s : ℂ) :
    Integrable (deBruijnNewmanRiemannSiegelMajorant N s) := by
  have hgauss : Integrable (fun v : ℝ ↦ Real.exp (-(Real.pi / 2) * v ^ 2)) :=
    integrable_exp_neg_mul_sq (by positivity)
  change Integrable (fun v : ℝ ↦
    ((1 / 2) * Real.exp (deBruijnNewmanRiemannSiegelMajorantConstant N s)) *
      Real.exp (-(Real.pi / 2) * v ^ 2))
  exact hgauss.const_mul
    ((1 / 2) * Real.exp (deBruijnNewmanRiemannSiegelMajorantConstant N s))

/-- Absolute integrability of the actual infinite diagonal source integral. -/
theorem integrable_deBruijnNewmanRiemannSiegelLineIntegrand (N : ℕ) (s : ℂ) :
    Integrable (deBruijnNewmanRiemannSiegelLineIntegrand N s) := by
  refine Integrable.mono' (integrable_deBruijnNewmanRiemannSiegelMajorant N s)
    (continuous_deBruijnNewmanRiemannSiegelLineIntegrand N s).aestronglyMeasurable ?_
  exact ae_of_all _ fun v ↦ norm_deBruijnNewmanRiemannSiegelLineIntegrand_le_majorant N s v

/-- Auditable proper prefix of the Riemann--Siegel contour argument: the actual source kernel is
absolutely integrable on every fixed midpoint line, and every crossed positive integer has the
exact source residue. The finite contour shift is deliberately not part of this theorem. -/
theorem deBruijnNewmanRiemannSiegelContour_prefix (N : ℕ) (s : ℂ) :
    Integrable (deBruijnNewmanRiemannSiegelLineIntegrand N s) ∧
      ∀ n : ℕ, 0 < n →
        Tendsto
          (fun w : ℂ ↦ (w - n) * deBruijnNewmanRiemannSiegelKernel s w)
          (𝓝[≠] (n : ℂ))
          (𝓝 ((n : ℂ) ^ (-s) / (2 * (Real.pi : ℂ) * Complex.I))) := by
  exact ⟨integrable_deBruijnNewmanRiemannSiegelLineIntegrand N s,
    fun _ hn ↦ deBruijnNewmanRiemannSiegelKernel_hasResidue hn s⟩

end

end LeanLab.Riemann
