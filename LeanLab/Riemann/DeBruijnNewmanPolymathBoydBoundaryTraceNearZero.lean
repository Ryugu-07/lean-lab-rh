import LeanLab.Riemann.DeBruijnNewmanPolymathBoydBoundaryTraceTwoScale
import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Near-zero removal for the Boyd boundary trace

This module removes the Gamma pole at the boundary origin and eliminates the near-zero residual
from the Loop 29 two-scale reduction.
-/

namespace LeanLab.Riemann

open Complex Filter MeasureTheory Real Set
open scoped Interval Real Topology

noncomputable section

/-- The principal square-root factor which removes the scaled-Gamma singularity at zero. -/
def deBruijnNewmanPolymathScaledGammaZeroFactor (w : ℂ) : ℂ :=
  Complex.sqrt w * Complex.exp (w - w * Complex.log w) /
    (Real.sqrt (2 * Real.pi) : ℂ)

/-- Although the principal logarithm is singular at zero, multiplication by its argument gives a
globally continuous function there. -/
theorem continuousAt_complex_self_mul_log_zero :
    ContinuousAt (fun w : ℂ => w * Complex.log w) 0 := by
  rw [ContinuousAt, show (0 : ℂ) * Complex.log 0 = 0 by simp,
    tendsto_zero_iff_norm_tendsto_zero]
  have hmul : Tendsto (fun w : ℂ => ‖w‖ * Real.log ‖w‖) (𝓝 0) (𝓝 0) := by
    have hc : ContinuousAt
        ((fun x : ℝ => x * Real.log x) ∘ fun w : ℂ => ‖w‖) 0 :=
      (Real.continuous_mul_log.comp
        (continuous_norm : Continuous fun w : ℂ => ‖w‖)).continuousAt
    change Tendsto
      ((fun x : ℝ => x * Real.log x) ∘ fun w : ℂ => ‖w‖)
      (𝓝 0) (𝓝 (((fun x : ℝ => x * Real.log x) ∘ fun w : ℂ => ‖w‖) 0)) at hc
    simpa only [Function.comp_def, norm_zero, Real.log_zero, mul_zero] using hc
  have habs : Tendsto (fun w : ℂ => ‖‖w‖ * Real.log ‖w‖‖) (𝓝 0) (𝓝 0) := by
    simpa using hmul.norm
  have hlinear : Tendsto (fun w : ℂ => Real.pi * ‖w‖) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul
      (continuous_norm.continuousAt : ContinuousAt (fun w : ℂ => ‖w‖) 0))
  have hbound : Tendsto
      (fun w : ℂ => ‖‖w‖ * Real.log ‖w‖‖ + Real.pi * ‖w‖)
      (𝓝 0) (𝓝 0) := by
    simpa using habs.add hlinear
  refine squeeze_zero (fun w => norm_nonneg (w * Complex.log w)) (fun w => ?_) hbound
  calc
    ‖w * Complex.log w‖ = ‖w‖ * ‖Complex.log w‖ := norm_mul _ _
    _ ≤ ‖w‖ * (|Real.log ‖w‖| + Real.pi) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg w)
      calc
        ‖Complex.log w‖ ≤ |(Complex.log w).re| + |(Complex.log w).im| :=
          Complex.norm_le_abs_re_add_abs_im _
        _ = |Real.log ‖w‖| + |Complex.arg w| := by
          rw [Complex.log_re, Complex.log_im]
        _ ≤ |Real.log ‖w‖| + Real.pi := by
          exact add_le_add (le_refl _) (Complex.abs_arg_le_pi w)
    _ = ‖‖w‖ * Real.log ‖w‖‖ + Real.pi * ‖w‖ := by
      rw [Real.norm_eq_abs, abs_mul, abs_norm]
      ring

theorem continuousAt_deBruijnNewmanPolymathScaledGammaZeroFactor_zero :
    ContinuousAt deBruijnNewmanPolymathScaledGammaZeroFactor 0 := by
  unfold deBruijnNewmanPolymathScaledGammaZeroFactor
  have hsqrt : ContinuousAt Complex.sqrt 0 :=
    Complex.continuousAt_sqrt (Or.inl (by simp))
  have hexp : ContinuousAt
      (fun w : ℂ => Complex.exp (w - w * Complex.log w)) 0 :=
    (continuousAt_id.sub continuousAt_complex_self_mul_log_zero).cexp
  exact (hsqrt.mul hexp).div_const _

/-- Exact global removal of the Gamma pole, including the totalized value at zero. -/
theorem deBruijnNewmanPolymath_self_mul_scaledGamma_eq_zeroFactor
    (w : ℂ) :
    w * deBruijnNewmanPolymathScaledGamma w =
      Complex.Gamma (w + 1) * deBruijnNewmanPolymathScaledGammaZeroFactor w := by
  by_cases hw : w = 0
  · simp [hw, deBruijnNewmanPolymathScaledGammaZeroFactor]
  have hsqrt := sqrt_eq_exp hw
  have hgamma := Complex.Gamma_add_one w hw
  have hinvMain :
      ((Real.sqrt (2 * Real.pi) : ℂ) *
        Complex.exp ((w - 1 / 2) * Complex.log w - w))⁻¹ =
      Complex.exp (Complex.log w / 2) *
        Complex.exp (w - w * Complex.log w) /
          (Real.sqrt (2 * Real.pi) : ℂ) := by
    have hexp :
        Complex.exp (-((w - 1 / 2) * Complex.log w - w)) =
          Complex.exp (Complex.log w / 2) *
            Complex.exp (w - w * Complex.log w) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    rw [mul_inv, ← Complex.exp_neg, hexp, div_eq_mul_inv]
    ring
  rw [deBruijnNewmanPolymathScaledGamma,
    deBruijnNewmanPolymathGammaStirlingMain,
    deBruijnNewmanPolymathScaledGammaZeroFactor, div_eq_mul_inv,
    hinvMain, hgamma, hsqrt]
  ring

/-- The reciprocal scaled Gamma function has the same principal square-root zero. -/
theorem deBruijnNewmanPolymath_inv_scaledGamma_eq_zeroFactor
    (w : ℂ) :
    (1 : ℂ) / deBruijnNewmanPolymathScaledGamma w =
      (Real.sqrt (2 * Real.pi) : ℂ) * Complex.sqrt w *
        Complex.exp (w * Complex.log w - w) / Complex.Gamma (w + 1) := by
  by_cases hw : w = 0
  · simp [hw, deBruijnNewmanPolymathScaledGamma]
  have hsqrt := sqrt_eq_exp hw
  have hinvGamma := Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one w
  have hmain :
      Complex.exp ((w - 1 / 2) * Complex.log w - w) * w =
        Complex.exp (Complex.log w / 2) *
          Complex.exp (w * Complex.log w - w) := by
    conv_lhs =>
      rhs
      rw [← Complex.exp_log hw]
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  rw [deBruijnNewmanPolymathScaledGamma,
    deBruijnNewmanPolymathGammaStirlingMain, one_div_div,
    div_eq_mul_inv, hinvGamma, hsqrt]
  rw [show (Real.sqrt (2 * Real.pi) : ℂ) *
      Complex.exp ((w - 1 / 2) * Complex.log w - w) *
        (w * (Complex.Gamma (w + 1))⁻¹) =
      (Real.sqrt (2 * Real.pi) : ℂ) *
        (Complex.exp ((w - 1 / 2) * Complex.log w - w) * w) *
          (Complex.Gamma (w + 1))⁻¹ by ring,
    hmain]
  ring

theorem deBruijnNewmanPolymath_self_mul_scaledGamma_continuousAt_zero :
    ContinuousAt
      (fun w : ℂ => w * deBruijnNewmanPolymathScaledGamma w) 0 := by
  rw [funext deBruijnNewmanPolymath_self_mul_scaledGamma_eq_zeroFactor]
  have hgamma : ContinuousAt (fun w : ℂ => Complex.Gamma (w + 1)) 0 :=
    Complex.continuousAt_Gamma_one.comp_of_eq
      (continuousAt_id.add_const 1) (by simp)
  exact hgamma.mul continuousAt_deBruijnNewmanPolymathScaledGammaZeroFactor_zero

theorem deBruijnNewmanPolymath_inv_scaledGamma_continuousAt_zero :
    ContinuousAt
      (fun w : ℂ => (1 : ℂ) / deBruijnNewmanPolymathScaledGamma w) 0 := by
  rw [funext deBruijnNewmanPolymath_inv_scaledGamma_eq_zeroFactor]
  have hsqrt : ContinuousAt Complex.sqrt 0 :=
    Complex.continuousAt_sqrt (Or.inl (by simp))
  have hexp : ContinuousAt
      (fun w : ℂ => Complex.exp (w * Complex.log w - w)) 0 :=
    (continuousAt_complex_self_mul_log_zero.sub continuousAt_id).cexp
  have hgamma : ContinuousAt (fun w : ℂ => Complex.Gamma (w + 1)) 0 :=
    Complex.continuousAt_Gamma_one.comp_of_eq
      (continuousAt_id.add_const 1) (by simp)
  have hgamma0 : Complex.Gamma ((0 : ℂ) + 1) ≠ 0 := by simp
  exact ((continuousAt_const.mul hsqrt).mul hexp).div hgamma hgamma0

theorem deBruijnNewmanPolymath_self_mul_scaledGamma_continuousAt_of_re_nonneg
    {w : ℂ} (hwre : 0 ≤ w.re) :
    ContinuousAt (fun u : ℂ => u * deBruijnNewmanPolymathScaledGamma u) w := by
  by_cases hw0 : w = 0
  · simpa [hw0] using
      deBruijnNewmanPolymath_self_mul_scaledGamma_continuousAt_zero
  have hslit : w ∈ Complex.slitPlane := by
    rcases hwre.eq_or_lt with hre | hre
    · right
      intro him
      exact hw0 (Complex.ext hre.symm (by simpa using him))
    · exact Or.inl hre
  have hnotpole : ∀ m : ℕ, w ≠ -m := by
    intro m hm
    have hre : w.re = -(m : ℝ) := by
      simpa using congrArg Complex.re hm
    have hmNonneg : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hmReal : (m : ℝ) = 0 := by nlinarith
    have hmNat : m = 0 := Nat.cast_eq_zero.mp hmReal
    exact hw0 (by simpa [hmNat] using hm)
  exact continuousAt_id.mul
    (deBruijnNewmanPolymathScaledGamma_differentiableAt
      hslit hnotpole).continuousAt

theorem deBruijnNewmanPolymath_inv_scaledGamma_continuousAt_of_re_nonneg
    {w : ℂ} (hwre : 0 ≤ w.re) :
    ContinuousAt
      (fun u : ℂ => (1 : ℂ) / deBruijnNewmanPolymathScaledGamma u) w := by
  by_cases hw0 : w = 0
  · simpa [hw0] using
      deBruijnNewmanPolymath_inv_scaledGamma_continuousAt_zero
  have hslit : w ∈ Complex.slitPlane := by
    rcases hwre.eq_or_lt with hre | hre
    · right
      intro him
      exact hw0 (Complex.ext hre.symm (by simpa using him))
    · exact Or.inl hre
  have hnotpole : ∀ m : ℕ, w ≠ -m := by
    intro m hm
    have hre : w.re = -(m : ℝ) := by
      simpa using congrArg Complex.re hm
    have hmNonneg : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hmReal : (m : ℝ) = 0 := by nlinarith
    have hmNat : m = 0 := Nat.cast_eq_zero.mp hmReal
    exact hw0 (by simpa [hmNat] using hm)
  exact (deBruijnNewmanPolymathScaledGamma_inv_differentiableAt
    hslit hnotpole).continuousAt

/-- The pole-free expression for the paired offset kernel, defined also at the boundary origin. -/
def deBruijnNewmanPolymathBoydNearZeroRegularizedPairIntegrand
    (z : ℂ) (epsilon y : ℝ) : ℂ :=
  let w : ℂ := (epsilon : ℂ) + (y : ℂ) * Complex.I
  let q : ℂ := -(epsilon : ℂ) + (y : ℂ) * Complex.I
  Complex.I *
    (((w * deBruijnNewmanPolymathScaledGamma w - w) / (w - z)) -
      ((q / deBruijnNewmanPolymathScaledGamma (-q) - q) / (q - z)) +
      (epsilon : ℂ) / (6 * (w - z) * (q - z)))

/-- The Loop 29 normal form remains exact at zero offset, including the totalized origin. -/
theorem deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand_eq_nearZeroRegularized_of_nonneg
    {z : ℂ} {epsilon y : ℝ} (hepsilon : 0 ≤ epsilon)
    (hepsilonz : epsilon < z.re) :
    deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand z epsilon y =
      deBruijnNewmanPolymathBoydNearZeroRegularizedPairIntegrand z epsilon y := by
  by_cases hzero : epsilon = 0 ∧ y = 0
  · rcases hzero with ⟨rfl, rfl⟩
    simp [deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand,
      deBruijnNewmanPolymathBoydR2CauchyWeight,
      deBruijnNewmanPolymathBoydInverseR2CauchyWeight,
      deBruijnNewmanPolymathBoydNearZeroRegularizedPairIntegrand]
  let w : ℂ := (epsilon : ℂ) + (y : ℂ) * Complex.I
  let q : ℂ := -(epsilon : ℂ) + (y : ℂ) * Complex.I
  have hw0 : w ≠ 0 := by
    intro h
    apply hzero
    constructor
    · have hre := congrArg Complex.re h
      simpa [w] using hre
    · have him := congrArg Complex.im h
      simpa [w] using him
  have hq0 : q ≠ 0 := by
    intro h
    apply hzero
    constructor
    · have hre := congrArg Complex.re h
      have : -epsilon = 0 := by simpa [q] using hre
      linarith
    · have him := congrArg Complex.im h
      simpa [q] using him
  have hwz : w - z ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    have hre := congrArg Complex.re h
    simp [w] at hre
    linarith
  have hqz : q - z ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    have hre := congrArg Complex.re h
    simp [q] at hre
    linarith
  have hright : deBruijnNewmanPolymathBoydR2CauchyWeight w =
      w * deBruijnNewmanPolymathScaledGamma w - w - 1 / 12 := by
    rw [deBruijnNewmanPolymathBoydR2CauchyWeight,
      deBruijnNewmanPolymathGammaStirlingR2]
    change w * (deBruijnNewmanPolymathScaledGamma w - 1 - 1 / (12 * w)) = _
    field_simp [hw0]
  have hleft : deBruijnNewmanPolymathBoydInverseR2CauchyWeight q =
      q / deBruijnNewmanPolymathScaledGamma (-q) - q - 1 / 12 := by
    rw [deBruijnNewmanPolymathBoydInverseR2CauchyWeight,
      deBruijnNewmanPolymathScaledGammaInverseR2]
    field_simp [hq0]
    ring
  rw [deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand,
    deBruijnNewmanPolymathBoydNearZeroRegularizedPairIntegrand]
  change Complex.I *
    (deBruijnNewmanPolymathBoydR2CauchyWeight w / (w - z) -
      deBruijnNewmanPolymathBoydInverseR2CauchyWeight q / (q - z)) =
    Complex.I *
      (((w * deBruijnNewmanPolymathScaledGamma w - w) / (w - z)) -
        ((q / deBruijnNewmanPolymathScaledGamma (-q) - q) / (q - z)) +
        (epsilon : ℂ) / (6 * (w - z) * (q - z)))
  rw [hright, hleft]
  field_simp [hwz, hqz]
  ring

theorem deBruijnNewmanPolymathBoydNearZeroRegularizedPairIntegrand_zero
    {z : ℂ} (hz : 0 < z.re) (y : ℝ) :
    deBruijnNewmanPolymathBoydNearZeroRegularizedPairIntegrand z 0 y =
      deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand z y := by
  rw [← deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand_eq_nearZeroRegularized_of_nonneg
    (z := z) (epsilon := 0) (y := y) (le_refl 0) hz]
  by_cases hy : y = 0
  · subst y
    simp [deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand,
      deBruijnNewmanPolymathBoydR2CauchyWeight,
      deBruijnNewmanPolymathBoydInverseR2CauchyWeight,
      deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand]
  · exact deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand_zero z hy

/-- Joint continuity of the pole-free pair on a right-offset slab crossing the boundary origin. -/
theorem deBruijnNewmanPolymathBoydNearZeroRegularizedPairIntegrand_continuousOn_slab_near
    {z : ℂ} {r delta : ℝ} (hrz : r < z.re) :
    ContinuousOn
      (fun p : ℝ × ℝ =>
        deBruijnNewmanPolymathBoydNearZeroRegularizedPairIntegrand z p.1 p.2)
      (Icc 0 r ×ˢ Icc (-delta) delta) := by
  intro p hp
  let w : ℂ := (p.1 : ℂ) + (p.2 : ℂ) * Complex.I
  let q : ℂ := -(p.1 : ℂ) + (p.2 : ℂ) * Complex.I
  have hepsilonPath : ContinuousAt
      (fun x : ℝ × ℝ => (x.1 : ℂ)) p := by fun_prop
  have hwPath : ContinuousAt
      (fun x : ℝ × ℝ => (x.1 : ℂ) + (x.2 : ℂ) * Complex.I) p := by
    fun_prop
  have hqPath : ContinuousAt
      (fun x : ℝ × ℝ => -(x.1 : ℂ) + (x.2 : ℂ) * Complex.I) p := by
    fun_prop
  have hwre : 0 ≤ w.re := by simpa [w] using hp.1.1
  have hnegqre : 0 ≤ (-q).re := by simpa [q] using hp.1.1
  have hself : ContinuousAt
      (fun x : ℝ × ℝ =>
        ((x.1 : ℂ) + (x.2 : ℂ) * Complex.I) *
          deBruijnNewmanPolymathScaledGamma
            ((x.1 : ℂ) + (x.2 : ℂ) * Complex.I)) p :=
    (deBruijnNewmanPolymath_self_mul_scaledGamma_continuousAt_of_re_nonneg
      hwre).comp_of_eq hwPath rfl
  have hinv : ContinuousAt
      (fun x : ℝ × ℝ => (1 : ℂ) /
        deBruijnNewmanPolymathScaledGamma
          (-(-(x.1 : ℂ) + (x.2 : ℂ) * Complex.I))) p :=
    (deBruijnNewmanPolymath_inv_scaledGamma_continuousAt_of_re_nonneg
      hnegqre).comp_of_eq hqPath.neg rfl
  have hqInv : ContinuousAt
      (fun x : ℝ × ℝ =>
        (-(x.1 : ℂ) + (x.2 : ℂ) * Complex.I) /
          deBruijnNewmanPolymathScaledGamma
            (-(-(x.1 : ℂ) + (x.2 : ℂ) * Complex.I))) p := by
    exact (hqPath.mul hinv).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun x => by
        simp only [Pi.mul_apply, div_eq_mul_inv, one_mul])
  have hwDen : ContinuousAt
      (fun x : ℝ × ℝ => (x.1 : ℂ) + (x.2 : ℂ) * Complex.I - z) p := by
    fun_prop
  have hqDen : ContinuousAt
      (fun x : ℝ × ℝ => -(x.1 : ℂ) + (x.2 : ℂ) * Complex.I - z) p := by
    fun_prop
  have hwz : w - z ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    have hre := congrArg Complex.re h
    have hpz : p.1 < z.re := lt_of_le_of_lt hp.1.2 hrz
    simp [w] at hre
    linarith
  have hzpos : 0 < z.re := lt_of_le_of_lt hp.1.1 (lt_of_le_of_lt hp.1.2 hrz)
  have hqz : q - z ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    have hre := congrArg Complex.re h
    simp [q] at hre
    nlinarith [hp.1.1, hzpos]
  have hright : ContinuousAt
      (fun x : ℝ × ℝ =>
        ((((x.1 : ℂ) + (x.2 : ℂ) * Complex.I) *
            deBruijnNewmanPolymathScaledGamma
              ((x.1 : ℂ) + (x.2 : ℂ) * Complex.I)) -
          ((x.1 : ℂ) + (x.2 : ℂ) * Complex.I)) /
            ((x.1 : ℂ) + (x.2 : ℂ) * Complex.I - z)) p :=
    (hself.sub hwPath).div hwDen hwz
  have hleft : ContinuousAt
      (fun x : ℝ × ℝ =>
        (((-(x.1 : ℂ) + (x.2 : ℂ) * Complex.I) /
            deBruijnNewmanPolymathScaledGamma
              (-(-(x.1 : ℂ) + (x.2 : ℂ) * Complex.I))) -
          (-(x.1 : ℂ) + (x.2 : ℂ) * Complex.I)) /
            (-(x.1 : ℂ) + (x.2 : ℂ) * Complex.I - z)) p :=
    (hqInv.sub hqPath).div hqDen hqz
  have hdenProduct : 6 * (w - z) * (q - z) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) hwz) hqz
  have hcorrection : ContinuousAt
      (fun x : ℝ × ℝ =>
        (x.1 : ℂ) /
          (6 * ((x.1 : ℂ) + (x.2 : ℂ) * Complex.I - z) *
            (-(x.1 : ℂ) + (x.2 : ℂ) * Complex.I - z))) p :=
    hepsilonPath.div ((continuousAt_const.mul hwDen).mul hqDen) hdenProduct
  have hI : ContinuousAt (fun _ : ℝ × ℝ => Complex.I) p := continuousAt_const
  have htotal := hI.mul ((hright.sub hleft).add hcorrection)
  exact (htotal.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun x => by
      simp only [Pi.mul_apply, Pi.add_apply,
        deBruijnNewmanPolymathBoydNearZeroRegularizedPairIntegrand])).continuousWithinAt

/-- The paired offset kernel converges uniformly through the boundary origin when the offset
approaches zero from the right. -/
theorem deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand_tendstoUniformlyOn_near
    {z : ℂ} (hz : 0 < z.re) {delta : ℝ} (_hdelta : 0 < delta) :
    TendstoUniformlyOn
      (fun epsilon y =>
        deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand z epsilon y)
      (deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand z)
      (𝓝[Ici 0] 0)
      (Icc (-delta) delta) := by
  let r : ℝ := z.re / 2
  let U : Set ℝ := Icc 0 r
  let V : Set ℝ := Icc (-delta) delta
  have hr : 0 < r := by simp [r, hz]
  have hrz : r < z.re := by dsimp [r]; linarith
  have hcompact : IsCompact (U ×ˢ V) := isCompact_Icc.prod isCompact_Icc
  have hcontinuous : ContinuousOn
      (fun p : ℝ × ℝ =>
        deBruijnNewmanPolymathBoydNearZeroRegularizedPairIntegrand z p.1 p.2)
      (U ×ˢ V) := by
    exact deBruijnNewmanPolymathBoydNearZeroRegularizedPairIntegrand_continuousOn_slab_near
      hrz
  have huniform : UniformContinuousOn
      (Function.uncurry fun epsilon y =>
        deBruijnNewmanPolymathBoydNearZeroRegularizedPairIntegrand z epsilon y)
      (U ×ˢ V) :=
    hcompact.uniformContinuousOn_of_continuous hcontinuous
  have hzero : (0 : ℝ) ∈ U := by simp [U, hr.le]
  have hfilters : 𝓝[U] (0 : ℝ) = 𝓝[Ici 0] 0 := by
    rw [nhdsWithin_eq_iff_eventuallyEq]
    filter_upwards [Iio_mem_nhds hr] with epsilon hepsilon
    have hlt : epsilon < r := by simpa only [mem_Iio] using hepsilon
    apply propext
    change (0 ≤ epsilon ∧ epsilon ≤ r) ↔ 0 ≤ epsilon
    exact and_iff_left hlt.le
  have hraw : TendstoUniformlyOn
      (fun epsilon y =>
        deBruijnNewmanPolymathBoydNearZeroRegularizedPairIntegrand z epsilon y)
      (fun y =>
        deBruijnNewmanPolymathBoydNearZeroRegularizedPairIntegrand z 0 y)
      (𝓝[Ici 0] 0) V := by
    rw [← hfilters]
    exact huniform.tendstoUniformlyOn hzero
  have haxis : TendstoUniformlyOn
      (fun epsilon y =>
        deBruijnNewmanPolymathBoydNearZeroRegularizedPairIntegrand z epsilon y)
      (deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand z)
      (𝓝[Ici 0] 0) V :=
    hraw.congr_right fun y _hy =>
      deBruijnNewmanPolymathBoydNearZeroRegularizedPairIntegrand_zero hz y
  have hepsilon : ∀ᶠ epsilon in 𝓝[Ici 0] (0 : ℝ), epsilon ∈ Icc 0 r := by
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds hr)] with epsilon hepsilon hlt
    exact ⟨hepsilon, hlt.le⟩
  have heq : ∀ᶠ epsilon in 𝓝[Ici 0] (0 : ℝ),
      Set.EqOn
        (fun y =>
          deBruijnNewmanPolymathBoydNearZeroRegularizedPairIntegrand z epsilon y)
        (fun y =>
          deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand z epsilon y)
        V := by
    filter_upwards [hepsilon] with epsilon hepsilon
    intro y _hy
    exact (deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand_eq_nearZeroRegularized_of_nonneg
      hepsilon.1 (lt_of_le_of_lt hepsilon.2 hrz)).symm
  exact haxis.congr heq

/-- The complete fixed near-zero residual vanishes as the offset approaches zero from the
right. -/
theorem deBruijnNewmanPolymathBoydBoundaryNearResidual_tendsto
    {z : ℂ} (hz : 0 < z.re) {delta : ℝ} (hdelta : 0 < delta) :
    Filter.Tendsto
      (fun epsilon =>
        deBruijnNewmanPolymathBoydBoundaryNearResidual z epsilon delta)
      (𝓝[Ici 0] 0) (𝓝 0) := by
  have huniform :=
    deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand_tendstoUniformlyOn_near
      hz hdelta
  have hnegdelta : -delta ≤ delta := by linarith
  have hintegral : Filter.Tendsto
      (fun epsilon => ∫ y : ℝ in -delta..delta,
        deBruijnNewmanPolymathBoydBoundaryTraceErrorIntegrand z epsilon y)
      (𝓝[Ici 0] 0) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro eta heta
    let c : ℝ := eta / (|delta - (-delta)| + 1)
    have hlength : 0 < |delta - (-delta)| + 1 := by positivity
    have hc : 0 < c := div_pos heta hlength
    have heventually := (Metric.tendstoUniformlyOn_iff.mp huniform) c hc
    filter_upwards [heventually] with epsilon hepsilon
    have hnorm :
        ‖∫ y : ℝ in -delta..delta,
          deBruijnNewmanPolymathBoydBoundaryTraceErrorIntegrand z epsilon y‖ ≤
          c * |delta - (-delta)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro y hy
      have hy' : y ∈ Icc (-delta) delta := by
        have hy'' := uIoc_subset_uIcc hy
        rw [uIcc_of_le hnegdelta] at hy''
        exact hy''
      have hdist := hepsilon y hy'
      exact (by
        simpa only [deBruijnNewmanPolymathBoydBoundaryTraceErrorIntegrand,
          dist_eq_norm, norm_sub_rev] using hdist.le)
    rw [dist_zero_right]
    calc
      ‖∫ y : ℝ in -delta..delta,
          deBruijnNewmanPolymathBoydBoundaryTraceErrorIntegrand z epsilon y‖
          ≤ c * |delta - (-delta)| := hnorm
      _ < c * (|delta - (-delta)| + 1) := by
        exact mul_lt_mul_of_pos_left
          (by linarith [abs_nonneg (delta - (-delta))]) hc
      _ = eta := by
        dsimp [c]
        exact div_mul_cancel₀ eta (ne_of_gt hlength)
  have hconst : Filter.Tendsto
      (fun _ : ℝ => -(1 / (2 * Real.pi * Complex.I * z)))
      (𝓝[Ici 0] 0) (𝓝 (-(1 / (2 * Real.pi * Complex.I * z)))) :=
    tendsto_const_nhds
  simpa [deBruijnNewmanPolymathBoydBoundaryNearResidual,
    deBruijnNewmanPolymathBoydBoundarySegmentResidual] using
      hconst.mul hintegral

/-- The near-zero residual vanishes along the canonical positive offset sequence. -/
theorem deBruijnNewmanPolymathBoydBoundaryNearResidual_tendsto_canonical
    {z : ℂ} (hz : 0 < z.re) {delta : ℝ} (hdelta : 0 < delta) :
    Filter.Tendsto
      (fun n : ℕ => deBruijnNewmanPolymathBoydBoundaryNearResidual z
        (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) delta)
      Filter.atTop (𝓝 0) := by
  have hepsilonRight : Filter.Tendsto
      (deBruijnNewmanPolymathBoydBoundaryEpsilon z)
      Filter.atTop (𝓝[Ici 0] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (deBruijnNewmanPolymathBoydBoundaryEpsilon_tendsto_zero z)
      (Filter.Eventually.of_forall fun n =>
        mem_Ici.mpr (deBruijnNewmanPolymathBoydBoundaryEpsilon_pos hz n).le)
  exact (deBruijnNewmanPolymathBoydBoundaryNearResidual_tendsto hz hdelta).comp
    hepsilonRight

/-- After the boundary-origin singularity is removed, the complete trace discrepancy is exactly
equivalent to the shifted-tail residual alone. -/
theorem deBruijnNewmanPolymathBoydBoundaryTrace_tendsto_iff_tail
    {z : ℂ} (hz : 0 < z.re) {A : ℝ} (hA : 0 < A) :
    Filter.Tendsto
        (deBruijnNewmanPolymathBoydBoundaryTraceDiscrepancy z)
        Filter.atTop (𝓝 0) ↔
      Filter.Tendsto
        (fun n : ℕ => deBruijnNewmanPolymathBoydBoundaryTailResidual z
          (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) A
          (deBruijnNewmanPolymathBoydBoundaryHeight z n))
        Filter.atTop (𝓝 0) := by
  have hnear :=
    deBruijnNewmanPolymathBoydBoundaryNearResidual_tendsto_canonical hz hA
  have hnearTailIff :=
    deBruijnNewmanPolymathBoydBoundaryTrace_tendsto_iff_near_add_tail
      hz hA (le_refl A)
  constructor
  · intro hdiscrepancy
    have hnearTail := hnearTailIff.mp hdiscrepancy
    simpa using hnearTail.sub hnear
  · intro htail
    exact hnearTailIff.mpr (by simpa using hnear.add htail)

/-- Auditable Loop 30 certificate: both scaled-Gamma boundary factors are removable, the entire
near residual vanishes, and the remaining trace problem is exactly the shifted tail. -/
def deBruijnNewmanPolymathBoydBoundaryTraceNearZeroCertificateStatement : Prop :=
  (∀ w : ℂ,
    w * deBruijnNewmanPolymathScaledGamma w =
      Complex.Gamma (w + 1) * deBruijnNewmanPolymathScaledGammaZeroFactor w) ∧
  (∀ w : ℂ,
    (1 : ℂ) / deBruijnNewmanPolymathScaledGamma w =
      (Real.sqrt (2 * Real.pi) : ℂ) * Complex.sqrt w *
        Complex.exp (w * Complex.log w - w) / Complex.Gamma (w + 1)) ∧
  ContinuousAt
    (fun w : ℂ => w * deBruijnNewmanPolymathScaledGamma w) 0 ∧
  ContinuousAt
    (fun w : ℂ => (1 : ℂ) / deBruijnNewmanPolymathScaledGamma w) 0 ∧
  (∀ (z : ℂ), 0 < z.re → ∀ (delta : ℝ), 0 < delta →
    TendstoUniformlyOn
      (fun epsilon y =>
        deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand z epsilon y)
      (deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand z)
      (𝓝[Ici 0] 0)
      (Icc (-delta) delta)) ∧
  (∀ (z : ℂ), 0 < z.re → ∀ (delta : ℝ), 0 < delta →
    Filter.Tendsto
      (fun n : ℕ => deBruijnNewmanPolymathBoydBoundaryNearResidual z
        (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) delta)
      Filter.atTop (𝓝 0)) ∧
  (∀ (z : ℂ), 0 < z.re → ∀ (A : ℝ), 0 < A →
    (Filter.Tendsto
        (deBruijnNewmanPolymathBoydBoundaryTraceDiscrepancy z)
        Filter.atTop (𝓝 0) ↔
      Filter.Tendsto
        (fun n : ℕ => deBruijnNewmanPolymathBoydBoundaryTailResidual z
          (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) A
          (deBruijnNewmanPolymathBoydBoundaryHeight z n))
        Filter.atTop (𝓝 0)))

/-- The complete unconditional Loop 30 near-zero elimination certificate. -/
theorem deBruijnNewmanPolymathBoydBoundaryTraceNearZeroCertificate :
    deBruijnNewmanPolymathBoydBoundaryTraceNearZeroCertificateStatement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact deBruijnNewmanPolymath_self_mul_scaledGamma_eq_zeroFactor
  · exact deBruijnNewmanPolymath_inv_scaledGamma_eq_zeroFactor
  · exact deBruijnNewmanPolymath_self_mul_scaledGamma_continuousAt_zero
  · exact deBruijnNewmanPolymath_inv_scaledGamma_continuousAt_zero
  · exact fun _ hz _ hdelta =>
      deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand_tendstoUniformlyOn_near
        hz hdelta
  · exact fun _ hz _ hdelta =>
      deBruijnNewmanPolymathBoydBoundaryNearResidual_tendsto_canonical hz hdelta
  · exact fun _ hz _ hA =>
      deBruijnNewmanPolymathBoydBoundaryTrace_tendsto_iff_tail hz hA

end

end LeanLab.Riemann
