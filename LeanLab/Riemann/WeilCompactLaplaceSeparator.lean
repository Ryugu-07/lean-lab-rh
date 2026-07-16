import LeanLab.Riemann.WeilGaussianPositivityCriterion
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

noncomputable section

open Complex Filter Function MeasureTheory Set
open scoped ContDiff Convolution Topology

namespace LeanLab.Riemann

/-- The bilateral Laplace transform on the additive logarithmic line. -/
def compactLaplaceTransform (f : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ x : ℝ, Complex.exp (s * (x : ℂ)) * f x

theorem integrable_compactLaplaceKernel {f : ℝ → ℂ}
    (hf : Continuous f) (hfsupp : HasCompactSupport f) (s : ℂ) :
    Integrable (fun x : ℝ ↦ Complex.exp (s * (x : ℂ)) * f x) := by
  apply Continuous.integrable_of_hasCompactSupport
  · fun_prop
  · exact hfsupp.mul_left

@[simp] theorem compactLaplaceTransform_zero (s : ℂ) :
    compactLaplaceTransform (fun _ : ℝ ↦ 0) s = 0 := by
  simp [compactLaplaceTransform]

theorem compactLaplaceTransform_add {f g : ℝ → ℂ} (s : ℂ)
    (hf : Integrable (fun x : ℝ ↦ Complex.exp (s * (x : ℂ)) * f x))
    (hg : Integrable (fun x : ℝ ↦ Complex.exp (s * (x : ℂ)) * g x)) :
    compactLaplaceTransform (fun x ↦ f x + g x) s =
      compactLaplaceTransform f s + compactLaplaceTransform g s := by
  simp only [compactLaplaceTransform, mul_add]
  exact integral_add hf hg

theorem compactLaplaceTransform_const_mul (c : ℂ) (f : ℝ → ℂ) (s : ℂ) :
    compactLaplaceTransform (fun x ↦ c * f x) s = c * compactLaplaceTransform f s := by
  simp only [compactLaplaceTransform]
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

theorem compactLaplaceTransform_translate (f : ℝ → ℂ) (a : ℝ) (s : ℂ) :
    compactLaplaceTransform (fun x ↦ f (x - a)) s =
      Complex.exp (s * (a : ℂ)) * compactLaplaceTransform f s := by
  simp only [compactLaplaceTransform]
  rw [← integral_add_right_eq_self
    (fun x : ℝ ↦ Complex.exp (s * (x : ℂ)) * f (x - a)) a,
    ← integral_const_mul]
  congr 1
  funext x
  simp only [ofReal_add, add_sub_cancel_right, mul_add, Complex.exp_add]
  ring

/-- Additive convolution of complex-valued functions on the logarithmic line. -/
def additiveConvolution (f g : ℝ → ℂ) : ℝ → ℂ :=
  f ⋆[ContinuousLinearMap.mul ℝ ℂ] g

theorem compactLaplaceKernel_additiveConvolution (f g : ℝ → ℂ) (s : ℂ) (x : ℝ) :
    Complex.exp (s * (x : ℂ)) * additiveConvolution f g x =
      additiveConvolution
        (fun y ↦ Complex.exp (s * (y : ℂ)) * f y)
        (fun y ↦ Complex.exp (s * (y : ℂ)) * g y) x := by
  simp only [additiveConvolution, MeasureTheory.convolution]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  change Complex.exp (s * (x : ℂ)) * (f y * g (x - y)) =
    (Complex.exp (s * (y : ℂ)) * f y) *
      (Complex.exp (s * ((x - y : ℝ) : ℂ)) * g (x - y))
  have hexp : Complex.exp (s * (x : ℂ)) =
      Complex.exp (s * (y : ℂ)) * Complex.exp (s * ((x - y : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hexp]
  ring

theorem compactLaplaceTransform_additiveConvolution {f g : ℝ → ℂ} (s : ℂ)
    (hf : Integrable (fun x : ℝ ↦ Complex.exp (s * (x : ℂ)) * f x))
    (hg : Integrable (fun x : ℝ ↦ Complex.exp (s * (x : ℂ)) * g x)) :
    compactLaplaceTransform (additiveConvolution f g) s =
      compactLaplaceTransform f s * compactLaplaceTransform g s := by
  simp only [compactLaplaceTransform]
  calc
    ∫ x : ℝ, Complex.exp (s * (x : ℂ)) * additiveConvolution f g x =
        ∫ x : ℝ, additiveConvolution
          (fun y ↦ Complex.exp (s * (y : ℂ)) * f y)
          (fun y ↦ Complex.exp (s * (y : ℂ)) * g y) x := by
      apply integral_congr_ae
      filter_upwards with x
      exact compactLaplaceKernel_additiveConvolution f g s x
    _ = (∫ x : ℝ, Complex.exp (s * (x : ℂ)) * f x) *
        ∫ x : ℝ, Complex.exp (s * (x : ℂ)) * g x := by
      exact integral_convolution (ContinuousLinearMap.mul ℝ ℂ) hf hg

theorem compactLaplaceTransform_deriv {f : ℝ → ℂ}
    (hf : ContDiff ℝ 1 f) (hfsupp : HasCompactSupport f) (s : ℂ) :
    compactLaplaceTransform (deriv f) s = -s * compactLaplaceTransform f s := by
  have hexp (x : ℝ) :
      HasDerivAt (fun y : ℝ ↦ Complex.exp (s * (y : ℂ)))
        (s * Complex.exp (s * (x : ℂ))) x := by
    simpa [mul_comm] using
      ((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul s).cexp
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  have h0 : Integrable (fun x : ℝ ↦ Complex.exp (s * (x : ℂ)) * f x) :=
    integrable_compactLaplaceKernel hf.continuous hfsupp s
  have h1 : Integrable (fun x : ℝ ↦ Complex.exp (s * (x : ℂ)) * deriv f x) :=
    integrable_compactLaplaceKernel hf.continuous_deriv_one hfsupp.deriv s
  have hs0 : Integrable
      (fun x : ℝ ↦ (s * Complex.exp (s * (x : ℂ))) * f x) := by
    have h := h0.const_mul s
    convert h using 1
    funext x
    ring
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x : ℝ ↦ Complex.exp (s * (x : ℂ)))
    (u' := fun x : ℝ ↦ s * Complex.exp (s * (x : ℂ)))
    (v := f) (v' := deriv f)
    (fun x _ ↦ hexp x) (fun x _ ↦ (hfd x).hasDerivAt) h1 hs0 h0
  calc
    compactLaplaceTransform (deriv f) s =
        ∫ x : ℝ, Complex.exp (s * (x : ℂ)) * deriv f x := rfl
    _ = -∫ x : ℝ, (s * Complex.exp (s * (x : ℂ))) * f x := by
      simpa only [Pi.mul_apply] using hibp
    _ = -s * compactLaplaceTransform f s := by
      simp only [compactLaplaceTransform]
      rw [show (∫ x : ℝ, (s * Complex.exp (s * (x : ℂ))) * f x) =
          s * ∫ x : ℝ, Complex.exp (s * (x : ℂ)) * f x by
        rw [← integral_const_mul]
        congr 1
        funext x
        ring]
      ring

theorem compactLaplaceTransform_deriv_deriv {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfsupp : HasCompactSupport f) (s : ℂ) :
    compactLaplaceTransform (deriv (deriv f)) s =
      s ^ 2 * compactLaplaceTransform f s := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hdf : ContDiff ℝ 1 (deriv f) := by
    simpa using hf.deriv'
  rw [compactLaplaceTransform_deriv hdf hfsupp.deriv s,
    compactLaplaceTransform_deriv hf1 hfsupp s]
  ring

theorem norm_compactLaplaceKernel_le_exp_abs_mul
    {f : ℝ → ℂ} {s : ℂ} (hre0 : 0 ≤ s.re) (hre1 : s.re ≤ 1) (x : ℝ) :
    ‖Complex.exp (s * (x : ℂ)) * f x‖ ≤ Real.exp |x| * ‖f x‖ := by
  rw [norm_mul, Complex.norm_exp]
  gcongr
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
    nlinarith
  · rw [abs_of_neg (lt_of_not_ge hx)]
    nlinarith

/-- A strip-uniform mass controlling a compactly supported Laplace transform. -/
def compactLaplaceSecondDerivativeMass (f : ℝ → ℂ) : ℝ :=
  ∫ x : ℝ, Real.exp |x| * ‖deriv (deriv f) x‖

theorem integrable_compactLaplaceSecondDerivativeMajorant {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfsupp : HasCompactSupport f) :
    Integrable (fun x : ℝ ↦ Real.exp |x| * ‖deriv (deriv f) x‖) := by
  have hdf : ContDiff ℝ 1 (deriv f) := by
    simpa using hf.deriv'
  apply Continuous.integrable_of_hasCompactSupport
  · exact (Real.continuous_exp.comp continuous_abs).mul hdf.continuous_deriv_one.norm
  · exact hfsupp.deriv.deriv.norm.mul_left

theorem compactLaplaceSecondDerivativeMass_nonneg (f : ℝ → ℂ) :
    0 ≤ compactLaplaceSecondDerivativeMass f := by
  apply integral_nonneg
  intro x
  positivity

theorem norm_compactLaplaceTransform_deriv_deriv_le_mass
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfsupp : HasCompactSupport f)
    {s : ℂ} (hre0 : 0 ≤ s.re) (hre1 : s.re ≤ 1) :
    ‖compactLaplaceTransform (deriv (deriv f)) s‖ ≤
      compactLaplaceSecondDerivativeMass f := by
  apply norm_integral_le_of_norm_le
    (integrable_compactLaplaceSecondDerivativeMajorant hf hfsupp)
  filter_upwards with x
  exact norm_compactLaplaceKernel_le_exp_abs_mul hre0 hre1 x

theorem norm_compactLaplaceTransform_le_mass_mul_inv_sq
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfsupp : HasCompactSupport f)
    {s : ℂ} (hs0 : s ≠ 0) (hre0 : 0 ≤ s.re) (hre1 : s.re ≤ 1) :
    ‖compactLaplaceTransform f s‖ ≤
      compactLaplaceSecondDerivativeMass f * (‖s‖⁻¹ ^ (2 : ℕ)) := by
  have hbound := norm_compactLaplaceTransform_deriv_deriv_le_mass hf hfsupp hre0 hre1
  have hnorm : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have hident := compactLaplaceTransform_deriv_deriv hf hfsupp s
  calc
    ‖compactLaplaceTransform f s‖ =
        ‖compactLaplaceTransform (deriv (deriv f)) s‖ * (‖s‖⁻¹ ^ (2 : ℕ)) := by
      rw [hident, norm_mul, norm_pow]
      field_simp [hnorm.ne']
    _ ≤ compactLaplaceSecondDerivativeMass f * (‖s‖⁻¹ ^ (2 : ℕ)) := by
      gcongr

theorem norm_compactLaplaceTransform_xiDivisorZero_le
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfsupp : HasCompactSupport f)
    (p : RiemannXiDivisorZeroIndex) :
    ‖compactLaplaceTransform f (riemannXiDivisorZeroValue p)‖ ≤
      compactLaplaceSecondDerivativeMass f *
        (‖riemannXiDivisorZeroValue p‖⁻¹ ^ (2 : ℕ)) := by
  have hpZero := riemannXiDivisorZeroIndex_val_isNontrivialZero p
  have hpReflect : IsNontrivialZero (1 - riemannXiDivisorZeroValue p) := by
    rw [isNontrivialZero_iff_riemannXi_eq_zero, riemannXi_one_sub]
    exact (isNontrivialZero_iff_riemannXi_eq_zero _).mp hpZero
  have hre0 : 0 ≤ (riemannXiDivisorZeroValue p).re := by
    have hreflectRe := nontrivial_zero_re_lt_one hpReflect
    simp only [Complex.sub_re, Complex.one_re] at hreflectRe
    linarith
  have hre1 : (riemannXiDivisorZeroValue p).re ≤ 1 :=
    (nontrivial_zero_re_lt_one hpZero).le
  exact norm_compactLaplaceTransform_le_mass_mul_inv_sq hf hfsupp
    (Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p) hre0 hre1

theorem summable_norm_compactLaplaceTransform_xiDivisorZero
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfsupp : HasCompactSupport f) :
    Summable (fun p : RiemannXiDivisorZeroIndex ↦
      ‖compactLaplaceTransform f (riemannXiDivisorZeroValue p)‖) := by
  exact (summable_riemannXiDivisorZeroIndex_norm_inv_sq.mul_left
    (compactLaplaceSecondDerivativeMass f)).of_nonneg_of_le
      (fun p ↦ norm_nonneg _) (fun p ↦
        norm_compactLaplaceTransform_xiDivisorZero_le hf hfsupp p)

/-- A fixed smooth bump with support in `[-2, 2]` and a unit inner plateau. -/
def compactLaplaceBump : ContDiffBump (0 : ℝ) :=
  ⟨1, 2, by norm_num, by norm_num⟩

/-- The fixed bump normalized to have real integral one. -/
def compactLaplaceUnitBump : ℝ → ℝ :=
  compactLaplaceBump.normed volume

theorem contDiff_compactLaplaceUnitBump : ContDiff ℝ ∞ compactLaplaceUnitBump := by
  exact compactLaplaceBump.contDiff_normed

theorem hasCompactSupport_compactLaplaceUnitBump :
    HasCompactSupport compactLaplaceUnitBump := by
  exact compactLaplaceBump.hasCompactSupport_normed

theorem integral_compactLaplaceUnitBump : ∫ x : ℝ, compactLaplaceUnitBump x = 1 := by
  exact compactLaplaceBump.integral_normed

/-- Modulating by the protected point makes its Laplace transform equal the unit bump integral. -/
def compactLaplaceModulatedBump (rho : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (-rho * (x : ℂ)) * (compactLaplaceUnitBump x : ℂ)

theorem contDiff_compactLaplaceModulatedBump (rho : ℂ) :
    ContDiff ℝ ∞ (compactLaplaceModulatedBump rho) := by
  apply ContDiff.mul
  · exact (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
  · exact Complex.ofRealCLM.contDiff.comp contDiff_compactLaplaceUnitBump

theorem hasCompactSupport_compactLaplaceModulatedBump (rho : ℂ) :
    HasCompactSupport (compactLaplaceModulatedBump rho) := by
  exact (HasCompactSupport.comp_left hasCompactSupport_compactLaplaceUnitBump
    Complex.ofReal_zero).mul_left

@[simp] theorem compactLaplaceTransform_modulatedBump_self (rho : ℂ) :
    compactLaplaceTransform (compactLaplaceModulatedBump rho) rho = 1 := by
  simp only [compactLaplaceTransform, compactLaplaceModulatedBump]
  have hpoint : (fun x : ℝ ↦
      Complex.exp (rho * (x : ℂ)) *
        (Complex.exp (-rho * (x : ℂ)) * (compactLaplaceUnitBump x : ℂ))) =
      fun x : ℝ ↦ (compactLaplaceUnitBump x : ℂ) := by
    funext x
    have hexp : Complex.exp (rho * (x : ℂ)) *
        Complex.exp (-rho * (x : ℂ)) = 1 := by
      rw [← Complex.exp_add]
      ring_nf
      simp
    rw [← mul_assoc, hexp, one_mul]
  rw [hpoint, integral_complex_ofReal, integral_compactLaplaceUnitBump]
  norm_num

theorem exists_compactLaplaceBadValueFinset
    (p0 : RiemannXiDivisorZeroIndex) {q : ℝ} (hq : 0 < q) :
    ∃ U : Finset ℂ,
      riemannXiDivisorZeroValue p0 ∉ U ∧
      ∀ p : RiemannXiDivisorZeroIndex,
        riemannXiDivisorZeroValue p ≠ riemannXiDivisorZeroValue p0 →
        q ≤ ‖compactLaplaceTransform
          (compactLaplaceModulatedBump (riemannXiDivisorZeroValue p0))
          (riemannXiDivisorZeroValue p)‖ →
        riemannXiDivisorZeroValue p ∈ U := by
  classical
  let f := compactLaplaceModulatedBump (riemannXiDivisorZeroValue p0)
  have hf : ContDiff ℝ 2 f :=
    (contDiff_compactLaplaceModulatedBump _).of_le
      (WithTop.coe_le_coe.mpr (OrderTop.le_top (2 : ℕ∞)))
  have hfsupp : HasCompactSupport f := hasCompactSupport_compactLaplaceModulatedBump _
  have hsum : Summable (fun p : RiemannXiDivisorZeroIndex ↦
      ‖compactLaplaceTransform f (riemannXiDivisorZeroValue p)‖) :=
    summable_norm_compactLaplaceTransform_xiDivisorZero hf hfsupp
  have hsuper : {p : RiemannXiDivisorZeroIndex |
      q ≤ ‖compactLaplaceTransform f (riemannXiDivisorZeroValue p)‖}.Finite := by
    simpa using hsum.tendsto_cofinite_zero.eventually_lt_const hq
  let bad : Set RiemannXiDivisorZeroIndex := {p |
    riemannXiDivisorZeroValue p ≠ riemannXiDivisorZeroValue p0 ∧
      q ≤ ‖compactLaplaceTransform f (riemannXiDivisorZeroValue p)‖}
  have hbad : bad.Finite := hsuper.subset (fun p hp ↦ hp.2)
  let U : Finset ℂ := (hbad.image riemannXiDivisorZeroValue).toFinset
  refine ⟨U, ?_, ?_⟩
  · intro hp0U
    have hp0Image : riemannXiDivisorZeroValue p0 ∈
        riemannXiDivisorZeroValue '' bad := by
      exact (hbad.image riemannXiDivisorZeroValue).mem_toFinset.mp hp0U
    obtain ⟨p, hpbad, hpval⟩ := hp0Image
    exact hpbad.1 hpval
  · intro p hpne hpq
    change riemannXiDivisorZeroValue p ∈
      (hbad.image riemannXiDivisorZeroValue).toFinset
    rw [(hbad.image riemannXiDivisorZeroValue).mem_toFinset]
    exact ⟨p, ⟨hpne, hpq⟩, rfl⟩

/-- A finite polynomial that vanishes at the exponential images of the unwanted values. -/
def compactLaplaceSeparatorPolynomial (h : ℝ) (U : Finset ℂ) : Polynomial ℂ :=
  ∏ u ∈ U, (Polynomial.X - Polynomial.C (Complex.exp ((h : ℂ) * u)))

theorem compactLaplaceSeparatorPolynomial_eval_eq_zero
    (h : ℝ) (U : Finset ℂ) {u : ℂ} (hu : u ∈ U) :
    Polynomial.eval (Complex.exp ((h : ℂ) * u))
      (compactLaplaceSeparatorPolynomial h U) = 0 := by
  classical
  simp only [compactLaplaceSeparatorPolynomial, Polynomial.eval_prod,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [Finset.prod_eq_zero_iff]
  exact ⟨u, hu, sub_self _⟩

theorem compactLaplaceSeparatorPolynomial_eval_ne_zero
    {h : ℝ} {U : Finset ℂ} {z0 : ℂ}
    (hsep : ∀ u ∈ U,
      Complex.exp ((h : ℂ) * z0) ≠ Complex.exp ((h : ℂ) * u)) :
    Polynomial.eval (Complex.exp ((h : ℂ) * z0))
      (compactLaplaceSeparatorPolynomial h U) ≠ 0 := by
  classical
  rw [compactLaplaceSeparatorPolynomial, Polynomial.eval_prod]
  rw [Finset.prod_ne_zero_iff]
  intro u hu
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  exact sub_ne_zero.mpr (hsep u hu)

/-- The polynomial coefficient packet realized by finitely many real translates. -/
def compactLaplacePolynomialPacket (P : Polynomial ℂ) (h : ℝ)
    (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑ k ∈ P.support, P.coeff k * f (x - (k : ℝ) * h)

theorem contDiff_compactLaplacePolynomialPacket
    {P : Polynomial ℂ} {h : ℝ} {f : ℝ → ℂ} {n : ℕ∞ω}
    (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (compactLaplacePolynomialPacket P h f) := by
  classical
  apply ContDiff.sum
  intro k _hk
  exact contDiff_const.mul (hf.comp (contDiff_id.sub contDiff_const))

theorem hasCompactSupport_compactLaplacePolynomialPacket
    (P : Polynomial ℂ) (h : ℝ) {f : ℝ → ℂ}
    (hfsupp : HasCompactSupport f) :
    HasCompactSupport (compactLaplacePolynomialPacket P h f) := by
  classical
  unfold compactLaplacePolynomialPacket
  induction P.support using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      change HasCompactSupport (0 : ℝ → ℂ)
      exact HasCompactSupport.zero
  | @insert k S hk ih =>
      simp only [Finset.sum_insert hk]
      apply HasCompactSupport.add
      · exact (hfsupp.comp_homeomorph
          (Homeomorph.addRight (-((k : ℝ) * h)))).mul_left
      · exact ih

theorem compactLaplaceTransform_polynomialPacket
    (P : Polynomial ℂ) (h : ℝ) {f : ℝ → ℂ}
    (hf : Continuous f) (hfsupp : HasCompactSupport f) (s : ℂ) :
    compactLaplaceTransform (compactLaplacePolynomialPacket P h f) s =
      Polynomial.eval (Complex.exp ((h : ℂ) * s)) P * compactLaplaceTransform f s := by
  classical
  have htermCont (k : ℕ) :
      Continuous (fun x : ℝ ↦ P.coeff k * f (x - (k : ℝ) * h)) := by
    fun_prop
  have htermSupp (k : ℕ) :
      HasCompactSupport (fun x : ℝ ↦ P.coeff k * f (x - (k : ℝ) * h)) := by
    exact (hfsupp.comp_homeomorph
      (Homeomorph.addRight (-((k : ℝ) * h)))).mul_left
  have htermInt (k : ℕ) : Integrable (fun x : ℝ ↦
      Complex.exp (s * (x : ℂ)) * (P.coeff k * f (x - (k : ℝ) * h))) :=
    integrable_compactLaplaceKernel (htermCont k) (htermSupp k) s
  calc
    compactLaplaceTransform (compactLaplacePolynomialPacket P h f) s =
        ∑ k ∈ P.support,
          compactLaplaceTransform
            (fun x : ℝ ↦ P.coeff k * f (x - (k : ℝ) * h)) s := by
      simp only [compactLaplaceTransform, compactLaplacePolynomialPacket, Finset.mul_sum]
      exact integral_finsetSum P.support (fun k _hk ↦ htermInt k)
    _ = ∑ k ∈ P.support,
        P.coeff k *
          (Complex.exp (s * (((k : ℝ) * h : ℝ) : ℂ)) * compactLaplaceTransform f s) := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [compactLaplaceTransform_const_mul, compactLaplaceTransform_translate]
    _ = (∑ k ∈ P.support,
        P.coeff k * Complex.exp (s * (((k : ℝ) * h : ℝ) : ℂ))) *
          compactLaplaceTransform f s := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _hk
      ring
    _ = Polynomial.eval (Complex.exp ((h : ℂ) * s)) P *
        compactLaplaceTransform f s := by
      congr 1
      rw [Polynomial.eval_eq_sum]
      apply Finset.sum_congr rfl
      intro k _hk
      congr 1
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring

/-- The `(n + 1)`-fold additive convolution power, avoiding a distributional zeroth power. -/
def compactLaplaceConvolutionIterate (f : ℝ → ℂ) : ℕ → ℝ → ℂ
  | 0 => f
  | n + 1 => additiveConvolution (compactLaplaceConvolutionIterate f n) f

theorem hasCompactSupport_compactLaplaceConvolutionIterate
    {f : ℝ → ℂ} (hfsupp : HasCompactSupport f) :
    ∀ n : ℕ, HasCompactSupport (compactLaplaceConvolutionIterate f n)
  | 0 => hfsupp
  | n + 1 =>
      (hasCompactSupport_compactLaplaceConvolutionIterate hfsupp n).convolution
        (ContinuousLinearMap.mul ℝ ℂ) hfsupp

theorem contDiff_compactLaplaceConvolutionIterate
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hfsupp : HasCompactSupport f) :
    ∀ n : ℕ, ContDiff ℝ ∞ (compactLaplaceConvolutionIterate f n)
  | 0 => hf
  | n + 1 => by
      have hprev := contDiff_compactLaplaceConvolutionIterate hf hfsupp n
      exact (hasCompactSupport_compactLaplaceConvolutionIterate hfsupp n).contDiff_convolution_left
        (ContinuousLinearMap.mul ℝ ℂ) hprev hf.continuous.locallyIntegrable

theorem compactLaplaceTransform_convolutionIterate
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hfsupp : HasCompactSupport f)
    (s : ℂ) : ∀ n : ℕ,
    compactLaplaceTransform (compactLaplaceConvolutionIterate f n) s =
      compactLaplaceTransform f s ^ (n + 1)
  | 0 => by simp [compactLaplaceConvolutionIterate]
  | n + 1 => by
      rw [compactLaplaceConvolutionIterate,
        compactLaplaceTransform_additiveConvolution s
          (integrable_compactLaplaceKernel
            (contDiff_compactLaplaceConvolutionIterate hf hfsupp n).continuous
            (hasCompactSupport_compactLaplaceConvolutionIterate hfsupp n) s)
          (integrable_compactLaplaceKernel hf.continuous hfsupp s),
        compactLaplaceTransform_convolutionIterate hf hfsupp s n]
      ring

theorem exists_compactLaplaceNormalizedSeparatorData
    (p0 : RiemannXiDivisorZeroIndex) :
    ∃ h : ℝ, ∃ P : Polynomial ℂ,
      0 < h ∧
      Polynomial.eval
        (Complex.exp ((h : ℂ) * riemannXiDivisorZeroValue p0)) P = 1 ∧
      ∀ p : RiemannXiDivisorZeroIndex,
        riemannXiDivisorZeroValue p ≠ riemannXiDivisorZeroValue p0 →
        (1 / 2 : ℝ) ≤ ‖compactLaplaceTransform
          (compactLaplaceModulatedBump (riemannXiDivisorZeroValue p0))
          (riemannXiDivisorZeroValue p)‖ →
        Polynomial.eval
          (Complex.exp ((h : ℂ) * riemannXiDivisorZeroValue p)) P = 0 := by
  classical
  obtain ⟨U, hp0U, hU⟩ := exists_compactLaplaceBadValueFinset p0 (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨h, hh, hsep⟩ := gaussianCriterion_exists_pos_exp_mul_separates_finset
    (riemannXiDivisorZeroValue p0) U hp0U
  let P0 := compactLaplaceSeparatorPolynomial h U
  let z0 := Complex.exp ((h : ℂ) * riemannXiDivisorZeroValue p0)
  have hP0 : Polynomial.eval z0 P0 ≠ 0 := by
    exact compactLaplaceSeparatorPolynomial_eval_ne_zero hsep
  let P : Polynomial ℂ := Polynomial.C ((Polynomial.eval z0 P0)⁻¹) * P0
  refine ⟨h, P, hh, ?_, ?_⟩
  · simp [P, z0, hP0]
  · intro p hpne hpLarge
    have hpU : riemannXiDivisorZeroValue p ∈ U := hU p hpne hpLarge
    have hP0zero : Polynomial.eval
        (Complex.exp ((h : ℂ) * riemannXiDivisorZeroValue p)) P0 = 0 := by
      exact compactLaplaceSeparatorPolynomial_eval_eq_zero h U hpU
    simp [P, hP0zero]

/-- A coefficient majorant for polynomial evaluation throughout the closed xi strip. -/
def compactLaplacePolynomialStripBound (h : ℝ) (P : Polynomial ℂ) : ℝ :=
  ∑ k ∈ P.support, ‖P.coeff k‖ * Real.exp h ^ k

theorem compactLaplacePolynomialStripBound_nonneg (h : ℝ) (P : Polynomial ℂ) :
    0 ≤ compactLaplacePolynomialStripBound h P := by
  apply Finset.sum_nonneg
  intro k _hk
  positivity

theorem norm_compactLaplacePolynomial_eval_le_stripBound
    {h : ℝ} (hh : 0 ≤ h) (P : Polynomial ℂ) {s : ℂ} (hre1 : s.re ≤ 1) :
    ‖Polynomial.eval (Complex.exp ((h : ℂ) * s)) P‖ ≤
      compactLaplacePolynomialStripBound h P := by
  rw [Polynomial.eval_eq_sum]
  calc
    ‖∑ k ∈ P.support, P.coeff k * Complex.exp ((h : ℂ) * s) ^ k‖ ≤
        ∑ k ∈ P.support, ‖P.coeff k * Complex.exp ((h : ℂ) * s) ^ k‖ :=
      norm_sum_le _ _
    _ = ∑ k ∈ P.support,
        ‖P.coeff k‖ * ‖Complex.exp ((h : ℂ) * s)‖ ^ k := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [norm_mul, norm_pow]
    _ ≤ compactLaplacePolynomialStripBound h P := by
      apply Finset.sum_le_sum
      intro k _hk
      gcongr
      rw [Complex.norm_exp, Real.exp_le_exp]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      nlinarith

/-- The normalized polynomial packet applied to a compact convolution power. -/
def compactLaplaceGeneratedSeparator
    (p0 : RiemannXiDivisorZeroIndex) (h : ℝ) (P : Polynomial ℂ) (m : ℕ) : ℝ → ℂ :=
  compactLaplacePolynomialPacket P h
    (compactLaplaceConvolutionIterate
      (compactLaplaceModulatedBump (riemannXiDivisorZeroValue p0)) m)

theorem contDiff_compactLaplaceGeneratedSeparator
    (p0 : RiemannXiDivisorZeroIndex) (h : ℝ) (P : Polynomial ℂ) (m : ℕ) :
    ContDiff ℝ ∞ (compactLaplaceGeneratedSeparator p0 h P m) := by
  apply contDiff_compactLaplacePolynomialPacket
  exact contDiff_compactLaplaceConvolutionIterate
    (contDiff_compactLaplaceModulatedBump _)
    (hasCompactSupport_compactLaplaceModulatedBump _) m

theorem hasCompactSupport_compactLaplaceGeneratedSeparator
    (p0 : RiemannXiDivisorZeroIndex) (h : ℝ) (P : Polynomial ℂ) (m : ℕ) :
    HasCompactSupport (compactLaplaceGeneratedSeparator p0 h P m) := by
  apply hasCompactSupport_compactLaplacePolynomialPacket
  exact hasCompactSupport_compactLaplaceConvolutionIterate
    (hasCompactSupport_compactLaplaceModulatedBump _) m

theorem compactLaplaceTransform_generatedSeparator
    (p0 : RiemannXiDivisorZeroIndex) (h : ℝ) (P : Polynomial ℂ) (m : ℕ) (s : ℂ) :
    compactLaplaceTransform (compactLaplaceGeneratedSeparator p0 h P m) s =
      Polynomial.eval (Complex.exp ((h : ℂ) * s)) P *
        compactLaplaceTransform
          (compactLaplaceModulatedBump (riemannXiDivisorZeroValue p0)) s ^ (m + 1) := by
  rw [compactLaplaceGeneratedSeparator,
    compactLaplaceTransform_polynomialPacket P h
      (contDiff_compactLaplaceConvolutionIterate
        (contDiff_compactLaplaceModulatedBump _)
        (hasCompactSupport_compactLaplaceModulatedBump _) m).continuous
      (hasCompactSupport_compactLaplaceConvolutionIterate
        (hasCompactSupport_compactLaplaceModulatedBump _) m) s,
    compactLaplaceTransform_convolutionIterate
      (contDiff_compactLaplaceModulatedBump _)
      (hasCompactSupport_compactLaplaceModulatedBump _) s m]

theorem compactLaplaceTransform_generatedSeparator_target
    (p0 : RiemannXiDivisorZeroIndex) {h : ℝ} {P : Polynomial ℂ}
    (hP : Polynomial.eval
      (Complex.exp ((h : ℂ) * riemannXiDivisorZeroValue p0)) P = 1) (m : ℕ) :
    compactLaplaceTransform (compactLaplaceGeneratedSeparator p0 h P m)
      (riemannXiDivisorZeroValue p0) = 1 := by
  rw [compactLaplaceTransform_generatedSeparator, hP,
    compactLaplaceTransform_modulatedBump_self]
  simp

theorem compactLaplaceGeneratedSeparator_tail_le
    (p0 : RiemannXiDivisorZeroIndex) {h : ℝ} (hh : 0 < h) {P : Polynomial ℂ}
    (hkill : ∀ p : RiemannXiDivisorZeroIndex,
      riemannXiDivisorZeroValue p ≠ riemannXiDivisorZeroValue p0 →
      (1 / 2 : ℝ) ≤ ‖compactLaplaceTransform
        (compactLaplaceModulatedBump (riemannXiDivisorZeroValue p0))
        (riemannXiDivisorZeroValue p)‖ →
      Polynomial.eval
        (Complex.exp ((h : ℂ) * riemannXiDivisorZeroValue p)) P = 0)
    (m : ℕ) (p : RiemannXiDivisorZeroIndex) :
    (if riemannXiDivisorZeroValue p = riemannXiDivisorZeroValue p0 then 0
      else ‖compactLaplaceTransform (compactLaplaceGeneratedSeparator p0 h P m)
        (riemannXiDivisorZeroValue p)‖) ≤
      (compactLaplacePolynomialStripBound h P * (1 / 2 : ℝ) ^ m) *
        ‖compactLaplaceTransform
          (compactLaplaceModulatedBump (riemannXiDivisorZeroValue p0))
          (riemannXiDivisorZeroValue p)‖ := by
  have hB : 0 ≤ compactLaplacePolynomialStripBound h P :=
    compactLaplacePolynomialStripBound_nonneg h P
  by_cases hp : riemannXiDivisorZeroValue p = riemannXiDivisorZeroValue p0
  · rw [if_pos hp]
    positivity
  · simp only [if_neg hp]
    let A := ‖compactLaplaceTransform
      (compactLaplaceModulatedBump (riemannXiDivisorZeroValue p0))
      (riemannXiDivisorZeroValue p)‖
    have hpZero := riemannXiDivisorZeroIndex_val_isNontrivialZero p
    have hre1 : (riemannXiDivisorZeroValue p).re ≤ 1 :=
      (nontrivial_zero_re_lt_one hpZero).le
    rw [compactLaplaceTransform_generatedSeparator, norm_mul, norm_pow]
    by_cases hlarge : (1 / 2 : ℝ) ≤ A
    · rw [hkill p hp hlarge, norm_zero, zero_mul]
      positivity
    · have hsmall : A ≤ (1 / 2 : ℝ) := le_of_not_ge hlarge
      calc
        ‖Polynomial.eval
            (Complex.exp ((h : ℂ) * riemannXiDivisorZeroValue p)) P‖ * A ^ (m + 1) ≤
            compactLaplacePolynomialStripBound h P * A ^ (m + 1) := by
          gcongr
          exact norm_compactLaplacePolynomial_eval_le_stripBound hh.le P hre1
        _ = compactLaplacePolynomialStripBound h P * (A ^ m * A) := by
          rw [pow_succ]
        _ ≤ compactLaplacePolynomialStripBound h P * ((1 / 2 : ℝ) ^ m * A) := by
          gcongr
        _ = (compactLaplacePolynomialStripBound h P * (1 / 2 : ℝ) ^ m) * A := by
          ring

theorem exists_compactSupport_xiDivisor_laplace_tsum_separator
    (p0 : RiemannXiDivisorZeroIndex) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : ℝ → ℂ,
      ContDiff ℝ ∞ f ∧
      HasCompactSupport f ∧
      compactLaplaceTransform f (riemannXiDivisorZeroValue p0) = 1 ∧
      Summable (fun p : RiemannXiDivisorZeroIndex ↦
        ‖compactLaplaceTransform f (riemannXiDivisorZeroValue p)‖) ∧
      ∑' p : RiemannXiDivisorZeroIndex,
        (if riemannXiDivisorZeroValue p = riemannXiDivisorZeroValue p0 then 0
        else ‖compactLaplaceTransform f (riemannXiDivisorZeroValue p)‖) < ε := by
  obtain ⟨h, P, hh, hPtarget, hkill⟩ := exists_compactLaplaceNormalizedSeparatorData p0
  let f0 := compactLaplaceModulatedBump (riemannXiDivisorZeroValue p0)
  let B := compactLaplacePolynomialStripBound h P
  let S := ∑' p : RiemannXiDivisorZeroIndex,
    ‖compactLaplaceTransform f0 (riemannXiDivisorZeroValue p)‖
  have hbaseSum : Summable (fun p : RiemannXiDivisorZeroIndex ↦
      ‖compactLaplaceTransform f0 (riemannXiDivisorZeroValue p)‖) := by
    apply summable_norm_compactLaplaceTransform_xiDivisorZero
    · exact (contDiff_compactLaplaceModulatedBump _).of_le
        (WithTop.coe_le_coe.mpr (OrderTop.le_top (2 : ℕ∞)))
    · exact hasCompactSupport_compactLaplaceModulatedBump _
  have hpow : Tendsto (fun m : ℕ ↦ (1 / 2 : ℝ) ^ m) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hboundTendsto : Tendsto
      (fun m : ℕ ↦ (B * (1 / 2 : ℝ) ^ m) * S) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hpow).mul tendsto_const_nhds
  obtain ⟨m, hm⟩ := (hboundTendsto.eventually_lt_const hε).exists
  let f := compactLaplaceGeneratedSeparator p0 h P m
  have hfSmooth : ContDiff ℝ ∞ f := contDiff_compactLaplaceGeneratedSeparator p0 h P m
  have hfSupp : HasCompactSupport f :=
    hasCompactSupport_compactLaplaceGeneratedSeparator p0 h P m
  have hfSum : Summable (fun p : RiemannXiDivisorZeroIndex ↦
      ‖compactLaplaceTransform f (riemannXiDivisorZeroValue p)‖) := by
    apply summable_norm_compactLaplaceTransform_xiDivisorZero
    · exact hfSmooth.of_le
        (WithTop.coe_le_coe.mpr (OrderTop.le_top (2 : ℕ∞)))
    · exact hfSupp
  let tail : RiemannXiDivisorZeroIndex → ℝ := fun p ↦
    if riemannXiDivisorZeroValue p = riemannXiDivisorZeroValue p0 then 0
    else ‖compactLaplaceTransform f (riemannXiDivisorZeroValue p)‖
  have htailSum : Summable tail := by
    apply hfSum.of_nonneg_of_le
    · intro p
      simp only [tail]
      split <;> positivity
    · intro p
      simp only [tail]
      split <;> simp
  have hmajorSum : Summable (fun p : RiemannXiDivisorZeroIndex ↦
      (B * (1 / 2 : ℝ) ^ m) *
        ‖compactLaplaceTransform f0 (riemannXiDivisorZeroValue p)‖) :=
    hbaseSum.mul_left (B * (1 / 2 : ℝ) ^ m)
  have htailPoint : ∀ p : RiemannXiDivisorZeroIndex,
      tail p ≤ (B * (1 / 2 : ℝ) ^ m) *
        ‖compactLaplaceTransform f0 (riemannXiDivisorZeroValue p)‖ := by
    intro p
    exact compactLaplaceGeneratedSeparator_tail_le p0 hh hkill m p
  refine ⟨f, hfSmooth, hfSupp,
    compactLaplaceTransform_generatedSeparator_target p0 hPtarget m, hfSum, ?_⟩
  change ∑' p : RiemannXiDivisorZeroIndex, tail p < ε
  calc
    ∑' p : RiemannXiDivisorZeroIndex, tail p ≤
        ∑' p : RiemannXiDivisorZeroIndex,
          (B * (1 / 2 : ℝ) ^ m) *
            ‖compactLaplaceTransform f0 (riemannXiDivisorZeroValue p)‖ :=
      htailSum.tsum_le_tsum htailPoint hmajorSum
    _ = (B * (1 / 2 : ℝ) ^ m) * S := by
      rw [tsum_mul_left]
    _ < ε := hm

end LeanLab.Riemann
