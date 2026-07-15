import LeanLab.Riemann.WeilGaussianPositivityCriterion
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# A fixed-width Gaussian-Weil positivity criterion for RH

This module proves that the width parameter in the finite Gaussian-Weil positivity criterion can
be fixed in advance. Finite Rademacher exponential sums approximate every increase of Gaussian
width through powers of `cosh`. The centered real parts of all xi divisor zeros lie in a fixed
strip, so the approximation is uniformly dominated by the original positive-width Gaussian
packet over the complete multiplicity-bearing divisor.

Consequently, for every `a0 > 0`, RH is equivalent to arithmetic quadratic positivity for all
finite real shift families at exactly the single width `a0`. This remains an RH-equivalent
criterion; it does not prove the fixed-width arithmetic inequalities unconditionally.
-/

open Complex Filter
open scoped BigOperators Topology

namespace LeanLab.Riemann

noncomputable section

theorem fixedWidth_norm_cosh_le_real_cosh_re (z : ℂ) :
    ‖Complex.cosh z‖ ≤ Real.cosh z.re := by
  rw [Complex.cosh, norm_div, norm_ofNat]
  calc
    ‖Complex.exp z + Complex.exp (-z)‖ / 2 ≤
        (‖Complex.exp z‖ + ‖Complex.exp (-z)‖) / 2 := by
      gcongr
      exact norm_add_le _ _
    _ = Real.cosh z.re := by
      rw [Complex.norm_exp, Complex.norm_exp, Complex.neg_re, Real.cosh_eq]

theorem fixedWidth_norm_cosh_le_exp_re_sq_half (z : ℂ) :
    ‖Complex.cosh z‖ ≤ Real.exp (z.re ^ 2 / 2) :=
  (fixedWidth_norm_cosh_le_real_cosh_re z).trans (Real.cosh_le_exp_half_sq z.re)

def fixedWidthCoshScale (c : ℝ) (n : ℕ) : ℝ := Real.sqrt (c / (n : ℝ))

theorem fixedWidth_tendsto_coshScale_zero {c : ℝ} :
    Tendsto (fixedWidthCoshScale c) atTop (𝓝 0) := by
  have hdiv : Tendsto (fun n : ℕ => c / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  change Tendsto ((fun x : ℝ => Real.sqrt x) ∘ fun n : ℕ => c / (n : ℝ))
    atTop (𝓝 0)
  simpa only [Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hdiv

theorem fixedWidth_tendsto_coshScale_mul (c : ℝ) (z : ℂ) :
    Tendsto (fun n : ℕ => (fixedWidthCoshScale c n : ℂ) * z) atTop (𝓝 0) := by
  simpa using (Complex.continuous_ofReal.tendsto 0).comp
    fixedWidth_tendsto_coshScale_zero |>.mul_const z

theorem fixedWidth_tendsto_sinh_div_coshScale_mul_one
    {c : ℝ} (hc : 0 < c) {z : ℂ} (hz : z ≠ 0) :
    Tendsto (fun n : ℕ =>
      Complex.sinh ((fixedWidthCoshScale c n : ℂ) * z) /
        ((fixedWidthCoshScale c n : ℂ) * z)) atTop (𝓝 1) := by
  have hequiv := Complex.isEquivalent_sinh.comp_tendsto
    (fixedWidth_tendsto_coshScale_mul c z)
  have hne : ∀ᶠ n : ℕ in atTop, (fixedWidthCoshScale c n : ℂ) * z ≠ 0 := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hdiv : 0 < c / (n : ℝ) := div_pos hc (by exact_mod_cast hn)
    exact mul_ne_zero (ofReal_ne_zero.mpr (Real.sqrt_pos.2 hdiv).ne') hz
  exact (Asymptotics.isEquivalent_iff_tendsto_one hne).mp hequiv

theorem fixedWidth_tendsto_nat_mul_cosh_sq_sub_one
    {c : ℝ} (hc : 0 < c) (z : ℂ) :
    Tendsto (fun n : ℕ =>
      (n : ℂ) *
        (Complex.cosh ((fixedWidthCoshScale c n : ℂ) * z) ^ 2 - 1))
      atTop (𝓝 ((c : ℂ) * z ^ 2)) := by
  by_cases hz : z = 0
  · subst z
    simp
  have hratio := fixedWidth_tendsto_sinh_div_coshScale_mul_one hc hz
  have hlim : Tendsto (fun n : ℕ =>
      ((c : ℂ) * z ^ 2) *
        (Complex.sinh ((fixedWidthCoshScale c n : ℂ) * z) /
          ((fixedWidthCoshScale c n : ℂ) * z)) ^ 2)
      atTop (𝓝 ((c : ℂ) * z ^ 2)) := by
    simpa using (tendsto_const_nhds.mul (hratio.pow 2))
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hdiv_pos : 0 < c / (n : ℝ) := div_pos hc (by exact_mod_cast hn)
  have hdiv_nonneg : 0 ≤ c / (n : ℝ) := hdiv_pos.le
  have hsqrt : fixedWidthCoshScale c n ^ 2 = c / (n : ℝ) := by
    exact Real.sq_sqrt hdiv_nonneg
  have hsqrtC : (fixedWidthCoshScale c n : ℂ) ^ 2 = (c : ℂ) / (n : ℂ) := by
    exact_mod_cast hsqrt
  have hcC : (c : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc.ne'
  rw [Complex.cosh_sq]
  field_simp [fixedWidthCoshScale, hnreal, hz, Real.sqrt_ne_zero'.mpr hdiv_pos]
  rw [hsqrtC]
  field_simp [hcC, hnreal]
  ring_nf

theorem fixedWidth_tendsto_cosh_pow_exp
    {c : ℝ} (hc : 0 < c) (z : ℂ) :
    Tendsto (fun n : ℕ =>
      Complex.cosh ((fixedWidthCoshScale c n : ℂ) * z) ^ (2 * n))
      atTop (𝓝 (Complex.exp ((c : ℂ) * z ^ 2))) := by
  have h := Complex.tendsto_one_add_pow_exp_of_tendsto
    (fixedWidth_tendsto_nat_mul_cosh_sq_sub_one hc z)
  convert h using 1
  ext n
  ring_nf

def fixedWidthRademacherShift (n : ℕ) (h : ℝ) (sigma : Fin n → Bool) : ℝ :=
  ∑ k, if sigma k then h else -h

def fixedWidthRademacherCoeff (n : ℕ) (_sigma : Fin n → Bool) : ℝ :=
  (1 / 2 : ℝ) ^ n

theorem fixedWidth_gaussianWeilExponentialSum_rademacher
    (n : ℕ) (h : ℝ) (z : ℂ) :
    gaussianCriterion_gaussianWeilExponentialSum
        (fixedWidthRademacherShift n h) (fixedWidthRademacherCoeff n) z =
      Complex.cosh ((h : ℂ) * z) ^ n := by
  classical
  rw [gaussianCriterion_gaussianWeilExponentialSum]
  calc
    (∑ sigma : Fin n → Bool,
        (fixedWidthRademacherCoeff n sigma : ℂ) *
          Complex.exp ((fixedWidthRademacherShift n h sigma : ℂ) * z)) =
        ∑ sigma : Fin n → Bool,
          ∏ k : Fin n,
            ((1 / 2 : ℂ) *
              Complex.exp (((if sigma k then h else -h : ℝ) : ℂ) * z)) := by
      apply Finset.sum_congr rfl
      intro sigma _hsigma
      rw [fixedWidthRademacherCoeff, fixedWidthRademacherShift]
      push_cast
      rw [Finset.sum_mul, Complex.exp_sum, Finset.prod_mul_distrib]
      simp
    _ = (∑ s : Bool,
          (1 / 2 : ℂ) *
            Complex.exp (((if s then h else -h : ℝ) : ℂ) * z)) ^ n := by
      rw [Fintype.sum_pow]
    _ = Complex.cosh ((h : ℂ) * z) ^ n := by
      congr 1
      rw [Fintype.sum_bool]
      rw [if_pos rfl, if_neg (by decide : false ≠ true)]
      change (1 / 2 : ℂ) * Complex.exp ((h : ℂ) * z) +
          (1 / 2 : ℂ) * Complex.exp (((-h : ℝ) : ℂ) * z) =
        Complex.cosh ((h : ℂ) * z)
      rw [show (((-h : ℝ) : ℂ) * z) = -((h : ℂ) * z) by push_cast; ring_nf]
      calc
        (1 / 2 : ℂ) * Complex.exp ((h : ℂ) * z) +
            (1 / 2 : ℂ) * Complex.exp (-((h : ℂ) * z)) =
            (Complex.exp ((h : ℂ) * z) + Complex.exp (-((h : ℂ) * z))) / 2 := by ring_nf
        _ = Complex.cosh ((h : ℂ) * z) := by
          rw [← Complex.two_cosh]
          ring_nf

def fixedWidthTensorShift {ι : Type*}
    (b : ι → ℝ) (n : ℕ) (h : ℝ) (q : ι × (Fin n → Bool)) : ℝ :=
  b q.1 + fixedWidthRademacherShift n h q.2

def fixedWidthTensorCoeff {ι : Type*}
    (w : ι → ℝ) (n : ℕ) (q : ι × (Fin n → Bool)) : ℝ :=
  w q.1 * fixedWidthRademacherCoeff n q.2

theorem fixedWidth_gaussianWeilExponentialSum_tensor
    {ι : Type*} [Fintype ι] (b w : ι → ℝ) (n : ℕ) (h : ℝ) (z : ℂ) :
    gaussianCriterion_gaussianWeilExponentialSum
        (fixedWidthTensorShift b n h) (fixedWidthTensorCoeff w n) z =
      gaussianCriterion_gaussianWeilExponentialSum b w z *
        Complex.cosh ((h : ℂ) * z) ^ n := by
  classical
  rw [gaussianCriterion_gaussianWeilExponentialSum,
    gaussianCriterion_gaussianWeilExponentialSum, Fintype.sum_prod_type]
  calc
    (∑ i, ∑ sigma,
        (fixedWidthTensorCoeff w n (i, sigma) : ℂ) *
          Complex.exp ((fixedWidthTensorShift b n h (i, sigma) : ℂ) * z)) =
        ∑ i, ((w i : ℂ) * Complex.exp ((b i : ℂ) * z)) *
          gaussianCriterion_gaussianWeilExponentialSum
            (fixedWidthRademacherShift n h) (fixedWidthRademacherCoeff n) z := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [gaussianCriterion_gaussianWeilExponentialSum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro sigma _hsigma
      rw [fixedWidthTensorCoeff, fixedWidthTensorShift]
      push_cast
      rw [add_mul, Complex.exp_add]
      ring_nf
    _ = (∑ i, (w i : ℂ) * Complex.exp ((b i : ℂ) * z)) *
        gaussianCriterion_gaussianWeilExponentialSum
          (fixedWidthRademacherShift n h) (fixedWidthRademacherCoeff n) z := by
      rw [Finset.sum_mul]
    _ = _ := by
      rw [fixedWidth_gaussianWeilExponentialSum_rademacher]

theorem fixedWidth_gaussianPacket_tensor_eq_cosh_mul
    {ι : Type*} [Fintype ι] (a0 : ℝ) (b w : ι → ℝ)
    (n : ℕ) (h : ℝ) (rho : ℂ) :
    riemannXiSymmetricGaussianPacketWeight
        (gaussianWeilPairWidth a0)
        (gaussianWeilPairShift (fixedWidthTensorShift b n h))
        (gaussianWeilPairCoeff (fixedWidthTensorCoeff w n)) rho =
      riemannXiSymmetricGaussianPacketWeight
          (gaussianWeilPairWidth a0) (gaussianWeilPairShift b)
          (gaussianWeilPairCoeff w) rho *
        Complex.cosh ((h : ℂ) * (rho - 1 / 2)) ^ (2 * n) := by
  rw [gaussianCriterion_gaussianWeilPacket_eq_exp_mul_exponentialSum,
    gaussianCriterion_gaussianWeilPacket_eq_exp_mul_exponentialSum,
    fixedWidth_gaussianWeilExponentialSum_tensor,
    fixedWidth_gaussianWeilExponentialSum_tensor]
  rw [show (h : ℂ) * (-(rho - 1 / 2)) = -((h : ℂ) * (rho - 1 / 2)) by ring_nf,
    Complex.cosh_neg]
  ring_nf

theorem fixedWidth_tendsto_gaussianPacket_tensor_width
    {ι : Type*} [Fintype ι] {a0 c : ℝ} (hc : 0 < c)
    (b w : ι → ℝ) (rho : ℂ) :
    Tendsto (fun n : ℕ =>
      riemannXiSymmetricGaussianPacketWeight
        (gaussianWeilPairWidth a0)
        (gaussianWeilPairShift (fixedWidthTensorShift b n (fixedWidthCoshScale c n)))
        (gaussianWeilPairCoeff (fixedWidthTensorCoeff w n)) rho)
      atTop
      (𝓝 (riemannXiSymmetricGaussianPacketWeight
        (gaussianWeilPairWidth (a0 + c)) (gaussianWeilPairShift b)
        (gaussianWeilPairCoeff w) rho)) := by
  rw [show (fun n : ℕ =>
      riemannXiSymmetricGaussianPacketWeight
        (gaussianWeilPairWidth a0)
        (gaussianWeilPairShift (fixedWidthTensorShift b n (fixedWidthCoshScale c n)))
        (gaussianWeilPairCoeff (fixedWidthTensorCoeff w n)) rho) =
      fun n : ℕ =>
        riemannXiSymmetricGaussianPacketWeight
          (gaussianWeilPairWidth a0) (gaussianWeilPairShift b)
          (gaussianWeilPairCoeff w) rho *
        Complex.cosh (((fixedWidthCoshScale c n : ℝ) : ℂ) * (rho - 1 / 2)) ^
          (2 * n) by
    funext n
    exact fixedWidth_gaussianPacket_tensor_eq_cosh_mul a0 b w n (fixedWidthCoshScale c n) rho]
  have hlim : Tendsto (fun n : ℕ =>
      riemannXiSymmetricGaussianPacketWeight
          (gaussianWeilPairWidth a0) (gaussianWeilPairShift b)
          (gaussianWeilPairCoeff w) rho *
        Complex.cosh ((fixedWidthCoshScale c n : ℂ) * (rho - 1 / 2)) ^ (2 * n))
      atTop
      (𝓝 (riemannXiSymmetricGaussianPacketWeight
          (gaussianWeilPairWidth a0) (gaussianWeilPairShift b)
          (gaussianWeilPairCoeff w) rho *
        Complex.exp ((c : ℂ) * (rho - 1 / 2) ^ 2))) := by
    exact tendsto_const_nhds.mul
      (fixedWidth_tendsto_cosh_pow_exp hc (rho - 1 / 2))
  convert hlim using 1
  rw [gaussianCriterion_gaussianWeilPacket_eq_exp_mul_exponentialSum,
    gaussianCriterion_gaussianWeilPacket_eq_exp_mul_exponentialSum]
  rw [show ((a0 + c : ℝ) : ℂ) * (rho - 1 / 2) ^ 2 =
      (a0 : ℂ) * (rho - 1 / 2) ^ 2 + (c : ℂ) * (rho - 1 / 2) ^ 2 by
    push_cast
    ring_nf, Complex.exp_add]
  ring_nf

theorem fixedWidth_norm_coshScale_pow_le_exp
    {c : ℝ} (hc : 0 < c) {n : ℕ} (hn : 0 < n) {z : ℂ}
    (hz : z.re ^ 2 ≤ 1) :
    ‖Complex.cosh ((fixedWidthCoshScale c n : ℂ) * z) ^ (2 * n)‖ ≤
      Real.exp c := by
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hdiv_nonneg : 0 ≤ c / (n : ℝ) := (div_pos hc (by exact_mod_cast hn)).le
  have hsqrt : fixedWidthCoshScale c n ^ 2 = c / (n : ℝ) :=
    Real.sq_sqrt hdiv_nonneg
  rw [norm_pow]
  calc
    ‖Complex.cosh ((fixedWidthCoshScale c n : ℂ) * z)‖ ^ (2 * n) ≤
        Real.exp ((((fixedWidthCoshScale c n : ℂ) * z).re ^ 2) / 2) ^ (2 * n) :=
      pow_le_pow_left₀ (norm_nonneg _)
        (fixedWidth_norm_cosh_le_exp_re_sq_half ((fixedWidthCoshScale c n : ℂ) * z)) _
    _ = Real.exp (c * z.re ^ 2) := by
      rw [← Real.exp_nat_mul]
      congr 1
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      rw [mul_pow, hsqrt]
      field_simp [hnreal]
      push_cast
      ring_nf
    _ ≤ Real.exp c := by
      rw [Real.exp_le_exp]
      nlinarith

theorem fixedWidth_centeredXiDivisorZero_re_sq_le_one
    (p : RiemannXiDivisorZeroIndex) :
    (gaussianCriterion_centeredXiDivisorZero p).re ^ 2 ≤ 1 := by
  have hpZero := riemannXiDivisorZeroIndex_val_isNontrivialZero p
  have hpReflect : IsNontrivialZero (1 - riemannXiDivisorZeroValue p) := by
    rw [isNontrivialZero_iff_riemannXi_eq_zero, riemannXi_one_sub]
    exact (isNontrivialZero_iff_riemannXi_eq_zero _).mp hpZero
  have hrePos : 0 < (riemannXiDivisorZeroValue p).re := by
    have hreflectRe := nontrivial_zero_re_lt_one hpReflect
    simp only [Complex.sub_re, Complex.one_re] at hreflectRe
    linarith
  have hreLt : (riemannXiDivisorZeroValue p).re < 1 :=
    nontrivial_zero_re_lt_one hpZero
  have hcenterRe : (gaussianCriterion_centeredXiDivisorZero p).re =
      (riemannXiDivisorZeroValue p).re - 1 / 2 := by
    simp [gaussianCriterion_centeredXiDivisorZero]
  rw [hcenterRe]
  nlinarith [sq_nonneg ((riemannXiDivisorZeroValue p).re - 1 / 2)]

theorem fixedWidth_tendsto_gaussianXiZeroQuadratic_tensor_width
    {ι : Type*} [Fintype ι] {a0 c : ℝ} (ha0 : 0 < a0) (hc : 0 < c)
    (b w : ι → ℝ) :
    Tendsto (fun n : ℕ =>
      gaussianXiZeroQuadratic a0
        (fixedWidthTensorShift b n (fixedWidthCoshScale c n)) (fixedWidthTensorCoeff w n))
      atTop (𝓝 (gaussianXiZeroQuadratic (a0 + c) b w)) := by
  let base : RiemannXiDivisorZeroIndex → ℂ := fun p =>
    riemannXiSymmetricGaussianPacketWeight
      (gaussianWeilPairWidth a0) (gaussianWeilPairShift b)
      (gaussianWeilPairCoeff w) (riemannXiDivisorZeroValue p)
  let bound : RiemannXiDivisorZeroIndex → ℝ := fun p =>
    Real.exp c * ‖base p‖
  have hbase : Summable base := by
    exact summable_riemannXiSymmetricGaussianPacketWeight
      (gaussianWeilPairWidth a0) (gaussianWeilPairShift b)
      (gaussianWeilPairCoeff w) (fun _ => ha0)
  have hbound : Summable bound := by
    exact hbase.norm.mul_left (Real.exp c)
  have hpoint (p : RiemannXiDivisorZeroIndex) : Tendsto (fun n : ℕ =>
      riemannXiSymmetricGaussianPacketWeight
        (gaussianWeilPairWidth a0)
        (gaussianWeilPairShift (fixedWidthTensorShift b n (fixedWidthCoshScale c n)))
        (gaussianWeilPairCoeff (fixedWidthTensorCoeff w n))
        (riemannXiDivisorZeroValue p)) atTop
      (𝓝 (riemannXiSymmetricGaussianPacketWeight
        (gaussianWeilPairWidth (a0 + c)) (gaussianWeilPairShift b)
        (gaussianWeilPairCoeff w) (riemannXiDivisorZeroValue p))) :=
    fixedWidth_tendsto_gaussianPacket_tensor_width hc b w (riemannXiDivisorZeroValue p)
  have heventual : ∀ᶠ n : ℕ in atTop, ∀ p : RiemannXiDivisorZeroIndex,
      ‖riemannXiSymmetricGaussianPacketWeight
        (gaussianWeilPairWidth a0)
        (gaussianWeilPairShift (fixedWidthTensorShift b n (fixedWidthCoshScale c n)))
        (gaussianWeilPairCoeff (fixedWidthTensorCoeff w n))
        (riemannXiDivisorZeroValue p)‖ ≤ bound p := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    intro p
    rw [fixedWidth_gaussianPacket_tensor_eq_cosh_mul, norm_mul]
    dsimp only [bound, base]
    calc
      ‖riemannXiSymmetricGaussianPacketWeight
          (gaussianWeilPairWidth a0) (gaussianWeilPairShift b)
          (gaussianWeilPairCoeff w) (riemannXiDivisorZeroValue p)‖ *
          ‖Complex.cosh ((fixedWidthCoshScale c n : ℂ) *
            (riemannXiDivisorZeroValue p - 1 / 2)) ^ (2 * n)‖ ≤
        ‖riemannXiSymmetricGaussianPacketWeight
          (gaussianWeilPairWidth a0) (gaussianWeilPairShift b)
          (gaussianWeilPairCoeff w) (riemannXiDivisorZeroValue p)‖ * Real.exp c := by
        gcongr
        exact fixedWidth_norm_coshScale_pow_le_exp hc hn
          (fixedWidth_centeredXiDivisorZero_re_sq_le_one p)
      _ = Real.exp c *
          ‖riemannXiSymmetricGaussianPacketWeight
            (gaussianWeilPairWidth a0) (gaussianWeilPairShift b)
            (gaussianWeilPairCoeff w) (riemannXiDivisorZeroValue p)‖ := by ring_nf
  simpa only [gaussianXiZeroQuadratic] using
    tendsto_tsum_of_dominated_convergence hbound hpoint heventual

theorem fixedWidth_exists_arithmetic_neg_of_largerWidth_neg
    {ι : Type*} [Fintype ι] {a0 c : ℝ} (ha0 : 0 < a0) (hc : 0 < c)
    (b w : ι → ℝ)
    (hneg : (gaussianXiArithmeticQuadratic (a0 + c) b w 2).re < 0) :
    ∃ n : ℕ,
      (gaussianXiArithmeticQuadratic a0
        (fixedWidthTensorShift b n (fixedWidthCoshScale c n))
        (fixedWidthTensorCoeff w n) 2).re < 0 := by
  have htargetFormula := gaussianXiZeroQuadratic_arithmetic_formula
    (c := 2) (add_pos ha0 hc) (by norm_num) b w
  have hzeroNeg : (gaussianXiZeroQuadratic (a0 + c) b w).re < 0 := by
    rw [← htargetFormula] at hneg
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] at hneg
    rcases mul_neg_iff.mp hneg with h | h
    · exact h.2
    · exact (not_lt_of_ge Real.pi_pos.le h.1).elim
  have hzeroTendsto := fixedWidth_tendsto_gaussianXiZeroQuadratic_tensor_width ha0 hc b w
  have hrealTendsto : Tendsto (fun n : ℕ =>
      (gaussianXiZeroQuadratic a0
        (fixedWidthTensorShift b n (fixedWidthCoshScale c n))
        (fixedWidthTensorCoeff w n)).re)
      atTop (𝓝 (gaussianXiZeroQuadratic (a0 + c) b w).re) :=
    (Complex.continuous_re.tendsto _).comp hzeroTendsto
  have hevent : ∀ᶠ n : ℕ in atTop,
      (gaussianXiZeroQuadratic a0
        (fixedWidthTensorShift b n (fixedWidthCoshScale c n))
        (fixedWidthTensorCoeff w n)).re < 0 :=
    hrealTendsto.eventually (Iio_mem_nhds hzeroNeg)
  obtain ⟨n, hn⟩ := hevent.exists
  refine ⟨n, ?_⟩
  have hbaseFormula := gaussianXiZeroQuadratic_arithmetic_formula
    (c := 2) ha0 (by norm_num)
      (fixedWidthTensorShift b n (fixedWidthCoshScale c n)) (fixedWidthTensorCoeff w n)
  rw [← hbaseFormula]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  exact mul_neg_of_pos_of_neg Real.pi_pos hn

theorem fixedWidth_exists_gt_tsum_gaussianGeneratedPacket_re_neg_of_phase_locked
    (aMin : ℝ) (p0 : RiemannXiDivisorZeroIndex) (P : Polynomial ℝ) (h : ℝ)
    (hkill : ∀ (a : ℝ) (p : RiemannXiDivisorZeroIndex),
      gaussianCriterion_gaussianDecayRate p ≤ gaussianCriterion_gaussianDecayRate p0 →
      ¬gaussianCriterion_isGaussianTargetSquare
          (gaussianCriterion_centeredXiDivisorZero p0) (gaussianCriterion_centeredXiDivisorZero p) →
        gaussianCriterion_gaussianGeneratedPacket P h a p = 0)
    {k : ℝ} (hk : k < 0) {A : ℕ → ℝ} (hA : Tendsto A atTop atTop)
    (hphase : ∀ n : ℕ,
      (Complex.exp
          (((A n * (gaussianCriterion_centeredXiDivisorZero p0 ^ 2).im : ℝ) : ℂ) * I) *
        gaussianCriterion_gaussianPolynomialProduct P h
          (gaussianCriterion_centeredXiDivisorZero p0)).re = k) :
    ∃ a : ℝ, 0 < a ∧ aMin < a ∧
      (∑' p : RiemannXiDivisorZeroIndex,
        gaussianCriterion_gaussianGeneratedPacket P h a p).re < 0 := by
  have htail := gaussianCriterion_tendsto_tsum_gaussianScaledHigherTerm_zero
    (gaussianCriterion_gaussianDecayRate p0) P h
  have htailA := htail.comp hA
  have htailRe : Tendsto
      (fun n : ℕ =>
        (∑' p : RiemannXiDivisorZeroIndex,
          gaussianCriterion_gaussianScaledHigherTerm
            (gaussianCriterion_gaussianDecayRate p0) P h (A n) p).re)
      atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (Complex.continuous_re.tendsto 0).comp htailA
  have htailSmall : ∀ᶠ n : ℕ in atTop,
      (∑' p : RiemannXiDivisorZeroIndex,
        gaussianCriterion_gaussianScaledHigherTerm
          (gaussianCriterion_gaussianDecayRate p0) P h (A n) p).re < -k / 2 :=
    htailRe.eventually (gt_mem_nhds (by linarith))
  have hApos : ∀ᶠ n : ℕ in atTop, 0 < A n :=
    hA.eventually (eventually_gt_atTop 0)
  have hAmin : ∀ᶠ n : ℕ in atTop, aMin < A n :=
    hA.eventually (eventually_gt_atTop aMin)
  have hevent : ∀ᶠ n : ℕ in atTop,
      0 < A n ∧ aMin < A n ∧
        (∑' p : RiemannXiDivisorZeroIndex,
          gaussianCriterion_gaussianGeneratedPacket P h (A n) p).re < 0 := by
    filter_upwards [hApos, hAmin, htailSmall] with n hnpos hnmin hntail
    refine ⟨hnpos, hnmin, ?_⟩
    have hlow :
        (gaussianCriterion_gaussianScaledLowSum p0 P h (A n)).re ≤ k :=
      gaussianCriterion_gaussianScaledLowSum_re_le_phase p0 P h (A n) k
        (hkill (A n)) (hphase n) hk.le
    have hsplit := gaussianCriterion_gaussianScaledLow_add_higher_eq_tsum
      p0 P h (A n) hnpos
    have hscaledNeg :
        (∑' p : RiemannXiDivisorZeroIndex,
          (Real.exp (A n * gaussianCriterion_gaussianDecayRate p0) : ℂ) *
            gaussianCriterion_gaussianGeneratedPacket P h (A n) p).re < 0 := by
      rw [← hsplit]
      simp only [Complex.add_re]
      linarith
    have hpacket : Summable (gaussianCriterion_gaussianGeneratedPacket P h (A n)) := by
      exact summable_riemannXiSymmetricGaussianPacketWeight
        (gaussianWeilPairWidth (A n))
        (gaussianWeilPairShift (gaussianCriterion_polynomialShift P h))
        (gaussianWeilPairCoeff (gaussianCriterion_polynomialCoeff P))
        (fun _ => by simpa only [gaussianWeilPairWidth] using hnpos)
    rw [hpacket.tsum_mul_left
      (Real.exp (A n * gaussianCriterion_gaussianDecayRate p0) : ℂ)] at hscaledNeg
    have hprod :
        Real.exp (A n * gaussianCriterion_gaussianDecayRate p0) *
          (∑' p : RiemannXiDivisorZeroIndex,
            gaussianCriterion_gaussianGeneratedPacket P h (A n) p).re < 0 := by
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero] using hscaledNeg
    rcases mul_neg_iff.mp hprod with hneg | hneg
    · exact hneg.2
    · exact (not_lt_of_ge (Real.exp_pos _).le hneg.1).elim
  obtain ⟨n, hn⟩ := hevent.exists
  exact ⟨A n, hn.1, hn.2.1, hn.2.2⟩

theorem fixedWidth_exists_gt_tsum_gaussianGeneratedPacket_re_neg_of_offLine
    (aMin : ℝ) (p0 : RiemannXiDivisorZeroIndex)
    (hp0 : (riemannXiDivisorZeroValue p0).re ≠ 1 / 2) :
    ∃ (h a : ℝ), 0 < h ∧ 0 < a ∧ aMin < a ∧
      (∑' p : RiemannXiDivisorZeroIndex,
        gaussianCriterion_gaussianGeneratedPacket
          (gaussianCriterion_gaussianProtectedSeparatorPolynomial h
            (gaussianCriterion_gaussianUnwantedLowCenterFinset p0)) h a p).re < 0 := by
  obtain ⟨h, hh, hsepForward, hsepBackward⟩ :=
    gaussianCriterion_exists_gaussianUnwantedLowSeparator p0
  let U := gaussianCriterion_gaussianUnwantedLowCenterFinset p0
  let P := gaussianCriterion_gaussianProtectedSeparatorPolynomial h U
  let z0 := gaussianCriterion_centeredXiDivisorZero p0
  let C := gaussianCriterion_gaussianPolynomialProduct P h z0
  have hCne : C ≠ 0 :=
    gaussianCriterion_gaussianSelectedPolynomialProduct_ne_zero p0 hp0 hh
      hsepForward hsepBackward
  have hkill : ∀ (a : ℝ) (p : RiemannXiDivisorZeroIndex),
      gaussianCriterion_gaussianDecayRate p ≤ gaussianCriterion_gaussianDecayRate p0 →
      ¬gaussianCriterion_isGaussianTargetSquare
          (gaussianCriterion_centeredXiDivisorZero p0) (gaussianCriterion_centeredXiDivisorZero p) →
        gaussianCriterion_gaussianGeneratedPacket P h a p = 0 := by
    intro a p hrate htarget
    exact gaussianCriterion_gaussianGeneratedPacket_eq_zero_of_unwanted_low
      p0 p h a hrate htarget
  by_cases htheta : (z0 ^ 2).im = 0
  · have hCneg : C.re < 0 :=
      gaussianCriterion_gaussianSelectedPolynomialProduct_re_neg_of_sq_im_zero
        p0 hp0 hh hsepForward hsepBackward htheta
    let A : ℕ → ℝ := fun n => n
    have hA : Tendsto A atTop atTop := by
      simpa only [A] using (tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
    have hphase (n : ℕ) :
        (Complex.exp (((A n * (z0 ^ 2).im : ℝ) : ℂ) * I) * C).re = C.re := by
      rw [htheta]
      simp
    obtain ⟨a, ha, hamin, hneg⟩ :=
      fixedWidth_exists_gt_tsum_gaussianGeneratedPacket_re_neg_of_phase_locked
        aMin p0 P h hkill hCneg hA hphase
    exact ⟨h, a, hh, ha, hamin, hneg⟩
  · obtain ⟨A, hA, hphase⟩ :=
      gaussianCriterion_exists_phase_locked_widths htheta C
    have hk : -‖C‖ < 0 := neg_lt_zero.mpr (norm_pos_iff.mpr hCne)
    obtain ⟨a, ha, hamin, hneg⟩ :=
      fixedWidth_exists_gt_tsum_gaussianGeneratedPacket_re_neg_of_phase_locked
        aMin p0 P h hkill hk hA hphase
    exact ⟨h, a, hh, ha, hamin, hneg⟩

theorem fixedWidth_exists_gt_gaussianXiArithmeticQuadratic_re_neg_of_offLine
    (aMin : ℝ) (p0 : RiemannXiDivisorZeroIndex)
    (hp0 : (riemannXiDivisorZeroValue p0).re ≠ 1 / 2) :
    ∃ (h a : ℝ), 0 < h ∧ 0 < a ∧ aMin < a ∧
      (gaussianXiArithmeticQuadratic a
        (gaussianCriterion_polynomialShift
          (gaussianCriterion_gaussianProtectedSeparatorPolynomial h
            (gaussianCriterion_gaussianUnwantedLowCenterFinset p0)) h)
        (gaussianCriterion_polynomialCoeff
          (gaussianCriterion_gaussianProtectedSeparatorPolynomial h
            (gaussianCriterion_gaussianUnwantedLowCenterFinset p0))) 2).re < 0 := by
  obtain ⟨h, a, hh, ha, hamin, hzeroNeg⟩ :=
    fixedWidth_exists_gt_tsum_gaussianGeneratedPacket_re_neg_of_offLine aMin p0 hp0
  let P := gaussianCriterion_gaussianProtectedSeparatorPolynomial h
    (gaussianCriterion_gaussianUnwantedLowCenterFinset p0)
  let b := gaussianCriterion_polynomialShift P h
  let w := gaussianCriterion_polynomialCoeff P
  have hzero : (gaussianXiZeroQuadratic a b w).re < 0 := by
    rw [gaussianCriterion_gaussianXiZeroQuadratic_eq_tsum_generatedPacket]
    exact hzeroNeg
  have hformula := gaussianXiZeroQuadratic_arithmetic_formula
    (c := 2) ha (by norm_num) b w
  refine ⟨h, a, hh, ha, hamin, ?_⟩
  change (gaussianXiArithmeticQuadratic a b w 2).re < 0
  rw [← hformula]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  exact mul_neg_of_pos_of_neg Real.pi_pos hzero

/-- Positivity of every finite real Gaussian-Weil quadratic at one fixed positive width excludes
every off-critical-line xi divisor zero. -/
theorem riemannHypothesis_of_fixedWidth_gaussianXiArithmeticQuadratic_re_nonneg
    {a0 : ℝ} (ha0 : 0 < a0)
    (hpos : ∀ (ι : Type) [Fintype ι], ∀ b w : ι → ℝ,
      0 ≤ (gaussianXiArithmeticQuadratic a0 b w 2).re) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_nontrivial_zeros_on_line]
  intro rho hrho
  rw [OnCriticalLine]
  obtain ⟨p, hp⟩ := exists_riemannXiDivisorZeroIndex_of_isNontrivialZero hrho
  by_contra hline
  have hpOff : (riemannXiDivisorZeroValue p).re ≠ 1 / 2 := by
    simpa only [hp] using hline
  obtain ⟨h, a, _hh, _ha, ha0a, hneg⟩ :=
    fixedWidth_exists_gt_gaussianXiArithmeticQuadratic_re_neg_of_offLine a0 p hpOff
  let P := gaussianCriterion_gaussianProtectedSeparatorPolynomial h
    (gaussianCriterion_gaussianUnwantedLowCenterFinset p)
  let b := gaussianCriterion_polynomialShift P h
  let w := gaussianCriterion_polynomialCoeff P
  let c := a - a0
  have hc : 0 < c := sub_pos.mpr ha0a
  have hnegBW : (gaussianXiArithmeticQuadratic a b w 2).re < 0 := by
    simpa only [P, b, w] using hneg
  have hneg' : (gaussianXiArithmeticQuadratic (a0 + c) b w 2).re < 0 := by
    convert hnegBW using 1
    dsimp only [c]
    ring_nf
  obtain ⟨n, hn⟩ :=
    fixedWidth_exists_arithmetic_neg_of_largerWidth_neg ha0 hc b w hneg'
  exact (not_lt_of_ge
    (hpos (↥(Finset.range (P.natDegree + 1)) × (Fin n → Bool))
      (fixedWidthTensorShift b n (fixedWidthCoshScale c n))
      (fixedWidthTensorCoeff w n))) hn

/-- For every preassigned positive width, its finite real Gaussian-Weil arithmetic quadratics are
all nonnegative exactly when RH holds. -/
theorem riemannHypothesis_iff_fixedWidth_gaussianXiArithmeticQuadratic_re_nonneg
    {a0 : ℝ} (ha0 : 0 < a0) :
    RiemannHypothesis ↔
      ∀ (ι : Type) [Fintype ι], ∀ b w : ι → ℝ,
        0 ≤ (gaussianXiArithmeticQuadratic a0 b w 2).re := by
  constructor
  · intro hRH ι _inst b w
    exact RiemannHypothesis.gaussianXiArithmeticQuadratic_re_nonneg
      hRH ha0 (by norm_num) b w
  · exact riemannHypothesis_of_fixedWidth_gaussianXiArithmeticQuadratic_re_nonneg ha0

end

end LeanLab.Riemann
