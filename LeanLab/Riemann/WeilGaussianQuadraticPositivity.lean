import LeanLab.Riemann.WeilFiniteGaussianTestCore

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Gaussian-Weil quadratic positivity under RH

This module applies the finite symmetric-Gaussian packet formula to every ordered pair of a
finite family of real shifts. Under RH, the zero side is an exponentially damped sum of two
squares, so the real part of the corresponding direct arithmetic expression is nonnegative.

The result is only the RH-forward direction for this finite Gaussian kernel. It does not assert
unconditional positivity or a converse criterion for RH.
-/

open Complex
open scoped BigOperators

namespace LeanLab.Riemann

noncomputable section

/-- The common Gaussian width on an ordered-pair packet. -/
def gaussianWeilPairWidth {ι : Type*} (a : ℝ) : ι × ι → ℝ :=
  fun _ => a

/-- The difference shift on an ordered-pair packet. -/
def gaussianWeilPairShift {ι : Type*} (b : ι → ℝ) : ι × ι → ℝ :=
  fun q => b q.1 - b q.2

/-- The real Gram coefficient on an ordered-pair packet, embedded in `ℂ`. -/
def gaussianWeilPairCoeff {ι : Type*} (w : ι → ℝ) : ι × ι → ℂ :=
  fun q => (w q.1 * w q.2 : ℝ)

/-- The divisor-indexed zero sum of the Gaussian ordered-pair packet. -/
def gaussianXiZeroQuadratic
    {ι : Type*} [Fintype ι] (a : ℝ) (b w : ι → ℝ) : ℂ :=
  ∑' p : RiemannXiDivisorZeroIndex,
    riemannXiSymmetricGaussianPacketWeight
      (gaussianWeilPairWidth a) (gaussianWeilPairShift b)
      (gaussianWeilPairCoeff w) (riemannXiDivisorZeroValue p)

/-- The nonnegative real summand obtained from a divisor zero on the critical line. -/
def gaussianXiZeroSquareTerm
    {ι : Type*} [Fintype ι] (a : ℝ) (b w : ι → ℝ)
    (p : RiemannXiDivisorZeroIndex) : ℝ :=
  Real.exp (-a * (riemannXiDivisorZeroValue p).im ^ 2) *
    ((∑ i, w i * Real.cos (b i * (riemannXiDivisorZeroValue p).im)) ^ 2 +
      (∑ i, w i * Real.sin (b i * (riemannXiDivisorZeroValue p).im)) ^ 2)

/-- The direct pole, real-place, and prime-power expression of the ordered-pair packet. -/
def gaussianXiArithmeticQuadratic
    {ι : Type*} [Fintype ι] (a : ℝ) (b w : ι → ℝ) (c : ℝ) : ℂ :=
  2 * (Real.pi : ℂ) *
      symmetricGaussianXiPacketPoleFactor
        (gaussianWeilPairWidth a) (gaussianWeilPairShift b)
        (gaussianWeilPairCoeff w) +
    symmetricGaussianXiPacketArchimedeanIntegral
      (gaussianWeilPairWidth a) (gaussianWeilPairShift b)
      (gaussianWeilPairCoeff w) c -
    ∑' n : ℕ,
      symmetricGaussianPacketVonMangoldtWeight
        (gaussianWeilPairWidth a) (gaussianWeilPairShift b)
        (gaussianWeilPairCoeff w) n

/-- Under RH, a symmetric Gaussian probe at a divisor zero is a real Gaussian-cosine weight. -/
theorem RiemannHypothesis.riemannXiSymmetricGaussianWeight_on_criticalLine
    (hRH : RiemannHypothesis) (a b : ℝ) (p : RiemannXiDivisorZeroIndex) :
    riemannXiSymmetricGaussianWeight a b (riemannXiDivisorZeroValue p) =
      (Real.exp (-a * (riemannXiDivisorZeroValue p).im ^ 2) *
        Real.cos (b * (riemannXiDivisorZeroValue p).im) : ℝ) := by
  have hline := RiemannHypothesis.nontrivial_zero_on_line hRH
    (riemannXiDivisorZeroIndex_val_isNontrivialZero p)
  change (riemannXiDivisorZeroValue p).re = 1 / 2 at hline
  have hcenter : riemannXiDivisorZeroValue p - 1 / 2 =
      ((riemannXiDivisorZeroValue p).im : ℂ) * I := by
    apply Complex.ext
    · simp [hline]
    · simp
  rw [riemannXiSymmetricGaussianWeight, riemannXiGaussianWeight, hcenter]
  rw [show (a : ℂ) * (((riemannXiDivisorZeroValue p).im : ℂ) * I) ^ 2 =
      ((-a * (riemannXiDivisorZeroValue p).im ^ 2 : ℝ) : ℂ) by
    push_cast
    rw [mul_pow, I_sq]
    ring]
  rw [show (b : ℂ) * ((riemannXiDivisorZeroValue p).im * I) =
      ((b * (riemannXiDivisorZeroValue p).im : ℝ) : ℂ) * I by
    push_cast
    ring]
  rw [← Complex.ofReal_exp, Complex.cosh_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_mul]

/-- The real cosine-difference kernel is the Gram kernel of cosine and sine coordinates. -/
theorem gaussianWeil_sum_mul_cos_sub_eq_sq_add_sq
    {ι : Type*} [Fintype ι] (b w : ι → ℝ) (t : ℝ) :
    (∑ i, ∑ j, w i * w j * Real.cos ((b i - b j) * t)) =
      (∑ i, w i * Real.cos (b i * t)) ^ 2 +
        (∑ i, w i * Real.sin (b i * t)) ^ 2 := by
  classical
  have harg (i j : ι) : (b i - b j) * t = b i * t - b j * t := by ring
  simp_rw [harg, Real.cos_sub, mul_add]
  simp_rw [Finset.sum_add_distrib]
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  · apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro j _hj
    ring

/-- Under RH, every ordered-pair packet value at a zero is its nonnegative square term. -/
theorem RiemannHypothesis.gaussianWeilPacket_on_criticalLine
    {ι : Type*} [Fintype ι] (hRH : RiemannHypothesis)
    (a : ℝ) (b w : ι → ℝ) (p : RiemannXiDivisorZeroIndex) :
    riemannXiSymmetricGaussianPacketWeight
        (gaussianWeilPairWidth a) (gaussianWeilPairShift b)
        (gaussianWeilPairCoeff w) (riemannXiDivisorZeroValue p) =
      (gaussianXiZeroSquareTerm a b w p : ℝ) := by
  classical
  rw [riemannXiSymmetricGaussianPacketWeight, Fintype.sum_prod_type]
  simp_rw [gaussianWeilPairWidth, gaussianWeilPairShift, gaussianWeilPairCoeff,
    RiemannHypothesis.riemannXiSymmetricGaussianWeight_on_criticalLine hRH]
  norm_cast
  rw [gaussianXiZeroSquareTerm]
  calc
    (∑ i, ∑ j, w i * w j *
        (Real.exp (-a * (riemannXiDivisorZeroValue p).im ^ 2) *
          Real.cos ((b i - b j) * (riemannXiDivisorZeroValue p).im))) =
        Real.exp (-a * (riemannXiDivisorZeroValue p).im ^ 2) *
          ∑ i, ∑ j, w i * w j *
            Real.cos ((b i - b j) * (riemannXiDivisorZeroValue p).im) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ = _ := by
      rw [gaussianWeil_sum_mul_cos_sub_eq_sq_add_sq]

/-- Under RH and positive width, the real square family is absolutely summable. -/
theorem RiemannHypothesis.summable_gaussianXiZeroSquareTerm
    {ι : Type*} [Fintype ι] (hRH : RiemannHypothesis)
    {a : ℝ} (ha : 0 < a) (b w : ι → ℝ) :
    Summable (gaussianXiZeroSquareTerm a b w) := by
  have hpacket := summable_riemannXiSymmetricGaussianPacketWeight
    (gaussianWeilPairWidth a) (gaussianWeilPairShift b)
    (gaussianWeilPairCoeff w) (fun _ => ha)
  have hcomplex : Summable (fun p : RiemannXiDivisorZeroIndex =>
      (gaussianXiZeroSquareTerm a b w p : ℂ)) := by
    simpa only [RiemannHypothesis.gaussianWeilPacket_on_criticalLine hRH a b w] using hpacket
  simpa [Function.comp_def] using
    hcomplex.map Complex.reCLM Complex.reCLM.continuous

/-- Under RH, the packet zero `tsum` is exactly the real `tsum` of square terms. -/
theorem RiemannHypothesis.gaussianXiZeroQuadratic_eq_tsum_square
    {ι : Type*} [Fintype ι] (hRH : RiemannHypothesis)
    (a : ℝ) (b w : ι → ℝ) :
    gaussianXiZeroQuadratic a b w =
      ((∑' p : RiemannXiDivisorZeroIndex,
        gaussianXiZeroSquareTerm a b w p : ℝ) : ℂ) := by
  rw [gaussianXiZeroQuadratic, Complex.ofReal_tsum]
  apply tsum_congr
  intro p
  exact RiemannHypothesis.gaussianWeilPacket_on_criticalLine hRH a b w p

/-- Under RH, the real part of the Gaussian packet zero sum is nonnegative. -/
theorem RiemannHypothesis.gaussianXiZeroQuadratic_re_nonneg
    {ι : Type*} [Fintype ι] (hRH : RiemannHypothesis)
    (a : ℝ) (b w : ι → ℝ) :
    0 ≤ (gaussianXiZeroQuadratic a b w).re := by
  rw [RiemannHypothesis.gaussianXiZeroQuadratic_eq_tsum_square hRH a b w]
  simp only [Complex.ofReal_re]
  apply tsum_nonneg
  intro p
  unfold gaussianXiZeroSquareTerm
  positivity

/-- The zero quadratic and its direct arithmetic expression satisfy the packet explicit formula. -/
theorem gaussianXiZeroQuadratic_arithmetic_formula
    {ι : Type*} [Fintype ι] {a c : ℝ} (ha : 0 < a) (hc : 1 < c)
    (b w : ι → ℝ) :
    (Real.pi : ℂ) * gaussianXiZeroQuadratic a b w =
      gaussianXiArithmeticQuadratic a b w c := by
  exact symmetricGaussianXiPacket_arithmetic_explicit_formula
    (gaussianWeilPairWidth a) (gaussianWeilPairShift b)
    (gaussianWeilPairCoeff w) (fun _ => ha) hc

/-- Under RH, the direct arithmetic Gaussian-Weil quadratic has nonnegative real part. -/
theorem RiemannHypothesis.gaussianXiArithmeticQuadratic_re_nonneg
    {ι : Type*} [Fintype ι] (hRH : RiemannHypothesis)
    {a c : ℝ} (ha : 0 < a) (hc : 1 < c) (b w : ι → ℝ) :
    0 ≤ (gaussianXiArithmeticQuadratic a b w c).re := by
  rw [← gaussianXiZeroQuadratic_arithmetic_formula ha hc b w]
  simpa using mul_nonneg (le_of_lt Real.pi_pos)
    (RiemannHypothesis.gaussianXiZeroQuadratic_re_nonneg hRH a b w)

/-- A singleton square term reduces to one Gaussian times the square of its coefficient. -/
theorem gaussianXiZeroSquareTerm_unit
    (a b w : ℝ) (p : RiemannXiDivisorZeroIndex) :
    gaussianXiZeroSquareTerm (ι := Unit) a (fun _ => b) (fun _ => w) p =
      Real.exp (-a * (riemannXiDivisorZeroValue p).im ^ 2) * w ^ 2 := by
  simp only [gaussianXiZeroSquareTerm, Fintype.sum_unique]
  rw [mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq]
  ring

/-- The direct arithmetic quadratic is exactly zero when every coefficient is zero. -/
theorem gaussianXiArithmeticQuadratic_zero
    {ι : Type*} [Fintype ι] (a : ℝ) (b : ι → ℝ) (c : ℝ) :
    gaussianXiArithmeticQuadratic a b (fun _ => 0) c = 0 := by
  classical
  simp [gaussianXiArithmeticQuadratic, gaussianWeilPairCoeff,
    symmetricGaussianXiPacketPoleFactor, symmetricGaussianXiPacketArchimedeanIntegral,
    riemannXiSymmetricGaussianPacketWeight, symmetricGaussianPacketVonMangoldtWeight]

end

end LeanLab.Riemann
