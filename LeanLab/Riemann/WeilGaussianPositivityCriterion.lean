import LeanLab.Riemann.WeilGaussianQuadraticPositivity

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# A finite Gaussian-Weil positivity criterion for RH

This module proves the converse to the finite Gaussian quadratic positivity theorem. An off-line
xi divisor zero is isolated by a finite real exponential separator. After multiplying by a
protected polynomial, the lowest decay layer contributes a strictly negative main term while the
higher layers vanish after rescaling by dominated convergence. The explicit formula then produces
a positive-width finite real Gaussian arithmetic quadratic with negative real part.

Consequently, RH is equivalent to nonnegativity of every such quadratic over finite types in
`Type`.
-/

open Complex
open Filter
open scoped BigOperators ComplexConjugate Topology

namespace LeanLab.Riemann

noncomputable section

def gaussianCriterion_gaussianWeilExponentialSum
    {ι : Type*} [Fintype ι] (b w : ι → ℝ) (z : ℂ) : ℂ :=
  ∑ i, (w i : ℂ) * Complex.exp ((b i : ℂ) * z)

theorem gaussianCriterion_sum_mul_cosh_sub_eq_exponentialSum_mul
    {ι : Type*} [Fintype ι] (b w : ι → ℝ) (z : ℂ) :
    (∑ i, ∑ j, (w i * w j : ℝ) *
        Complex.cosh (((b i - b j : ℝ) : ℂ) * z)) =
      gaussianCriterion_gaussianWeilExponentialSum b w z *
        gaussianCriterion_gaussianWeilExponentialSum b w (-z) := by
  classical
  let S : ℂ := ∑ i, ∑ j, (w i * w j : ℝ) *
    Complex.exp (((b i - b j : ℝ) : ℂ) * z)
  let T : ℂ := ∑ i, ∑ j, (w i * w j : ℝ) *
    Complex.exp (-(((b i - b j : ℝ) : ℂ) * z))
  have hTS : T = S := by
    dsimp only [S, T]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro j _hj
    congr 1
    · push_cast
      ring
    · congr 1
      push_cast
      ring
  calc
    (∑ i, ∑ j, (w i * w j : ℝ) *
        Complex.cosh (((b i - b j : ℝ) : ℂ) * z)) = (S + T) / 2 := by
      dsimp only [S, T]
      rw [add_div]
      simp only [Finset.sum_div]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Complex.cosh]
      ring
    _ = S := by rw [hTS]; ring
    _ = gaussianCriterion_gaussianWeilExponentialSum b w z *
        gaussianCriterion_gaussianWeilExponentialSum b w (-z) := by
      dsimp only [S]
      rw [gaussianCriterion_gaussianWeilExponentialSum, gaussianCriterion_gaussianWeilExponentialSum,
        Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      have harg : (((b i - b j : ℝ) : ℂ) * z) =
          (b i : ℂ) * z + (b j : ℂ) * (-z) := by
        push_cast
        ring
      rw [harg, Complex.exp_add]
      push_cast
      ring

theorem gaussianCriterion_gaussianWeilPacket_eq_exp_mul_exponentialSum
    {ι : Type*} [Fintype ι] (a : ℝ) (b w : ι → ℝ) (rho : ℂ) :
    riemannXiSymmetricGaussianPacketWeight
        (gaussianWeilPairWidth a) (gaussianWeilPairShift b)
        (gaussianWeilPairCoeff w) rho =
      Complex.exp ((a : ℂ) * (rho - 1 / 2) ^ 2) *
        gaussianCriterion_gaussianWeilExponentialSum b w (rho - 1 / 2) *
          gaussianCriterion_gaussianWeilExponentialSum b w (-(rho - 1 / 2)) := by
  classical
  rw [riemannXiSymmetricGaussianPacketWeight, Fintype.sum_prod_type]
  simp_rw [gaussianWeilPairWidth, gaussianWeilPairShift, gaussianWeilPairCoeff,
    riemannXiSymmetricGaussianWeight, riemannXiGaussianWeight]
  calc
    (∑ i, ∑ j, (w i * w j : ℝ) *
        (Complex.exp ((a : ℂ) * (rho - 1 / 2) ^ 2) *
          Complex.cosh (((b i - b j : ℝ) : ℂ) * (rho - 1 / 2)))) =
        Complex.exp ((a : ℂ) * (rho - 1 / 2) ^ 2) *
          ∑ i, ∑ j, (w i * w j : ℝ) *
            Complex.cosh (((b i - b j : ℝ) : ℂ) * (rho - 1 / 2)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ = _ := by
      rw [gaussianCriterion_sum_mul_cosh_sub_eq_exponentialSum_mul]
      ring

def gaussianCriterion_gaussianSeparatorFactor (h : ℝ) (u : ℂ) : Polynomial ℝ :=
  Polynomial.X ^ 2 -
      Polynomial.C (2 * (Complex.exp ((h : ℂ) * u)).re) * Polynomial.X +
    Polynomial.C (Complex.normSq (Complex.exp ((h : ℂ) * u)))

theorem gaussianCriterion_eval₂_gaussianSeparatorFactor
    (h : ℝ) (u x : ℂ) :
    Polynomial.eval₂ Complex.ofRealHom x (gaussianCriterion_gaussianSeparatorFactor h u) =
      (x - Complex.exp ((h : ℂ) * u)) *
        (x - (starRingEnd ℂ) (Complex.exp ((h : ℂ) * u))) := by
  let r := Complex.exp ((h : ℂ) * u)
  simp only [gaussianCriterion_gaussianSeparatorFactor, Polynomial.eval₂_add,
    Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_ofNat,
    map_mul, map_ofNat]
  change x ^ 2 - (2 : ℂ) * (r.re : ℂ) * x + (Complex.normSq r : ℂ) =
    (x - r) * (x - (starRingEnd ℂ) r)
  have hre : (2 : ℂ) * (r.re : ℂ) = r + (starRingEnd ℂ) r := by
    rw [Complex.add_conj]
    push_cast
    rfl
  rw [hre, ← Complex.mul_conj r]
  ring

def gaussianCriterion_polynomialShift
    (P : Polynomial ℝ) (h : ℝ) (n : ↥(Finset.range (P.natDegree + 1))) : ℝ :=
  (n.1 : ℝ) * h

def gaussianCriterion_polynomialCoeff
    (P : Polynomial ℝ) (n : ↥(Finset.range (P.natDegree + 1))) : ℝ :=
  P.coeff n.1

theorem gaussianCriterion_exponentialSum_polynomialShift_coeff
    (P : Polynomial ℝ) (h : ℝ) (z : ℂ) :
    gaussianCriterion_gaussianWeilExponentialSum
        (gaussianCriterion_polynomialShift P h) (gaussianCriterion_polynomialCoeff P) z =
      Polynomial.eval₂ Complex.ofRealHom (Complex.exp ((h : ℂ) * z)) P := by
  rw [gaussianCriterion_gaussianWeilExponentialSum, Polynomial.eval₂_eq_sum_range]
  rw [Finset.sum_subtype (Finset.range (P.natDegree + 1)) (fun _ => Iff.rfl)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [gaussianCriterion_polynomialShift, gaussianCriterion_polynomialCoeff]
  congr 1
  rw [show (((n : ℝ) * h : ℝ) : ℂ) * z = (n : ℕ) * ((h : ℂ) * z) by
    push_cast
    ring]
  rw [Complex.exp_nat_mul]

def gaussianCriterion_centeredXiDivisorZero (p : RiemannXiDivisorZeroIndex) : ℂ :=
  riemannXiDivisorZeroValue p - 1 / 2

def gaussianCriterion_gaussianDecayRate (p : RiemannXiDivisorZeroIndex) : ℝ :=
  -(gaussianCriterion_centeredXiDivisorZero p ^ 2).re

theorem gaussianCriterion_gaussianDecayRate_eq (p : RiemannXiDivisorZeroIndex) :
    gaussianCriterion_gaussianDecayRate p =
      (riemannXiDivisorZeroValue p).im ^ 2 -
        ((riemannXiDivisorZeroValue p).re - 1 / 2) ^ 2 := by
  simp [gaussianCriterion_gaussianDecayRate, gaussianCriterion_centeredXiDivisorZero, pow_two]

theorem gaussianCriterion_finite_gaussianDecayRate_le
    (p0 : RiemannXiDivisorZeroIndex) :
    ({p : RiemannXiDivisorZeroIndex |
      gaussianCriterion_gaussianDecayRate p ≤ gaussianCriterion_gaussianDecayRate p0} : Set _).Finite := by
  let T : ℝ := |(riemannXiDivisorZeroValue p0).im| + 1
  apply (finite_riemannXiZeroStrictlyInsideRectangle 0 1 (-T) T).subset
  intro p hp
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
  have hcenterSq :
      ((riemannXiDivisorZeroValue p).re - 1 / 2) ^ 2 < 1 / 4 := by
    nlinarith [sq_nonneg ((riemannXiDivisorZeroValue p).re - 1 / 2)]
  change gaussianCriterion_gaussianDecayRate p ≤ gaussianCriterion_gaussianDecayRate p0 at hp
  rw [gaussianCriterion_gaussianDecayRate_eq, gaussianCriterion_gaussianDecayRate_eq] at hp
  have himSq :
      (riemannXiDivisorZeroValue p).im ^ 2 <
        (riemannXiDivisorZeroValue p0).im ^ 2 + 1 / 4 := by
    nlinarith [sq_nonneg ((riemannXiDivisorZeroValue p0).re - 1 / 2)]
  have hTpos : 0 < T := by
    dsimp only [T]
    positivity
  have hT :
      (riemannXiDivisorZeroValue p).im ^ 2 < T ^ 2 := by
    have habsSq : |(riemannXiDivisorZeroValue p0).im| ^ 2 =
        (riemannXiDivisorZeroValue p0).im ^ 2 := sq_abs _
    dsimp only [T]
    nlinarith [abs_nonneg (riemannXiDivisorZeroValue p0).im]
  have himLower : -T < (riemannXiDivisorZeroValue p).im := by
    nlinarith [sq_nonneg ((riemannXiDivisorZeroValue p).im + T)]
  have himUpper : (riemannXiDivisorZeroValue p).im < T := by
    nlinarith [sq_nonneg ((riemannXiDivisorZeroValue p).im - T)]
  exact ⟨hrePos, hreLt, himLower, himUpper⟩

theorem gaussianCriterion_exists_minimal_offLine_gaussianDecayRate
    (p0 : RiemannXiDivisorZeroIndex)
    (hp0 : (riemannXiDivisorZeroValue p0).re ≠ 1 / 2) :
    ∃ pmin : RiemannXiDivisorZeroIndex,
      (riemannXiDivisorZeroValue pmin).re ≠ 1 / 2 ∧
        ∀ p : RiemannXiDivisorZeroIndex,
          (riemannXiDivisorZeroValue p).re ≠ 1 / 2 →
            gaussianCriterion_gaussianDecayRate pmin ≤ gaussianCriterion_gaussianDecayRate p := by
  classical
  let s : Set RiemannXiDivisorZeroIndex := {p |
    gaussianCriterion_gaussianDecayRate p ≤ gaussianCriterion_gaussianDecayRate p0 ∧
      (riemannXiDivisorZeroValue p).re ≠ 1 / 2}
  have hsFinite : s.Finite :=
    (gaussianCriterion_finite_gaussianDecayRate_le p0).subset (fun _ hp => hp.1)
  let S : Finset RiemannXiDivisorZeroIndex := hsFinite.toFinset
  have hp0S : p0 ∈ S := by
    change p0 ∈ hsFinite.toFinset
    rw [hsFinite.mem_toFinset]
    exact ⟨le_rfl, hp0⟩
  obtain ⟨pmin, hpminS, hpmin⟩ :=
    S.exists_min_image gaussianCriterion_gaussianDecayRate ⟨p0, hp0S⟩
  have hpminSet : pmin ∈ s := by
    change pmin ∈ hsFinite.toFinset at hpminS
    exact hsFinite.mem_toFinset.mp hpminS
  refine ⟨pmin, hpminSet.2, ?_⟩
  intro p hpOff
  by_cases hpRate : gaussianCriterion_gaussianDecayRate p ≤ gaussianCriterion_gaussianDecayRate p0
  · apply hpmin p
    change p ∈ hsFinite.toFinset
    rw [hsFinite.mem_toFinset]
    exact ⟨hpRate, hpOff⟩
  · have hp0Le : gaussianCriterion_gaussianDecayRate pmin ≤ gaussianCriterion_gaussianDecayRate p0 :=
      hpmin p0 hp0S
    exact hp0Le.trans (le_of_lt (lt_of_not_ge hpRate))

theorem gaussianCriterion_exists_pos_exp_mul_separates_finset
    (z0 : ℂ) (U : Finset ℂ) (hz0 : z0 ∉ U) :
    ∃ h : ℝ, 0 < h ∧ ∀ u ∈ U,
      Complex.exp ((h : ℂ) * z0) ≠ Complex.exp ((h : ℂ) * u) := by
  let D : ℝ := |z0.im| + ∑ u ∈ U, |u.im|
  let h : ℝ := 1 / (D + 1)
  have hDnonneg : 0 ≤ D := by
    dsimp only [D]
    positivity
  have hdenom : 0 < D + 1 := by linarith
  have hhpos : 0 < h := by
    dsimp only [h]
    positivity
  have hhD : h * D < 1 := by
    rw [show h * D = D / (D + 1) by
      dsimp only [h]
      field_simp]
    exact (div_lt_one hdenom).2 (by linarith)
  have hzAbs : |h * z0.im| < 1 := by
    rw [abs_mul, abs_of_pos hhpos]
    have hzLe : |z0.im| ≤ D := by
      dsimp only [D]
      have hsum : 0 ≤ ∑ u ∈ U, |u.im| := by positivity
      linarith
    exact (mul_le_mul_of_nonneg_left hzLe hhpos.le).trans_lt hhD
  refine ⟨h, hhpos, ?_⟩
  intro u hu hExp
  have huLeSum : |u.im| ≤ ∑ v ∈ U, |v.im| :=
    Finset.single_le_sum (fun v _hv => abs_nonneg v.im) hu
  have huLeD : |u.im| ≤ D := by
    dsimp only [D]
    linarith [abs_nonneg z0.im]
  have huAbs : |h * u.im| < 1 := by
    rw [abs_mul, abs_of_pos hhpos]
    exact (mul_le_mul_of_nonneg_left huLeD hhpos.le).trans_lt hhD
  have hzBounds := abs_lt.mp hzAbs
  have huBounds := abs_lt.mp huAbs
  have honeLtPi : (1 : ℝ) < Real.pi := by
    linarith [Real.pi_gt_three]
  have hnegPiLtNegOne : -Real.pi < (-1 : ℝ) := neg_lt_neg honeLtPi
  have hEq : (h : ℂ) * z0 = (h : ℂ) * u := by
    apply Complex.exp_inj_of_neg_pi_lt_of_le_pi
    · simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, add_zero] using hnegPiLtNegOne.trans hzBounds.1
    · have := hzBounds.2.trans honeLtPi
      simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, add_zero] using this.le
    · simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, add_zero] using hnegPiLtNegOne.trans huBounds.1
    · have := huBounds.2.trans honeLtPi
      simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, add_zero] using this.le
    · exact hExp
  have hzEq : z0 = u := by
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hhpos.ne') hEq
  exact hz0 (hzEq ▸ hu)

theorem gaussianCriterion_star_exp_ofReal_mul (h : ℝ) (u : ℂ) :
    (starRingEnd ℂ) (Complex.exp ((h : ℂ) * u)) =
      Complex.exp ((h : ℂ) * (starRingEnd ℂ) u) := by
  rw [← Complex.exp_conj]
  congr 1
  simp

theorem gaussianCriterion_exists_pos_exp_mul_separates_finset_and_stars
    (z0 : ℂ) (U : Finset ℂ)
    (hz0 : z0 ∉ U ∪ U.image (starRingEnd ℂ)) :
    ∃ h : ℝ, 0 < h ∧ ∀ u ∈ U,
      Complex.exp ((h : ℂ) * z0) ≠ Complex.exp ((h : ℂ) * u) ∧
        Complex.exp ((h : ℂ) * z0) ≠
          (starRingEnd ℂ) (Complex.exp ((h : ℂ) * u)) := by
  classical
  obtain ⟨h, hh, hsep⟩ :=
    gaussianCriterion_exists_pos_exp_mul_separates_finset z0
      (U ∪ U.image (starRingEnd ℂ)) hz0
  refine ⟨h, hh, ?_⟩
  intro u hu
  constructor
  · exact hsep u (Finset.mem_union_left _ hu)
  · rw [gaussianCriterion_star_exp_ofReal_mul]
    exact hsep ((starRingEnd ℂ) u)
      (Finset.mem_union_right U (Finset.mem_image.mpr ⟨u, hu, rfl⟩))

theorem gaussianCriterion_exists_pos_exp_mul_separates_finsets
    (V U : Finset ℂ) (hdisjoint : Disjoint V U) :
    ∃ h : ℝ, 0 < h ∧ ∀ v ∈ V, ∀ u ∈ U,
      Complex.exp ((h : ℂ) * v) ≠ Complex.exp ((h : ℂ) * u) := by
  classical
  let W : Finset ℂ := (V ×ˢ U).image (fun q => q.1 - q.2)
  have hzero : (0 : ℂ) ∉ W := by
    intro hmem
    obtain ⟨q, hq, hqzero⟩ := Finset.mem_image.mp hmem
    have hqmem := Finset.mem_product.mp hq
    have hqu : q.1 = q.2 := sub_eq_zero.mp hqzero
    have hqU : q.1 ∈ U := by simpa [hqu] using hqmem.2
    exact Finset.disjoint_left.mp hdisjoint hqmem.1 hqU
  obtain ⟨h, hh, hsep⟩ :=
    gaussianCriterion_exists_pos_exp_mul_separates_finset 0 W hzero
  refine ⟨h, hh, ?_⟩
  intro v hv u hu hExp
  have hvuW : v - u ∈ W :=
    Finset.mem_image.mpr ⟨(v, u), Finset.mem_product.mpr ⟨hv, hu⟩, rfl⟩
  have harg : (h : ℂ) * (v - u) = (h : ℂ) * v - (h : ℂ) * u := by ring
  have hdiff : Complex.exp ((h : ℂ) * (v - u)) = 1 := by
    rw [harg, Complex.exp_sub, hExp]
    exact div_self (Complex.exp_ne_zero _)
  exact hsep (v - u) hvuW (by simp [hdiff])

def gaussianCriterion_gaussianSeparatorPolynomial (h : ℝ) (U : Finset ℂ) : Polynomial ℝ :=
  ∏ u ∈ U, gaussianCriterion_gaussianSeparatorFactor h u

theorem gaussianCriterion_eval₂_gaussianSeparatorPolynomial_eq_zero
    (h : ℝ) (U : Finset ℂ) {u : ℂ} (hu : u ∈ U) :
    Polynomial.eval₂ Complex.ofRealHom (Complex.exp ((h : ℂ) * u))
        (gaussianCriterion_gaussianSeparatorPolynomial h U) = 0 := by
  classical
  rw [gaussianCriterion_gaussianSeparatorPolynomial, Polynomial.eval₂_finsetProd]
  apply Finset.prod_eq_zero hu
  rw [gaussianCriterion_eval₂_gaussianSeparatorFactor]
  simp

theorem gaussianCriterion_eval₂_gaussianSeparatorPolynomial_ne_zero
    (h : ℝ) (U : Finset ℂ) (z0 : ℂ)
    (hsep : ∀ u ∈ U,
      Complex.exp ((h : ℂ) * z0) ≠ Complex.exp ((h : ℂ) * u) ∧
        Complex.exp ((h : ℂ) * z0) ≠
          (starRingEnd ℂ) (Complex.exp ((h : ℂ) * u))) :
    Polynomial.eval₂ Complex.ofRealHom (Complex.exp ((h : ℂ) * z0))
        (gaussianCriterion_gaussianSeparatorPolynomial h U) ≠ 0 := by
  classical
  rw [gaussianCriterion_gaussianSeparatorPolynomial, Polynomial.eval₂_finsetProd]
  apply Finset.prod_ne_zero_iff.mpr
  intro u hu
  rw [gaussianCriterion_eval₂_gaussianSeparatorFactor]
  exact mul_ne_zero (sub_ne_zero.mpr (hsep u hu).1)
    (sub_ne_zero.mpr (hsep u hu).2)

def gaussianCriterion_gaussianProtectedSeparatorPolynomial
    (h : ℝ) (U : Finset ℂ) : Polynomial ℝ :=
  gaussianCriterion_gaussianSeparatorPolynomial h U ^ 2 * (Polynomial.X - 1)

theorem gaussianCriterion_complex_exp_ofReal_mul_ne_one_of_re_ne_zero
    {h : ℝ} (hh : 0 < h) {z : ℂ} (hz : z.re ≠ 0) :
    Complex.exp ((h : ℂ) * z) ≠ 1 := by
  intro hExp
  have hnorm := congrArg norm hExp
  rw [Complex.norm_exp, norm_one] at hnorm
  have hreZero : ((h : ℂ) * z).re = 0 :=
    Iff.mp (Real.exp_eq_one_iff _) hnorm
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hreZero
  exact hz ((mul_eq_zero.mp hreZero).resolve_left hh.ne')

theorem gaussianCriterion_eval₂_gaussianProtectedSeparatorPolynomial_eq_zero
    (h : ℝ) (U : Finset ℂ) {u : ℂ} (hu : u ∈ U) :
    Polynomial.eval₂ Complex.ofRealHom (Complex.exp ((h : ℂ) * u))
        (gaussianCriterion_gaussianProtectedSeparatorPolynomial h U) = 0 := by
  rw [gaussianCriterion_gaussianProtectedSeparatorPolynomial, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow,
    gaussianCriterion_eval₂_gaussianSeparatorPolynomial_eq_zero h U hu]
  simp

theorem gaussianCriterion_eval₂_gaussianProtectedSeparatorPolynomial_ne_zero
    {h : ℝ} (hh : 0 < h) (U : Finset ℂ) {z : ℂ} (hz : z.re ≠ 0)
    (hsep : ∀ u ∈ U,
      Complex.exp ((h : ℂ) * z) ≠ Complex.exp ((h : ℂ) * u) ∧
        Complex.exp ((h : ℂ) * z) ≠
          (starRingEnd ℂ) (Complex.exp ((h : ℂ) * u))) :
    Polynomial.eval₂ Complex.ofRealHom (Complex.exp ((h : ℂ) * z))
        (gaussianCriterion_gaussianProtectedSeparatorPolynomial h U) ≠ 0 := by
  rw [gaussianCriterion_gaussianProtectedSeparatorPolynomial, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_sub, Polynomial.eval₂_X,
    Polynomial.eval₂_one]
  exact mul_ne_zero
    (pow_ne_zero 2 (gaussianCriterion_eval₂_gaussianSeparatorPolynomial_ne_zero h U z hsep))
    (sub_ne_zero.mpr (gaussianCriterion_complex_exp_ofReal_mul_ne_one_of_re_ne_zero hh hz))

theorem gaussianCriterion_norm_scaled_gaussian_exp_le
    {q0 q a : ℝ} {z C : ℂ} (ha : 1 ≤ a) (hq : q0 < q)
    (hqz : q = -(z ^ 2).re) :
    ‖(Real.exp (a * q0) : ℂ) * Complex.exp ((a : ℂ) * z ^ 2) * C‖ ≤
      Real.exp q0 * (Real.exp ((z ^ 2).re) * ‖C‖) := by
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), Complex.norm_exp, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  calc
    Real.exp (a * q0) * Real.exp (a * (z ^ 2).re) * ‖C‖ =
        Real.exp (a * q0 + a * (z ^ 2).re) * ‖C‖ := by
      rw [Real.exp_add]
    _ ≤
        Real.exp (q0 + (z ^ 2).re) * ‖C‖ := by
      apply mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg C)
      rw [hqz] at hq
      nlinarith
    _ = Real.exp q0 * (Real.exp ((z ^ 2).re) * ‖C‖) := by
      rw [Real.exp_add, mul_assoc]

theorem gaussianCriterion_tendsto_scaled_gaussian_exp_zero
    {q0 q : ℝ} {z C : ℂ} (hq : q0 < q) (hqz : q = -(z ^ 2).re) :
    Tendsto
      (fun a : ℝ =>
        (Real.exp (a * q0) : ℂ) * Complex.exp ((a : ℂ) * z ^ 2) * C)
      atTop (𝓝 0) := by
  have hcoef : (((q0 : ℂ) + z ^ 2).re) < 0 := by
    simp only [Complex.add_re, Complex.ofReal_re]
    rw [hqz] at hq
    linarith
  have hexp : Tendsto
      (fun a : ℝ => Complex.exp (((q0 : ℂ) + z ^ 2) * (a : ℂ)))
      atTop (𝓝 0) := by
    simpa [Complex.tendsto_exp_nhds_zero_iff, mul_re] using
      tendsto_const_nhds.neg_mul_atTop hcoef tendsto_id
  have htarget : Tendsto
      (fun a : ℝ => Complex.exp (((q0 : ℂ) + z ^ 2) * (a : ℂ)) * C)
      atTop (𝓝 0) := by
    simpa using hexp.mul_const C
  apply htarget.congr'
  filter_upwards [] with a
  rw [show ((Real.exp (a * q0) : ℝ) : ℂ) =
      Complex.exp ((a * q0 : ℝ) : ℂ) by rw [Complex.ofReal_exp]]
  rw [← Complex.exp_add]
  congr 2
  push_cast
  ring

def gaussianCriterion_gaussianGeneratedPacket
    (P : Polynomial ℝ) (h a : ℝ) (p : RiemannXiDivisorZeroIndex) : ℂ :=
  riemannXiSymmetricGaussianPacketWeight
    (gaussianWeilPairWidth a)
    (gaussianWeilPairShift (gaussianCriterion_polynomialShift P h))
    (gaussianWeilPairCoeff (gaussianCriterion_polynomialCoeff P))
    (riemannXiDivisorZeroValue p)

def gaussianCriterion_gaussianScaledHigherTerm
    (q0 : ℝ) (P : Polynomial ℝ) (h a : ℝ)
    (p : RiemannXiDivisorZeroIndex) : ℂ :=
  if q0 < gaussianCriterion_gaussianDecayRate p then
    (Real.exp (a * q0) : ℂ) * gaussianCriterion_gaussianGeneratedPacket P h a p
  else 0

theorem gaussianCriterion_tendsto_tsum_gaussianScaledHigherTerm_zero
    (q0 : ℝ) (P : Polynomial ℝ) (h : ℝ) :
    Tendsto
      (fun a : ℝ => ∑' p : RiemannXiDivisorZeroIndex,
        gaussianCriterion_gaussianScaledHigherTerm q0 P h a p)
      atTop (𝓝 0) := by
  let b := gaussianCriterion_polynomialShift P h
  let w := gaussianCriterion_polynomialCoeff P
  have hpacketOne : Summable (gaussianCriterion_gaussianGeneratedPacket P h 1) := by
    exact summable_riemannXiSymmetricGaussianPacketWeight
      (gaussianWeilPairWidth 1) (gaussianWeilPairShift b)
      (gaussianWeilPairCoeff w) (fun _ => by simp [gaussianWeilPairWidth])
  have hbound : Summable (fun p : RiemannXiDivisorZeroIndex =>
      Real.exp q0 * ‖gaussianCriterion_gaussianGeneratedPacket P h 1 p‖) :=
    Summable.mul_left (Real.exp q0) hpacketOne.norm
  have hpoint (p : RiemannXiDivisorZeroIndex) :
      Tendsto (fun a : ℝ => gaussianCriterion_gaussianScaledHigherTerm q0 P h a p)
        atTop (𝓝 0) := by
    by_cases hp : q0 < gaussianCriterion_gaussianDecayRate p
    · rw [show (fun a : ℝ => gaussianCriterion_gaussianScaledHigherTerm q0 P h a p) =
          fun a : ℝ => (Real.exp (a * q0) : ℂ) *
            gaussianCriterion_gaussianGeneratedPacket P h a p by
        funext a
        simp only [gaussianCriterion_gaussianScaledHigherTerm, if_pos hp]]
      simp_rw [gaussianCriterion_gaussianGeneratedPacket,
        gaussianCriterion_gaussianWeilPacket_eq_exp_mul_exponentialSum]
      simpa only [gaussianCriterion_centeredXiDivisorZero, mul_assoc] using
        (gaussianCriterion_tendsto_scaled_gaussian_exp_zero
          (z := gaussianCriterion_centeredXiDivisorZero p)
          (C := gaussianCriterion_gaussianWeilExponentialSum
              (gaussianCriterion_polynomialShift P h) (gaussianCriterion_polynomialCoeff P)
                (gaussianCriterion_centeredXiDivisorZero p) *
            gaussianCriterion_gaussianWeilExponentialSum
              (gaussianCriterion_polynomialShift P h) (gaussianCriterion_polynomialCoeff P)
                (-gaussianCriterion_centeredXiDivisorZero p)) hp rfl)
    · simp only [gaussianCriterion_gaussianScaledHigherTerm, if_neg hp]
      exact tendsto_const_nhds
  have heventual : ∀ᶠ a : ℝ in atTop, ∀ p : RiemannXiDivisorZeroIndex,
      ‖gaussianCriterion_gaussianScaledHigherTerm q0 P h a p‖ ≤
        Real.exp q0 * ‖gaussianCriterion_gaussianGeneratedPacket P h 1 p‖ := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with a ha p
    by_cases hp : q0 < gaussianCriterion_gaussianDecayRate p
    · simp only [gaussianCriterion_gaussianScaledHigherTerm, if_pos hp,
        gaussianCriterion_gaussianGeneratedPacket]
      rw [gaussianCriterion_gaussianWeilPacket_eq_exp_mul_exponentialSum,
        gaussianCriterion_gaussianWeilPacket_eq_exp_mul_exponentialSum]
      simpa only [gaussianCriterion_centeredXiDivisorZero, one_mul, Complex.ofReal_one,
        mul_assoc, norm_mul, Complex.norm_exp] using
        (gaussianCriterion_norm_scaled_gaussian_exp_le
          (z := gaussianCriterion_centeredXiDivisorZero p)
          (C := gaussianCriterion_gaussianWeilExponentialSum
              (gaussianCriterion_polynomialShift P h) (gaussianCriterion_polynomialCoeff P)
                (gaussianCriterion_centeredXiDivisorZero p) *
            gaussianCriterion_gaussianWeilExponentialSum
              (gaussianCriterion_polynomialShift P h) (gaussianCriterion_polynomialCoeff P)
                (-gaussianCriterion_centeredXiDivisorZero p)) ha hp (rfl :
            gaussianCriterion_gaussianDecayRate p =
              -(gaussianCriterion_centeredXiDivisorZero p ^ 2).re))
    · simp only [gaussianCriterion_gaussianScaledHigherTerm, if_neg hp, norm_zero]
      positivity
  simpa using tendsto_tsum_of_dominated_convergence hbound hpoint heventual

theorem gaussianCriterion_phase_pi_sub_arg_re (C : ℂ) :
    (Complex.exp ((((Real.pi - Complex.arg C : ℝ) : ℂ) * I)) * C).re =
      -‖C‖ := by
  have hcomplex :
      Complex.exp ((((Real.pi - Complex.arg C : ℝ) : ℂ) * I)) * C =
        -(‖C‖ : ℂ) := by
    have hpolar : (‖C‖ : ℂ) * Complex.exp ((Complex.arg C : ℂ) * I) = C :=
      Complex.norm_mul_exp_arg_mul_I C
    calc
      Complex.exp ((((Real.pi - Complex.arg C : ℝ) : ℂ) * I)) * C =
          Complex.exp ((((Real.pi - Complex.arg C : ℝ) : ℂ) * I)) *
            ((‖C‖ : ℂ) * Complex.exp ((Complex.arg C : ℂ) * I)) := by
        rw [hpolar]
      _ = (‖C‖ : ℂ) *
            (Complex.exp ((((Real.pi - Complex.arg C : ℝ) : ℂ) * I)) *
              Complex.exp ((Complex.arg C : ℂ) * I)) := by ring
      _ = (‖C‖ : ℂ) * Complex.exp ((Real.pi : ℂ) * I) := by
        rw [← Complex.exp_add]
        congr 2
        push_cast
        ring
      _ = -(‖C‖ : ℂ) := by rw [Complex.exp_pi_mul_I]; ring
  rw [hcomplex]
  simp

theorem gaussianCriterion_exists_phase_locked_widths
    {theta : ℝ} (htheta : theta ≠ 0) (C : ℂ) :
    ∃ A : ℕ → ℝ, Tendsto A atTop atTop ∧
      ∀ n : ℕ,
        (Complex.exp (((A n * theta : ℝ) : ℂ) * I) * C).re = -‖C‖ := by
  let a0 : ℝ := (Real.pi - Complex.arg C) / theta
  rcases lt_or_gt_of_ne htheta with hthetaNeg | hthetaPos
  · let T : ℝ := -(2 * Real.pi) / theta
    have hTpos : 0 < T := by
      dsimp only [T]
      exact div_pos_of_neg_of_neg (neg_lt_zero.mpr Real.two_pi_pos) hthetaNeg
    let A : ℕ → ℝ := fun n => a0 + (n : ℝ) * T
    have hA : Tendsto A atTop atTop := by
      have hmul := tendsto_natCast_atTop_atTop.const_mul_atTop hTpos
      simpa only [A, add_comm, mul_comm] using hmul.atTop_add tendsto_const_nhds
    refine ⟨A, hA, ?_⟩
    intro n
    have hphase : A n * theta =
        (Real.pi - Complex.arg C) - (n : ℝ) * (2 * Real.pi) := by
      dsimp only [A, a0, T]
      field_simp [htheta]
      ring
    rw [hphase]
    rw [show (((Real.pi - Complex.arg C) - (n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) =
        ((Real.pi - Complex.arg C : ℝ) : ℂ) -
          (n : ℂ) * (2 * (Real.pi : ℂ)) by
      push_cast
      ring]
    rw [Complex.exp_mul_I_periodic.sub_nat_mul_eq n]
    exact gaussianCriterion_phase_pi_sub_arg_re C
  · let T : ℝ := (2 * Real.pi) / theta
    have hTpos : 0 < T := by
      dsimp only [T]
      exact div_pos Real.two_pi_pos hthetaPos
    let A : ℕ → ℝ := fun n => a0 + (n : ℝ) * T
    have hA : Tendsto A atTop atTop := by
      have hmul := tendsto_natCast_atTop_atTop.const_mul_atTop hTpos
      simpa only [A, add_comm, mul_comm] using hmul.atTop_add tendsto_const_nhds
    refine ⟨A, hA, ?_⟩
    intro n
    have hphase : A n * theta =
        (Real.pi - Complex.arg C) + (n : ℝ) * (2 * Real.pi) := by
      dsimp only [A, a0, T]
      field_simp [htheta]
    rw [hphase]
    rw [show (((Real.pi - Complex.arg C) + (n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) =
        ((Real.pi - Complex.arg C : ℝ) : ℂ) +
          (n : ℂ) * (2 * (Real.pi : ℂ)) by
      push_cast
      ring]
    have hperiod :
        Complex.exp ((((Real.pi - Complex.arg C : ℝ) : ℂ) +
              (n : ℂ) * (2 * (Real.pi : ℂ))) * I) =
          Complex.exp (((Real.pi - Complex.arg C : ℝ) : ℂ) * I) :=
      (Complex.exp_mul_I_periodic.nat_mul n)
        ((Real.pi - Complex.arg C : ℝ) : ℂ)
    rw [hperiod]
    exact gaussianCriterion_phase_pi_sub_arg_re C

theorem gaussianCriterion_exp_mul_sub_one_mul_inv_sub_one_neg
    {x : ℝ} (hx : 0 < x) (hxone : x ≠ 1) :
    (x - 1) * (x⁻¹ - 1) < 0 := by
  have hsq : 0 < (x - 1) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hxone)
  have hid : (x - 1) * (x⁻¹ - 1) = -((x - 1) ^ 2) / x := by
    field_simp [hx.ne']
    ring
  rw [hid]
  exact div_neg_of_neg_of_pos (neg_lt_zero.mpr hsq) hx

theorem gaussianCriterion_real_eval_gaussianProtectedSeparatorPolynomial_product_neg
    (h : ℝ) (U : Finset ℂ) {x : ℝ} (hx : 0 < x) (hxone : x ≠ 1)
    (hforward : (gaussianCriterion_gaussianSeparatorPolynomial h U).eval x ≠ 0)
    (hbackward : (gaussianCriterion_gaussianSeparatorPolynomial h U).eval x⁻¹ ≠ 0) :
    (gaussianCriterion_gaussianProtectedSeparatorPolynomial h U).eval x *
        (gaussianCriterion_gaussianProtectedSeparatorPolynomial h U).eval x⁻¹ < 0 := by
  have hsquares : 0 <
      (gaussianCriterion_gaussianSeparatorPolynomial h U).eval x ^ 2 *
        (gaussianCriterion_gaussianSeparatorPolynomial h U).eval x⁻¹ ^ 2 :=
    mul_pos (sq_pos_of_ne_zero hforward) (sq_pos_of_ne_zero hbackward)
  rw [gaussianCriterion_gaussianProtectedSeparatorPolynomial, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one]
  rw [show
      (gaussianCriterion_gaussianSeparatorPolynomial h U).eval x ^ 2 * (x - 1) *
          ((gaussianCriterion_gaussianSeparatorPolynomial h U).eval x⁻¹ ^ 2 * (x⁻¹ - 1)) =
        ((gaussianCriterion_gaussianSeparatorPolynomial h U).eval x ^ 2 *
          (gaussianCriterion_gaussianSeparatorPolynomial h U).eval x⁻¹ ^ 2) *
            ((x - 1) * (x⁻¹ - 1)) by ring]
  exact mul_neg_of_pos_of_neg hsquares
    (gaussianCriterion_exp_mul_sub_one_mul_inv_sub_one_neg hx hxone)

theorem gaussianCriterion_exp_ofReal_mul_real_center
    (h : ℝ) {z : ℂ} (hzreal : z.im = 0) :
    Complex.exp ((h : ℂ) * z) = (Real.exp (h * z.re) : ℂ) := by
  have harg : (h : ℂ) * z = ((h * z.re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [Complex.mul_re]
    · simp [Complex.mul_im, hzreal]
  rw [harg, ← Complex.ofReal_exp]

theorem gaussianCriterion_eval₂_gaussianProtectedSeparatorPolynomial_product_re_neg_of_real
    {h : ℝ} (hh : 0 < h) (U : Finset ℂ) {z : ℂ}
    (hzreal : z.im = 0) (hzre : z.re ≠ 0)
    (hsepForward : ∀ u ∈ U,
      Complex.exp ((h : ℂ) * z) ≠ Complex.exp ((h : ℂ) * u) ∧
        Complex.exp ((h : ℂ) * z) ≠
          (starRingEnd ℂ) (Complex.exp ((h : ℂ) * u)))
    (hsepBackward : ∀ u ∈ U,
      Complex.exp ((h : ℂ) * (-z)) ≠ Complex.exp ((h : ℂ) * u) ∧
        Complex.exp ((h : ℂ) * (-z)) ≠
          (starRingEnd ℂ) (Complex.exp ((h : ℂ) * u))) :
    (Polynomial.eval₂ Complex.ofRealHom (Complex.exp ((h : ℂ) * z))
          (gaussianCriterion_gaussianProtectedSeparatorPolynomial h U) *
        Polynomial.eval₂ Complex.ofRealHom (Complex.exp ((h : ℂ) * (-z)))
          (gaussianCriterion_gaussianProtectedSeparatorPolynomial h U)).re < 0 := by
  let x : ℝ := Real.exp (h * z.re)
  have hx : 0 < x := by simp only [x, Real.exp_pos]
  have hxone : x ≠ 1 := by
    intro hEq
    have hzero : h * z.re = 0 := Iff.mp (Real.exp_eq_one_iff _) hEq
    exact hzre ((mul_eq_zero.mp hzero).resolve_left hh.ne')
  have hznegReal : (-z).im = 0 := by simp [hzreal]
  have hforwardComplex :=
    gaussianCriterion_eval₂_gaussianSeparatorPolynomial_ne_zero h U z hsepForward
  have hbackwardComplex :=
    gaussianCriterion_eval₂_gaussianSeparatorPolynomial_ne_zero h U (-z) hsepBackward
  have hevalForward (Q : Polynomial ℝ) :
      Polynomial.eval₂ Complex.ofRealHom (x : ℂ) Q =
        ((Q.eval x : ℝ) : ℂ) := by
    change Polynomial.eval₂ Complex.ofRealHom (Complex.ofRealHom x) Q =
      Complex.ofRealHom (Q.eval x)
    exact Polynomial.eval₂_at_apply Complex.ofRealHom x
  have hevalBackward (Q : Polynomial ℝ) :
      Polynomial.eval₂ Complex.ofRealHom ((x⁻¹ : ℝ) : ℂ) Q =
        ((Q.eval (x⁻¹ : ℝ) : ℝ) : ℂ) := by
    change Polynomial.eval₂ Complex.ofRealHom (Complex.ofRealHom (x⁻¹ : ℝ)) Q =
      Complex.ofRealHom (Q.eval (x⁻¹ : ℝ))
    exact Polynomial.eval₂_at_apply Complex.ofRealHom (x⁻¹ : ℝ)
  have hforward : (gaussianCriterion_gaussianSeparatorPolynomial h U).eval x ≠ 0 := by
    rw [gaussianCriterion_exp_ofReal_mul_real_center h hzreal] at hforwardComplex
    change Polynomial.eval₂ Complex.ofRealHom (x : ℂ)
      (gaussianCriterion_gaussianSeparatorPolynomial h U) ≠ 0 at hforwardComplex
    rw [hevalForward] at hforwardComplex
    exact Complex.ofReal_ne_zero.mp hforwardComplex
  have hbackward : (gaussianCriterion_gaussianSeparatorPolynomial h U).eval x⁻¹ ≠ 0 := by
    rw [gaussianCriterion_exp_ofReal_mul_real_center h hznegReal] at hbackwardComplex
    have harg : h * (-z).re = -(h * z.re) := by simp
    have hxneg : Real.exp (h * (-z).re) = x⁻¹ := by
      rw [harg, Real.exp_neg]
    rw [hxneg] at hbackwardComplex
    rw [hevalBackward] at hbackwardComplex
    exact Complex.ofReal_ne_zero.mp hbackwardComplex
  rw [gaussianCriterion_exp_ofReal_mul_real_center h hzreal,
    gaussianCriterion_exp_ofReal_mul_real_center h hznegReal]
  have harg : h * (-z).re = -(h * z.re) := by simp
  have hxneg : Real.exp (h * (-z).re) = x⁻¹ := by
    rw [harg, Real.exp_neg]
  rw [hxneg, hevalForward, hevalBackward]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  exact gaussianCriterion_real_eval_gaussianProtectedSeparatorPolynomial_product_neg
    h U hx hxone hforward hbackward

def gaussianCriterion_isGaussianTargetSquare (z0 z : ℂ) : Prop :=
  z ^ 2 = z0 ^ 2 ∨ z ^ 2 = (starRingEnd ℂ) (z0 ^ 2)

def gaussianCriterion_gaussianLowIndexFinset
    (p0 : RiemannXiDivisorZeroIndex) : Finset RiemannXiDivisorZeroIndex :=
  (gaussianCriterion_finite_gaussianDecayRate_le p0).toFinset

noncomputable def gaussianCriterion_gaussianUnwantedLowCenterFinset
    (p0 : RiemannXiDivisorZeroIndex) : Finset ℂ := by
  classical
  exact ((gaussianCriterion_gaussianLowIndexFinset p0).filter fun p =>
    ¬gaussianCriterion_isGaussianTargetSquare (gaussianCriterion_centeredXiDivisorZero p0)
      (gaussianCriterion_centeredXiDivisorZero p)).image gaussianCriterion_centeredXiDivisorZero

theorem gaussianCriterion_mem_gaussianUnwantedLowCenterFinset
    (p0 p : RiemannXiDivisorZeroIndex)
    (hrate : gaussianCriterion_gaussianDecayRate p ≤ gaussianCriterion_gaussianDecayRate p0)
    (htarget : ¬gaussianCriterion_isGaussianTargetSquare
      (gaussianCriterion_centeredXiDivisorZero p0) (gaussianCriterion_centeredXiDivisorZero p)) :
    gaussianCriterion_centeredXiDivisorZero p ∈
      gaussianCriterion_gaussianUnwantedLowCenterFinset p0 := by
  classical
  rw [gaussianCriterion_gaussianUnwantedLowCenterFinset]
  apply Finset.mem_image.mpr
  refine ⟨p, Finset.mem_filter.mpr ⟨?_, htarget⟩, rfl⟩
  rw [gaussianCriterion_gaussianLowIndexFinset,
    (gaussianCriterion_finite_gaussianDecayRate_le p0).mem_toFinset]
  exact hrate

theorem gaussianCriterion_mem_gaussianUnwantedLowCenterFinset_sq_ne
    (p0 : RiemannXiDivisorZeroIndex) {u : ℂ}
    (hu : u ∈ gaussianCriterion_gaussianUnwantedLowCenterFinset p0) :
    u ^ 2 ≠ gaussianCriterion_centeredXiDivisorZero p0 ^ 2 ∧
      u ^ 2 ≠ (starRingEnd ℂ) (gaussianCriterion_centeredXiDivisorZero p0 ^ 2) := by
  classical
  rw [gaussianCriterion_gaussianUnwantedLowCenterFinset] at hu
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hu
  exact not_or.mp (Finset.mem_filter.mp hp).2

theorem gaussianCriterion_targetSquare_not_mem_unwanted_union_stars
    (p0 : RiemannXiDivisorZeroIndex) {v : ℂ}
    (hv : gaussianCriterion_isGaussianTargetSquare
      (gaussianCriterion_centeredXiDivisorZero p0) v) :
    v ∉ gaussianCriterion_gaussianUnwantedLowCenterFinset p0 ∪
      (gaussianCriterion_gaussianUnwantedLowCenterFinset p0).image (starRingEnd ℂ) := by
  classical
  intro hmem
  rcases Finset.mem_union.mp hmem with hvU | hvStar
  · have hne := gaussianCriterion_mem_gaussianUnwantedLowCenterFinset_sq_ne p0 hvU
    exact hv.elim hne.1 hne.2
  · obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp hvStar
    have hne := gaussianCriterion_mem_gaussianUnwantedLowCenterFinset_sq_ne p0 hu
    have huEq : u = (starRingEnd ℂ) v := by
      calc
        u = (starRingEnd ℂ) ((starRingEnd ℂ) u) := by simp
        _ = (starRingEnd ℂ) v := by rw [huv]
    have husq : u ^ 2 = (starRingEnd ℂ) (v ^ 2) := by
      rw [huEq, map_pow]
    rcases hv with hv | hv
    · apply hne.2
      rw [husq, hv]
    · apply hne.1
      rw [husq, hv]
      simp

def gaussianCriterion_gaussianTargetSignFinset (z0 : ℂ) : Finset ℂ :=
  {z0, -z0}

theorem gaussianCriterion_gaussianTargetSignFinset_disjoint_unwanted_union_stars
    (p0 : RiemannXiDivisorZeroIndex) :
    Disjoint
      (gaussianCriterion_gaussianTargetSignFinset (gaussianCriterion_centeredXiDivisorZero p0))
      (gaussianCriterion_gaussianUnwantedLowCenterFinset p0 ∪
        (gaussianCriterion_gaussianUnwantedLowCenterFinset p0).image (starRingEnd ℂ)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hv hmem
  simp only [gaussianCriterion_gaussianTargetSignFinset, Finset.mem_insert,
    Finset.mem_singleton] at hv
  rcases hv with rfl | rfl
  · exact gaussianCriterion_targetSquare_not_mem_unwanted_union_stars p0 (Or.inl rfl) hmem
  · apply gaussianCriterion_targetSquare_not_mem_unwanted_union_stars p0 (Or.inl ?_) hmem
    ring

theorem gaussianCriterion_exists_gaussianUnwantedLowSeparator
    (p0 : RiemannXiDivisorZeroIndex) :
    ∃ h : ℝ, 0 < h ∧
      (∀ u ∈ gaussianCriterion_gaussianUnwantedLowCenterFinset p0,
        Complex.exp ((h : ℂ) * gaussianCriterion_centeredXiDivisorZero p0) ≠
            Complex.exp ((h : ℂ) * u) ∧
          Complex.exp ((h : ℂ) * gaussianCriterion_centeredXiDivisorZero p0) ≠
            (starRingEnd ℂ) (Complex.exp ((h : ℂ) * u))) ∧
      (∀ u ∈ gaussianCriterion_gaussianUnwantedLowCenterFinset p0,
        Complex.exp ((h : ℂ) * (-gaussianCriterion_centeredXiDivisorZero p0)) ≠
            Complex.exp ((h : ℂ) * u) ∧
          Complex.exp ((h : ℂ) * (-gaussianCriterion_centeredXiDivisorZero p0)) ≠
            (starRingEnd ℂ) (Complex.exp ((h : ℂ) * u))) := by
  classical
  let z0 := gaussianCriterion_centeredXiDivisorZero p0
  let U := gaussianCriterion_gaussianUnwantedLowCenterFinset p0
  obtain ⟨h, hh, hsep⟩ := gaussianCriterion_exists_pos_exp_mul_separates_finsets
    (gaussianCriterion_gaussianTargetSignFinset z0)
    (U ∪ U.image (starRingEnd ℂ))
    (gaussianCriterion_gaussianTargetSignFinset_disjoint_unwanted_union_stars p0)
  refine ⟨h, hh, ?_, ?_⟩
  · intro u hu
    constructor
    · exact hsep z0 (by simp [gaussianCriterion_gaussianTargetSignFinset]) u
        (Finset.mem_union_left _ hu)
    · rw [gaussianCriterion_star_exp_ofReal_mul]
      exact hsep z0 (by simp [gaussianCriterion_gaussianTargetSignFinset])
        ((starRingEnd ℂ) u)
        (Finset.mem_union_right U (Finset.mem_image.mpr ⟨u, hu, rfl⟩))
  · intro u hu
    constructor
    · exact hsep (-z0) (by simp [gaussianCriterion_gaussianTargetSignFinset]) u
        (Finset.mem_union_left _ hu)
    · rw [gaussianCriterion_star_exp_ofReal_mul]
      exact hsep (-z0) (by simp [gaussianCriterion_gaussianTargetSignFinset])
        ((starRingEnd ℂ) u)
        (Finset.mem_union_right U (Finset.mem_image.mpr ⟨u, hu, rfl⟩))

theorem gaussianCriterion_gaussianGeneratedPacket_eq_zero_of_unwanted_low
    (p0 p : RiemannXiDivisorZeroIndex) (h a : ℝ)
    (hrate : gaussianCriterion_gaussianDecayRate p ≤ gaussianCriterion_gaussianDecayRate p0)
    (htarget : ¬gaussianCriterion_isGaussianTargetSquare
      (gaussianCriterion_centeredXiDivisorZero p0) (gaussianCriterion_centeredXiDivisorZero p)) :
    gaussianCriterion_gaussianGeneratedPacket
      (gaussianCriterion_gaussianProtectedSeparatorPolynomial h
        (gaussianCriterion_gaussianUnwantedLowCenterFinset p0)) h a p = 0 := by
  let U := gaussianCriterion_gaussianUnwantedLowCenterFinset p0
  let Q := gaussianCriterion_gaussianProtectedSeparatorPolynomial h U
  have hpU : gaussianCriterion_centeredXiDivisorZero p ∈ U :=
    gaussianCriterion_mem_gaussianUnwantedLowCenterFinset p0 p hrate htarget
  have hzero :
      Polynomial.eval₂ Complex.ofRealHom
          (Complex.exp ((h : ℂ) *
            (riemannXiDivisorZeroValue p - 1 / 2)))
          (gaussianCriterion_gaussianProtectedSeparatorPolynomial h
            (gaussianCriterion_gaussianUnwantedLowCenterFinset p0)) = 0 := by
    simpa only [U, gaussianCriterion_centeredXiDivisorZero] using
      gaussianCriterion_eval₂_gaussianProtectedSeparatorPolynomial_eq_zero h U hpU
  rw [gaussianCriterion_gaussianGeneratedPacket,
    gaussianCriterion_gaussianWeilPacket_eq_exp_mul_exponentialSum,
    gaussianCriterion_exponentialSum_polynomialShift_coeff]
  rw [hzero]
  ring

theorem gaussianCriterion_star_gaussianWeilExponentialSum
    {ι : Type*} [Fintype ι] (b w : ι → ℝ) (z : ℂ) :
    (starRingEnd ℂ) (gaussianCriterion_gaussianWeilExponentialSum b w z) =
      gaussianCriterion_gaussianWeilExponentialSum b w ((starRingEnd ℂ) z) := by
  classical
  rw [gaussianCriterion_gaussianWeilExponentialSum, map_sum,
    gaussianCriterion_gaussianWeilExponentialSum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [map_mul, gaussianCriterion_star_exp_ofReal_mul]
  simp

def gaussianCriterion_gaussianPolynomialProduct (P : Polynomial ℝ) (h : ℝ) (z : ℂ) : ℂ :=
  gaussianCriterion_gaussianWeilExponentialSum
      (gaussianCriterion_polynomialShift P h) (gaussianCriterion_polynomialCoeff P) z *
    gaussianCriterion_gaussianWeilExponentialSum
      (gaussianCriterion_polynomialShift P h) (gaussianCriterion_polynomialCoeff P) (-z)

theorem gaussianCriterion_gaussianPolynomialProduct_neg
    (P : Polynomial ℝ) (h : ℝ) (z : ℂ) :
    gaussianCriterion_gaussianPolynomialProduct P h (-z) =
      gaussianCriterion_gaussianPolynomialProduct P h z := by
  rw [gaussianCriterion_gaussianPolynomialProduct, gaussianCriterion_gaussianPolynomialProduct]
  simp only [neg_neg]
  ring

theorem gaussianCriterion_gaussianPolynomialProduct_star
    (P : Polynomial ℝ) (h : ℝ) (z : ℂ) :
    gaussianCriterion_gaussianPolynomialProduct P h ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (gaussianCriterion_gaussianPolynomialProduct P h z) := by
  rw [gaussianCriterion_gaussianPolynomialProduct, gaussianCriterion_gaussianPolynomialProduct, map_mul]
  rw [gaussianCriterion_star_gaussianWeilExponentialSum,
    gaussianCriterion_star_gaussianWeilExponentialSum]
  simp

theorem gaussianCriterion_gaussianPolynomialProduct_targetSquare
    (P : Polynomial ℝ) (h : ℝ) {z0 z : ℂ}
    (hz : gaussianCriterion_isGaussianTargetSquare z0 z) :
    gaussianCriterion_gaussianPolynomialProduct P h z =
        gaussianCriterion_gaussianPolynomialProduct P h z0 ∨
      gaussianCriterion_gaussianPolynomialProduct P h z =
        (starRingEnd ℂ) (gaussianCriterion_gaussianPolynomialProduct P h z0) := by
  rcases hz with hz | hz
  · rcases eq_or_eq_neg_of_sq_eq_sq z z0 hz with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inl (gaussianCriterion_gaussianPolynomialProduct_neg P h z0)
  · have hstarSq : ((starRingEnd ℂ) z0) ^ 2 =
        (starRingEnd ℂ) (z0 ^ 2) := by rw [map_pow]
    rcases eq_or_eq_neg_of_sq_eq_sq z ((starRingEnd ℂ) z0)
        (hz.trans hstarSq.symm) with rfl | rfl
    · exact Or.inr (gaussianCriterion_gaussianPolynomialProduct_star P h z0)
    · exact Or.inr ((gaussianCriterion_gaussianPolynomialProduct_neg P h
        ((starRingEnd ℂ) z0)).trans
          (gaussianCriterion_gaussianPolynomialProduct_star P h z0))

theorem gaussianCriterion_gaussianGeneratedPacket_eq_exp_mul_polynomialProduct
    (P : Polynomial ℝ) (h a : ℝ) (p : RiemannXiDivisorZeroIndex) :
    gaussianCriterion_gaussianGeneratedPacket P h a p =
      Complex.exp ((a : ℂ) * gaussianCriterion_centeredXiDivisorZero p ^ 2) *
        gaussianCriterion_gaussianPolynomialProduct P h
          (gaussianCriterion_centeredXiDivisorZero p) := by
  rw [gaussianCriterion_gaussianGeneratedPacket,
    gaussianCriterion_gaussianWeilPacket_eq_exp_mul_exponentialSum]
  rw [gaussianCriterion_centeredXiDivisorZero, gaussianCriterion_gaussianPolynomialProduct]
  ring

theorem gaussianCriterion_scaled_complex_exp_eq_phase
    {q : ℝ} {s C : ℂ} (hq : q = -s.re) (a : ℝ) :
    (Real.exp (a * q) : ℂ) * Complex.exp ((a : ℂ) * s) * C =
      Complex.exp (((a * s.im : ℝ) : ℂ) * I) * C := by
  rw [show ((Real.exp (a * q) : ℝ) : ℂ) =
      Complex.exp ((a * q : ℝ) : ℂ) by rw [Complex.ofReal_exp]]
  rw [← Complex.exp_add]
  congr 2
  apply Complex.ext
  · simp [hq, Complex.mul_re]
  · simp [Complex.mul_im]

theorem gaussianCriterion_scaled_targetPacket_re_eq_phase
    (p0 p : RiemannXiDivisorZeroIndex) (P : Polynomial ℝ) (h a : ℝ)
    (htarget : gaussianCriterion_isGaussianTargetSquare
      (gaussianCriterion_centeredXiDivisorZero p0) (gaussianCriterion_centeredXiDivisorZero p)) :
    ((Real.exp (a * gaussianCriterion_gaussianDecayRate p0) : ℂ) *
        gaussianCriterion_gaussianGeneratedPacket P h a p).re =
      (Complex.exp (((a * (gaussianCriterion_centeredXiDivisorZero p0 ^ 2).im : ℝ) : ℂ) * I) *
        gaussianCriterion_gaussianPolynomialProduct P h
          (gaussianCriterion_centeredXiDivisorZero p0)).re := by
  let z0 := gaussianCriterion_centeredXiDivisorZero p0
  let z := gaussianCriterion_centeredXiDivisorZero p
  let C := gaussianCriterion_gaussianPolynomialProduct P h z0
  rw [gaussianCriterion_gaussianGeneratedPacket_eq_exp_mul_polynomialProduct]
  rcases htarget with htarget | htarget
  · have hprod : gaussianCriterion_gaussianPolynomialProduct P h z = C := by
      rcases eq_or_eq_neg_of_sq_eq_sq z z0 htarget with hz | hz
      · rw [hz]
      · rw [hz, gaussianCriterion_gaussianPolynomialProduct_neg]
    rw [show gaussianCriterion_centeredXiDivisorZero p ^ 2 = z0 ^ 2 from htarget,
      show gaussianCriterion_gaussianPolynomialProduct P h
        (gaussianCriterion_centeredXiDivisorZero p) = C from hprod]
    simpa only [z0, C, mul_assoc] using congrArg Complex.re
      (gaussianCriterion_scaled_complex_exp_eq_phase
        (q := gaussianCriterion_gaussianDecayRate p0) (s := z0 ^ 2) (C := C) rfl a)
  · have hstarSq : ((starRingEnd ℂ) z0) ^ 2 =
        (starRingEnd ℂ) (z0 ^ 2) := by rw [map_pow]
    have hprod : gaussianCriterion_gaussianPolynomialProduct P h z =
        (starRingEnd ℂ) C := by
      rcases eq_or_eq_neg_of_sq_eq_sq z ((starRingEnd ℂ) z0)
          (htarget.trans hstarSq.symm) with hz | hz
      · rw [hz, gaussianCriterion_gaussianPolynomialProduct_star]
      · rw [hz, gaussianCriterion_gaussianPolynomialProduct_neg,
          gaussianCriterion_gaussianPolynomialProduct_star]
    rw [show gaussianCriterion_centeredXiDivisorZero p ^ 2 =
        (starRingEnd ℂ) (z0 ^ 2) from htarget,
      show gaussianCriterion_gaussianPolynomialProduct P h
        (gaussianCriterion_centeredXiDivisorZero p) = (starRingEnd ℂ) C from hprod]
    calc
      (↑(Real.exp (a * gaussianCriterion_gaussianDecayRate p0)) *
          (Complex.exp (↑a * (starRingEnd ℂ) (z0 ^ 2)) *
            (starRingEnd ℂ) C)).re =
          (Complex.exp
              (((a * ((starRingEnd ℂ) (z0 ^ 2)).im : ℝ) : ℂ) * I) *
            (starRingEnd ℂ) C).re := by
        simpa only [mul_assoc] using congrArg Complex.re
          (gaussianCriterion_scaled_complex_exp_eq_phase
            (q := gaussianCriterion_gaussianDecayRate p0)
            (s := (starRingEnd ℂ) (z0 ^ 2)) (C := (starRingEnd ℂ) C)
            (by
              rw [gaussianCriterion_gaussianDecayRate]
              change -(z0 ^ 2).re = -((starRingEnd ℂ) (z0 ^ 2)).re
              rw [show ((starRingEnd ℂ) (z0 ^ 2)).re = (z0 ^ 2).re by
                exact Complex.conj_re (z0 ^ 2)]) a)
      _ = (Complex.exp (((a * (z0 ^ 2).im : ℝ) : ℂ) * I) * C).re := by
        rw [show
          Complex.exp
                (((a * ((starRingEnd ℂ) (z0 ^ 2)).im : ℝ) : ℂ) * I) *
              (starRingEnd ℂ) C =
            (starRingEnd ℂ)
              (Complex.exp (((a * (z0 ^ 2).im : ℝ) : ℂ) * I) * C) by
          have harg :
              (((a * ((starRingEnd ℂ) (z0 ^ 2)).im : ℝ) : ℂ) * I) =
                (starRingEnd ℂ) (((a * (z0 ^ 2).im : ℝ) : ℂ) * I) := by
            rw [show ((starRingEnd ℂ) (z0 ^ 2)).im = -(z0 ^ 2).im by
              exact Complex.conj_im (z0 ^ 2)]
            apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
          rw [map_mul]
          rw [← Complex.exp_conj]
          rw [harg]]
        simp
      _ = _ := by simp only [z0, C]

def gaussianCriterion_gaussianScaledLowSum
    (p0 : RiemannXiDivisorZeroIndex) (P : Polynomial ℝ) (h a : ℝ) : ℂ :=
  ∑ p ∈ gaussianCriterion_gaussianLowIndexFinset p0,
    (Real.exp (a * gaussianCriterion_gaussianDecayRate p0) : ℂ) *
      gaussianCriterion_gaussianGeneratedPacket P h a p

theorem gaussianCriterion_gaussianScaledLowSum_re_neg
    (p0 : RiemannXiDivisorZeroIndex) (P : Polynomial ℝ) (h a : ℝ)
    (hkill : ∀ p : RiemannXiDivisorZeroIndex,
      gaussianCriterion_gaussianDecayRate p ≤ gaussianCriterion_gaussianDecayRate p0 →
      ¬gaussianCriterion_isGaussianTargetSquare
          (gaussianCriterion_centeredXiDivisorZero p0) (gaussianCriterion_centeredXiDivisorZero p) →
        gaussianCriterion_gaussianGeneratedPacket P h a p = 0)
    (hphase :
      (Complex.exp
          (((a * (gaussianCriterion_centeredXiDivisorZero p0 ^ 2).im : ℝ) : ℂ) * I) *
        gaussianCriterion_gaussianPolynomialProduct P h
          (gaussianCriterion_centeredXiDivisorZero p0)).re < 0) :
    (gaussianCriterion_gaussianScaledLowSum p0 P h a).re < 0 := by
  classical
  let L := gaussianCriterion_gaussianLowIndexFinset p0
  let f : RiemannXiDivisorZeroIndex → ℝ := fun p =>
    ((Real.exp (a * gaussianCriterion_gaussianDecayRate p0) : ℂ) *
      gaussianCriterion_gaussianGeneratedPacket P h a p).re
  have hp0L : p0 ∈ L := by
    dsimp only [L]
    rw [gaussianCriterion_gaussianLowIndexFinset,
      (gaussianCriterion_finite_gaussianDecayRate_le p0).mem_toFinset]
    exact le_refl (gaussianCriterion_gaussianDecayRate p0)
  have hnonpos (p : RiemannXiDivisorZeroIndex) (hpL : p ∈ L) : f p ≤ 0 := by
    have hrate : gaussianCriterion_gaussianDecayRate p ≤ gaussianCriterion_gaussianDecayRate p0 := by
      dsimp only [L] at hpL
      rw [gaussianCriterion_gaussianLowIndexFinset,
        (gaussianCriterion_finite_gaussianDecayRate_le p0).mem_toFinset] at hpL
      exact hpL
    by_cases htarget : gaussianCriterion_isGaussianTargetSquare
        (gaussianCriterion_centeredXiDivisorZero p0) (gaussianCriterion_centeredXiDivisorZero p)
    · dsimp only [f]
      rw [gaussianCriterion_scaled_targetPacket_re_eq_phase p0 p P h a htarget]
      exact hphase.le
    · dsimp only [f]
      rw [hkill p hrate htarget]
      simp
  have hp0neg : f p0 < 0 := by
    dsimp only [f]
    rw [gaussianCriterion_scaled_targetPacket_re_eq_phase p0 p0 P h a (Or.inl rfl)]
    exact hphase
  have herase : ∑ p ∈ L.erase p0, f p ≤ 0 := by
    apply Finset.sum_nonpos
    intro p hp
    exact hnonpos p (Finset.mem_of_mem_erase hp)
  rw [gaussianCriterion_gaussianScaledLowSum]
  change Complex.reAddGroupHom
      (∑ p ∈ gaussianCriterion_gaussianLowIndexFinset p0,
        (Real.exp (a * gaussianCriterion_gaussianDecayRate p0) : ℂ) *
          gaussianCriterion_gaussianGeneratedPacket P h a p) < 0
  rw [map_sum]
  change ∑ p ∈ L, f p < 0
  rw [← L.sum_erase_add f hp0L]
  exact add_neg_of_nonpos_of_neg herase hp0neg

theorem gaussianCriterion_gaussianScaledLowSum_re_le_phase
    (p0 : RiemannXiDivisorZeroIndex) (P : Polynomial ℝ) (h a k : ℝ)
    (hkill : ∀ p : RiemannXiDivisorZeroIndex,
      gaussianCriterion_gaussianDecayRate p ≤ gaussianCriterion_gaussianDecayRate p0 →
      ¬gaussianCriterion_isGaussianTargetSquare
          (gaussianCriterion_centeredXiDivisorZero p0) (gaussianCriterion_centeredXiDivisorZero p) →
        gaussianCriterion_gaussianGeneratedPacket P h a p = 0)
    (hphase :
      (Complex.exp
          (((a * (gaussianCriterion_centeredXiDivisorZero p0 ^ 2).im : ℝ) : ℂ) * I) *
        gaussianCriterion_gaussianPolynomialProduct P h
          (gaussianCriterion_centeredXiDivisorZero p0)).re = k)
    (hk : k ≤ 0) :
    (gaussianCriterion_gaussianScaledLowSum p0 P h a).re ≤ k := by
  classical
  let L := gaussianCriterion_gaussianLowIndexFinset p0
  let f : RiemannXiDivisorZeroIndex → ℝ := fun p =>
    ((Real.exp (a * gaussianCriterion_gaussianDecayRate p0) : ℂ) *
      gaussianCriterion_gaussianGeneratedPacket P h a p).re
  have hp0L : p0 ∈ L := by
    dsimp only [L]
    rw [gaussianCriterion_gaussianLowIndexFinset,
      (gaussianCriterion_finite_gaussianDecayRate_le p0).mem_toFinset]
    exact le_refl (gaussianCriterion_gaussianDecayRate p0)
  have hnonpos (p : RiemannXiDivisorZeroIndex) (hpL : p ∈ L) : f p ≤ 0 := by
    have hrate : gaussianCriterion_gaussianDecayRate p ≤ gaussianCriterion_gaussianDecayRate p0 := by
      dsimp only [L] at hpL
      rw [gaussianCriterion_gaussianLowIndexFinset,
        (gaussianCriterion_finite_gaussianDecayRate_le p0).mem_toFinset] at hpL
      exact hpL
    by_cases htarget : gaussianCriterion_isGaussianTargetSquare
        (gaussianCriterion_centeredXiDivisorZero p0) (gaussianCriterion_centeredXiDivisorZero p)
    · dsimp only [f]
      rw [gaussianCriterion_scaled_targetPacket_re_eq_phase p0 p P h a htarget, hphase]
      exact hk
    · dsimp only [f]
      rw [hkill p hrate htarget]
      simp
  have hp0eq : f p0 = k := by
    dsimp only [f]
    rw [gaussianCriterion_scaled_targetPacket_re_eq_phase p0 p0 P h a (Or.inl rfl)]
    exact hphase
  have herase : ∑ p ∈ L.erase p0, f p ≤ 0 := by
    apply Finset.sum_nonpos
    intro p hp
    exact hnonpos p (Finset.mem_of_mem_erase hp)
  rw [gaussianCriterion_gaussianScaledLowSum]
  change Complex.reAddGroupHom
      (∑ p ∈ gaussianCriterion_gaussianLowIndexFinset p0,
        (Real.exp (a * gaussianCriterion_gaussianDecayRate p0) : ℂ) *
          gaussianCriterion_gaussianGeneratedPacket P h a p) ≤ k
  rw [map_sum]
  change ∑ p ∈ L, f p ≤ k
  rw [← L.sum_erase_add f hp0L, hp0eq]
  linarith

theorem gaussianCriterion_sum_toFinset_add_tsum_indicator_compl_eq_tsum
    {f : RiemannXiDivisorZeroIndex → ℂ} (hf : Summable f)
    {s : Set RiemannXiDivisorZeroIndex} (hs : s.Finite) :
    (∑ p ∈ hs.toFinset, f p) + ∑' p, sᶜ.indicator f p = ∑' p, f p := by
  rw [sum_eq_tsum_indicator]
  simp only [hs.coe_toFinset]
  rw [← (hf.indicator s).tsum_add (hf.indicator sᶜ)]
  apply tsum_congr
  intro p
  by_cases hp : p ∈ s <;> simp [hp]

theorem gaussianCriterion_gaussianScaledLow_add_higher_eq_tsum
    (p0 : RiemannXiDivisorZeroIndex) (P : Polynomial ℝ) (h a : ℝ) (ha : 0 < a) :
    gaussianCriterion_gaussianScaledLowSum p0 P h a +
        ∑' p : RiemannXiDivisorZeroIndex,
          gaussianCriterion_gaussianScaledHigherTerm
            (gaussianCriterion_gaussianDecayRate p0) P h a p =
      ∑' p : RiemannXiDivisorZeroIndex,
        (Real.exp (a * gaussianCriterion_gaussianDecayRate p0) : ℂ) *
          gaussianCriterion_gaussianGeneratedPacket P h a p := by
  let s : Set RiemannXiDivisorZeroIndex := {p |
    gaussianCriterion_gaussianDecayRate p ≤ gaussianCriterion_gaussianDecayRate p0}
  have hs : s.Finite := gaussianCriterion_finite_gaussianDecayRate_le p0
  have hpacket : Summable (gaussianCriterion_gaussianGeneratedPacket P h a) := by
    exact summable_riemannXiSymmetricGaussianPacketWeight
      (gaussianWeilPairWidth a)
      (gaussianWeilPairShift (gaussianCriterion_polynomialShift P h))
      (gaussianWeilPairCoeff (gaussianCriterion_polynomialCoeff P))
      (fun _ => by simpa only [gaussianWeilPairWidth] using ha)
  have hscaled : Summable (fun p : RiemannXiDivisorZeroIndex =>
      (Real.exp (a * gaussianCriterion_gaussianDecayRate p0) : ℂ) *
        gaussianCriterion_gaussianGeneratedPacket P h a p) :=
    Summable.mul_left _ hpacket
  have hsplit := gaussianCriterion_sum_toFinset_add_tsum_indicator_compl_eq_tsum hscaled hs
  rw [← hsplit]
  apply congrArg₂ (· + ·)
  · rw [gaussianCriterion_gaussianScaledLowSum]
    apply Finset.sum_congr
    · exact congrArg Set.Finite.toFinset rfl
    · intro p _hp
      rfl
  · apply tsum_congr
    intro p
    by_cases hp : gaussianCriterion_gaussianDecayRate p ≤ gaussianCriterion_gaussianDecayRate p0
    · simp [gaussianCriterion_gaussianScaledHigherTerm, hp, s]
    · have hp' : gaussianCriterion_gaussianDecayRate p0 < gaussianCriterion_gaussianDecayRate p :=
        lt_of_not_ge hp
      simp [gaussianCriterion_gaussianScaledHigherTerm, hp, hp', s]

theorem gaussianCriterion_exists_pos_tsum_gaussianGeneratedPacket_re_neg_of_phase_locked
    (p0 : RiemannXiDivisorZeroIndex) (P : Polynomial ℝ) (h : ℝ)
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
    ∃ a : ℝ, 0 < a ∧
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
  have hevent : ∀ᶠ n : ℕ in atTop,
      0 < A n ∧
        (∑' p : RiemannXiDivisorZeroIndex,
          gaussianCriterion_gaussianGeneratedPacket P h (A n) p).re < 0 := by
    filter_upwards [hApos, htailSmall] with n hnpos hntail
    refine ⟨hnpos, ?_⟩
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
  exact ⟨A n, hn.1, hn.2⟩

theorem gaussianCriterion_centeredXiDivisorZero_re_ne_zero
    (p : RiemannXiDivisorZeroIndex)
    (hp : (riemannXiDivisorZeroValue p).re ≠ 1 / 2) :
    (gaussianCriterion_centeredXiDivisorZero p).re ≠ 0 := by
  simpa [gaussianCriterion_centeredXiDivisorZero, sub_ne_zero] using hp

theorem gaussianCriterion_im_eq_zero_of_sq_im_eq_zero_of_re_ne_zero
    {z : ℂ} (hzre : z.re ≠ 0) (hzsq : (z ^ 2).im = 0) :
    z.im = 0 := by
  have hprod : z.re * z.im = 0 := by
    simp only [pow_two, Complex.mul_im] at hzsq
    linarith
  exact (mul_eq_zero.mp hprod).resolve_left hzre

theorem gaussianCriterion_gaussianSelectedPolynomialProduct_ne_zero
    (p0 : RiemannXiDivisorZeroIndex)
    (hp0 : (riemannXiDivisorZeroValue p0).re ≠ 1 / 2)
    {h : ℝ} (hh : 0 < h)
    (hsepForward : ∀ u ∈ gaussianCriterion_gaussianUnwantedLowCenterFinset p0,
      Complex.exp ((h : ℂ) * gaussianCriterion_centeredXiDivisorZero p0) ≠
          Complex.exp ((h : ℂ) * u) ∧
        Complex.exp ((h : ℂ) * gaussianCriterion_centeredXiDivisorZero p0) ≠
          (starRingEnd ℂ) (Complex.exp ((h : ℂ) * u)))
    (hsepBackward : ∀ u ∈ gaussianCriterion_gaussianUnwantedLowCenterFinset p0,
      Complex.exp ((h : ℂ) * (-gaussianCriterion_centeredXiDivisorZero p0)) ≠
          Complex.exp ((h : ℂ) * u) ∧
        Complex.exp ((h : ℂ) * (-gaussianCriterion_centeredXiDivisorZero p0)) ≠
          (starRingEnd ℂ) (Complex.exp ((h : ℂ) * u))) :
    gaussianCriterion_gaussianPolynomialProduct
        (gaussianCriterion_gaussianProtectedSeparatorPolynomial h
          (gaussianCriterion_gaussianUnwantedLowCenterFinset p0)) h
        (gaussianCriterion_centeredXiDivisorZero p0) ≠ 0 := by
  let U := gaussianCriterion_gaussianUnwantedLowCenterFinset p0
  let z0 := gaussianCriterion_centeredXiDivisorZero p0
  have hz0re : z0.re ≠ 0 := gaussianCriterion_centeredXiDivisorZero_re_ne_zero p0 hp0
  have hnegRe : (-z0).re ≠ 0 := by simpa using hz0re
  rw [gaussianCriterion_gaussianPolynomialProduct,
    gaussianCriterion_exponentialSum_polynomialShift_coeff,
    gaussianCriterion_exponentialSum_polynomialShift_coeff]
  exact mul_ne_zero
    (gaussianCriterion_eval₂_gaussianProtectedSeparatorPolynomial_ne_zero
      hh U hz0re hsepForward)
    (gaussianCriterion_eval₂_gaussianProtectedSeparatorPolynomial_ne_zero
      hh U hnegRe hsepBackward)

theorem gaussianCriterion_gaussianSelectedPolynomialProduct_re_neg_of_sq_im_zero
    (p0 : RiemannXiDivisorZeroIndex)
    (hp0 : (riemannXiDivisorZeroValue p0).re ≠ 1 / 2)
    {h : ℝ} (hh : 0 < h)
    (hsepForward : ∀ u ∈ gaussianCriterion_gaussianUnwantedLowCenterFinset p0,
      Complex.exp ((h : ℂ) * gaussianCriterion_centeredXiDivisorZero p0) ≠
          Complex.exp ((h : ℂ) * u) ∧
        Complex.exp ((h : ℂ) * gaussianCriterion_centeredXiDivisorZero p0) ≠
          (starRingEnd ℂ) (Complex.exp ((h : ℂ) * u)))
    (hsepBackward : ∀ u ∈ gaussianCriterion_gaussianUnwantedLowCenterFinset p0,
      Complex.exp ((h : ℂ) * (-gaussianCriterion_centeredXiDivisorZero p0)) ≠
          Complex.exp ((h : ℂ) * u) ∧
        Complex.exp ((h : ℂ) * (-gaussianCriterion_centeredXiDivisorZero p0)) ≠
          (starRingEnd ℂ) (Complex.exp ((h : ℂ) * u)))
    (hsq : (gaussianCriterion_centeredXiDivisorZero p0 ^ 2).im = 0) :
    (gaussianCriterion_gaussianPolynomialProduct
        (gaussianCriterion_gaussianProtectedSeparatorPolynomial h
          (gaussianCriterion_gaussianUnwantedLowCenterFinset p0)) h
        (gaussianCriterion_centeredXiDivisorZero p0)).re < 0 := by
  let U := gaussianCriterion_gaussianUnwantedLowCenterFinset p0
  let z0 := gaussianCriterion_centeredXiDivisorZero p0
  have hz0re : z0.re ≠ 0 := gaussianCriterion_centeredXiDivisorZero_re_ne_zero p0 hp0
  have hz0real : z0.im = 0 :=
    gaussianCriterion_im_eq_zero_of_sq_im_eq_zero_of_re_ne_zero hz0re hsq
  rw [gaussianCriterion_gaussianPolynomialProduct,
    gaussianCriterion_exponentialSum_polynomialShift_coeff,
    gaussianCriterion_exponentialSum_polynomialShift_coeff]
  exact gaussianCriterion_eval₂_gaussianProtectedSeparatorPolynomial_product_re_neg_of_real
    hh U hz0real hz0re hsepForward hsepBackward

theorem gaussianCriterion_exists_pos_tsum_gaussianGeneratedPacket_re_neg_of_offLine
    (p0 : RiemannXiDivisorZeroIndex)
    (hp0 : (riemannXiDivisorZeroValue p0).re ≠ 1 / 2) :
    ∃ (h a : ℝ), 0 < h ∧ 0 < a ∧
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
    obtain ⟨a, ha, hneg⟩ :=
      gaussianCriterion_exists_pos_tsum_gaussianGeneratedPacket_re_neg_of_phase_locked
        p0 P h hkill hCneg hA hphase
    exact ⟨h, a, hh, ha, hneg⟩
  · obtain ⟨A, hA, hphase⟩ :=
      gaussianCriterion_exists_phase_locked_widths htheta C
    have hk : -‖C‖ < 0 := neg_lt_zero.mpr (norm_pos_iff.mpr hCne)
    obtain ⟨a, ha, hneg⟩ :=
      gaussianCriterion_exists_pos_tsum_gaussianGeneratedPacket_re_neg_of_phase_locked
        p0 P h hkill hk hA hphase
    exact ⟨h, a, hh, ha, hneg⟩

theorem gaussianCriterion_gaussianXiZeroQuadratic_eq_tsum_generatedPacket
    (P : Polynomial ℝ) (h a : ℝ) :
    gaussianXiZeroQuadratic a
        (gaussianCriterion_polynomialShift P h) (gaussianCriterion_polynomialCoeff P) =
      ∑' p : RiemannXiDivisorZeroIndex,
        gaussianCriterion_gaussianGeneratedPacket P h a p := by
  rfl

theorem gaussianCriterion_exists_pos_gaussianXiArithmeticQuadratic_re_neg_of_offLine
    (p0 : RiemannXiDivisorZeroIndex)
    (hp0 : (riemannXiDivisorZeroValue p0).re ≠ 1 / 2) :
    ∃ (h a : ℝ), 0 < h ∧ 0 < a ∧
      (gaussianXiArithmeticQuadratic a
        (gaussianCriterion_polynomialShift
          (gaussianCriterion_gaussianProtectedSeparatorPolynomial h
            (gaussianCriterion_gaussianUnwantedLowCenterFinset p0)) h)
        (gaussianCriterion_polynomialCoeff
          (gaussianCriterion_gaussianProtectedSeparatorPolynomial h
            (gaussianCriterion_gaussianUnwantedLowCenterFinset p0))) 2).re < 0 := by
  obtain ⟨h, a, hh, ha, hzeroNeg⟩ :=
    gaussianCriterion_exists_pos_tsum_gaussianGeneratedPacket_re_neg_of_offLine p0 hp0
  let P := gaussianCriterion_gaussianProtectedSeparatorPolynomial h
    (gaussianCriterion_gaussianUnwantedLowCenterFinset p0)
  let b := gaussianCriterion_polynomialShift P h
  let w := gaussianCriterion_polynomialCoeff P
  have hzero : (gaussianXiZeroQuadratic a b w).re < 0 := by
    rw [gaussianCriterion_gaussianXiZeroQuadratic_eq_tsum_generatedPacket]
    exact hzeroNeg
  have hformula := gaussianXiZeroQuadratic_arithmetic_formula
    (c := 2) ha (by norm_num) b w
  refine ⟨h, a, hh, ha, ?_⟩
  change (gaussianXiArithmeticQuadratic a b w 2).re < 0
  rw [← hformula]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  exact mul_neg_of_pos_of_neg Real.pi_pos hzero

theorem riemannHypothesis_of_gaussianXiArithmeticQuadratic_re_nonneg
    (hpos : ∀ (ι : Type) [Fintype ι] {a : ℝ}, 0 < a →
      ∀ b w : ι → ℝ,
        0 ≤ (gaussianXiArithmeticQuadratic a b w 2).re) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_nontrivial_zeros_on_line]
  intro rho hrho
  rw [OnCriticalLine]
  obtain ⟨p, hp⟩ := exists_riemannXiDivisorZeroIndex_of_isNontrivialZero hrho
  by_contra hline
  have hpOff : (riemannXiDivisorZeroValue p).re ≠ 1 / 2 := by
    simpa only [hp] using hline
  obtain ⟨h, a, _hh, ha, hneg⟩ :=
    gaussianCriterion_exists_pos_gaussianXiArithmeticQuadratic_re_neg_of_offLine p hpOff
  let P := gaussianCriterion_gaussianProtectedSeparatorPolynomial h
    (gaussianCriterion_gaussianUnwantedLowCenterFinset p)
  exact (not_lt_of_ge
    (hpos (↥(Finset.range (P.natDegree + 1))) ha
      (gaussianCriterion_polynomialShift P h) (gaussianCriterion_polynomialCoeff P))) hneg

theorem riemannHypothesis_iff_gaussianXiArithmeticQuadratic_re_nonneg :
    RiemannHypothesis ↔
      ∀ (ι : Type) [Fintype ι] {a : ℝ}, 0 < a →
        ∀ b w : ι → ℝ,
          0 ≤ (gaussianXiArithmeticQuadratic a b w 2).re := by
  constructor
  · intro hRH ι _inst a ha b w
    exact RiemannHypothesis.gaussianXiArithmeticQuadratic_re_nonneg
      hRH ha (by norm_num) b w
  · exact riemannHypothesis_of_gaussianXiArithmeticQuadratic_re_nonneg

end

end LeanLab.Riemann
