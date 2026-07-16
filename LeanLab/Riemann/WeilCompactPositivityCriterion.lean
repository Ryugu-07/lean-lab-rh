import LeanLab.Riemann.WeilCompactLaplaceArithmeticFormula

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Compact Weil positivity criterion

This module assembles the compact-support Weil criterion on the additive logarithmic line.  The
conjugate involution below is the additive form of `g^*(u) = u^-1 * conj (g (u^-1))`.
-/

open Complex Filter Function MeasureTheory Set Topology
open scoped BigOperators ContDiff Convolution Topology

namespace LeanLab.Riemann

noncomputable section

/-- The project xi function is real with respect to complex conjugation. -/
@[simp] theorem riemannXi_conj (s : ℂ) :
    riemannXi ((starRingEnd ℂ) s) = (starRingEnd ℂ) (riemannXi s) := by
  rw [riemannXi, riemannXi, completedRiemannZeta₀_conj]
  simp only [map_add, map_mul, map_sub, map_div₀, map_one, map_ofNat]

/-- Nontrivial xi zeros are closed under complex conjugation. -/
theorem isNontrivialZero_conj {s : ℂ} (hs : IsNontrivialZero s) :
    IsNontrivialZero ((starRingEnd ℂ) s) := by
  rw [isNontrivialZero_iff_riemannXi_eq_zero, riemannXi_conj]
  simp [(isNontrivialZero_iff_riemannXi_eq_zero s).mp hs]

/-- Nontrivial xi zeros are closed under conjugate reflection. -/
theorem isNontrivialZero_one_sub_conj {s : ℂ} (hs : IsNontrivialZero s) :
    IsNontrivialZero (1 - (starRingEnd ℂ) s) := by
  rw [isNontrivialZero_iff_riemannXi_eq_zero, riemannXi_one_sub, riemannXi_conj]
  simp [(isNontrivialZero_iff_riemannXi_eq_zero s).mp hs]

/-- Additive-log form of the Mellin conjugate involution. -/
def compactLaplaceConjInvolution (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  (Real.exp (-x) : ℂ) * (starRingEnd ℂ) (g (-x))

theorem contDiff_compactLaplaceConjInvolution {g : ℝ → ℂ} {n : ℕ∞ω}
    (hg : ContDiff ℝ n g) :
    ContDiff ℝ n (compactLaplaceConjInvolution g) := by
  unfold compactLaplaceConjInvolution
  apply ContDiff.mul
  · exact Complex.ofRealCLM.contDiff.comp
      (Real.contDiff_exp.comp contDiff_id.neg)
  · exact Complex.conjCLE.contDiff.comp (hg.comp contDiff_id.neg)

theorem hasCompactSupport_compactLaplaceConjInvolution {g : ℝ → ℂ}
    (hgsupp : HasCompactSupport g) :
    HasCompactSupport (compactLaplaceConjInvolution g) := by
  have hneg : HasCompactSupport (fun x : ℝ ↦ g (-x)) := by
    simpa [Function.comp_def] using
      hgsupp.comp_homeomorph (Homeomorph.neg ℝ)
  have hconj : HasCompactSupport (fun x : ℝ ↦ (starRingEnd ℂ) (g (-x))) := by
    simpa [Function.comp_def] using hneg.comp_left (map_zero (starRingEnd ℂ))
  exact hconj.mul_left

theorem compactLaplaceTransform_conjInvolution (g : ℝ → ℂ) (s : ℂ) :
    compactLaplaceTransform (compactLaplaceConjInvolution g) s =
      (starRingEnd ℂ) (compactLaplaceTransform g (1 - (starRingEnd ℂ) s)) := by
  simp only [compactLaplaceTransform, compactLaplaceConjInvolution]
  rw [← integral_neg_eq_self, ← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  simp only [neg_neg, Complex.ofReal_exp, map_mul, ← Complex.exp_conj]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  simp
  ring

theorem compactLaplaceTransform_sub {f g : ℝ → ℂ} (s : ℂ)
    (hf : Integrable (fun x : ℝ ↦ Complex.exp (s * (x : ℂ)) * f x))
    (hg : Integrable (fun x : ℝ ↦ Complex.exp (s * (x : ℂ)) * g x)) :
    compactLaplaceTransform (fun x ↦ f x - g x) s =
      compactLaplaceTransform f s - compactLaplaceTransform g s := by
  simp only [compactLaplaceTransform, mul_sub]
  exact integral_sub hf hg

/-- Additive convolution square attached to a compact Weil test function. -/
def compactLaplaceAutocorrelation (g : ℝ → ℂ) : ℝ → ℂ :=
  additiveConvolution g (compactLaplaceConjInvolution g)

theorem contDiff_compactLaplaceAutocorrelation {g : ℝ → ℂ}
    (hg : ContDiff ℝ ∞ g) (hgsupp : HasCompactSupport g) :
    ContDiff ℝ ∞ (compactLaplaceAutocorrelation g) := by
  unfold compactLaplaceAutocorrelation
  exact hgsupp.contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℂ) hg
    (contDiff_compactLaplaceConjInvolution hg).continuous.locallyIntegrable

theorem hasCompactSupport_compactLaplaceAutocorrelation {g : ℝ → ℂ}
    (hgsupp : HasCompactSupport g) :
    HasCompactSupport (compactLaplaceAutocorrelation g) := by
  unfold compactLaplaceAutocorrelation
  exact hgsupp.convolution (ContinuousLinearMap.mul ℝ ℂ)
    (hasCompactSupport_compactLaplaceConjInvolution hgsupp)

theorem compactLaplaceTransform_autocorrelation {g : ℝ → ℂ}
    (hg : ContDiff ℝ ∞ g) (hgsupp : HasCompactSupport g) (s : ℂ) :
    compactLaplaceTransform (compactLaplaceAutocorrelation g) s =
      compactLaplaceTransform g s *
        (starRingEnd ℂ) (compactLaplaceTransform g (1 - (starRingEnd ℂ) s)) := by
  rw [compactLaplaceAutocorrelation,
    compactLaplaceTransform_additiveConvolution s
      (integrable_compactLaplaceKernel hg.continuous hgsupp s)
      (integrable_compactLaplaceKernel
        (contDiff_compactLaplaceConjInvolution hg).continuous
        (hasCompactSupport_compactLaplaceConjInvolution hgsupp) s),
    compactLaplaceTransform_conjInvolution]

/-- The complete compact arithmetic Weil quadratic, evaluated on an autocorrelation. -/
def compactWeilArithmeticQuadratic (g : ℝ → ℂ) : ℂ :=
  compactSymmetrizedXiArchimedeanIntegral (compactLaplaceAutocorrelation g) 2 -
    ∑' n : ℕ, compactSymmetrizedVonMangoldtWeight
      (compactLaplaceAutocorrelation g) n

/-- The complete multiplicity-bearing xi-zero quadratic attached to an autocorrelation. -/
def compactWeilZeroQuadratic (g : ℝ → ℂ) : ℂ :=
  ∑' p : RiemannXiDivisorZeroIndex,
    symmetrizedCompactLaplaceWeight (compactLaplaceAutocorrelation g)
      (riemannXiDivisorZeroValue p)

/-- The unsymmetrized autocorrelation sum; divisor reflection makes it equal the symmetrized sum. -/
def compactWeilRawZeroQuadratic (g : ℝ → ℂ) : ℂ :=
  ∑' p : RiemannXiDivisorZeroIndex,
    compactLaplaceTransform (compactLaplaceAutocorrelation g)
      (riemannXiDivisorZeroValue p)

/-- A compact-support mass which bounds a bilateral Laplace transform throughout the closed xi
strip. -/
def compactLaplaceStripMass (g : ℝ → ℂ) : ℝ :=
  ∫ x : ℝ, Real.exp |x| * ‖g x‖

theorem integrable_compactLaplaceStripMajorant {g : ℝ → ℂ}
    (hg : Continuous g) (hgsupp : HasCompactSupport g) :
    Integrable (fun x : ℝ ↦ Real.exp |x| * ‖g x‖) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (Real.continuous_exp.comp continuous_abs).mul hg.norm
  · exact hgsupp.norm.mul_left

theorem compactLaplaceStripMass_nonneg (g : ℝ → ℂ) :
    0 ≤ compactLaplaceStripMass g := by
  apply integral_nonneg
  intro x
  positivity

theorem norm_compactLaplaceTransform_le_stripMass {g : ℝ → ℂ}
    (hg : Continuous g) (hgsupp : HasCompactSupport g)
    {s : ℂ} (hre0 : 0 ≤ s.re) (hre1 : s.re ≤ 1) :
    ‖compactLaplaceTransform g s‖ ≤ compactLaplaceStripMass g := by
  apply norm_integral_le_of_norm_le
    (integrable_compactLaplaceStripMajorant hg hgsupp)
  filter_upwards with x
  exact norm_compactLaplaceKernel_le_exp_abs_mul hre0 hre1 x

theorem compactWeilZeroQuadratic_eq_rawZeroQuadratic
    {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hgsupp : HasCompactSupport g) :
    compactWeilZeroQuadratic g = compactWeilRawZeroQuadratic g := by
  let H : ℂ → ℂ := fun s ↦
    compactLaplaceTransform (compactLaplaceAutocorrelation g) s
  have hautoSmooth := contDiff_compactLaplaceAutocorrelation hg hgsupp
  have hautoSupp := hasCompactSupport_compactLaplaceAutocorrelation hgsupp
  have hsum : Summable (fun p : RiemannXiDivisorZeroIndex ↦
      H (riemannXiDivisorZeroValue p)) := by
    exact (summable_norm_compactLaplaceTransform_xiDivisorZero
      (hautoSmooth.of_le
        (WithTop.coe_le_coe.mpr (OrderTop.le_top (2 : ℕ∞)))) hautoSupp).of_norm
  have hreflect : Summable (fun p : RiemannXiDivisorZeroIndex ↦
      H (1 - riemannXiDivisorZeroValue p)) := by
    simpa only [H] using summable_compactLaplaceTransform_one_sub_xiDivisorZero
      (hautoSmooth.of_le
        (WithTop.coe_le_coe.mpr (OrderTop.le_top (2 : ℕ∞)))) hautoSupp
  have hreflectTsum :
      (∑' p : RiemannXiDivisorZeroIndex,
        H (1 - riemannXiDivisorZeroValue p)) =
      ∑' p : RiemannXiDivisorZeroIndex, H (riemannXiDivisorZeroValue p) := by
    simpa only [riemannXiDivisorZeroReflectEquiv_apply,
      riemannXiDivisorZeroValue_reflect] using
        (riemannXiDivisorZeroReflectEquiv.tsum_eq
          (fun p : RiemannXiDivisorZeroIndex ↦ H (riemannXiDivisorZeroValue p)))
  unfold compactWeilZeroQuadratic compactWeilRawZeroQuadratic
    symmetrizedCompactLaplaceWeight
  change (∑' p : RiemannXiDivisorZeroIndex,
      (H (riemannXiDivisorZeroValue p) +
        H (1 - riemannXiDivisorZeroValue p)) / 2) =
    ∑' p : RiemannXiDivisorZeroIndex, H (riemannXiDivisorZeroValue p)
  rw [tsum_div_const, hsum.tsum_add hreflect, hreflectTsum]
  ring

theorem symmetrizedCompactLaplaceWeight_autocorrelation_one_eq_zero
    {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hgsupp : HasCompactSupport g)
    (hzero : compactLaplaceTransform g 0 = 0)
    (hone : compactLaplaceTransform g 1 = 0) :
    symmetrizedCompactLaplaceWeight (compactLaplaceAutocorrelation g) 1 = 0 := by
  unfold symmetrizedCompactLaplaceWeight
  rw [compactLaplaceTransform_autocorrelation hg hgsupp,
    compactLaplaceTransform_autocorrelation hg hgsupp]
  simp [hzero, hone]

/-- With the two endpoint moments removed, the compact explicit formula is exactly the arithmetic
quadratic/zero-quadratic identity. -/
theorem compactWeilArithmeticQuadratic_eq_pi_mul_zeroQuadratic
    {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hgsupp : HasCompactSupport g)
    (hzero : compactLaplaceTransform g 0 = 0)
    (hone : compactLaplaceTransform g 1 = 0) :
    compactWeilArithmeticQuadratic g =
      (Real.pi : ℂ) * compactWeilZeroQuadratic g := by
  have hformula := symmetrizedCompactLaplaceXi_arithmetic_explicit_formula
    (contDiff_compactLaplaceAutocorrelation hg hgsupp)
    (hasCompactSupport_compactLaplaceAutocorrelation hgsupp)
    (c := 2) (by norm_num : (1 : ℝ) < 2)
  have hpole := symmetrizedCompactLaplaceWeight_autocorrelation_one_eq_zero
    hg hgsupp hzero hone
  simpa [compactWeilArithmeticQuadratic, compactWeilZeroQuadratic, hpole] using hformula.symm

theorem RiemannHypothesis.compactLaplaceTransform_autocorrelation_xiZero_eq_normSq
    (hRH : RiemannHypothesis) {g : ℝ → ℂ}
    (hg : ContDiff ℝ ∞ g) (hgsupp : HasCompactSupport g)
    (p : RiemannXiDivisorZeroIndex) :
    compactLaplaceTransform (compactLaplaceAutocorrelation g)
        (riemannXiDivisorZeroValue p) =
      (Complex.normSq (compactLaplaceTransform g
        (riemannXiDivisorZeroValue p)) : ℂ) := by
  have hreflect :=
    RiemannHypothesis.one_sub_riemannXiDivisorZeroValue_eq_conj hRH p
  have hcritical :
      1 - (starRingEnd ℂ) (riemannXiDivisorZeroValue p) =
        riemannXiDivisorZeroValue p := by
    calc
      1 - (starRingEnd ℂ) (riemannXiDivisorZeroValue p) =
          (starRingEnd ℂ) (1 - riemannXiDivisorZeroValue p) := by simp
      _ = (starRingEnd ℂ) ((starRingEnd ℂ) (riemannXiDivisorZeroValue p)) := by
        rw [hreflect]
      _ = riemannXiDivisorZeroValue p := by simp
  rw [compactLaplaceTransform_autocorrelation hg hgsupp, hcritical,
    Complex.mul_conj]

theorem RiemannHypothesis.symmetrizedCompactLaplaceWeight_autocorrelation_re_nonneg
    (hRH : RiemannHypothesis) {g : ℝ → ℂ}
    (hg : ContDiff ℝ ∞ g) (hgsupp : HasCompactSupport g)
    (p : RiemannXiDivisorZeroIndex) :
    0 ≤ (symmetrizedCompactLaplaceWeight (compactLaplaceAutocorrelation g)
      (riemannXiDivisorZeroValue p)).re := by
  have hfirst :=
    RiemannHypothesis.compactLaplaceTransform_autocorrelation_xiZero_eq_normSq
      hRH hg hgsupp p
  have hsecond :=
    RiemannHypothesis.compactLaplaceTransform_autocorrelation_xiZero_eq_normSq
      hRH hg hgsupp (riemannXiDivisorZeroReflectEquiv p)
  have hsecond' :
      compactLaplaceTransform (compactLaplaceAutocorrelation g)
          (1 - riemannXiDivisorZeroValue p) =
        (Complex.normSq (compactLaplaceTransform g
          (1 - riemannXiDivisorZeroValue p)) : ℂ) := by
    simpa only [riemannXiDivisorZeroReflectEquiv_apply,
      riemannXiDivisorZeroValue_reflect] using hsecond
  unfold symmetrizedCompactLaplaceWeight
  rw [hfirst, hsecond']
  simp only [Complex.add_re, Complex.div_re, Complex.ofReal_re]
  norm_num
  nlinarith [Complex.normSq_nonneg
      (compactLaplaceTransform g (riemannXiDivisorZeroValue p)),
    Complex.normSq_nonneg
      (compactLaplaceTransform g (1 - riemannXiDivisorZeroValue p))]

theorem RiemannHypothesis.compactWeilZeroQuadratic_re_nonneg
    (hRH : RiemannHypothesis) {g : ℝ → ℂ}
    (hg : ContDiff ℝ ∞ g) (hgsupp : HasCompactSupport g) :
    0 ≤ (compactWeilZeroQuadratic g).re := by
  have hsum : Summable (fun p : RiemannXiDivisorZeroIndex ↦
      symmetrizedCompactLaplaceWeight (compactLaplaceAutocorrelation g)
        (riemannXiDivisorZeroValue p)) := by
    apply summable_symmetrizedCompactLaplaceWeight_xiDivisorZero
    · exact (contDiff_compactLaplaceAutocorrelation hg hgsupp).of_le
        (WithTop.coe_le_coe.mpr (OrderTop.le_top (2 : ℕ∞)))
    · exact hasCompactSupport_compactLaplaceAutocorrelation hgsupp
  rw [compactWeilZeroQuadratic, Complex.re_tsum hsum]
  exact tsum_nonneg fun p ↦
    RiemannHypothesis.symmetrizedCompactLaplaceWeight_autocorrelation_re_nonneg
      hRH hg hgsupp p

theorem RiemannHypothesis.compactWeilArithmeticQuadratic_re_nonneg
    (hRH : RiemannHypothesis) {g : ℝ → ℂ}
    (hg : ContDiff ℝ ∞ g) (hgsupp : HasCompactSupport g)
    (hzero : compactLaplaceTransform g 0 = 0)
    (hone : compactLaplaceTransform g 1 = 0) :
    0 ≤ (compactWeilArithmeticQuadratic g).re := by
  rw [compactWeilArithmeticQuadratic_eq_pi_mul_zeroQuadratic
    hg hgsupp hzero hone]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg Real.pi_pos.le
    (RiemannHypothesis.compactWeilZeroQuadratic_re_nonneg hRH hg hgsupp)

theorem RiemannHypothesis.compactWeilArithmeticQuadratic_re_nonneg_of_vanishesOn
    (hRH : RiemannHypothesis) (F : Finset ℂ) (hzero : 0 ∈ F) (hone : 1 ∈ F) :
    ∀ g : ℝ → ℂ,
      ContDiff ℝ ∞ g →
      HasCompactSupport g →
      (∀ z ∈ F, compactLaplaceTransform g z = 0) →
      0 ≤ (compactWeilArithmeticQuadratic g).re := by
  intro g hg hgsupp hvanish
  exact RiemannHypothesis.compactWeilArithmeticQuadratic_re_nonneg
    hRH hg hgsupp (hvanish 0 hzero) (hvanish 1 hone)

/-- Normalized separator data with an additional finite set of exact transform zeros. -/
theorem exists_compactLaplaceNormalizedSeparatorData_vanishesOn
    (p0 : RiemannXiDivisorZeroIndex) (V : Finset ℂ)
    (hp0V : riemannXiDivisorZeroValue p0 ∉ V) :
    ∃ h : ℝ, ∃ P : Polynomial ℂ,
      0 < h ∧
      Polynomial.eval
        (Complex.exp ((h : ℂ) * riemannXiDivisorZeroValue p0)) P = 1 ∧
      (∀ z ∈ V,
        Polynomial.eval (Complex.exp ((h : ℂ) * z)) P = 0) ∧
      ∀ p : RiemannXiDivisorZeroIndex,
        riemannXiDivisorZeroValue p ≠ riemannXiDivisorZeroValue p0 →
        (1 / 2 : ℝ) ≤ ‖compactLaplaceTransform
          (compactLaplaceModulatedBump (riemannXiDivisorZeroValue p0))
          (riemannXiDivisorZeroValue p)‖ →
        Polynomial.eval
          (Complex.exp ((h : ℂ) * riemannXiDivisorZeroValue p)) P = 0 := by
  classical
  obtain ⟨U0, hp0U0, hU0⟩ := exists_compactLaplaceBadValueFinset p0
    (by norm_num : (0 : ℝ) < 1 / 2)
  let U := U0 ∪ V
  have hp0U : riemannXiDivisorZeroValue p0 ∉ U := by
    simp only [U, Finset.mem_union, not_or]
    exact ⟨hp0U0, hp0V⟩
  obtain ⟨h, hh, hsep⟩ := gaussianCriterion_exists_pos_exp_mul_separates_finset
    (riemannXiDivisorZeroValue p0) U hp0U
  let P0 := compactLaplaceSeparatorPolynomial h U
  let z0 := Complex.exp ((h : ℂ) * riemannXiDivisorZeroValue p0)
  have hP0 : Polynomial.eval z0 P0 ≠ 0 := by
    exact compactLaplaceSeparatorPolynomial_eval_ne_zero hsep
  let P : Polynomial ℂ := Polynomial.C ((Polynomial.eval z0 P0)⁻¹) * P0
  refine ⟨h, P, hh, ?_, ?_, ?_⟩
  · simp [P, z0, hP0]
  · intro z hz
    have hzU : z ∈ U := by
      exact Finset.mem_union_right U0 hz
    have hP0zero : Polynomial.eval (Complex.exp ((h : ℂ) * z)) P0 = 0 :=
      compactLaplaceSeparatorPolynomial_eval_eq_zero h U hzU
    simp [P, hP0zero]
  · intro p hpne hpLarge
    have hpU0 : riemannXiDivisorZeroValue p ∈ U0 := hU0 p hpne hpLarge
    have hpU : riemannXiDivisorZeroValue p ∈ U :=
      Finset.mem_union_left V hpU0
    have hP0zero : Polynomial.eval
        (Complex.exp ((h : ℂ) * riemannXiDivisorZeroValue p)) P0 = 0 :=
      compactLaplaceSeparatorPolynomial_eval_eq_zero h U hpU
    simp [P, hP0zero]

/-- A compact smooth complete-divisor separator which also vanishes on a prescribed finite set. -/
theorem exists_compactSupport_xiDivisor_laplace_tsum_separator_vanishesOn
    (p0 : RiemannXiDivisorZeroIndex) (V : Finset ℂ)
    (hp0V : riemannXiDivisorZeroValue p0 ∉ V)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : ℝ → ℂ,
      ContDiff ℝ ∞ f ∧
      HasCompactSupport f ∧
      compactLaplaceTransform f (riemannXiDivisorZeroValue p0) = 1 ∧
      (∀ z ∈ V, compactLaplaceTransform f z = 0) ∧
      Summable (fun p : RiemannXiDivisorZeroIndex ↦
        ‖compactLaplaceTransform f (riemannXiDivisorZeroValue p)‖) ∧
      ∑' p : RiemannXiDivisorZeroIndex,
        (if riemannXiDivisorZeroValue p = riemannXiDivisorZeroValue p0 then 0
        else ‖compactLaplaceTransform f (riemannXiDivisorZeroValue p)‖) < ε := by
  obtain ⟨h, P, hh, hPtarget, hPvanish, hkill⟩ :=
    exists_compactLaplaceNormalizedSeparatorData_vanishesOn p0 V hp0V
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
  have hfSmooth : ContDiff ℝ ∞ f :=
    contDiff_compactLaplaceGeneratedSeparator p0 h P m
  have hfSupp : HasCompactSupport f :=
    hasCompactSupport_compactLaplaceGeneratedSeparator p0 h P m
  have hfVanish : ∀ z ∈ V, compactLaplaceTransform f z = 0 := by
    intro z hz
    rw [compactLaplaceTransform_generatedSeparator, hPvanish z hz]
    simp
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
    compactLaplaceTransform_generatedSeparator_target p0 hPtarget m,
    hfVanish, hfSum, ?_⟩
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

theorem norm_compactLaplaceTransform_lt_of_separator_tail
    {f : ℝ → ℂ} {p0 p : RiemannXiDivisorZeroIndex} {ε : ℝ}
    (hsum : Summable (fun q : RiemannXiDivisorZeroIndex ↦
      ‖compactLaplaceTransform f (riemannXiDivisorZeroValue q)‖))
    (htail : ∑' q : RiemannXiDivisorZeroIndex,
      (if riemannXiDivisorZeroValue q = riemannXiDivisorZeroValue p0 then 0
      else ‖compactLaplaceTransform f (riemannXiDivisorZeroValue q)‖) < ε)
    (hp : riemannXiDivisorZeroValue p ≠ riemannXiDivisorZeroValue p0) :
    ‖compactLaplaceTransform f (riemannXiDivisorZeroValue p)‖ < ε := by
  let tail : RiemannXiDivisorZeroIndex → ℝ := fun q ↦
    if riemannXiDivisorZeroValue q = riemannXiDivisorZeroValue p0 then 0
    else ‖compactLaplaceTransform f (riemannXiDivisorZeroValue q)‖
  have htailSum : Summable tail := by
    apply hsum.of_nonneg_of_le
    · intro q
      simp only [tail]
      split <;> positivity
    · intro q
      simp only [tail]
      split <;> simp
  have hle : tail p ≤ ∑' q : RiemannXiDivisorZeroIndex, tail q :=
    htailSum.le_tsum p (fun q _hq ↦ by
      simp only [tail]
      split <;> positivity)
  have hpTail : tail p = ‖compactLaplaceTransform f (riemannXiDivisorZeroValue p)‖ := by
    simp [tail, hp]
  rw [hpTail] at hle
  exact lt_of_le_of_lt hle (by simpa only [tail] using htail)

/-- The transform mass away from the two conjugate-reflection target values. -/
def compactWeilOffLineTail (g : ℝ → ℂ) (rho sigma : ℂ)
    (p : RiemannXiDivisorZeroIndex) : ℝ :=
  if riemannXiDivisorZeroValue p = rho ∨ riemannXiDivisorZeroValue p = sigma then 0
  else ‖compactLaplaceTransform g (riemannXiDivisorZeroValue p)‖

/-- Conjugate reflection about the critical line. -/
def compactWeilConjugateReflection (z : ℂ) : ℂ :=
  1 - (starRingEnd ℂ) z

@[simp] theorem compactWeilConjugateReflection_involution (z : ℂ) :
    compactWeilConjugateReflection (compactWeilConjugateReflection z) = z := by
  simp [compactWeilConjugateReflection]

theorem norm_compactLaplaceTransform_conjugateReflection_lt_of_offLineTail
    {g : ℝ → ℂ} {rho : ℂ}
    (htailSum : Summable
      (compactWeilOffLineTail g rho (compactWeilConjugateReflection rho)))
    (htail : ∑' q : RiemannXiDivisorZeroIndex,
      compactWeilOffLineTail g rho (compactWeilConjugateReflection rho) q < 1 / 4)
    (p : RiemannXiDivisorZeroIndex)
    (hprho : riemannXiDivisorZeroValue p ≠ rho)
    (hpsigma : riemannXiDivisorZeroValue p ≠ compactWeilConjugateReflection rho) :
    ‖compactLaplaceTransform g
      (compactWeilConjugateReflection (riemannXiDivisorZeroValue p))‖ < 1 / 4 := by
  let z := riemannXiDivisorZeroValue p
  have hzZero : IsNontrivialZero z :=
    riemannXiDivisorZeroIndex_val_isNontrivialZero p
  have hpartnerZero : IsNontrivialZero (compactWeilConjugateReflection z) := by
    exact isNontrivialZero_one_sub_conj hzZero
  obtain ⟨q, hq⟩ :=
    exists_riemannXiDivisorZeroIndex_of_isNontrivialZero hpartnerZero
  have hpartnerRho : compactWeilConjugateReflection z ≠ rho := by
    intro heq
    have hback := congrArg compactWeilConjugateReflection heq
    have : z = compactWeilConjugateReflection rho := by
      simpa using hback
    exact hpsigma (by simpa only [z] using this)
  have hpartnerSigma :
      compactWeilConjugateReflection z ≠ compactWeilConjugateReflection rho := by
    intro heq
    have hback := congrArg compactWeilConjugateReflection heq
    have : z = rho := by simpa using hback
    exact hprho (by simpa only [z] using this)
  have hqTail :
      compactWeilOffLineTail g rho (compactWeilConjugateReflection rho) q =
        ‖compactLaplaceTransform g (compactWeilConjugateReflection z)‖ := by
    simp [compactWeilOffLineTail, hq, hpartnerRho, hpartnerSigma]
  have hle := htailSum.le_tsum q (fun r _hr ↦ by
    unfold compactWeilOffLineTail
    split <;> positivity)
  rw [hqTail] at hle
  exact lt_of_le_of_lt hle htail

theorem exists_compactWeil_offLine_pair_separator
    (F : Finset ℂ) (hFzero : ∀ z ∈ F, ¬ IsNontrivialZero z)
    (p0 : RiemannXiDivisorZeroIndex)
    (hp0 : (riemannXiDivisorZeroValue p0).re ≠ 1 / 2) :
    ∃ g : ℝ → ℂ,
      ContDiff ℝ ∞ g ∧
      HasCompactSupport g ∧
      (∀ z ∈ F, compactLaplaceTransform g z = 0) ∧
      compactLaplaceTransform g (riemannXiDivisorZeroValue p0) = 1 ∧
      compactLaplaceTransform g
        (1 - (starRingEnd ℂ) (riemannXiDivisorZeroValue p0)) = -1 ∧
      Summable (fun p : RiemannXiDivisorZeroIndex ↦
        ‖compactLaplaceTransform g (riemannXiDivisorZeroValue p)‖) ∧
      Summable (compactWeilOffLineTail g (riemannXiDivisorZeroValue p0)
        (1 - (starRingEnd ℂ) (riemannXiDivisorZeroValue p0))) ∧
      ∑' p : RiemannXiDivisorZeroIndex,
        compactWeilOffLineTail g (riemannXiDivisorZeroValue p0)
          (1 - (starRingEnd ℂ) (riemannXiDivisorZeroValue p0)) p < 1 / 4 := by
  classical
  let rho := riemannXiDivisorZeroValue p0
  let sigma := 1 - (starRingEnd ℂ) rho
  have hrhoZero : IsNontrivialZero rho :=
    riemannXiDivisorZeroIndex_val_isNontrivialZero p0
  have hsigmaZero : IsNontrivialZero sigma := by
    exact isNontrivialZero_one_sub_conj hrhoZero
  have hsigmaNe : sigma ≠ rho := by
    intro heq
    apply hp0
    have hre := congrArg Complex.re heq
    dsimp only [sigma, rho] at hre ⊢
    simp at hre
    linarith
  obtain ⟨q0, hq0⟩ :=
    exists_riemannXiDivisorZeroIndex_of_isNontrivialZero hsigmaZero
  have hrhoF : rho ∉ F := by
    intro hrhoMem
    exact hFzero rho hrhoMem hrhoZero
  have hsigmaF : sigma ∉ F := by
    intro hsigmaMem
    exact hFzero sigma hsigmaMem hsigmaZero
  let Vrho := insert sigma F
  let Vsigma := insert rho F
  have hrhoVrho : rho ∉ Vrho := by
    simp only [Vrho, Finset.mem_insert, not_or]
    exact ⟨Ne.symm hsigmaNe, hrhoF⟩
  have hsigmaVsigma : sigma ∉ Vsigma := by
    simp only [Vsigma, Finset.mem_insert, not_or]
    exact ⟨hsigmaNe, hsigmaF⟩
  obtain ⟨u, huSmooth, huSupp, huRho, huVanish, huSum, huTail⟩ :=
    exists_compactSupport_xiDivisor_laplace_tsum_separator_vanishesOn
      p0 Vrho hrhoVrho (by norm_num : (0 : ℝ) < 1 / 8)
  have hq0V : riemannXiDivisorZeroValue q0 ∉ Vsigma := by
    simpa only [hq0] using hsigmaVsigma
  obtain ⟨v, hvSmooth, hvSupp, hvSigma0, hvVanish, hvSum, hvTail0⟩ :=
    exists_compactSupport_xiDivisor_laplace_tsum_separator_vanishesOn
      q0 Vsigma hq0V (by norm_num : (0 : ℝ) < 1 / 8)
  have huSigma : compactLaplaceTransform u sigma = 0 :=
    huVanish sigma (Finset.mem_insert_self sigma F)
  have hvRho : compactLaplaceTransform v rho = 0 :=
    hvVanish rho (Finset.mem_insert_self rho F)
  have hvSigma : compactLaplaceTransform v sigma = 1 := by
    simpa only [hq0] using hvSigma0
  have huF : ∀ z ∈ F, compactLaplaceTransform u z = 0 := by
    intro z hz
    exact huVanish z (Finset.mem_insert_of_mem hz)
  have hvF : ∀ z ∈ F, compactLaplaceTransform v z = 0 := by
    intro z hz
    exact hvVanish z (Finset.mem_insert_of_mem hz)
  let g : ℝ → ℂ := fun x ↦ u x - v x
  have hgSmooth : ContDiff ℝ ∞ g := huSmooth.sub hvSmooth
  have hgSupp : HasCompactSupport g := huSupp.sub hvSupp
  have hgTransform (s : ℂ) :
      compactLaplaceTransform g s =
        compactLaplaceTransform u s - compactLaplaceTransform v s := by
    exact compactLaplaceTransform_sub s
      (integrable_compactLaplaceKernel huSmooth.continuous huSupp s)
      (integrable_compactLaplaceKernel hvSmooth.continuous hvSupp s)
  have hgF : ∀ z ∈ F, compactLaplaceTransform g z = 0 := by
    intro z hz
    rw [hgTransform, huF z hz, hvF z hz]
    simp
  have hgRho : compactLaplaceTransform g rho = 1 := by
    rw [hgTransform, huRho, hvRho]
    simp
  have hgSigma : compactLaplaceTransform g sigma = -1 := by
    rw [hgTransform, huSigma, hvSigma]
    ring
  have hgSum : Summable (fun p : RiemannXiDivisorZeroIndex ↦
      ‖compactLaplaceTransform g (riemannXiDivisorZeroValue p)‖) := by
    apply summable_norm_compactLaplaceTransform_xiDivisorZero
    · exact hgSmooth.of_le
        (WithTop.coe_le_coe.mpr (OrderTop.le_top (2 : ℕ∞)))
    · exact hgSupp
  let tu : RiemannXiDivisorZeroIndex → ℝ := fun p ↦
    if riemannXiDivisorZeroValue p = rho then 0
    else ‖compactLaplaceTransform u (riemannXiDivisorZeroValue p)‖
  let tv : RiemannXiDivisorZeroIndex → ℝ := fun p ↦
    if riemannXiDivisorZeroValue p = sigma then 0
    else ‖compactLaplaceTransform v (riemannXiDivisorZeroValue p)‖
  have htuSum : Summable tu := by
    apply huSum.of_nonneg_of_le
    · intro p
      simp only [tu]
      split <;> positivity
    · intro p
      simp only [tu]
      split <;> simp
  have htvSum : Summable tv := by
    apply hvSum.of_nonneg_of_le
    · intro p
      simp only [tv]
      split <;> positivity
    · intro p
      simp only [tv]
      split <;> simp
  have htuTail : (∑' p : RiemannXiDivisorZeroIndex, tu p) < 1 / 8 := by
    simpa only [tu, rho] using huTail
  have htvTail : (∑' p : RiemannXiDivisorZeroIndex, tv p) < 1 / 8 := by
    simpa only [tv, sigma, hq0] using hvTail0
  have hgTailSum : Summable (compactWeilOffLineTail g rho sigma) := by
    apply hgSum.of_nonneg_of_le
    · intro p
      unfold compactWeilOffLineTail
      split <;> positivity
    · intro p
      unfold compactWeilOffLineTail
      split <;> simp
  have hgTailPoint : ∀ p : RiemannXiDivisorZeroIndex,
      compactWeilOffLineTail g rho sigma p ≤ tu p + tv p := by
    intro p
    unfold compactWeilOffLineTail
    split_ifs with htarget
    · positivity
    · have hrho : riemannXiDivisorZeroValue p ≠ rho := by
        exact fun h ↦ htarget (Or.inl h)
      have hsigma : riemannXiDivisorZeroValue p ≠ sigma := by
        exact fun h ↦ htarget (Or.inr h)
      rw [hgTransform]
      simp only [tu, tv, if_neg hrho, if_neg hsigma]
      exact norm_sub_le _ _
  have hgTail :
      (∑' p : RiemannXiDivisorZeroIndex,
        compactWeilOffLineTail g rho sigma p) < 1 / 4 := by
    calc
      (∑' p : RiemannXiDivisorZeroIndex,
          compactWeilOffLineTail g rho sigma p) ≤
          ∑' p : RiemannXiDivisorZeroIndex, (tu p + tv p) :=
        hgTailSum.tsum_le_tsum hgTailPoint (htuSum.add htvSum)
      _ = (∑' p : RiemannXiDivisorZeroIndex, tu p) +
          ∑' p : RiemannXiDivisorZeroIndex, tv p := htuSum.tsum_add htvSum
      _ < 1 / 4 := by linarith
  refine ⟨g, hgSmooth, hgSupp, hgF, ?_, ?_, hgSum, ?_, ?_⟩
  · simpa only [rho] using hgRho
  · simpa only [rho, sigma] using hgSigma
  · simpa only [rho, sigma] using hgTailSum
  · simpa only [rho, sigma] using hgTail

theorem exists_compactWeilRawZeroQuadratic_re_neg_of_offLine
    (F : Finset ℂ) (hFzero : ∀ z ∈ F, ¬ IsNontrivialZero z)
    (p0 : RiemannXiDivisorZeroIndex)
    (hp0 : (riemannXiDivisorZeroValue p0).re ≠ 1 / 2) :
    ∃ g : ℝ → ℂ,
      ContDiff ℝ ∞ g ∧
      HasCompactSupport g ∧
      (∀ z ∈ F, compactLaplaceTransform g z = 0) ∧
      (compactWeilRawZeroQuadratic g).re < 0 := by
  classical
  obtain ⟨g, hgSmooth, hgSupp, hgF, hgRho0, hgSigma0, hgSum,
      hgTailSum0, hgTail0⟩ :=
    exists_compactWeil_offLine_pair_separator F hFzero p0 hp0
  let rho := riemannXiDivisorZeroValue p0
  let sigma := compactWeilConjugateReflection rho
  have hgRho : compactLaplaceTransform g rho = 1 := by
    simpa only [rho] using hgRho0
  have hgSigma : compactLaplaceTransform g sigma = -1 := by
    simpa only [rho, sigma, compactWeilConjugateReflection] using hgSigma0
  have hgTailSum : Summable (compactWeilOffLineTail g rho sigma) := by
    simpa only [rho, sigma, compactWeilConjugateReflection] using hgTailSum0
  have hgTail :
      (∑' p : RiemannXiDivisorZeroIndex,
        compactWeilOffLineTail g rho sigma p) < 1 / 4 := by
    simpa only [rho, sigma, compactWeilConjugateReflection] using hgTail0
  let term : RiemannXiDivisorZeroIndex → ℂ := fun p ↦
    compactLaplaceTransform (compactLaplaceAutocorrelation g)
      (riemannXiDivisorZeroValue p)
  have hautoSmooth := contDiff_compactLaplaceAutocorrelation hgSmooth hgSupp
  have hautoSupp := hasCompactSupport_compactLaplaceAutocorrelation hgSupp
  have htermSum : Summable term := by
    exact (summable_norm_compactLaplaceTransform_xiDivisorZero
      (hautoSmooth.of_le
        (WithTop.coe_le_coe.mpr (OrderTop.le_top (2 : ℕ∞)))) hautoSupp).of_norm
  have htermFormula (p : RiemannXiDivisorZeroIndex) :
      term p = compactLaplaceTransform g (riemannXiDivisorZeroValue p) *
        (starRingEnd ℂ) (compactLaplaceTransform g
          (compactWeilConjugateReflection (riemannXiDivisorZeroValue p))) := by
    simpa only [term, compactWeilConjugateReflection] using
      compactLaplaceTransform_autocorrelation hgSmooth hgSupp
        (riemannXiDivisorZeroValue p)
  let major : RiemannXiDivisorZeroIndex → ℝ := fun p ↦
    (if p = p0 then -1 else 0) +
      compactWeilOffLineTail g rho sigma p * (1 / 4)
  have hsingleSum : Summable (fun p : RiemannXiDivisorZeroIndex ↦
      if p = p0 then (-1 : ℝ) else 0) :=
    (hasSum_ite_eq p0 (-1 : ℝ)).summable
  have hscaledSum : Summable (fun p : RiemannXiDivisorZeroIndex ↦
      compactWeilOffLineTail g rho sigma p * (1 / 4)) :=
    hgTailSum.mul_right (1 / 4)
  have hmajorSum : Summable major := by
    exact hsingleSum.add hscaledSum
  have hmajorTsum :
      (∑' p : RiemannXiDivisorZeroIndex, major p) =
        -1 + (∑' p : RiemannXiDivisorZeroIndex,
          compactWeilOffLineTail g rho sigma p) * (1 / 4) := by
    change tsum (fun p : RiemannXiDivisorZeroIndex ↦
      (if p = p0 then (-1 : ℝ) else 0) +
        compactWeilOffLineTail g rho sigma p * (1 / 4)) = _
    rw [hsingleSum.tsum_add hscaledSum, (hasSum_ite_eq p0 (-1 : ℝ)).tsum_eq,
      tsum_mul_right]
  have hmajorNeg : (∑' p : RiemannXiDivisorZeroIndex, major p) < 0 := by
    rw [hmajorTsum]
    nlinarith
  have hpoint : ∀ p : RiemannXiDivisorZeroIndex, (term p).re ≤ major p := by
    intro p
    rw [htermFormula]
    by_cases hpidx : p = p0
    · subst p
      have hsigmaArg : compactWeilConjugateReflection
          (riemannXiDivisorZeroValue p0) = sigma := rfl
      rw [hgRho, hsigmaArg, hgSigma]
      simp [major, compactWeilOffLineTail, rho]
    · by_cases htarget :
          riemannXiDivisorZeroValue p = rho ∨
            riemannXiDivisorZeroValue p = sigma
      · rcases htarget with hrho | hsigma
        · rw [hrho, hgRho]
          have harg : compactWeilConjugateReflection rho = sigma := rfl
          rw [harg, hgSigma]
          simp [major, hpidx, compactWeilOffLineTail, hrho]
        · rw [hsigma, hgSigma]
          have harg : compactWeilConjugateReflection sigma = rho := by
            simp [sigma]
          rw [harg, hgRho]
          simp [major, hpidx, compactWeilOffLineTail, hsigma]
      · have hprho : riemannXiDivisorZeroValue p ≠ rho :=
          fun h ↦ htarget (Or.inl h)
        have hpsigma : riemannXiDivisorZeroValue p ≠ sigma :=
          fun h ↦ htarget (Or.inr h)
        have hpartner : ‖compactLaplaceTransform g
            (compactWeilConjugateReflection (riemannXiDivisorZeroValue p))‖ < 1 / 4 := by
          exact norm_compactLaplaceTransform_conjugateReflection_lt_of_offLineTail
            hgTailSum hgTail p hprho hpsigma
        calc
          (compactLaplaceTransform g (riemannXiDivisorZeroValue p) *
              (starRingEnd ℂ) (compactLaplaceTransform g
                (compactWeilConjugateReflection
                  (riemannXiDivisorZeroValue p)))).re ≤
              ‖compactLaplaceTransform g (riemannXiDivisorZeroValue p) *
                (starRingEnd ℂ) (compactLaplaceTransform g
                  (compactWeilConjugateReflection
                    (riemannXiDivisorZeroValue p)))‖ :=
            Complex.re_le_norm _
          _ = ‖compactLaplaceTransform g (riemannXiDivisorZeroValue p)‖ *
              ‖compactLaplaceTransform g
                (compactWeilConjugateReflection
                  (riemannXiDivisorZeroValue p))‖ := by simp
          _ ≤ compactWeilOffLineTail g rho sigma p * (1 / 4) := by
            simp only [compactWeilOffLineTail, if_neg htarget]
            exact mul_le_mul_of_nonneg_left hpartner.le (norm_nonneg _)
          _ = major p := by simp [major, hpidx]
  have htermReSum : Summable (fun p : RiemannXiDivisorZeroIndex ↦ (term p).re) := by
    simpa [Function.comp_def] using
      htermSum.map Complex.reCLM Complex.reCLM.continuous
  have hsumLe : (∑' p : RiemannXiDivisorZeroIndex, (term p).re) ≤
      ∑' p : RiemannXiDivisorZeroIndex, major p :=
    htermReSum.tsum_le_tsum hpoint hmajorSum
  refine ⟨g, hgSmooth, hgSupp, hgF, ?_⟩
  rw [compactWeilRawZeroQuadratic, Complex.re_tsum htermSum]
  change (∑' p : RiemannXiDivisorZeroIndex, (term p).re) < 0
  exact lt_of_le_of_lt hsumLe hmajorNeg

theorem exists_compactWeilArithmeticQuadratic_re_neg_of_offLine
    (F : Finset ℂ) (hFzero : ∀ z ∈ F, ¬ IsNontrivialZero z)
    (hzero : 0 ∈ F) (hone : 1 ∈ F)
    (p0 : RiemannXiDivisorZeroIndex)
    (hp0 : (riemannXiDivisorZeroValue p0).re ≠ 1 / 2) :
    ∃ g : ℝ → ℂ,
      ContDiff ℝ ∞ g ∧
      HasCompactSupport g ∧
      (∀ z ∈ F, compactLaplaceTransform g z = 0) ∧
      (compactWeilArithmeticQuadratic g).re < 0 := by
  obtain ⟨g, hgSmooth, hgSupp, hgF, hrawNeg⟩ :=
    exists_compactWeilRawZeroQuadratic_re_neg_of_offLine F hFzero p0 hp0
  have hformula := compactWeilArithmeticQuadratic_eq_pi_mul_zeroQuadratic
    hgSmooth hgSupp (hgF 0 hzero) (hgF 1 hone)
  have hzeroRaw := compactWeilZeroQuadratic_eq_rawZeroQuadratic hgSmooth hgSupp
  refine ⟨g, hgSmooth, hgSupp, hgF, ?_⟩
  rw [hformula, hzeroRaw]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_neg_of_pos_of_neg Real.pi_pos hrawNeg

theorem riemannHypothesis_of_compactWeilArithmeticQuadratic_re_nonneg
    (F : Finset ℂ) (hFzero : ∀ z ∈ F, ¬ IsNontrivialZero z)
    (hzero : 0 ∈ F) (hone : 1 ∈ F)
    (hpos : ∀ g : ℝ → ℂ,
      ContDiff ℝ ∞ g →
      HasCompactSupport g →
      (∀ z ∈ F, compactLaplaceTransform g z = 0) →
      0 ≤ (compactWeilArithmeticQuadratic g).re) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_nontrivial_zeros_on_line]
  intro rho hrho
  rw [OnCriticalLine]
  obtain ⟨p, hp⟩ := exists_riemannXiDivisorZeroIndex_of_isNontrivialZero hrho
  by_contra hline
  have hpOff : (riemannXiDivisorZeroValue p).re ≠ 1 / 2 := by
    simpa only [hp] using hline
  obtain ⟨g, hgSmooth, hgSupp, hgF, hneg⟩ :=
    exists_compactWeilArithmeticQuadratic_re_neg_of_offLine
      F hFzero hzero hone p hpOff
  exact (not_lt_of_ge (hpos g hgSmooth hgSupp hgF)) hneg

/-- Connes--Consani/Yoshida compact-support Weil criterion on the additive logarithmic class. -/
theorem riemannHypothesis_iff_compactWeilArithmeticQuadratic_re_nonneg
    (F : Finset ℂ)
    (hFzero : ∀ z ∈ F, ¬ IsNontrivialZero z)
    (hzero : 0 ∈ F) (hone : 1 ∈ F) :
    RiemannHypothesis ↔
      ∀ g : ℝ → ℂ,
        ContDiff ℝ ∞ g →
        HasCompactSupport g →
        (∀ z ∈ F, compactLaplaceTransform g z = 0) →
        0 ≤ (compactWeilArithmeticQuadratic g).re := by
  constructor
  · intro hRH
    exact RiemannHypothesis.compactWeilArithmeticQuadratic_re_nonneg_of_vanishesOn
      hRH F hzero hone
  · exact riemannHypothesis_of_compactWeilArithmeticQuadratic_re_nonneg
      F hFzero hzero hone
end

end LeanLab.Riemann
