import LeanLab.Riemann.LevinsonMontgomeryPairedMassDensity
import LeanLab.Riemann.DeBruijnNewmanPolymathStieltjesScaledGamma
import LeanLab.Riemann.WeilGaussianExplicitFormula
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Levinson--Montgomery logarithmic derivative to paired mass

This file reconstructs equation (2.1) of Levinson and Montgomery from the actual project zeta,
xi, and multiplicity-bearing paired zero divisor.  It derives the required digamma estimate from
the compiled Stieltjes representation, then feeds the resulting negative paired mass into the
existing dense zero-count branch.
-/

namespace LeanLab.Riemann

open Complex Filter Function MeasureTheory Real Set
open scoped BigOperators ComplexConjugate Interval Real Topology

noncomputable section

theorem levinsonMontgomeryRealPairedZeroSum_eq_logDeriv_riemannXi_re
    {s : ℂ} (hxi : riemannXi s ≠ 0) :
    levinsonMontgomeryRealPairedZeroSum s =
      (logDeriv riemannXi s).re := by
  let f : RiemannXiDivisorZeroIndex → ℝ := fun p =>
    (riemannXiLogDerivZeroTerm p s).re
  let g : RiemannXiDivisorZeroIndex → ℝ := fun p =>
    (1 / riemannXiDivisorZeroValue p).re
  have hf : Summable f := by
    have hcomplex :=
      summable_riemannXiLogDerivZeroTerm_of_mem_nonzeroSet
        (show s ∈ riemannXiNonzeroSet from hxi)
    simpa [f, Function.comp_def] using
      hcomplex.map Complex.reCLM Complex.reCLM.continuous
  have hg : Summable g := by
    simpa [g] using summable_re_inv_riemannXiDivisorZeroValue
  have hfPair : Summable (fun p =>
      f (levinsonMontgomeryPairedZeroEquiv p)) :=
    hf.comp_injective levinsonMontgomeryPairedZeroEquiv.injective
  have hgPair : Summable (fun p =>
      g (levinsonMontgomeryPairedZeroEquiv p)) :=
    hg.comp_injective levinsonMontgomeryPairedZeroEquiv.injective
  have hpaired :
      levinsonMontgomeryRealPairedZeroSum s =
        (∑' p, f p) - ∑' p, g p := by
    rw [levinsonMontgomeryRealPairedZeroSum]
    calc
      (∑' p : RiemannXiDivisorZeroIndex,
          levinsonMontgomeryPairedReciprocalTerm s p) =
          ∑' p : RiemannXiDivisorZeroIndex,
            (1 / 2 : ℝ) *
              (f p + f (levinsonMontgomeryPairedZeroEquiv p) -
                g p - g (levinsonMontgomeryPairedZeroEquiv p)) := by
        apply tsum_congr
        intro p
        simp only [levinsonMontgomeryPairedReciprocalTerm,
          riemannXiLogDerivZeroTerm, f, g, add_re]
        ring
      _ = (1 / 2 : ℝ) * ∑' p : RiemannXiDivisorZeroIndex,
          (f p + f (levinsonMontgomeryPairedZeroEquiv p) -
            g p - g (levinsonMontgomeryPairedZeroEquiv p)) := by
        rw [tsum_mul_left]
      _ = (∑' p, f p) - ∑' p, g p := by
        rw [((hf.add hfPair).sub hg).tsum_sub hgPair,
          (hf.add hfPair).tsum_sub hg, hf.tsum_add hfPair,
          levinsonMontgomeryPairedZeroEquiv.tsum_eq,
          levinsonMontgomeryPairedZeroEquiv.tsum_eq]
        ring
  obtain ⟨P, hdegree, hfac⟩ := exists_riemannXi_hadamard_factorization
  have hzeroComplex :=
    summable_riemannXiLogDerivZeroTerm_of_mem_nonzeroSet
      (show s ∈ riemannXiNonzeroSet from hxi)
  have hlog :=
    riemannXi_logDeriv_eq_polynomial_derivative_add_tsum
      hfac (show s ∈ riemannXiNonzeroSet from hxi)
  have hcancel :=
    hadamard_polynomial_add_half_reciprocal_tsum_eq_zero hdegree hfac
  have hfirst : Summable (fun p : RiemannXiDivisorZeroIndex =>
      (1 / (1 - riemannXiDivisorZeroValue p)).re) := by
    have hreflect := hg.comp_injective riemannXiDivisorZeroReflectEquiv.injective
    refine hreflect.congr (fun p => ?_)
    simp [g]
  have hfirstTsum :
      (∑' p : RiemannXiDivisorZeroIndex,
          (1 / (1 - riemannXiDivisorZeroValue p)).re) =
        ∑' p : RiemannXiDivisorZeroIndex,
          (1 / riemannXiDivisorZeroValue p).re := by
    change (∑' p : RiemannXiDivisorZeroIndex,
      g (riemannXiDivisorZeroReflectEquiv p)) = ∑' p, g p
    exact riemannXiDivisorZeroReflectEquiv.tsum_eq g
  have hpairRe :
      (∑' p : RiemannXiDivisorZeroIndex,
          riemannXiLiReciprocalPair p).re =
        2 * ∑' p : RiemannXiDivisorZeroIndex,
          (1 / riemannXiDivisorZeroValue p).re := by
    rw [Complex.re_tsum summable_riemannXiLiReciprocalPair]
    simp only [riemannXiLiReciprocalPair, add_re]
    rw [hfirst.tsum_add hg, hfirstTsum]
    ring
  have hPconstant :
      Polynomial.eval s P.derivative = Polynomial.eval 1 P.derivative := by
    rw [polynomial_derivative_eq_C_eval_one_of_degree_le_one hdegree]
    simp
  have hPre :
      (Polynomial.eval s P.derivative).re =
        -(∑' p : RiemannXiDivisorZeroIndex,
          (1 / riemannXiDivisorZeroValue p).re) := by
    have htwo :
        2 * Polynomial.eval 1 P.derivative +
            (∑' p : RiemannXiDivisorZeroIndex,
              riemannXiLiReciprocalPair p) = 0 := by
      calc
        2 * Polynomial.eval 1 P.derivative +
            (∑' p : RiemannXiDivisorZeroIndex,
              riemannXiLiReciprocalPair p) =
            2 * (Polynomial.eval 1 P.derivative +
              (∑' p : RiemannXiDivisorZeroIndex,
                riemannXiLiReciprocalPair p) / 2) := by ring
        _ = 0 := by rw [hcancel]; ring
    have hcancelRe := congrArg Complex.re htwo
    rw [add_re, mul_re, hpairRe] at hcancelRe
    norm_num at hcancelRe
    rw [hPconstant]
    simp only [one_div, inv_re]
    linarith
  rw [hpaired, hlog, add_re, Complex.re_tsum hzeroComplex, hPre]
  simp only [f, g]
  ring

/-- The differentiated Stieltjes remainder in the logarithmic Stirling formula. -/
def levinsonMontgomeryDigammaStirlingRemainder (z : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0,
    deBruijnNewmanPolymathStieltjesIntegrandDerivative z t

theorem levinsonMontgomeryGammaStirlingMain_hasDerivAt
    {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt deBruijnNewmanPolymathGammaStirlingMain
      (deBruijnNewmanPolymathGammaStirlingMain z *
        (Complex.log z - 1 / (2 * z))) z := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    norm_num at hz
  have hlog := Complex.hasDerivAt_log (Or.inl hz)
  have hlinear := (hasDerivAt_id z).sub_const (1 / 2 : ℂ)
  have hphaseRaw := (hlinear.mul hlog).sub (hasDerivAt_id z)
  have hphaseDeriv :
      1 * Complex.log z + (id z - 1 / 2) * z⁻¹ - 1 =
        Complex.log z - 1 / (2 * z) := by
    simp only [id_eq]
    field_simp [hz0]
    ring
  have hphase :
      HasDerivAt
        (fun w : ℂ => (w - 1 / 2) * Complex.log w - w)
        (Complex.log z - 1 / (2 * z)) z := by
    refine (hphaseRaw.congr_deriv hphaseDeriv).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun w => ?_)
    rfl
  have hexp := hphase.cexp
  have hmain := hexp.const_mul (Real.sqrt (2 * Real.pi) : ℂ)
  unfold deBruijnNewmanPolymathGammaStirlingMain
  simpa only [Pi.mul_apply] using hmain.congr_deriv (by ring)

theorem logDeriv_deBruijnNewmanPolymathGammaStirlingMain
    {z : ℂ} (hz : 0 < z.re) :
    logDeriv deBruijnNewmanPolymathGammaStirlingMain z =
      Complex.log z - 1 / (2 * z) := by
  rw [logDeriv_apply,
    (levinsonMontgomeryGammaStirlingMain_hasDerivAt hz).deriv]
  exact mul_div_cancel_left₀ _
    (deBruijnNewmanPolymathGammaStirlingMain_ne_zero z)

theorem logDeriv_deBruijnNewmanPolymathScaledGamma_eq_stieltjesDerivative
    {z : ℂ} (hz : 0 < z.re) :
    logDeriv deBruijnNewmanPolymathScaledGamma z =
      levinsonMontgomeryDigammaStirlingRemainder z := by
  let U : Set ℂ := {w : ℂ | 0 < w.re}
  have hU : U ∈ 𝓝 z :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz
  have heq : deBruijnNewmanPolymathScaledGamma =ᶠ[𝓝 z]
      fun w => Complex.exp
        (deBruijnNewmanPolymathStieltjesLogRemainder w) := by
    filter_upwards [hU] with w hw
    exact deBruijnNewmanPolymath_scaledGamma_eq_exp_stieltjes hw
  have hrem :
      HasDerivAt deBruijnNewmanPolymathStieltjesLogRemainder
        (levinsonMontgomeryDigammaStirlingRemainder z) z := by
    change HasDerivAt
      (fun w : ℂ => ∫ t : ℝ in Ioi 0,
        deBruijnNewmanPolymathStieltjesIntegrand w t)
      (∫ t : ℝ in Ioi 0,
        deBruijnNewmanPolymathStieltjesIntegrandDerivative z t) z
    exact deBruijnNewmanPolymathStieltjesLogRemainder_hasDerivAt hz
  have hexp := hrem.cexp
  rw [logDeriv_apply, heq.deriv_eq, heq.self_of_nhds, hexp.deriv]
  field_simp

/-- Stieltjes's logarithmic Stirling formula for the actual project digamma function. -/
theorem levinsonMontgomery_digamma_stirling
    {z : ℂ} (hz : 0 < z.re) :
    Complex.digamma z =
      Complex.log z - 1 / (2 * z) +
        levinsonMontgomeryDigammaStirlingRemainder z := by
  have hnotpole : ∀ m : ℕ, z ≠ -m := by
    intro m h
    have hre := congrArg Complex.re h
    simp only [Complex.natCast_re, Complex.neg_re] at hre
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hgamma : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero hnotpole
  have hmain : deBruijnNewmanPolymathGammaStirlingMain z ≠ 0 :=
    deBruijnNewmanPolymathGammaStirlingMain_ne_zero z
  have hdiv := logDeriv_div z hgamma hmain
    (Complex.differentiableAt_Gamma z hnotpole)
    (levinsonMontgomeryGammaStirlingMain_hasDerivAt hz).differentiableAt
  change logDeriv deBruijnNewmanPolymathScaledGamma z =
      logDeriv Complex.Gamma z -
        logDeriv deBruijnNewmanPolymathGammaStirlingMain z at hdiv
  rw [logDeriv_deBruijnNewmanPolymathScaledGamma_eq_stieltjesDerivative hz,
    logDeriv_deBruijnNewmanPolymathGammaStirlingMain hz,
    ← Complex.digamma_def] at hdiv
  rw [hdiv]
  ring

theorem norm_levinsonMontgomeryStieltjesDerivative_le
    {z : ℂ} (hz : 0 < z.re) {t : ℝ} (ht : 0 ≤ t) :
    ‖deBruijnNewmanPolymathStieltjesIntegrandDerivative z t‖ ≤
      (27 / 32 : ℝ) * (t + ‖z‖) ^ (-3 : ℝ) := by
  have hQ0 := deBruijnNewmanPolymathStieltjesQ_nonneg t
  have hQ8 := deBruijnNewmanPolymathStieltjesQ_le_one_eighth t
  have hinv := inv_norm_add_cube_le_stieltjes_radial hz ht
  rw [deBruijnNewmanPolymathStieltjesIntegrandDerivative,
    norm_div, norm_mul, norm_pow, norm_real, Real.norm_of_nonneg hQ0,
    div_eq_mul_inv]
  norm_num only [norm_neg, norm_ofNat]
  calc
    2 * deBruijnNewmanPolymathStieltjesQ t *
        (‖z + (t : ℂ)‖ ^ 3)⁻¹ ≤
        2 * (1 / 8) * (‖z + (t : ℂ)‖ ^ 3)⁻¹ := by
      gcongr
    _ ≤ 2 * (1 / 8) *
        ((27 / 8) * (t + ‖z‖) ^ (-3 : ℝ)) := by
      gcongr
    _ = (27 / 32 : ℝ) * (t + ‖z‖) ^ (-3 : ℝ) := by ring

/-- An explicit derivative remainder, obtained only from the compiled Stieltjes kernel. -/
theorem levinsonMontgomery_digamma_stirling_remainder_norm_le
    {z : ℂ} (hz : 0 < z.re) :
    ‖levinsonMontgomeryDigammaStirlingRemainder z‖ ≤
      27 / (64 * ‖z‖ ^ 2) := by
  have hzNorm : 0 < ‖z‖ :=
    hz.trans_le ((le_abs_self z.re).trans (Complex.abs_re_le_norm z))
  have hint : IntegrableOn
      (fun t : ℝ => (27 / 32 : ℝ) * (t + ‖z‖) ^ (-3 : ℝ))
      (Ioi (0 : ℝ)) :=
    (integrableOn_add_rpow_Ioi_of_lt (a := (-3 : ℝ)) (c := 0)
      (m := ‖z‖) (by norm_num) (by linarith)).const_mul (27 / 32)
  have hnorm := norm_integral_le_of_norm_le hint (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact norm_levinsonMontgomeryStieltjesDerivative_le hz ht.le)
  rw [levinsonMontgomeryDigammaStirlingRemainder]
  calc
    ‖∫ t : ℝ in Ioi 0,
        deBruijnNewmanPolymathStieltjesIntegrandDerivative z t‖ ≤
        ∫ t : ℝ in Ioi 0,
          (27 / 32 : ℝ) * (t + ‖z‖) ^ (-3 : ℝ) := hnorm
    _ = (27 / 32 : ℝ) *
        ∫ t : ℝ in Ioi 0, (t + ‖z‖) ^ (-3 : ℝ) := by
      rw [integral_const_mul]
    _ = (27 / 32 : ℝ) * (1 / (2 * ‖z‖ ^ 2)) := by
      rw [integral_add_rpow_neg_three_Ioi hzNorm]
    _ = 27 / (64 * ‖z‖ ^ 2) := by ring

theorem riemannXi_eq_factor_mul_GammaR_mul_riemannZeta_of_re_pos
    {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannXi s = s * (s - 1) / 2 * Gammaℝ s * riemannZeta s := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hgamma : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs
  rw [riemannXi_eq_mul_completedRiemannZeta hs0 hs1,
    riemannZeta_def_of_ne_zero hs0]
  field_simp

theorem logDeriv_riemannXi_eq_poles_archimedean_add_riemannZeta
    {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    (hzeta : riemannZeta s ≠ 0) :
    logDeriv riemannXi s =
      1 / s + 1 / (s - 1) + logDeriv Gammaℝ s +
        logDeriv riemannZeta s := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hgamma : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs
  let A : ℂ → ℂ := fun z => z * (z - 1) / 2
  have hA : A s ≠ 0 := by
    dsimp [A]
    exact div_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) (by norm_num)
  have hdA : DifferentiableAt ℂ A s := by
    dsimp [A]
    fun_prop
  have hdGamma : DifferentiableAt ℂ Gammaℝ s :=
    differentiableAt_GammaR_of_re_pos hs
  have hdZeta : DifferentiableAt ℂ riemannZeta s :=
    differentiableAt_riemannZeta hs1
  have hAGamma : A s * Gammaℝ s ≠ 0 := mul_ne_zero hA hgamma
  have hxi : riemannXi =ᶠ[𝓝 s]
      fun z => A z * Gammaℝ z * riemannZeta z := by
    have hopen :
        {z : ℂ | 0 < z.re} ∩ ({(1 : ℂ)} : Set ℂ)ᶜ ∈ 𝓝 s :=
      inter_mem
        ((isOpen_lt continuous_const continuous_re).mem_nhds hs)
        (isOpen_compl_singleton.mem_nhds hs1)
    filter_upwards [hopen] with z hz
    simpa [A] using
      riemannXi_eq_factor_mul_GammaR_mul_riemannZeta_of_re_pos hz.1 hz.2
  have hlogEq :
      logDeriv riemannXi s =
        logDeriv (fun z => A z * Gammaℝ z * riemannZeta z) s := by
    rw [logDeriv_apply, logDeriv_apply, hxi.deriv_eq, hxi.self_of_nhds]
  rw [hlogEq,
    logDeriv_mul (f := fun z => A z * Gammaℝ z) (g := riemannZeta)
      s hAGamma hzeta (hdA.mul hdGamma) hdZeta,
    logDeriv_mul (f := A) (g := Gammaℝ) s hA hgamma hdA hdGamma,
    show logDeriv A s = 1 / s + 1 / (s - 1) by
      simpa [A] using logDeriv_riemannXiFactor hs0 hs1]

/-- The nonzero pole/Gamma term in Levinson--Montgomery equation (2.1). -/
def levinsonMontgomeryLogDerivArchimedeanTerm (s : ℂ) : ℝ :=
  -(1 / (s - 1)).re + Real.log Real.pi / 2 -
    (Complex.digamma (s / 2 + 1)).re / 2

/-- Levinson--Montgomery equation (2.1), with the zero side interpreted by the actual
multiplicity-bearing paired divisor sum. -/
theorem levinsonMontgomery_equation_two_one
    {s : ℂ} (hs0 : 0 < s.re) (hsHalf : s.re < 1 / 2)
    (hzeta : riemannZeta s ≠ 0) :
    (logDeriv riemannZeta s).re =
      levinsonMontgomeryLogDerivArchimedeanTerm s +
        levinsonMontgomeryRealPairedZeroSum s := by
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hsHalf
    norm_num at hsHalf
  have hgamma : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs0
  have hxiValue :=
    riemannXi_eq_factor_mul_GammaR_mul_riemannZeta_of_re_pos hs0 hs1
  have hfactor : s * (s - 1) / 2 ≠ 0 := by
    have hsZero : s ≠ 0 := by
      intro h
      rw [h] at hs0
      norm_num at hs0
    exact div_ne_zero (mul_ne_zero hsZero (sub_ne_zero.mpr hs1)) (by norm_num)
  have hxi : riemannXi s ≠ 0 := by
    rw [hxiValue]
    exact mul_ne_zero (mul_ne_zero hfactor hgamma) hzeta
  have hxiLog :=
    logDeriv_riemannXi_eq_poles_archimedean_add_riemannZeta
      hs0 hs1 hzeta
  have hgammaLog := logDeriv_GammaR_eq_digamma hs0
  have hsHalfRe : 0 < (s / 2).re := by
    norm_num [div_re]
    linarith
  have hnotpole : ∀ m : ℕ, s / 2 ≠ -m := by
    intro m h
    have hre := congrArg Complex.re h
    simp only [Complex.natCast_re, Complex.neg_re] at hre
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hpsi := Complex.digamma_apply_add_one (s / 2) hnotpole
  have hsZero : s ≠ 0 := by
    intro h
    rw [h] at hs0
    norm_num at hs0
  have hhalfInv : (s / 2)⁻¹ = 2 / s := by
    field_simp [hsZero]
  have hsourceComplex :
      logDeriv riemannZeta s =
        logDeriv riemannXi s - 1 / (s - 1) +
          (Real.log Real.pi : ℂ) / 2 -
          Complex.digamma (s / 2 + 1) / 2 := by
    rw [hgammaLog] at hxiLog
    rw [hpsi, hhalfInv]
    rw [hxiLog]
    simp only [div_eq_mul_inv]
    ring
  have hsourceReal := congrArg Complex.re hsourceComplex
  rw [levinsonMontgomeryRealPairedZeroSum_eq_logDeriv_riemannXi_re hxi]
  calc
    (logDeriv riemannZeta s).re =
        (logDeriv riemannXi s - 1 / (s - 1) +
          (Real.log Real.pi : ℂ) / 2 -
          Complex.digamma (s / 2 + 1) / 2).re := hsourceReal
    _ = levinsonMontgomeryLogDerivArchimedeanTerm s +
        (logDeriv riemannXi s).re := by
      rw [levinsonMontgomeryLogDerivArchimedeanTerm]
      norm_num
      ring

theorem levinsonMontgomeryLogDerivArchimedeanTerm_neg
    {s : ℂ} (hs0 : 0 ≤ s.re) (hsHalf : s.re ≤ 1 / 2)
    (hsIm : 10 ≤ s.im) :
    levinsonMontgomeryLogDerivArchimedeanTerm s < 0 := by
  let w : ℂ := s / 2 + 1
  have hwRe : 0 < w.re := by
    dsimp [w]
    norm_num [div_re]
    linarith
  have hwReLe : w.re ≤ 5 / 4 := by
    dsimp [w]
    norm_num [div_re]
    linarith
  have hwIm : 5 ≤ w.im := by
    dsimp [w]
    norm_num [div_im]
    linarith
  have hwNorm : 5 ≤ ‖w‖ := by
    calc
      5 ≤ |w.im| := by
        rw [abs_of_nonneg (by linarith)]
        exact hwIm
      _ ≤ ‖w‖ := Complex.abs_im_le_norm w
  have hwNormSq : 25 ≤ ‖w‖ ^ 2 := by
    nlinarith [norm_nonneg w]
  have hwNormPos : 0 < ‖w‖ := lt_of_lt_of_le (by norm_num) hwNorm
  have hlogPi :
      Real.log Real.pi / 2 < 7 / 10 := by
    have hpi := Real.log_lt_log Real.pi_pos Real.pi_lt_four
    have hlogFour : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      calc
        Real.log (4 : ℝ) = Real.log ((2 : ℝ) * 2) := by norm_num
        _ = Real.log 2 + Real.log 2 := by
          rw [Real.log_mul (by norm_num) (by norm_num)]
        _ = 2 * Real.log 2 := by ring
    rw [hlogFour] at hpi
    nlinarith [Real.log_two_lt_d9]
  have hlogFive : 3 / 2 < Real.log (5 : ℝ) := by
    have hquarter :=
      Real.le_log_one_add_of_nonneg (x := (1 / 4 : ℝ)) (by norm_num)
    have hlogFiveEq :
        Real.log (5 : ℝ) =
          2 * Real.log 2 + Real.log (1 + (1 / 4 : ℝ)) := by
      calc
        Real.log (5 : ℝ) =
            Real.log ((4 : ℝ) * (5 / 4 : ℝ)) := by norm_num
        _ = Real.log (4 : ℝ) + Real.log (5 / 4 : ℝ) := by
          rw [Real.log_mul (by norm_num) (by norm_num)]
        _ = 2 * Real.log 2 + Real.log (1 + (1 / 4 : ℝ)) := by
          congr 1
          · calc
              Real.log (4 : ℝ) = Real.log ((2 : ℝ) * 2) := by norm_num
              _ = Real.log 2 + Real.log 2 := by
                rw [Real.log_mul (by norm_num) (by norm_num)]
              _ = 2 * Real.log 2 := by ring
          · norm_num
    rw [hlogFiveEq]
    nlinarith [Real.log_two_gt_d9]
  have hlogW : 3 / 2 < Real.log ‖w‖ := by
    exact hlogFive.trans_le
      (Real.log_le_log (by norm_num) hwNorm)
  have hPoleDen : 100 ≤ Complex.normSq (s - 1) := by
    rw [Complex.normSq_apply]
    simp only [sub_re, one_re, sub_im, one_im]
    nlinarith [sq_nonneg (s.re - 1)]
  have hPoleDenPos : 0 < Complex.normSq (s - 1) :=
    lt_of_lt_of_le (by norm_num) hPoleDen
  have hPole :
      -(1 / (s - 1)).re ≤ 1 / 100 := by
    have hEq :
        -(1 / (s - 1)).re =
          (1 - s.re) / Complex.normSq (s - 1) := by
      rw [one_div, Complex.inv_re]
      simp only [sub_re, one_re]
      ring
    rw [hEq, div_le_iff₀ hPoleDenPos]
    nlinarith
  have hwNormSqComplex :
      25 ≤ Complex.normSq w := by
    rw [Complex.normSq_eq_norm_sq]
    exact hwNormSq
  have hwNormSqComplexPos : 0 < Complex.normSq w :=
    lt_of_lt_of_le (by norm_num) hwNormSqComplex
  have hInvCorrectionEq :
      (1 / (2 * w)).re / 2 =
        w.re / (4 * Complex.normSq w) := by
    rw [one_div, Complex.inv_re]
    norm_num [Complex.normSq_mul]
    ring
  have hInvCorrection :
      (1 / (2 * w)).re / 2 ≤ 1 / 80 := by
    rw [hInvCorrectionEq]
    have hden : 0 < 4 * Complex.normSq w := mul_pos (by norm_num) hwNormSqComplexPos
    rw [div_le_iff₀ hden]
    nlinarith
  let R : ℂ := levinsonMontgomeryDigammaStirlingRemainder w
  have hRnorm :
      ‖R‖ ≤ 27 / (64 * ‖w‖ ^ 2) := by
    exact levinsonMontgomery_digamma_stirling_remainder_norm_le hwRe
  have hRsmall : ‖R‖ ≤ 1 / 50 := by
    calc
      ‖R‖ ≤ 27 / (64 * ‖w‖ ^ 2) := hRnorm
      _ ≤ 1 / 50 := by
        have hden : 0 < 64 * ‖w‖ ^ 2 := by positivity
        rw [div_le_iff₀ hden]
        nlinarith
  have hRreal : -R.re / 2 ≤ 1 / 100 := by
    have hre : -R.re ≤ ‖R‖ :=
      (neg_le_abs R.re).trans (Complex.abs_re_le_norm R)
    linarith
  have hdigamma := levinsonMontgomery_digamma_stirling hwRe
  change Complex.digamma w =
      Complex.log w - 1 / (2 * w) + R at hdigamma
  have hterm :
      levinsonMontgomeryLogDerivArchimedeanTerm s =
        -(1 / (s - 1)).re + Real.log Real.pi / 2 -
          Real.log ‖w‖ / 2 + (1 / (2 * w)).re / 2 - R.re / 2 := by
    rw [levinsonMontgomeryLogDerivArchimedeanTerm,
      show s / 2 + 1 = w by rfl, hdigamma]
    simp only [add_re, sub_re, Complex.log_re]
    ring
  rw [hterm]
  linarith

theorem riemannXi_ne_zero_of_re_pos_of_re_lt_one_of_riemannZeta_ne_zero
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hzeta : riemannZeta s ≠ 0) :
    riemannXi s ≠ 0 := by
  have hsZero : s ≠ 0 := by
    intro h
    rw [h] at hs0
    norm_num at hs0
  have hsOne : s ≠ 1 := by
    intro h
    rw [h] at hs1
    norm_num at hs1
  have hgamma : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs0
  have hfactor : s * (s - 1) / 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero hsZero (sub_ne_zero.mpr hsOne)) (by norm_num)
  rw [riemannXi_eq_factor_mul_GammaR_mul_riemannZeta_of_re_pos hs0 hsOne]
  exact mul_ne_zero (mul_ne_zero hfactor hgamma) hzeta

theorem levinsonMontgomeryPairedMass_neg_of_logDeriv_riemannZeta_re_nonneg
    {s : ℂ} (hs0 : 0 < s.re) (hsHalf : s.re < 1 / 2)
    (hsIm : 10 ≤ s.im) (hzeta : riemannZeta s ≠ 0)
    (hlog : 0 ≤ (logDeriv riemannZeta s).re) :
    levinsonMontgomeryPairedZeroMass s < 0 := by
  have hxi :=
    riemannXi_ne_zero_of_re_pos_of_re_lt_one_of_riemannZeta_ne_zero
      hs0 (hsHalf.trans (by norm_num)) hzeta
  have heq :=
    levinsonMontgomery_equation_two_one hs0 hsHalf hzeta
  have hpair :=
    levinsonMontgomery_real_paired_zero_sum_eq hsHalf hxi
  have harch :=
    levinsonMontgomeryLogDerivArchimedeanTerm_neg
      hs0.le hsHalf.le hsIm
  rw [hpair] at heq
  by_contra h
  have hmass : 0 ≤ levinsonMontgomeryPairedZeroMass s :=
    le_of_not_gt h
  have hdelta : 0 < 1 / 2 - s.re := sub_pos.mpr hsHalf
  nlinarith [mul_nonneg hdelta.le hmass]

/-- The interior-witness branch isolated from the later boundary and contour argument. -/
def LevinsonMontgomeryEventuallyNonnegativeLogDerivAtIntegers : Prop :=
  ∃ n0 : ℕ, 10 ≤ n0 ∧ ∀ n : ℕ, n0 ≤ n →
    ∃ sigma : ℝ, 0 < sigma ∧ sigma < 1 / 2 ∧
      riemannZeta (levinsonMontgomeryIntegerPoint sigma n) ≠ 0 ∧
      0 ≤ (logDeriv riemannZeta
        (levinsonMontgomeryIntegerPoint sigma n)).re

theorem levinsonMontgomeryPairedMassNegativeAtIntegers_of_eventuallyNonnegativeLogDeriv
    (hlog : LevinsonMontgomeryEventuallyNonnegativeLogDerivAtIntegers) :
    LevinsonMontgomeryPairedMassNegativeAtIntegers := by
  rcases hlog with ⟨n0, hn0, hlog⟩
  refine ⟨n0, by omega, fun n hn => ?_⟩
  obtain ⟨sigma, hsigma0, hsigmaHalf, hzeta, hnonneg⟩ :=
    hlog n hn
  let s := levinsonMontgomeryIntegerPoint sigma n
  have hsRe0 : 0 < s.re := by
    simpa [s] using hsigma0
  have hsReHalf : s.re < 1 / 2 := by
    simpa [s] using hsigmaHalf
  have hsIm : 10 ≤ s.im := by
    dsimp only [s]
    rw [levinsonMontgomeryIntegerPoint_im]
    exact_mod_cast hn0.trans hn
  have hmass :
      levinsonMontgomeryPairedZeroMass s < 0 :=
    levinsonMontgomeryPairedMass_neg_of_logDeriv_riemannZeta_re_nonneg
      hsRe0 hsReHalf hsIm hzeta hnonneg
  have hxi : riemannXi s ≠ 0 :=
    riemannXi_ne_zero_of_re_pos_of_re_lt_one_of_riemannZeta_ne_zero
      hsRe0 (hsReHalf.trans (by norm_num)) hzeta
  exact ⟨sigma, hsigma0, hsigmaHalf, by simpa [s] using hxi,
    by simpa [s] using hmass⟩

theorem levinsonMontgomeryDenseBranch_of_eventuallyNonnegativeLogDerivAtIntegers
    (hlog : LevinsonMontgomeryEventuallyNonnegativeLogDerivAtIntegers) :
    ∃ T0 : ℝ, ∀ T : ℝ, T0 ≤ T →
      T / 2 < (speiserUpperLeftZetaZeroCount T : ℝ) :=
  levinsonMontgomeryDenseBranch_of_pairedMassNegativeAtIntegers
    (levinsonMontgomeryPairedMassNegativeAtIntegers_of_eventuallyNonnegativeLogDeriv hlog)

end

end LeanLab.Riemann
