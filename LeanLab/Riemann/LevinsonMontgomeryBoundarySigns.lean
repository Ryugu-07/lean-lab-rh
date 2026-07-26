import LeanLab.Riemann.LevinsonMontgomeryLogDerivMassBridge

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Levinson--Montgomery boundary signs

This file extends the logarithmic-derivative identity to the vertical boundaries used in the
Levinson--Montgomery contour argument. It also isolates the exact integer-height alternative
that feeds the already compiled dense zero-count branch.
-/

namespace LeanLab.Riemann

open Complex Filter Function Real Set
open scoped BigOperators ComplexConjugate Real Topology

noncomputable section

private theorem levinsonMontgomery_ne_pairedZero_of_riemannXi_ne_zero
    {s : ℂ} (hxi : riemannXi s ≠ 0) (p : RiemannXiDivisorZeroIndex) :
    s ≠ riemannXiDivisorZeroValue p := by
  intro h
  apply hxi
  rw [h]
  exact riemannXi_eq_zero_of_isNontrivialZero
    (riemannXiDivisorZeroIndex_val_isNontrivialZero p)

theorem differentiableAt_GammaR_of_not_neg_even
    {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(2 * m)) :
    DifferentiableAt ℂ Gammaℝ s := by
  change DifferentiableAt ℂ
    (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Gamma (z / 2)) s
  refine ((differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow ?_).mul ?_
  · exact Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero)
  · refine (differentiableAt_Gamma (s / 2) ?_).comp s
      (differentiableAt_id.div_const (2 : ℂ))
    intro m hm
    apply hs m
    calc
      s = (s / 2) * 2 := by ring
      _ = (-m : ℂ) * 2 := by rw [hm]
      _ = -(2 * (m : ℂ)) := by ring

theorem GammaR_ne_zero_of_not_neg_even
    {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(2 * m)) :
    Gammaℝ s ≠ 0 := by
  rw [Ne, Gammaℝ_eq_zero_iff]
  simpa only [not_exists] using hs

theorem logDeriv_GammaR_eq_digamma_of_not_neg_even
    {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(2 * m)) :
    logDeriv Gammaℝ s =
      -(Real.log Real.pi : ℂ) / 2 + digamma (s / 2) / 2 := by
  let A : ℂ → ℂ := fun z => (Real.pi : ℂ) ^ (-z / 2)
  let B : ℂ → ℂ := fun z => Gamma (z / 2)
  have hA : A s ≠ 0 := by
    dsimp [A]
    exact Complex.cpow_ne_zero_iff.mpr
      (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hnotpole : ∀ m : ℕ, s / 2 ≠ -m := by
    intro m hm
    apply hs m
    calc
      s = (s / 2) * 2 := by ring
      _ = (-m : ℂ) * 2 := by rw [hm]
      _ = -(2 * (m : ℂ)) := by ring
  have hGammaDiff : DifferentiableAt ℂ Gamma (s / 2) :=
    differentiableAt_Gamma (s / 2) hnotpole
  have hB : B s ≠ 0 := by
    dsimp [B]
    exact Gamma_ne_zero hnotpole
  have hAdiff : DifferentiableAt ℂ A s := by
    dsimp [A]
    exact ((differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow
      (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero)))
  have hHalfDiff : DifferentiableAt ℂ (fun z : ℂ => z / 2) s :=
    differentiableAt_id.div_const (2 : ℂ)
  have hBdiff : DifferentiableAt ℂ B s := by
    dsimp [B]
    exact hGammaDiff.comp s (by fun_prop)
  have hderivNegHalf : deriv (fun z : ℂ => -z / 2) s = -1 / 2 := by
    simp
  have hderivHalf : deriv (fun z : ℂ => z / 2) s = 1 / 2 := by
    simp
  have hlogA : logDeriv A s = -(Real.log Real.pi : ℂ) / 2 := by
    rw [logDeriv_apply]
    change deriv (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s / A s = _
    rw [Complex.deriv_const_cpow (by fun_prop), hderivNegHalf]
    change Complex.log (Real.pi : ℂ) * (-1 / 2) * A s / A s = _
    rw [mul_div_cancel_right₀ _ hA]
    rw [← Complex.ofReal_log Real.pi_pos.le]
    ring
  have hlogB : logDeriv B s = digamma (s / 2) / 2 := by
    change logDeriv (Gamma ∘ fun z : ℂ => z / 2) s = _
    rw [logDeriv_comp (f := Gamma) (g := fun z : ℂ => z / 2) (x := s)
      hGammaDiff hHalfDiff, hderivHalf, ← digamma_def]
    ring
  change logDeriv (fun z : ℂ => A z * B z) s = _
  rw [logDeriv_mul s hA hB hAdiff hBdiff, hlogA, hlogB]

theorem riemannXi_eq_factor_mul_GammaR_mul_riemannZeta_of_nonpole
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hgamma : Gammaℝ s ≠ 0) :
    riemannXi s = s * (s - 1) / 2 * Gammaℝ s * riemannZeta s := by
  rw [riemannXi_eq_mul_completedRiemannZeta hs0 hs1,
    riemannZeta_def_of_ne_zero hs0]
  field_simp

theorem logDeriv_riemannXi_eq_poles_archimedean_add_riemannZeta_of_nonpole
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hnotpole : ∀ m : ℕ, s ≠ -(2 * m))
    (hzeta : riemannZeta s ≠ 0) :
    logDeriv riemannXi s =
      1 / s + 1 / (s - 1) + logDeriv Gammaℝ s +
        logDeriv riemannZeta s := by
  have hgamma : Gammaℝ s ≠ 0 :=
    GammaR_ne_zero_of_not_neg_even hnotpole
  let A : ℂ → ℂ := fun z => z * (z - 1) / 2
  have hA : A s ≠ 0 := by
    dsimp [A]
    exact div_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) (by norm_num)
  have hdA : DifferentiableAt ℂ A s := by
    dsimp [A]
    fun_prop
  have hdGamma : DifferentiableAt ℂ Gammaℝ s :=
    differentiableAt_GammaR_of_not_neg_even hnotpole
  have hdZeta : DifferentiableAt ℂ riemannZeta s :=
    differentiableAt_riemannZeta hs1
  have hAGamma : A s * Gammaℝ s ≠ 0 := mul_ne_zero hA hgamma
  have hxi : riemannXi =ᶠ[𝓝 s]
      fun z => A z * Gammaℝ z * riemannZeta z := by
    filter_upwards [continuousAt_id.eventually_ne hs0,
      continuousAt_id.eventually_ne hs1,
      hdGamma.continuousAt.eventually_ne hgamma] with z hz0 hz1 hzGamma
    have hz0' : z ≠ 0 := by simpa using hz0
    have hz1' : z ≠ 1 := by simpa using hz1
    simpa [A] using
      riemannXi_eq_factor_mul_GammaR_mul_riemannZeta_of_nonpole
        hz0' hz1' hzGamma
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

private theorem levinsonMontgomery_not_neg_even_of_im_pos
    {s : ℂ} (hsIm : 0 < s.im) :
    ∀ m : ℕ, s ≠ -(2 * m) := by
  intro m h
  have him : s.im = 0 := by simpa using congrArg Complex.im h
  linarith

theorem levinsonMontgomery_equation_two_one_closed
    {s : ℂ} (_hs0 : 0 ≤ s.re) (_hsHalf : s.re ≤ 1 / 2)
    (hsIm : 10 ≤ s.im) (hzeta : riemannZeta s ≠ 0) :
    (logDeriv riemannZeta s).re =
      levinsonMontgomeryLogDerivArchimedeanTerm s +
        levinsonMontgomeryRealPairedZeroSum s := by
  have hsImPos : 0 < s.im := by linarith
  have hsZero : s ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp only [zero_im] at him
    linarith
  have hsOne : s ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp only [one_im] at him
    linarith
  have hnotpole : ∀ m : ℕ, s ≠ -(2 * m) :=
    levinsonMontgomery_not_neg_even_of_im_pos hsImPos
  have hgamma : Gammaℝ s ≠ 0 :=
    GammaR_ne_zero_of_not_neg_even hnotpole
  have hxiValue :=
    riemannXi_eq_factor_mul_GammaR_mul_riemannZeta_of_nonpole
      hsZero hsOne hgamma
  have hfactor : s * (s - 1) / 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero hsZero (sub_ne_zero.mpr hsOne)) (by norm_num)
  have hxi : riemannXi s ≠ 0 := by
    rw [hxiValue]
    exact mul_ne_zero (mul_ne_zero hfactor hgamma) hzeta
  have hxiLog :=
    logDeriv_riemannXi_eq_poles_archimedean_add_riemannZeta_of_nonpole
      hsZero hsOne hnotpole hzeta
  have hgammaLog :=
    logDeriv_GammaR_eq_digamma_of_not_neg_even hnotpole
  have hnotpoleHalf : ∀ m : ℕ, s / 2 ≠ -m := by
    intro m hm
    apply hnotpole m
    calc
      s = (s / 2) * 2 := by ring
      _ = (-m : ℂ) * 2 := by rw [hm]
      _ = -(2 * (m : ℂ)) := by ring
  have hpsi := Complex.digamma_apply_add_one (s / 2) hnotpoleHalf
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

theorem levinsonMontgomeryRealPairedZeroSum_eq_zero_of_re_eq_half
    {s : ℂ} (hsRe : s.re = 1 / 2) (hxi : riemannXi s ≠ 0) :
    levinsonMontgomeryRealPairedZeroSum s = 0 := by
  rw [levinsonMontgomeryRealPairedZeroSum]
  calc
    (∑' p : RiemannXiDivisorZeroIndex,
        levinsonMontgomeryPairedReciprocalTerm s p) =
        ∑' _p : RiemannXiDivisorZeroIndex, (0 : ℝ) := by
      apply tsum_congr
      intro p
      rw [levinsonMontgomeryPairedReciprocalTerm_eq s p
        (levinsonMontgomery_ne_pairedZero_of_riemannXi_ne_zero hxi p)
        (levinsonMontgomery_ne_pairedZero_of_riemannXi_ne_zero hxi
          (levinsonMontgomeryPairedZeroEquiv p))]
      rw [hsRe]
      norm_num
    _ = 0 := tsum_zero

theorem levinsonMontgomeryPairedKernel_nonneg_of_re_eq_zero
    {s : ℂ} (hsRe : s.re = 0) (hxi : riemannXi s ≠ 0)
    (p : RiemannXiDivisorZeroIndex) :
    0 ≤ levinsonMontgomeryPairedKernel s p := by
  let rho := riemannXiDivisorZeroValue p
  have hrhoZero : IsNontrivialZero rho :=
    riemannXiDivisorZeroIndex_val_isNontrivialZero p
  have hrhoPos : 0 < rho.re := speiser_nontrivial_zero_re_pos hrhoZero
  have hrhoLt : rho.re < 1 := nontrivial_zero_re_lt_one hrhoZero
  have hrhoProd : rho.re * (rho.re - 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hrhoPos.le (sub_nonpos.mpr hrhoLt.le)
  have hnum :
      0 ≤ (s.im - rho.im) ^ 2 + (s.re - 1 / 2) ^ 2 -
        (rho.re - 1 / 2) ^ 2 := by
    rw [hsRe]
    norm_num
    nlinarith [sq_nonneg (s.im - rho.im), hrhoProd]
  have hp := levinsonMontgomery_ne_pairedZero_of_riemannXi_ne_zero hxi p
  have hq := levinsonMontgomery_ne_pairedZero_of_riemannXi_ne_zero hxi
    (levinsonMontgomeryPairedZeroEquiv p)
  have hden :
      0 ≤ Complex.normSq (s - rho) *
        Complex.normSq (s - riemannXiDivisorZeroValue
          (levinsonMontgomeryPairedZeroEquiv p)) :=
    (mul_pos (Complex.normSq_pos.mpr (sub_ne_zero.mpr hp))
      (Complex.normSq_pos.mpr (sub_ne_zero.mpr hq))).le
  simpa [levinsonMontgomeryPairedKernel, rho] using div_nonneg hnum hden

theorem levinsonMontgomeryRealPairedZeroSum_nonpos_of_re_eq_zero
    {s : ℂ} (hsRe : s.re = 0) (hxi : riemannXi s ≠ 0) :
    levinsonMontgomeryRealPairedZeroSum s ≤ 0 := by
  rw [levinsonMontgomeryRealPairedZeroSum]
  apply tsum_nonpos
  intro p
  rw [levinsonMontgomeryPairedReciprocalTerm_eq s p
    (levinsonMontgomery_ne_pairedZero_of_riemannXi_ne_zero hxi p)
    (levinsonMontgomery_ne_pairedZero_of_riemannXi_ne_zero hxi
      (levinsonMontgomeryPairedZeroEquiv p))]
  have hkernel := levinsonMontgomeryPairedKernel_nonneg_of_re_eq_zero hsRe hxi p
  rw [hsRe]
  norm_num
  linarith

theorem levinsonMontgomery_logDeriv_riemannZeta_re_neg_on_left_boundary
    {s : ℂ} (hsRe : s.re = 0) (hsIm : 10 ≤ s.im) :
    riemannZeta s ≠ 0 ∧ (logDeriv riemannZeta s).re < 0 := by
  have hsImPos : 0 < s.im := by linarith
  have hsZero : s ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp only [zero_im] at him
    linarith
  have hsOne : s ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp only [one_im] at him
    linarith
  have hnotpole : ∀ m : ℕ, s ≠ -(2 * m) :=
    levinsonMontgomery_not_neg_even_of_im_pos hsImPos
  have hgamma : Gammaℝ s ≠ 0 :=
    GammaR_ne_zero_of_not_neg_even hnotpole
  have hxi : riemannXi s ≠ 0 := by
    intro hzero
    have hsNontrivial : IsNontrivialZero s :=
      (isNontrivialZero_iff_riemannXi_eq_zero s).2 hzero
    have hsRePos := speiser_nontrivial_zero_re_pos hsNontrivial
    linarith
  have hxiValue :=
    riemannXi_eq_factor_mul_GammaR_mul_riemannZeta_of_nonpole
      hsZero hsOne hgamma
  have hzeta : riemannZeta s ≠ 0 := by
    intro hzeta
    apply hxi
    rw [hxiValue, hzeta]
    ring
  refine ⟨hzeta, ?_⟩
  have hs0 : 0 ≤ s.re := by rw [hsRe]
  have hsHalf : s.re ≤ 1 / 2 := by rw [hsRe]; norm_num
  have heq :=
    levinsonMontgomery_equation_two_one_closed hs0 hsHalf hsIm hzeta
  have hpair :=
    levinsonMontgomeryRealPairedZeroSum_nonpos_of_re_eq_zero hsRe hxi
  have harch :=
    levinsonMontgomeryLogDerivArchimedeanTerm_neg hs0 hsHalf hsIm
  rw [heq]
  linarith

theorem levinsonMontgomery_logDeriv_riemannZeta_re_neg_on_critical_boundary
    {s : ℂ} (hsRe : s.re = 1 / 2) (hsIm : 10 ≤ s.im)
    (hzeta : riemannZeta s ≠ 0) :
    (logDeriv riemannZeta s).re < 0 := by
  have hs0 : 0 ≤ s.re := by rw [hsRe]; norm_num
  have hs0Strict : 0 < s.re := by rw [hsRe]; norm_num
  have hsHalf : s.re ≤ 1 / 2 := by rw [hsRe]
  have hsOne : s.re < 1 := by rw [hsRe]; norm_num
  have hxi :=
    riemannXi_ne_zero_of_re_pos_of_re_lt_one_of_riemannZeta_ne_zero
      hs0Strict hsOne hzeta
  have heq :=
    levinsonMontgomery_equation_two_one_closed hs0 hsHalf hsIm hzeta
  have hpair :=
    levinsonMontgomeryRealPairedZeroSum_eq_zero_of_re_eq_half hsRe hxi
  have harch :=
    levinsonMontgomeryLogDerivArchimedeanTerm_neg hs0 hsHalf hsIm
  rw [heq, hpair, add_zero]
  exact harch

/-- Strict negativity at every zero-free interior point of one integer height. -/
def LevinsonMontgomeryNegativeLogDerivAtIntegerHeight (n : ℕ) : Prop :=
  ∀ sigma : ℝ, 0 < sigma → sigma < 1 / 2 →
    riemannZeta (levinsonMontgomeryIntegerPoint sigma n) ≠ 0 →
    (logDeriv riemannZeta
      (levinsonMontgomeryIntegerPoint sigma n)).re < 0

theorem levinsonMontgomery_integer_height_logDeriv_dichotomy :
    (∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      LevinsonMontgomeryNegativeLogDerivAtIntegerHeight n) ∨
    LevinsonMontgomeryEventuallyNonnegativeLogDerivAtIntegers := by
  classical
  by_cases hcofinal : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      LevinsonMontgomeryNegativeLogDerivAtIntegerHeight n
  · exact Or.inl hcofinal
  · right
    push Not at hcofinal
    obtain ⟨N, hN⟩ := hcofinal
    let n0 := max 10 N
    refine ⟨n0, Nat.le_max_left 10 N, fun n hn => ?_⟩
    have hNn : N ≤ n := (Nat.le_max_right 10 N).trans hn
    have hfail := hN n hNn
    rw [LevinsonMontgomeryNegativeLogDerivAtIntegerHeight] at hfail
    push Not at hfail
    exact hfail

theorem levinsonMontgomeryDenseBranch_of_not_cofinallyNegativeLogDerivAtIntegers
    (h : ¬(∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      LevinsonMontgomeryNegativeLogDerivAtIntegerHeight n)) :
    ∃ T0 : ℝ, ∀ T : ℝ, T0 ≤ T →
      T / 2 < (speiserUpperLeftZetaZeroCount T : ℝ) := by
  rcases levinsonMontgomery_integer_height_logDeriv_dichotomy with
    hcofinal | heventual
  · exact (h hcofinal).elim
  · exact
      levinsonMontgomeryDenseBranch_of_eventuallyNonnegativeLogDerivAtIntegers
        heventual

/-- Local analytic factorization of xi at an actual nontrivial zero, retaining multiplicity. -/
theorem exists_riemannXi_zero_analytic_factor
    {rho : ℂ} (hrho : IsNontrivialZero rho) :
    ∃ (m : ℕ) (g : ℂ → ℂ), 0 < m ∧ AnalyticAt ℂ g rho ∧ g rho ≠ 0 ∧
      riemannXi =ᶠ[𝓝 rho] fun z => (z - rho) ^ m * g z := by
  have hanalytic : AnalyticAt ℂ riemannXi rho := analyticAt_riemannXi rho
  have hfinite := analyticOrderAt_riemannXi_ne_top rho
  let m := riemannXiZeroMultiplicity rho
  have hm : 0 < m := (riemannXiZeroMultiplicity_pos_iff rho).2 hrho
  obtain ⟨g, hganalytic, hgzero, hfactor⟩ :=
    (hanalytic.analyticOrderNatAt_eq_iff hfinite).mp (show m = m from rfl)
  exact ⟨m, g, hm, hganalytic, hgzero, hfactor⟩

/-- The analytic residual logarithmic derivative in the local zero factorization is continuous. -/
theorem levinsonMontgomery_continuousAt_logDeriv_of_analyticAt_of_ne_zero
    {g : ℂ → ℂ} {rho : ℂ} (hg : AnalyticAt ℂ g rho) (hgne : g rho ≠ 0) :
    ContinuousAt (logDeriv g) rho := by
  change ContinuousAt (deriv g / g) rho
  exact (hg.deriv.div hg hgne).continuousAt

/-- The multiplicity pole itself points strictly left on the left side of its zero. -/
theorem levinsonMontgomery_principalZeroTerm_re_neg
    {rho z : ℂ} {m : ℕ} (hm : 0 < m) (hz : z ≠ rho)
    (hleft : z.re < rho.re) :
    (((m : ℂ) / (z - rho)).re) < 0 := by
  have hmReal : (0 : ℝ) < m := by exact_mod_cast hm
  have hden : 0 < Complex.normSq (z - rho) :=
    Complex.normSq_pos.mpr (sub_ne_zero.mpr hz)
  rw [div_eq_mul_inv]
  simp only [mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul,
    sub_zero, inv_re, sub_re]
  simpa [mul_div_assoc] using
    div_neg_of_neg_of_pos
      (mul_neg_of_pos_of_neg hmReal (sub_neg.mpr hleft)) hden

end

end LeanLab.Riemann
