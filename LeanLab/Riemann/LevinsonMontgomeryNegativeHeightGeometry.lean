import LeanLab.Riemann.LevinsonMontgomeryCriticalIndentation
import LeanLab.Riemann.LevinsonMontgomeryLeftHalfPlaneWinding

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Negative integer-height geometry in the Levinson--Montgomery contour

This file proves that strict negativity of `Re (zeta'/zeta)` at every nonzero interior point of
an integer-height segment already excludes zeta zeros on that segment. The key is the positive
principal part immediately to the right of a positive-multiplicity zero.
-/

namespace LeanLab.Riemann

open Complex Filter Function Real Set
open scoped Topology

noncomputable section

private theorem eventually_eventuallyEq_nhds_of_eventuallyEq
    {f g : ℂ → ℂ} {z : ℂ} (hfg : f =ᶠ[𝓝 z] g) :
    ∀ᶠ w in 𝓝 z, f =ᶠ[𝓝 w] g := by
  change {w | f w = g w} ∈ 𝓝 z at hfg
  have hinterior : interior {w | f w = g w} ∈ 𝓝 z :=
    interior_mem_nhds.mpr hfg
  filter_upwards [hinterior] with w hw
  change {v | f v = g v} ∈ 𝓝 w
  exact mem_interior_iff_mem_nhds.mp hw

private theorem logDeriv_centered_pow_at
    {rho z : ℂ} {m : ℕ} (_hz : z ≠ rho) :
    logDeriv (fun w : ℂ => (w - rho) ^ m) z = (m : ℂ) / (z - rho) := by
  rw [logDeriv_fun_pow (by fun_prop)]
  have hbase :
      logDeriv (fun w : ℂ => w - rho) z = 1 / (z - rho) := by
    rw [logDeriv_apply]
    simp
  rw [hbase]
  ring_nf

/-- Every actual nontrivial zeta zero has a positive-multiplicity analytic local factorization. -/
theorem exists_riemannZeta_zero_analytic_factor
    {rho : ℂ} (hrho : IsNontrivialZero rho) :
    ∃ (m : ℕ) (h : ℂ → ℂ), 0 < m ∧ AnalyticAt ℂ h rho ∧ h rho ≠ 0 ∧
      riemannZeta =ᶠ[𝓝 rho] fun z => (z - rho) ^ m * h z := by
  obtain ⟨m, g, hm, hg, hgne, hfactorXi⟩ :=
    exists_riemannXi_zero_analytic_factor hrho
  let h : ℂ → ℂ := fun z => g z / riemannXiZetaUnit z
  have hunit := analyticAt_riemannXiZetaUnit_of_isNontrivialZero hrho
  have hunitNe := riemannXiZetaUnit_ne_zero_of_isNontrivialZero hrho
  have hh : AnalyticAt ℂ h rho := by
    exact hg.div hunit hunitNe
  have hhne : h rho ≠ 0 := by
    dsimp [h]
    exact div_ne_zero hgne hunitNe
  have hxiUnit := eventually_riemannXi_eq_unit_mul_riemannZeta hrho
  have hunitEventually := hunit.continuousAt.eventually_ne hunitNe
  have hfactorZeta :
      riemannZeta =ᶠ[𝓝 rho] fun z => (z - rho) ^ m * h z := by
    filter_upwards [hfactorXi, hxiUnit, hunitEventually] with z hxi hunitEq hzUnit
    apply mul_left_cancel₀ hzUnit
    calc
      riemannXiZetaUnit z * riemannZeta z = riemannXi z := hunitEq.symm
      _ = (z - rho) ^ m * g z := hxi
      _ = riemannXiZetaUnit z * ((z - rho) ^ m * h z) := by
        dsimp [h]
        field_simp
  exact ⟨m, h, hm, hh, hhne, hfactorZeta⟩

/-- To the immediate right of a positive-multiplicity analytic zero, the real logarithmic
derivative is positive. The analytic residual is locally bounded while `m / delta` diverges. -/
theorem exists_logDeriv_re_pos_right_of_analytic_zero_factor
    {f h : ℂ → ℂ} {rho : ℂ} {m : ℕ}
    (hm : 0 < m) (hh : AnalyticAt ℂ h rho) (hhne : h rho ≠ 0)
    (hfactor : f =ᶠ[𝓝 rho] fun z => (z - rho) ^ m * h z)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ delta < eta ∧
      f (rho + delta) ≠ 0 ∧ (logDeriv f (rho + delta)).re > 0 := by
  let r0 : ℝ := (logDeriv h rho).re
  let A : ℝ := |r0| + 2
  have hA : 0 < A := by
    dsimp only [A]
    positivity
  have hlogCont :=
    levinsonMontgomery_continuousAt_logDeriv_of_analyticAt_of_ne_zero hh hhne
  have hlogReCont :
      ContinuousAt (fun z => (logDeriv h z).re) rho :=
    Complex.continuous_re.continuousAt.comp hlogCont
  have hresEventually :
      ∀ᶠ z in 𝓝 rho, r0 - 1 < (logDeriv h z).re :=
    hlogReCont.eventually (Ioi_mem_nhds (by dsimp only [r0]; linarith))
  have hhEventually := hh.continuousAt.eventually_ne hhne
  have hhAnalyticEventually := hh.eventually_analyticAt
  have hfactorAt := eventually_eventuallyEq_nhds_of_eventuallyEq hfactor
  have hevent :
      ∀ᶠ z in 𝓝 rho,
        r0 - 1 < (logDeriv h z).re ∧ h z ≠ 0 ∧ AnalyticAt ℂ h z ∧
          f =ᶠ[𝓝 z] fun w => (w - rho) ^ m * h w := by
    filter_upwards [hresEventually, hhEventually, hhAnalyticEventually, hfactorAt] with
      z hres hzH hzAnalytic hlocal
    exact ⟨hres, hzH, hzAnalytic, hlocal⟩
  change {z | r0 - 1 < (logDeriv h z).re ∧ h z ≠ 0 ∧ AnalyticAt ℂ h z ∧
    f =ᶠ[𝓝 z] fun w => (w - rho) ^ m * h w} ∈ 𝓝 rho at hevent
  rcases Metric.mem_nhds_iff.mp hevent with ⟨epsilon, hepsilon, hball⟩
  let upper : ℝ := min epsilon (min eta ((m : ℝ) / A))
  have hmReal : (0 : ℝ) < m := by exact_mod_cast hm
  have hupper : 0 < upper := by
    dsimp only [upper]
    exact lt_min hepsilon (lt_min heta (div_pos hmReal hA))
  let delta : ℝ := upper / 2
  have hdelta : 0 < delta := by
    dsimp only [delta]
    linarith
  have hdeltaUpper : delta < upper := by
    dsimp only [delta]
    linarith
  have hdeltaEpsilon : delta < epsilon :=
    hdeltaUpper.trans_le (min_le_left _ _)
  have hdeltaEta : delta < eta :=
    hdeltaUpper.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hdeltaMA : delta < (m : ℝ) / A :=
    hdeltaUpper.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  let z : ℂ := rho + delta
  have hzBall : z ∈ Metric.ball rho epsilon := by
    rw [Metric.mem_ball]
    simpa [z, Real.norm_eq_abs, abs_of_pos hdelta] using hdeltaEpsilon
  have hzData := hball hzBall
  have hz : z ≠ rho := by
    intro hzEq
    have hre := congrArg Complex.re hzEq
    simp only [z, add_re, ofReal_re] at hre
    linarith
  have hzBase : z - rho ≠ 0 := sub_ne_zero.mpr hz
  have hzPow : (z - rho) ^ m ≠ 0 := pow_ne_zero m hzBase
  have hfactorValue : f z = (z - rho) ^ m * h z :=
    hzData.2.2.2.self_of_nhds
  have hfz : f z ≠ 0 := by
    rw [hfactorValue]
    exact mul_ne_zero hzPow hzData.2.1
  have hlogCongr :
      logDeriv f z =
        logDeriv (fun w : ℂ => (w - rho) ^ m * h w) z := by
    rw [logDeriv_apply, logDeriv_apply, hzData.2.2.2.deriv_eq, hfactorValue]
  have hlogMul :=
    logDeriv_mul (f := fun w : ℂ => (w - rho) ^ m) (g := h)
      z hzPow hzData.2.1 (by fun_prop) hzData.2.2.1.differentiableAt
  have hlogFormula :
      logDeriv f z = (m : ℂ) / (z - rho) + logDeriv h z := by
    rw [hlogCongr, hlogMul, logDeriv_centered_pow_at hz]
  have hzSub : z - rho = (delta : ℂ) := by
    simp [z]
  have hprincipal :
      (((m : ℂ) / (z - rho)).re) = (m : ℝ) / delta := by
    rw [hzSub]
    norm_num
  have hprincipalLarge : A < (m : ℝ) / delta := by
    apply (lt_div_iff₀ hdelta).2
    have hmul : delta * A < (m : ℝ) :=
      (lt_div_iff₀ hA).mp hdeltaMA
    nlinarith
  have hr0Lower : -|r0| ≤ r0 := neg_abs_le r0
  have hpositive : 0 < (logDeriv f z).re := by
    rw [hlogFormula]
    simp only [add_re, hprincipal]
    dsimp only [A] at hprincipalLarge
    linarith [hzData.1]
  refine ⟨delta, hdelta, hdeltaEta, ?_, ?_⟩
  · simpa [z] using hfz
  · simpa [z] using hpositive

/-- Strict negativity at every nonzero point of an integer-height open segment excludes all
actual zeta zeros on that segment. -/
theorem levinsonMontgomery_negativeIntegerHeight_interiorZeroFree
    {n : ℕ} (hn : 10 ≤ n)
    (hneg : LevinsonMontgomeryNegativeLogDerivAtIntegerHeight n) :
    ∀ sigma : ℝ, 0 < sigma → sigma < 1 / 2 →
      riemannZeta (levinsonMontgomeryIntegerPoint sigma n) ≠ 0 := by
  intro sigma hsigma0 hsigmaHalf hzero
  let rho : ℂ := levinsonMontgomeryIntegerPoint sigma n
  have hnPos : 0 < n := (by omega : 0 < n)
  have hrhoStrip : rho ∈ speiserUpperLeftStrip := by
    change 0 < rho.im ∧ 0 < rho.re ∧ rho.re < 1 / 2
    simp only [rho, levinsonMontgomeryIntegerPoint_im,
      levinsonMontgomeryIntegerPoint_re]
    exact ⟨by exact_mod_cast hnPos, hsigma0, hsigmaHalf⟩
  have hrhoZero : IsNontrivialZero rho :=
    isNontrivialZero_of_mem_speiserUpperLeftStrip hrhoStrip (by simpa [rho] using hzero)
  obtain ⟨m, h, hm, hh, hhne, hfactor⟩ :=
    exists_riemannZeta_zero_analytic_factor hrhoZero
  have heta : 0 < (1 / 2 : ℝ) - sigma := sub_pos.mpr hsigmaHalf
  obtain ⟨delta, hdelta, hdeltaEta, hzeta, hpositive⟩ :=
    exists_logDeriv_re_pos_right_of_analytic_zero_factor
      hm hh hhne hfactor heta
  have hpoint :
      rho + (delta : ℂ) =
        levinsonMontgomeryIntegerPoint (sigma + delta) n := by
    apply Complex.ext
    · simp [rho, levinsonMontgomeryIntegerPoint]
    · simp [rho, levinsonMontgomeryIntegerPoint]
  have hzeta' :
      riemannZeta (levinsonMontgomeryIntegerPoint (sigma + delta) n) ≠ 0 := by
    rw [← hpoint]
    exact hzeta
  have hnegative :=
    hneg (sigma + delta) (by linarith) (by linarith) hzeta'
  rw [← hpoint] at hnegative
  linarith

/-- At a negative integer height the actual ratio is strictly left-pointing and both zeta and its
derivative are nonzero throughout the open horizontal segment. -/
theorem levinsonMontgomery_negativeIntegerHeight_interiorGeometry
    {n : ℕ} (hn : 10 ≤ n)
    (hneg : LevinsonMontgomeryNegativeLogDerivAtIntegerHeight n) :
    ∀ sigma : ℝ, 0 < sigma → sigma < 1 / 2 →
      riemannZeta (levinsonMontgomeryIntegerPoint sigma n) ≠ 0 ∧
      deriv riemannZeta (levinsonMontgomeryIntegerPoint sigma n) ≠ 0 ∧
      (speiserZetaDerivRatio
        (levinsonMontgomeryIntegerPoint sigma n)).re < 0 := by
  intro sigma hsigma0 hsigmaHalf
  have hzeta :=
    levinsonMontgomery_negativeIntegerHeight_interiorZeroFree
      hn hneg sigma hsigma0 hsigmaHalf
  have hlog := hneg sigma hsigma0 hsigmaHalf hzeta
  have hderiv :
      deriv riemannZeta (levinsonMontgomeryIntegerPoint sigma n) ≠ 0 := by
    intro hzero
    rw [logDeriv_apply, hzero, zero_div, Complex.zero_re] at hlog
    exact (lt_irrefl 0) hlog
  refine ⟨hzeta, hderiv, ?_⟩
  simpa only [speiserZetaDerivRatio, logDeriv_apply] using hlog

/-- The actual source geometry at a negative integer height. The half-open segment is strictly
left-pointing. At the critical endpoint either the same is true or an actual multiplicity-aware
left indentation is available. -/
def LevinsonMontgomeryNegativeHeightGeometry (n : ℕ) : Prop :=
  (∀ sigma : ℝ, 0 ≤ sigma → sigma < 1 / 2 →
    riemannZeta (levinsonMontgomeryIntegerPoint sigma n) ≠ 0 ∧
    deriv riemannZeta (levinsonMontgomeryIntegerPoint sigma n) ≠ 0 ∧
    (speiserZetaDerivRatio
      (levinsonMontgomeryIntegerPoint sigma n)).re < 0) ∧
  let rho : ℂ := (1 / 2 : ℂ) + (n : ℂ) * I
  (riemannZeta rho ≠ 0 ∧ deriv riemannZeta rho ≠ 0 ∧
      (speiserZetaDerivRatio rho).re < 0) ∨
    (IsNontrivialZero rho ∧
      ∃ r : ℝ, 0 < r ∧
        ∀ z : ℂ, dist z rho = r → z.re ≤ 1 / 2 →
          riemannZeta z ≠ 0 ∧ deriv riemannZeta z ≠ 0 ∧
            (speiserZetaDerivRatio z).re < 0)

/-- A negative integer-height witness supplies the complete source horizontal geometry, including
the critical-endpoint indentation alternative. -/
theorem levinsonMontgomery_negativeHeightGeometry_of_negativeLogDeriv
    {n : ℕ} (hn : 10 < n)
    (hneg : LevinsonMontgomeryNegativeLogDerivAtIntegerHeight n) :
    LevinsonMontgomeryNegativeHeightGeometry n := by
  have hnWeak : 10 ≤ n := hn.le
  have hnReal : (10 : ℝ) < n := by exact_mod_cast hn
  constructor
  · intro sigma hsigma0 hsigmaHalf
    rcases hsigma0.eq_or_lt with rfl | hsigmaPos
    · let s : ℂ := levinsonMontgomeryIntegerPoint 0 n
      have hsRe : s.re = 0 := by simp [s]
      have hsIm : 10 ≤ s.im := by
        simp only [s, levinsonMontgomeryIntegerPoint_im]
        exact_mod_cast hnWeak
      have hleft :=
        levinsonMontgomery_logDeriv_riemannZeta_re_neg_on_left_boundary hsRe hsIm
      have hderiv : deriv riemannZeta s ≠ 0 := by
        intro hzero
        have hnegLeft := hleft.2
        rw [logDeriv_apply, hzero, zero_div, Complex.zero_re] at hnegLeft
        exact (lt_irrefl 0) hnegLeft
      refine ⟨by simpa [s] using hleft.1, by simpa [s] using hderiv, ?_⟩
      simpa only [s, speiserZetaDerivRatio, logDeriv_apply] using hleft.2
    · exact
        levinsonMontgomery_negativeIntegerHeight_interiorGeometry
          hnWeak hneg sigma hsigmaPos hsigmaHalf
  · let rho : ℂ := (1 / 2 : ℂ) + (n : ℂ) * I
    by_cases hzeta : riemannZeta rho = 0
    · right
      have hrho : IsNontrivialZero rho := by
        refine ⟨hzeta, ?_, ?_⟩
        · intro htrivial
          rcases htrivial with ⟨k, hk⟩
          have him := congrArg Complex.im hk
          simp [rho] at him
          linarith
        · intro hrhoOne
          have him := congrArg Complex.im hrhoOne
          simp [rho] at him
          linarith
      have hrhoRe : rho.re = 1 / 2 := by simp [rho]
      have hrhoIm : 10 < rho.im := by simpa [rho] using hnReal
      obtain ⟨r, hr, hcircle⟩ :=
        exists_levinsonMontgomery_negative_left_semicircle hrho hrhoRe hrhoIm
      refine ⟨hrho, r, hr, ?_⟩
      intro z hzDist hzLeft
      have hdata := hcircle z hzDist hzLeft
      have hderiv : deriv riemannZeta z ≠ 0 := by
        intro hzero
        have hnegative := hdata.2
        rw [logDeriv_apply, hzero, zero_div, Complex.zero_re] at hnegative
        exact (lt_irrefl 0) hnegative
      refine ⟨hdata.1, hderiv, ?_⟩
      simpa only [speiserZetaDerivRatio, logDeriv_apply] using hdata.2
    · left
      have hrhoRe : rho.re = 1 / 2 := by simp [rho]
      have hrhoIm : 10 ≤ rho.im := by
        have hnWeakReal : (10 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnWeak
        simpa [rho] using hnWeakReal
      have hnegative :=
        levinsonMontgomery_logDeriv_riemannZeta_re_neg_on_critical_boundary
          hrhoRe hrhoIm hzeta
      have hderiv : deriv riemannZeta rho ≠ 0 := by
        intro hzero
        rw [logDeriv_apply, hzero, zero_div, Complex.zero_re] at hnegative
        exact (lt_irrefl 0) hnegative
      refine ⟨hzeta, hderiv, ?_⟩
      simpa only [speiserZetaDerivRatio, logDeriv_apply] using hnegative

/-- Cofinal availability of actual negative-height source geometry. -/
def LevinsonMontgomeryCofinalNegativeHeightGeometry : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 10 < n ∧
    LevinsonMontgomeryNegativeHeightGeometry n

theorem levinsonMontgomeryCofinalNegativeHeightGeometry_of_cofinallyNegative
    (hcofinal : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      LevinsonMontgomeryNegativeLogDerivAtIntegerHeight n) :
    LevinsonMontgomeryCofinalNegativeHeightGeometry := by
  intro N
  obtain ⟨n, hn, hneg⟩ := hcofinal (max N 11)
  have hnN : N ≤ n := (le_max_left N 11).trans hn
  have hnLarge : 10 < n := by
    have : 11 ≤ n := (le_max_right N 11).trans hn
    omega
  exact ⟨n, hnN, hnLarge,
    levinsonMontgomery_negativeHeightGeometry_of_negativeLogDeriv hnLarge hneg⟩

/-- The actual source branch split: either strict-negative/indented contour heights occur
cofinally, or the already compiled upper-left zeta-zero count is eventually linearly dense. -/
theorem levinsonMontgomery_negativeGeometry_or_dense_dichotomy :
    LevinsonMontgomeryCofinalNegativeHeightGeometry ∨
      ∃ T0 : ℝ, ∀ T : ℝ, T0 ≤ T →
        T / 2 < (speiserUpperLeftZetaZeroCount T : ℝ) := by
  rcases levinsonMontgomery_integer_height_logDeriv_dichotomy with
    hcofinal | heventual
  · left
    exact
      levinsonMontgomeryCofinalNegativeHeightGeometry_of_cofinallyNegative hcofinal
  · right
    exact
      levinsonMontgomeryDenseBranch_of_eventuallyNonnegativeLogDerivAtIntegers
        heventual

end

end LeanLab.Riemann
