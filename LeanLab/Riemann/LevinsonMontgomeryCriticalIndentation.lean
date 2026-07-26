import LeanLab.Riemann.LevinsonMontgomeryBoundarySigns
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Levinson--Montgomery critical-zero indentations

This file formalizes the local sign mechanism on left indentations around critical-line zeros.
-/

namespace LeanLab

namespace Riemann

open scoped ComplexConjugate Topology

open Complex Filter Set

noncomputable section

theorem levinsonMontgomery_logDeriv_riemannXi_re_eq_zero_on_criticalLine
    {s : ℂ} (hsRe : s.re = 1 / 2) (hxi : riemannXi s ≠ 0) :
    (logDeriv riemannXi s).re = 0 := by
  rw [← levinsonMontgomeryRealPairedZeroSum_eq_logDeriv_riemannXi_re hxi]
  exact levinsonMontgomeryRealPairedZeroSum_eq_zero_of_re_eq_half hsRe hxi

theorem riemannXi_one_sub_conj (z : ℂ) :
    riemannXi (1 - conj z) = conj (riemannXi z) := by
  rw [riemannXi_one_sub, riemannXi_conj]

private theorem eventuallyEq_nhds_of_punctured_of_continuousAt
    {f h : ℂ → ℂ} {z : ℂ} (hfh : f =ᶠ[𝓝[≠] z] h)
    (hf : ContinuousAt f z) (hh : ContinuousAt h z) :
    f =ᶠ[𝓝 z] h := by
  have hpunctured : NeBot (𝓝[≠] z) := inferInstance
  have hflim : Tendsto f (𝓝[≠] z) (𝓝 (f z)) :=
    hf.tendsto.mono_left nhdsWithin_le_nhds
  have hhlim : Tendsto h (𝓝[≠] z) (𝓝 (h z)) :=
    hh.tendsto.mono_left nhdsWithin_le_nhds
  have hflim' : Tendsto f (𝓝[≠] z) (𝓝 (h z)) :=
    hhlim.congr' hfh.symm
  have hcenter : f z = h z := tendsto_nhds_unique hflim hflim'
  change ∀ᶠ w in 𝓝[≠] z, f w = h w at hfh
  rw [eventually_nhdsWithin_iff] at hfh
  filter_upwards [hfh] with w hw
  by_cases hwz : w = z
  · simpa [hwz] using hcenter
  · exact hw (by simpa using hwz)

private theorem eventually_eventuallyEq_nhds
    {f h : ℂ → ℂ} {z : ℂ} (hfh : f =ᶠ[𝓝 z] h) :
    ∀ᶠ w in 𝓝 z, f =ᶠ[𝓝 w] h := by
  change {w | f w = h w} ∈ 𝓝 z at hfh
  have hinterior : interior {w | f w = h w} ∈ 𝓝 z :=
    interior_mem_nhds.mpr hfh
  filter_upwards [hinterior] with w hw
  change {v | f v = h v} ∈ 𝓝 w
  exact mem_interior_iff_mem_nhds.mp hw

private theorem eventually_zeroFactor_reflection
    {rho : ℂ} {m : ℕ} {g : ℂ → ℂ} (hrhoRe : rho.re = 1 / 2)
    (hg : AnalyticAt ℂ g rho)
    (hfactor : riemannXi =ᶠ[𝓝 rho] fun z => (z - rho) ^ m * g z) :
    let G : ℂ → ℂ := fun w => g (rho + w)
    let H : ℂ → ℂ := fun w => conj (G (-conj w))
    G =ᶠ[𝓝 0] fun w => ((-1 : ℂ) ^ m) * H w := by
  let G : ℂ → ℂ := fun w => g (rho + w)
  let H : ℂ → ℂ := fun w => conj (G (-conj w))
  have hrhoFix : 1 - conj rho = rho := by
    apply Complex.ext
    · simp [hrhoRe]
      norm_num
    · simp
  have hplus : Tendsto (fun w : ℂ => rho + w) (𝓝 0) (𝓝 rho) := by
    simpa using
      ((tendsto_const_nhds : Tendsto (fun _ : ℂ => rho) (𝓝 0) (𝓝 rho)).add
        (tendsto_id : Tendsto (fun w : ℂ => w) (𝓝 0) (𝓝 0)))
  have hminus : Tendsto (fun w : ℂ => rho - conj w) (𝓝 0) (𝓝 rho) := by
    simpa using
      ((tendsto_const_nhds : Tendsto (fun _ : ℂ => rho) (𝓝 0) (𝓝 rho)).sub
        continuous_conj.continuousAt.tendsto)
  have hfactorPlus := hfactor.comp_tendsto hplus
  have hfactorMinus := hfactor.comp_tendsto hminus
  have hpunctured :
      G =ᶠ[𝓝[≠] 0] fun w => ((-1 : ℂ) ^ m) * H w := by
    change ∀ᶠ w in 𝓝[≠] 0, G w = ((-1 : ℂ) ^ m) * H w
    rw [eventually_nhdsWithin_iff]
    filter_upwards [hfactorPlus, hfactorMinus] with w hwPlus hwMinus hw0
    have hwne : w ≠ 0 := by simpa using hw0
    have hsym :
        riemannXi (rho + w) = conj (riemannXi (rho - conj w)) := by
      rw [← riemannXi_one_sub_conj (rho - conj w)]
      congr 1
      calc
        rho + w = (1 - conj rho) + w := by rw [hrhoFix]
        _ = 1 - (conj rho - w) := by ring_nf
        _ = 1 - conj (rho - conj w) := by rw [map_sub, conj_conj]
    have hwMinus' :
        riemannXi (rho - conj w) =
          (rho - conj w - rho) ^ m * g (rho - conj w) := by
      simpa only [Function.comp_apply] using hwMinus
    have hmul :
        w ^ m * G w = w ^ m * (((-1 : ℂ) ^ m) * H w) := by
      calc
        w ^ m * G w = riemannXi (rho + w) := by
          simpa [G] using hwPlus.symm
        _ = conj (riemannXi (rho - conj w)) := hsym
        _ = conj (((rho - conj w - rho) ^ m) * g (rho - conj w)) := by
          exact congrArg conj hwMinus'
        _ = w ^ m * (((-1 : ℂ) ^ m) * H w) := by
          simp [G, H]
          ring_nf
    exact (mul_left_cancel₀ (pow_ne_zero m hwne) hmul)
  have hGcont : ContinuousAt G 0 := by
    change ContinuousAt (g ∘ fun w : ℂ => rho + w) 0
    exact hg.continuousAt.comp_of_eq
      (continuousAt_const.add continuousAt_id) (by simp)
  have hHcont : ContinuousAt H 0 := by
    have hinner : ContinuousAt (fun w : ℂ => -conj w) 0 :=
      continuous_neg.comp continuous_conj |>.continuousAt
    have hGinner : ContinuousAt (fun w : ℂ => G (-conj w)) 0 := by
      change ContinuousAt (G ∘ fun w : ℂ => -conj w) 0
      exact hGcont.comp_of_eq hinner (by simp)
    exact continuous_conj.continuousAt.comp hGinner
  exact eventuallyEq_nhds_of_punctured_of_continuousAt hpunctured hGcont
    (continuousAt_const.mul hHcont)

theorem levinsonMontgomery_zeroFactor_logDeriv_re_eq_zero
    {rho : ℂ} {m : ℕ} {g : ℂ → ℂ}
    (hrhoRe : rho.re = 1 / 2) (hg : AnalyticAt ℂ g rho)
    (hgne : g rho ≠ 0)
    (hfactor : riemannXi =ᶠ[𝓝 rho] fun z => (z - rho) ^ m * g z) :
    (logDeriv g rho).re = 0 := by
  let G : ℂ → ℂ := fun w => g (rho + w)
  let J : ℂ → ℂ := fun w => G (-w)
  let H : ℂ → ℂ := fun w => conj (G (-conj w))
  let c : ℂ := (-1 : ℂ) ^ m
  have hrelation : G =ᶠ[𝓝 0] fun w => c * H w := by
    simpa only [G, H, c] using
      eventually_zeroFactor_reflection hrhoRe hg hfactor
  have hGdiff : DifferentiableAt ℂ G 0 := by
    change DifferentiableAt ℂ (g ∘ fun w : ℂ => rho + w) 0
    have hg' : DifferentiableAt ℂ g (rho + (0 : ℂ)) := by
      simpa using hg.differentiableAt
    exact hg'.comp 0 (by fun_prop)
  have hJdiff : DifferentiableAt ℂ J 0 := by
    change DifferentiableAt ℂ (G ∘ fun w : ℂ => -w) 0
    have hG' : DifferentiableAt ℂ G (-(0 : ℂ)) := by
      simpa using hGdiff
    exact hG'.comp 0 (by fun_prop)
  have hHfun : H = conj ∘ J ∘ conj := by
    funext w
    rfl
  have hHdiff : DifferentiableAt ℂ H 0 := by
    rw [hHfun]
    simpa using hJdiff.star_conj
  have hc : c ≠ 0 := pow_ne_zero m (by norm_num)
  have hG0 : G 0 ≠ 0 := by simpa [G] using hgne
  have hvalue := hrelation.self_of_nhds
  change G 0 = c * H 0 at hvalue
  have hH0 : H 0 ≠ 0 := by
    intro hzero
    apply hG0
    rw [hvalue, hzero, mul_zero]
  have hlogRelation : logDeriv G 0 = logDeriv H 0 := by
    have hcongr :
        logDeriv G 0 = logDeriv (fun w : ℂ => c * H w) 0 := by
      rw [logDeriv_apply, logDeriv_apply, hrelation.deriv_eq, hvalue]
    rw [hcongr]
    simpa using
      (logDeriv_mul (f := fun _ : ℂ => c) (g := H) 0 hc hH0
        (by fun_prop) hHdiff)
  have hJderiv : deriv J 0 = -deriv G 0 := by
    change deriv (G ∘ fun w : ℂ => -w) 0 = _
    have hout : DifferentiableAt ℂ G ((fun w : ℂ => -w) 0) := by
      simpa using hGdiff
    have hin : DifferentiableAt ℂ (fun w : ℂ => -w) 0 := by fun_prop
    rw [deriv_comp (𝕜 := ℂ) (𝕜' := ℂ) (0 : ℂ) hout hin]
    simp
  have hHderiv : deriv H 0 = -conj (deriv G 0) := by
    rw [hHfun]
    have hstar := congrFun (deriv_conj_conj (f := J)) 0
    rw [hstar]
    simp [Function.comp_apply, hJderiv]
  have hlogReflection : logDeriv H 0 = -conj (logDeriv G 0) := by
    rw [logDeriv_apply, logDeriv_apply, hHderiv]
    simp only [H, map_zero, neg_zero, map_div₀]
    rw [neg_div]
  have hpure : logDeriv G 0 = -conj (logDeriv G 0) := by
    calc
      logDeriv G 0 = logDeriv H 0 := hlogRelation
      _ = -conj (logDeriv G 0) := hlogReflection
  have hGlog : logDeriv G 0 = logDeriv g rho := by
    change logDeriv (g ∘ fun w : ℂ => rho + w) 0 = _
    have hg0 : DifferentiableAt ℂ g (rho + 0) := by
      simpa using hg.differentiableAt
    rw [logDeriv_comp hg0
      (differentiableAt_const _ |>.add differentiableAt_id)]
    simp
  rw [hGlog] at hpure
  have hre : (logDeriv g rho).re = -(logDeriv g rho).re := by
    simpa using congrArg Complex.re hpure
  linarith

def levinsonMontgomeryCriticalZetaResidual (g : ℂ → ℂ) (z : ℂ) : ℂ :=
  logDeriv g z - logDeriv riemannXiZetaUnit z

theorem logDeriv_riemannXiZetaUnit_eq_poles_add_GammaR
    {s : ℂ} (hs : IsNontrivialZero s) :
    logDeriv riemannXiZetaUnit s =
      1 / s + 1 / (s - 1) + logDeriv Gammaℝ s := by
  let A : ℂ → ℂ := fun z => z * (z - 1) / 2
  have hs0 : s ≠ 0 := ne_zero_of_isNontrivialZero hs
  have hs1 : s ≠ 1 := hs.2.2
  have hA : A s ≠ 0 := by
    dsimp [A]
    exact div_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) (by norm_num)
  have hgamma : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_isNontrivialZero hs
  have hsRe : 0 < s.re := speiser_nontrivial_zero_re_pos hs
  have hdA : DifferentiableAt ℂ A s := by
    dsimp [A]
    fun_prop
  have hdGamma : DifferentiableAt ℂ Gammaℝ s :=
    differentiableAt_GammaR_of_re_pos hsRe
  change logDeriv (fun z : ℂ => z * (z - 1) / 2 * ((Gammaℝ z)⁻¹)⁻¹) s = _
  simp only [inv_inv]
  rw [logDeriv_mul s hA hgamma hdA hdGamma]
  rw [show logDeriv A s = 1 / s + 1 / (s - 1) by
    simpa [A] using logDeriv_riemannXiFactor hs0 hs1]

theorem levinsonMontgomeryCriticalZetaResidual_re_eq_archimedean
    {rho : ℂ} {m : ℕ} {g : ℂ → ℂ}
    (hrho : IsNontrivialZero rho) (hrhoRe : rho.re = 1 / 2)
    (hg : AnalyticAt ℂ g rho) (hgne : g rho ≠ 0)
    (hfactor : riemannXi =ᶠ[𝓝 rho] fun z => (z - rho) ^ m * g z) :
    (levinsonMontgomeryCriticalZetaResidual g rho).re =
      levinsonMontgomeryLogDerivArchimedeanTerm rho := by
  have hgRe :=
    levinsonMontgomery_zeroFactor_logDeriv_re_eq_zero hrhoRe hg hgne hfactor
  have hunit :=
    logDeriv_riemannXiZetaUnit_eq_poles_add_GammaR hrho
  have hrho0 : rho ≠ 0 := ne_zero_of_isNontrivialZero hrho
  have hnotpole : ∀ k : ℕ, rho ≠ -(2 * k) := by
    intro k h
    have hre := congrArg Complex.re h
    norm_num at hre
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    rw [hrhoRe] at hre
    norm_num at hre
    linarith
  have hgammaLog :=
    logDeriv_GammaR_eq_digamma_of_not_neg_even hnotpole
  have hhalfNotPole : ∀ k : ℕ, rho / 2 ≠ -k := by
    intro k h
    have hre := congrArg Complex.re h
    norm_num [div_re] at hre
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    rw [hrhoRe] at hre
    norm_num at hre
    linarith
  have hpsi := Complex.digamma_apply_add_one (rho / 2) hhalfNotPole
  have hhalfInv : (rho / 2)⁻¹ = 2 / rho := by
    field_simp [hrho0]
  have hsource :
      -logDeriv riemannXiZetaUnit rho =
        -1 / (rho - 1) + (Real.log Real.pi : ℂ) / 2 -
          Complex.digamma (rho / 2 + 1) / 2 := by
    rw [hunit, hgammaLog, hpsi, hhalfInv]
    simp only [div_eq_mul_inv]
    ring_nf
  have hsourceRe := congrArg Complex.re hsource
  rw [levinsonMontgomeryCriticalZetaResidual]
  calc
    (logDeriv g rho - logDeriv riemannXiZetaUnit rho).re =
        (-logDeriv riemannXiZetaUnit rho).re := by
      simp only [sub_re, neg_re]
      linarith
    _ = (-1 / (rho - 1) + (Real.log Real.pi : ℂ) / 2 -
          Complex.digamma (rho / 2 + 1) / 2).re := hsourceRe
    _ = levinsonMontgomeryLogDerivArchimedeanTerm rho := by
      rw [levinsonMontgomeryLogDerivArchimedeanTerm]
      rw [neg_div]
      norm_num

theorem levinsonMontgomery_continuousAt_criticalZetaResidual
    {rho : ℂ} {g : ℂ → ℂ} (hrho : IsNontrivialZero rho)
    (hg : AnalyticAt ℂ g rho) (hgne : g rho ≠ 0) :
    ContinuousAt (levinsonMontgomeryCriticalZetaResidual g) rho := by
  have hunit := analyticAt_riemannXiZetaUnit_of_isNontrivialZero hrho
  have hunitNe := riemannXiZetaUnit_ne_zero_of_isNontrivialZero hrho
  exact
    (levinsonMontgomery_continuousAt_logDeriv_of_analyticAt_of_ne_zero hg hgne).sub
      (levinsonMontgomery_continuousAt_logDeriv_of_analyticAt_of_ne_zero
        hunit hunitNe)

theorem levinsonMontgomeryCriticalZetaResidual_re_neg
    {rho : ℂ} {m : ℕ} {g : ℂ → ℂ}
    (hrho : IsNontrivialZero rho) (hrhoRe : rho.re = 1 / 2)
    (hrhoIm : 10 ≤ rho.im) (hg : AnalyticAt ℂ g rho) (hgne : g rho ≠ 0)
    (hfactor : riemannXi =ᶠ[𝓝 rho] fun z => (z - rho) ^ m * g z) :
    (levinsonMontgomeryCriticalZetaResidual g rho).re < 0 := by
  rw [levinsonMontgomeryCriticalZetaResidual_re_eq_archimedean
    hrho hrhoRe hg hgne hfactor]
  apply levinsonMontgomeryLogDerivArchimedeanTerm_neg
  · rw [hrhoRe]
    norm_num
  · rw [hrhoRe]
  · exact hrhoIm

theorem exists_riemannZeta_critical_zero_analytic_factor
    {rho : ℂ} (hrho : IsNontrivialZero rho)
    (hrhoRe : rho.re = 1 / 2) (hrhoIm : 10 ≤ rho.im) :
    ∃ (m : ℕ) (h : ℂ → ℂ), 0 < m ∧ AnalyticAt ℂ h rho ∧ h rho ≠ 0 ∧
      (riemannZeta =ᶠ[𝓝 rho] fun z => (z - rho) ^ m * h z) ∧
      (logDeriv h rho).re < 0 := by
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
    apply (mul_left_cancel₀ hzUnit)
    calc
      riemannXiZetaUnit z * riemannZeta z = riemannXi z := hunitEq.symm
      _ = (z - rho) ^ m * g z := hxi
      _ = riemannXiZetaUnit z * ((z - rho) ^ m * h z) := by
        dsimp [h]
        field_simp
  have hlogh :
      logDeriv h rho = levinsonMontgomeryCriticalZetaResidual g rho := by
    simpa [h, levinsonMontgomeryCriticalZetaResidual] using
      (logDeriv_div rho hgne hunitNe hg.differentiableAt hunit.differentiableAt)
  have hresNeg :=
    levinsonMontgomeryCriticalZetaResidual_re_neg
      hrho hrhoRe hrhoIm hg hgne hfactorXi
  refine ⟨m, h, hm, hh, hhne, hfactorZeta, ?_⟩
  rw [hlogh]
  exact hresNeg

theorem levinsonMontgomery_principalZeroTerm_re_nonpos
    {rho z : ℂ} {m : ℕ} (hz : z ≠ rho) (hleft : z.re ≤ rho.re) :
    (((m : ℂ) / (z - rho)).re) ≤ 0 := by
  by_cases hm : m = 0
  · subst m
    simp
  · rcases hleft.eq_or_lt with heq | hlt
    · have hsubRe : (z - rho).re = 0 := by
        simp only [sub_re]
        linarith
      rw [div_eq_mul_inv]
      simp [mul_re, hsubRe]
    · exact
        (levinsonMontgomery_principalZeroTerm_re_neg
          (m := m) (Nat.zero_lt_of_ne_zero hm) hz hlt).le

private theorem logDeriv_centered_pow
    {rho z : ℂ} {m : ℕ} (_hz : z ≠ rho) :
    logDeriv (fun w : ℂ => (w - rho) ^ m) z = (m : ℂ) / (z - rho) := by
  rw [logDeriv_fun_pow (by fun_prop)]
  have hbase :
      logDeriv (fun w : ℂ => w - rho) z = 1 / (z - rho) := by
    rw [logDeriv_apply]
    simp
  rw [hbase]
  ring_nf

private theorem exists_negative_left_neighborhood_of_analytic_factor
    {f h : ℂ → ℂ} {rho : ℂ} {m : ℕ}
    (hh : AnalyticAt ℂ h rho) (hhne : h rho ≠ 0)
    (hfactor : f =ᶠ[𝓝 rho] fun z => (z - rho) ^ m * h z)
    (hresNeg : (logDeriv h rho).re < 0) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ z : ℂ, dist z rho < epsilon → z ≠ rho → z.re ≤ rho.re →
        f z ≠ 0 ∧ (logDeriv f z).re < 0 := by
  have hlogCont :=
    levinsonMontgomery_continuousAt_logDeriv_of_analyticAt_of_ne_zero hh hhne
  have hlogReCont :
      ContinuousAt (fun z => (logDeriv h z).re) rho :=
    Complex.continuous_re.continuousAt.comp hlogCont
  have hresEventually : ∀ᶠ z in 𝓝 rho, (logDeriv h z).re < 0 :=
    hlogReCont.eventually_lt_const hresNeg
  have hhEventually := hh.continuousAt.eventually_ne hhne
  have hhAnalyticEventually := hh.eventually_analyticAt
  have hfactorAt := eventually_eventuallyEq_nhds hfactor
  have hevent :
      ∀ᶠ z in 𝓝 rho, ∀ hz : z ≠ rho, z.re ≤ rho.re →
        f z ≠ 0 ∧ (logDeriv f z).re < 0 := by
    filter_upwards [hresEventually, hhEventually, hhAnalyticEventually, hfactorAt] with
      z hzResidual hzH hzAnalytic hfactorZ hz hleft
    have hzBase : z - rho ≠ 0 := sub_ne_zero.mpr hz
    have hzPow : (z - rho) ^ m ≠ 0 := pow_ne_zero m hzBase
    have hfactorValue : f z = (z - rho) ^ m * h z :=
      hfactorZ.self_of_nhds
    have hfz : f z ≠ 0 := by
      rw [hfactorValue]
      exact mul_ne_zero hzPow hzH
    refine ⟨hfz, ?_⟩
    have hlogCongr :
        logDeriv f z =
          logDeriv (fun w : ℂ => (w - rho) ^ m * h w) z := by
      rw [logDeriv_apply, logDeriv_apply, hfactorZ.deriv_eq, hfactorValue]
    have hlogMul :=
      logDeriv_mul (f := fun w : ℂ => (w - rho) ^ m) (g := h)
        z hzPow hzH (by fun_prop) hzAnalytic.differentiableAt
    have hlogFormula :
        logDeriv f z = (m : ℂ) / (z - rho) + logDeriv h z := by
      rw [hlogCongr, hlogMul, logDeriv_centered_pow hz]
    rw [hlogFormula]
    have hprincipal :=
      levinsonMontgomery_principalZeroTerm_re_nonpos (m := m) hz hleft
    simp only [add_re]
    linarith
  change {z | ∀ hz : z ≠ rho, z.re ≤ rho.re →
    f z ≠ 0 ∧ (logDeriv f z).re < 0} ∈ 𝓝 rho at hevent
  rcases Metric.mem_nhds_iff.mp hevent with ⟨epsilon, hepsilon, hball⟩
  refine ⟨epsilon, hepsilon, fun z hzDist hz hleft => ?_⟩
  exact hball (by simpa [Metric.mem_ball] using hzDist) hz hleft

theorem exists_levinsonMontgomery_critical_zero_left_neighborhood
    {rho : ℂ} (hrho : IsNontrivialZero rho)
    (hrhoRe : rho.re = 1 / 2) (hrhoIm : 10 < rho.im) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ z : ℂ, dist z rho < epsilon → z ≠ rho → z.re ≤ 1 / 2 →
        riemannZeta z ≠ 0 ∧ (logDeriv riemannZeta z).re < 0 := by
  obtain ⟨m, h, _hm, hh, hhne, hfactor, hresNeg⟩ :=
    exists_riemannZeta_critical_zero_analytic_factor
      hrho hrhoRe (le_of_lt hrhoIm)
  obtain ⟨epsilon, hepsilon, hnegative⟩ :=
    exists_negative_left_neighborhood_of_analytic_factor
      hh hhne hfactor hresNeg
  refine ⟨epsilon, hepsilon, fun z hzDist hz hleft => ?_⟩
  apply hnegative z hzDist hz
  rw [hrhoRe]
  exact hleft

theorem exists_levinsonMontgomery_negative_left_semicircle
    {rho : ℂ} (hrho : IsNontrivialZero rho)
    (hrhoRe : rho.re = 1 / 2) (hrhoIm : 10 < rho.im) :
    ∃ r : ℝ, 0 < r ∧
      ∀ z : ℂ, dist z rho = r → z.re ≤ 1 / 2 →
        riemannZeta z ≠ 0 ∧ (logDeriv riemannZeta z).re < 0 := by
  obtain ⟨epsilon, hepsilon, hnegative⟩ :=
    exists_levinsonMontgomery_critical_zero_left_neighborhood
      hrho hrhoRe hrhoIm
  refine ⟨epsilon / 2, by positivity, fun z hzDist hleft => ?_⟩
  have hzNear : dist z rho < epsilon := by
    rw [hzDist]
    linarith
  have hz : z ≠ rho := by
    intro hz
    subst z
    simp only [dist_self] at hzDist
    linarith
  exact hnegative z hzNear hz hleft

end

end Riemann

end LeanLab
