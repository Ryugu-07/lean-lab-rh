import LeanLab.Riemann.LevinsonMontgomeryFiniteArgumentPrinciple
import LeanLab.Riemann.LevinsonMontgomeryTopArgumentVariation
import Mathlib.Topology.MetricSpace.Thickening

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# A uniform negative strip left of the critical line

The source indents the critical line around each zeta zero. On a fixed compact height interval,
the same local sign information gives a uniform straight vertical line just left of the critical
line. This module isolates that compactness step.
-/

open Complex Filter Function MeasureTheory Metric Set Topology
open scoped BigOperators Interval Topology

namespace LeanLab.Riemann

noncomputable section

/-- The compact critical-line segment between two heights. -/
def levinsonMontgomeryCriticalSegment (b t : ℝ) : Set ℂ :=
  ({1 / 2} : Set ℝ) ×ℂ Set.Icc b t

theorem isCompact_levinsonMontgomeryCriticalSegment (b t : ℝ) :
    IsCompact (levinsonMontgomeryCriticalSegment b t) := by
  exact isCompact_singleton.reProdIm isCompact_Icc

/-- Every critical-line point above height ten has a neighborhood whose strict-left part is
zeta-zero-free and has strictly negative real logarithmic derivative. At a critical zero the
center is never evaluated, because a strict-left point cannot equal the center. -/
theorem exists_levinsonMontgomery_criticalPoint_leftNegative_ball
    {rho : ℂ} (hrhoRe : rho.re = 1 / 2) (hrhoIm : 10 < rho.im) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ z : ℂ, dist z rho < epsilon → z.re < 1 / 2 →
        riemannZeta z ≠ 0 ∧ (logDeriv riemannZeta z).re < 0 := by
  by_cases hrhoZero : riemannZeta rho = 0
  · have hrho : IsNontrivialZero rho := by
      refine ⟨hrhoZero, ?_, ?_⟩
      · rintro ⟨m, hm⟩
        have him := congrArg Complex.im hm
        norm_num at him
        linarith
      · intro hrhoOne
        have him := congrArg Complex.im hrhoOne
        norm_num at him
        linarith
    obtain ⟨epsilon, hepsilon, hnegative⟩ :=
      exists_levinsonMontgomery_critical_zero_left_neighborhood
        hrho hrhoRe hrhoIm
    refine ⟨epsilon, hepsilon, fun z hzDist hzRe => ?_⟩
    have hzNe : z ≠ rho := by
      intro hz
      subst z
      linarith
    exact hnegative z hzDist hzNe hzRe.le
  · have hrhoOne : rho ≠ 1 := by
      intro hrhoOne
      have him := congrArg Complex.im hrhoOne
      norm_num at him
      linarith
    have hnegative : (logDeriv riemannZeta rho).re < 0 :=
      levinsonMontgomery_logDeriv_riemannZeta_re_neg_on_critical_boundary
        hrhoRe (le_of_lt hrhoIm) hrhoZero
    have hanalytic : AnalyticAt ℂ riemannZeta rho :=
      analyticOn_riemannZeta rho (by simpa using hrhoOne)
    have hlogContinuous : ContinuousAt (logDeriv riemannZeta) rho :=
      levinsonMontgomery_continuousAt_logDeriv_of_analyticAt_of_ne_zero
        hanalytic hrhoZero
    have hrealContinuous :
        ContinuousAt (fun z : ℂ => (logDeriv riemannZeta z).re) rho :=
      Complex.continuous_re.continuousAt.comp hlogContinuous
    have heventually :
        ∀ᶠ z in 𝓝 rho,
          riemannZeta z ≠ 0 ∧ (logDeriv riemannZeta z).re < 0 :=
      (hanalytic.continuousAt.eventually_ne hrhoZero).and
        (hrealContinuous.eventually_lt_const hnegative)
    change {z : ℂ |
      riemannZeta z ≠ 0 ∧ (logDeriv riemannZeta z).re < 0} ∈ 𝓝 rho at heventually
    obtain ⟨epsilon, hepsilon, hball⟩ := Metric.mem_nhds_iff.mp heventually
    exact ⟨epsilon, hepsilon, fun z hzDist _hzRe =>
      hball (by simpa [Metric.mem_ball] using hzDist)⟩

/-- On every compact height interval above ten, strict negativity on the critical boundary and
the punctured critical-zero neighborhoods thicken to one uniform left strip. -/
theorem exists_levinsonMontgomery_uniformNegativeCriticalLeftStrip
    {b t : ℝ} (hb : 10 < b) (_hbt : b ≤ t) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ z : ℂ, z.im ∈ Set.Icc b t →
        1 / 2 - delta < z.re → z.re < 1 / 2 →
          riemannZeta z ≠ 0 ∧ (logDeriv riemannZeta z).re < 0 := by
  classical
  let K : Set ℂ := levinsonMontgomeryCriticalSegment b t
  have hK : IsCompact K := isCompact_levinsonMontgomeryCriticalSegment b t
  have hlocal :
      ∀ rho : K, ∃ epsilon : ℝ, 0 < epsilon ∧
        ∀ z : ℂ, dist z rho < epsilon → z.re < 1 / 2 →
          riemannZeta z ≠ 0 ∧ (logDeriv riemannZeta z).re < 0 := by
    intro rho
    have hrhoRe : (rho : ℂ).re = 1 / 2 := by
      exact rho.property.1
    have hrhoIm : 10 < (rho : ℂ).im := by
      exact hb.trans_le rho.property.2.1
    exact exists_levinsonMontgomery_criticalPoint_leftNegative_ball
      hrhoRe hrhoIm
  choose epsilon hepsilon hnegative using hlocal
  let U : Set ℂ := ⋃ rho : K, Metric.ball (rho : ℂ) (epsilon rho)
  have hUOpen : IsOpen U := by
    dsimp only [U]
    exact isOpen_iUnion fun rho => Metric.isOpen_ball
  have hKU : K ⊆ U := by
    intro rho hrho
    change rho ∈ ⋃ p : K, Metric.ball (p : ℂ) (epsilon p)
    apply Set.mem_iUnion.mpr
    let p : K := ⟨rho, hrho⟩
    refine ⟨p, ?_⟩
    exact Metric.mem_ball_self (hepsilon p)
  obtain ⟨delta, hdelta, hthick⟩ :=
    hK.exists_thickening_subset_open hUOpen hKU
  refine ⟨delta, hdelta, fun z hzIm hzNear hzLeft => ?_⟩
  let p : ℂ := (1 / 2 : ℂ) + z.im * I
  have hpK : p ∈ K := by
    change p.re ∈ ({1 / 2} : Set ℝ) ∧ p.im ∈ Set.Icc b t
    simpa [p] using hzIm
  have hzDist : dist z p = 1 / 2 - z.re := by
    have hsub : z - p = ((z.re - 1 / 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [p]
    rw [dist_eq_norm, hsub]
    have hzNonpos : z.re - 1 / 2 ≤ 0 := by linarith
    simp only [norm_real, Real.norm_eq_abs, abs_of_nonpos hzNonpos]
    ring
  have hzThick : z ∈ Metric.thickening delta K := by
    apply Metric.mem_thickening_iff.mpr
    exact ⟨p, hpK, by rw [hzDist]; linarith⟩
  have hzU := hthick hzThick
  change z ∈ ⋃ rho : K, Metric.ball (rho : ℂ) (epsilon rho) at hzU
  obtain ⟨rho, hzBall⟩ := Set.mem_iUnion.mp hzU
  exact hnegative rho z (by simpa [Metric.mem_ball] using hzBall) hzLeft

/-- The finite-support cutoff can be chosen inside the uniform negative strip. It therefore
retains every divisor point strictly left of the critical line and makes the whole right
vertical side strictly left-pointing for `zeta'/zeta`. -/
theorem exists_levinsonMontgomery_negativeCommonRightCutoff
    {K : Set ℂ} (hK : IsCompact K) (hKDomain : K ⊆ ({1} : Set ℂ)ᶜ)
    {b t : ℝ} (hb : 10 < b) (hbt : b ≤ t) :
    ∃ r : ℝ, 0 < r ∧ r < 1 / 2 ∧
      (∀ u ∈ compactAnalyticDivisorSupportFinset riemannZeta K hK,
        u.re < 1 / 2 → u.re < r) ∧
      (∀ u ∈ compactAnalyticDivisorSupportFinset (deriv riemannZeta) K hK,
        u.re < 1 / 2 → u.re < r) ∧
      ∀ y : ℝ, y ∈ Set.Icc b t →
        riemannZeta ((r : ℂ) + y * I) ≠ 0 ∧
          deriv riemannZeta ((r : ℂ) + y * I) ≠ 0 ∧
          (speiserZetaDerivRatio ((r : ℂ) + y * I)).re < 0 := by
  obtain ⟨delta, hdelta, hnegative⟩ :=
    exists_levinsonMontgomery_uniformNegativeCriticalLeftStrip hb hbt
  let l : ℝ := max 0 (1 / 2 - delta)
  have hlHalf : l < 1 / 2 := by
    dsimp only [l]
    apply max_lt
    · norm_num
    · linarith
  obtain ⟨r, hlr, hrHalf, hzetaBound, hderivBound, _hright⟩ :=
    exists_levinsonMontgomery_commonRightCutoff hK hKDomain hlHalf
  have hrPos : 0 < r := by
    have hzeroLe : 0 ≤ l := by
      dsimp only [l]
      exact le_max_left _ _
    exact hzeroLe.trans_lt hlr
  have hrStrip : 1 / 2 - delta < r := by
    have hstripLe : 1 / 2 - delta ≤ l := by
      dsimp only [l]
      exact le_max_right _ _
    exact hstripLe.trans_lt hlr
  refine ⟨r, hrPos, hrHalf, hzetaBound, hderivBound, fun y hy => ?_⟩
  let z : ℂ := (r : ℂ) + y * I
  have hzIm : z.im ∈ Set.Icc b t := by
    simpa [z] using hy
  have hzRe : z.re = r := by simp [z]
  have hzData := hnegative z hzIm (by rw [hzRe]; exact hrStrip)
    (by rw [hzRe]; exact hrHalf)
  have hzDeriv : deriv riemannZeta z ≠ 0 := by
    intro hzDeriv
    have hneg := hzData.2
    rw [logDeriv_apply, hzDeriv, zero_div, Complex.zero_re] at hneg
    exact (lt_irrefl 0) hneg
  have hzRatio : (speiserZetaDerivRatio z).re < 0 := by
    simpa only [speiserZetaDerivRatio, logDeriv_apply] using hzData.2
  simpa only [z] using ⟨hzData.1, hzDeriv, hzRatio⟩

/-- The uniform negative strip and finite divisor stabilization can be imposed on the same
concrete contour. The returned straight right side therefore computes the exact global
multiplicity-count difference and keeps `zeta'/zeta` in the strict left half-plane. -/
theorem exists_levinsonMontgomery_negativeRight_globalCountDifference_of_topOpen_actual
    {b t : ℝ} (hb : 10 < b) (hbt : b < t)
    (hbottom : SpeiserCommonZeroFreeHorizontal b)
    (htop : ∀ x : ℝ, 0 ≤ x → x < 1 / 2 →
      riemannZeta ((x : ℂ) + t * I) ≠ 0 ∧
        deriv riemannZeta ((x : ℂ) + t * I) ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ r < 1 / 2 ∧
      (∀ y : ℝ, y ∈ Set.Icc b t →
        riemannZeta ((r : ℂ) + y * I) ≠ 0 ∧
          deriv riemannZeta ((r : ℂ) + y * I) ≠ 0 ∧
          (speiserZetaDerivRatio ((r : ℂ) + y * I)).re < 0) ∧
      rectangleBoundaryIntegral (logDeriv (deriv riemannZeta)) 0 r b t -
          rectangleBoundaryIntegral (logDeriv riemannZeta) 0 r b t =
        2 * (Real.pi : ℂ) * I *
          (((speiserUpperLeftDerivZeroCount t : ℂ) -
              (speiserUpperLeftZetaZeroCount t : ℂ)) -
            ((speiserUpperLeftDerivZeroCount b : ℂ) -
              (speiserUpperLeftZetaZeroCount b : ℂ))) := by
  let K : Set ℂ := levinsonMontgomeryCountCompactCutoff b t
  let V : Set ℂ := levinsonMontgomeryCountOpenCutoff b t
  have hK : IsCompact K :=
    isCompact_levinsonMontgomeryCountCompactCutoff b t
  have hKDomain : K ⊆ ({1} : Set ℂ)ᶜ :=
    levinsonMontgomeryCountCompactCutoff_subset_zetaDomain b t
  have hVOpen : IsOpen V :=
    isOpen_levinsonMontgomeryCountOpenCutoff b t
  have hVPre : IsPreconnected V :=
    isPreconnected_levinsonMontgomeryCountOpenCutoff b t
  have hVK : V ⊆ K :=
    levinsonMontgomeryCountOpenCutoff_subset_compact b t
  have hwideRect : ([[0, (1 / 2 : ℝ)]] ×ℂ [[b, t]]) ⊆ V :=
    levinsonMontgomery_sourceRectangle_subset_openCutoff hbt
  have hz0 : (1 / 4 : ℂ) + b * I ∈ V :=
    exists_mem_levinsonMontgomeryCountOpenCutoff hbt
  obtain ⟨r, hr0, hrHalf, hzetaBound, hderivBound, hright⟩ :=
    exists_levinsonMontgomery_negativeCommonRightCutoff
      hK hKDomain hb hbt.le
  have hhorizontal : [[(0 : ℝ), r]] ⊆ Set.Icc (0 : ℝ) (1 / 2) := by
    intro x hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) r := by
      simpa only [uIcc_of_le hr0.le] using hx
    exact ⟨hxIcc.1, hxIcc.2.trans hrHalf.le⟩
  have hvertical : [[b, t]] ⊆ Set.Icc b t := by
    intro y hy
    simpa only [uIcc_of_le hbt.le] using hy
  have hrect : ([[0, r]] ×ℂ [[b, t]]) ⊆ V := by
    intro z hz
    apply hwideRect
    have hzRe : z.re ∈ [[(0 : ℝ), (1 / 2 : ℝ)]] := by
      simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] using
        hhorizontal hz.1
    exact ⟨hzRe, hz.2⟩
  have hbottomNarrow : ∀ x ∈ [[(0 : ℝ), r]],
      riemannZeta ((x : ℂ) + b * I) ≠ 0 ∧
        deriv riemannZeta ((x : ℂ) + b * I) ≠ 0 := by
    intro x hx
    exact hbottom.2 x (hhorizontal hx)
  have htopNarrow : ∀ x ∈ [[(0 : ℝ), r]],
      riemannZeta ((x : ℂ) + t * I) ≠ 0 ∧
        deriv riemannZeta ((x : ℂ) + t * I) ≠ 0 := by
    intro x hx
    have hxIcc : x ∈ Set.Icc (0 : ℝ) r := by
      simpa only [uIcc_of_le hr0.le] using hx
    exact htop x hxIcc.1 (hxIcc.2.trans_lt hrHalf)
  have hrightBoundary : ∀ y ∈ [[b, t]],
      riemannZeta ((r : ℂ) + y * I) ≠ 0 ∧
        deriv riemannZeta ((r : ℂ) + y * I) ≠ 0 := by
    intro y hy
    exact ⟨(hright y (hvertical hy)).1, (hright y (hvertical hy)).2.1⟩
  have hleft : ∀ y ∈ [[b, t]],
      riemannZeta (((0 : ℝ) : ℂ) + y * I) ≠ 0 ∧
        deriv riemannZeta (((0 : ℝ) : ℂ) + y * I) ≠ 0 := by
    intro y hy
    have hyIcc := hvertical hy
    let s : ℂ := ((0 : ℝ) : ℂ) + y * I
    have hsRe : s.re = 0 := by simp [s]
    have hsIm : 10 ≤ s.im := by
      have hsImEq : s.im = y := by simp [s]
      rw [hsImEq]
      exact hb.le.trans hyIcc.1
    have hsData :=
      levinsonMontgomery_logDeriv_riemannZeta_re_neg_on_left_boundary hsRe hsIm
    have hsDeriv : deriv riemannZeta s ≠ 0 := by
      intro hzero
      have hneg := hsData.2
      rw [logDeriv_apply, hzero, zero_div, Complex.zero_re] at hneg
      exact (lt_irrefl 0) hneg
    simpa only [s] using And.intro hsData.1 hsDeriv
  have hdiff := levinsonMontgomery_zeroFreeRectangle_countDifference
    hK hKDomain hVOpen hVPre hVK hz0 hrect hr0 hbt
      (fun x hx => (hbottomNarrow x hx).1)
      (fun x hx => (htopNarrow x hx).1)
      (fun y hy => (hrightBoundary y hy).1)
      (fun y hy => (hleft y hy).1)
      (fun x hx => (hbottomNarrow x hx).2)
      (fun x hx => (htopNarrow x hx).2)
      (fun y hy => (hrightBoundary y hy).2)
      (fun y hy => (hleft y hy).2)
  have hzetaCount :=
    compactZetaStrictRectangleCount_eq_criticalLine_of_rightCutoff
      hK (b := b) (t := t) hrHalf hzetaBound
  have hderivCount :=
    compactZetaDerivStrictRectangleCount_eq_criticalLine_of_rightCutoff
      hK (b := b) (t := t) hrHalf hderivBound
  rw [sum_divisor_deriv_riemannZeta_eq_compactCount hK hKDomain 0 r b t,
    sum_divisor_riemannZeta_eq_compactCount hK hKDomain 0 r b t,
    hzetaCount, hderivCount] at hdiff
  have hrectK : ([[0, (1 / 2 : ℝ)]] ×ℂ [[b, t]]) ⊆ K :=
    fun _ hz => hVK (hwideRect hz)
  have hzetaSplit := speiserUpperLeftZetaZeroCount_add_compactCount
    hK hKDomain hbt hbottom hrectK
  have hderivSplit := speiserUpperLeftDerivZeroCount_add_compactCount
    hK hKDomain hbt hbottom hrectK
  have hzetaCast :
      (speiserUpperLeftZetaZeroCount b : ℂ) +
          (compactZetaStrictRectangleCount K hK 0 (1 / 2) b t : ℂ) =
        (speiserUpperLeftZetaZeroCount t : ℂ) := by
    exact_mod_cast hzetaSplit
  have hderivCast :
      (speiserUpperLeftDerivZeroCount b : ℂ) +
          (compactZetaDerivStrictRectangleCount K hK 0 (1 / 2) b t : ℂ) =
        (speiserUpperLeftDerivZeroCount t : ℂ) := by
    exact_mod_cast hderivSplit
  have hzetaCompact :
      (compactZetaStrictRectangleCount K hK 0 (1 / 2) b t : ℂ) =
        (speiserUpperLeftZetaZeroCount t : ℂ) -
          (speiserUpperLeftZetaZeroCount b : ℂ) := by
    linear_combination hzetaCast
  have hderivCompact :
      (compactZetaDerivStrictRectangleCount K hK 0 (1 / 2) b t : ℂ) =
        (speiserUpperLeftDerivZeroCount t : ℂ) -
          (speiserUpperLeftDerivZeroCount b : ℂ) := by
    linear_combination hderivCast
  rw [hzetaCompact, hderivCompact] at hdiff
  refine ⟨r, hr0, hrHalf, hright, ?_⟩
  calc
    rectangleBoundaryIntegral (logDeriv (deriv riemannZeta)) 0 r b t -
        rectangleBoundaryIntegral (logDeriv riemannZeta) 0 r b t =
      2 * (Real.pi : ℂ) * I *
        (((speiserUpperLeftDerivZeroCount t : ℂ) -
            (speiserUpperLeftDerivZeroCount b : ℂ)) -
          ((speiserUpperLeftZetaZeroCount t : ℂ) -
            (speiserUpperLeftZetaZeroCount b : ℂ))) := hdiff
    _ = 2 * (Real.pi : ℂ) * I *
        (((speiserUpperLeftDerivZeroCount t : ℂ) -
            (speiserUpperLeftZetaZeroCount t : ℂ)) -
          ((speiserUpperLeftDerivZeroCount b : ℂ) -
            (speiserUpperLeftZetaZeroCount b : ℂ))) := by ring

/-- The negative-right global count identity at an ordinary common zero-free top height. -/
theorem exists_levinsonMontgomery_negativeRight_globalCountDifference_actual
    {b t : ℝ} (hb : 10 < b) (hbt : b < t)
    (hbottom : SpeiserCommonZeroFreeHorizontal b)
    (htop : SpeiserCommonZeroFreeHorizontal t) :
    ∃ r : ℝ, 0 < r ∧ r < 1 / 2 ∧
      (∀ y : ℝ, y ∈ Set.Icc b t →
        riemannZeta ((r : ℂ) + y * I) ≠ 0 ∧
          deriv riemannZeta ((r : ℂ) + y * I) ≠ 0 ∧
          (speiserZetaDerivRatio ((r : ℂ) + y * I)).re < 0) ∧
      rectangleBoundaryIntegral (logDeriv (deriv riemannZeta)) 0 r b t -
          rectangleBoundaryIntegral (logDeriv riemannZeta) 0 r b t =
        2 * (Real.pi : ℂ) * I *
          (((speiserUpperLeftDerivZeroCount t : ℂ) -
              (speiserUpperLeftZetaZeroCount t : ℂ)) -
            ((speiserUpperLeftDerivZeroCount b : ℂ) -
              (speiserUpperLeftZetaZeroCount b : ℂ))) := by
  apply exists_levinsonMontgomery_negativeRight_globalCountDifference_of_topOpen_actual
    hb hbt hbottom
  intro x hx0 hxHalf
  exact htop.2 x ⟨hx0, hxHalf.le⟩

/-- The same exact count identity at a source negative-height geometry witness. A possible zeta
zero at the critical endpoint is outside the adaptive straight contour. -/
theorem exists_levinsonMontgomery_negativeRight_globalCountDifference_of_negativeHeightGeometry
    {b : ℝ} {n : ℕ} (hb : 10 < b) (hbn : b < n)
    (hbottom : SpeiserCommonZeroFreeHorizontal b)
    (htop : LevinsonMontgomeryNegativeHeightGeometry n) :
    ∃ r : ℝ, 0 < r ∧ r < 1 / 2 ∧
      (∀ y : ℝ, y ∈ Set.Icc b n →
        riemannZeta ((r : ℂ) + y * I) ≠ 0 ∧
          deriv riemannZeta ((r : ℂ) + y * I) ≠ 0 ∧
          (speiserZetaDerivRatio ((r : ℂ) + y * I)).re < 0) ∧
      rectangleBoundaryIntegral (logDeriv (deriv riemannZeta)) 0 r b n -
          rectangleBoundaryIntegral (logDeriv riemannZeta) 0 r b n =
        2 * (Real.pi : ℂ) * I *
          (((speiserUpperLeftDerivZeroCount n : ℂ) -
              (speiserUpperLeftZetaZeroCount n : ℂ)) -
            ((speiserUpperLeftDerivZeroCount b : ℂ) -
              (speiserUpperLeftZetaZeroCount b : ℂ))) := by
  apply exists_levinsonMontgomery_negativeRight_globalCountDifference_of_topOpen_actual
    hb hbn hbottom
  intro x hx0 hxHalf
  have hx := htop.1 x hx0 hxHalf
  have hnCast : (((n : ℝ) : ℂ)) = (n : ℂ) := by norm_num
  rw [hnCast]
  simpa only [levinsonMontgomeryIntegerPoint] using And.intro hx.1 hx.2.1

/-- Real-parameter derivative of the actual ratio along a vertical line. -/
theorem hasDerivAt_speiserZetaDerivRatio_vertical
    {r y : ℝ} (hy : 0 < y)
    (hzeta : riemannZeta ((r : ℂ) + y * I) ≠ 0)
    (hderivZeta : deriv riemannZeta ((r : ℂ) + y * I) ≠ 0) :
    HasDerivAt
      (fun u : ℝ => speiserZetaDerivRatio ((r : ℂ) + u * I))
      (I * ((logDeriv (deriv riemannZeta) ((r : ℂ) + y * I) -
          logDeriv riemannZeta ((r : ℂ) + y * I)) *
        speiserZetaDerivRatio ((r : ℂ) + y * I))) y := by
  have hs : (r : ℂ) + y * I ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    norm_num at him
    linarith
  have houter :=
    hasDerivAt_speiserZetaDerivRatio hs hzeta hderivZeta
  have hline :
      HasDerivAt (fun u : ℝ => (r : ℂ) + u * I) I y := by
    have h := (((hasDerivAt_id y).ofReal_comp.mul_const I).const_add (r : ℂ))
    simpa [add_comm] using h
  change HasDerivAt
    (speiserZetaDerivRatio ∘ fun u : ℝ => (r : ℂ) + u * I) _ y
  simpa only [smul_eq_mul] using houter.scomp y hline

theorem intervalIntegrable_riemannZetaLogDeriv_vertical
    {r b t : ℝ} (hb : 0 < b) (hbt : b ≤ t)
    (hzeta : ∀ y : ℝ, y ∈ Set.Icc b t →
      riemannZeta ((r : ℂ) + y * I) ≠ 0) :
    IntervalIntegrable
      (fun y : ℝ => logDeriv riemannZeta ((r : ℂ) + y * I))
      (volume : Measure ℝ) b t := by
  apply ContinuousOn.intervalIntegrable_of_Icc hbt
  intro y hy
  have hsOne : (r : ℂ) + y * I ≠ 1 := by
    intro hs
    have him := congrArg Complex.im hs
    norm_num at him
    linarith [hb, hy.1]
  have hanalytic : AnalyticAt ℂ riemannZeta ((r : ℂ) + y * I) :=
    analyticOn_riemannZeta _ (by simpa using hsOne)
  let phi : ℝ → ℂ := fun u => (r : ℂ) + u * I
  have hphi : Continuous phi := by fun_prop
  have houter :=
    levinsonMontgomery_continuousAt_logDeriv_of_analyticAt_of_ne_zero
      hanalytic (hzeta y hy)
  simpa only [phi, Function.comp_def] using
    (ContinuousAt.comp (f := phi) (x := y)
      houter hphi.continuousAt).continuousWithinAt

theorem intervalIntegrable_riemannZetaDerivLogDeriv_vertical
    {r b t : ℝ} (hb : 0 < b) (hbt : b ≤ t)
    (hderiv : ∀ y : ℝ, y ∈ Set.Icc b t →
      deriv riemannZeta ((r : ℂ) + y * I) ≠ 0) :
    IntervalIntegrable
      (fun y : ℝ => logDeriv (deriv riemannZeta) ((r : ℂ) + y * I))
      (volume : Measure ℝ) b t := by
  apply ContinuousOn.intervalIntegrable_of_Icc hbt
  intro y hy
  have hsOne : (r : ℂ) + y * I ≠ 1 := by
    intro hs
    have him := congrArg Complex.im hs
    norm_num at him
    linarith [hb, hy.1]
  have hanalytic :
      AnalyticAt ℂ (deriv riemannZeta) ((r : ℂ) + y * I) :=
    analyticOnNhd_deriv_riemannZeta _ (by simpa using hsOne)
  let phi : ℝ → ℂ := fun u => (r : ℂ) + u * I
  have hphi : Continuous phi := by fun_prop
  have houter :=
    levinsonMontgomery_continuousAt_logDeriv_of_analyticAt_of_ne_zero
      hanalytic (hderiv y hy)
  simpa only [phi, Function.comp_def] using
    (ContinuousAt.comp (f := phi) (x := y)
      houter hphi.continuousAt).continuousWithinAt

/-- On a strict-negative vertical side, its contribution to the contour difference is the
endpoint change of one principal logarithm. In particular, its imaginary part is an argument
change rather than a logarithmic-modulus change. -/
theorem intervalIntegral_speiserZetaDerivRatio_vertical
    {r b t : ℝ} (hb : 0 < b) (hbt : b ≤ t)
    (hright : ∀ y : ℝ, y ∈ Set.Icc b t →
      riemannZeta ((r : ℂ) + y * I) ≠ 0 ∧
        deriv riemannZeta ((r : ℂ) + y * I) ≠ 0 ∧
        (speiserZetaDerivRatio ((r : ℂ) + y * I)).re < 0) :
    I * (∫ y : ℝ in b..t,
      (logDeriv (deriv riemannZeta) ((r : ℂ) + y * I) -
        logDeriv riemannZeta ((r : ℂ) + y * I))) =
      Complex.log (-speiserZetaDerivRatio ((r : ℂ) + t * I)) -
        Complex.log (-speiserZetaDerivRatio ((r : ℂ) + b * I)) := by
  let g : ℝ → ℂ := fun y =>
    speiserZetaDerivRatio ((r : ℂ) + y * I)
  let d : ℝ → ℂ := fun y =>
    logDeriv (deriv riemannZeta) ((r : ℂ) + y * I) -
      logDeriv riemannZeta ((r : ℂ) + y * I)
  let g' : ℝ → ℂ := fun y => I * (d y * g y)
  have huIcc : Set.uIcc b t = Set.Icc b t :=
    Set.uIcc_of_le hbt
  have hderiv : ∀ y ∈ Set.uIcc b t, HasDerivAt g (g' y) y := by
    intro y hy
    have hyIcc : y ∈ Set.Icc b t := by simpa only [huIcc] using hy
    have hyPos : 0 < y := hb.trans_le hyIcc.1
    have hdata := hright y hyIcc
    exact hasDerivAt_speiserZetaDerivRatio_vertical hyPos hdata.1 hdata.2.1
  have hneg : ∀ y ∈ Set.uIcc b t, (g y).re < 0 := by
    intro y hy
    have hyIcc : y ∈ Set.Icc b t := by simpa only [huIcc] using hy
    exact (hright y hyIcc).2.2
  have hzetaInt :
      IntervalIntegrable
        (fun y : ℝ => logDeriv riemannZeta ((r : ℂ) + y * I))
        (volume : Measure ℝ) b t := by
    apply ContinuousOn.intervalIntegrable_of_Icc hbt
    intro y hy
    have hsOne : (r : ℂ) + y * I ≠ 1 := by
      intro hs
      have him := congrArg Complex.im hs
      norm_num at him
      linarith [hb, hy.1]
    have hanalytic : AnalyticAt ℂ riemannZeta ((r : ℂ) + y * I) :=
      analyticOn_riemannZeta _ (by simpa using hsOne)
    let phi : ℝ → ℂ := fun u => (r : ℂ) + u * I
    have hphi : Continuous phi := by fun_prop
    have houter :=
      levinsonMontgomery_continuousAt_logDeriv_of_analyticAt_of_ne_zero
        hanalytic (hright y hy).1
    simpa only [phi, Function.comp_def] using
      (ContinuousAt.comp (f := phi) (x := y) houter hphi.continuousAt).continuousWithinAt
  have hderivInt :
      IntervalIntegrable
        (fun y : ℝ => logDeriv (deriv riemannZeta) ((r : ℂ) + y * I))
        (volume : Measure ℝ) b t := by
    apply ContinuousOn.intervalIntegrable_of_Icc hbt
    intro y hy
    have hsOne : (r : ℂ) + y * I ≠ 1 := by
      intro hs
      have him := congrArg Complex.im hs
      norm_num at him
      linarith [hb, hy.1]
    have hanalytic :
        AnalyticAt ℂ (deriv riemannZeta) ((r : ℂ) + y * I) :=
      analyticOnNhd_deriv_riemannZeta _ (by simpa using hsOne)
    let phi : ℝ → ℂ := fun u => (r : ℂ) + u * I
    have hphi : Continuous phi := by fun_prop
    have houter :=
      levinsonMontgomery_continuousAt_logDeriv_of_analyticAt_of_ne_zero
        hanalytic (hright y hy).2.1
    simpa only [phi, Function.comp_def] using
      (ContinuousAt.comp (f := phi) (x := y) houter hphi.continuousAt).continuousWithinAt
  have hdInt : IntervalIntegrable d (volume : Measure ℝ) b t := by
    exact hderivInt.sub hzetaInt
  have hpoint : ∀ y ∈ Set.uIcc b t, g' y / g y = I * d y := by
    intro y hy
    have hyIcc : y ∈ Set.Icc b t := by simpa only [huIcc] using hy
    have hgNe : g y ≠ 0 := by
      dsimp only [g, speiserZetaDerivRatio]
      exact div_ne_zero (hright y hyIcc).2.1 (hright y hyIcc).1
    dsimp only [g']
    rw [mul_div_assoc, mul_div_cancel_right₀ _ hgNe]
  have hquotInt :
      IntervalIntegrable (fun y => g' y / g y)
        (volume : Measure ℝ) b t := by
    apply (hdInt.const_mul I).congr
    intro y hy
    exact (hpoint y (Set.uIoc_subset_uIcc hy)).symm
  have hformula :=
    intervalIntegral_deriv_div_eq_log_sub_of_re_neg
      hderiv hquotInt hneg
  calc
    I * (∫ y : ℝ in b..t,
      (logDeriv (deriv riemannZeta) ((r : ℂ) + y * I) -
        logDeriv riemannZeta ((r : ℂ) + y * I))) =
        ∫ y : ℝ in b..t, I * d y := by
          rw [intervalIntegral.integral_const_mul]
    _ = ∫ y : ℝ in b..t, g' y / g y := by
      apply intervalIntegral.integral_congr
      intro y hy
      exact (hpoint y hy).symm
    _ = Complex.log (-g t) - Complex.log (-g b) := hformula
    _ = Complex.log (-speiserZetaDerivRatio ((r : ℂ) + t * I)) -
        Complex.log (-speiserZetaDerivRatio ((r : ℂ) + b * I)) := by
          rfl

/-- Strict left-half-plane containment bounds the argument variation on any such vertical side
by `pi`, independently of its length. -/
theorem abs_im_I_mul_intervalIntegral_logDerivDifference_vertical_le_pi
    {r b t : ℝ} (hb : 0 < b) (hbt : b ≤ t)
    (hright : ∀ y : ℝ, y ∈ Set.Icc b t →
      riemannZeta ((r : ℂ) + y * I) ≠ 0 ∧
        deriv riemannZeta ((r : ℂ) + y * I) ≠ 0 ∧
        (speiserZetaDerivRatio ((r : ℂ) + y * I)).re < 0) :
    abs ((I * (∫ y : ℝ in b..t,
      (logDeriv (deriv riemannZeta) ((r : ℂ) + y * I) -
        logDeriv riemannZeta ((r : ℂ) + y * I)))).im) ≤ Real.pi := by
  rw [intervalIntegral_speiserZetaDerivRatio_vertical hb hbt hright]
  simp only [Complex.sub_im, Complex.log_im]
  have hbData := hright b ⟨le_rfl, hbt⟩
  have htData := hright t ⟨hbt, le_rfl⟩
  calc
    |Complex.arg (-speiserZetaDerivRatio ((r : ℂ) + t * I)) -
        Complex.arg (-speiserZetaDerivRatio ((r : ℂ) + b * I))| ≤
      |Complex.arg (-speiserZetaDerivRatio ((r : ℂ) + t * I))| +
        |Complex.arg (-speiserZetaDerivRatio ((r : ℂ) + b * I))| :=
          abs_sub _ _
    _ ≤ Real.pi / 2 + Real.pi / 2 := add_le_add
      (Complex.abs_arg_le_pi_div_two_iff.mpr (by
        simpa only [neg_re] using neg_nonneg.mpr htData.2.2.le))
      (Complex.abs_arg_le_pi_div_two_iff.mpr (by
        simpa only [neg_re] using neg_nonneg.mpr hbData.2.2.le))
    _ = Real.pi := by ring

/-- The same vertical bound in the separate-integrals form appearing after the rectangle boundary
is unfolded. -/
theorem abs_im_I_mul_sub_intervalIntegrals_logDeriv_vertical_le_pi
    {r b t : ℝ} (hb : 0 < b) (hbt : b ≤ t)
    (hright : ∀ y : ℝ, y ∈ Set.Icc b t →
      riemannZeta ((r : ℂ) + y * I) ≠ 0 ∧
        deriv riemannZeta ((r : ℂ) + y * I) ≠ 0 ∧
        (speiserZetaDerivRatio ((r : ℂ) + y * I)).re < 0) :
    abs ((I *
      ((∫ y : ℝ in b..t,
          logDeriv (deriv riemannZeta) ((r : ℂ) + y * I)) -
        ∫ y : ℝ in b..t,
          logDeriv riemannZeta ((r : ℂ) + y * I))).im) ≤ Real.pi := by
  have hzInt := intervalIntegrable_riemannZetaLogDeriv_vertical
    hb hbt (fun y hy => (hright y hy).1)
  have hdInt := intervalIntegrable_riemannZetaDerivLogDeriv_vertical
    hb hbt (fun y hy => (hright y hy).2.1)
  rw [← intervalIntegral.integral_sub hdInt hzInt]
  exact abs_im_I_mul_intervalIntegral_logDerivDifference_vertical_le_pi
    hb hbt hright

/-- The fixed left vertical side has the same strict-negative ratio geometry as the adaptive
right side. -/
theorem levinsonMontgomery_leftVertical_negative
    {b t : ℝ} (hb : 10 ≤ b) :
    ∀ y : ℝ, y ∈ Set.Icc b t →
      riemannZeta (y * I) ≠ 0 ∧
        deriv riemannZeta (y * I) ≠ 0 ∧
        (speiserZetaDerivRatio (y * I)).re < 0 := by
  intro y hy
  let s : ℂ := y * I
  have hsRe : s.re = 0 := by simp [s]
  have hsIm : 10 ≤ s.im := by
    have hsImEq : s.im = y := by simp [s]
    rw [hsImEq]
    exact hb.trans hy.1
  have hsData :=
    levinsonMontgomery_logDeriv_riemannZeta_re_neg_on_left_boundary hsRe hsIm
  have hsDeriv : deriv riemannZeta s ≠ 0 := by
    intro hzero
    have hneg := hsData.2
    rw [logDeriv_apply, hzero, zero_div, Complex.zero_re] at hneg
    exact (lt_irrefl 0) hneg
  have hsRatio : (speiserZetaDerivRatio s).re < 0 := by
    simpa only [speiserZetaDerivRatio, logDeriv_apply] using hsData.2
  simpa only [s] using ⟨hsData.1, hsDeriv, hsRatio⟩

/-- The left vertical contribution has uniformly bounded argument variation. -/
theorem abs_im_I_mul_intervalIntegral_logDerivDifference_left_le_pi
    {b t : ℝ} (hb : 10 ≤ b) (hbt : b ≤ t) :
    abs ((I * (∫ y : ℝ in b..t,
      (logDeriv (deriv riemannZeta) (y * I) -
        logDeriv riemannZeta (y * I)))).im) ≤ Real.pi := by
  have hdata : ∀ y : ℝ, y ∈ Set.Icc b t →
      riemannZeta (((0 : ℝ) : ℂ) + y * I) ≠ 0 ∧
        deriv riemannZeta (((0 : ℝ) : ℂ) + y * I) ≠ 0 ∧
        (speiserZetaDerivRatio (((0 : ℝ) : ℂ) + y * I)).re < 0 := by
    intro y hy
    simpa using levinsonMontgomery_leftVertical_negative hb y hy
  simpa using
    (abs_im_I_mul_intervalIntegral_logDerivDifference_vertical_le_pi
      (r := (0 : ℝ)) (by linarith) hbt hdata)

/-- The zeta top-side argument variation on any initial subinterval is charged to the same
Jensen crossing support as the complete source segment. -/
theorem abs_im_levinsonMontgomeryZetaTopLogDeriv_zero_rightCutoff_le_card
    {t r : ℝ} (htLarge : 23 ≤ t)
    (ht : LevinsonMontgomeryTopAdmissible t)
    (hr0 : 0 < r) (hrOne : r ≤ 1) :
    abs ((∫ sigma : ℝ in (0 : ℝ)..r,
      logDeriv riemannZeta (sigma + t * I)).im) ≤
      Real.pi *
        (((levinsonMontgomeryZetaTopCrossingFinset t).card : ℝ) + 1) := by
  have hsubset : Set.Icc (0 : ℝ) r ⊆ Set.Icc (0 : ℝ) 1 := by
    intro sigma hsigma
    exact ⟨hsigma.1, hsigma.2.trans hrOne⟩
  have hintegrable :
      IntervalIntegrable
        (fun sigma : ℝ => logDeriv riemannZeta (sigma + t * I))
        (volume : Measure ℝ) (0 : ℝ) r := by
    apply (intervalIntegrable_levinsonMontgomeryZetaLogDeriv_top ht).mono_set
    intro sigma hsigma
    have hsigmaIcc : sigma ∈ Set.Icc (0 : ℝ) r := by
      simpa only [Set.uIcc_of_le hr0.le] using hsigma
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
      hsubset hsigmaIcc
  have hsource :=
    abs_im_intervalIntegral_deriv_div_le_of_crossings_subset
      (g := fun sigma : ℝ => riemannZeta (sigma + t * I))
      (g' := fun sigma : ℝ => deriv riemannZeta (sigma + t * I))
      (a := (0 : ℝ)) (b := r) hr0.le
      (fun sigma _ => hasDerivAt_riemannZeta_top ht.1)
      (by simpa only [logDeriv_apply] using hintegrable)
      (fun sigma hsigma => (ht.2 sigma (hsubset hsigma)).1)
      (levinsonMontgomeryZetaTopCrossingFinset t)
      (fun sigma hsigma hzero =>
        levinsonMontgomeryZetaTop_crossing_mem_crossingFinset
          htLarge (hsubset (Set.Ioo_subset_Icc_self hsigma)) hzero)
  simpa only [logDeriv_apply] using hsource

/-- The phase-normalized derivative gives the analogous initial-subinterval bound for `zeta'`.
The phase cancels from its logarithmic derivative. -/
theorem abs_im_levinsonMontgomeryZetaDerivTopLogDeriv_zero_rightCutoff_le_card
    {t r : ℝ} (htLarge : 23 ≤ t)
    (ht : LevinsonMontgomeryTopAdmissible t)
    (hr0 : 0 < r) (hrOne : r ≤ 1) :
    abs ((∫ sigma : ℝ in (0 : ℝ)..r,
      logDeriv (deriv riemannZeta) (sigma + t * I)).im) ≤
      Real.pi *
        (((levinsonMontgomeryZetaDerivTopCrossingFinset t).card : ℝ) + 1) := by
  let phase : ℂ := levinsonMontgomeryDerivPhase t
  let g : ℝ → ℂ := fun sigma =>
    phase * deriv riemannZeta (sigma + t * I)
  let g' : ℝ → ℂ := fun sigma =>
    phase * deriv (deriv riemannZeta) (sigma + t * I)
  have hphase : phase ≠ 0 := by
    exact levinsonMontgomeryDerivPhase_ne_zero t
  have hsubset : Set.Icc (0 : ℝ) r ⊆ Set.Icc (0 : ℝ) 1 := by
    intro sigma hsigma
    exact ⟨hsigma.1, hsigma.2.trans hrOne⟩
  have hquot : ∀ sigma : ℝ,
      g' sigma / g sigma =
        logDeriv (deriv riemannZeta) (sigma + t * I) := by
    intro sigma
    dsimp only [g, g', phase]
    rw [logDeriv_apply]
    exact mul_div_mul_left _ _ (levinsonMontgomeryDerivPhase_ne_zero t)
  have hbaseInt :
      IntervalIntegrable
        (fun sigma : ℝ =>
          logDeriv (deriv riemannZeta) (sigma + t * I))
        (volume : Measure ℝ) (0 : ℝ) r := by
    apply
      (intervalIntegrable_levinsonMontgomeryZetaDerivLogDeriv_top ht).mono_set
    intro sigma hsigma
    have hsigmaIcc : sigma ∈ Set.Icc (0 : ℝ) r := by
      simpa only [Set.uIcc_of_le hr0.le] using hsigma
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
      hsubset hsigmaIcc
  have hquotInt :
      IntervalIntegrable (fun sigma => g' sigma / g sigma)
        (volume : Measure ℝ) (0 : ℝ) r := by
    apply hbaseInt.congr
    intro sigma _hsigma
    exact (hquot sigma).symm
  have hsource :=
    abs_im_intervalIntegral_deriv_div_le_of_crossings_subset
      (g := g) (g' := g') (a := (0 : ℝ)) (b := r) hr0.le
      (fun sigma _ => by
        dsimp only [g, g', phase]
        exact
          (hasDerivAt_riemannZetaDeriv_top
            (sigma := sigma) ht.1).const_mul
              (levinsonMontgomeryDerivPhase t))
      hquotInt
      (fun sigma hsigma => by
        dsimp only [g, phase]
        exact mul_ne_zero hphase (ht.2 sigma (hsubset hsigma)).2)
      (levinsonMontgomeryZetaDerivTopCrossingFinset t)
      (fun sigma hsigma hzero => by
        apply
          levinsonMontgomeryZetaDerivTop_crossing_mem_crossingFinset
            htLarge (hsubset (Set.Ioo_subset_Icc_self hsigma))
        simpa only [g, phase] using hzero)
  calc
    abs ((∫ sigma : ℝ in (0 : ℝ)..r,
      logDeriv (deriv riemannZeta) (sigma + t * I)).im) =
        abs ((∫ sigma : ℝ in (0 : ℝ)..r,
          g' sigma / g sigma).im) := by
            congr 2
            apply intervalIntegral.integral_congr
            intro sigma _hsigma
            exact (hquot sigma).symm
    _ ≤ Real.pi *
        (((levinsonMontgomeryZetaDerivTopCrossingFinset t).card : ℝ) + 1) :=
      hsource

/-- The actual zeta top variation is `O(log(t+2))` uniformly over all initial cutoffs in
`(0,1]`. -/
theorem exists_abs_im_levinsonMontgomeryZetaTopLogDeriv_zero_rightCutoff_le_log :
    ∃ C T0 : ℝ, 0 ≤ C ∧
      ∀ t r : ℝ, T0 ≤ t → LevinsonMontgomeryTopAdmissible t →
        0 < r → r ≤ 1 →
        abs ((∫ sigma : ℝ in (0 : ℝ)..r,
          logDeriv riemannZeta (sigma + t * I)).im) ≤
            C * Real.log (t + 2) := by
  obtain ⟨C, T0, hC, hJensen⟩ :=
    exists_levinsonMontgomeryZetaTopSymm_sum_divisor_le_log
  let C' : ℝ := Real.pi * (C + 1)
  let T0' : ℝ := max T0 23
  refine ⟨C', T0', ?_, ?_⟩
  · dsimp only [C']
    exact mul_nonneg Real.pi_pos.le (by linarith)
  intro t r htLarge ht hr0 hrOne
  have htJensen : T0 ≤ t := (le_max_left T0 23).trans htLarge
  have htTwentyThree : 23 ≤ t := (le_max_right T0 23).trans htLarge
  have hlogOne : 1 ≤ Real.log (t + 2) := by
    apply (Real.le_log_iff_exp_le (by linarith)).mpr
    exact Real.exp_one_lt_three.le.trans (by linarith)
  have hcardInt :=
    zetaTopCrossingFinset_card_le_divisorSum t htTwentyThree
  have hcard :
      ((levinsonMontgomeryZetaTopCrossingFinset t).card : ℝ) ≤
        (((∑ᶠ z : ℂ,
          MeromorphicOn.divisor (levinsonMontgomeryZetaTopSymm t)
            (Metric.closedBall levinsonMontgomeryJensenCenter
              levinsonMontgomeryJensenInnerRadius) z) : ℤ) : ℝ) := by
    exact_mod_cast hcardInt
  have hdivisor := hJensen t htJensen
  calc
    abs ((∫ sigma : ℝ in (0 : ℝ)..r,
      logDeriv riemannZeta (sigma + t * I)).im) ≤
        Real.pi *
          (((levinsonMontgomeryZetaTopCrossingFinset t).card : ℝ) + 1) :=
      abs_im_levinsonMontgomeryZetaTopLogDeriv_zero_rightCutoff_le_card
        htTwentyThree ht hr0 hrOne
    _ ≤ Real.pi *
        (((((∑ᶠ z : ℂ,
          MeromorphicOn.divisor (levinsonMontgomeryZetaTopSymm t)
            (Metric.closedBall levinsonMontgomeryJensenCenter
              levinsonMontgomeryJensenInnerRadius) z) : ℤ) : ℝ)) + 1) := by
      gcongr
    _ ≤ Real.pi * (C * Real.log (t + 2) + 1) := by
      gcongr
    _ ≤ Real.pi * ((C + 1) * Real.log (t + 2)) := by
      gcongr
      nlinarith
    _ = C' * Real.log (t + 2) := by
      dsimp only [C']
      ring

/-- The actual zeta-derivative top variation satisfies the same uniform initial-cutoff
estimate. -/
theorem exists_abs_im_levinsonMontgomeryZetaDerivTopLogDeriv_zero_rightCutoff_le_log :
    ∃ C T0 : ℝ, 0 ≤ C ∧
      ∀ t r : ℝ, T0 ≤ t → LevinsonMontgomeryTopAdmissible t →
        0 < r → r ≤ 1 →
        abs ((∫ sigma : ℝ in (0 : ℝ)..r,
          logDeriv (deriv riemannZeta) (sigma + t * I)).im) ≤
            C * Real.log (t + 2) := by
  obtain ⟨C, T0, hC, hJensen⟩ :=
    exists_levinsonMontgomeryZetaDerivTopSymm_sum_divisor_le_log
  let C' : ℝ := Real.pi * (C + 1)
  let T0' : ℝ := max T0 23
  refine ⟨C', T0', ?_, ?_⟩
  · dsimp only [C']
    exact mul_nonneg Real.pi_pos.le (by linarith)
  intro t r htLarge ht hr0 hrOne
  have htJensen : T0 ≤ t := (le_max_left T0 23).trans htLarge
  have htTwentyThree : 23 ≤ t := (le_max_right T0 23).trans htLarge
  have hlogOne : 1 ≤ Real.log (t + 2) := by
    apply (Real.le_log_iff_exp_le (by linarith)).mpr
    exact Real.exp_one_lt_three.le.trans (by linarith)
  have hcardInt :=
    zetaDerivTopCrossingFinset_card_le_divisorSum t htTwentyThree
  have hcard :
      ((levinsonMontgomeryZetaDerivTopCrossingFinset t).card : ℝ) ≤
        (((∑ᶠ z : ℂ,
          MeromorphicOn.divisor (levinsonMontgomeryZetaDerivTopSymm t)
            (Metric.closedBall levinsonMontgomeryJensenCenter
              levinsonMontgomeryJensenInnerRadius) z) : ℤ) : ℝ) := by
    exact_mod_cast hcardInt
  have hdivisor := hJensen t htJensen
  calc
    abs ((∫ sigma : ℝ in (0 : ℝ)..r,
      logDeriv (deriv riemannZeta) (sigma + t * I)).im) ≤
        Real.pi *
          (((levinsonMontgomeryZetaDerivTopCrossingFinset t).card : ℝ) + 1) :=
      abs_im_levinsonMontgomeryZetaDerivTopLogDeriv_zero_rightCutoff_le_card
        htTwentyThree ht hr0 hrOne
    _ ≤ Real.pi *
        (((((∑ᶠ z : ℂ,
          MeromorphicOn.divisor (levinsonMontgomeryZetaDerivTopSymm t)
            (Metric.closedBall levinsonMontgomeryJensenCenter
              levinsonMontgomeryJensenInnerRadius) z) : ℤ) : ℝ)) + 1) := by
      gcongr
    _ ≤ Real.pi * (C * Real.log (t + 2) + 1) := by
      gcongr
    _ ≤ Real.pi * ((C + 1) * Real.log (t + 2)) := by
      gcongr
      nlinarith
    _ = C' * Real.log (t + 2) := by
      dsimp only [C']
      ring

/-- The top contribution to the logarithmic-derivative difference is uniformly `O(log(t+2))`
on every adaptive initial cutoff. -/
theorem exists_abs_im_levinsonMontgomeryTopLogDerivDifference_zero_rightCutoff_le_log :
    ∃ C T0 : ℝ, 0 ≤ C ∧
      ∀ t r : ℝ, T0 ≤ t → LevinsonMontgomeryTopAdmissible t →
        0 < r → r ≤ 1 →
        abs ((∫ sigma : ℝ in (0 : ℝ)..r,
          (logDeriv (deriv riemannZeta) (sigma + t * I) -
            logDeriv riemannZeta (sigma + t * I))).im) ≤
              C * Real.log (t + 2) := by
  obtain ⟨Cz, Tz, hCz, hz⟩ :=
    exists_abs_im_levinsonMontgomeryZetaTopLogDeriv_zero_rightCutoff_le_log
  obtain ⟨Cd, Td, hCd, hd⟩ :=
    exists_abs_im_levinsonMontgomeryZetaDerivTopLogDeriv_zero_rightCutoff_le_log
  refine ⟨Cd + Cz, max Tz Td, add_nonneg hCd hCz, ?_⟩
  intro t r htLarge ht hr0 hrOne
  have htZ : Tz ≤ t := (le_max_left Tz Td).trans htLarge
  have htD : Td ≤ t := (le_max_right Tz Td).trans htLarge
  have hsubset : Set.uIcc (0 : ℝ) r ⊆ Set.uIcc (0 : ℝ) 1 := by
    intro sigma hsigma
    rw [Set.uIcc_of_le hr0.le] at hsigma
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ⟨hsigma.1, hsigma.2.trans hrOne⟩
  have hzInt :
      IntervalIntegrable
        (fun sigma : ℝ => logDeriv riemannZeta (sigma + t * I))
        (volume : Measure ℝ) (0 : ℝ) r :=
    (intervalIntegrable_levinsonMontgomeryZetaLogDeriv_top ht).mono_set hsubset
  have hdInt :
      IntervalIntegrable
        (fun sigma : ℝ => logDeriv (deriv riemannZeta) (sigma + t * I))
        (volume : Measure ℝ) (0 : ℝ) r :=
    (intervalIntegrable_levinsonMontgomeryZetaDerivLogDeriv_top ht).mono_set hsubset
  have hzBound := hz t r htZ ht hr0 hrOne
  have hdBound := hd t r htD ht hr0 hrOne
  rw [intervalIntegral.integral_sub hdInt hzInt, Complex.sub_im]
  calc
    |(∫ sigma : ℝ in (0 : ℝ)..r,
        logDeriv (deriv riemannZeta) (sigma + t * I)).im -
      (∫ sigma : ℝ in (0 : ℝ)..r,
        logDeriv riemannZeta (sigma + t * I)).im| ≤
        |(∫ sigma : ℝ in (0 : ℝ)..r,
          logDeriv (deriv riemannZeta) (sigma + t * I)).im| +
        |(∫ sigma : ℝ in (0 : ℝ)..r,
          logDeriv riemannZeta (sigma + t * I)).im| := abs_sub _ _
    _ ≤ Cd * Real.log (t + 2) + Cz * Real.log (t + 2) :=
      add_le_add hdBound hzBound
    _ = (Cd + Cz) * Real.log (t + 2) := by ring

/-- A fixed common zero-free bottom controls both partial horizontal integrals uniformly over
all adaptive cutoffs left of the critical line. -/
theorem exists_speiserUniformPartialBottomLogDerivBound
    {b : ℝ} (hbottom : SpeiserCommonZeroFreeHorizontal b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 ≤ r → r ≤ 1 / 2 →
      ‖∫ sigma : ℝ in (0 : ℝ)..r,
          logDeriv riemannZeta (sigma + b * I)‖ +
        ‖∫ sigma : ℝ in (0 : ℝ)..r,
          logDeriv (deriv riemannZeta) (sigma + b * I)‖ ≤ C := by
  let fz : ℝ → ℂ := fun sigma =>
    logDeriv riemannZeta (sigma + b * I)
  let fd : ℝ → ℂ := fun sigma =>
    logDeriv (deriv riemannZeta) (sigma + b * I)
  have hcontZ : ContinuousOn fz (Set.Icc (0 : ℝ) (1 / 2)) := by
    intro sigma hsigma
    have hsOne : (sigma : ℂ) + b * I ≠ 1 := by
      intro hs
      have him := congrArg Complex.im hs
      norm_num at him
      linarith [hbottom.1]
    have hanalytic : AnalyticAt ℂ riemannZeta ((sigma : ℂ) + b * I) :=
      analyticOn_riemannZeta _ (by simpa using hsOne)
    let phi : ℝ → ℂ := fun x => x + b * I
    have hphi : Continuous phi := by fun_prop
    have houter :=
      levinsonMontgomery_continuousAt_logDeriv_of_analyticAt_of_ne_zero
        hanalytic (hbottom.2 sigma hsigma).1
    simpa only [fz, phi, Function.comp_def] using
      (ContinuousAt.comp (f := phi) (x := sigma)
        houter hphi.continuousAt).continuousWithinAt
  have hcontD : ContinuousOn fd (Set.Icc (0 : ℝ) (1 / 2)) := by
    intro sigma hsigma
    have hsOne : (sigma : ℂ) + b * I ≠ 1 := by
      intro hs
      have him := congrArg Complex.im hs
      norm_num at him
      linarith [hbottom.1]
    have hanalytic :
        AnalyticAt ℂ (deriv riemannZeta) ((sigma : ℂ) + b * I) :=
      analyticOnNhd_deriv_riemannZeta _ (by simpa using hsOne)
    let phi : ℝ → ℂ := fun x => x + b * I
    have hphi : Continuous phi := by fun_prop
    have houter :=
      levinsonMontgomery_continuousAt_logDeriv_of_analyticAt_of_ne_zero
        hanalytic (hbottom.2 sigma hsigma).2
    simpa only [fd, phi, Function.comp_def] using
      (ContinuousAt.comp (f := phi) (x := sigma)
        houter hphi.continuousAt).continuousWithinAt
  have hcontNorm : ContinuousOn (fun sigma => ‖fz sigma‖ + ‖fd sigma‖)
      (Set.Icc (0 : ℝ) (1 / 2)) :=
    hcontZ.norm.add hcontD.norm
  obtain ⟨B0, hB0⟩ := bddAbove_def.mp
    (isCompact_Icc.bddAbove_image hcontNorm)
  let B : ℝ := |B0| + 1
  have hB : 0 ≤ B := by
    dsimp only [B]
    linarith [abs_nonneg B0]
  have hBbound : ∀ sigma ∈ Set.Icc (0 : ℝ) (1 / 2),
      ‖fz sigma‖ + ‖fd sigma‖ ≤ B := by
    intro sigma hsigma
    calc
      ‖fz sigma‖ + ‖fd sigma‖ ≤ B0 :=
        hB0 _ ⟨sigma, hsigma, rfl⟩
      _ ≤ |B0| := le_abs_self B0
      _ ≤ B := by simp [B]
  refine ⟨B, hB, ?_⟩
  intro r hr0 hrHalf
  have hinterval : ∀ sigma ∈ Set.uIoc (0 : ℝ) r,
      sigma ∈ Set.Icc (0 : ℝ) (1 / 2) := by
    intro sigma hsigma
    have hsigmaIcc : sigma ∈ Set.uIcc (0 : ℝ) r :=
      Set.uIoc_subset_uIcc hsigma
    rw [Set.uIcc_of_le hr0] at hsigmaIcc
    exact ⟨hsigmaIcc.1, hsigmaIcc.2.trans hrHalf⟩
  have hzPoint : ∀ sigma ∈ Set.uIoc (0 : ℝ) r, ‖fz sigma‖ ≤ B := by
    intro sigma hsigma
    exact (le_add_of_nonneg_right (norm_nonneg (fd sigma))).trans
      (hBbound sigma (hinterval sigma hsigma))
  have hdPoint : ∀ sigma ∈ Set.uIoc (0 : ℝ) r, ‖fd sigma‖ ≤ B := by
    intro sigma hsigma
    exact (le_add_of_nonneg_left (norm_nonneg (fz sigma))).trans
      (hBbound sigma (hinterval sigma hsigma))
  have hzNorm := intervalIntegral.norm_integral_le_of_norm_le_const hzPoint
  have hdNorm := intervalIntegral.norm_integral_le_of_norm_le_const hdPoint
  have habs : |r - 0| = r := by simp [abs_of_nonneg hr0]
  rw [habs] at hzNorm hdNorm
  change ‖∫ sigma : ℝ in (0 : ℝ)..r, fz sigma‖ +
      ‖∫ sigma : ℝ in (0 : ℝ)..r, fd sigma‖ ≤ B
  calc
    ‖∫ sigma : ℝ in (0 : ℝ)..r, fz sigma‖ +
        ‖∫ sigma : ℝ in (0 : ℝ)..r, fd sigma‖ ≤
      B * r + B * r := add_le_add hzNorm hdNorm
    _ ≤ B := by nlinarith [mul_nonneg hB hr0]

/-- For one fixed common zero-free bottom, the complete boundary-integral difference is
`O(log(t+2))` at every admissible top and every strict-negative adaptive right cutoff. -/
theorem exists_abs_im_levinsonMontgomeryRectangleLogDerivDifference_le_log
    {b : ℝ} (hb : 10 < b)
    (hbottom : SpeiserCommonZeroFreeHorizontal b) :
    ∃ C T0 : ℝ, 0 ≤ C ∧
      ∀ t r : ℝ, T0 ≤ t → b < t → LevinsonMontgomeryTopAdmissible t →
        0 < r → r < 1 / 2 →
        (∀ y : ℝ, y ∈ Set.Icc b t →
          riemannZeta ((r : ℂ) + y * I) ≠ 0 ∧
            deriv riemannZeta ((r : ℂ) + y * I) ≠ 0 ∧
            (speiserZetaDerivRatio ((r : ℂ) + y * I)).re < 0) →
        abs ((rectangleBoundaryIntegral (logDeriv (deriv riemannZeta)) 0 r b t -
          rectangleBoundaryIntegral (logDeriv riemannZeta) 0 r b t).im) ≤
            C * Real.log (t + 2) := by
  obtain ⟨Ct, Tt, hCt, htop⟩ :=
    exists_abs_im_levinsonMontgomeryTopLogDerivDifference_zero_rightCutoff_le_log
  obtain ⟨Cb, hCb, hbottomBound⟩ :=
    exists_speiserUniformPartialBottomLogDerivBound hbottom
  let C : ℝ := Ct + Cb + 2 * Real.pi
  let T0 : ℝ := max Tt 1
  refine ⟨C, T0, ?_, ?_⟩
  · dsimp only [C]
    positivity
  intro t r htLarge hbt htopAdmissible hr0 hrHalf hright
  have htTop : Tt ≤ t := (le_max_left Tt 1).trans htLarge
  have htOne : 1 ≤ t := (le_max_right Tt 1).trans htLarge
  have hlogOne : 1 ≤ Real.log (t + 2) := by
    apply (Real.le_log_iff_exp_le (by linarith)).mpr
    exact Real.exp_one_lt_three.le.trans (by linarith)
  have hrOne : r ≤ 1 := hrHalf.le.trans (by norm_num)
  let bottomD : ℂ := ∫ sigma : ℝ in (0 : ℝ)..r,
    logDeriv (deriv riemannZeta) (sigma + b * I)
  let bottomZ : ℂ := ∫ sigma : ℝ in (0 : ℝ)..r,
    logDeriv riemannZeta (sigma + b * I)
  let topD : ℂ := ∫ sigma : ℝ in (0 : ℝ)..r,
    logDeriv (deriv riemannZeta) (sigma + t * I)
  let topZ : ℂ := ∫ sigma : ℝ in (0 : ℝ)..r,
    logDeriv riemannZeta (sigma + t * I)
  let rightD : ℂ := ∫ y : ℝ in b..t,
    logDeriv (deriv riemannZeta) ((r : ℂ) + y * I)
  let rightZ : ℂ := ∫ y : ℝ in b..t,
    logDeriv riemannZeta ((r : ℂ) + y * I)
  let leftD : ℂ := ∫ y : ℝ in b..t,
    logDeriv (deriv riemannZeta) (y * I)
  let leftZ : ℂ := ∫ y : ℝ in b..t,
    logDeriv riemannZeta (y * I)
  have hbottomIm : abs ((bottomD - bottomZ).im) ≤ Cb := by
    calc
      |(bottomD - bottomZ).im| ≤ ‖bottomD - bottomZ‖ :=
        Complex.abs_im_le_norm _
      _ ≤ ‖bottomD‖ + ‖bottomZ‖ := norm_sub_le _ _
      _ ≤ Cb := by
        simpa only [bottomD, bottomZ, add_comm] using
          hbottomBound r hr0.le hrHalf.le
  have htopIm :
      abs ((topD - topZ).im) ≤ Ct * Real.log (t + 2) := by
    have hsubset : Set.uIcc (0 : ℝ) r ⊆ Set.uIcc (0 : ℝ) 1 := by
      intro sigma hsigma
      rw [Set.uIcc_of_le hr0.le] at hsigma
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact ⟨hsigma.1, hsigma.2.trans hrOne⟩
    have hzInt :=
      (intervalIntegrable_levinsonMontgomeryZetaLogDeriv_top
        htopAdmissible).mono_set hsubset
    have hdInt :=
      (intervalIntegrable_levinsonMontgomeryZetaDerivLogDeriv_top
        htopAdmissible).mono_set hsubset
    dsimp only [topD, topZ]
    rw [← intervalIntegral.integral_sub hdInt hzInt]
    exact htop t r htTop htopAdmissible hr0 hrOne
  have hrightIm : abs ((I * (rightD - rightZ)).im) ≤ Real.pi := by
    simpa only [rightD, rightZ] using
      abs_im_I_mul_sub_intervalIntegrals_logDeriv_vertical_le_pi
        (by linarith) hbt.le hright
  have hleftData : ∀ y : ℝ, y ∈ Set.Icc b t →
      riemannZeta (((0 : ℝ) : ℂ) + y * I) ≠ 0 ∧
        deriv riemannZeta (((0 : ℝ) : ℂ) + y * I) ≠ 0 ∧
        (speiserZetaDerivRatio (((0 : ℝ) : ℂ) + y * I)).re < 0 := by
    intro y hy
    simpa using levinsonMontgomery_leftVertical_negative hb.le y hy
  have hleftIm : abs ((I * (leftD - leftZ)).im) ≤ Real.pi := by
    simpa only [leftD, leftZ, ofReal_zero, zero_add] using
      abs_im_I_mul_sub_intervalIntegrals_logDeriv_vertical_le_pi
        (r := (0 : ℝ)) (by linarith) hbt.le hleftData
  have hboundary :
      rectangleBoundaryIntegral (logDeriv (deriv riemannZeta)) 0 r b t -
          rectangleBoundaryIntegral (logDeriv riemannZeta) 0 r b t =
        (bottomD - bottomZ) - (topD - topZ) +
          I * (rightD - rightZ) - I * (leftD - leftZ) := by
    unfold rectangleBoundaryIntegral
    simp only [ofReal_zero, zero_add]
    change
      (bottomD - topD + I * rightD - I * leftD) -
          (bottomZ - topZ + I * rightZ - I * leftZ) =
        (bottomD - bottomZ) - (topD - topZ) +
          I * (rightD - rightZ) - I * (leftD - leftZ)
    ring
  rw [hboundary]
  simp only [Complex.add_im, Complex.sub_im]
  calc
    |(bottomD - bottomZ).im - (topD - topZ).im +
        (I * (rightD - rightZ)).im - (I * (leftD - leftZ)).im| ≤
      (|(bottomD - bottomZ).im| + |(topD - topZ).im|) +
        |(I * (rightD - rightZ)).im| +
          |(I * (leftD - leftZ)).im| := by
      calc
        |(bottomD - bottomZ).im - (topD - topZ).im +
            (I * (rightD - rightZ)).im - (I * (leftD - leftZ)).im| ≤
          |(bottomD - bottomZ).im - (topD - topZ).im +
            (I * (rightD - rightZ)).im| +
              |(I * (leftD - leftZ)).im| := abs_sub _ _
        _ ≤ (|(bottomD - bottomZ).im - (topD - topZ).im| +
            |(I * (rightD - rightZ)).im|) +
              |(I * (leftD - leftZ)).im| := by gcongr; exact abs_add_le _ _
        _ ≤ (|(bottomD - bottomZ).im| + |(topD - topZ).im|) +
            |(I * (rightD - rightZ)).im| +
              |(I * (leftD - leftZ)).im| := by gcongr; exact abs_sub _ _
    _ ≤ Cb + Ct * Real.log (t + 2) + Real.pi + Real.pi := by
      gcongr
    _ ≤ (Ct + Cb + 2 * Real.pi) * Real.log (t + 2) := by
      nlinarith [mul_le_mul_of_nonneg_left hlogOne hCb,
        mul_le_mul_of_nonneg_left hlogOne Real.pi_pos.le]
    _ = C * Real.log (t + 2) := by
      dsimp only [C]

/-- At every sufficiently large common zero-free top height, the actual global multiplicity-count
difference is `O(log(t+2))`. The remaining transfer to arbitrary real cutoffs is purely a local
constancy problem for the two finite zero counts. -/
theorem exists_levinsonMontgomeryAdmissibleLogCountBound :
    ∃ C T0 : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, T0 ≤ t → LevinsonMontgomeryTopAdmissible t →
        abs ((speiserUpperLeftDerivZeroCount t : ℝ) -
          (speiserUpperLeftZetaZeroCount t : ℝ)) ≤
            C * Real.log (t + 2) := by
  obtain ⟨b, hbTen, hbottom⟩ :=
    exists_speiserCommonZeroFreeHorizontal_above 10
  obtain ⟨Cb, Tb, hCb, hboundary⟩ :=
    exists_abs_im_levinsonMontgomeryRectangleLogDerivDifference_le_log
      hbTen hbottom
  let twoPi : ℝ := 2 * Real.pi
  have htwoPi : 0 < twoPi := by
    dsimp only [twoPi]
    positivity
  let bottomDifference : ℝ :=
    (speiserUpperLeftDerivZeroCount b : ℝ) -
      (speiserUpperLeftZetaZeroCount b : ℝ)
  let C : ℝ := Cb / twoPi + |bottomDifference|
  let T0 : ℝ := max Tb (b + 1)
  refine ⟨C, T0, ?_, ?_⟩
  · dsimp only [C]
    exact add_nonneg (div_nonneg hCb htwoPi.le) (abs_nonneg _)
  intro t htLarge ht
  have htBoundary : Tb ≤ t := (le_max_left Tb (b + 1)).trans htLarge
  have hbt : b < t := by
    have hbOne : b < b + 1 := by linarith
    exact hbOne.trans_le ((le_max_right Tb (b + 1)).trans htLarge)
  have htopCommon : SpeiserCommonZeroFreeHorizontal t := by
    refine ⟨ht.1, fun sigma hsigma => ?_⟩
    apply ht.2 sigma
    exact ⟨hsigma.1, hsigma.2.trans (by norm_num)⟩
  obtain ⟨r, hr0, hrHalf, hright, hcount⟩ :=
    exists_levinsonMontgomery_negativeRight_globalCountDifference_actual
      hbTen hbt hbottom htopCommon
  have hboundaryBound :=
    hboundary t r htBoundary hbt ht hr0 hrHalf hright
  let topDifference : ℝ :=
    (speiserUpperLeftDerivZeroCount t : ℝ) -
      (speiserUpperLeftZetaZeroCount t : ℝ)
  have hcountIm :
      (rectangleBoundaryIntegral (logDeriv (deriv riemannZeta)) 0 r b t -
        rectangleBoundaryIntegral (logDeriv riemannZeta) 0 r b t).im =
          twoPi * (topDifference - bottomDifference) := by
    rw [hcount]
    dsimp only [twoPi, topDifference, bottomDifference]
    norm_num [Complex.mul_im, Complex.sub_im]
  have hscaled :
      twoPi * |topDifference - bottomDifference| ≤
        Cb * Real.log (t + 2) := by
    rw [hcountIm] at hboundaryBound
    have habs : |twoPi * (topDifference - bottomDifference)| =
        twoPi * |topDifference - bottomDifference| := by
      rw [abs_mul, abs_of_pos htwoPi]
    rw [habs] at hboundaryBound
    exact hboundaryBound
  have hdifference :
      |topDifference - bottomDifference| ≤
        (Cb / twoPi) * Real.log (t + 2) := by
    have hdiv :
        |topDifference - bottomDifference| ≤
          (Cb * Real.log (t + 2)) / twoPi := by
      apply (le_div_iff₀ htwoPi).2
      simpa only [mul_comm] using hscaled
    calc
      |topDifference - bottomDifference| ≤
          (Cb * Real.log (t + 2)) / twoPi := hdiv
      _ = (Cb / twoPi) * Real.log (t + 2) := by field_simp
  have hlogOne : 1 ≤ Real.log (t + 2) := by
    apply (Real.le_log_iff_exp_le (by linarith [ht.1])).mpr
    exact Real.exp_one_lt_three.le.trans (by linarith [ht.1])
  change |topDifference| ≤ C * Real.log (t + 2)
  calc
    |topDifference| =
        |(topDifference - bottomDifference) + bottomDifference| := by ring_nf
    _ ≤ |topDifference - bottomDifference| + |bottomDifference| :=
      abs_add_le _ _
    _ ≤ (Cb / twoPi) * Real.log (t + 2) + |bottomDifference| :=
      add_le_add hdifference le_rfl
    _ ≤ (Cb / twoPi + |bottomDifference|) * Real.log (t + 2) := by
      have hbottomAbs :=
        mul_le_mul_of_nonneg_left hlogOne (abs_nonneg bottomDifference)
      nlinarith
    _ = C * Real.log (t + 2) := by
      dsimp only [C]

/-- A finite real set lying strictly below `T` has a common strict upper bound still below `T`. -/
theorem exists_finset_strictUpperBound_below
    {S : Finset ℝ} {T : ℝ} (hS : ∀ x ∈ S, x < T) :
    ∃ a : ℝ, a < T ∧ ∀ x ∈ S, x < a := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      refine ⟨T - 1, by linarith, ?_⟩
      simp
  | @insert x0 S hx ih =>
      have hxT : x0 < T := hS x0 (by simp)
      have hST : ∀ y ∈ S, y < T := by
        intro y hy
        exact hS y (by simp [hy])
      obtain ⟨a, haT, ha⟩ := ih hST
      let a' : ℝ := (max x0 a + T) / 2
      have hmaxT : max x0 a < T := max_lt hxT haT
      refine ⟨a', by dsimp only [a']; linarith, ?_⟩
      intro y hy
      rw [Finset.mem_insert] at hy
      rcases hy with hyEq | hy
      · subst y
        have hle : x0 ≤ max x0 a := le_max_left _ _
        dsimp only [a']
        linarith
      · have hya : y < a := ha y hy
        have hle : a ≤ max x0 a := le_max_right _ _
        dsimp only [a']
        linarith

/-- Below every positive cutoff and above every prescribed lower threshold, there is an
admissible top at which both strict multiplicity counts are exactly the counts at the cutoff. -/
theorem exists_levinsonMontgomeryTopAdmissible_below_countStable
    {B T : ℝ} (hT : 0 < T) (hBT : B < T) :
    ∃ t : ℝ, B < t ∧ t < T ∧ LevinsonMontgomeryTopAdmissible t ∧
      speiserUpperLeftZetaZeroCount t = speiserUpperLeftZetaZeroCount T ∧
      speiserUpperLeftDerivZeroCount t = speiserUpperLeftDerivZeroCount T := by
  classical
  let S : Finset ℝ :=
    insert 0 (insert B
      ((speiserUpperLeftZetaZeroFinset T ∪
        speiserUpperLeftDerivZeroFinset T).image Complex.im))
  have hS : ∀ y ∈ S, y < T := by
    intro y hy
    simp only [S, Finset.mem_insert, Finset.mem_image, Finset.mem_union] at hy
    rcases hy with rfl | rfl | ⟨z, hz, rfl⟩
    · exact hT
    · exact hBT
    · rcases hz with hz | hz
      · exact (mem_speiserUpperLeftZetaZeroFinset.mp hz).1.2
      · exact (mem_speiserUpperLeftDerivZeroFinset.mp hz).1.2
  obtain ⟨a, haT, ha⟩ := exists_finset_strictUpperBound_below hS
  have hzeroS : (0 : ℝ) ∈ S := by simp [S]
  have hBS : B ∈ S := by simp [S]
  have haPos : 0 < a := ha 0 hzeroS
  have hBa : B < a := ha B hBS
  obtain ⟨t, htIoo, ht⟩ :=
    exists_levinsonMontgomeryTopAdmissible_between haPos haT
  have hzetaFinset :
      speiserUpperLeftZetaZeroFinset t =
        speiserUpperLeftZetaZeroFinset T := by
    ext z
    simp only [mem_speiserUpperLeftZetaZeroFinset]
    constructor
    · rintro ⟨⟨hzStrip, hzt⟩, hzZero⟩
      exact ⟨⟨hzStrip, hzt.trans htIoo.2⟩, hzZero⟩
    · rintro ⟨⟨hzStrip, hzT⟩, hzZero⟩
      have hzMem : z.im ∈ S := by
        simp only [S, Finset.mem_insert, Finset.mem_image, Finset.mem_union]
        exact Or.inr (Or.inr ⟨z, Or.inl
          (mem_speiserUpperLeftZetaZeroFinset.mpr
            ⟨⟨hzStrip, hzT⟩, hzZero⟩), rfl⟩)
      exact ⟨⟨hzStrip, (ha z.im hzMem).trans htIoo.1⟩, hzZero⟩
  have hderivFinset :
      speiserUpperLeftDerivZeroFinset t =
        speiserUpperLeftDerivZeroFinset T := by
    ext z
    simp only [mem_speiserUpperLeftDerivZeroFinset]
    constructor
    · rintro ⟨⟨hzStrip, hzt⟩, hzZero⟩
      exact ⟨⟨hzStrip, hzt.trans htIoo.2⟩, hzZero⟩
    · rintro ⟨⟨hzStrip, hzT⟩, hzZero⟩
      have hzMem : z.im ∈ S := by
        simp only [S, Finset.mem_insert, Finset.mem_image, Finset.mem_union]
        exact Or.inr (Or.inr ⟨z, Or.inr
          (mem_speiserUpperLeftDerivZeroFinset.mpr
            ⟨⟨hzStrip, hzT⟩, hzZero⟩), rfl⟩)
      exact ⟨⟨hzStrip, (ha z.im hzMem).trans htIoo.1⟩, hzZero⟩
  refine ⟨t, hBa.trans htIoo.1, htIoo.2, ht, ?_, ?_⟩
  · unfold speiserUpperLeftZetaZeroCount
    rw [hzetaFinset]
  · unfold speiserUpperLeftDerivZeroCount
    rw [hderivFinset]

/-- The full first conclusion of Levinson--Montgomery Theorem 1 for the project's actual
multiplicity-bearing source counts. -/
theorem levinsonMontgomeryLogCountBound_actual :
    LevinsonMontgomeryLogCountBound := by
  obtain ⟨C, Tsource, hC, hsource⟩ :=
    exists_levinsonMontgomeryAdmissibleLogCountBound
  let T0 : ℝ := max Tsource 2 + 1
  refine ⟨2 * C, mul_nonneg (by norm_num) hC, T0, ?_⟩
  intro T hTlarge
  have hTsource : Tsource < T := by
    have hsourceMax : Tsource ≤ max Tsource 2 := le_max_left _ _
    dsimp only [T0] at hTlarge
    linarith
  have hTtwo : 2 < T := by
    have htwoMax : (2 : ℝ) ≤ max Tsource 2 := le_max_right _ _
    dsimp only [T0] at hTlarge
    linarith
  have hTpos : 0 < T := by linarith
  obtain ⟨t, hTsourceT, htT, ht, hzetaCount, hderivCount⟩ :=
    exists_levinsonMontgomeryTopAdmissible_below_countStable
      hTpos hTsource
  have htBound := hsource t hTsourceT.le ht
  have hshift : t + 2 ≤ 2 * T := by linarith
  have hshiftPos : 0 < t + 2 := by linarith [ht.1]
  have hlogShift : Real.log (t + 2) ≤ 2 * Real.log T := by
    calc
      Real.log (t + 2) ≤ Real.log (2 * T) :=
        Real.log_le_log hshiftPos hshift
      _ = Real.log 2 + Real.log T := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hTpos)]
      _ ≤ Real.log T + Real.log T := by
        gcongr
      _ = 2 * Real.log T := by ring
  rw [hderivCount, hzetaCount] at htBound
  calc
    |(speiserUpperLeftDerivZeroCount T : ℝ) -
        (speiserUpperLeftZetaZeroCount T : ℝ)| ≤
      C * Real.log (t + 2) := htBound
    _ ≤ C * (2 * Real.log T) :=
      mul_le_mul_of_nonneg_left hlogShift hC
    _ = (2 * C) * Real.log T := by ring

/-- Horizontal interval-integrability of the zeta logarithmic derivative on an arbitrary
zero-free segment. -/
theorem intervalIntegrable_riemannZetaLogDeriv_horizontal_upto
    {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r)
    (hzeta : ∀ sigma : ℝ, sigma ∈ Set.Icc (0 : ℝ) r →
      riemannZeta ((sigma : ℂ) + t * I) ≠ 0) :
    IntervalIntegrable
      (fun sigma : ℝ => logDeriv riemannZeta ((sigma : ℂ) + t * I))
      (volume : Measure ℝ) (0 : ℝ) r := by
  apply ContinuousOn.intervalIntegrable_of_Icc hr
  intro sigma hsigma
  have hsOne : (sigma : ℂ) + t * I ≠ 1 := by
    intro hs
    have him := congrArg Complex.im hs
    norm_num at him
    linarith
  have hanalytic :
      AnalyticAt ℂ riemannZeta ((sigma : ℂ) + t * I) :=
    analyticOn_riemannZeta _ (by simpa using hsOne)
  let phi : ℝ → ℂ := fun x => (x : ℂ) + t * I
  have hphi : Continuous phi := by fun_prop
  have houter :=
    levinsonMontgomery_continuousAt_logDeriv_of_analyticAt_of_ne_zero
      hanalytic (hzeta sigma hsigma)
  simpa only [phi, Function.comp_def] using
    (ContinuousAt.comp (f := phi) (x := sigma)
      houter hphi.continuousAt).continuousWithinAt

/-- Horizontal interval-integrability of the zeta-derivative logarithmic derivative on an
arbitrary zero-free segment. -/
theorem intervalIntegrable_riemannZetaDerivLogDeriv_horizontal_upto
    {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r)
    (hderiv : ∀ sigma : ℝ, sigma ∈ Set.Icc (0 : ℝ) r →
      deriv riemannZeta ((sigma : ℂ) + t * I) ≠ 0) :
    IntervalIntegrable
      (fun sigma : ℝ =>
        logDeriv (deriv riemannZeta) ((sigma : ℂ) + t * I))
      (volume : Measure ℝ) (0 : ℝ) r := by
  apply ContinuousOn.intervalIntegrable_of_Icc hr
  intro sigma hsigma
  have hsOne : (sigma : ℂ) + t * I ≠ 1 := by
    intro hs
    have him := congrArg Complex.im hs
    norm_num at him
    linarith
  have hanalytic :
      AnalyticAt ℂ (deriv riemannZeta) ((sigma : ℂ) + t * I) :=
    analyticOnNhd_deriv_riemannZeta _ (by simpa using hsOne)
  let phi : ℝ → ℂ := fun x => (x : ℂ) + t * I
  have hphi : Continuous phi := by fun_prop
  have houter :=
    levinsonMontgomery_continuousAt_logDeriv_of_analyticAt_of_ne_zero
      hanalytic (hderiv sigma hsigma)
  simpa only [phi, Function.comp_def] using
    (ContinuousAt.comp (f := phi) (x := sigma)
      houter hphi.continuousAt).continuousWithinAt

/-- Principal-log endpoint control on an arbitrary strict-left horizontal segment. Unlike the
source-height wrapper ending at `1 / 2`, this form may stop at an adaptive cutoff before a
critical-line zero. -/
theorem intervalIntegral_speiserZetaDerivRatio_horizontal_upto
    {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r)
    (hsegment : ∀ sigma : ℝ, sigma ∈ Set.Icc (0 : ℝ) r →
      riemannZeta ((sigma : ℂ) + t * I) ≠ 0 ∧
        deriv riemannZeta ((sigma : ℂ) + t * I) ≠ 0 ∧
        (speiserZetaDerivRatio ((sigma : ℂ) + t * I)).re < 0) :
    (∫ sigma : ℝ in (0 : ℝ)..r,
      (logDeriv (deriv riemannZeta) ((sigma : ℂ) + t * I) -
        logDeriv riemannZeta ((sigma : ℂ) + t * I))) =
      Complex.log (-speiserZetaDerivRatio ((r : ℂ) + t * I)) -
        Complex.log (-speiserZetaDerivRatio (t * I)) := by
  let g : ℝ → ℂ := fun sigma =>
    speiserZetaDerivRatio ((sigma : ℂ) + t * I)
  let d : ℝ → ℂ := fun sigma =>
    logDeriv (deriv riemannZeta) ((sigma : ℂ) + t * I) -
      logDeriv riemannZeta ((sigma : ℂ) + t * I)
  let g' : ℝ → ℂ := fun sigma => d sigma * g sigma
  have huIcc : Set.uIcc (0 : ℝ) r = Set.Icc 0 r := Set.uIcc_of_le hr
  have hderiv : ∀ sigma ∈ Set.uIcc (0 : ℝ) r,
      HasDerivAt g (g' sigma) sigma := by
    intro sigma hsigma
    have hsigmaIcc : sigma ∈ Set.Icc (0 : ℝ) r := by
      simpa only [huIcc] using hsigma
    have hdata := hsegment sigma hsigmaIcc
    exact hasDerivAt_speiserZetaDerivRatio_horizontal ht hdata.1 hdata.2.1
  have hneg : ∀ sigma ∈ Set.uIcc (0 : ℝ) r, (g sigma).re < 0 := by
    intro sigma hsigma
    have hsigmaIcc : sigma ∈ Set.Icc (0 : ℝ) r := by
      simpa only [huIcc] using hsigma
    exact (hsegment sigma hsigmaIcc).2.2
  have hzetaInt :
      IntervalIntegrable
        (fun sigma : ℝ => logDeriv riemannZeta ((sigma : ℂ) + t * I))
        (volume : Measure ℝ) (0 : ℝ) r := by
    apply ContinuousOn.intervalIntegrable_of_Icc hr
    intro sigma hsigma
    have hsOne : (sigma : ℂ) + t * I ≠ 1 := by
      intro hs
      have him := congrArg Complex.im hs
      norm_num at him
      linarith
    have hanalytic :
        AnalyticAt ℂ riemannZeta ((sigma : ℂ) + t * I) :=
      analyticOn_riemannZeta _ (by simpa using hsOne)
    let phi : ℝ → ℂ := fun x => (x : ℂ) + t * I
    have hphi : Continuous phi := by fun_prop
    have houter :=
      levinsonMontgomery_continuousAt_logDeriv_of_analyticAt_of_ne_zero
        hanalytic (hsegment sigma hsigma).1
    simpa only [phi, Function.comp_def] using
      (ContinuousAt.comp (f := phi) (x := sigma)
        houter hphi.continuousAt).continuousWithinAt
  have hderivInt :
      IntervalIntegrable
        (fun sigma : ℝ =>
          logDeriv (deriv riemannZeta) ((sigma : ℂ) + t * I))
        (volume : Measure ℝ) (0 : ℝ) r := by
    apply ContinuousOn.intervalIntegrable_of_Icc hr
    intro sigma hsigma
    have hsOne : (sigma : ℂ) + t * I ≠ 1 := by
      intro hs
      have him := congrArg Complex.im hs
      norm_num at him
      linarith
    have hanalytic :
        AnalyticAt ℂ (deriv riemannZeta) ((sigma : ℂ) + t * I) :=
      analyticOnNhd_deriv_riemannZeta _ (by simpa using hsOne)
    let phi : ℝ → ℂ := fun x => (x : ℂ) + t * I
    have hphi : Continuous phi := by fun_prop
    have houter :=
      levinsonMontgomery_continuousAt_logDeriv_of_analyticAt_of_ne_zero
        hanalytic (hsegment sigma hsigma).2.1
    simpa only [phi, Function.comp_def] using
      (ContinuousAt.comp (f := phi) (x := sigma)
        houter hphi.continuousAt).continuousWithinAt
  have hdInt : IntervalIntegrable d (volume : Measure ℝ) (0 : ℝ) r :=
    hderivInt.sub hzetaInt
  have hpoint : ∀ sigma ∈ Set.uIcc (0 : ℝ) r,
      g' sigma / g sigma = d sigma := by
    intro sigma hsigma
    have hsigmaIcc : sigma ∈ Set.Icc (0 : ℝ) r := by
      simpa only [huIcc] using hsigma
    have hgNe : g sigma ≠ 0 := by
      dsimp only [g, speiserZetaDerivRatio]
      exact div_ne_zero (hsegment sigma hsigmaIcc).2.1
        (hsegment sigma hsigmaIcc).1
    dsimp only [g']
    exact mul_div_cancel_right₀ _ hgNe
  have hquotInt :
      IntervalIntegrable (fun sigma => g' sigma / g sigma)
        (volume : Measure ℝ) (0 : ℝ) r := by
    apply hdInt.congr
    intro sigma hsigma
    exact (hpoint sigma (Set.uIoc_subset_uIcc hsigma)).symm
  have hformula :=
    intervalIntegral_deriv_div_eq_log_sub_of_re_neg
      hderiv hquotInt hneg
  calc
    (∫ sigma : ℝ in (0 : ℝ)..r,
      (logDeriv (deriv riemannZeta) ((sigma : ℂ) + t * I) -
        logDeriv riemannZeta ((sigma : ℂ) + t * I))) =
        ∫ sigma : ℝ in (0 : ℝ)..r, g' sigma / g sigma := by
          apply intervalIntegral.integral_congr
          intro sigma hsigma
          exact (hpoint sigma hsigma).symm
    _ = Complex.log (-g r) - Complex.log (-g 0) := hformula
    _ = Complex.log (-speiserZetaDerivRatio ((r : ℂ) + t * I)) -
        Complex.log (-speiserZetaDerivRatio (t * I)) := by
          simp only [g]
          norm_num

/-- If the actual ratio is strictly left-pointing on all four sides of an adaptive rectangle,
the difference of the zeta-derivative and zeta logarithmic-derivative boundary integrals is
exactly zero. -/
theorem rectangleBoundaryIntegral_logDerivDifference_eq_zero_of_strictNegative
    {r b t : ℝ} (hr : 0 ≤ r) (hb : 0 < b) (hbt : b ≤ t)
    (hbottom : ∀ sigma : ℝ, sigma ∈ Set.Icc (0 : ℝ) r →
      riemannZeta ((sigma : ℂ) + b * I) ≠ 0 ∧
        deriv riemannZeta ((sigma : ℂ) + b * I) ≠ 0 ∧
        (speiserZetaDerivRatio ((sigma : ℂ) + b * I)).re < 0)
    (htop : ∀ sigma : ℝ, sigma ∈ Set.Icc (0 : ℝ) r →
      riemannZeta ((sigma : ℂ) + t * I) ≠ 0 ∧
        deriv riemannZeta ((sigma : ℂ) + t * I) ≠ 0 ∧
        (speiserZetaDerivRatio ((sigma : ℂ) + t * I)).re < 0)
    (hright : ∀ y : ℝ, y ∈ Set.Icc b t →
      riemannZeta ((r : ℂ) + y * I) ≠ 0 ∧
        deriv riemannZeta ((r : ℂ) + y * I) ≠ 0 ∧
        (speiserZetaDerivRatio ((r : ℂ) + y * I)).re < 0)
    (hleft : ∀ y : ℝ, y ∈ Set.Icc b t →
      riemannZeta (((0 : ℝ) : ℂ) + y * I) ≠ 0 ∧
        deriv riemannZeta (((0 : ℝ) : ℂ) + y * I) ≠ 0 ∧
        (speiserZetaDerivRatio (((0 : ℝ) : ℂ) + y * I)).re < 0) :
    rectangleBoundaryIntegral (logDeriv (deriv riemannZeta)) 0 r b t -
        rectangleBoundaryIntegral (logDeriv riemannZeta) 0 r b t = 0 := by
  have ht : 0 < t := hb.trans_le hbt
  have hbZetaInt := intervalIntegrable_riemannZetaLogDeriv_horizontal_upto
    hb hr (fun sigma hsigma => (hbottom sigma hsigma).1)
  have hbDerivInt := intervalIntegrable_riemannZetaDerivLogDeriv_horizontal_upto
    hb hr (fun sigma hsigma => (hbottom sigma hsigma).2.1)
  have htZetaInt := intervalIntegrable_riemannZetaLogDeriv_horizontal_upto
    ht hr (fun sigma hsigma => (htop sigma hsigma).1)
  have htDerivInt := intervalIntegrable_riemannZetaDerivLogDeriv_horizontal_upto
    ht hr (fun sigma hsigma => (htop sigma hsigma).2.1)
  have hrZetaInt := intervalIntegrable_riemannZetaLogDeriv_vertical
    hb hbt (fun y hy => (hright y hy).1)
  have hrDerivInt := intervalIntegrable_riemannZetaDerivLogDeriv_vertical
    hb hbt (fun y hy => (hright y hy).2.1)
  have hlZetaInt := intervalIntegrable_riemannZetaLogDeriv_vertical
    (r := 0) hb hbt (fun y hy => (hleft y hy).1)
  have hlDerivInt := intervalIntegrable_riemannZetaDerivLogDeriv_vertical
    (r := 0) hb hbt (fun y hy => (hleft y hy).2.1)
  have hbottomFormula :=
    intervalIntegral_speiserZetaDerivRatio_horizontal_upto hb hr hbottom
  have htopFormula :=
    intervalIntegral_speiserZetaDerivRatio_horizontal_upto ht hr htop
  have hrightFormula :=
    intervalIntegral_speiserZetaDerivRatio_vertical hb hbt hright
  have hleftFormula :=
    intervalIntegral_speiserZetaDerivRatio_vertical (r := 0) hb hbt hleft
  calc
    rectangleBoundaryIntegral (logDeriv (deriv riemannZeta)) 0 r b t -
        rectangleBoundaryIntegral (logDeriv riemannZeta) 0 r b t =
      (∫ sigma : ℝ in (0 : ℝ)..r,
          (logDeriv (deriv riemannZeta) ((sigma : ℂ) + b * I) -
            logDeriv riemannZeta ((sigma : ℂ) + b * I))) -
        (∫ sigma : ℝ in (0 : ℝ)..r,
          (logDeriv (deriv riemannZeta) ((sigma : ℂ) + t * I) -
            logDeriv riemannZeta ((sigma : ℂ) + t * I))) +
        I * (∫ y : ℝ in b..t,
          (logDeriv (deriv riemannZeta) ((r : ℂ) + y * I) -
            logDeriv riemannZeta ((r : ℂ) + y * I))) -
        I * (∫ y : ℝ in b..t,
          (logDeriv (deriv riemannZeta) (((0 : ℝ) : ℂ) + y * I) -
            logDeriv riemannZeta (((0 : ℝ) : ℂ) + y * I))) := by
      unfold rectangleBoundaryIntegral
      rw [intervalIntegral.integral_sub hbDerivInt hbZetaInt,
        intervalIntegral.integral_sub htDerivInt htZetaInt,
        intervalIntegral.integral_sub hrDerivInt hrZetaInt,
        intervalIntegral.integral_sub hlDerivInt hlZetaInt]
      ring
    _ = 0 := by
      rw [hbottomFormula, htopFormula, hrightFormula, hleftFormula]
      simp only [ofReal_zero, zero_add]
      ring

/-- The finite source datum suppressed by the phrase "using standard explicit estimates" in
Levinson--Montgomery's proof: one strict-negative horizontal above height ten at which the two
global strict-left multiplicity counts have zero offset. -/
def LevinsonMontgomeryNegativeExactCountBase : Prop :=
  ∃ b : ℝ, 10 < b ∧ SpeiserStrictNegativeHorizontal b ∧
    speiserUpperLeftDerivZeroCount b = speiserUpperLeftZetaZeroCount b

/-- A zero-offset strict-negative base turns cofinal source negative-height geometry into the
exact-count sequence. The adaptive right side avoids every possible critical-line endpoint zero,
and the four principal-log endpoint changes cancel exactly. -/
theorem levinsonMontgomeryExactCountSequence_of_negativeExactCountBase_of_cofinalGeometry
    (hbase : LevinsonMontgomeryNegativeExactCountBase)
    (hcofinal : LevinsonMontgomeryCofinalNegativeHeightGeometry) :
    LevinsonMontgomeryExactCountSequence := by
  intro B
  obtain ⟨b, hb, hbottom, hbaseCount⟩ := hbase
  let N : ℕ := Nat.ceil (max B b + 1)
  obtain ⟨n, hnN, _hnTen, htopGeometry⟩ := hcofinal N
  have hceil : max B b + 1 ≤ (N : ℝ) := by
    dsimp only [N]
    exact Nat.le_ceil _
  have hNn : (N : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hnN
  have hBn : B < (n : ℝ) := by
    linarith [le_max_left B b]
  have hbn : b < (n : ℝ) := by
    linarith [le_max_right B b]
  obtain ⟨r, hr, hrHalf, hright, hcount⟩ :=
    exists_levinsonMontgomery_negativeRight_globalCountDifference_of_negativeHeightGeometry
      hb hbn hbottom.toCommonZeroFree htopGeometry
  have hbottomNarrow : ∀ sigma : ℝ, sigma ∈ Set.Icc (0 : ℝ) r →
      riemannZeta ((sigma : ℂ) + b * I) ≠ 0 ∧
        deriv riemannZeta ((sigma : ℂ) + b * I) ≠ 0 ∧
        (speiserZetaDerivRatio ((sigma : ℂ) + b * I)).re < 0 := by
    intro sigma hsigma
    exact hbottom.2 sigma ⟨hsigma.1, hsigma.2.trans hrHalf.le⟩
  have htopNarrow : ∀ sigma : ℝ, sigma ∈ Set.Icc (0 : ℝ) r →
      riemannZeta ((sigma : ℂ) + (n : ℝ) * I) ≠ 0 ∧
        deriv riemannZeta ((sigma : ℂ) + (n : ℝ) * I) ≠ 0 ∧
        (speiserZetaDerivRatio
          ((sigma : ℂ) + (n : ℝ) * I)).re < 0 := by
    intro sigma hsigma
    have hdata := htopGeometry.1 sigma hsigma.1
      (hsigma.2.trans_lt hrHalf)
    have hnCast : (((n : ℝ) : ℂ)) = (n : ℂ) := by norm_num
    rw [hnCast]
    simpa only [levinsonMontgomeryIntegerPoint] using hdata
  have hleft : ∀ y : ℝ, y ∈ Set.Icc b (n : ℝ) →
      riemannZeta (((0 : ℝ) : ℂ) + y * I) ≠ 0 ∧
        deriv riemannZeta (((0 : ℝ) : ℂ) + y * I) ≠ 0 ∧
        (speiserZetaDerivRatio (((0 : ℝ) : ℂ) + y * I)).re < 0 := by
    intro y hy
    simpa only [ofReal_zero, zero_add] using
      (levinsonMontgomery_leftVertical_negative (b := b) (t := (n : ℝ)) hb.le y hy)
  have hboundary :
      rectangleBoundaryIntegral (logDeriv (deriv riemannZeta)) 0 r b n -
          rectangleBoundaryIntegral (logDeriv riemannZeta) 0 r b n = 0 :=
    rectangleBoundaryIntegral_logDerivDifference_eq_zero_of_strictNegative
      hr.le hbottom.1 hbn.le hbottomNarrow htopNarrow hright hleft
  rw [hboundary] at hcount
  have hfactor : 2 * (Real.pi : ℂ) * I ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  have hcountDifference :
      (((speiserUpperLeftDerivZeroCount n : ℂ) -
          (speiserUpperLeftZetaZeroCount n : ℂ)) -
        ((speiserUpperLeftDerivZeroCount b : ℂ) -
          (speiserUpperLeftZetaZeroCount b : ℂ))) = 0 :=
    (mul_eq_zero.mp hcount.symm).resolve_left hfactor
  have htopDifference :
      (speiserUpperLeftDerivZeroCount n : ℂ) -
        (speiserUpperLeftZetaZeroCount n : ℂ) = 0 := by
    rw [hbaseCount] at hcountDifference
    simpa using hcountDifference
  have htopCast :
      (speiserUpperLeftDerivZeroCount n : ℂ) =
        (speiserUpperLeftZetaZeroCount n : ℂ) :=
    sub_eq_zero.mp htopDifference
  have htopCount :
      speiserUpperLeftDerivZeroCount n =
        speiserUpperLeftZetaZeroCount n := by
    have hre := congrArg Complex.re htopCast
    norm_num at hre
    exact_mod_cast hre
  exact ⟨(n : ℝ), hBn, htopCount⟩

/-- The whole source count dichotomy is reduced to the one finite low-height datum used in the
1974 proof. The alternative branch is the already compiled eventual linear-density conclusion. -/
theorem levinsonMontgomeryCountDichotomy_of_negativeExactCountBase
    (hbase : LevinsonMontgomeryNegativeExactCountBase) :
    LevinsonMontgomeryCountDichotomy := by
  rcases levinsonMontgomery_negativeGeometry_or_dense_dichotomy with
    hcofinal | hdense
  · left
    exact
      levinsonMontgomeryExactCountSequence_of_negativeExactCountBase_of_cofinalGeometry
        hbase hcofinal
  · right
    exact hdense

/-- Conditional completion of both Levinson--Montgomery count outputs after isolating the finite
low-height source certificate. -/
theorem levinsonMontgomeryTheoremOne_of_negativeExactCountBase
    (hbase : LevinsonMontgomeryNegativeExactCountBase) :
    LevinsonMontgomeryLogCountBound ∧ LevinsonMontgomeryCountDichotomy :=
  ⟨levinsonMontgomeryLogCountBound_actual,
    levinsonMontgomeryCountDichotomy_of_negativeExactCountBase hbase⟩

/-- Strict negativity on one complete source horizontal persists uniformly through a small
height neighborhood. -/
theorem exists_speiserStrictNegativeHorizontal_near
    {t : ℝ} (ht : SpeiserStrictNegativeHorizontal t) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ u : ℝ, dist u t < epsilon → SpeiserStrictNegativeHorizontal u := by
  classical
  let K : Set ℂ := Set.Icc (0 : ℝ) (1 / 2) ×ℂ ({t} : Set ℝ)
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_singleton
  have hlocal : ∀ rho : K, ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ z : ℂ, dist z rho < epsilon →
        riemannZeta z ≠ 0 ∧ deriv riemannZeta z ≠ 0 ∧
          (speiserZetaDerivRatio z).re < 0 := by
    intro rho
    have hrhoRe : (rho : ℂ).re ∈ Set.Icc (0 : ℝ) (1 / 2) :=
      rho.property.1
    have hrhoIm : (rho : ℂ).im = t := by
      simpa using rho.property.2
    have hrhoPoint : (rho : ℂ) = ((rho : ℂ).re : ℂ) + t * I := by
      apply Complex.ext
      · simp
      · simp [hrhoIm]
    have hdata := ht.2 (rho : ℂ).re hrhoRe
    rw [← hrhoPoint] at hdata
    have hrhoOne : (rho : ℂ) ≠ 1 := by
      intro hrhoOne
      have him := congrArg Complex.im hrhoOne
      rw [hrhoIm] at him
      norm_num at him
      linarith [ht.1]
    have hzetaAnalytic : AnalyticAt ℂ riemannZeta rho :=
      analyticOn_riemannZeta _ (by simpa using hrhoOne)
    have hderivAnalytic : AnalyticAt ℂ (deriv riemannZeta) rho :=
      analyticOnNhd_deriv_riemannZeta _ (by simpa using hrhoOne)
    have hratioContinuous : ContinuousAt speiserZetaDerivRatio rho :=
      (hasDerivAt_speiserZetaDerivRatio hrhoOne hdata.1 hdata.2.1).continuousAt
    have hratioReContinuous :
        ContinuousAt (fun z : ℂ => (speiserZetaDerivRatio z).re) rho :=
      Complex.continuous_re.continuousAt.comp hratioContinuous
    have heventually : ∀ᶠ z in nhds (rho : ℂ),
        riemannZeta z ≠ 0 ∧ deriv riemannZeta z ≠ 0 ∧
          (speiserZetaDerivRatio z).re < 0 :=
      (hzetaAnalytic.continuousAt.eventually_ne hdata.1).and
        ((hderivAnalytic.continuousAt.eventually_ne hdata.2.1).and
          (hratioReContinuous.eventually_lt_const hdata.2.2))
    change {z : ℂ | riemannZeta z ≠ 0 ∧ deriv riemannZeta z ≠ 0 ∧
      (speiserZetaDerivRatio z).re < 0} ∈ nhds (rho : ℂ) at heventually
    obtain ⟨epsilon, hepsilon, hball⟩ := Metric.mem_nhds_iff.mp heventually
    exact ⟨epsilon, hepsilon, fun z hz =>
      hball (by simpa [Metric.mem_ball] using hz)⟩
  choose epsilon hepsilon hnegative using hlocal
  let U : Set ℂ := ⋃ rho : K, Metric.ball (rho : ℂ) (epsilon rho)
  have hUOpen : IsOpen U := by
    dsimp only [U]
    exact isOpen_iUnion fun rho => Metric.isOpen_ball
  have hKU : K ⊆ U := by
    intro rho hrho
    change rho ∈ ⋃ p : K, Metric.ball (p : ℂ) (epsilon p)
    apply Set.mem_iUnion.mpr
    let p : K := ⟨rho, hrho⟩
    exact ⟨p, Metric.mem_ball_self (hepsilon p)⟩
  obtain ⟨delta, hdelta, hthick⟩ :=
    hK.exists_thickening_subset_open hUOpen hKU
  let epsilon0 : ℝ := min delta (t / 2)
  have hepsilon0 : 0 < epsilon0 := by
    dsimp only [epsilon0]
    exact lt_min hdelta (half_pos ht.1)
  refine ⟨epsilon0, hepsilon0, fun u hu => ?_⟩
  have huClose : dist u t < delta := hu.trans_le (min_le_left _ _)
  have huHalf : dist u t < t / 2 := hu.trans_le (min_le_right _ _)
  have huPos : 0 < u := by
    rw [Real.dist_eq] at huHalf
    have hlower := (abs_lt.mp huHalf).1
    linarith [ht.1]
  refine ⟨huPos, fun sigma hsigma => ?_⟩
  let z : ℂ := (sigma : ℂ) + u * I
  let p : ℂ := (sigma : ℂ) + t * I
  have hpK : p ∈ K := by
    change p.re ∈ Set.Icc (0 : ℝ) (1 / 2) ∧ p.im ∈ ({t} : Set ℝ)
    simpa [p] using hsigma
  have hzDist : dist z p = dist u t := by
    rw [dist_eq_norm]
    have hsub : z - p = ((u - t : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [z, p]
    rw [hsub, norm_mul]
    simp only [norm_real, norm_I, mul_one, Real.norm_eq_abs, Real.dist_eq]
  have hzThick : z ∈ Metric.thickening delta K := by
    apply Metric.mem_thickening_iff.mpr
    exact ⟨p, hpK, by rw [hzDist]; exact huClose⟩
  have hzU := hthick hzThick
  change z ∈ ⋃ rho : K, Metric.ball (rho : ℂ) (epsilon rho) at hzU
  obtain ⟨rho, hzBall⟩ := Set.mem_iUnion.mp hzU
  simpa only [z] using
    hnegative rho z (by simpa [Metric.mem_ball] using hzBall)

/-- The literal finite input at height ten used by Levinson--Montgomery. The source obtains the
strict sign and zero offset from explicit low-zero information. -/
def LevinsonMontgomeryHeightTenCertificate : Prop :=
  SpeiserStrictNegativeHorizontal 10 ∧
    speiserUpperLeftDerivZeroCount 10 = speiserUpperLeftZetaZeroCount 10

/-- The literal height-ten certificate propagates to the slightly higher base required by the
uniform critical-strip construction, with both multiplicity-bearing finite counts unchanged. -/
theorem levinsonMontgomeryNegativeExactCountBase_of_heightTenCertificate
    (hcert : LevinsonMontgomeryHeightTenCertificate) :
    LevinsonMontgomeryNegativeExactCountBase := by
  classical
  obtain ⟨epsilon, hepsilon, hnear⟩ :=
    exists_speiserStrictNegativeHorizontal_near hcert.1
  let eta : ℝ := min epsilon 1
  have heta : 0 < eta := by
    dsimp only [eta]
    exact lt_min hepsilon (by norm_num)
  let b : ℝ := 10 + eta / 2
  have htenb : (10 : ℝ) < b := by
    dsimp only [b]
    linarith
  have hetaEpsilon : eta ≤ epsilon := min_le_left _ _
  have hbClose : dist b (10 : ℝ) < epsilon := by
    rw [Real.dist_eq]
    have hdiff : b - 10 = eta / 2 := by simp [b]
    rw [hdiff, abs_of_pos (half_pos heta)]
    linarith
  have hbNegative : SpeiserStrictNegativeHorizontal b := hnear b hbClose
  have hbetweenNear : ∀ y : ℝ, (10 : ℝ) ≤ y → y < b →
      SpeiserStrictNegativeHorizontal y := by
    intro y hyTen hyb
    apply hnear y
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hyTen)]
    have hyEta : y - 10 < eta / 2 := by
      dsimp only [b] at hyb
      linarith
    exact hyEta.trans (by linarith)
  have hzetaFinset :
      speiserUpperLeftZetaZeroFinset b =
        speiserUpperLeftZetaZeroFinset 10 := by
    ext z
    simp only [mem_speiserUpperLeftZetaZeroFinset]
    constructor
    · rintro ⟨⟨hzStrip, hzb⟩, hzZero⟩
      have hzTen : z.im < 10 := by
        by_contra hnot
        have htenLe : (10 : ℝ) ≤ z.im := le_of_not_gt hnot
        have hnegative := hbetweenNear z.im htenLe hzb
        have hpoint := hnegative.2 z.re
          ⟨hzStrip.2.1.le, hzStrip.2.2.le⟩
        have hzPoint : ((z.re : ℂ) + z.im * I) = z := by
          apply Complex.ext <;> simp
        rw [hzPoint] at hpoint
        exact (hpoint.1 hzZero.1).elim
      exact ⟨⟨hzStrip, hzTen⟩, hzZero⟩
    · rintro ⟨⟨hzStrip, hzTen⟩, hzZero⟩
      exact ⟨⟨hzStrip, hzTen.trans htenb⟩, hzZero⟩
  have hderivFinset :
      speiserUpperLeftDerivZeroFinset b =
        speiserUpperLeftDerivZeroFinset 10 := by
    ext z
    simp only [mem_speiserUpperLeftDerivZeroFinset]
    constructor
    · rintro ⟨⟨hzStrip, hzb⟩, hzZero⟩
      have hzTen : z.im < 10 := by
        by_contra hnot
        have htenLe : (10 : ℝ) ≤ z.im := le_of_not_gt hnot
        have hnegative := hbetweenNear z.im htenLe hzb
        have hpoint := hnegative.2 z.re
          ⟨hzStrip.2.1.le, hzStrip.2.2.le⟩
        have hzPoint : ((z.re : ℂ) + z.im * I) = z := by
          apply Complex.ext <;> simp
        rw [hzPoint] at hpoint
        exact (hpoint.2.1 hzZero).elim
      exact ⟨⟨hzStrip, hzTen⟩, hzZero⟩
    · rintro ⟨⟨hzStrip, hzTen⟩, hzZero⟩
      exact ⟨⟨hzStrip, hzTen.trans htenb⟩, hzZero⟩
  have hzetaCount :
      speiserUpperLeftZetaZeroCount b =
        speiserUpperLeftZetaZeroCount 10 := by
    unfold speiserUpperLeftZetaZeroCount
    rw [hzetaFinset]
  have hderivCount :
      speiserUpperLeftDerivZeroCount b =
        speiserUpperLeftDerivZeroCount 10 := by
    unfold speiserUpperLeftDerivZeroCount
    rw [hderivFinset]
  refine ⟨b, htenb, hbNegative, ?_⟩
  calc
    speiserUpperLeftDerivZeroCount b =
        speiserUpperLeftDerivZeroCount 10 := hderivCount
    _ = speiserUpperLeftZetaZeroCount 10 := hcert.2
    _ = speiserUpperLeftZetaZeroCount b := hzetaCount.symm

/-- Both source count conclusions follow from the exact finite certificate stated at the source's
literal base height. -/
theorem levinsonMontgomeryTheoremOne_of_heightTenCertificate
    (hcert : LevinsonMontgomeryHeightTenCertificate) :
    LevinsonMontgomeryLogCountBound ∧ LevinsonMontgomeryCountDichotomy :=
  levinsonMontgomeryTheoremOne_of_negativeExactCountBase
    (levinsonMontgomeryNegativeExactCountBase_of_heightTenCertificate hcert)

end

end LeanLab.Riemann
