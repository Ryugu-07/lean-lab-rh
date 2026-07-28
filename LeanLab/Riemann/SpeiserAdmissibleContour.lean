import LeanLab.Riemann.LevinsonMontgomeryCriticalIndentation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.Interval.Set.Infinite

/-!
# Common admissible horizontal contours for Speiser counting

This file removes the numerical low-zero input from the bottom edge of the
Levinson--Montgomery contour. Local finiteness of the actual zeta and zeta-derivative divisors
gives a common zero-free horizontal segment in every positive-height interval. On any selected
segment, both logarithmic derivatives are interval integrable and contribute one fixed constant.
-/

namespace LeanLab.Riemann

open Complex Function MeasureTheory Set
open scoped Topology

noncomputable section

/-- The closed left-half critical-strip rectangle used to select horizontal contours. -/
def speiserClosedLeftRectangle (a b : ℝ) : Set ℂ :=
  Set.Icc (0 : ℝ) (1 / 2) ×ℂ Set.Icc a b

/-- A horizontal segment that avoids zeros of both zeta and its derivative. -/
def SpeiserCommonZeroFreeHorizontal (t : ℝ) : Prop :=
  0 < t ∧
    ∀ sigma : ℝ, sigma ∈ Set.Icc (0 : ℝ) (1 / 2) →
      riemannZeta (sigma + t * I) ≠ 0 ∧
        deriv riemannZeta (sigma + t * I) ≠ 0

private theorem isNontrivialZero_of_positive_imaginary
    {s : ℂ} (hsIm : 0 < s.im) (hzero : riemannZeta s = 0) :
    IsNontrivialZero s := by
  refine ⟨hzero, ?_, ?_⟩
  · rintro ⟨n, rfl⟩
    norm_num at hsIm
  · rintro rfl
    norm_num at hsIm

/-- Zeta zeros in a closed positive-height left-half rectangle form a finite set. -/
theorem finite_speiserClosedLeftZetaZeroSet
    {a b : ℝ} (ha : 0 < a) :
    ({s : ℂ | s ∈ speiserClosedLeftRectangle a b ∧ riemannZeta s = 0} :
      Set ℂ).Finite := by
  let K : Set ℂ := speiserClosedLeftRectangle a b
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  apply (compact_inter_nontrivialZeros_finite hK).subset
  intro s hs
  refine ⟨hs.1, isNontrivialZero_of_positive_imaginary ?_ hs.2⟩
  have hsIm : a ≤ s.im := hs.1.2.1
  linarith

/-- Zeros of `zeta'` in a closed positive-height left-half rectangle form a finite set. -/
theorem finite_speiserClosedLeftDerivZeroSet
    {a b : ℝ} :
    ({s : ℂ | s ∈ speiserClosedLeftRectangle a b ∧
      deriv riemannZeta s = 0} : Set ℂ).Finite := by
  let K : Set ℂ := speiserClosedLeftRectangle a b
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hKDomain : K ⊆ (({1} : Set ℂ)ᶜ) := by
    intro s hs hsOne
    subst s
    change (1 : ℂ).re ∈ Set.Icc (0 : ℝ) (1 / 2) ∧
      (1 : ℂ).im ∈ Set.Icc a b at hs
    norm_num at hs
  have hAnalyticK : AnalyticOnNhd ℂ (deriv riemannZeta) K :=
    analyticOnNhd_deriv_riemannZeta.mono hKDomain
  apply ((MeromorphicOn.divisor (deriv riemannZeta) K).finiteSupport hK).subset
  intro s hs
  rw [Function.mem_support]
  have hsOne : s ≠ 1 := hKDomain hs.1
  have hdivisor :
      MeromorphicOn.divisor (deriv riemannZeta) K s =
        (riemannZetaDerivZeroMultiplicity s : ℤ) := by
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hAnalyticK hs.1,
      ← Nat.cast_analyticOrderNatAt (analyticOrderAt_deriv_riemannZeta_ne_top hsOne)]
    simp [riemannZetaDerivZeroMultiplicity]
  rw [hdivisor]
  exact_mod_cast Nat.ne_of_gt
    ((riemannZetaDerivZeroMultiplicity_pos_iff hsOne).mpr hs.2)

/-- Imaginary parts that cannot be used as a common horizontal contour in `[a,b]`. -/
def speiserCommonBadHeightSet (a b : ℝ) : Set ℝ :=
  Complex.im '' {s : ℂ |
      s ∈ speiserClosedLeftRectangle a b ∧ riemannZeta s = 0} ∪
    Complex.im '' {s : ℂ |
      s ∈ speiserClosedLeftRectangle a b ∧ deriv riemannZeta s = 0}

theorem finite_speiserCommonBadHeightSet
    {a b : ℝ} (ha : 0 < a) :
    (speiserCommonBadHeightSet a b).Finite := by
  apply Set.Finite.union
  · exact (finite_speiserClosedLeftZetaZeroSet ha).image Complex.im
  · exact finite_speiserClosedLeftDerivZeroSet.image Complex.im

/-- Every positive-height interval contains a horizontal segment avoiding both actual divisors. -/
theorem exists_speiserCommonZeroFreeHorizontal_between
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ t : ℝ, t ∈ Set.Ioo a b ∧ SpeiserCommonZeroFreeHorizontal t := by
  have hinfinite :
      (Set.Ioo a b \ speiserCommonBadHeightSet a b).Infinite :=
    (Set.Ioo_infinite hab).sdiff (finite_speiserCommonBadHeightSet ha)
  obtain ⟨t, htIoo, htGood⟩ := hinfinite.nonempty
  refine ⟨t, htIoo, ⟨ha.trans htIoo.1, fun sigma hsigma => ?_⟩⟩
  let s : ℂ := sigma + t * I
  have hsRect : s ∈ speiserClosedLeftRectangle a b := by
    change s.re ∈ Set.Icc (0 : ℝ) (1 / 2) ∧ s.im ∈ Set.Icc a b
    simpa [s] using And.intro hsigma ⟨htIoo.1.le, htIoo.2.le⟩
  constructor
  · intro hzero
    apply htGood
    left
    exact ⟨s, ⟨hsRect, hzero⟩, by simp [s]⟩
  · intro hzero
    apply htGood
    right
    exact ⟨s, ⟨hsRect, hzero⟩, by simp [s]⟩

/-- Common zero-free horizontal segments occur above every prescribed height. -/
theorem exists_speiserCommonZeroFreeHorizontal_above (B : ℝ) :
    ∃ t : ℝ, B < t ∧ SpeiserCommonZeroFreeHorizontal t := by
  let a : ℝ := max B 0 + 1
  let b : ℝ := a + 1
  have ha : 0 < a := by
    dsimp [a]
    linarith [le_max_right B 0]
  have hab : a < b := by
    dsimp [b]
    linarith
  obtain ⟨t, ht, hfree⟩ :=
    exists_speiserCommonZeroFreeHorizontal_between ha hab
  refine ⟨t, ?_, hfree⟩
  have hBa : B < a := by
    dsimp [a]
    linarith [le_max_left B 0]
  exact hBa.trans ht.1

theorem intervalIntegrable_speiserZetaLogDeriv_horizontal
    {t : ℝ} (ht : SpeiserCommonZeroFreeHorizontal t) :
    IntervalIntegrable
      (fun sigma : ℝ => logDeriv riemannZeta (sigma + t * I))
      (volume : Measure ℝ) (0 : ℝ) (1 / 2) := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
  intro sigma hsigma
  have hsOne : (sigma : ℂ) + t * I ≠ 1 := by
    intro hs
    have hre := congrArg Complex.re hs
    norm_num at hre
    linarith [hsigma.2]
  have hanalytic : AnalyticAt ℂ riemannZeta ((sigma : ℂ) + t * I) :=
    analyticOn_riemannZeta _ (by simpa using hsOne)
  let phi : ℝ → ℂ := fun x => x + t * I
  have hphi : Continuous phi := by
    fun_prop
  have houter :=
    levinsonMontgomery_continuousAt_logDeriv_of_analyticAt_of_ne_zero
      hanalytic (ht.2 sigma hsigma).1
  simpa only [phi, Function.comp_def] using
    (ContinuousAt.comp (f := phi) (x := sigma) houter hphi.continuousAt).continuousWithinAt

theorem intervalIntegrable_speiserZetaDerivLogDeriv_horizontal
    {t : ℝ} (ht : SpeiserCommonZeroFreeHorizontal t) :
    IntervalIntegrable
      (fun sigma : ℝ => logDeriv (deriv riemannZeta) (sigma + t * I))
      (volume : Measure ℝ) (0 : ℝ) (1 / 2) := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
  intro sigma hsigma
  have hsOne : (sigma : ℂ) + t * I ≠ 1 := by
    intro hs
    have hre := congrArg Complex.re hs
    norm_num at hre
    linarith [hsigma.2]
  have hanalytic :
      AnalyticAt ℂ (deriv riemannZeta) ((sigma : ℂ) + t * I) :=
    analyticOnNhd_deriv_riemannZeta _ (by simpa using hsOne)
  let phi : ℝ → ℂ := fun x => x + t * I
  have hphi : Continuous phi := by
    fun_prop
  have houter :=
    levinsonMontgomery_continuousAt_logDeriv_of_analyticAt_of_ne_zero
      hanalytic (ht.2 sigma hsigma).2
  simpa only [phi, Function.comp_def] using
    (ContinuousAt.comp (f := phi) (x := sigma) houter hphi.continuousAt).continuousWithinAt

/-- A selected bottom contributes one fixed constant, with no low-zero sign input. -/
theorem exists_speiserFixedBottomLogDerivBound
    {b : ℝ} (hb : SpeiserCommonZeroFreeHorizontal b) :
    ∃ C : ℝ, 0 ≤ C ∧
      ‖∫ sigma : ℝ in (0 : ℝ)..(1 / 2),
          logDeriv riemannZeta (sigma + b * I)‖ +
        ‖∫ sigma : ℝ in (0 : ℝ)..(1 / 2),
          logDeriv (deriv riemannZeta) (sigma + b * I)‖ ≤ C := by
  have _hzeta :=
    intervalIntegrable_speiserZetaLogDeriv_horizontal hb
  have _hderiv :=
    intervalIntegrable_speiserZetaDerivLogDeriv_horizontal hb
  refine ⟨
    ‖∫ sigma : ℝ in (0 : ℝ)..(1 / 2),
        logDeriv riemannZeta (sigma + b * I)‖ +
      ‖∫ sigma : ℝ in (0 : ℝ)..(1 / 2),
        logDeriv (deriv riemannZeta) (sigma + b * I)‖,
    add_nonneg (norm_nonneg _) (norm_nonneg _), le_rfl⟩

/-- A nonvanishing closed model path whose logarithmic derivative has winding one. -/
def speiserNonzeroWindingModel (z : ℂ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * I * z)

theorem speiserNonzeroWindingModel_ne_zero (z : ℂ) :
    speiserNonzeroWindingModel z ≠ 0 :=
  Complex.exp_ne_zero _

theorem speiserNonzeroWindingModel_zero_eq_one :
    speiserNonzeroWindingModel 0 = speiserNonzeroWindingModel 1 := by
  simp [speiserNonzeroWindingModel, Complex.exp_two_pi_mul_I]

theorem logDeriv_speiserNonzeroWindingModel (z : ℂ) :
    logDeriv speiserNonzeroWindingModel z =
      2 * (Real.pi : ℂ) * I := by
  rw [logDeriv_apply]
  have hlinear :
      HasDerivAt (fun w : ℂ => 2 * (Real.pi : ℂ) * I * w)
        (2 * (Real.pi : ℂ) * I) z := by
    simpa only [id_eq, mul_one] using
      (hasDerivAt_id z).const_mul (2 * (Real.pi : ℂ) * I)
  have hexp :=
    (Complex.hasDerivAt_exp (2 * (Real.pi : ℂ) * I * z)).comp z hlinear
  have hderiv :
      deriv (fun w : ℂ => Complex.exp (2 * (Real.pi : ℂ) * I * w)) z =
        Complex.exp (2 * (Real.pi : ℂ) * I * z) *
          (2 * (Real.pi : ℂ) * I) := by
    simpa only [Function.comp_def] using hexp.deriv
  change
    deriv (fun w : ℂ => Complex.exp (2 * (Real.pi : ℂ) * I * w)) z /
        Complex.exp (2 * (Real.pi : ℂ) * I * z) =
      2 * (Real.pi : ℂ) * I
  rw [hderiv]
  field_simp [Complex.exp_ne_zero]

/-- Nonvanishing and matching endpoints alone do not force zero logarithmic winding. -/
theorem integral_logDeriv_speiserNonzeroWindingModel :
    (∫ x : ℝ in (0 : ℝ)..1,
      logDeriv speiserNonzeroWindingModel x) =
        2 * (Real.pi : ℂ) * I := by
  simp only [logDeriv_speiserNonzeroWindingModel]
  norm_num

/-- Aggregate certificate for the source's numerical-bottom replacement. -/
theorem speiserAdmissibleHorizontal_endpoint :
    (∀ B : ℝ, ∃ t : ℝ, B < t ∧ SpeiserCommonZeroFreeHorizontal t) ∧
      ∀ b : ℝ, SpeiserCommonZeroFreeHorizontal b →
        IntervalIntegrable
          (fun sigma : ℝ => logDeriv riemannZeta (sigma + b * I))
          (volume : Measure ℝ) (0 : ℝ) (1 / 2) ∧
        IntervalIntegrable
          (fun sigma : ℝ => logDeriv (deriv riemannZeta) (sigma + b * I))
          (volume : Measure ℝ) (0 : ℝ) (1 / 2) ∧
        ∃ C : ℝ, 0 ≤ C ∧
          ‖∫ sigma : ℝ in (0 : ℝ)..(1 / 2),
              logDeriv riemannZeta (sigma + b * I)‖ +
            ‖∫ sigma : ℝ in (0 : ℝ)..(1 / 2),
              logDeriv (deriv riemannZeta) (sigma + b * I)‖ ≤ C := by
  refine ⟨exists_speiserCommonZeroFreeHorizontal_above, fun b hb => ?_⟩
  exact ⟨intervalIntegrable_speiserZetaLogDeriv_horizontal hb,
    intervalIntegrable_speiserZetaDerivLogDeriv_horizontal hb,
    exists_speiserFixedBottomLogDerivBound hb⟩

end

end LeanLab.Riemann
