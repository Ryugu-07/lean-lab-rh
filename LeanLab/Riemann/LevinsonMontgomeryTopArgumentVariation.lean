import LeanLab.Riemann.LevinsonMontgomeryJensenTopZeroCount
import Mathlib.Data.Finset.Sort
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.Interval.Set.Infinite

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Top argument variation in the Levinson--Montgomery contour

This file converts a finite set containing every real-part crossing of a nonvanishing
differentiable complex path into a bound for its continuous argument variation. It then charges
the actual zeta and phase-normalized zeta-derivative crossings to the Jensen divisors constructed
in `LevinsonMontgomeryJensenTopZeroCount`.
-/

namespace LeanLab.Riemann

open Complex Function MeasureTheory Set
open scoped Topology

noncomputable section

/-- A weakly right-half-plane path has the principal-log endpoint formula. Nonvanishing is
needed only when the path touches the imaginary axis. -/
theorem intervalIntegral_deriv_div_eq_log_sub_of_re_nonneg
    {g g' : ℝ → ℂ} {a b : ℝ}
    (hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt g (g' x) x)
    (hintegrable :
      IntervalIntegrable (fun x => g' x / g x) (volume : Measure ℝ) a b)
    (hne : ∀ x ∈ Set.uIcc a b, g x ≠ 0)
    (hre : ∀ x ∈ Set.uIcc a b, 0 ≤ (g x).re) :
    (∫ x : ℝ in a..b, g' x / g x) =
      Complex.log (g b) - Complex.log (g a) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    have hslit : g x ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      by_cases hpos : 0 < (g x).re
      · exact Or.inl hpos
      · right
        intro him
        apply hne x hx
        apply Complex.ext
        · simpa using le_antisymm (not_lt.mp hpos) (hre x hx)
        · simpa using him
    exact (hderiv x hx).clog_real hslit
  · exact hintegrable

/-- A weakly left-half-plane path has the principal-log endpoint formula after negation. -/
theorem intervalIntegral_deriv_div_eq_log_neg_sub_of_re_nonpos
    {g g' : ℝ → ℂ} {a b : ℝ}
    (hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt g (g' x) x)
    (hintegrable :
      IntervalIntegrable (fun x => g' x / g x) (volume : Measure ℝ) a b)
    (hne : ∀ x ∈ Set.uIcc a b, g x ≠ 0)
    (hre : ∀ x ∈ Set.uIcc a b, (g x).re ≤ 0) :
    (∫ x : ℝ in a..b, g' x / g x) =
      Complex.log (-g b) - Complex.log (-g a) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    have hslit : -g x ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      by_cases hpos : 0 < (-g x).re
      · exact Or.inl hpos
      · right
        intro him
        apply neg_ne_zero.mpr (hne x hx)
        apply Complex.ext
        · exact le_antisymm (not_lt.mp hpos) (by simpa using hre x hx)
        · exact him
    simpa only [Pi.neg_apply, neg_div_neg_eq] using
      (hderiv x hx).neg.clog_real hslit
  · exact hintegrable

private theorem exists_interior_re_eq_zero_of_opposite
    {g : ℝ → ℂ} {a b x y : ℝ}
    (hcont : ContinuousOn g (Set.Icc a b))
    (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b)
    (hxneg : (g x).re < 0) (hypos : 0 < (g y).re) :
    ∃ z ∈ Set.Ioo a b, (g z).re = 0 := by
  have hsub : Set.uIcc x y ⊆ Set.Icc a b := by
    intro z hz
    rcases le_total x y with hxy | hyx
    · rw [Set.uIcc_of_le hxy] at hz
      exact ⟨hx.1.trans hz.1, hz.2.trans hy.2⟩
    · rw [Set.uIcc_of_ge hyx] at hz
      exact ⟨hy.1.trans hz.1, hz.2.trans hx.2⟩
  have hcontRe :
      ContinuousOn (fun z : ℝ => (g z).re) (Set.uIcc x y) :=
    Complex.continuous_re.comp_continuousOn (hcont.mono hsub)
  have hzero :
      (0 : ℝ) ∈ Set.uIcc (g x).re (g y).re := by
    rw [Set.uIcc_of_le (hxneg.le.trans hypos.le)]
    exact ⟨hxneg.le, hypos.le⟩
  obtain ⟨z, hz, hzzero⟩ :=
    (intermediate_value_uIcc hcontRe) hzero
  refine ⟨z, ?_, hzzero⟩
  rcases le_total x y with hxy | hyx
  · rw [Set.uIcc_of_le hxy] at hz
    have hxz : x < z := lt_of_le_of_ne hz.1 (by
      intro hzx
      subst z
      linarith)
    have hzy : z < y := lt_of_le_of_ne hz.2 (by
      intro hzy
      subst y
      linarith)
    exact ⟨lt_of_le_of_lt hx.1 hxz, lt_of_lt_of_le hzy hy.2⟩
  · rw [Set.uIcc_of_ge hyx] at hz
    have hyz : y < z := lt_of_le_of_ne hz.1 (by
      intro hzy
      subst z
      linarith)
    have hzx : z < x := lt_of_le_of_ne hz.2 (by
      intro hzx
      subst x
      linarith)
    exact ⟨lt_of_le_of_lt hy.1 hyz, lt_of_lt_of_le hzx hx.2⟩

private theorem re_halfPlane_alternative_of_no_interior_crossing
    {g : ℝ → ℂ} {a b : ℝ}
    (hab : a < b)
    (hcont : ContinuousOn g (Set.Icc a b))
    (hcross : ∀ x ∈ Set.Ioo a b, (g x).re ≠ 0) :
    (∀ x ∈ Set.Icc a b, 0 ≤ (g x).re) ∨
      (∀ x ∈ Set.Icc a b, (g x).re ≤ 0) := by
  let m : ℝ := (a + b) / 2
  have hm : m ∈ Set.Ioo a b := by
    dsimp only [m]
    constructor <;> linarith
  rcases lt_or_gt_of_ne (hcross m hm) with hmneg | hmpos
  · right
    intro x hx
    by_contra hxpos
    have hxpos' : 0 < (g x).re := lt_of_not_ge hxpos
    obtain ⟨z, hz, hzero⟩ :=
      exists_interior_re_eq_zero_of_opposite hcont
        (Set.Ioo_subset_Icc_self hm) hx hmneg hxpos'
    exact hcross z hz hzero
  · left
    intro x hx
    by_contra hxneg
    have hxneg' : (g x).re < 0 := lt_of_not_ge hxneg
    obtain ⟨z, hz, hzero⟩ :=
      exists_interior_re_eq_zero_of_opposite hcont
        hx (Set.Ioo_subset_Icc_self hm) hxneg' hmpos
    exact hcross z hz hzero

/-- On one crossing-free gap, continuous argument variation is at most `pi`. -/
theorem abs_im_intervalIntegral_deriv_div_le_pi_of_no_interior_crossing
    {g g' : ℝ → ℂ} {a b : ℝ}
    (hab : a < b)
    (hderiv : ∀ x ∈ Set.Icc a b, HasDerivAt g (g' x) x)
    (hintegrable :
      IntervalIntegrable (fun x => g' x / g x) (volume : Measure ℝ) a b)
    (hne : ∀ x ∈ Set.Icc a b, g x ≠ 0)
    (hcross : ∀ x ∈ Set.Ioo a b, (g x).re ≠ 0) :
    abs ((∫ x : ℝ in a..b, g' x / g x).im) ≤ Real.pi := by
  have hcont : ContinuousOn g (Set.Icc a b) := by
    intro x hx
    exact (hderiv x hx).continuousAt.continuousWithinAt
  rcases re_halfPlane_alternative_of_no_interior_crossing
      hab hcont hcross with hre | hre
  · have hformula :=
      intervalIntegral_deriv_div_eq_log_sub_of_re_nonneg
        (a := a) (b := b)
        (by simpa only [Set.uIcc_of_le hab.le] using hderiv)
        hintegrable
        (by simpa only [Set.uIcc_of_le hab.le] using hne)
        (by simpa only [Set.uIcc_of_le hab.le] using hre)
    rw [hformula]
    simp only [Complex.sub_im, Complex.log_im]
    calc
      |Complex.arg (g b) - Complex.arg (g a)| ≤
          |Complex.arg (g b)| + |Complex.arg (g a)| := abs_sub _ _
      _ ≤ Real.pi / 2 + Real.pi / 2 := add_le_add
        (Complex.abs_arg_le_pi_div_two_iff.mpr (hre b ⟨hab.le, le_rfl⟩))
        (Complex.abs_arg_le_pi_div_two_iff.mpr (hre a ⟨le_rfl, hab.le⟩))
      _ = Real.pi := by ring
  · have hformula :=
      intervalIntegral_deriv_div_eq_log_neg_sub_of_re_nonpos
        (a := a) (b := b)
        (by simpa only [Set.uIcc_of_le hab.le] using hderiv)
        hintegrable
        (by simpa only [Set.uIcc_of_le hab.le] using hne)
        (by simpa only [Set.uIcc_of_le hab.le] using hre)
    rw [hformula]
    simp only [Complex.sub_im, Complex.log_im]
    calc
      |Complex.arg (-g b) - Complex.arg (-g a)| ≤
          |Complex.arg (-g b)| + |Complex.arg (-g a)| := abs_sub _ _
      _ ≤ Real.pi / 2 + Real.pi / 2 := add_le_add
        (Complex.abs_arg_le_pi_div_two_iff.mpr (by
          simpa only [neg_re] using neg_nonneg.mpr (hre b ⟨hab.le, le_rfl⟩)))
        (Complex.abs_arg_le_pi_div_two_iff.mpr (by
          simpa only [neg_re] using neg_nonneg.mpr (hre a ⟨le_rfl, hab.le⟩)))
      _ = Real.pi := by ring

private theorem abs_im_intervalIntegral_deriv_div_le_of_crossingList
    {g g' : ℝ → ℂ} {a b : ℝ}
    (points : List ℝ)
    (hab : a < b)
    (hsorted : points.Pairwise (· < ·))
    (hpoints : ∀ x ∈ points, x ∈ Set.Ioo a b)
    (hderiv : ∀ x ∈ Set.Icc a b, HasDerivAt g (g' x) x)
    (hintegrable :
      IntervalIntegrable (fun x => g' x / g x) (volume : Measure ℝ) a b)
    (hne : ∀ x ∈ Set.Icc a b, g x ≠ 0)
    (hcross : ∀ x ∈ Set.Ioo a b, (g x).re = 0 → x ∈ points) :
    abs ((∫ x : ℝ in a..b, g' x / g x).im) ≤
      Real.pi * ((points.length : ℝ) + 1) := by
  induction points generalizing a with
  | nil =>
      have hnocross : ∀ x ∈ Set.Ioo a b, (g x).re ≠ 0 := by
        intro x hx hzero
        simpa using hcross x hx hzero
      simpa using
        abs_im_intervalIntegral_deriv_div_le_pi_of_no_interior_crossing
          hab hderiv hintegrable hne hnocross
  | cons x xs ih =>
      have hsortedData := List.pairwise_cons.mp hsorted
      have hx : x ∈ Set.Ioo a b := hpoints x (by simp)
      have hleftNoCross :
          ∀ y ∈ Set.Ioo a x, (g y).re ≠ 0 := by
        intro y hy hzero
        have hyab : y ∈ Set.Ioo a b :=
          ⟨hy.1, hy.2.trans hx.2⟩
        have hymem := hcross y hyab hzero
        rcases List.mem_cons.mp hymem with heq | hymem
        · exact (ne_of_lt hy.2) heq
        · exact (not_lt_of_ge (hsortedData.1 y hymem).le hy.2)
      have hleftDeriv :
          ∀ y ∈ Set.Icc a x, HasDerivAt g (g' y) y := by
        intro y hy
        exact hderiv y ⟨hy.1, hy.2.trans hx.2.le⟩
      have hrightDeriv :
          ∀ y ∈ Set.Icc x b, HasDerivAt g (g' y) y := by
        intro y hy
        exact hderiv y ⟨hx.1.le.trans hy.1, hy.2⟩
      have hleftInt :
          IntervalIntegrable (fun y => g' y / g y)
            (volume : Measure ℝ) a x := by
        apply hintegrable.mono_set
        rw [Set.uIcc_of_le hx.1.le, Set.uIcc_of_le hab.le]
        exact Set.Icc_subset_Icc_right hx.2.le
      have hrightInt :
          IntervalIntegrable (fun y => g' y / g y)
            (volume : Measure ℝ) x b := by
        apply hintegrable.mono_set
        rw [Set.uIcc_of_le hx.2.le, Set.uIcc_of_le hab.le]
        exact Set.Icc_subset_Icc_left hx.1.le
      have hleftNe : ∀ y ∈ Set.Icc a x, g y ≠ 0 := by
        intro y hy
        exact hne y ⟨hy.1, hy.2.trans hx.2.le⟩
      have hrightNe : ∀ y ∈ Set.Icc x b, g y ≠ 0 := by
        intro y hy
        exact hne y ⟨hx.1.le.trans hy.1, hy.2⟩
      have hleft :=
        abs_im_intervalIntegral_deriv_div_le_pi_of_no_interior_crossing
          hx.1 hleftDeriv hleftInt hleftNe hleftNoCross
      have hpointsTail : ∀ y ∈ xs, y ∈ Set.Ioo x b := by
        intro y hy
        exact ⟨hsortedData.1 y hy, (hpoints y (by simp [hy])).2⟩
      have hcrossTail :
          ∀ y ∈ Set.Ioo x b, (g y).re = 0 → y ∈ xs := by
        intro y hy hzero
        have hyab : y ∈ Set.Ioo a b :=
          ⟨hx.1.trans hy.1, hy.2⟩
        have hymem := hcross y hyab hzero
        rcases List.mem_cons.mp hymem with heq | hymem
        · exact (ne_of_gt hy.1 heq).elim
        · exact hymem
      have hright :=
        ih hx.2 hsortedData.2 hpointsTail hrightDeriv hrightInt hrightNe hcrossTail
      have hsplit :=
        intervalIntegral.integral_add_adjacent_intervals hleftInt hrightInt
      calc
        abs ((∫ y : ℝ in a..b, g' y / g y).im) =
            abs (((∫ y : ℝ in a..x, g' y / g y) +
              ∫ y : ℝ in x..b, g' y / g y).im) := by rw [hsplit]
        _ = abs ((∫ y : ℝ in a..x, g' y / g y).im +
              (∫ y : ℝ in x..b, g' y / g y).im) := by
              rw [Complex.add_im]
        _ ≤ abs ((∫ y : ℝ in a..x, g' y / g y).im) +
              abs ((∫ y : ℝ in x..b, g' y / g y).im) := abs_add_le _ _
        _ ≤ Real.pi + Real.pi * ((xs.length : ℝ) + 1) :=
          add_le_add hleft hright
        _ = Real.pi * (((x :: xs).length : ℝ) + 1) := by
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          ring

/-- A finite set containing every interior real-part crossing bounds the continuous argument
variation by `pi * (card + 1)`. The set may contain extraneous points. -/
theorem abs_im_intervalIntegral_deriv_div_le_of_crossings_subset
    {g g' : ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b)
    (hderiv : ∀ x ∈ Set.Icc a b, HasDerivAt g (g' x) x)
    (hintegrable :
      IntervalIntegrable (fun x => g' x / g x) (volume : Measure ℝ) a b)
    (hne : ∀ x ∈ Set.Icc a b, g x ≠ 0)
    (S : Finset ℝ)
    (hcross : ∀ x ∈ Set.Ioo a b, (g x).re = 0 → x ∈ S) :
    abs ((∫ x : ℝ in a..b, g' x / g x).im) ≤
      Real.pi * ((S.card : ℝ) + 1) := by
  rcases hab.eq_or_lt with rfl | hab
  · simp only [intervalIntegral.integral_same, Complex.zero_im, abs_zero]
    exact mul_nonneg Real.pi_pos.le (by positivity)
  · let T : Finset ℝ := S.filter fun x => x ∈ Set.Ioo a b
    let points : List ℝ := T.sort
    have hsorted : points.Pairwise (· < ·) :=
      (Finset.sortedLT_sort T).pairwise
    have hpoints : ∀ x ∈ points, x ∈ Set.Ioo a b := by
      intro x hx
      have hxT : x ∈ T := (Finset.mem_sort (r := (· ≤ ·))).mp hx
      exact (Finset.mem_filter.mp hxT).2
    have hcrossPoints :
        ∀ x ∈ Set.Ioo a b, (g x).re = 0 → x ∈ points := by
      intro x hx hzero
      apply (Finset.mem_sort (r := (· ≤ ·))).mpr
      exact Finset.mem_filter.mpr ⟨hcross x hx hzero, hx⟩
    have hlist :=
      abs_im_intervalIntegral_deriv_div_le_of_crossingList
        points hab hsorted hpoints hderiv hintegrable hne hcrossPoints
    calc
      abs ((∫ x : ℝ in a..b, g' x / g x).im) ≤
          Real.pi * ((points.length : ℝ) + 1) := hlist
      _ = Real.pi * ((T.card : ℝ) + 1) := by
        rw [Finset.length_sort]
      _ ≤ Real.pi * ((S.card : ℝ) + 1) := by
        gcongr
        dsimp only [T]
        exact Finset.filter_subset (fun x : ℝ => x ∈ Set.Ioo a b) S

/-- The complete closed source rectangle used to select zero-free top heights. -/
def levinsonMontgomeryClosedTopRectangle (a b : ℝ) : Set ℂ :=
  Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc a b

/-- A positive top height avoiding both actual divisors on the complete source segment. -/
def LevinsonMontgomeryTopAdmissible (t : ℝ) : Prop :=
  0 < t ∧
    ∀ sigma : ℝ, sigma ∈ Set.Icc (0 : ℝ) 1 →
      riemannZeta (sigma + t * I) ≠ 0 ∧
        deriv riemannZeta (sigma + t * I) ≠ 0

private theorem isNontrivialZero_of_positive_imaginary_top
    {s : ℂ} (hsIm : 0 < s.im) (hzero : riemannZeta s = 0) :
    IsNontrivialZero s := by
  refine ⟨hzero, ?_, ?_⟩
  · rintro ⟨n, rfl⟩
    norm_num at hsIm
  · rintro rfl
    norm_num at hsIm

theorem finite_levinsonMontgomeryClosedTopZetaZeroSet
    {a b : ℝ} (ha : 0 < a) :
    ({s : ℂ | s ∈ levinsonMontgomeryClosedTopRectangle a b ∧
      riemannZeta s = 0} : Set ℂ).Finite := by
  let K : Set ℂ := levinsonMontgomeryClosedTopRectangle a b
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  apply (compact_inter_nontrivialZeros_finite hK).subset
  intro s hs
  refine ⟨hs.1, isNontrivialZero_of_positive_imaginary_top ?_ hs.2⟩
  have hsIm : a ≤ s.im := hs.1.2.1
  linarith

theorem finite_levinsonMontgomeryClosedTopDerivZeroSet
    {a b : ℝ} (ha : 0 < a) :
    ({s : ℂ | s ∈ levinsonMontgomeryClosedTopRectangle a b ∧
      deriv riemannZeta s = 0} : Set ℂ).Finite := by
  let K : Set ℂ := levinsonMontgomeryClosedTopRectangle a b
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hKDomain : K ⊆ (({1} : Set ℂ)ᶜ) := by
    intro s hs hsOne
    have hsEq : s = 1 := by simpa using hsOne
    subst s
    change (1 : ℂ).re ∈ Set.Icc (0 : ℝ) 1 ∧
      (1 : ℂ).im ∈ Set.Icc a b at hs
    norm_num at hs
    linarith
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
      ← Nat.cast_analyticOrderNatAt
        (analyticOrderAt_deriv_riemannZeta_ne_top hsOne)]
    simp [riemannZetaDerivZeroMultiplicity]
  rw [hdivisor]
  exact_mod_cast Nat.ne_of_gt
    ((riemannZetaDerivZeroMultiplicity_pos_iff hsOne).mpr hs.2)

def levinsonMontgomeryTopBadHeightSet (a b : ℝ) : Set ℝ :=
  Complex.im '' {s : ℂ |
      s ∈ levinsonMontgomeryClosedTopRectangle a b ∧ riemannZeta s = 0} ∪
    Complex.im '' {s : ℂ |
      s ∈ levinsonMontgomeryClosedTopRectangle a b ∧
        deriv riemannZeta s = 0}

theorem finite_levinsonMontgomeryTopBadHeightSet
    {a b : ℝ} (ha : 0 < a) :
    (levinsonMontgomeryTopBadHeightSet a b).Finite := by
  apply Set.Finite.union
  · exact (finite_levinsonMontgomeryClosedTopZetaZeroSet ha).image Complex.im
  · exact
      (finite_levinsonMontgomeryClosedTopDerivZeroSet ha).image Complex.im

theorem exists_levinsonMontgomeryTopAdmissible_between
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ t : ℝ, t ∈ Set.Ioo a b ∧ LevinsonMontgomeryTopAdmissible t := by
  have hinfinite :
      (Set.Ioo a b \ levinsonMontgomeryTopBadHeightSet a b).Infinite :=
    (Set.Ioo_infinite hab).sdiff (finite_levinsonMontgomeryTopBadHeightSet ha)
  obtain ⟨t, htIoo, htGood⟩ := hinfinite.nonempty
  refine ⟨t, htIoo, ⟨ha.trans htIoo.1, fun sigma hsigma => ?_⟩⟩
  let s : ℂ := sigma + t * I
  have hsRect : s ∈ levinsonMontgomeryClosedTopRectangle a b := by
    change s.re ∈ Set.Icc (0 : ℝ) 1 ∧ s.im ∈ Set.Icc a b
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

/-- Common zero-free actual top heights occur above every prescribed height. -/
theorem exists_levinsonMontgomeryTopAdmissible_above (B : ℝ) :
    ∃ t : ℝ, B < t ∧ LevinsonMontgomeryTopAdmissible t := by
  let a : ℝ := max B 0 + 1
  let b : ℝ := a + 1
  have ha : 0 < a := by
    dsimp only [a]
    linarith [le_max_right B 0]
  have hab : a < b := by
    dsimp only [b]
    linarith
  obtain ⟨t, ht, hfree⟩ :=
    exists_levinsonMontgomeryTopAdmissible_between ha hab
  refine ⟨t, ?_, hfree⟩
  have hBa : B < a := by
    dsimp only [a]
    linarith [le_max_left B 0]
  exact hBa.trans ht.1

theorem intervalIntegrable_levinsonMontgomeryZetaLogDeriv_top
    {t : ℝ} (ht : LevinsonMontgomeryTopAdmissible t) :
    IntervalIntegrable
      (fun sigma : ℝ => logDeriv riemannZeta (sigma + t * I))
      (volume : Measure ℝ) (0 : ℝ) 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
  intro sigma hsigma
  have hsOne : (sigma : ℂ) + t * I ≠ 1 := by
    intro hs
    have him := congrArg Complex.im hs
    norm_num at him
    linarith [ht.1]
  have hanalytic : AnalyticAt ℂ riemannZeta ((sigma : ℂ) + t * I) :=
    analyticOn_riemannZeta _ (by simpa using hsOne)
  let phi : ℝ → ℂ := fun x => x + t * I
  have hphi : Continuous phi := by fun_prop
  have houter :=
    levinsonMontgomery_continuousAt_logDeriv_of_analyticAt_of_ne_zero
      hanalytic (ht.2 sigma hsigma).1
  simpa only [phi, Function.comp_def] using
    (ContinuousAt.comp (f := phi) (x := sigma)
      houter hphi.continuousAt).continuousWithinAt

theorem intervalIntegrable_levinsonMontgomeryZetaDerivLogDeriv_top
    {t : ℝ} (ht : LevinsonMontgomeryTopAdmissible t) :
    IntervalIntegrable
      (fun sigma : ℝ =>
        logDeriv (deriv riemannZeta) (sigma + t * I))
      (volume : Measure ℝ) (0 : ℝ) 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
  intro sigma hsigma
  have hsOne : (sigma : ℂ) + t * I ≠ 1 := by
    intro hs
    have him := congrArg Complex.im hs
    norm_num at him
    linarith [ht.1]
  have hanalytic :
      AnalyticAt ℂ (deriv riemannZeta) ((sigma : ℂ) + t * I) :=
    analyticOnNhd_deriv_riemannZeta _ (by simpa using hsOne)
  let phi : ℝ → ℂ := fun x => x + t * I
  have hphi : Continuous phi := by fun_prop
  have houter :=
    levinsonMontgomery_continuousAt_logDeriv_of_analyticAt_of_ne_zero
      hanalytic (ht.2 sigma hsigma).2
  simpa only [phi, Function.comp_def] using
    (ContinuousAt.comp (f := phi) (x := sigma)
      houter hphi.continuousAt).continuousWithinAt

/-- The finite support of a divisor on a compact set. -/
noncomputable def compactDivisorSupportFinset
    (f : ℂ → ℂ) (K : Set ℂ) (hK : IsCompact K) : Finset ℂ :=
  ((MeromorphicOn.divisor f K).finiteSupport hK).toFinset

@[simp]
theorem mem_compactDivisorSupportFinset
    {f : ℂ → ℂ} {K : Set ℂ} {hK : IsCompact K} {z : ℂ} :
    z ∈ compactDivisorSupportFinset f K hK ↔
      z ∈ Function.support (MeromorphicOn.divisor f K) := by
  simp [compactDivisorSupportFinset]

/-- For an analytic function, every divisor support point contributes at least one to the
multiplicity sum. -/
theorem compactDivisorSupportFinset_card_le_finsum
    {f : ℂ → ℂ} {K : Set ℂ} (hK : IsCompact K)
    (hanalytic : AnalyticOnNhd ℂ f K) :
    ((compactDivisorSupportFinset f K hK).card : ℤ) ≤
      ∑ᶠ z : ℂ, MeromorphicOn.divisor f K z := by
  classical
  let d : ℂ → ℤ := MeromorphicOn.divisor f K
  let S : Finset ℂ := compactDivisorSupportFinset f K hK
  have hpos : ∀ z ∈ S, (1 : ℤ) ≤ d z := by
    intro z hz
    have hzSupport : z ∈ Function.support d := by
      simpa only [S, d, mem_compactDivisorSupportFinset] using hz
    have hzNe : d z ≠ 0 := by
      simpa only [Function.mem_support] using hzSupport
    have hzNonneg : 0 ≤ d z :=
      MeromorphicOn.AnalyticOnNhd.divisor_nonneg hanalytic z
    omega
  calc
    (S.card : ℤ) = ∑ z ∈ S, (1 : ℤ) := by simp
    _ ≤ ∑ z ∈ S, d z := Finset.sum_le_sum fun z hz => hpos z hz
    _ = ∑ᶠ z : ℂ, d z := by
      symm
      apply finsum_eq_sum_of_support_subset
      intro z hz
      change z ∈ compactDivisorSupportFinset f K hK
      exact mem_compactDivisorSupportFinset.mpr hz

noncomputable def levinsonMontgomeryZetaTopCrossingFinset
    (t : ℝ) : Finset ℝ :=
  (compactDivisorSupportFinset
    (levinsonMontgomeryZetaTopSymm t)
    (Metric.closedBall levinsonMontgomeryJensenCenter
      levinsonMontgomeryJensenInnerRadius)
    (isCompact_closedBall levinsonMontgomeryJensenCenter
      levinsonMontgomeryJensenInnerRadius)).image Complex.re

noncomputable def levinsonMontgomeryZetaDerivTopCrossingFinset
    (t : ℝ) : Finset ℝ :=
  (compactDivisorSupportFinset
    (levinsonMontgomeryZetaDerivTopSymm t)
    (Metric.closedBall levinsonMontgomeryJensenCenter
      levinsonMontgomeryJensenInnerRadius)
    (isCompact_closedBall levinsonMontgomeryJensenCenter
      levinsonMontgomeryJensenInnerRadius)).image Complex.re

theorem levinsonMontgomeryZetaTop_crossing_mem_crossingFinset
    {t x : ℝ} (ht : 23 ≤ t) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hzero : (riemannZeta (x + t * I)).re = 0) :
    x ∈ levinsonMontgomeryZetaTopCrossingFinset t := by
  apply Finset.mem_image.mpr
  refine ⟨(x : ℂ), ?_, by simp⟩
  rw [mem_compactDivisorSupportFinset]
  exact levinsonMontgomeryZetaTop_crossing_mem_divisorSupport ht hx hzero

theorem levinsonMontgomeryZetaDerivTop_crossing_mem_crossingFinset
    {t x : ℝ} (ht : 23 ≤ t) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hzero :
      (levinsonMontgomeryDerivPhase t *
        deriv riemannZeta (x + t * I)).re = 0) :
    x ∈ levinsonMontgomeryZetaDerivTopCrossingFinset t := by
  apply Finset.mem_image.mpr
  refine ⟨(x : ℂ), ?_, by simp⟩
  rw [mem_compactDivisorSupportFinset]
  exact
    levinsonMontgomeryZetaDerivTop_crossing_mem_divisorSupport ht hx hzero

theorem zetaTopCrossingFinset_card_le_divisorSum
    (t : ℝ) (ht : 23 ≤ t) :
    ((levinsonMontgomeryZetaTopCrossingFinset t).card : ℤ) ≤
      ∑ᶠ z : ℂ,
        MeromorphicOn.divisor (levinsonMontgomeryZetaTopSymm t)
          (Metric.closedBall levinsonMontgomeryJensenCenter
            levinsonMontgomeryJensenInnerRadius) z := by
  calc
    ((levinsonMontgomeryZetaTopCrossingFinset t).card : ℤ) ≤
        ((compactDivisorSupportFinset
          (levinsonMontgomeryZetaTopSymm t)
          (Metric.closedBall levinsonMontgomeryJensenCenter
            levinsonMontgomeryJensenInnerRadius)
          (isCompact_closedBall levinsonMontgomeryJensenCenter
            levinsonMontgomeryJensenInnerRadius)).card : ℤ) := by
      exact_mod_cast Finset.card_image_le
    _ ≤ ∑ᶠ z : ℂ,
        MeromorphicOn.divisor (levinsonMontgomeryZetaTopSymm t)
          (Metric.closedBall levinsonMontgomeryJensenCenter
            levinsonMontgomeryJensenInnerRadius) z := by
      apply compactDivisorSupportFinset_card_le_finsum
        (isCompact_closedBall levinsonMontgomeryJensenCenter
          levinsonMontgomeryJensenInnerRadius)
      exact
        (analyticOnNhd_levinsonMontgomeryZetaTopSymm
          (by rw [abs_of_nonneg (by linarith : 0 ≤ t)]; linarith)).mono
          (Metric.closedBall_subset_closedBall (by
            norm_num [levinsonMontgomeryJensenInnerRadius,
              levinsonMontgomeryJensenOuterRadius]))

theorem zetaDerivTopCrossingFinset_card_le_divisorSum
    (t : ℝ) (ht : 23 ≤ t) :
    ((levinsonMontgomeryZetaDerivTopCrossingFinset t).card : ℤ) ≤
      ∑ᶠ z : ℂ,
        MeromorphicOn.divisor (levinsonMontgomeryZetaDerivTopSymm t)
          (Metric.closedBall levinsonMontgomeryJensenCenter
            levinsonMontgomeryJensenInnerRadius) z := by
  calc
    ((levinsonMontgomeryZetaDerivTopCrossingFinset t).card : ℤ) ≤
        ((compactDivisorSupportFinset
          (levinsonMontgomeryZetaDerivTopSymm t)
          (Metric.closedBall levinsonMontgomeryJensenCenter
            levinsonMontgomeryJensenInnerRadius)
          (isCompact_closedBall levinsonMontgomeryJensenCenter
            levinsonMontgomeryJensenInnerRadius)).card : ℤ) := by
      exact_mod_cast Finset.card_image_le
    _ ≤ ∑ᶠ z : ℂ,
        MeromorphicOn.divisor (levinsonMontgomeryZetaDerivTopSymm t)
          (Metric.closedBall levinsonMontgomeryJensenCenter
            levinsonMontgomeryJensenInnerRadius) z := by
      apply compactDivisorSupportFinset_card_le_finsum
        (isCompact_closedBall levinsonMontgomeryJensenCenter
          levinsonMontgomeryJensenInnerRadius)
      exact
        (analyticOnNhd_levinsonMontgomeryZetaDerivTopSymm
          (by rw [abs_of_nonneg (by linarith : 0 ≤ t)]; linarith)).mono
          (Metric.closedBall_subset_closedBall (by
            norm_num [levinsonMontgomeryJensenInnerRadius,
              levinsonMontgomeryJensenOuterRadius]))

theorem hasDerivAt_riemannZeta_top
    {t sigma : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun x : ℝ => riemannZeta (x + t * I))
      (deriv riemannZeta (sigma + t * I)) sigma := by
  have hs : (sigma : ℂ) + t * I ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    norm_num at him
    linarith
  have houter :=
    (differentiableAt_riemannZeta hs).hasDerivAt
  have hline :
      HasDerivAt (fun x : ℝ => (x : ℂ) + t * I) 1 sigma := by
    simpa using (hasDerivAt_id sigma).ofReal_comp.add_const (t * I)
  change HasDerivAt
    (riemannZeta ∘ fun x : ℝ => (x : ℂ) + t * I) _ sigma
  simpa only [one_smul] using houter.scomp sigma hline

theorem hasDerivAt_riemannZetaDeriv_top
    {t sigma : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun x : ℝ => deriv riemannZeta (x + t * I))
      (deriv (deriv riemannZeta) (sigma + t * I)) sigma := by
  have hs : (sigma : ℂ) + t * I ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    norm_num at him
    linarith
  have houter :=
    (analyticOnNhd_deriv_riemannZeta
      ((sigma : ℂ) + t * I) hs).differentiableAt.hasDerivAt
  have hline :
      HasDerivAt (fun x : ℝ => (x : ℂ) + t * I) 1 sigma := by
    simpa using (hasDerivAt_id sigma).ofReal_comp.add_const (t * I)
  change HasDerivAt
    ((deriv riemannZeta) ∘ fun x : ℝ => (x : ℂ) + t * I) _ sigma
  simpa only [one_smul] using houter.scomp sigma hline

theorem levinsonMontgomeryDerivPhase_ne_zero (t : ℝ) :
    levinsonMontgomeryDerivPhase t ≠ 0 := by
  intro hzero
  have hnorm := norm_levinsonMontgomeryDerivPhase t
  rw [hzero, norm_zero] at hnorm
  norm_num at hnorm

/-- Before the Jensen asymptotic is used, the actual zeta top variation is bounded by the
cardinality of the projected divisor support. -/
theorem abs_im_levinsonMontgomeryZetaTopLogDeriv_le_card
    {t : ℝ} (htLarge : 23 ≤ t)
    (ht : LevinsonMontgomeryTopAdmissible t) :
    abs ((∫ sigma : ℝ in (0 : ℝ)..1,
      logDeriv riemannZeta (sigma + t * I)).im) ≤
      Real.pi *
        (((levinsonMontgomeryZetaTopCrossingFinset t).card : ℝ) + 1) := by
  have hsource :=
    abs_im_intervalIntegral_deriv_div_le_of_crossings_subset
      (g := fun sigma : ℝ => riemannZeta (sigma + t * I))
      (g' := fun sigma : ℝ => deriv riemannZeta (sigma + t * I))
      (a := (0 : ℝ)) (b := 1)
      (by norm_num)
      (fun sigma _ => hasDerivAt_riemannZeta_top ht.1)
      (by
        simpa only [logDeriv_apply] using
          intervalIntegrable_levinsonMontgomeryZetaLogDeriv_top ht)
      (fun sigma hsigma => (ht.2 sigma hsigma).1)
      (levinsonMontgomeryZetaTopCrossingFinset t)
      (fun sigma hsigma hzero =>
        levinsonMontgomeryZetaTop_crossing_mem_crossingFinset
          htLarge (Set.Ioo_subset_Icc_self hsigma) hzero)
  simpa only [logDeriv_apply] using hsource

/-- The phase-normalized derivative path has the same logarithmic derivative as `zeta'`.
Its real-part crossings are therefore charged by the derivative Jensen divisor. -/
theorem abs_im_levinsonMontgomeryZetaDerivTopLogDeriv_le_card
    {t : ℝ} (htLarge : 23 ≤ t)
    (ht : LevinsonMontgomeryTopAdmissible t) :
    abs ((∫ sigma : ℝ in (0 : ℝ)..1,
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
  have hquot : ∀ sigma : ℝ,
      g' sigma / g sigma =
        logDeriv (deriv riemannZeta) (sigma + t * I) := by
    intro sigma
    dsimp only [g, g', phase]
    rw [logDeriv_apply]
    exact mul_div_mul_left _ _ (levinsonMontgomeryDerivPhase_ne_zero t)
  have hquotInt :
      IntervalIntegrable (fun sigma => g' sigma / g sigma)
        (volume : Measure ℝ) (0 : ℝ) 1 := by
    apply
      (intervalIntegrable_levinsonMontgomeryZetaDerivLogDeriv_top
        ht).congr
    intro sigma hsigma
    exact (hquot sigma).symm
  have hsource :=
    abs_im_intervalIntegral_deriv_div_le_of_crossings_subset
      (g := g) (g' := g') (a := (0 : ℝ)) (b := 1)
      (by norm_num)
      (fun sigma _ => by
        dsimp only [g, g', phase]
        exact
          (hasDerivAt_riemannZetaDeriv_top
            (sigma := sigma) ht.1).const_mul
              (levinsonMontgomeryDerivPhase t))
      hquotInt
      (fun sigma hsigma => by
        dsimp only [g, phase]
        exact mul_ne_zero hphase (ht.2 sigma hsigma).2)
      (levinsonMontgomeryZetaDerivTopCrossingFinset t)
      (fun sigma hsigma hzero => by
        apply
          levinsonMontgomeryZetaDerivTop_crossing_mem_crossingFinset
            htLarge (Set.Ioo_subset_Icc_self hsigma)
        simpa only [g, phase] using hzero)
  calc
    abs ((∫ sigma : ℝ in (0 : ℝ)..1,
      logDeriv (deriv riemannZeta) (sigma + t * I)).im) =
        abs ((∫ sigma : ℝ in (0 : ℝ)..1,
          g' sigma / g sigma).im) := by
            congr 2
            apply intervalIntegral.integral_congr
            intro sigma hsigma
            exact (hquot sigma).symm
    _ ≤ Real.pi *
        (((levinsonMontgomeryZetaDerivTopCrossingFinset t).card : ℝ) + 1) :=
      hsource

/-- The actual zeta top-side continuous argument variation is `O(log(t+2))` at every
admissible sufficiently large height. -/
theorem exists_abs_im_levinsonMontgomeryZetaTopLogDeriv_le_log :
    ∃ C T0 : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, T0 ≤ t → LevinsonMontgomeryTopAdmissible t →
        abs ((∫ sigma : ℝ in (0 : ℝ)..1,
          logDeriv riemannZeta (sigma + t * I)).im) ≤
            C * Real.log (t + 2) := by
  obtain ⟨C, T0, hC, hJensen⟩ :=
    exists_levinsonMontgomeryZetaTopSymm_sum_divisor_le_log
  let C' : ℝ := Real.pi * (C + 1)
  let T0' : ℝ := max T0 23
  refine ⟨C', T0', ?_, ?_⟩
  · dsimp only [C']
    exact mul_nonneg Real.pi_pos.le (by linarith)
  intro t htLarge ht
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
    abs ((∫ sigma : ℝ in (0 : ℝ)..1,
      logDeriv riemannZeta (sigma + t * I)).im) ≤
        Real.pi *
          (((levinsonMontgomeryZetaTopCrossingFinset t).card : ℝ) + 1) :=
      abs_im_levinsonMontgomeryZetaTopLogDeriv_le_card htTwentyThree ht
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

/-- The actual zeta-derivative top-side continuous argument variation is `O(log(t+2))` at
every admissible sufficiently large height. -/
theorem exists_abs_im_levinsonMontgomeryZetaDerivTopLogDeriv_le_log :
    ∃ C T0 : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, T0 ≤ t → LevinsonMontgomeryTopAdmissible t →
        abs ((∫ sigma : ℝ in (0 : ℝ)..1,
          logDeriv (deriv riemannZeta) (sigma + t * I)).im) ≤
            C * Real.log (t + 2) := by
  obtain ⟨C, T0, hC, hJensen⟩ :=
    exists_levinsonMontgomeryZetaDerivTopSymm_sum_divisor_le_log
  let C' : ℝ := Real.pi * (C + 1)
  let T0' : ℝ := max T0 23
  refine ⟨C', T0', ?_, ?_⟩
  · dsimp only [C']
    exact mul_nonneg Real.pi_pos.le (by linarith)
  intro t htLarge ht
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
    abs ((∫ sigma : ℝ in (0 : ℝ)..1,
      logDeriv (deriv riemannZeta) (sigma + t * I)).im) ≤
        Real.pi *
          (((levinsonMontgomeryZetaDerivTopCrossingFinset t).card : ℝ) + 1) :=
      abs_im_levinsonMontgomeryZetaDerivTopLogDeriv_le_card htTwentyThree ht
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

/-- One pair of constants controls both actual top-side variations. -/
theorem exists_levinsonMontgomeryTopArgumentVariation_le_log :
    ∃ C T0 : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, T0 ≤ t → LevinsonMontgomeryTopAdmissible t →
        abs ((∫ sigma : ℝ in (0 : ℝ)..1,
          logDeriv riemannZeta (sigma + t * I)).im) ≤
            C * Real.log (t + 2) ∧
        abs ((∫ sigma : ℝ in (0 : ℝ)..1,
          logDeriv (deriv riemannZeta) (sigma + t * I)).im) ≤
            C * Real.log (t + 2) := by
  obtain ⟨Cz, Tz, hCz, hz⟩ :=
    exists_abs_im_levinsonMontgomeryZetaTopLogDeriv_le_log
  obtain ⟨Cd, Td, hCd, hd⟩ :=
    exists_abs_im_levinsonMontgomeryZetaDerivTopLogDeriv_le_log
  refine ⟨max Cz Cd, max Tz Td, ?_, ?_⟩
  · exact hCz.trans (le_max_left Cz Cd)
  intro t htLarge ht
  have htZ : Tz ≤ t := (le_max_left Tz Td).trans htLarge
  have htD : Td ≤ t := (le_max_right Tz Td).trans htLarge
  have hlog : 0 ≤ Real.log (t + 2) :=
    Real.log_nonneg (by linarith [ht.1])
  constructor
  · exact (hz t htZ ht).trans
      (mul_le_mul_of_nonneg_right (le_max_left Cz Cd) hlog)
  · exact (hd t htD ht).trans
      (mul_le_mul_of_nonneg_right (le_max_right Cz Cd) hlog)

/-- The two actual top-side bounds hold simultaneously at arbitrarily large common zero-free
heights. -/
theorem exists_cofinal_levinsonMontgomeryTopArgumentVariation :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ B : ℝ, ∃ t : ℝ, B < t ∧ LevinsonMontgomeryTopAdmissible t ∧
        abs ((∫ sigma : ℝ in (0 : ℝ)..1,
          logDeriv riemannZeta (sigma + t * I)).im) ≤
            C * Real.log (t + 2) ∧
        abs ((∫ sigma : ℝ in (0 : ℝ)..1,
          logDeriv (deriv riemannZeta) (sigma + t * I)).im) ≤
            C * Real.log (t + 2) := by
  obtain ⟨C, T0, hC, hbound⟩ :=
    exists_levinsonMontgomeryTopArgumentVariation_le_log
  refine ⟨C, hC, ?_⟩
  intro B
  obtain ⟨t, htLarge, ht⟩ :=
    exists_levinsonMontgomeryTopAdmissible_above (max B T0)
  refine ⟨t, (le_max_left B T0).trans_lt htLarge, ht, ?_⟩
  exact hbound t ((le_max_right B T0).trans htLarge.le) ht

/-- Aggregate certificate for the complete top-side variation campaign. -/
theorem levinsonMontgomeryTopArgumentVariation_endpoint :
    (∀ B : ℝ, ∃ t : ℝ, B < t ∧ LevinsonMontgomeryTopAdmissible t) ∧
    (∃ C T0 : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, T0 ≤ t → LevinsonMontgomeryTopAdmissible t →
        abs ((∫ sigma : ℝ in (0 : ℝ)..1,
          logDeriv riemannZeta (sigma + t * I)).im) ≤
            C * Real.log (t + 2) ∧
        abs ((∫ sigma : ℝ in (0 : ℝ)..1,
          logDeriv (deriv riemannZeta) (sigma + t * I)).im) ≤
            C * Real.log (t + 2)) := by
  exact ⟨exists_levinsonMontgomeryTopAdmissible_above,
    exists_levinsonMontgomeryTopArgumentVariation_le_log⟩

end

end LeanLab.Riemann
