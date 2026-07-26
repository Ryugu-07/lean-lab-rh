import LeanLab.Riemann.WeilCompactPositivityCriterion

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Hardy's real critical-line xi coordinate

This module isolates the exact real sign consumer at the entrance to Hardy's critical-line
method. It does not assert that the required sign changes occur.
-/

open Complex Set

namespace LeanLab.Riemann

noncomputable section

/-- The literal point `1 / 2 + i t` on the critical line. -/
def hardyCriticalLinePoint (t : ℝ) : ℂ :=
  (1 / 2 : ℂ) + Complex.I * t

@[simp] theorem hardyCriticalLinePoint_re (t : ℝ) :
    (hardyCriticalLinePoint t).re = 1 / 2 := by
  simp [hardyCriticalLinePoint]

@[simp] theorem hardyCriticalLinePoint_im (t : ℝ) :
    (hardyCriticalLinePoint t).im = t := by
  simp [hardyCriticalLinePoint]

theorem hardyCriticalLinePoint_conj (t : ℝ) :
    (starRingEnd ℂ) (hardyCriticalLinePoint t) =
      1 - hardyCriticalLinePoint t := by
  apply Complex.ext
  · norm_num [hardyCriticalLinePoint]
  · simp [hardyCriticalLinePoint]

theorem hardyCriticalLinePoint_neg (t : ℝ) :
    hardyCriticalLinePoint (-t) = 1 - hardyCriticalLinePoint t := by
  apply Complex.ext
  · norm_num [hardyCriticalLinePoint]
  · simp [hardyCriticalLinePoint]

theorem onCriticalLine_hardyCriticalLinePoint (t : ℝ) :
    OnCriticalLine (hardyCriticalLinePoint t) := by
  simp [OnCriticalLine]

/-- The project xi function restricted to the critical line. -/
def hardyCriticalXi (t : ℝ) : ℂ :=
  riemannXi (hardyCriticalLinePoint t)

/-- The real coordinate of the project xi function on the critical line. -/
def hardyXi (t : ℝ) : ℝ :=
  (hardyCriticalXi t).re

theorem star_hardyCriticalXi (t : ℝ) :
    (starRingEnd ℂ) (hardyCriticalXi t) = hardyCriticalXi t := by
  rw [hardyCriticalXi, ← riemannXi_conj, hardyCriticalLinePoint_conj,
    riemannXi_one_sub]

theorem hardyCriticalXi_eq_ofReal (t : ℝ) :
    hardyCriticalXi t = (hardyXi t : ℂ) := by
  exact (Complex.conj_eq_iff_re.mp (star_hardyCriticalXi t)).symm

theorem hardyCriticalXi_neg (t : ℝ) :
    hardyCriticalXi (-t) = hardyCriticalXi t := by
  simp only [hardyCriticalXi]
  rw [hardyCriticalLinePoint_neg, riemannXi_one_sub]

theorem hardyXi_even :
    Function.Even hardyXi := by
  intro t
  change (hardyCriticalXi (-t)).re = (hardyCriticalXi t).re
  rw [hardyCriticalXi_neg]

theorem continuous_hardyCriticalLinePoint :
    Continuous hardyCriticalLinePoint := by
  unfold hardyCriticalLinePoint
  fun_prop

theorem continuous_hardyCriticalXi :
    Continuous hardyCriticalXi :=
  differentiable_riemannXi.continuous.comp continuous_hardyCriticalLinePoint

theorem continuous_hardyXi :
    Continuous hardyXi :=
  Complex.continuous_re.comp continuous_hardyCriticalXi

theorem hardyXi_eq_zero_iff_hardyCriticalXi_eq_zero (t : ℝ) :
    hardyXi t = 0 ↔ hardyCriticalXi t = 0 := by
  rw [hardyCriticalXi_eq_ofReal]
  simp

theorem hardyXi_eq_zero_iff_isNontrivialZero (t : ℝ) :
    hardyXi t = 0 ↔ IsNontrivialZero (hardyCriticalLinePoint t) := by
  rw [hardyXi_eq_zero_iff_hardyCriticalXi_eq_zero, hardyCriticalXi,
    ← isNontrivialZero_iff_riemannXi_eq_zero]

/-- The two possible endpoint-sign orientations for a closed interval. -/
def HardyXiBracketsZero (a b : ℝ) : Prop :=
  (hardyXi a ≤ 0 ∧ 0 ≤ hardyXi b) ∨
    (hardyXi b ≤ 0 ∧ 0 ≤ hardyXi a)

theorem exists_hardyXi_zero_of_sign_change_forward
    {a b : ℝ} (hab : a ≤ b)
    (ha : hardyXi a ≤ 0) (hb : 0 ≤ hardyXi b) :
    ∃ t ∈ Icc a b,
      IsNontrivialZero (hardyCriticalLinePoint t) ∧
        OnCriticalLine (hardyCriticalLinePoint t) := by
  obtain ⟨t, ht, hzero⟩ :=
    intermediate_value_Icc hab continuous_hardyXi.continuousOn ⟨ha, hb⟩
  refine ⟨t, ht, (hardyXi_eq_zero_iff_isNontrivialZero t).mp ?_, ?_⟩
  · exact hzero
  · exact onCriticalLine_hardyCriticalLinePoint t

theorem exists_hardyXi_zero_of_sign_change_reverse
    {a b : ℝ} (hab : a ≤ b)
    (hb : hardyXi b ≤ 0) (ha : 0 ≤ hardyXi a) :
    ∃ t ∈ Icc a b,
      IsNontrivialZero (hardyCriticalLinePoint t) ∧
        OnCriticalLine (hardyCriticalLinePoint t) := by
  obtain ⟨t, ht, hzero⟩ :=
    intermediate_value_Icc' hab continuous_hardyXi.continuousOn ⟨hb, ha⟩
  refine ⟨t, ht, (hardyXi_eq_zero_iff_isNontrivialZero t).mp ?_, ?_⟩
  · exact hzero
  · exact onCriticalLine_hardyCriticalLinePoint t

theorem exists_hardyXi_zero_of_bracket
    {a b : ℝ} (hab : a ≤ b) (hbracket : HardyXiBracketsZero a b) :
    ∃ t ∈ Icc a b,
      IsNontrivialZero (hardyCriticalLinePoint t) ∧
        OnCriticalLine (hardyCriticalLinePoint t) := by
  rcases hbracket with hforward | hreverse
  · exact exists_hardyXi_zero_of_sign_change_forward hab hforward.1 hforward.2
  · exact exists_hardyXi_zero_of_sign_change_reverse hab hreverse.1 hreverse.2

/-- Adjacent intervals in `u` are ordered and bracket a zero of the real xi coordinate. -/
def HardyXiAlternatingIntervalSequence (u : ℕ → ℝ) : Prop :=
  ∀ n, u n ≤ u (n + 1) ∧ HardyXiBracketsZero (u n) (u (n + 1))

theorem exists_hardyXi_zero_in_each_alternating_interval
    {u : ℕ → ℝ} (hu : HardyXiAlternatingIntervalSequence u) :
    ∀ n, ∃ t ∈ Icc (u n) (u (n + 1)),
      IsNontrivialZero (hardyCriticalLinePoint t) ∧
        OnCriticalLine (hardyCriticalLinePoint t) := by
  intro n
  exact exists_hardyXi_zero_of_bracket (hu n).1 (hu n).2

/-- The complete xi-specific real-sign bridge at the entrance to Hardy's method. -/
structure HardyCriticalLineSignCertificate : Prop where
  realCoordinate :
    ∀ t, hardyCriticalXi t = (hardyXi t : ℂ)
  evenCoordinate : Function.Even hardyXi
  continuousCoordinate : Continuous hardyXi
  zeroDictionary :
    ∀ t, hardyXi t = 0 ↔ IsNontrivialZero (hardyCriticalLinePoint t)
  intervalConsumer :
    ∀ {a b}, a ≤ b → HardyXiBracketsZero a b →
      ∃ t ∈ Icc a b,
        IsNontrivialZero (hardyCriticalLinePoint t) ∧
          OnCriticalLine (hardyCriticalLinePoint t)
  sequenceConsumer :
    ∀ {u : ℕ → ℝ}, HardyXiAlternatingIntervalSequence u →
      ∀ n, ∃ t ∈ Icc (u n) (u (n + 1)),
        IsNontrivialZero (hardyCriticalLinePoint t) ∧
          OnCriticalLine (hardyCriticalLinePoint t)

theorem hardyCriticalLineSign_endpoint :
    HardyCriticalLineSignCertificate where
  realCoordinate := hardyCriticalXi_eq_ofReal
  evenCoordinate := hardyXi_even
  continuousCoordinate := continuous_hardyXi
  zeroDictionary := hardyXi_eq_zero_iff_isNontrivialZero
  intervalConsumer := exists_hardyXi_zero_of_bracket
  sequenceConsumer := exists_hardyXi_zero_in_each_alternating_interval

end

end LeanLab.Riemann
