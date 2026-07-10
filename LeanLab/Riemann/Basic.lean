import Mathlib

set_option linter.style.header false

/-!
# First scaffolding for the Riemann Hypothesis

This file records only small statements that are already justified by mathlib.
It is a proof-engineering boundary for RH work: no speculative step belongs
here unless Lean checks it without proof placeholders.
-/

namespace LeanLab.Riemann

open Complex

/-- A point is a zero of the Riemann zeta function. -/
def IsZetaZero (s : ℂ) : Prop :=
  riemannZeta s = 0

/-- The trivial zeros are the negative even integers in mathlib's indexing. -/
def IsTrivialZeroPoint (s : ℂ) : Prop :=
  ∃ n : ℕ, s = -2 * (n + 1)

/-- The local working predicate for nontrivial zeta zeros. -/
def IsNontrivialZero (s : ℂ) : Prop :=
  IsZetaZero s ∧ ¬ IsTrivialZeroPoint s ∧ s ≠ 1

/-- The critical line `re s = 1 / 2`. -/
def OnCriticalLine (s : ℂ) : Prop :=
  s.re = 1 / 2

/-- The open critical strip. -/
def InCriticalStrip (s : ℂ) : Prop :=
  0 < s.re ∧ s.re < 1

theorem isZetaZero_iff_mem_riemannZetaZeros {s : ℂ} :
    IsZetaZero s ↔ s ∈ riemannZetaZeros := by
  exact (mem_riemannZetaZeros (z := s)).symm

theorem trivial_zero_is_zeta_zero (n : ℕ) :
    IsZetaZero (-2 * (n + 1) : ℂ) := by
  exact riemannZeta_neg_two_mul_nat_add_one n

theorem trivial_zero_re_lt_zero (n : ℕ) :
    ((-2 * (n + 1) : ℂ).re) < 0 := by
  norm_num
  positivity

theorem trivial_zero_not_inCriticalStrip (n : ℕ) :
    ¬ InCriticalStrip (-2 * (n + 1) : ℂ) := by
  intro hstrip
  exact (not_lt_of_ge (le_of_lt (trivial_zero_re_lt_zero n))) hstrip.1

theorem zeta_zero_not_in_closed_right_half_plane {s : ℂ} (hs : 1 ≤ s.re) :
    ¬ IsZetaZero s := by
  exact riemannZeta_ne_zero_of_one_le_re (s := s) hs

theorem zeta_zero_re_lt_one {s : ℂ} (hz : IsZetaZero s) :
    s.re < 1 := by
  by_contra h
  exact zeta_zero_not_in_closed_right_half_plane (s := s) (le_of_not_gt h) hz

theorem nontrivial_zero_re_lt_one {s : ℂ} (hz : IsNontrivialZero s) :
    s.re < 1 := by
  exact zeta_zero_re_lt_one hz.1

theorem riemannHypothesis_iff_nontrivial_zeros_on_line :
    RiemannHypothesis ↔ ∀ s : ℂ, IsNontrivialZero s → OnCriticalLine s := by
  constructor
  · intro hRH s hs
    exact hRH s hs.1 hs.2.1 hs.2.2
  · intro h s hz htriv hne_one
    exact h s ⟨hz, htriv, hne_one⟩

theorem RiemannHypothesis.nontrivial_zero_on_line
    (hRH : RiemannHypothesis) {s : ℂ} (hs : IsNontrivialZero s) :
    OnCriticalLine s := by
  exact (riemannHypothesis_iff_nontrivial_zeros_on_line.mp hRH) s hs

theorem RiemannHypothesis.nontrivial_zero_inCriticalStrip
    (hRH : RiemannHypothesis) {s : ℂ} (hs : IsNontrivialZero s) :
    InCriticalStrip s := by
  have hline : OnCriticalLine s := RiemannHypothesis.nontrivial_zero_on_line hRH hs
  rw [OnCriticalLine] at hline
  rw [InCriticalStrip]
  constructor
  · rw [hline]
    norm_num
  · rw [hline]
    norm_num

theorem RiemannHypothesis.zero_on_line_or_trivial
    (hRH : RiemannHypothesis) {s : ℂ} (hz : IsZetaZero s) :
    OnCriticalLine s ∨ IsTrivialZeroPoint s := by
  by_cases htriv : IsTrivialZeroPoint s
  · exact Or.inr htriv
  · left
    apply hRH s hz htriv
    intro hs_one
    have hone : riemannZeta (1 : ℂ) ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re (s := (1 : ℂ)) (by norm_num)
    exact hone (by simpa [IsZetaZero, hs_one] using hz)

/-- Under RH, zeta has no zero strictly to the right of any vertical line
whose real part is at least `1 / 2`. This is the zero-free hypothesis used
when applying the Balazard-Saias estimate in the Baez-Duarte route. -/
theorem RiemannHypothesis.riemannZeta_ne_zero_of_half_le_lt_re
    (hRH : RiemannHypothesis) {α : ℝ} (hα : 1 / 2 ≤ α)
    {s : ℂ} (hs : α < s.re) :
    riemannZeta s ≠ 0 := by
  intro hz
  rcases RiemannHypothesis.zero_on_line_or_trivial hRH (hz := hz) with hline | htriv
  · rw [OnCriticalLine] at hline
    linarith
  · rcases htriv with ⟨n, rfl⟩
    have hneg := trivial_zero_re_lt_zero n
    linarith

theorem riemannZetaZeros_closed :
    IsClosed riemannZetaZeros :=
  isClosed_riemannZetaZeros

theorem riemannZetaZeros_discrete :
    IsDiscrete riemannZetaZeros :=
  isDiscrete_riemannZetaZeros

theorem compact_inter_riemannZetaZeros_finite {S : Set ℂ} (hS : IsCompact S) :
    (S ∩ riemannZetaZeros).Finite :=
  IsCompact.inter_riemannZetaZeros_finite hS

theorem zeta_eq_dirichlet_series_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = ∑' n : ℕ, 1 / (n : ℂ) ^ s :=
  zeta_eq_tsum_one_div_nat_cpow hs

end LeanLab.Riemann
