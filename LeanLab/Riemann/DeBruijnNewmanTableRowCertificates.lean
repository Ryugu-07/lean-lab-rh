import LeanLab.Riemann.DeBruijnNewmanPolymathCriterion

set_option linter.style.header false

/-!
# Certificates for the Polymath one-fifth table row

This module begins the kernel-checked reconstruction of the three numerical certificates in the
second row of Polymath Table 1. It does not assert any finite computation. The first edge only
transports a finite-height Riemann-hypothesis statement to the exact initial zero-free region.
-/

open Complex

namespace LeanLab.Riemann

noncomputable section

/-- Every nontrivial zeta zero with positive ordinate at most `T` lies on the critical line. -/
def riemannHypothesisUpTo (T : ℝ) : Prop :=
  ∀ s : ℂ, IsNontrivialZero s → 0 < s.im → s.im ≤ T → OnCriticalLine s

/-- Full RH implies every finite-height upper-half-plane verification. -/
theorem RiemannHypothesis.riemannHypothesisUpTo
    (hRH : RiemannHypothesis) (T : ℝ) :
    riemannHypothesisUpTo T := by
  intro s hs _hsPos _hsT
  exact RiemannHypothesis.nontrivial_zero_on_line hRH hs

/-- A finite-height RH verification supplies the initial region in the Polymath criterion. The
zero-ordinate boundary is handled independently by positivity of the heat family on the imaginary
axis. -/
theorem deBruijnNewmanPolymathInitialRegionZeroFree_of_riemannHypothesisUpTo
    {t0 X y0 T : ℝ}
    (hT : X / 2 ≤ T)
    (hrad : 0 < y0 ^ 2 + 2 * t0)
    (hfinite : riemannHypothesisUpTo T) :
    deBruijnNewmanPolymathInitialRegionZeroFree t0 X y0 := by
  intro x y hx0 hxX hyLower _hyUpper
  by_cases hx : x = 0
  · subst x
    simpa using deBruijnNewmanH_mul_I_ne_zero 0 y
  · intro hzero
    let s : ℂ := (1 + I * ((x : ℂ) + (y : ℂ) * I)) / 2
    have hs : IsNontrivialZero s := by
      exact (deBruijnNewmanH_zero_iff_isNontrivialZero _).1 hzero
    have hsIm : s.im = x / 2 := by
      simp [s]
    have hsRe : s.re = (1 - y) / 2 := by
      simp [s]
      ring
    have hxPos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx)
    have hsImPos : 0 < s.im := by
      rw [hsIm]
      linarith
    have hsImLe : s.im ≤ T := by
      rw [hsIm]
      linarith
    have hsLine := hfinite s hs hsImPos hsImLe
    rw [OnCriticalLine, hsRe] at hsLine
    have hsqrtPos : 0 < Real.sqrt (y0 ^ 2 + 2 * t0) := Real.sqrt_pos.2 hrad
    have hyPos : 0 < y := hsqrtPos.trans_le hyLower
    linarith

/-- Exact Table 1 arithmetic: a finite RH verification through height `3*10^12` covers the
initial region for the second row. -/
theorem
    deBruijnNewmanPolymathInitialRegionZeroFree_table_row_of_rh_up_to_three_trillion
    (hfinite : riemannHypothesisUpTo ((3 : ℝ) * 10 ^ 12)) :
    deBruijnNewmanPolymathInitialRegionZeroFree
      ((93 : ℝ) / 500) ((5 : ℝ) * 10 ^ 12 + 194858) ((16733 : ℝ) / 100000) := by
  refine deBruijnNewmanPolymathInitialRegionZeroFree_of_riemannHypothesisUpTo
      (T := (3 : ℝ) * 10 ^ 12) ?_ ?_ hfinite
  · norm_num
  · norm_num

end

end LeanLab.Riemann
