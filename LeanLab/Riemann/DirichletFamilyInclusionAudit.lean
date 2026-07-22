import LeanLab.Riemann.LiReverseCriterion
import Mathlib.NumberTheory.LSeries.DirichletContinuation

set_option linter.style.header false

/-!
# Dirichlet-family inclusion audit

This module records the exact inclusion of Riemann zeta as the modulus-one Dirichlet L-function.
It also separates the valid one-way transfer from zero control of a product containing zeta from
the invalid reverse intuition that extra factors preserve the same critical-strip zero set.
-/

namespace LeanLab.Riemann

open Complex

/-- Every zero of `f` in the open critical strip lies on the critical line. -/
def criticalStripZerosOnLine (f : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, f s = 0 → InCriticalStrip s → OnCriticalLine s

theorem criticalStripZerosOnLine_congr {f g : ℂ → ℂ} (hfg : f = g) :
    criticalStripZerosOnLine f ↔ criticalStripZerosOnLine g := by
  subst g
  rfl

/-- Critical-strip zero control for Riemann zeta is exactly Mathlib's RH. -/
theorem criticalStripZerosOnLine_riemannZeta_iff :
    criticalStripZerosOnLine riemannZeta ↔ RiemannHypothesis := by
  constructor
  · intro hzeros
    rw [riemannHypothesis_iff_nontrivial_zeros_on_line]
    intro s hs
    exact hzeros s hs.1 ⟨nontrivial_zero_re_pos hs, nontrivial_zero_re_lt_one hs⟩
  · intro hRH s hsZero hsStrip
    apply (riemannHypothesis_iff_nontrivial_zeros_on_line.mp hRH) s
    refine ⟨hsZero, ?_, ?_⟩
    · rintro ⟨n, rfl⟩
      exact trivial_zero_not_inCriticalStrip n hsStrip
    · intro hsOne
      subst s
      norm_num [InCriticalStrip] at hsStrip

/-- The modulus-one Dirichlet L-function critical-strip claim is exactly RH. -/
theorem criticalStripZerosOnLine_dirichletL_modOne_iff
    (χ : DirichletCharacter ℂ 1) :
    criticalStripZerosOnLine (DirichletCharacter.LFunction χ) ↔ RiemannHypothesis := by
  simpa only [DirichletCharacter.LFunction_modOne_eq] using
    criticalStripZerosOnLine_riemannZeta_iff

/-- The family-wide critical-strip claim for all Dirichlet L-functions. -/
def allDirichletCriticalStripZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
    criticalStripZerosOnLine (DirichletCharacter.LFunction χ)

/-- A theorem for the entire Dirichlet family contains RH as its modulus-one member. -/
theorem riemannHypothesis_of_allDirichletCriticalStripZerosOnLine
    (hfamily : allDirichletCriticalStripZerosOnLine) :
    RiemannHypothesis := by
  exact (criticalStripZerosOnLine_dirichletL_modOne_iff
    (1 : DirichletCharacter ℂ 1)).1 (hfamily 1 1)

/-- Zero control for a product containing zeta implies zero control for zeta itself. -/
theorem criticalStripZerosOnLine_riemannZeta_of_mul
    (g : ℂ → ℂ)
    (hproduct : criticalStripZerosOnLine (fun s => riemannZeta s * g s)) :
    criticalStripZerosOnLine riemannZeta := by
  intro s hsZero hsStrip
  apply hproduct s
  · change riemannZeta s * g s = 0
    rw [hsZero, zero_mul]
  · exact hsStrip

/-- Any critical-strip theorem for a product having zeta as a factor implies RH. -/
theorem riemannHypothesis_of_criticalStripZerosOnLine_riemannZeta_mul
    (g : ℂ → ℂ)
    (hproduct : criticalStripZerosOnLine (fun s => riemannZeta s * g s)) :
    RiemannHypothesis := by
  exact criticalStripZerosOnLine_riemannZeta_iff.mp
    (criticalStripZerosOnLine_riemannZeta_of_mul g hproduct)

/-- An explicit extra factor can insert a critical-strip zero away from the critical line. -/
theorem not_criticalStripZerosOnLine_riemannZeta_mul_offLineFactor :
    ¬ criticalStripZerosOnLine
      (fun s => riemannZeta s * (s - (1 / 4 : ℂ))) := by
  intro hproduct
  have hline := hproduct (1 / 4 : ℂ) (by norm_num) (by norm_num [InCriticalStrip])
  norm_num [OnCriticalLine] at hline

/-- Aggregate H13 transfer audit: exact family inclusion, one-way factor transfer, and the
extra-factor obstruction are logically separate. -/
theorem dirichletFamilyInclusionAudit_endpoint :
    (∀ χ : DirichletCharacter ℂ 1,
      criticalStripZerosOnLine (DirichletCharacter.LFunction χ) ↔ RiemannHypothesis) ∧
    (allDirichletCriticalStripZerosOnLine → RiemannHypothesis) ∧
    (∀ g : ℂ → ℂ,
      criticalStripZerosOnLine (fun s => riemannZeta s * g s) → RiemannHypothesis) ∧
    ¬ criticalStripZerosOnLine
      (fun s => riemannZeta s * (s - (1 / 4 : ℂ))) := by
  exact ⟨criticalStripZerosOnLine_dirichletL_modOne_iff,
    riemannHypothesis_of_allDirichletCriticalStripZerosOnLine,
    riemannHypothesis_of_criticalStripZerosOnLine_riemannZeta_mul,
    not_criticalStripZerosOnLine_riemannZeta_mul_offLineFactor⟩

end LeanLab.Riemann
