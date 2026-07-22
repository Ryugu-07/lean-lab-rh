import LeanLab.Riemann.Basic

set_option linter.style.header false

/-!
# Finite-height promotion audit

This module gives a finite symmetric critical-strip model showing that verification through an
arbitrary finite height does not, by itself, exclude off-line points above that height.
-/

namespace LeanLab.Riemann

open Complex

/-- Every listed point through absolute ordinate `T` lies on the critical line. -/
def verifiedOnCriticalLineUpTo (zeros : Finset ℂ) (T : ℝ) : Prop :=
  ∀ rho ∈ zeros, |rho.im| ≤ T → OnCriticalLine rho

/-- A right-side off-line point placed one unit above the checked height. -/
noncomputable def finiteHeightAuditBase (T : ℝ) : ℂ :=
  ⟨1 / 4, T + 1⟩

/-- The orbit of the base point under conjugation and `rho |-> 1-rho`. -/
noncomputable def finiteHeightAuditOrbit (T : ℝ) : Finset ℂ :=
  {finiteHeightAuditBase T,
    star (finiteHeightAuditBase T),
    1 - finiteHeightAuditBase T,
    1 - star (finiteHeightAuditBase T)}

theorem finiteHeightAuditOrbit_finite (T : ℝ) :
    (finiteHeightAuditOrbit T : Set ℂ).Finite := by
  exact (finiteHeightAuditOrbit T).finite_toSet

theorem finiteHeightAuditOrbit_nonempty (T : ℝ) :
    (finiteHeightAuditOrbit T).Nonempty := by
  exact ⟨finiteHeightAuditBase T, by simp [finiteHeightAuditOrbit]⟩

theorem finiteHeightAuditOrbit_conj_closed (T : ℝ) {rho : ℂ}
    (hrho : rho ∈ finiteHeightAuditOrbit T) :
    star rho ∈ finiteHeightAuditOrbit T := by
  simp only [finiteHeightAuditOrbit, Finset.mem_insert, Finset.mem_singleton] at hrho ⊢
  rcases hrho with rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl (by simp)
  · exact Or.inr (Or.inr (Or.inr (by simp)))
  · exact Or.inr (Or.inr (Or.inl (by simp)))

theorem finiteHeightAuditOrbit_one_sub_closed (T : ℝ) {rho : ℂ}
    (hrho : rho ∈ finiteHeightAuditOrbit T) :
    1 - rho ∈ finiteHeightAuditOrbit T := by
  simp only [finiteHeightAuditOrbit, Finset.mem_insert, Finset.mem_singleton] at hrho ⊢
  rcases hrho with rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))
  · exact Or.inl (by ring)
  · exact Or.inr (Or.inl (by ring))

theorem finiteHeightAuditOrbit_inCriticalStrip (T : ℝ) {rho : ℂ}
    (hrho : rho ∈ finiteHeightAuditOrbit T) :
    InCriticalStrip rho := by
  simp only [finiteHeightAuditOrbit, Finset.mem_insert, Finset.mem_singleton] at hrho
  rcases hrho with rfl | rfl | rfl | rfl
  all_goals norm_num [finiteHeightAuditBase, InCriticalStrip]

theorem finiteHeightAuditOrbit_abs_im {T : ℝ} (hT : 0 ≤ T) {rho : ℂ}
    (hrho : rho ∈ finiteHeightAuditOrbit T) :
    |rho.im| = T + 1 := by
  have hT1 : 0 ≤ T + 1 := by linarith
  simp only [finiteHeightAuditOrbit, Finset.mem_insert, Finset.mem_singleton] at hrho
  rcases hrho with rfl | rfl | rfl | rfl
  · simp [finiteHeightAuditBase, abs_of_nonneg hT1]
  · change |-(T + 1)| = T + 1
    rw [abs_neg, abs_of_nonneg hT1]
  · simp only [Complex.sub_im, Complex.one_im, finiteHeightAuditBase]
    rw [zero_sub, abs_neg, abs_of_nonneg hT1]
  · simp [finiteHeightAuditBase, abs_of_nonneg hT1]

theorem finiteHeightAuditOrbit_verified {T : ℝ} (hT : 0 ≤ T) :
    verifiedOnCriticalLineUpTo (finiteHeightAuditOrbit T) T := by
  intro rho hrho hheight
  have habs := finiteHeightAuditOrbit_abs_im hT hrho
  rw [habs] at hheight
  exfalso
  linarith

theorem finiteHeightAuditOrbit_has_high_offLine {T : ℝ} (hT : 0 ≤ T) :
    ∃ rho ∈ finiteHeightAuditOrbit T,
      ¬ OnCriticalLine rho ∧ T < |rho.im| := by
  refine ⟨finiteHeightAuditBase T, by simp [finiteHeightAuditOrbit], ?_, ?_⟩
  · norm_num [finiteHeightAuditBase, OnCriticalLine]
  · have hT1 : 0 ≤ T + 1 := by linarith
    simp [finiteHeightAuditBase, abs_of_nonneg hT1]

/-- At every nonnegative finite height, all the zeta-like geometric symmetries and all checked
points can coexist with an unchecked off-line point above the certificate. -/
theorem exists_finiteHeightAuditOrbit (T : ℝ) (hT : 0 ≤ T) :
    ∃ zeros : Finset ℂ,
      (zeros : Set ℂ).Finite ∧
      zeros.Nonempty ∧
      (∀ rho ∈ zeros, star rho ∈ zeros) ∧
      (∀ rho ∈ zeros, 1 - rho ∈ zeros) ∧
      (∀ rho ∈ zeros, InCriticalStrip rho) ∧
      verifiedOnCriticalLineUpTo zeros T ∧
      ∃ rho ∈ zeros, ¬ OnCriticalLine rho ∧ T < |rho.im| := by
  exact ⟨finiteHeightAuditOrbit T,
    finiteHeightAuditOrbit_finite T,
    finiteHeightAuditOrbit_nonempty T,
    fun _ hrho => finiteHeightAuditOrbit_conj_closed T hrho,
    fun _ hrho => finiteHeightAuditOrbit_one_sub_closed T hrho,
    fun _ hrho => finiteHeightAuditOrbit_inCriticalStrip T hrho,
    finiteHeightAuditOrbit_verified hT,
    finiteHeightAuditOrbit_has_high_offLine hT⟩

theorem finiteHeightPromotionAudit_endpoint :
    ∀ T : ℝ, 0 ≤ T →
      ∃ zeros : Finset ℂ,
        (zeros : Set ℂ).Finite ∧
        zeros.Nonempty ∧
        (∀ rho ∈ zeros, star rho ∈ zeros) ∧
        (∀ rho ∈ zeros, 1 - rho ∈ zeros) ∧
        (∀ rho ∈ zeros, InCriticalStrip rho) ∧
        verifiedOnCriticalLineUpTo zeros T ∧
        ∃ rho ∈ zeros, ¬ OnCriticalLine rho ∧ T < |rho.im| := by
  exact exists_finiteHeightAuditOrbit

end LeanLab.Riemann
