import Mathlib

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Half-isolated bow geometry audit

This module isolates the finite geometry in the Maynard--Pratt half-isolated-zero method. The
finite sets below are not asserted to be zero sets of the Riemann zeta function.
-/

namespace LeanLab.Riemann

noncomputable section

/-- The local disjunction in the source definition of a half-isolated zero. -/
def halfIsolatedIn
    (zeros : Set ℂ) (nearRadius similarWidth leftGap : ℝ) (rho0 : ℂ) : Prop :=
  ∀ rho, rho ∈ zeros → dist rho rho0 ≤ nearRadius →
    (|rho.re - rho0.re| ≤ similarWidth ∧ rho0.im ≤ rho.im) ∨
      rho.re ≤ rho0.re - leftGap

/-- Reflection across the critical line, preserving the ordinate. -/
def criticalLineReflect (rho : ℂ) : ℂ :=
  1 - (starRingEnd ℂ) rho

theorem criticalLineReflect_re (rho : ℂ) :
    (criticalLineReflect rho).re = 1 - rho.re := by
  simp [criticalLineReflect]

theorem criticalLineReflect_im (rho : ℂ) :
    (criticalLineReflect rho).im = rho.im := by
  simp [criticalLineReflect]

theorem criticalLineReflect_involutive : Function.Involutive criticalLineReflect := by
  intro rho
  apply Complex.ext
  · simp [criticalLineReflect_re]
  · simp [criticalLineReflect_im]

/-- Discrete vertical lines plus a bottom point give the source half-isolation disjunction. -/
theorem halfIsolatedIn_of_rightmost_bottom_and_verticalGap
    {zeros : Set ℂ} {nearRadius similarWidth leftGap : ℝ} {rho0 : ℂ}
    (hsimilar : 0 ≤ similarWidth)
    (hverticalGap :
      ∀ rho ∈ zeros, rho.re = rho0.re ∨ rho.re ≤ rho0.re - leftGap)
    (hbottom :
      ∀ rho ∈ zeros, rho.re = rho0.re → rho0.im ≤ rho.im) :
    halfIsolatedIn zeros nearRadius similarWidth leftGap rho0 := by
  intro rho hrho _hnear
  rcases hverticalGap rho hrho with hre | hleft
  · left
    constructor
    · rw [hre, sub_self, abs_zero]
      exact hsimilar
    · exact hbottom rho hrho hre
  · exact Or.inr hleft

/-- The bottom point of a three-point finite bow. -/
def finiteBowBase : ℂ :=
  (1 / 2 : ℝ)

/-- The right off-line point of a three-point finite bow. -/
def finiteBowRight (step rise : ℝ) : ℂ :=
  ((1 / 2 + step : ℝ) : ℂ) + (rise : ℂ) * Complex.I

/-- The reflected left point of the finite bow. -/
def finiteBowLeft (step rise : ℝ) : ℂ :=
  criticalLineReflect (finiteBowRight step rise)

/-- A minimal local bow and its critical-line reflection. -/
def finiteBow (step rise : ℝ) : Set ℂ :=
  {finiteBowBase, finiteBowRight step rise, finiteBowLeft step rise}

theorem finiteBow_finite (step rise : ℝ) : (finiteBow step rise).Finite := by
  simp [finiteBow]

theorem criticalLineReflect_finiteBowBase :
    criticalLineReflect finiteBowBase = finiteBowBase := by
  apply Complex.ext <;> norm_num [criticalLineReflect, finiteBowBase]

theorem criticalLineReflect_finiteBowRight (step rise : ℝ) :
    criticalLineReflect (finiteBowRight step rise) = finiteBowLeft step rise := by
  rfl

theorem criticalLineReflect_finiteBowLeft (step rise : ℝ) :
    criticalLineReflect (finiteBowLeft step rise) = finiteBowRight step rise := by
  exact criticalLineReflect_involutive (finiteBowRight step rise)

theorem finiteBow_reflect_mem {step rise : ℝ} {rho : ℂ}
    (hrho : rho ∈ finiteBow step rise) :
    criticalLineReflect rho ∈ finiteBow step rise := by
  simp only [finiteBow, Set.mem_insert_iff, Set.mem_singleton_iff] at hrho ⊢
  rcases hrho with rfl | rfl | rfl
  · exact Or.inl criticalLineReflect_finiteBowBase
  · exact Or.inr (Or.inr (criticalLineReflect_finiteBowRight step rise))
  · exact Or.inr (Or.inl (criticalLineReflect_finiteBowLeft step rise))

theorem finiteBow_is_reflectionInvariant (step rise : ℝ) (rho : ℂ) :
    rho ∈ finiteBow step rise ↔ criticalLineReflect rho ∈ finiteBow step rise := by
  constructor
  · exact finiteBow_reflect_mem
  · intro hreflect
    have hreflect' := finiteBow_reflect_mem hreflect
    simpa only [criticalLineReflect_involutive rho] using hreflect'

theorem finiteBowBase_mem (step rise : ℝ) :
    finiteBowBase ∈ finiteBow step rise := by
  simp [finiteBow]

theorem finiteBowRight_mem (step rise : ℝ) :
    finiteBowRight step rise ∈ finiteBow step rise := by
  simp [finiteBow]

theorem finiteBowLeft_mem (step rise : ℝ) :
    finiteBowLeft step rise ∈ finiteBow step rise := by
  simp [finiteBow]

theorem finiteBowRight_re (step rise : ℝ) :
    (finiteBowRight step rise).re = 1 / 2 + step := by
  simp [finiteBowRight]

theorem finiteBowRight_im (step rise : ℝ) :
    (finiteBowRight step rise).im = rise := by
  simp [finiteBowRight]

theorem finiteBowBase_re : finiteBowBase.re = 1 / 2 := by
  norm_num [finiteBowBase]

theorem finiteBowBase_im : finiteBowBase.im = 0 := by
  norm_num [finiteBowBase]

theorem finiteBowLeft_re (step rise : ℝ) :
    (finiteBowLeft step rise).re = 1 / 2 - step := by
  rw [finiteBowLeft, criticalLineReflect_re, finiteBowRight_re]
  ring

theorem finiteBowRight_offLine {step rise : ℝ} (hstep : 0 < step) :
    (1 / 2 : ℝ) < (finiteBowRight step rise).re := by
  rw [finiteBowRight_re]
  linarith

theorem finiteBow_blocker_is_lower {step rise : ℝ} (hrise : 0 < rise) :
    finiteBowBase.im < (finiteBowRight step rise).im := by
  rw [finiteBowBase_im, finiteBowRight_im]
  exact hrise

theorem finiteBow_blocker_intermediate_displacement
    {step rise similarWidth leftGap : ℝ}
    (hstep : 0 < step) (hsmall : similarWidth < step) (hlarge : step < leftGap) :
    similarWidth < |finiteBowBase.re - (finiteBowRight step rise).re| ∧
      (finiteBowRight step rise).re - leftGap < finiteBowBase.re := by
  rw [finiteBowBase_re, finiteBowRight_re]
  constructor
  · rw [show (1 / 2 : ℝ) - (1 / 2 + step) = -step by ring]
    simpa [abs_of_pos hstep] using hsmall
  · linarith

/-- A nearby lower point at an intermediate real displacement defeats both source branches. -/
theorem not_halfIsolatedIn_of_intermediate_lower_blocker
    {zeros : Set ℂ} {nearRadius similarWidth leftGap : ℝ} {rho0 blocker : ℂ}
    (hblocker : blocker ∈ zeros)
    (hnear : dist blocker rho0 ≤ nearRadius)
    (hlower : blocker.im < rho0.im)
    (hnotLeft : rho0.re - leftGap < blocker.re) :
    ¬ halfIsolatedIn zeros nearRadius similarWidth leftGap rho0 := by
  intro hisolated
  rcases hisolated blocker hblocker hnear with hsimilar | hleft
  · exact (not_le_of_gt hlower) hsimilar.2
  · exact (not_le_of_gt hnotLeft) hleft

theorem finiteBowRight_not_halfIsolated
    {step rise nearRadius similarWidth leftGap : ℝ}
    (hrise : 0 < rise)
    (hnear : dist finiteBowBase (finiteBowRight step rise) ≤ nearRadius)
    (hlarge : step < leftGap) :
    ¬ halfIsolatedIn (finiteBow step rise) nearRadius similarWidth leftGap
      (finiteBowRight step rise) := by
  apply not_halfIsolatedIn_of_intermediate_lower_blocker
    (finiteBowBase_mem step rise) hnear
  · exact finiteBow_blocker_is_lower hrise
  · rw [finiteBowBase_re, finiteBowRight_re]
    linarith

theorem finiteBow_right_point_unique
    {step rise : ℝ} (hstep : 0 < step) {rho : ℂ}
    (hrho : rho ∈ finiteBow step rise) (hoffLine : (1 / 2 : ℝ) < rho.re) :
    rho = finiteBowRight step rise := by
  simp only [finiteBow, Set.mem_insert_iff, Set.mem_singleton_iff] at hrho
  rcases hrho with rfl | rfl | rfl
  · rw [finiteBowBase_re] at hoffLine
    exact (lt_irrefl _ hoffLine).elim
  · rfl
  · rw [finiteBowLeft_re] at hoffLine
    linarith

theorem finiteBow_no_right_offLine_halfIsolated
    {step rise nearRadius similarWidth leftGap : ℝ}
    (hstep : 0 < step) (hrise : 0 < rise)
    (hnear : dist finiteBowBase (finiteBowRight step rise) ≤ nearRadius)
    (hlarge : step < leftGap) :
    ∀ rho ∈ finiteBow step rise, (1 / 2 : ℝ) < rho.re →
      ¬ halfIsolatedIn (finiteBow step rise) nearRadius similarWidth leftGap rho := by
  intro rho hrho hoffLine
  have hrhoeq := finiteBow_right_point_unique hstep hrho hoffLine
  subst rho
  exact finiteBowRight_not_halfIsolated hrise hnear hlarge

/-- A concrete nonvacuous bow with intermediate displacement `0 < 1 < 2`. -/
theorem finiteBow_concreteCounterexample :
    (finiteBow (1 : ℝ) 1).Finite ∧
    (∀ rho, rho ∈ finiteBow (1 : ℝ) 1 ↔
      criticalLineReflect rho ∈ finiteBow (1 : ℝ) 1) ∧
    (∃ rho ∈ finiteBow (1 : ℝ) 1, (1 / 2 : ℝ) < rho.re) ∧
    finiteBowBase.im < (finiteBowRight (1 : ℝ) 1).im ∧
    (0 : ℝ) < |finiteBowBase.re - (finiteBowRight (1 : ℝ) 1).re| ∧
    (finiteBowRight (1 : ℝ) 1).re - 2 < finiteBowBase.re ∧
    (∀ rho ∈ finiteBow (1 : ℝ) 1, (1 / 2 : ℝ) < rho.re →
      ¬ halfIsolatedIn (finiteBow (1 : ℝ) 1)
        (dist finiteBowBase (finiteBowRight (1 : ℝ) 1)) 0 2 rho) := by
  have hintermediate := finiteBow_blocker_intermediate_displacement
    (step := (1 : ℝ)) (rise := (1 : ℝ)) (similarWidth := 0) (leftGap := 2)
    (by norm_num) (by norm_num) (by norm_num)
  exact ⟨finiteBow_finite 1 1,
    finiteBow_is_reflectionInvariant 1 1,
    ⟨finiteBowRight 1 1, finiteBowRight_mem 1 1, finiteBowRight_offLine (by norm_num)⟩,
    finiteBow_blocker_is_lower (by norm_num),
    hintermediate.1,
    hintermediate.2,
    finiteBow_no_right_offLine_halfIsolated
      (by norm_num) (by norm_num) le_rfl (by norm_num)⟩

/-- Aggregate endpoint: vertical rigidity is sufficient, while reflection symmetry alone is not. -/
theorem halfIsolatedBowAudit_endpoint :
    (∀ (zeros : Set ℂ) (nearRadius similarWidth leftGap : ℝ) (rho0 : ℂ),
      0 ≤ similarWidth →
      (∀ rho ∈ zeros, rho.re = rho0.re ∨ rho.re ≤ rho0.re - leftGap) →
      (∀ rho ∈ zeros, rho.re = rho0.re → rho0.im ≤ rho.im) →
      halfIsolatedIn zeros nearRadius similarWidth leftGap rho0) ∧
    (∀ step rise nearRadius similarWidth leftGap : ℝ,
      0 < step → 0 < rise →
      dist finiteBowBase (finiteBowRight step rise) ≤ nearRadius →
      similarWidth < step →
      step < leftGap →
      (∀ rho, rho ∈ finiteBow step rise ↔
        criticalLineReflect rho ∈ finiteBow step rise) ∧
      (∃ rho ∈ finiteBow step rise, (1 / 2 : ℝ) < rho.re) ∧
      finiteBowBase.im < (finiteBowRight step rise).im ∧
      similarWidth < |finiteBowBase.re - (finiteBowRight step rise).re| ∧
      (finiteBowRight step rise).re - leftGap < finiteBowBase.re ∧
      (∀ rho ∈ finiteBow step rise, (1 / 2 : ℝ) < rho.re →
        ¬ halfIsolatedIn (finiteBow step rise) nearRadius similarWidth leftGap rho)) ∧
    (finiteBow (1 : ℝ) 1).Finite ∧
    (∀ rho, rho ∈ finiteBow (1 : ℝ) 1 ↔
      criticalLineReflect rho ∈ finiteBow (1 : ℝ) 1) ∧
    (∃ rho ∈ finiteBow (1 : ℝ) 1, (1 / 2 : ℝ) < rho.re) ∧
    (∀ rho ∈ finiteBow (1 : ℝ) 1, (1 / 2 : ℝ) < rho.re →
      ¬ halfIsolatedIn (finiteBow (1 : ℝ) 1)
        (dist finiteBowBase (finiteBowRight (1 : ℝ) 1)) 0 2 rho) := by
  constructor
  · exact fun _zeros _nearRadius _similarWidth _leftGap _rho0 =>
      halfIsolatedIn_of_rightmost_bottom_and_verticalGap
  · constructor
    · intro step rise nearRadius similarWidth leftGap hstep hrise hnear hsmall hlarge
      have hintermediate := finiteBow_blocker_intermediate_displacement
        (rise := rise) hstep hsmall hlarge
      exact ⟨finiteBow_is_reflectionInvariant step rise,
        ⟨finiteBowRight step rise, finiteBowRight_mem step rise,
          finiteBowRight_offLine hstep⟩,
        finiteBow_blocker_is_lower hrise,
        hintermediate.1,
        hintermediate.2,
        finiteBow_no_right_offLine_halfIsolated hstep hrise hnear hlarge⟩
    · exact ⟨finiteBow_concreteCounterexample.1,
        finiteBow_concreteCounterexample.2.1,
        finiteBow_concreteCounterexample.2.2.1,
        finiteBow_concreteCounterexample.2.2.2.2.2.2⟩

end

end LeanLab.Riemann
