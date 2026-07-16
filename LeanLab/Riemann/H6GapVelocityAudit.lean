import LeanLab.Riemann.DeBruijnNewmanDynamics

set_option linter.style.header false

/-!
# Sharpness audit for the adjacent-gap velocity bound

This module gives an exact quadratic backward-heat family whose two real simple zeros collide after
backward time equal to their terminal squared gap divided by eight. It shows that the generic bound
`(gap^2)' <= 8` cannot by itself provide a height-uniform continuation interval. The model is not
the de Bruijn-Newman theta family and does not address RH.
-/

open Complex

namespace LeanLab.Riemann

noncomputable section

/-- A quadratic family satisfying the same source convention `partial_t H = -partial_z^2 H`. -/
def h6GapAuditHeatPolynomial (b epsilon t z : ℂ) : ℂ :=
  z ^ 2 - (2 * t + epsilon ^ 2 / 4 - 2 * b)

/-- The collision time selected so that the terminal gap at time `b` is `epsilon`. -/
def h6GapAuditCollisionTime (b epsilon : ℂ) : ℂ :=
  b - epsilon ^ 2 / 8

theorem hasDerivAt_h6GapAuditHeatPolynomial_time (b epsilon t z : ℂ) :
    HasDerivAt (fun tau : ℂ ↦ h6GapAuditHeatPolynomial b epsilon tau z) (-2) t := by
  convert! (hasDerivAt_const t (z ^ 2)).sub
    ((((hasDerivAt_id t).mul_const (2 : ℂ)).add_const
      (epsilon ^ 2 / 4)).sub_const (2 * b)) using 1
  · funext tau
    simp only [h6GapAuditHeatPolynomial, Function.id_def, Pi.sub_apply]
    ring
  · ring

theorem hasDerivAt_h6GapAuditHeatPolynomial_spatial (b epsilon t z : ℂ) :
    HasDerivAt (h6GapAuditHeatPolynomial b epsilon t) (2 * z) z := by
  convert! ((hasDerivAt_id z).pow 2).sub_const
    (2 * t + epsilon ^ 2 / 4 - 2 * b) using 1
  simp

theorem deriv_h6GapAuditHeatPolynomial_spatial (b epsilon t z : ℂ) :
    deriv (h6GapAuditHeatPolynomial b epsilon t) z = 2 * z :=
  (hasDerivAt_h6GapAuditHeatPolynomial_spatial b epsilon t z).deriv

theorem deriv_deriv_h6GapAuditHeatPolynomial_spatial (b epsilon t z : ℂ) :
    deriv (deriv (h6GapAuditHeatPolynomial b epsilon t)) z = 2 := by
  have hderiv : deriv (h6GapAuditHeatPolynomial b epsilon t) = fun w : ℂ ↦ 2 * w := by
    funext w
    exact deriv_h6GapAuditHeatPolynomial_spatial b epsilon t w
  rw [hderiv]
  simp

theorem h6GapAuditHeatPolynomial_backwardHeatEquation (b epsilon t z : ℂ) :
    deriv (fun tau : ℂ ↦ h6GapAuditHeatPolynomial b epsilon tau z) t =
      -deriv (deriv (h6GapAuditHeatPolynomial b epsilon t)) z := by
  rw [(hasDerivAt_h6GapAuditHeatPolynomial_time b epsilon t z).deriv,
    deriv_deriv_h6GapAuditHeatPolynomial_spatial]

theorem h6GapAuditHeatPolynomial_terminal_neg_zero (b epsilon : ℂ) :
    h6GapAuditHeatPolynomial b epsilon b (-epsilon / 2) = 0 := by
  simp [h6GapAuditHeatPolynomial]
  ring

theorem h6GapAuditHeatPolynomial_terminal_pos_zero (b epsilon : ℂ) :
    h6GapAuditHeatPolynomial b epsilon b (epsilon / 2) = 0 := by
  simp [h6GapAuditHeatPolynomial]
  ring

theorem deriv_h6GapAuditHeatPolynomial_terminal_neg_zero (b epsilon : ℂ) :
    deriv (h6GapAuditHeatPolynomial b epsilon b) (-epsilon / 2) = -epsilon := by
  rw [deriv_h6GapAuditHeatPolynomial_spatial]
  ring

theorem deriv_h6GapAuditHeatPolynomial_terminal_pos_zero (b epsilon : ℂ) :
    deriv (h6GapAuditHeatPolynomial b epsilon b) (epsilon / 2) = epsilon := by
  rw [deriv_h6GapAuditHeatPolynomial_spatial]
  ring

theorem h6GapAuditHeatPolynomial_terminal_gap_sq (epsilon : ℂ) :
    (epsilon / 2 - (-epsilon / 2)) ^ 2 = epsilon ^ 2 := by
  ring

theorem h6GapAuditHeatPolynomial_collision_zero (b epsilon : ℂ) :
    h6GapAuditHeatPolynomial b epsilon (h6GapAuditCollisionTime b epsilon) 0 = 0 := by
  simp [h6GapAuditHeatPolynomial, h6GapAuditCollisionTime]
  ring

theorem deriv_h6GapAuditHeatPolynomial_collision_zero (b epsilon : ℂ) :
    deriv (h6GapAuditHeatPolynomial b epsilon (h6GapAuditCollisionTime b epsilon)) 0 = 0 := by
  rw [deriv_h6GapAuditHeatPolynomial_spatial]
  ring

theorem h6GapAuditHeatPolynomial_collision_delay (b epsilon : ℂ) :
    b - h6GapAuditCollisionTime b epsilon = epsilon ^ 2 / 8 := by
  simp [h6GapAuditCollisionTime]

/-- For every positive proposed uniform backward interval, a quadratic backward-heat pair starts
with distinct simple real zeros and reaches a double zero in a strictly shorter time. -/
theorem exists_h6GapAuditHeatPolynomial_collision_within
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon ^ 2 / 8 < delta ∧
      h6GapAuditHeatPolynomial 0 epsilon 0 (-epsilon / 2) = 0 ∧
      h6GapAuditHeatPolynomial 0 epsilon 0 (epsilon / 2) = 0 ∧
      deriv (h6GapAuditHeatPolynomial 0 epsilon 0) (-epsilon / 2) ≠ 0 ∧
      deriv (h6GapAuditHeatPolynomial 0 epsilon 0) (epsilon / 2) ≠ 0 ∧
      h6GapAuditHeatPolynomial 0 epsilon (h6GapAuditCollisionTime 0 epsilon) 0 = 0 ∧
      deriv (h6GapAuditHeatPolynomial 0 epsilon (h6GapAuditCollisionTime 0 epsilon)) 0 = 0 := by
  let epsilon : ℝ := min 1 delta
  have hepsilon : 0 < epsilon := lt_min (by norm_num) hdelta
  have hepsilonOne : epsilon ≤ 1 := min_le_left _ _
  have hepsilonDelta : epsilon ≤ delta := min_le_right _ _
  have hdelay : epsilon ^ 2 / 8 < delta := by
    have hepsilonSq : epsilon ^ 2 ≤ epsilon := by nlinarith
    nlinarith
  refine ⟨epsilon, hepsilon, hdelay, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h6GapAuditHeatPolynomial_terminal_neg_zero 0 epsilon
  · exact h6GapAuditHeatPolynomial_terminal_pos_zero 0 epsilon
  · rw [deriv_h6GapAuditHeatPolynomial_terminal_neg_zero]
    exact neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hepsilon.ne')
  · rw [deriv_h6GapAuditHeatPolynomial_terminal_pos_zero]
    exact Complex.ofReal_ne_zero.mpr hepsilon.ne'
  · exact h6GapAuditHeatPolynomial_collision_zero 0 epsilon
  · exact deriv_h6GapAuditHeatPolynomial_collision_zero 0 epsilon

end

end LeanLab.Riemann
