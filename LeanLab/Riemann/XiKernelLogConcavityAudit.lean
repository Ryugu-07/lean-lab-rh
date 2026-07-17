import Mathlib.Data.Complex.Basic

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# External Xi-kernel log-concavity Lean audit

This module reconstructs and falsifies the exact omitted-premise Hurwitz schema at external commit
`7a89db1d546257d8dabefe1ac8b8d4769298a355`. It also records that the source's formal
`IsLogConcaveOn` shape concludes only `True`. No external code is imported, and this audit neither
proves nor refutes actual log-concavity of the Riemann Xi kernel.
-/

namespace LeanLab.Riemann

/-- The real-zero predicate used by the audited external Hurwitz declaration. -/
def xiLogConcavityAuditHasOnlyRealZeros (F : Complex → Complex) : Prop :=
  ∀ z, F z = 0 → z.im = 0

/-- The exact logical shape of the external declaration, with all convergence hypotheses absent. -/
def xiLogConcavityAuditHurwitzSchema : Prop :=
  ∀ (F : Nat → Complex → Complex) (G : Complex → Complex),
    (∀ n, xiLogConcavityAuditHasOnlyRealZeros (F n)) →
    (∃ z, G z ≠ 0) →
    xiLogConcavityAuditHasOnlyRealZeros G

/-- A zero-free constant sequence for the Hurwitz counterexample. -/
def xiLogConcavityAuditConstantSequence : Nat → Complex → Complex :=
  fun _ _ ↦ 1

/-- A nonzero function with the nonreal zero `I`. -/
def xiLogConcavityAuditLinearTarget (z : Complex) : Complex :=
  z - Complex.I

theorem xiLogConcavityAuditConstantSequence_hasOnlyRealZeros (n : Nat) :
    xiLogConcavityAuditHasOnlyRealZeros (xiLogConcavityAuditConstantSequence n) := by
  intro z hz
  simp [xiLogConcavityAuditConstantSequence] at hz

theorem xiLogConcavityAuditLinearTarget_zero_ne :
    xiLogConcavityAuditLinearTarget 0 ≠ 0 := by
  simp [xiLogConcavityAuditLinearTarget]

theorem xiLogConcavityAuditLinearTarget_I_eq_zero :
    xiLogConcavityAuditLinearTarget Complex.I = 0 := by
  simp [xiLogConcavityAuditLinearTarget]

theorem not_xiLogConcavityAuditLinearTarget_hasOnlyRealZeros :
    ¬ xiLogConcavityAuditHasOnlyRealZeros xiLogConcavityAuditLinearTarget := by
  intro hzeros
  have him := hzeros Complex.I xiLogConcavityAuditLinearTarget_I_eq_zero
  norm_num at him

/-- The external Hurwitz proposition is false without compact-uniform convergence and analyticity. -/
theorem not_xiLogConcavityAuditHurwitzSchema :
    ¬ xiLogConcavityAuditHurwitzSchema := by
  intro hschema
  have htarget := hschema xiLogConcavityAuditConstantSequence xiLogConcavityAuditLinearTarget
    xiLogConcavityAuditConstantSequence_hasOnlyRealZeros
    ⟨0, xiLogConcavityAuditLinearTarget_zero_ne⟩
  exact not_xiLogConcavityAuditLinearTarget_hasOnlyRealZeros htarget

/-- The exact source predicate shape: no derivative or inequality occurs in its conclusion. -/
def xiLogConcavityAuditIsLogConcaveOn (_K : Real → Real) : Prop :=
  ∀ t : Real, 0 ≤ t → ∀ (_Ksecond _Kfirst : Real), True

theorem xiLogConcavityAudit_isLogConcaveOn_trivial (K : Real → Real) :
    xiLogConcavityAuditIsLogConcaveOn K := by
  intro _t _ht _Ksecond _Kfirst
  trivial

/-- Aggregate endpoint for the pinned external-formalization audit. -/
theorem xiKernelLogConcavityExternalAudit_endpoint :
    (∀ K : Real → Real, xiLogConcavityAuditIsLogConcaveOn K) ∧
    (∀ n, xiLogConcavityAuditHasOnlyRealZeros (xiLogConcavityAuditConstantSequence n)) ∧
    (∃ z, xiLogConcavityAuditLinearTarget z ≠ 0) ∧
    ¬ xiLogConcavityAuditHasOnlyRealZeros xiLogConcavityAuditLinearTarget ∧
    ¬ xiLogConcavityAuditHurwitzSchema := by
  exact ⟨xiLogConcavityAudit_isLogConcaveOn_trivial,
    xiLogConcavityAuditConstantSequence_hasOnlyRealZeros,
    ⟨0, xiLogConcavityAuditLinearTarget_zero_ne⟩,
    not_xiLogConcavityAuditLinearTarget_hasOnlyRealZeros,
    not_xiLogConcavityAuditHurwitzSchema⟩

end LeanLab.Riemann
