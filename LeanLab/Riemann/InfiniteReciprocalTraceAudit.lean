import LeanLab.Riemann.FinitePowerSumRigidity

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Infinite reciprocal-trace transfer audit

This module isolates a generic obstruction to transferring finite Frobenius power traces to an
ordinary countably infinite sum. It does not model zeta zeros or regularized trace formulae.
-/

open Filter
open scoped Topology

namespace LeanLab.Riemann

noncomputable section

/-- A countable spectrum is paired to a constant by a permutation. -/
def infiniteSpectrumHasReciprocalPairing
    (alpha : ℕ → ℂ) (sigma : Equiv.Perm ℕ) (q : ℂ) : Prop :=
  ∀ n, alpha (sigma n) * alpha n = q

/-- The ordinary `k`-th power trace is admissible exactly when its terms are summable. -/
def infiniteSpectrumHasOrdinaryPowerTrace (alpha : ℕ → ℂ) (k : ℕ) : Prop :=
  Summable (fun n => alpha n ^ k)

theorem infiniteSpectrumHasOrdinaryPowerTrace_reindex
    {alpha : ℕ → ℂ} {sigma : Equiv.Perm ℕ} {k : ℕ}
    (htrace : infiniteSpectrumHasOrdinaryPowerTrace alpha k) :
    Summable (fun n => alpha (sigma n) ^ k) := by
  change Summable ((fun n => alpha n ^ k) ∘ sigma)
  exact sigma.summable_iff.mpr htrace

theorem infiniteSpectrumOrdinaryPowerTrace_tendsto_zero
    {alpha : ℕ → ℂ} {k : ℕ}
    (htrace : infiniteSpectrumHasOrdinaryPowerTrace alpha k) :
    Tendsto (fun n => alpha n ^ k) atTop (𝓝 0) :=
  htrace.tendsto_atTop_zero

theorem infiniteSpectrumOrdinaryPowerTrace_reindex_tendsto_zero
    {alpha : ℕ → ℂ} {sigma : Equiv.Perm ℕ} {k : ℕ}
    (htrace : infiniteSpectrumHasOrdinaryPowerTrace alpha k) :
    Tendsto (fun n => alpha (sigma n) ^ k) atTop (𝓝 0) :=
  (infiniteSpectrumHasOrdinaryPowerTrace_reindex htrace).tendsto_atTop_zero

/-- A positive ordinary power trace and a constant reciprocal pairing force the constant to zero. -/
theorem eq_zero_of_ordinaryPowerTrace_and_reciprocalPairing
    {alpha : ℕ → ℂ} {sigma : Equiv.Perm ℕ} {q : ℂ} {k : ℕ}
    (hk : 0 < k)
    (htrace : infiniteSpectrumHasOrdinaryPowerTrace alpha k)
    (hpair : infiniteSpectrumHasReciprocalPairing alpha sigma q) :
    q = 0 := by
  have horiginal : Tendsto (fun n => alpha n ^ k) atTop (𝓝 0) :=
    infiniteSpectrumOrdinaryPowerTrace_tendsto_zero htrace
  have hpaired : Tendsto (fun n => alpha (sigma n) ^ k) atTop (𝓝 0) :=
    infiniteSpectrumOrdinaryPowerTrace_reindex_tendsto_zero htrace
  have hproduct :
      Tendsto (fun n => alpha (sigma n) ^ k * alpha n ^ k) atTop (𝓝 0) := by
    simpa using hpaired.mul horiginal
  have hconstant :
      (fun n => alpha (sigma n) ^ k * alpha n ^ k) = (fun _ : ℕ => q ^ k) := by
    funext n
    rw [← mul_pow, hpair n]
  rw [hconstant] at hproduct
  have hqpow : q ^ k = 0 :=
    (tendsto_nhds_unique hproduct tendsto_const_nhds).symm
  exact (pow_eq_zero_iff (Nat.ne_of_gt hk)).mp hqpow

theorem not_ordinaryPowerTrace_of_reciprocalPairing
    {alpha : ℕ → ℂ} {sigma : Equiv.Perm ℕ} {q : ℂ} {k : ℕ}
    (hk : 0 < k) (hq : q ≠ 0)
    (hpair : infiniteSpectrumHasReciprocalPairing alpha sigma q) :
    ¬ infiniteSpectrumHasOrdinaryPowerTrace alpha k := by
  intro htrace
  exact hq (eq_zero_of_ordinaryPowerTrace_and_reciprocalPairing hk htrace hpair)

/-- Nonzero reciprocal pairing and ordinary power traces coexist on a finite spectrum. -/
theorem finiteReciprocalPairingWitness :
    ∃ (alpha : Fin 1 → ℂ) (sigma : Equiv.Perm (Fin 1)) (q : ℂ),
      q ≠ 0 ∧
      (∀ i, alpha (sigma i) * alpha i = q) ∧
      (∀ k : ℕ, Summable (fun i => alpha i ^ k)) := by
  refine ⟨fun _ => 1, Equiv.refl (Fin 1), 1, one_ne_zero, ?_, ?_⟩
  · intro i
    simp
  · intro k
    exact summable_of_hasFiniteSupport (Set.toFinite _)

/-- Aggregate finite/infinite contrast for the literal ordinary-trace transfer. -/
theorem infiniteReciprocalTraceAudit_endpoint :
    (∃ (alpha : Fin 1 → ℂ) (sigma : Equiv.Perm (Fin 1)) (q : ℂ),
      q ≠ 0 ∧
      (∀ i, alpha (sigma i) * alpha i = q) ∧
      (∀ k : ℕ, Summable (fun i => alpha i ^ k))) ∧
    (∀ (alpha : ℕ → ℂ) (sigma : Equiv.Perm ℕ) (q : ℂ) (k : ℕ),
      0 < k → q ≠ 0 →
      infiniteSpectrumHasReciprocalPairing alpha sigma q →
      ¬ infiniteSpectrumHasOrdinaryPowerTrace alpha k) := by
  exact ⟨finiteReciprocalPairingWitness,
    fun alpha sigma q k hk hq hpair =>
      not_ordinaryPowerTrace_of_reciprocalPairing hk hq hpair⟩

end

end LeanLab.Riemann
