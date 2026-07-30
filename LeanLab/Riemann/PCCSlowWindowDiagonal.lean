import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Sqrt

set_option linter.style.header false

/-!
# Slow moving windows from fixed-parameter convergence

This module isolates the diagonal-selection step used when a pair-correlation estimate is known
for every fixed compact parameter window but the application needs endpoints that move slowly.
It also records a fast-diagonal counterexample, so fixed-parameter convergence cannot be
misread as convergence along every moving parameter.
-/

open Filter Topology

namespace LeanLab.Riemann

noncomputable section

/-- A positive stage is admissible at index `n` when it respects the external cap and its current
error is smaller than the reciprocal stage. `pccSlowWindow` separately bounds the search by `n`. -/
def pccSlowWindowAdmissible (e : ℕ → ℕ → ℝ) (cap : ℕ → ℕ) (n k : ℕ) : Prop :=
  0 < k ∧ k ≤ cap n ∧ |e n k| < ((k : ℝ)⁻¹)

/-- The largest currently admissible stage below the search horizon. -/
def pccSlowWindow (e : ℕ → ℕ → ℝ) (cap : ℕ → ℕ) (n : ℕ) : ℕ :=
  by
    classical
    exact Nat.findGreatest (pccSlowWindowAdmissible e cap n) n

theorem eventually_pccSlowWindowAdmissible
    {e : ℕ → ℕ → ℝ} {cap : ℕ → ℕ}
    (hcap : Tendsto cap atTop atTop)
    (he : ∀ k, 0 < k → Tendsto (fun n => e n k) atTop (𝓝 0))
    {k : ℕ} (hk : 0 < k) :
    ∀ᶠ n in atTop, k ≤ n ∧ pccSlowWindowAdmissible e cap n k := by
  have hrecip : 0 < ((k : ℝ)⁻¹) := by positivity
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 (he k hk)) ((k : ℝ)⁻¹) hrecip
  filter_upwards [eventually_ge_atTop (max N k), tendsto_atTop.1 hcap k] with n hn hcapn
  have hkn : k ≤ n := le_trans (le_max_right N k) hn
  have herror : |e n k| < ((k : ℝ)⁻¹) := by
    simpa [Real.dist_eq] using hN n (le_trans (le_max_left N k) hn)
  exact ⟨hkn, hk, hcapn, herror⟩

/-- The selected slow window tends to infinity. Every fixed positive stage is eventually an
admissible candidate, so the greatest candidate eventually lies beyond any prescribed bound. -/
theorem tendsto_pccSlowWindow_atTop
    {e : ℕ → ℕ → ℝ} {cap : ℕ → ℕ}
    (hcap : Tendsto cap atTop atTop)
    (he : ∀ k, 0 < k → Tendsto (fun n => e n k) atTop (𝓝 0)) :
    Tendsto (pccSlowWindow e cap) atTop atTop := by
  classical
  refine tendsto_atTop.2 fun b => ?_
  let k := max 1 b
  have hk : 0 < k := lt_of_lt_of_le zero_lt_one (le_max_left 1 b)
  filter_upwards [eventually_pccSlowWindowAdmissible hcap he hk] with n hn
  exact (le_max_right 1 b).trans
    (Nat.le_findGreatest hn.1 hn.2)

theorem eventually_pccSlowWindow_admissible
    {e : ℕ → ℕ → ℝ} {cap : ℕ → ℕ}
    (hcap : Tendsto cap atTop atTop)
    (he : ∀ k, 0 < k → Tendsto (fun n => e n k) atTop (𝓝 0)) :
    ∀ᶠ n in atTop,
      pccSlowWindowAdmissible e cap n (pccSlowWindow e cap n) := by
  classical
  filter_upwards [eventually_pccSlowWindowAdmissible hcap he zero_lt_one] with n hn
  simpa only [pccSlowWindow] using Nat.findGreatest_spec hn.1 hn.2

theorem eventually_pccSlowWindow_pos
    {e : ℕ → ℕ → ℝ} {cap : ℕ → ℕ}
    (hcap : Tendsto cap atTop atTop)
    (he : ∀ k, 0 < k → Tendsto (fun n => e n k) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, 0 < pccSlowWindow e cap n :=
  (eventually_pccSlowWindow_admissible hcap he).mono fun _ hn => hn.1

theorem eventually_pccSlowWindow_le_cap
    {e : ℕ → ℕ → ℝ} {cap : ℕ → ℕ}
    (hcap : Tendsto cap atTop atTop)
    (he : ∀ k, 0 < k → Tendsto (fun n => e n k) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, pccSlowWindow e cap n ≤ cap n :=
  (eventually_pccSlowWindow_admissible hcap he).mono fun _ hn => hn.2.1

theorem eventually_abs_pccSlowWindow_error_lt
    {e : ℕ → ℕ → ℝ} {cap : ℕ → ℕ}
    (hcap : Tendsto cap atTop atTop)
    (he : ∀ k, 0 < k → Tendsto (fun n => e n k) atTop (𝓝 0)) :
    ∀ᶠ n in atTop,
      |e n (pccSlowWindow e cap n)| < (((pccSlowWindow e cap n : ℕ) : ℝ)⁻¹) :=
  (eventually_pccSlowWindow_admissible hcap he).mono fun _ hn => hn.2.2

/-- Reciprocals of the selected positive stages form the shrinking lower window. -/
theorem tendsto_pccSlowWindow_inv_zero
    {e : ℕ → ℕ → ℝ} {cap : ℕ → ℕ}
    (hcap : Tendsto cap atTop atTop)
    (he : ∀ k, 0 < k → Tendsto (fun n => e n k) atTop (𝓝 0)) :
    Tendsto (fun n => (((pccSlowWindow e cap n : ℕ) : ℝ)⁻¹)) atTop (𝓝 0) := by
  exact tendsto_inv_atTop_zero.comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_pccSlowWindow_atTop hcap he))

/-- The error converges to zero along the selected moving stage. -/
theorem tendsto_pccSlowWindow_error_zero
    {e : ℕ → ℕ → ℝ} {cap : ℕ → ℕ}
    (hcap : Tendsto cap atTop atTop)
    (he : ∀ k, 0 < k → Tendsto (fun n => e n k) atTop (𝓝 0)) :
    Tendsto (fun n => e n (pccSlowWindow e cap n)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.norm_eq_abs] using squeeze_zero'
    (Eventually.of_forall fun n => abs_nonneg (e n (pccSlowWindow e cap n)))
    ((eventually_abs_pccSlowWindow_error_lt hcap he).mono fun _ hn => hn.le)
    (tendsto_pccSlowWindow_inv_zero hcap he)

/-- Cap-preserving slow diagonal selection, including both moving window limits. -/
theorem exists_pccSlowWindow
    {e : ℕ → ℕ → ℝ} {cap : ℕ → ℕ}
    (hcap : Tendsto cap atTop atTop)
    (he : ∀ k, 0 < k → Tendsto (fun n => e n k) atTop (𝓝 0)) :
    ∃ window : ℕ → ℕ,
      Tendsto window atTop atTop ∧
      (∀ᶠ n in atTop, 0 < window n) ∧
      (∀ᶠ n in atTop, window n ≤ cap n) ∧
      Tendsto (fun n => e n (window n)) atTop (𝓝 0) ∧
      Tendsto (fun n => ((window n : ℝ)⁻¹)) atTop (𝓝 0) ∧
      Tendsto (fun n => (window n : ℝ)) atTop atTop := by
  refine ⟨pccSlowWindow e cap, tendsto_pccSlowWindow_atTop hcap he,
    eventually_pccSlowWindow_pos hcap he, eventually_pccSlowWindow_le_cap hcap he,
    tendsto_pccSlowWindow_error_zero hcap he, tendsto_pccSlowWindow_inv_zero hcap he, ?_⟩
  exact tendsto_natCast_atTop_atTop.comp (tendsto_pccSlowWindow_atTop hcap he)

/-- Choosing the external cap to be `Nat.sqrt L` retains the source-side square constraint. -/
theorem exists_pccSlowWindow_sq_le
    {e : ℕ → ℕ → ℝ} {L : ℕ → ℕ}
    (hsqrt : Tendsto (fun n => Nat.sqrt (L n)) atTop atTop)
    (he : ∀ k, 0 < k → Tendsto (fun n => e n k) atTop (𝓝 0)) :
    ∃ window : ℕ → ℕ,
      Tendsto window atTop atTop ∧
      (∀ᶠ n in atTop, 0 < window n) ∧
      (∀ᶠ n in atTop, window n ^ 2 ≤ L n) ∧
      Tendsto (fun n => e n (window n)) atTop (𝓝 0) ∧
      Tendsto (fun n => ((window n : ℝ)⁻¹)) atTop (𝓝 0) := by
  obtain ⟨window, hgrow, hpos, hcap, herror, hinv, _⟩ :=
    exists_pccSlowWindow hsqrt he
  refine ⟨window, hgrow, hpos, ?_, herror, hinv⟩
  exact hcap.mono fun n hn => Nat.le_sqrt'.mp hn

/-- A fixed-parameter error array whose error is zero once the sample index reaches the stage. -/
def pccFastDiagonalError (n k : ℕ) : ℝ :=
  if k ≤ n then 0 else 1

theorem tendsto_pccFastDiagonalError_fixed (k : ℕ) :
    Tendsto (fun n => pccFastDiagonalError n k) atTop (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop k] with n hn
  simp [pccFastDiagonalError, hn]

theorem pccFastDiagonalError_fast (n : ℕ) :
    pccFastDiagonalError n (n + 1) = 1 := by
  simp [pccFastDiagonalError]

theorem not_tendsto_pccFastDiagonalError_fast :
    ¬Tendsto (fun n => pccFastDiagonalError n (n + 1)) atTop (𝓝 0) := by
  intro h
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 h) (1 / 2) (by positivity)
  have := hN N le_rfl
  rw [pccFastDiagonalError_fast] at this
  norm_num [Real.dist_eq] at this

end

end LeanLab.Riemann
