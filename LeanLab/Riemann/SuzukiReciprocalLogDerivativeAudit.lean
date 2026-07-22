import Mathlib

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Suzuki reciprocal-log-derivative limit audit

This module isolates two generic regularity boundaries in a 2026 finite-interval spectral proposal.
Neither model is the source characteristic function or the Riemann xi function.
-/

open Filter
open scoped Topology

namespace LeanLab.Riemann

noncomputable section

/-- Every zero of a complex-valued function lies on the real axis. -/
def suzukiAuditHasOnlyRealZeros (F : ℂ → ℂ) : Prop :=
  ∀ z, F z = 0 → z.im = 0

/-- A target with the explicit nonreal zero `I`. -/
def suzukiAuditLinearTarget (z : ℂ) : ℂ :=
  z - Complex.I

/-- A nowhere-zero approximation obtained by replacing the target's value at `I`. -/
def suzukiAuditPuncturedApproximation (n : ℕ) (z : ℂ) : ℂ :=
  if z = Complex.I then 1 / ((n + 1 : ℕ) : ℂ) else z - Complex.I

theorem suzukiAuditPuncturedApproximation_ne_zero (n : ℕ) (z : ℂ) :
    suzukiAuditPuncturedApproximation n z ≠ 0 := by
  by_cases hz : z = Complex.I
  · subst z
    rw [suzukiAuditPuncturedApproximation, if_pos rfl]
    exact one_div_ne_zero (by exact_mod_cast Nat.succ_ne_zero n)
  · rw [suzukiAuditPuncturedApproximation, if_neg hz]
    exact sub_ne_zero.mpr hz

theorem suzukiAuditPuncturedApproximation_hasOnlyRealZeros (n : ℕ) :
    suzukiAuditHasOnlyRealZeros (suzukiAuditPuncturedApproximation n) := by
  intro z hz
  exact (suzukiAuditPuncturedApproximation_ne_zero n z hz).elim

/-- A uniform scalar error bound tending to zero gives uniform convergence on the set. -/
theorem tendstoUniformlyOn_of_dist_le
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {K : Set ℂ} {b : ℕ → ℝ}
    (hb : Tendsto b atTop (𝓝 0))
    (hb_nonneg : ∀ n, 0 ≤ b n)
    (hbound : ∀ n z, z ∈ K → dist (f z) (F n z) ≤ b n) :
    TendstoUniformlyOn F f atTop K := by
  refine Metric.tendstoUniformlyOn_iff.mpr ?_
  intro ε hε
  have hsmall : ∀ᶠ n : ℕ in atTop, dist (b n) 0 < ε :=
    (Metric.tendsto_nhds.mp hb) ε hε
  filter_upwards [hsmall] with n hn
  intro z hz
  apply lt_of_le_of_lt (hbound n z hz)
  simpa [Real.dist_eq, abs_of_nonneg (hb_nonneg n)] using hn

theorem suzukiAuditPuncturedApproximation_dist_le (n : ℕ) (z : ℂ) :
    dist (suzukiAuditLinearTarget z) (suzukiAuditPuncturedApproximation n z) ≤
      (1 : ℝ) / (n + 1 : ℝ) := by
  by_cases hz : z = Complex.I
  · subst z
    rw [suzukiAuditPuncturedApproximation, if_pos rfl]
    have htarget : suzukiAuditLinearTarget Complex.I = 0 := by
      simp [suzukiAuditLinearTarget]
    rw [htarget, dist_zero_left]
    rw [norm_div, norm_one, RCLike.norm_natCast]
    norm_num
  · rw [suzukiAuditPuncturedApproximation, if_neg hz]
    simp only [suzukiAuditLinearTarget, dist_self]
    positivity

/-- The punctured sequence converges uniformly even on an arbitrary set. -/
theorem suzukiAuditPuncturedApproximation_tendstoUniformlyOn (K : Set ℂ) :
    TendstoUniformlyOn
      (fun n : ℕ => fun z : ℂ => suzukiAuditPuncturedApproximation n z)
      (fun z : ℂ => suzukiAuditLinearTarget z) (atTop : Filter ℕ) K := by
  have hscalar :
      Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1 : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  exact tendstoUniformlyOn_of_dist_le hscalar
    (fun n => by positivity)
    (fun n z _hz => suzukiAuditPuncturedApproximation_dist_le n z)

/-- The zero-free source-shaped finite characteristic function. -/
def suzukiAuditFiniteW (_n : ℕ) (_z : ℂ) : ℂ :=
  1

/-- A finite-valued but nonregular logarithmic normalizer. -/
def suzukiAuditFinitePhi (n : ℕ) (z : ℂ) : ℂ :=
  Complex.log (suzukiAuditPuncturedApproximation n z)

theorem suzukiAuditFiniteW_hasOnlyRealZeros (n : ℕ) :
    suzukiAuditHasOnlyRealZeros (suzukiAuditFiniteW n) := by
  intro z hz
  simp [suzukiAuditFiniteW] at hz

theorem suzukiAuditFiniteNormalization_eq (n : ℕ) (z : ℂ) :
    Complex.exp (suzukiAuditFinitePhi n z) * suzukiAuditFiniteW n z =
      suzukiAuditPuncturedApproximation n z := by
  simp [suzukiAuditFinitePhi, suzukiAuditFiniteW,
    Complex.exp_log (suzukiAuditPuncturedApproximation_ne_zero n z)]

theorem suzukiAuditFiniteNormalization_tendstoUniformlyOn (K : Set ℂ) :
    TendstoUniformlyOn
      (fun n z => Complex.exp (suzukiAuditFinitePhi n z) * suzukiAuditFiniteW n z)
      suzukiAuditLinearTarget atTop K := by
  simpa only [suzukiAuditFiniteNormalization_eq] using
    suzukiAuditPuncturedApproximation_tendstoUniformlyOn K

theorem not_suzukiAuditLinearTarget_hasOnlyRealZeros :
    ¬ suzukiAuditHasOnlyRealZeros suzukiAuditLinearTarget := by
  intro h
  have hI := h Complex.I (by simp [suzukiAuditLinearTarget])
  norm_num at hI

/-- The literal finite-normalization zero-persistence schema, with no regularity imposed on `phi`. -/
def suzukiAuditFiniteNormalizationZeroPersistenceSchema : Prop :=
  ∀ (W : ℕ → ℂ → ℂ) (phi : ℕ → ℂ → ℂ) (G : ℂ → ℂ),
    (∀ n, suzukiAuditHasOnlyRealZeros (W n)) →
    (∀ K : Set ℂ, IsCompact K →
      TendstoUniformlyOn (fun n z => Complex.exp (phi n z) * W n z) G atTop K) →
    suzukiAuditHasOnlyRealZeros G

theorem not_suzukiAuditFiniteNormalizationZeroPersistenceSchema :
    ¬ suzukiAuditFiniteNormalizationZeroPersistenceSchema := by
  intro hschema
  have htarget := hschema suzukiAuditFiniteW suzukiAuditFinitePhi suzukiAuditLinearTarget
    suzukiAuditFiniteW_hasOnlyRealZeros
    (fun K _hK => suzukiAuditFiniteNormalization_tendstoUniformlyOn K)
  exact not_suzukiAuditLinearTarget_hasOnlyRealZeros htarget

/-- A symmetric quartic with four real roots and an off-center critical point. -/
def suzukiAuditQuartic (z : ℂ) : ℂ :=
  (z ^ 2 - (1 / 5 : ℂ) ^ 2) * (z ^ 2 - (7 / 5 : ℂ) ^ 2)

/-- The complex derivative of `suzukiAuditQuartic`. -/
def suzukiAuditQuarticDerivative (z : ℂ) : ℂ :=
  4 * z ^ 3 - 4 * z

theorem hasDerivAt_suzukiAuditQuartic (z : ℂ) :
    HasDerivAt suzukiAuditQuartic (suzukiAuditQuarticDerivative z) z := by
  have hleft :
      HasDerivAt (fun w : ℂ => w ^ 2 - (1 / 5 : ℂ) ^ 2) (2 * z) z := by
    simpa [Function.id_def] using
      ((hasDerivAt_id z).pow 2).sub_const ((1 / 5 : ℂ) ^ 2)
  have hright :
      HasDerivAt (fun w : ℂ => w ^ 2 - (7 / 5 : ℂ) ^ 2) (2 * z) z := by
    simpa [Function.id_def] using
      ((hasDerivAt_id z).pow 2).sub_const ((7 / 5 : ℂ) ^ 2)
  change HasDerivAt
    (fun w : ℂ => (w ^ 2 - (1 / 5 : ℂ) ^ 2) * (w ^ 2 - (7 / 5 : ℂ) ^ 2))
    (4 * z ^ 3 - 4 * z) z
  have hderiv :
      4 * z ^ 3 - 4 * z =
        2 * z * (z ^ 2 - (7 / 5 : ℂ) ^ 2) +
          (z ^ 2 - (1 / 5 : ℂ) ^ 2) * (2 * z) := by
    ring
  rw [hderiv]
  exact hleft.mul hright

theorem suzukiAuditQuartic_hasOnlyRealZeros :
    suzukiAuditHasOnlyRealZeros suzukiAuditQuartic := by
  intro z hz
  change (z ^ 2 - (1 / 5 : ℂ) ^ 2) * (z ^ 2 - (7 / 5 : ℂ) ^ 2) = 0 at hz
  rcases mul_eq_zero.mp hz with hz | hz
  · have hsq : z ^ 2 = (1 / 5 : ℂ) ^ 2 := sub_eq_zero.mp hz
    rcases eq_or_eq_neg_of_sq_eq_sq z (1 / 5 : ℂ) hsq with h | h
    · simp [h]
    · simp [h]
  · have hsq : z ^ 2 = (7 / 5 : ℂ) ^ 2 := sub_eq_zero.mp hz
    rcases eq_or_eq_neg_of_sq_eq_sq z (7 / 5 : ℂ) hsq with h | h
    · simp [h]
    · simp [h]

theorem suzukiAuditQuarticDerivative_one :
    suzukiAuditQuarticDerivative 1 = 0 := by
  norm_num [suzukiAuditQuarticDerivative]

theorem suzukiAuditQuartic_one_ne_zero :
    suzukiAuditQuartic 1 ≠ 0 := by
  norm_num [suzukiAuditQuartic]

/-- A finite-valued global extension of the scaled reciprocal logarithmic derivative. -/
def SuzukiAuditHasFiniteReciprocalLogDerivativeExtension
    (f f' : ℂ → ℂ) : Prop :=
  ∃ F : ℂ → ℂ, ∀ z, f' z * F z = z ^ 2 * f z

theorem not_hasFiniteReciprocalLogDerivativeExtension_of_critical
    {f f' : ℂ → ℂ} {c : ℂ}
    (hc : c ≠ 0) (hf' : f' c = 0) (hf : f c ≠ 0) :
    ¬ SuzukiAuditHasFiniteReciprocalLogDerivativeExtension f f' := by
  rintro ⟨F, hF⟩
  have h := hF c
  rw [hf', zero_mul] at h
  exact (mul_ne_zero (pow_ne_zero 2 hc) hf) h.symm

theorem not_exists_suzukiAuditQuartic_reciprocalLogDerivativeExtension :
    ¬ SuzukiAuditHasFiniteReciprocalLogDerivativeExtension
      suzukiAuditQuartic suzukiAuditQuarticDerivative := by
  exact not_hasFiniteReciprocalLogDerivativeExtension_of_critical
    (by norm_num : (1 : ℂ) ≠ 0)
    suzukiAuditQuarticDerivative_one
    suzukiAuditQuartic_one_ne_zero

/-- Aggregate endpoint for the two interpretation branches of the route audit. -/
theorem suzukiReciprocalLogDerivativeAudit_endpoint :
    (∀ n, suzukiAuditHasOnlyRealZeros (suzukiAuditFiniteW n)) ∧
    (∀ K : Set ℂ,
      TendstoUniformlyOn
        (fun n z => Complex.exp (suzukiAuditFinitePhi n z) * suzukiAuditFiniteW n z)
        suzukiAuditLinearTarget atTop K) ∧
    ¬ suzukiAuditHasOnlyRealZeros suzukiAuditLinearTarget ∧
    ¬ suzukiAuditFiniteNormalizationZeroPersistenceSchema ∧
    suzukiAuditHasOnlyRealZeros suzukiAuditQuartic ∧
    (∀ z, HasDerivAt suzukiAuditQuartic (suzukiAuditQuarticDerivative z) z) ∧
    ¬ SuzukiAuditHasFiniteReciprocalLogDerivativeExtension
      suzukiAuditQuartic suzukiAuditQuarticDerivative := by
  exact ⟨suzukiAuditFiniteW_hasOnlyRealZeros,
    suzukiAuditFiniteNormalization_tendstoUniformlyOn,
    not_suzukiAuditLinearTarget_hasOnlyRealZeros,
    not_suzukiAuditFiniteNormalizationZeroPersistenceSchema,
    suzukiAuditQuartic_hasOnlyRealZeros,
    hasDerivAt_suzukiAuditQuartic,
    not_exists_suzukiAuditQuartic_reciprocalLogDerivativeExtension⟩

end

end LeanLab.Riemann
