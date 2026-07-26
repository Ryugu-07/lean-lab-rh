import Mathlib.NumberTheory.ArithmeticFunction.Liouville
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Pólya--Turán finite Abel sign audit

This file separates the unweighted Pólya sum from Turán's harmonic-weighted Liouville sum.  It
proves their exact finite Abel relation over `ℚ` and records the precise sign information that the
finite transform carries.  No historical eventual-sign conjecture is assumed.
-/

namespace LeanLab.Riemann

open scoped BigOperators ArithmeticFunction.Omega

/-- The sum of the first `N` terms of a one-indexed rational sequence. -/
def finitePrefixSum (a : ℕ → ℚ) (N : ℕ) : ℚ :=
  ∑ n ∈ Finset.range N, a (n + 1)

/-- The harmonic-weighted sum of the first `N` terms of a one-indexed rational sequence. -/
def finiteHarmonicWeightedSum (a : ℕ → ℚ) (N : ℕ) : ℚ :=
  ∑ n ∈ Finset.range N, a (n + 1) / (n + 1 : ℕ)

@[simp] theorem finitePrefixSum_zero (a : ℕ → ℚ) :
    finitePrefixSum a 0 = 0 := by
  simp [finitePrefixSum]

@[simp] theorem finitePrefixSum_succ (a : ℕ → ℚ) (N : ℕ) :
    finitePrefixSum a (N + 1) = finitePrefixSum a N + a (N + 1) := by
  simp [finitePrefixSum, Finset.sum_range_succ]

@[simp] theorem finiteHarmonicWeightedSum_zero (a : ℕ → ℚ) :
    finiteHarmonicWeightedSum a 0 = 0 := by
  simp [finiteHarmonicWeightedSum]

@[simp] theorem finiteHarmonicWeightedSum_succ (a : ℕ → ℚ) (N : ℕ) :
    finiteHarmonicWeightedSum a (N + 1) =
      finiteHarmonicWeightedSum a N + a (N + 1) / (N + 1 : ℕ) := by
  simp [finiteHarmonicWeightedSum, Finset.sum_range_succ]

/-- Finite Abel summation for a harmonic weight, with all endpoints explicit. -/
theorem finiteHarmonicWeightedSum_eq_abel (a : ℕ → ℚ) (N : ℕ) :
    finiteHarmonicWeightedSum a (N + 1) =
      finitePrefixSum a (N + 1) / (N + 1 : ℕ) +
        ∑ k ∈ Finset.range N,
          finitePrefixSum a (k + 1) *
            (1 / (k + 1 : ℕ) - 1 / (k + 2 : ℕ)) := by
  induction N with
  | zero =>
      norm_num [finitePrefixSum, finiteHarmonicWeightedSum]
  | succ N ih =>
      rw [finiteHarmonicWeightedSum_succ a (N + 1), ih, Finset.sum_range_succ,
        finitePrefixSum_succ a (N + 1)]
      push_cast
      field_simp
      all_goals ring

/-- A version of finite Abel summation in which the first prefix contributes the visible `1/2`. -/
theorem finiteHarmonicWeightedSum_eq_half_add_tail (a : ℕ → ℚ)
    (hfirst : finitePrefixSum a 1 = 1) (N : ℕ) :
    finiteHarmonicWeightedSum a (N + 2) =
      1 / 2 + finitePrefixSum a (N + 2) / (N + 2 : ℕ) +
        ∑ k ∈ Finset.range N,
          finitePrefixSum a (k + 2) *
            (1 / (k + 2 : ℕ) - 1 / (k + 3 : ℕ)) := by
  induction N with
  | zero =>
      simp only [zero_add, finiteHarmonicWeightedSum_succ,
        finiteHarmonicWeightedSum_zero, Nat.cast_one, div_one, Nat.reduceAdd,
        Nat.cast_ofNat, one_div, finitePrefixSum_succ, finitePrefixSum_zero,
        Finset.range_zero, Nat.cast_add, Finset.sum_empty, add_zero] at hfirst ⊢
      rw [hfirst]
      ring
  | succ N ih =>
      rw [finiteHarmonicWeightedSum_succ a (N + 2), ih, Finset.sum_range_succ,
        finitePrefixSum_succ a (N + 2)]
      push_cast
      field_simp
      all_goals ring

/-- Mathlib's integer-valued Liouville function, embedded into exact rational arithmetic. -/
def liouvilleRat (n : ℕ) : ℚ :=
  (ArithmeticFunction.liouville n : ℚ)

@[simp] theorem liouvilleRat_one :
    liouvilleRat 1 = 1 := by
  simp [liouvilleRat, ArithmeticFunction.liouville_apply_one]

@[simp] theorem liouvilleRat_two :
    liouvilleRat 2 = -1 := by
  rw [liouvilleRat, ArithmeticFunction.liouville_apply (by norm_num),
    ArithmeticFunction.cardFactors_apply_prime Nat.prime_two]
  norm_num

/-- Pólya's unweighted finite Liouville sum, represented in `ℚ`. -/
def polyaLiouvilleSum (N : ℕ) : ℚ :=
  finitePrefixSum liouvilleRat N

/-- Turán's harmonic-weighted finite Liouville sum, represented in `ℚ`. -/
def turanLiouvilleSum (N : ℕ) : ℚ :=
  finiteHarmonicWeightedSum liouvilleRat N

@[simp] theorem polyaLiouvilleSum_one :
    polyaLiouvilleSum 1 = 1 := by
  simp [polyaLiouvilleSum]

@[simp] theorem turanLiouvilleSum_one :
    turanLiouvilleSum 1 = 1 := by
  norm_num [turanLiouvilleSum, finiteHarmonicWeightedSum]

@[simp] theorem polyaLiouvilleSum_two :
    polyaLiouvilleSum 2 = 0 := by
  simp [polyaLiouvilleSum, finitePrefixSum, Finset.sum_range_succ]

@[simp] theorem turanLiouvilleSum_two :
    turanLiouvilleSum 2 = 1 / 2 := by
  norm_num [turanLiouvilleSum, finiteHarmonicWeightedSum, Finset.sum_range_succ]

/-- The exact finite Abel identity specialized to the source Liouville sums. -/
theorem turanLiouvilleSum_eq_abel (N : ℕ) :
    turanLiouvilleSum (N + 1) =
      polyaLiouvilleSum (N + 1) / (N + 1 : ℕ) +
        ∑ k ∈ Finset.range N,
          polyaLiouvilleSum (k + 1) *
            (1 / (k + 1 : ℕ) - 1 / (k + 2 : ℕ)) := by
  exact finiteHarmonicWeightedSum_eq_abel liouvilleRat N

private theorem harmonicDifference_nonneg (k : ℕ) :
    0 ≤ (1 / (k + 2 : ℕ) - 1 / (k + 3 : ℕ) : ℚ) := by
  have hk2 : ((k + 2 : ℕ) : ℚ) ≠ 0 := by positivity
  have hk3 : ((k + 3 : ℕ) : ℚ) ≠ 0 := by positivity
  have hrewrite :
      (1 / (k + 2 : ℕ) - 1 / (k + 3 : ℕ) : ℚ) =
        1 / (((k + 2 : ℕ) : ℚ) * ((k + 3 : ℕ) : ℚ)) := by
    field_simp [hk2, hk3]
    push_cast
    ring
  rw [hrewrite]
  positivity

/-- Pólya-prefix nonpositivity beginning at `2` yields only the upper bound `T(N) ≤ 1/2`
through the finite Abel transform. -/
theorem turanLiouvilleSum_le_half_of_polya_nonpos (N : ℕ)
    (hpolya : ∀ k : ℕ, 2 ≤ k → k ≤ N + 2 → polyaLiouvilleSum k ≤ 0) :
    turanLiouvilleSum (N + 2) ≤ 1 / 2 := by
  rw [show turanLiouvilleSum (N + 2) =
      1 / 2 + polyaLiouvilleSum (N + 2) / (N + 2 : ℕ) +
        ∑ k ∈ Finset.range N,
          polyaLiouvilleSum (k + 2) *
            (1 / (k + 2 : ℕ) - 1 / (k + 3 : ℕ)) by
    exact finiteHarmonicWeightedSum_eq_half_add_tail liouvilleRat
      (by simp) N]
  have hfinal : polyaLiouvilleSum (N + 2) / (N + 2 : ℕ) ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (hpolya (N + 2) (by omega) le_rfl) (by positivity)
  have htail :
      (∑ k ∈ Finset.range N,
        polyaLiouvilleSum (k + 2) *
          (1 / (k + 2 : ℕ) - 1 / (k + 3 : ℕ))) ≤ 0 := by
    apply Finset.sum_nonpos
    intro k hk
    apply mul_nonpos_of_nonpos_of_nonneg
    · apply hpolya (k + 2) (by omega)
      have hkN : k < N := Finset.mem_range.mp hk
      omega
    · exact harmonicDifference_nonneg k
  linarith

/-- A two-term rational sequence witnessing that generic prefix nonpositivity does not imply
harmonic-weighted positivity. -/
def polyaTuranSignShortcutWitness (n : ℕ) : ℚ :=
  if n = 1 then 1 else if n = 2 then -3 else 0

theorem polyaTuranSignShortcutWitness_first :
    finitePrefixSum polyaTuranSignShortcutWitness 1 = 1 := by
  norm_num [finitePrefixSum, polyaTuranSignShortcutWitness]

theorem polyaTuranSignShortcutWitness_prefix_add_two (N : ℕ) :
    finitePrefixSum polyaTuranSignShortcutWitness (N + 2) = -2 := by
  induction N with
  | zero =>
      norm_num [finitePrefixSum, polyaTuranSignShortcutWitness, Finset.sum_range_succ]
  | succ N ih =>
      rw [show N + 1 + 2 = (N + 2) + 1 by omega,
        finitePrefixSum_succ, ih]
      have hneTwo : N + 2 + 1 ≠ 2 := by omega
      simp [polyaTuranSignShortcutWitness, hneTwo]

theorem polyaTuranSignShortcutWitness_prefix_nonpos (k : ℕ) (hk : 2 ≤ k) :
    finitePrefixSum polyaTuranSignShortcutWitness k ≤ 0 := by
  have hkEq : k = (k - 2) + 2 := by omega
  rw [hkEq, polyaTuranSignShortcutWitness_prefix_add_two]
  norm_num

theorem polyaTuranSignShortcutWitness_weighted_neg :
    finiteHarmonicWeightedSum polyaTuranSignShortcutWitness 2 < 0 := by
  norm_num [finiteHarmonicWeightedSum, polyaTuranSignShortcutWitness,
    Finset.sum_range_succ]

theorem exists_prefixNonpositive_weightedNegative :
    ∃ a : ℕ → ℚ,
      finitePrefixSum a 1 = 1 ∧
      (∀ k : ℕ, 2 ≤ k → finitePrefixSum a k ≤ 0) ∧
      finiteHarmonicWeightedSum a 2 < 0 := by
  exact ⟨polyaTuranSignShortcutWitness,
    polyaTuranSignShortcutWitness_first,
    polyaTuranSignShortcutWitness_prefix_nonpos,
    polyaTuranSignShortcutWitness_weighted_neg⟩

/-- The complete finite Pólya--Turán route audit. -/
structure PolyaTuranAbelSignAuditCertificate : Prop where
  genericAbel :
    ∀ (a : ℕ → ℚ) (N : ℕ),
      finiteHarmonicWeightedSum a (N + 1) =
        finitePrefixSum a (N + 1) / (N + 1 : ℕ) +
          ∑ k ∈ Finset.range N,
            finitePrefixSum a (k + 1) *
              (1 / (k + 1 : ℕ) - 1 / (k + 2 : ℕ))
  liouvilleAbel :
    ∀ N : ℕ,
      turanLiouvilleSum (N + 1) =
        polyaLiouvilleSum (N + 1) / (N + 1 : ℕ) +
          ∑ k ∈ Finset.range N,
            polyaLiouvilleSum (k + 1) *
              (1 / (k + 1 : ℕ) - 1 / (k + 2 : ℕ))
  finiteSignConsequence :
    ∀ N : ℕ,
      (∀ k : ℕ, 2 ≤ k → k ≤ N + 2 → polyaLiouvilleSum k ≤ 0) →
        turanLiouvilleSum (N + 2) ≤ 1 / 2
  signShortcutFails :
    ∃ a : ℕ → ℚ,
      finitePrefixSum a 1 = 1 ∧
      (∀ k : ℕ, 2 ≤ k → finitePrefixSum a k ≤ 0) ∧
      finiteHarmonicWeightedSum a 2 < 0

theorem polyaTuranAbelSignAudit_endpoint :
    PolyaTuranAbelSignAuditCertificate where
  genericAbel := finiteHarmonicWeightedSum_eq_abel
  liouvilleAbel := turanLiouvilleSum_eq_abel
  finiteSignConsequence := turanLiouvilleSum_le_half_of_polya_nonpos
  signShortcutFails := exists_prefixNonpositive_weightedNegative

end LeanLab.Riemann
