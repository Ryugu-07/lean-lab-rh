import LeanLab.Riemann.PairCorrelationHorizontalMultiplicity

set_option linter.style.header false

/-!
# Jensen polynomial eventual hyperbolicity

This module isolates the quantifier gap between fixed-degree eventual hyperbolicity and the
all-degree, all-shift real-rootedness condition. The coefficient model is generic and is not the
Taylor sequence of the Riemann xi function.
-/

open Complex Filter Polynomial
open scoped BigOperators Polynomial Topology

namespace LeanLab.Riemann

noncomputable section

/-- The degree-`d`, shift-`n` Jensen polynomial of a real coefficient sequence. -/
def jensenPolynomial (a : ℕ → ℝ) (d n : ℕ) : ℝ[X] :=
  ∑ j ∈ Finset.range (d + 1),
    C ((d.choose j : ℝ) * a (n + j)) * X ^ j

/-- Every complex root of the real polynomial lies on the real axis. -/
def JensenHasOnlyRealRoots (p : ℝ[X]) : Prop :=
  ∀ z : ℂ, p.eval₂ (algebraMap ℝ ℂ) z = 0 → z.im = 0

theorem jensenPolynomial_congr {a b : ℕ → ℝ} {d n : ℕ}
    (h : ∀ j ≤ d, a (n + j) = b (n + j)) :
    jensenPolynomial a d n = jensenPolynomial b d n := by
  unfold jensenPolynomial
  apply Finset.sum_congr rfl
  intro j hj
  have hjlt : j < d + 1 := Finset.mem_range.mp hj
  rw [h j (by omega)]

theorem jensenPolynomial_const_one (d n : ℕ) :
    jensenPolynomial (fun _ ↦ 1) d n = (1 + X) ^ d := by
  ext k
  rw [Polynomial.coeff_one_add_X_pow]
  by_cases hdk : d < k
  · simp [jensenPolynomial, Nat.choose_eq_zero_of_lt hdk]
  · have hk : k ≤ d := Nat.le_of_not_gt hdk
    simp [jensenPolynomial, hk]

theorem jensenHasOnlyRealRoots_one_add_X_pow (d : ℕ) :
    JensenHasOnlyRealRoots ((1 + X) ^ d : ℝ[X]) := by
  intro z hz
  have hzPow : (1 + z) ^ d = 0 := by
    simpa [JensenHasOnlyRealRoots] using hz
  have hzBase : 1 + z = 0 := (pow_eq_zero_iff'.mp hzPow).1
  have hzValue : z = -1 := by linear_combination hzBase
  rw [hzValue]
  norm_num

/-- One zero coefficient inserted after the initial indices `0,...,m`. -/
def jensenSingleDefectCoefficients (m k : ℕ) : ℝ :=
  if k = m + 1 then 0 else 1

theorem jensenSingleDefect_eq_one_of_le (m k : ℕ) (hk : k ≤ m) :
    jensenSingleDefectCoefficients m k = 1 := by
  simp [jensenSingleDefectCoefficients, show k ≠ m + 1 by omega]

theorem jensenSingleDefect_eq_one_of_defect_lt (m k : ℕ) (hk : m + 1 < k) :
    jensenSingleDefectCoefficients m k = 1 := by
  simp [jensenSingleDefectCoefficients, show k ≠ m + 1 by omega]

theorem jensenSingleDefect_finiteWedge_eq (m d n : ℕ) (hnd : n + d ≤ m) :
    jensenPolynomial (jensenSingleDefectCoefficients m) d n = (1 + X) ^ d := by
  rw [← jensenPolynomial_const_one d n]
  apply jensenPolynomial_congr
  intro j hj
  exact jensenSingleDefect_eq_one_of_le m (n + j) (by omega)

theorem jensenSingleDefect_finiteWedge (m d n : ℕ) (hnd : n + d ≤ m) :
    JensenHasOnlyRealRoots
      (jensenPolynomial (jensenSingleDefectCoefficients m) d n) := by
  rw [jensenSingleDefect_finiteWedge_eq m d n hnd]
  exact jensenHasOnlyRealRoots_one_add_X_pow d

theorem jensenSingleDefect_past_defect_eq (m d n : ℕ) (hn : m + 1 < n) :
    jensenPolynomial (jensenSingleDefectCoefficients m) d n = (1 + X) ^ d := by
  rw [← jensenPolynomial_const_one d n]
  apply jensenPolynomial_congr
  intro j _hj
  exact jensenSingleDefect_eq_one_of_defect_lt m (n + j) (by omega)

theorem jensenSingleDefect_eventually_hasOnlyRealRoots (m d : ℕ) :
    ∀ᶠ n in atTop,
      JensenHasOnlyRealRoots
        (jensenPolynomial (jensenSingleDefectCoefficients m) d n) := by
  filter_upwards [eventually_ge_atTop (m + 2)] with n hn
  rw [jensenSingleDefect_past_defect_eq m d n (by omega)]
  exact jensenHasOnlyRealRoots_one_add_X_pow d

theorem jensenSingleDefect_degree_two (m : ℕ) :
    jensenPolynomial (jensenSingleDefectCoefficients m) 2 m = 1 + X ^ 2 := by
  simp [jensenPolynomial, jensenSingleDefectCoefficients, Finset.sum_range_succ]

theorem not_jensenHasOnlyRealRoots_one_add_X_sq :
    ¬ JensenHasOnlyRealRoots (1 + X ^ 2 : ℝ[X]) := by
  intro hreal
  have him : Complex.I.im = 0 := hreal Complex.I (by norm_num)
  norm_num at him

theorem not_jensenSingleDefect_all_hasOnlyRealRoots (m : ℕ) :
    ¬ ∀ d n : ℕ,
      JensenHasOnlyRealRoots
        (jensenPolynomial (jensenSingleDefectCoefficients m) d n) := by
  intro hall
  have hbad := hall 2 m
  rw [jensenSingleDefect_degree_two m] at hbad
  exact not_jensenHasOnlyRealRoots_one_add_X_sq hbad

/-- Fixed-degree eventual hyperbolicity and all-index hyperbolicity have different quantifiers. -/
theorem exists_eventually_realRooted_not_all_realRooted :
    ∃ a : ℕ → ℝ,
      (∀ d : ℕ, ∀ᶠ n in atTop, JensenHasOnlyRealRoots (jensenPolynomial a d n)) ∧
      ¬ ∀ d n : ℕ, JensenHasOnlyRealRoots (jensenPolynomial a d n) := by
  refine ⟨jensenSingleDefectCoefficients 0, ?_,
    not_jensenSingleDefect_all_hasOnlyRealRoots 0⟩
  exact fun d ↦ jensenSingleDefect_eventually_hasOnlyRealRoots 0 d

end

end LeanLab.Riemann
