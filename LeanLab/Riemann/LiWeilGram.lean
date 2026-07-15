import LeanLab.Riemann.LiReverseCriterion

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The Li-test Weil Gram form

This file packages Lagarias's Weil pairing on the finite real span of the Li test functions. The
zero-side kernel is averaged under `rho |-> 1-rho`, so its linear reciprocal divergence cancels
before any infinite sum is taken.
-/

noncomputable section

open Complex Set
open scoped BigOperators ComplexConjugate

namespace LeanLab.Riemann

/-- One reflection-averaged, multiplicity-bearing Li-test Weil Gram term. -/
def liWeilGramTerm (n m : ℕ) (p : RiemannXiDivisorZeroIndex) : ℂ :=
  let ρ := riemannXiDivisorZeroValue p
  (liRawZeroTerm (n + 1) ρ * liRawZeroTerm (m + 1) (1 - ρ) +
      liRawZeroTerm (n + 1) (1 - ρ) * liRawZeroTerm (m + 1) ρ) / 2

private def liWeilSymPowTerm (n : ℕ) (q : ℂ) : ℂ :=
  ((1 - q ^ (n + 1)) + (1 - q⁻¹ ^ (n + 1))) / 2

private def liWeilGramPowTerm (n m : ℕ) (q : ℂ) : ℂ :=
  ((1 - q ^ (n + 1)) * (1 - q⁻¹ ^ (m + 1)) +
      (1 - q⁻¹ ^ (n + 1)) * (1 - q ^ (m + 1))) / 2

private theorem liWeilGramPowTerm_eq_of_le (q : ℂ) (hq : q ≠ 0)
    {n m : ℕ} (hnm : n ≤ m) :
    liWeilGramPowTerm n m q =
      liWeilSymPowTerm n q + liWeilSymPowTerm m q -
        if n = m then 0 else liWeilSymPowTerm (Nat.dist n m - 1) q := by
  by_cases hEq : n = m
  · subst m
    simp [liWeilGramPowTerm, liWeilSymPowTerm]
    field_simp [hq]
    ring
  · have hlt : n < m := lt_of_le_of_ne hnm hEq
    have hdist : Nat.dist n m = m - n := Nat.dist_eq_sub_of_le hnm
    have hsucc : m + 1 = (n + 1) + (m - n) := by omega
    have hpred : m - n - 1 + 1 = m - n := by omega
    have hqpow : q ^ (m + 1) = q ^ (n + 1) * q ^ (m - n) := by
      rw [hsucc, pow_add]
    rw [if_neg hEq, hdist]
    unfold liWeilGramPowTerm liWeilSymPowTerm
    simp only [inv_pow]
    rw [hpred, hqpow]
    field_simp [pow_ne_zero _ hq]
    ring

private theorem liWeilGramPowTerm_eq (q : ℂ) (hq : q ≠ 0) (n m : ℕ) :
    liWeilGramPowTerm n m q =
      liWeilSymPowTerm n q + liWeilSymPowTerm m q -
        if n = m then 0 else liWeilSymPowTerm (Nat.dist n m - 1) q := by
  by_cases hnm : n ≤ m
  · exact liWeilGramPowTerm_eq_of_le q hq hnm
  · have hmn : m ≤ n := Nat.le_of_not_ge hnm
    have hswap := liWeilGramPowTerm_eq_of_le q hq hmn
    simpa [liWeilGramPowTerm, Nat.dist_comm, eq_comm, add_comm, mul_comm] using hswap

private theorem one_sub_inv_one_sub_eq_inv_one_sub_inv
    {ρ : ℂ} (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1) :
    1 - 1 / (1 - ρ) = (1 - 1 / ρ)⁻¹ := by
  field_simp [hρ0, sub_ne_zero.mpr hρ1.symm, sub_ne_zero.mpr hρ1]
  ring

/-- Each Gram term is a finite combination of the compiled summable symmetry-paired Li terms. -/
theorem liWeilGramTerm_eq_symmetrized (n m : ℕ) (p : RiemannXiDivisorZeroIndex) :
    liWeilGramTerm n m p =
      riemannXiSymmetrizedLiZeroTerm n p +
        riemannXiSymmetrizedLiZeroTerm m p -
          if n = m then 0 else
            riemannXiSymmetrizedLiZeroTerm (Nat.dist n m - 1) p := by
  let ρ := riemannXiDivisorZeroValue p
  let q := 1 - 1 / ρ
  have hρ0 : ρ ≠ 0 := Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p
  have hρ1 : ρ ≠ 1 :=
    (sub_ne_zero.mp (one_sub_riemannXiDivisorZeroValue_ne_zero p)).symm
  have hq0 : q ≠ 0 := by
    dsimp [q]
    intro hq
    have hdiv : (1 : ℂ) = 1 / ρ := sub_eq_zero.mp hq
    have hone : (1 : ℂ) * ρ = 1 := (eq_div_iff hρ0).mp hdiv
    exact hρ1 (by simpa using hone)
  have hreflect : 1 - 1 / (1 - ρ) = q⁻¹ := by
    dsimp [q]
    exact one_sub_inv_one_sub_eq_inv_one_sub_inv hρ0 hρ1
  have hraw (k : ℕ) : liRawZeroTerm k ρ = 1 - q ^ k := by
    simp only [liRawZeroTerm, q]
  have hrawReflect (k : ℕ) : liRawZeroTerm k (1 - ρ) = 1 - q⁻¹ ^ k := by
    rw [liRawZeroTerm, hreflect]
  have hpow := liWeilGramPowTerm_eq q hq0 n m
  change
    (liRawZeroTerm (n + 1) ρ * liRawZeroTerm (m + 1) (1 - ρ) +
        liRawZeroTerm (n + 1) (1 - ρ) * liRawZeroTerm (m + 1) ρ) / 2 = _
  rw [hraw, hraw, hrawReflect, hrawReflect]
  simpa [riemannXiSymmetrizedLiZeroTerm, liWeilGramPowTerm, liWeilSymPowTerm,
    ρ, hraw, hrawReflect] using hpow

/-- The reflection-averaged Li-test Gram term is absolutely summable over the xi divisor. -/
theorem summable_liWeilGramTerm (n m : ℕ) :
    Summable (liWeilGramTerm n m) := by
  by_cases hnm : n = m
  · have hsum := (summable_riemannXiSymmetrizedLiZeroTerm n).add
      (summable_riemannXiSymmetrizedLiZeroTerm m)
    apply hsum.congr
    intro p
    simpa [hnm] using (liWeilGramTerm_eq_symmetrized n m p).symm
  · have hsum := ((summable_riemannXiSymmetrizedLiZeroTerm n).add
      (summable_riemannXiSymmetrizedLiZeroTerm m)).sub
        (summable_riemannXiSymmetrizedLiZeroTerm (Nat.dist n m - 1))
    apply hsum.congr
    intro p
    simpa [hnm] using (liWeilGramTerm_eq_symmetrized n m p).symm

/-- The Li-test Weil Gram entry, summed with divisor multiplicity. -/
def liWeilGram (n m : ℕ) : ℂ :=
  ∑' p : RiemannXiDivisorZeroIndex, liWeilGramTerm n m p

theorem liWeilGramTerm_comm (n m : ℕ) (p : RiemannXiDivisorZeroIndex) :
    liWeilGramTerm n m p = liWeilGramTerm m n p := by
  unfold liWeilGramTerm
  ring

theorem liWeilGram_comm (n m : ℕ) :
    liWeilGram n m = liWeilGram m n := by
  unfold liWeilGram
  apply tsum_congr
  exact liWeilGramTerm_comm n m

/-- Lagarias's Gram entry formula in the project's successor-indexed Li convention. -/
theorem liWeilGram_eq_liCoefficients (n m : ℕ) :
    liWeilGram n m =
      liCoefficientCandidate n + liCoefficientCandidate m -
        if n = m then 0 else liCoefficientCandidate (Nat.dist n m - 1) := by
  unfold liWeilGram
  by_cases hnm : n = m
  · rw [tsum_congr (liWeilGramTerm_eq_symmetrized n m)]
    simp only [if_pos hnm, sub_zero]
    rw [(summable_riemannXiSymmetrizedLiZeroTerm n).tsum_add
      (summable_riemannXiSymmetrizedLiZeroTerm m)]
    rw [← liCoefficientCandidate_eq_tsum_riemannXiSymmetrizedLiZeroTerm,
      ← liCoefficientCandidate_eq_tsum_riemannXiSymmetrizedLiZeroTerm]
  · rw [tsum_congr (liWeilGramTerm_eq_symmetrized n m)]
    simp only [if_neg hnm]
    rw [((summable_riemannXiSymmetrizedLiZeroTerm n).add
      (summable_riemannXiSymmetrizedLiZeroTerm m)).tsum_sub
        (summable_riemannXiSymmetrizedLiZeroTerm (Nat.dist n m - 1))]
    rw [(summable_riemannXiSymmetrizedLiZeroTerm n).tsum_add
      (summable_riemannXiSymmetrizedLiZeroTerm m)]
    rw [← liCoefficientCandidate_eq_tsum_riemannXiSymmetrizedLiZeroTerm,
      ← liCoefficientCandidate_eq_tsum_riemannXiSymmetrizedLiZeroTerm,
      ← liCoefficientCandidate_eq_tsum_riemannXiSymmetrizedLiZeroTerm]

/-- Every diagonal Gram entry is exactly twice the corresponding project Li coefficient. -/
theorem liWeilGram_diagonal (n : ℕ) :
    liWeilGram n n = 2 * liCoefficientCandidate n := by
  rw [liWeilGram_eq_liCoefficients]
  simp
  ring

/-- The Li test polynomial associated to a finitely supported real coefficient family. -/
def liWeilCombination (c : ℕ →₀ ℝ) (p : RiemannXiDivisorZeroIndex) : ℂ :=
  ∑ n ∈ c.support,
    (c n : ℂ) * liRawZeroTerm (n + 1) (riemannXiDivisorZeroValue p)

/-- The real quadratic form of the Li-test Weil Gram matrix. -/
def liWeilQuadratic (c : ℕ →₀ ℝ) : ℝ :=
  ∑ n ∈ c.support, ∑ m ∈ c.support,
    c n * c m * (liWeilGram n m).re

/-- On RH, the real part of each averaged kernel term is the usual Hermitian Gram term. -/
theorem RiemannHypothesis.liWeilGramTerm_re_eq
    (hRH : RiemannHypothesis) (n m : ℕ) (p : RiemannXiDivisorZeroIndex) :
    (liWeilGramTerm n m p).re =
      (liRawZeroTerm (n + 1) (riemannXiDivisorZeroValue p) *
        conj (liRawZeroTerm (m + 1) (riemannXiDivisorZeroValue p))).re := by
  have hreflect :=
    RiemannHypothesis.one_sub_riemannXiDivisorZeroValue_eq_conj hRH p
  rw [liWeilGramTerm]
  rw [hreflect, liRawZeroTerm_conj, liRawZeroTerm_conj]
  simp [Complex.mul_re]

private theorem normSq_finset_sum_eq_sum_mul_conj_re
    {α : Type*} (s : Finset α) (a : α → ℂ) :
    Complex.normSq (∑ i ∈ s, a i) =
      ∑ i ∈ s, ∑ j ∈ s, (a i * conj (a j)).re := by
  classical
  have hconj : conj (∑ j ∈ s, a j) = ∑ j ∈ s, conj (a j) := by
    simp
  have hmul :
      (∑ i ∈ s, a i) * (∑ j ∈ s, conj (a j)) =
        ∑ i ∈ s, ∑ j ∈ s, a i * conj (a j) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
  calc
    Complex.normSq (∑ i ∈ s, a i) =
        ((∑ i ∈ s, a i) * conj (∑ j ∈ s, a j)).re := by
      rw [Complex.mul_conj]
      simp
    _ = (∑ i ∈ s, ∑ j ∈ s, a i * conj (a j)).re := by
      rw [hconj, hmul]
    _ = ∑ i ∈ s, ∑ j ∈ s, (a i * conj (a j)).re := by
      simp

/-- Under RH, each finite real-coefficient kernel integrand is a squared norm. -/
theorem RiemannHypothesis.liWeilQuadraticIntegrand_eq_normSq
    (hRH : RiemannHypothesis) (c : ℕ →₀ ℝ) (p : RiemannXiDivisorZeroIndex) :
    (∑ n ∈ c.support, ∑ m ∈ c.support,
      c n * c m * (liWeilGramTerm n m p).re) =
        Complex.normSq (liWeilCombination c p) := by
  change _ = Complex.normSq (∑ n ∈ c.support,
    (c n : ℂ) * liRawZeroTerm (n + 1) (riemannXiDivisorZeroValue p))
  rw [normSq_finset_sum_eq_sum_mul_conj_re]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  rw [RiemannHypothesis.liWeilGramTerm_re_eq hRH]
  simp only [map_mul, conj_ofReal]
  simp [Complex.mul_re]
  ring

/-- Every finite quadratic integrand is summable before RH is imposed. -/
theorem summable_liWeilQuadraticIntegrand (c : ℕ →₀ ℝ) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      ∑ n ∈ c.support, ∑ m ∈ c.support,
        c n * c m * (liWeilGramTerm n m p).re) := by
  apply summable_sum
  intro n hn
  apply summable_sum
  intro m hm
  have hre : Summable (fun p : RiemannXiDivisorZeroIndex =>
      (liWeilGramTerm n m p).re) := by
    simpa only [Complex.reCLM_apply] using
      Complex.reCLM.summable (summable_liWeilGramTerm n m)
  exact hre.mul_left (c n * c m)

/-- Under RH, the squared norms of every finite Li-test combination are summable. -/
theorem RiemannHypothesis.summable_liWeilCombination_normSq
    (hRH : RiemannHypothesis) (c : ℕ →₀ ℝ) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      Complex.normSq (liWeilCombination c p)) := by
  apply (summable_liWeilQuadraticIntegrand c).congr
  intro p
  exact RiemannHypothesis.liWeilQuadraticIntegrand_eq_normSq hRH c p

/-- The finite Gram sum may be interchanged with its absolutely convergent divisor sum. -/
theorem liWeilQuadratic_eq_tsum_integrand (c : ℕ →₀ ℝ) :
    liWeilQuadratic c =
      ∑' p : RiemannXiDivisorZeroIndex,
        ∑ n ∈ c.support, ∑ m ∈ c.support,
          c n * c m * (liWeilGramTerm n m p).re := by
  let f : ℕ → ℕ → RiemannXiDivisorZeroIndex → ℝ := fun n m p =>
    c n * c m * (liWeilGramTerm n m p).re
  have hf (n m : ℕ) : Summable (f n m) := by
    have hre : Summable (fun p : RiemannXiDivisorZeroIndex =>
        (liWeilGramTerm n m p).re) := by
      simpa only [Complex.reCLM_apply] using
        Complex.reCLM.summable (summable_liWeilGramTerm n m)
    exact hre.mul_left (c n * c m)
  have hinner (n : ℕ) : Summable (fun p => ∑ m ∈ c.support, f n m p) :=
    summable_sum (fun m hm => hf n m)
  change (∑ n ∈ c.support, ∑ m ∈ c.support,
      c n * c m * (∑' p : RiemannXiDivisorZeroIndex, liWeilGramTerm n m p).re) = _
  calc
    (∑ n ∈ c.support, ∑ m ∈ c.support,
        c n * c m * (∑' p : RiemannXiDivisorZeroIndex,
          liWeilGramTerm n m p).re) =
      ∑ n ∈ c.support, ∑ m ∈ c.support, ∑' p, f n m p := by
        apply Finset.sum_congr rfl
        intro n hn
        apply Finset.sum_congr rfl
        intro m hm
        rw [Complex.re_tsum (summable_liWeilGramTerm n m)]
        exact tsum_mul_left.symm
    _ = ∑' p, ∑ n ∈ c.support, ∑ m ∈ c.support, f n m p := by
      rw [Summable.tsum_finsetSum (fun n hn => hinner n)]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Summable.tsum_finsetSum (fun m hm => hf n m)]
    _ = ∑' p : RiemannXiDivisorZeroIndex,
        ∑ n ∈ c.support, ∑ m ∈ c.support,
          c n * c m * (liWeilGramTerm n m p).re := by
      rfl

/-- Under RH, the full finite Li-test quadratic form is a sum of squared zero-side norms. -/
theorem RiemannHypothesis.liWeilQuadratic_eq_tsum_normSq
    (hRH : RiemannHypothesis) (c : ℕ →₀ ℝ) :
    liWeilQuadratic c =
      ∑' p : RiemannXiDivisorZeroIndex,
        Complex.normSq (liWeilCombination c p) := by
  rw [liWeilQuadratic_eq_tsum_integrand]
  apply tsum_congr
  exact RiemannHypothesis.liWeilQuadraticIntegrand_eq_normSq hRH c

/-- RH makes every finite real Li-test Weil quadratic value nonnegative. -/
theorem RiemannHypothesis.liWeilQuadratic_nonneg
    (hRH : RiemannHypothesis) (c : ℕ →₀ ℝ) :
    0 ≤ liWeilQuadratic c := by
  rw [RiemannHypothesis.liWeilQuadratic_eq_tsum_normSq hRH]
  exact tsum_nonneg fun p => Complex.normSq_nonneg _

/-- A one-coordinate quadratic value recovers twice the corresponding Li coefficient real part. -/
theorem liWeilQuadratic_single_one (n : ℕ) :
    liWeilQuadratic (Finsupp.single n 1) =
      2 * (liCoefficientCandidate n).re := by
  simp [liWeilQuadratic, liWeilGram_diagonal]

/-- Positivity of the finite real Li-test Weil Gram form is exactly the Riemann hypothesis. -/
theorem riemannHypothesis_iff_forall_liWeilQuadratic_nonneg :
    RiemannHypothesis ↔ ∀ c : ℕ →₀ ℝ, 0 ≤ liWeilQuadratic c := by
  constructor
  · intro hRH c
    exact RiemannHypothesis.liWeilQuadratic_nonneg hRH c
  · intro hQ
    apply riemannHypothesis_of_forall_liCoefficientCandidate_re_nonneg
    intro n
    have hn := hQ (Finsupp.single n 1)
    rw [liWeilQuadratic_single_one] at hn
    linarith

end LeanLab.Riemann
