import LeanLab.Riemann.LiZeroFormula
import Mathlib.Analysis.PSeries

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Symmetry-paired Li zero formula

This module replaces the genus-one compensated Li zero formula by a summable raw zero formula
paired under the multiplicity-preserving functional-equation involution `rho |-> 1-rho`.
-/

open Complex Filter Function Polynomial Set Topology
open scoped BigOperators ComplexConjugate Topology

namespace LeanLab.Riemann

noncomputable section

/-- One raw Li zero term. Its first reciprocal-power part is not separately absolutely summable. -/
def liRawZeroTerm (m : ℕ) (ρ : ℂ) : ℂ :=
  1 - (1 - 1 / ρ) ^ m

theorem liRawZeroTerm_one (ρ : ℂ) :
    liRawZeroTerm 1 ρ = 1 / ρ := by
  simp [liRawZeroTerm]

/-- Squared reciprocal summability alone does not imply summability of an unpaired raw Li term. -/
theorem summable_square_reciprocal_nat_succ :
    Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ (2 : ℕ)) 1).2
      (Real.summable_one_div_nat_pow.mpr (by norm_num))

theorem not_summable_liRawZeroTerm_one_nat_succ :
    ¬Summable (fun n : ℕ => liRawZeroTerm 1 ((n + 1 : ℕ) : ℂ)) := by
  intro h
  have hreal : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) := by
    rw [← Complex.summable_ofReal]
    simpa [liRawZeroTerm] using h
  exact Real.not_summable_one_div_natCast
    ((summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ)) 1).1
      (by simpa only [Nat.cast_add, Nat.cast_one] using hreal))

/-- A finite off-critical model: symmetry pairing is not termwise nonnegative without RH. -/
theorem liRawZeroTerm_pair_quarter_two :
    (liRawZeroTerm 2 (1 / 4 : ℂ) + liRawZeroTerm 2 (1 - (1 / 4 : ℂ))) / 2 =
      (-32 / 9 : ℂ) := by
  norm_num [liRawZeroTerm]

theorem one_sub_riemannXiDivisorZeroValue_ne_zero
    (p : RiemannXiDivisorZeroIndex) :
    1 - riemannXiDivisorZeroValue p ≠ 0 := by
  intro h
  have hp1 : riemannXiDivisorZeroValue p = 1 := by
    exact (sub_eq_zero.mp h).symm
  have hre := nontrivial_zero_re_lt_one
    (riemannXiDivisorZeroIndex_val_isNontrivialZero p)
  change (riemannXiDivisorZeroValue p).re < 1 at hre
  rw [hp1] at hre
  norm_num at hre

private theorem riemannXiDivisorZeroIndex_reflect_card
    (p : RiemannXiDivisorZeroIndex) :
    Int.toNat (MeromorphicOn.divisor riemannXi (Set.univ : Set ℂ)
        (1 - riemannXiDivisorZeroValue p)) =
      Int.toNat (MeromorphicOn.divisor riemannXi (Set.univ : Set ℂ)
        (riemannXiDivisorZeroValue p)) := by
  change Int.toNat (riemannXiZeroDivisor (1 - riemannXiDivisorZeroValue p)) =
    Int.toNat (riemannXiZeroDivisor (riemannXiDivisorZeroValue p))
  rw [riemannXiZeroDivisor_one_sub]

/-- Reflection of a multiplicity-bearing xi divisor index under the functional equation. -/
def riemannXiDivisorZeroReflect
    (p : RiemannXiDivisorZeroIndex) : RiemannXiDivisorZeroIndex :=
  ⟨⟨1 - riemannXiDivisorZeroValue p,
      Fin.cast (riemannXiDivisorZeroIndex_reflect_card p).symm p.1.2⟩,
    one_sub_riemannXiDivisorZeroValue_ne_zero p⟩

@[simp]
theorem riemannXiDivisorZeroValue_reflect (p : RiemannXiDivisorZeroIndex) :
    riemannXiDivisorZeroValue (riemannXiDivisorZeroReflect p) =
      1 - riemannXiDivisorZeroValue p :=
  rfl

theorem riemannXiDivisorZeroReflect_involutive :
    Function.Involutive riemannXiDivisorZeroReflect := by
  intro p
  apply Subtype.ext
  have hval : 1 - (1 - riemannXiDivisorZeroValue p) =
      riemannXiDivisorZeroValue p := by ring
  apply Sigma.ext hval
  refine (Fin.heq_ext_iff ?_).2 ?_
  · simp only [riemannXiDivisorZeroValue_reflect, hval]
  · simp [riemannXiDivisorZeroReflect]

/-- The divisor-index permutation induced by `rho |-> 1-rho`. -/
def riemannXiDivisorZeroReflectEquiv :
    RiemannXiDivisorZeroIndex ≃ RiemannXiDivisorZeroIndex :=
  riemannXiDivisorZeroReflect_involutive.toPerm

@[simp]
theorem riemannXiDivisorZeroReflectEquiv_apply (p : RiemannXiDivisorZeroIndex) :
    riemannXiDivisorZeroReflectEquiv p = riemannXiDivisorZeroReflect p :=
  rfl

/-- The raw Li zero term averaged over the functional-equation pair, with multiplicity. -/
def riemannXiSymmetrizedLiZeroTerm
    (n : ℕ) (p : RiemannXiDivisorZeroIndex) : ℂ :=
  (liRawZeroTerm (n + 1) (riemannXiDivisorZeroValue p) +
      liRawZeroTerm (n + 1) (1 - riemannXiDivisorZeroValue p)) / 2

theorem sum_choose_neg_one_mul_pow_succ (n : ℕ) (x : ℂ) :
    (∑ k ∈ Finset.range (n + 1),
        ((n + 1).choose (k + 1) : ℂ) * (-1 : ℂ) ^ k * x ^ (k + 1)) =
      1 - (1 - x) ^ (n + 1) := by
  have hpow := add_pow (-x) 1 (n + 1)
  rw [Finset.sum_range_succ'] at hpow
  simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one] at hpow
  rw [show (-x + 1) ^ (n + 1) = (1 - x) ^ (n + 1) by ring] at hpow
  rw [hpow]
  rw [show 1 -
      ((∑ k ∈ Finset.range (n + 1),
          (-x) ^ (k + 1) * ((n + 1).choose (k + 1) : ℂ)) + 1) =
        -(∑ k ∈ Finset.range (n + 1),
          (-x) ^ (k + 1) * ((n + 1).choose (k + 1) : ℂ)) by ring]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [neg_pow]
  ring

/-- The contribution of one multiplicity-bearing zero to the differentiated compensated formula. -/
def riemannXiLiZeroContribution
    (n : ℕ) (p : RiemannXiDivisorZeroIndex) : ℂ :=
  (∑ i ∈ Finset.range (n + 1),
      ((n + 1).choose i : ℂ) * (n.descFactorial i : ℂ) *
        riemannXiLogDerivZeroDerivativeTerm (n - i) p 1) /
    (n.factorial : ℂ)

private def normalizedReflectedLiZeroContributionTerm
    (n k : ℕ) (ρ : ℂ) : ℂ :=
  ((n + 1).choose (k + 1) : ℂ) * (-1 : ℂ) ^ k /
      (1 - ρ) ^ (k + 1) +
    if k = 0 then (n + 1 : ℂ) / ρ else 0

private theorem normalized_reflected_term_from_le
    (n i : ℕ) (hi : i < n + 1) (p : RiemannXiDivisorZeroIndex) :
    (((n + 1).choose i : ℂ) * (n.descFactorial i : ℂ) *
        riemannXiLogDerivZeroDerivativeTerm (n - i) p 1) /
      (n.factorial : ℂ) =
        normalizedReflectedLiZeroContributionTerm n (n - i)
          (riemannXiDivisorZeroValue p) := by
  have hin : i ≤ n := by omega
  have him : i ≤ n + 1 := by omega
  have hchoose : (n + 1).choose i = (n + 1).choose (n - i + 1) := by
    calc
      (n + 1).choose i = (n + 1).choose (n + 1 - i) :=
        (Nat.choose_symm him).symm
      _ = (n + 1).choose (n - i + 1) :=
        congrArg ((n + 1).choose ·) (by omega)
  have hfactorial : (n - i).factorial * n.descFactorial i = n.factorial :=
    Nat.factorial_mul_descFactorial hin
  have hfactorialC :
      ((n - i).factorial : ℂ) * (n.descFactorial i : ℂ) = (n.factorial : ℂ) := by
    exact_mod_cast hfactorial
  have hnfac : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hρ1 : (1 : ℂ) - riemannXiDivisorZeroValue p ≠ 0 :=
    one_sub_riemannXiDivisorZeroValue_ne_zero p
  have hρ0 : riemannXiDivisorZeroValue p ≠ 0 :=
    Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p
  by_cases hk : n - i = 0
  · have hi_eq : i = n := by omega
    subst i
    simp [normalizedReflectedLiZeroContributionTerm,
      riemannXiLogDerivZeroDerivativeTerm]
    field_simp [hnfac, hρ0, hρ1, Nat.descFactorial_self]
    exact_mod_cast Nat.descFactorial_self n
  · rw [riemannXiLogDerivZeroDerivativeTerm, if_neg hk, add_zero]
    rw [normalizedReflectedLiZeroContributionTerm, if_neg hk]
    simp only [add_zero]
    rw [hchoose]
    field_simp [hnfac, hρ1]
    calc
      ((n + 1).choose (n - i + 1) : ℂ) * (n.descFactorial i : ℂ) *
          ((n - i).factorial : ℂ) =
        ((n + 1).choose (n - i + 1) : ℂ) *
          (((n - i).factorial : ℂ) * (n.descFactorial i : ℂ)) := by ring
      _ = ((n + 1).choose (n - i + 1) : ℂ) * (n.factorial : ℂ) := by
        rw [hfactorialC]

theorem riemannXiLiZeroContribution_eq_reflected_raw
    (n : ℕ) (p : RiemannXiDivisorZeroIndex) :
    riemannXiLiZeroContribution n p =
      liRawZeroTerm (n + 1) (1 - riemannXiDivisorZeroValue p) +
        (n + 1 : ℂ) / riemannXiDivisorZeroValue p := by
  rw [riemannXiLiZeroContribution, Finset.sum_div]
  have hreflect :
      (∑ i ∈ Finset.range (n + 1),
          normalizedReflectedLiZeroContributionTerm n (n - i)
            (riemannXiDivisorZeroValue p)) =
        ∑ i ∈ Finset.range (n + 1),
          (((n + 1).choose i : ℂ) * (n.descFactorial i : ℂ) *
            riemannXiLogDerivZeroDerivativeTerm (n - i) p 1) /
              (n.factorial : ℂ) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact (normalized_reflected_term_from_le n i (Finset.mem_range.mp hi) p).symm
  rw [← hreflect]
  have hsumReflect := Finset.sum_range_reflect
    (fun k => normalizedReflectedLiZeroContributionTerm n k
      (riemannXiDivisorZeroValue p)) (n + 1)
  rw [show (∑ i ∈ Finset.range (n + 1),
      normalizedReflectedLiZeroContributionTerm n (n - i)
        (riemannXiDivisorZeroValue p)) =
      ∑ i ∈ Finset.range (n + 1),
        normalizedReflectedLiZeroContributionTerm n i
          (riemannXiDivisorZeroValue p) by
    simpa only [Nat.add_sub_cancel_right] using hsumReflect]
  unfold normalizedReflectedLiZeroContributionTerm
  rw [Finset.sum_add_distrib]
  have hlinear :
      (∑ k ∈ Finset.range (n + 1),
        if k = 0 then (n + 1 : ℂ) / riemannXiDivisorZeroValue p else 0) =
          (n + 1 : ℂ) / riemannXiDivisorZeroValue p := by
    simp
  rw [hlinear]
  rw [show (∑ k ∈ Finset.range (n + 1),
      ((n + 1).choose (k + 1) : ℂ) * (-1 : ℂ) ^ k /
        (1 - riemannXiDivisorZeroValue p) ^ (k + 1)) =
      liRawZeroTerm (n + 1) (1 - riemannXiDivisorZeroValue p) by
    rw [liRawZeroTerm]
    have hρ1 := one_sub_riemannXiDivisorZeroValue_ne_zero p
    have hx : 1 / (1 - riemannXiDivisorZeroValue p) =
        (1 - riemannXiDivisorZeroValue p)⁻¹ := one_div _
    rw [show 1 - 1 / (1 - riemannXiDivisorZeroValue p) =
        1 - (1 - riemannXiDivisorZeroValue p)⁻¹ by rw [hx]]
    rw [← sum_choose_neg_one_mul_pow_succ n
      ((1 - riemannXiDivisorZeroValue p)⁻¹)]
    apply Finset.sum_congr rfl
    intro k hk
    rw [div_eq_mul_inv, inv_pow]]

private theorem summable_finset_sum_of_summable
    {α : Type*} (s : Finset ℕ) (f : ℕ → α → ℂ)
    (hf : ∀ i ∈ s, Summable (f i)) :
    Summable (fun a => ∑ i ∈ s, f i a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hisum : Summable (fun a => ∑ j ∈ s, f j a) :=
        ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      have hiSummable : Summable (f i) := hf i (Finset.mem_insert_self i s)
      simpa [Finset.sum_insert hi] using hiSummable.add hisum

theorem summable_riemannXiLiZeroContribution (n : ℕ) :
    Summable (riemannXiLiZeroContribution n) := by
  unfold riemannXiLiZeroContribution
  apply Summable.div_const
  apply summable_finset_sum_of_summable
  intro i hi
  exact (summable_riemannXiLogDerivZeroDerivativeTerm_one (n - i)).mul_left
    (((n + 1).choose i : ℂ) * (n.descFactorial i : ℂ))

/-- The summable reciprocal pair that cancels the linear Hadamard contribution. -/
def riemannXiLiReciprocalPair (p : RiemannXiDivisorZeroIndex) : ℂ :=
  1 / (1 - riemannXiDivisorZeroValue p) + 1 / riemannXiDivisorZeroValue p

theorem summable_riemannXiLiReciprocalPair :
    Summable riemannXiLiReciprocalPair := by
  change Summable (fun p : RiemannXiDivisorZeroIndex =>
    1 / (1 - riemannXiDivisorZeroValue p) + 1 / riemannXiDivisorZeroValue p)
  simpa [riemannXiLogDerivZeroDerivativeTerm, one_div] using
    summable_riemannXiLogDerivZeroDerivativeTerm_one 0

theorem riemannXiLiZeroContribution_reflect_average
    (n : ℕ) (p : RiemannXiDivisorZeroIndex) :
    (riemannXiLiZeroContribution n p +
        riemannXiLiZeroContribution n (riemannXiDivisorZeroReflectEquiv p)) / 2 =
      riemannXiSymmetrizedLiZeroTerm n p +
        ((n + 1 : ℂ) / 2) * riemannXiLiReciprocalPair p := by
  rw [riemannXiLiZeroContribution_eq_reflected_raw,
    riemannXiLiZeroContribution_eq_reflected_raw]
  simp only [riemannXiDivisorZeroReflectEquiv_apply,
    riemannXiDivisorZeroValue_reflect]
  unfold riemannXiSymmetrizedLiZeroTerm riemannXiLiReciprocalPair
  rw [show 1 - (1 - riemannXiDivisorZeroValue p) =
      riemannXiDivisorZeroValue p by ring]
  ring

theorem summable_riemannXiSymmetrizedLiZeroTerm (n : ℕ) :
    Summable (riemannXiSymmetrizedLiZeroTerm n) := by
  let f : RiemannXiDivisorZeroIndex → ℂ := riemannXiLiZeroContribution n
  have hf : Summable f := summable_riemannXiLiZeroContribution n
  have hreflect : Summable (fun p => f (riemannXiDivisorZeroReflectEquiv p)) :=
    hf.comp_injective riemannXiDivisorZeroReflectEquiv.injective
  have havg : Summable (fun p =>
      (f p + f (riemannXiDivisorZeroReflectEquiv p)) / 2) :=
    (hf.add hreflect).div_const 2
  have hpair : Summable (fun p =>
      ((n + 1 : ℂ) / 2) * riemannXiLiReciprocalPair p) :=
    summable_riemannXiLiReciprocalPair.mul_left ((n + 1 : ℂ) / 2)
  apply (havg.sub hpair).congr
  intro p
  rw [riemannXiLiZeroContribution_reflect_average]
  ring

theorem tsum_riemannXiLiZeroContribution_eq_reflect_average (n : ℕ) :
    (∑' p : RiemannXiDivisorZeroIndex, riemannXiLiZeroContribution n p) =
      ∑' p : RiemannXiDivisorZeroIndex,
        (riemannXiLiZeroContribution n p +
          riemannXiLiZeroContribution n (riemannXiDivisorZeroReflectEquiv p)) / 2 := by
  have hf := summable_riemannXiLiZeroContribution n
  have hreflect : Summable (fun p =>
      riemannXiLiZeroContribution n (riemannXiDivisorZeroReflectEquiv p)) :=
    hf.comp_injective riemannXiDivisorZeroReflectEquiv.injective
  rw [tsum_div_const]
  rw [hf.tsum_add hreflect]
  rw [riemannXiDivisorZeroReflectEquiv.tsum_eq]
  ring

theorem polynomial_derivative_eq_C_eval_one_of_degree_le_one
    {P : Polynomial ℂ} (hdegree : P.degree ≤ 1) :
    P.derivative = Polynomial.C (Polynomial.eval 1 P.derivative) := by
  have hnat : P.natDegree ≤ 1 := Polynomial.natDegree_le_of_degree_le hdegree
  have hderivNat : P.derivative.natDegree = 0 := by
    have hle := Polynomial.natDegree_derivative_le P
    omega
  rw [Polynomial.eq_C_of_natDegree_eq_zero hderivNat]
  simp

/-- The finite contribution of the degree-at-most-one Hadamard polynomial. -/
def riemannXiLiPolynomialContribution (n : ℕ) (P : Polynomial ℂ) : ℂ :=
  (∑ i ∈ Finset.range (n + 1),
      ((n + 1).choose i : ℂ) * (n.descFactorial i : ℂ) *
        iteratedDeriv (n - i) (fun z : ℂ => Polynomial.eval z P.derivative) 1) /
    (n.factorial : ℂ)

theorem riemannXiLiPolynomialContribution_eq
    {P : Polynomial ℂ} (hdegree : P.degree ≤ 1) (n : ℕ) :
    riemannXiLiPolynomialContribution n P =
      (n + 1 : ℂ) * Polynomial.eval 1 P.derivative := by
  rw [riemannXiLiPolynomialContribution,
    polynomial_derivative_eq_C_eval_one_of_degree_le_one hdegree]
  simp only [Polynomial.eval_C]
  rw [Finset.sum_eq_single n]
  · simp only [Nat.choose_succ_self_right, Nat.cast_add, Nat.cast_one,
      Nat.descFactorial_self, tsub_self, iteratedDeriv_zero]
    have hnfac : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    apply (div_eq_iff hnfac).2
    ring
  · intro i hi hin
    have hi_le : i ≤ n := by simpa using Finset.mem_range.mp hi
    have hsub : n - i ≠ 0 := by omega
    simp [iteratedDeriv_const, hsub]
  · simp

theorem liCoefficientCandidate_eq_polynomial_add_tsum_zeroContribution
    {P : Polynomial ℂ}
    (hfac : ∀ z : ℂ, riemannXi z = Complex.exp (Polynomial.eval z P) *
      Complex.Hadamard.divisorCanonicalProduct 1 riemannXi (Set.univ : Set ℂ) z)
    (n : ℕ) :
    liCoefficientCandidate n =
      riemannXiLiPolynomialContribution n P +
        ∑' p : RiemannXiDivisorZeroIndex, riemannXiLiZeroContribution n p := by
  rw [liCoefficientCandidate_eq_finset_sum_iteratedDeriv_logDeriv]
  simp_rw [iteratedDeriv_logDeriv_riemannXi_eq_hadamard_zero_formula hfac]
  unfold riemannXiLiPolynomialContribution riemannXiLiZeroContribution
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, add_div]
  congr 1
  rw [tsum_div_const]
  rw [Summable.tsum_finsetSum]
  · congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [tsum_mul_left]
  · intro i hi
    exact (summable_riemannXiLogDerivZeroDerivativeTerm_one (n - i)).mul_left
      (((n + 1).choose i : ℂ) * (n.descFactorial i : ℂ))

theorem zero_mem_riemannXiNonzeroSet : (0 : ℂ) ∈ riemannXiNonzeroSet :=
  riemannXi_zero_ne_zero

theorem deriv_riemannXi_zero_eq_neg_one :
    deriv riemannXi 0 = -deriv riemannXi 1 := by
  have hcomp : HasDerivAt (fun z : ℂ => riemannXi (1 - z))
      (-deriv riemannXi 1) 0 := by
    apply HasDerivAt.comp_const_sub (1 : ℂ) 0
    simpa using (analyticAt_riemannXi 1).differentiableAt.hasDerivAt
  have heq : (fun z : ℂ => riemannXi (1 - z)) = riemannXi := by
    funext z
    exact riemannXi_one_sub z
  rw [heq] at hcomp
  exact hcomp.deriv

theorem logDeriv_riemannXi_zero_eq_neg_one :
    logDeriv riemannXi 0 = -logDeriv riemannXi 1 := by
  unfold logDeriv
  change deriv riemannXi 0 / riemannXi 0 =
    -(deriv riemannXi 1 / riemannXi 1)
  rw [deriv_riemannXi_zero_eq_neg_one, riemannXi_zero, riemannXi_one]
  ring

theorem hadamard_polynomial_add_half_reciprocal_tsum_eq_zero
    {P : Polynomial ℂ} (hdegree : P.degree ≤ 1)
    (hfac : ∀ z : ℂ, riemannXi z = Complex.exp (Polynomial.eval z P) *
      Complex.Hadamard.divisorCanonicalProduct 1 riemannXi (Set.univ : Set ℂ) z) :
    Polynomial.eval 1 P.derivative +
        (∑' p : RiemannXiDivisorZeroIndex, riemannXiLiReciprocalPair p) / 2 = 0 := by
  have hzero := riemannXi_logDeriv_eq_polynomial_derivative_add_tsum
    hfac zero_mem_riemannXiNonzeroSet
  have hone := riemannXi_logDeriv_eq_polynomial_derivative_add_tsum
    hfac one_mem_riemannXiNonzeroSet
  have hP := polynomial_derivative_eq_C_eval_one_of_degree_le_one hdegree
  have hzeroTerm : ∀ p : RiemannXiDivisorZeroIndex,
      riemannXiLogDerivZeroTerm p 0 = 0 := by
    intro p
    unfold riemannXiLogDerivZeroTerm
    have hp0 := Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p
    field_simp [hp0]
    ring
  have hzeroSum' :
      (∑' p : RiemannXiDivisorZeroIndex, riemannXiLogDerivZeroTerm p 0) = 0 := by
    rw [show (fun p : RiemannXiDivisorZeroIndex => riemannXiLogDerivZeroTerm p 0) =
        fun _ => 0 by funext p; exact hzeroTerm p]
    simp
  rw [hzeroSum'] at hzero
  simp only [add_zero] at hzero
  have hPconst : Polynomial.eval 0 P.derivative = Polynomial.eval 1 P.derivative := by
    rw [hP]
    simp
  change logDeriv riemannXi 1 = Polynomial.eval 1 P.derivative +
    ∑' p : RiemannXiDivisorZeroIndex, riemannXiLiReciprocalPair p at hone
  rw [logDeriv_riemannXi_zero_eq_neg_one, hone, hPconst] at hzero
  have htwo : 2 * Polynomial.eval 1 P.derivative +
      (∑' p : RiemannXiDivisorZeroIndex, riemannXiLiReciprocalPair p) = 0 := by
    calc
      2 * Polynomial.eval 1 P.derivative +
          (∑' p : RiemannXiDivisorZeroIndex, riemannXiLiReciprocalPair p) =
        -(-(Polynomial.eval 1 P.derivative +
          ∑' p : RiemannXiDivisorZeroIndex, riemannXiLiReciprocalPair p) -
            Polynomial.eval 1 P.derivative) := by ring
      _ = 0 := by rw [hzero]; ring
  calc
    Polynomial.eval 1 P.derivative +
        (∑' p : RiemannXiDivisorZeroIndex, riemannXiLiReciprocalPair p) / 2 =
      (2 * Polynomial.eval 1 P.derivative +
        ∑' p : RiemannXiDivisorZeroIndex, riemannXiLiReciprocalPair p) / 2 := by ring
    _ = 0 := by rw [htwo]; norm_num

theorem tsum_reflect_average_eq_symmetrized_add_reciprocal (n : ℕ) :
    (∑' p : RiemannXiDivisorZeroIndex,
        (riemannXiLiZeroContribution n p +
          riemannXiLiZeroContribution n (riemannXiDivisorZeroReflectEquiv p)) / 2) =
      (∑' p : RiemannXiDivisorZeroIndex, riemannXiSymmetrizedLiZeroTerm n p) +
        ((n + 1 : ℂ) / 2) *
          ∑' p : RiemannXiDivisorZeroIndex, riemannXiLiReciprocalPair p := by
  rw [show (fun p : RiemannXiDivisorZeroIndex =>
      (riemannXiLiZeroContribution n p +
        riemannXiLiZeroContribution n (riemannXiDivisorZeroReflectEquiv p)) / 2) =
      fun p => riemannXiSymmetrizedLiZeroTerm n p +
        ((n + 1 : ℂ) / 2) * riemannXiLiReciprocalPair p by
    funext p
    exact riemannXiLiZeroContribution_reflect_average n p]
  rw [(summable_riemannXiSymmetrizedLiZeroTerm n).tsum_add
    (summable_riemannXiLiReciprocalPair.mul_left ((n + 1 : ℂ) / 2))]
  rw [tsum_mul_left]

/-- Every derivative-defined project Li coefficient equals the summable raw zero term paired
under the functional-equation involution, with analytic multiplicity. -/
theorem liCoefficientCandidate_eq_tsum_riemannXiSymmetrizedLiZeroTerm (n : ℕ) :
    liCoefficientCandidate n =
      ∑' p : RiemannXiDivisorZeroIndex, riemannXiSymmetrizedLiZeroTerm n p := by
  obtain ⟨P, hdegree, hfac⟩ := exists_riemannXi_hadamard_factorization
  rw [liCoefficientCandidate_eq_polynomial_add_tsum_zeroContribution hfac]
  rw [riemannXiLiPolynomialContribution_eq hdegree]
  rw [tsum_riemannXiLiZeroContribution_eq_reflect_average]
  rw [tsum_reflect_average_eq_symmetrized_add_reciprocal]
  have hcancel := hadamard_polynomial_add_half_reciprocal_tsum_eq_zero hdegree hfac
  calc
    (n + 1 : ℂ) * Polynomial.eval 1 P.derivative +
        ((∑' p : RiemannXiDivisorZeroIndex, riemannXiSymmetrizedLiZeroTerm n p) +
          ((n + 1 : ℂ) / 2) *
            ∑' p : RiemannXiDivisorZeroIndex, riemannXiLiReciprocalPair p) =
      (∑' p : RiemannXiDivisorZeroIndex, riemannXiSymmetrizedLiZeroTerm n p) +
        (n + 1 : ℂ) *
          (Polynomial.eval 1 P.derivative +
            (∑' p : RiemannXiDivisorZeroIndex, riemannXiLiReciprocalPair p) / 2) := by ring
    _ = ∑' p : RiemannXiDivisorZeroIndex, riemannXiSymmetrizedLiZeroTerm n p := by
      rw [hcancel]
      ring

theorem liRawZeroTerm_add_reflect_eq_mul
    (m : ℕ) {ρ : ℂ} (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1) :
    liRawZeroTerm m ρ + liRawZeroTerm m (1 - ρ) =
      liRawZeroTerm m ρ * liRawZeroTerm m (1 - ρ) := by
  have hxbase : 1 - 1 / ρ = (ρ - 1) / ρ := by
    field_simp [hρ0]
  have hybase : 1 - 1 / (1 - ρ) = ρ / (ρ - 1) := by
    (field_simp [sub_ne_zero.mpr hρ1.symm, sub_ne_zero.mpr hρ1]; ring)
  have hbase : 1 - 1 / (1 - ρ) = (1 - 1 / ρ)⁻¹ := by
    rw [hxbase, hybase, inv_div]
  have hx : (1 - 1 / ρ) ^ m ≠ 0 := by
    apply pow_ne_zero
    rw [hxbase]
    exact div_ne_zero (sub_ne_zero.mpr hρ1) hρ0
  have hinv (x : ℂ) (hx0 : x ≠ 0) :
      (1 - x) + (1 - x⁻¹) = (1 - x) * (1 - x⁻¹) := by
    field_simp [hx0]
    ring
  unfold liRawZeroTerm
  rw [hbase, inv_pow]
  exact hinv _ hx

theorem RiemannHypothesis.one_sub_riemannXiDivisorZeroValue_eq_conj
    (hRH : RiemannHypothesis) (p : RiemannXiDivisorZeroIndex) :
    1 - riemannXiDivisorZeroValue p = conj (riemannXiDivisorZeroValue p) := by
  have hline := RiemannHypothesis.nontrivial_zero_on_line hRH
    (riemannXiDivisorZeroIndex_val_isNontrivialZero p)
  change (riemannXiDivisorZeroValue p).re = 1 / 2 at hline
  apply Complex.ext
  · simp [hline]
    ring
  · simp

theorem liRawZeroTerm_conj (m : ℕ) (ρ : ℂ) :
    liRawZeroTerm m (conj ρ) = conj (liRawZeroTerm m ρ) := by
  simp [liRawZeroTerm]

theorem RiemannHypothesis.riemannXiSymmetrizedLiZeroTerm_eq_normSq
    (hRH : RiemannHypothesis) (n : ℕ) (p : RiemannXiDivisorZeroIndex) :
    riemannXiSymmetrizedLiZeroTerm n p =
      (Complex.normSq
        (liRawZeroTerm (n + 1) (riemannXiDivisorZeroValue p)) : ℂ) / 2 := by
  have hρ0 : riemannXiDivisorZeroValue p ≠ 0 :=
    Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p
  have hρ1 : riemannXiDivisorZeroValue p ≠ 1 :=
    (sub_ne_zero.mp (one_sub_riemannXiDivisorZeroValue_ne_zero p)).symm
  unfold riemannXiSymmetrizedLiZeroTerm
  rw [show liRawZeroTerm (n + 1) (riemannXiDivisorZeroValue p) +
      liRawZeroTerm (n + 1) (1 - riemannXiDivisorZeroValue p) =
      liRawZeroTerm (n + 1) (riemannXiDivisorZeroValue p) *
        liRawZeroTerm (n + 1) (1 - riemannXiDivisorZeroValue p) by
    exact liRawZeroTerm_add_reflect_eq_mul (n + 1) hρ0 hρ1]
  rw [RiemannHypothesis.one_sub_riemannXiDivisorZeroValue_eq_conj hRH p]
  rw [liRawZeroTerm_conj]
  rw [Complex.mul_conj]

theorem RiemannHypothesis.liCoefficientCandidate_eq_tsum_normSq
    (hRH : RiemannHypothesis) (n : ℕ) :
    liCoefficientCandidate n =
      ∑' p : RiemannXiDivisorZeroIndex,
        (Complex.normSq
          (liRawZeroTerm (n + 1) (riemannXiDivisorZeroValue p)) : ℂ) / 2 := by
  rw [liCoefficientCandidate_eq_tsum_riemannXiSymmetrizedLiZeroTerm]
  apply tsum_congr
  exact RiemannHypothesis.riemannXiSymmetrizedLiZeroTerm_eq_normSq hRH n

private theorem RiemannHypothesis.summable_liZeroTerm_normSq
    (hRH : RiemannHypothesis) (n : ℕ) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      (Complex.normSq
        (liRawZeroTerm (n + 1) (riemannXiDivisorZeroValue p)) : ℂ) / 2) := by
  apply (summable_riemannXiSymmetrizedLiZeroTerm n).congr
  exact RiemannHypothesis.riemannXiSymmetrizedLiZeroTerm_eq_normSq hRH n

theorem RiemannHypothesis.liCoefficientCandidate_im_eq_zero
    (hRH : RiemannHypothesis) (n : ℕ) :
    (liCoefficientCandidate n).im = 0 := by
  rw [RiemannHypothesis.liCoefficientCandidate_eq_tsum_normSq hRH]
  rw [Complex.im_tsum (RiemannHypothesis.summable_liZeroTerm_normSq hRH n)]
  simp

theorem RiemannHypothesis.liCoefficientCandidate_re_nonneg
    (hRH : RiemannHypothesis) (n : ℕ) :
    0 ≤ (liCoefficientCandidate n).re := by
  rw [RiemannHypothesis.liCoefficientCandidate_eq_tsum_normSq hRH]
  rw [Complex.re_tsum (RiemannHypothesis.summable_liZeroTerm_normSq hRH n)]
  apply tsum_nonneg
  intro p
  simpa using div_nonneg
    (Complex.normSq_nonneg
      (liRawZeroTerm (n + 1) (riemannXiDivisorZeroValue p))) (by norm_num : (0 : ℝ) ≤ 2)

end

end LeanLab.Riemann
