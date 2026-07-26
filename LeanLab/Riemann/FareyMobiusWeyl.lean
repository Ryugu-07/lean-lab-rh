import LeanLab.Riemann.RedhefferMertensDeterminant
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

set_option linter.style.header false

/-!
# The finite Farey--Mobius transform

This file uses the positive-pair convention `0 < a ≤ q ≤ N`. Thus `0 / 1` is absent and
`1 / 1` occurs once. The first coordinate of a registered pair is its denominator.
-/

namespace LeanLab.Riemann

open scoped ArithmeticFunction.Moebius BigOperators

/-- Positive numerators coprime to `q`, represented on the source interval `1, ..., q`. -/
def fareyNumerators (q : ℕ) : Finset ℕ :=
  (Finset.Ico 1 (q + 1)).filter fun a => Nat.Coprime a q

/-- Reduced positive Farey pairs `(q, a)` with `0 < a ≤ q ≤ N`. -/
def fareyPairs (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Ico 1 (N + 1)).product (Finset.Ico 1 (N + 1))).filter fun p =>
    p.2 ≤ p.1 ∧ Nat.Coprime p.2 p.1

/-- The rational represented by a denominator--numerator pair `(q, a)`. -/
def fareyValue (p : ℕ × ℕ) : ℚ :=
  (p.2 : ℚ) / (p.1 : ℚ)

/-- The complete numerator block `∑_{a=1}^n f(a/n)`. -/
def fareyFullBlock (f : ℚ → ℂ) (n : ℕ) : ℂ :=
  ∑ a ∈ Finset.Ico 1 (n + 1), f ((a : ℚ) / (n : ℚ))

/-- The reduced numerator block at the fixed denominator `q`. -/
def fareyReducedBlock (f : ℚ → ℂ) (q : ℕ) : ℂ :=
  ∑ a ∈ fareyNumerators q, f ((a : ℚ) / (q : ℚ))

/-- The test-function sum over all reduced positive Farey pairs of order `N`. -/
def fareySum (f : ℚ → ℂ) (N : ℕ) : ℂ :=
  ∑ p ∈ fareyPairs N, f (fareyValue p)

/-- The first Weyl frequency on rational points. -/
noncomputable def fareyFrequencyOne (x : ℚ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))

private theorem fareyFrequencyOne_div_eq_pow {a n : ℕ} (hn : 0 < n) :
    fareyFrequencyOne ((a : ℚ) / (n : ℚ)) =
      Complex.exp (2 * Real.pi * Complex.I / (n : ℂ)) ^ a := by
  rw [fareyFrequencyOne, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp [Nat.ne_of_gt hn]

@[simp] theorem mem_fareyNumerators {q a : ℕ} :
    a ∈ fareyNumerators q ↔ 1 ≤ a ∧ a ≤ q ∧ Nat.Coprime a q := by
  simp only [fareyNumerators, Finset.mem_filter, Finset.mem_Ico, Nat.lt_add_one_iff]
  tauto

@[simp] theorem mem_fareyPairs {N q a : ℕ} :
    (q, a) ∈ fareyPairs N ↔
      1 ≤ q ∧ q ≤ N ∧ 1 ≤ a ∧ a ≤ q ∧ Nat.Coprime a q := by
  constructor
  · intro h
    have hp := Finset.mem_filter.mp h
    have hprod := Finset.mem_product.mp hp.1
    have hq := Finset.mem_Ico.mp hprod.1
    have ha := Finset.mem_Ico.mp hprod.2
    exact ⟨hq.1, Nat.lt_add_one_iff.mp hq.2, ha.1, hp.2.1, hp.2.2⟩
  · rintro ⟨hq1, hqN, ha1, haq, hcop⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_product.mpr
      exact ⟨Finset.mem_Ico.mpr ⟨hq1, Nat.lt_add_one_iff.mpr hqN⟩,
        Finset.mem_Ico.mpr ⟨ha1, Nat.lt_add_one_iff.mpr (haq.trans hqN)⟩⟩
    · exact ⟨haq, hcop⟩

theorem fareyPairs_denominator_pos {N q a : ℕ} (h : (q, a) ∈ fareyPairs N) :
    0 < q :=
  (mem_fareyPairs.mp h).1

theorem fareyPairs_numerator_pos {N q a : ℕ} (h : (q, a) ∈ fareyPairs N) :
    0 < a :=
  (mem_fareyPairs.mp h).2.2.1

theorem fareyPairs_numerator_le_denominator {N q a : ℕ}
    (h : (q, a) ∈ fareyPairs N) :
    a ≤ q :=
  (mem_fareyPairs.mp h).2.2.2.1

theorem fareyPairs_denominator_le {N q a : ℕ} (h : (q, a) ∈ fareyPairs N) :
    q ≤ N :=
  (mem_fareyPairs.mp h).2.1

theorem fareyPairs_coprime {N q a : ℕ} (h : (q, a) ∈ fareyPairs N) :
    Nat.Coprime a q :=
  (mem_fareyPairs.mp h).2.2.2.2

@[simp] theorem fareyNumerators_card (q : ℕ) :
    (fareyNumerators q).card = Nat.totient q := by
  simpa only [fareyNumerators, Nat.add_comm, Nat.coprime_comm] using
    Nat.filter_coprime_Ico_eq_totient q 1

theorem fareyPairs_card (N : ℕ) :
    (fareyPairs N).card = ∑ q ∈ Finset.Ico 1 (N + 1), Nat.totient q := by
  rw [Finset.card_eq_sum_ones]
  rw [Finset.sum_finset_product (fareyPairs N) (Finset.Ico 1 (N + 1))
    fareyNumerators]
  · simp
  · intro p
    rcases p with ⟨q, a⟩
    simp only [mem_fareyPairs, mem_fareyNumerators, Finset.mem_Ico, Nat.lt_add_one_iff]
    omega

theorem fareySum_eq_sum_reducedBlocks (f : ℚ → ℂ) (N : ℕ) :
    fareySum f N =
      ∑ q ∈ Finset.Ico 1 (N + 1), fareyReducedBlock f q := by
  rw [fareySum, Finset.sum_finset_product (fareyPairs N) (Finset.Ico 1 (N + 1))
    fareyNumerators]
  · rfl
  · intro p
    rcases p with ⟨q, a⟩
    simp only [mem_fareyPairs, mem_fareyNumerators, Finset.mem_Ico, Nat.lt_add_one_iff]
    omega

private theorem rat_div_gcd_ratio {a q : ℕ} (ha : 0 < a) (hq : 0 < q) :
    ((a / a.gcd q : ℕ) : ℚ) / ((q / a.gcd q : ℕ) : ℚ) =
      (a : ℚ) / (q : ℚ) := by
  have hgpos : 0 < a.gcd q := Nat.gcd_pos_of_pos_left q ha
  have hga : a.gcd q ∣ a := Nat.gcd_dvd_left a q
  have hgq : a.gcd q ∣ q := Nat.gcd_dvd_right a q
  have hqdiv : q / a.gcd q ≠ 0 :=
    Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd hq hgq) hgpos)
  apply (div_eq_div_iff (by exact_mod_cast hqdiv) (by exact_mod_cast Nat.ne_of_gt hq)).mpr
  exact_mod_cast (show (a / a.gcd q) * q = a * (q / a.gcd q) by
    calc
      (a / a.gcd q) * q =
          (a / a.gcd q) * ((q / a.gcd q) * a.gcd q) := by
            rw [Nat.div_mul_cancel hgq]
      _ = ((a / a.gcd q) * a.gcd q) * (q / a.gcd q) := by ac_rfl
      _ = a * (q / a.gcd q) := by rw [Nat.div_mul_cancel hga])

theorem fareyFullBlock_eq_sum_reducedBlocks_divisors
    (f : ℚ → ℂ) {q : ℕ} (hq : 0 < q) :
    fareyFullBlock f q =
      ∑ d ∈ q.divisors, fareyReducedBlock f d := by
  rw [fareyFullBlock]
  change
    (∑ a ∈ Finset.Ico 1 (q + 1), f ((a : ℚ) / (q : ℚ))) =
      ∑ d ∈ q.divisors,
        ∑ b ∈ fareyNumerators d, f ((b : ℚ) / (d : ℚ))
  rw [Finset.sum_sigma']
  refine Finset.sum_bij
    (fun a _ha => ⟨q / a.gcd q, a / a.gcd q⟩) ?_ ?_ ?_ ?_
  · intro a ha
    have haI := Finset.mem_Ico.mp ha
    have hapos : 0 < a := haI.1
    have hgpos : 0 < a.gcd q := Nat.gcd_pos_of_pos_left q hapos
    have hga : a.gcd q ∣ a := Nat.gcd_dvd_left a q
    have hgq : a.gcd q ∣ q := Nat.gcd_dvd_right a q
    apply Finset.mem_sigma.mpr
    constructor
    · exact Nat.mem_divisors.mpr
        ⟨Nat.div_dvd_of_dvd hgq, Nat.ne_of_gt hq⟩
    · apply mem_fareyNumerators.mpr
      exact
        ⟨Nat.div_pos (Nat.le_of_dvd hapos hga) hgpos,
          Nat.div_le_div_right (Nat.lt_add_one_iff.mp haI.2),
          Nat.coprime_div_gcd_div_gcd hgpos⟩
  · intro a₁ ha₁ a₂ ha₂ heq
    have ha₁pos : 0 < a₁ := (Finset.mem_Ico.mp ha₁).1
    have ha₂pos : 0 < a₂ := (Finset.mem_Ico.mp ha₂).1
    have hden :
        q / a₁.gcd q = q / a₂.gcd q :=
      congrArg Sigma.fst heq
    have hnum :
        a₁ / a₁.gcd q = a₂ / a₂.gcd q :=
      congrArg Sigma.snd heq
    have hreduced :
        ((a₁ / a₁.gcd q : ℕ) : ℚ) / ((q / a₁.gcd q : ℕ) : ℚ) =
          ((a₂ / a₂.gcd q : ℕ) : ℚ) / ((q / a₂.gcd q : ℕ) : ℚ) := by
      rw [hden, hnum]
    have hrat :
        (a₁ : ℚ) / (q : ℚ) = (a₂ : ℚ) / (q : ℚ) :=
      (rat_div_gcd_ratio ha₁pos hq).symm.trans
        (hreduced.trans (rat_div_gcd_ratio ha₂pos hq))
    have hcrossRat : (a₁ : ℚ) * (q : ℚ) = (a₂ : ℚ) * (q : ℚ) :=
      (div_eq_div_iff (by exact_mod_cast Nat.ne_of_gt hq)
        (by exact_mod_cast Nat.ne_of_gt hq)).mp hrat
    have hcross : a₁ * q = a₂ * q := by
      exact_mod_cast hcrossRat
    exact Nat.eq_of_mul_eq_mul_right hq hcross
  · intro z hz
    rcases z with ⟨d, b⟩
    have hz' := Finset.mem_sigma.mp hz
    have hd := Nat.mem_divisors.mp hz'.1
    have hb := mem_fareyNumerators.mp hz'.2
    let c := q / d
    let a := b * c
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd.1 hq
    have hcpos : 0 < c := Nat.div_pos (Nat.le_of_dvd hq hd.1) hdpos
    have hdc : d * c = q := by
      exact Nat.mul_div_cancel' hd.1
    have hapos : 0 < a := Nat.mul_pos hb.1 hcpos
    have hale : a ≤ q := by
      dsimp only [a]
      rw [← hdc]
      exact Nat.mul_le_mul_right c hb.2.1
    have hamem : a ∈ Finset.Ico 1 (q + 1) :=
      Finset.mem_Ico.mpr ⟨hapos, Nat.lt_add_one_iff.mpr hale⟩
    refine ⟨a, hamem, ?_⟩
    have hgcd : a.gcd q = c := by
      dsimp only [a]
      rw [← hdc, Nat.gcd_mul_right, hb.2.2.gcd_eq_one, one_mul]
    apply Sigma.ext
    · dsimp only
      rw [hgcd, ← hdc, Nat.mul_div_left d hcpos]
    · dsimp only [a]
      rw [hgcd]
      exact (Nat.mul_div_left b hcpos).heq
  · intro a ha
    exact congrArg f (rat_div_gcd_ratio (Finset.mem_Ico.mp ha).1 hq).symm

theorem fareyReducedBlock_eq_moebiusAntidiagonal
    (f : ℚ → ℂ) {q : ℕ} (hq : 0 < q) :
    (∑ x ∈ q.divisorsAntidiagonal,
        (ArithmeticFunction.moebius x.1 : ℂ) * fareyFullBlock f x.2) =
      fareyReducedBlock f q := by
  exact
    ((ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
      (f := fareyReducedBlock f) (g := fareyFullBlock f)).mp
        (fun n hn => (fareyFullBlock_eq_sum_reducedBlocks_divisors f hn).symm)) q hq

theorem sum_Ico_divisorsAntidiagonal_eq_sum_Ico_div
    {A : Type*} [AddCommMonoid A] (F : ℕ → ℕ → A) (N : ℕ) :
    (∑ q ∈ Finset.Ico 1 (N + 1),
        ∑ x ∈ q.divisorsAntidiagonal, F x.1 x.2) =
      ∑ n ∈ Finset.Ico 1 (N + 1),
        ∑ d ∈ Finset.Ico 1 (N / n + 1), F d n := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij
    (fun z _hz => ⟨z.2.2, z.2.1⟩) ?_ ?_ ?_ ?_
  · intro z hz
    rcases z with ⟨q, x⟩
    rcases x with ⟨d, n⟩
    have hz' := Finset.mem_sigma.mp hz
    have hqI := Finset.mem_Ico.mp hz'.1
    have hprod := Nat.mem_divisorsAntidiagonal.mp hz'.2
    have hqpos : 0 < q := hqI.1
    have hdnpos : 0 < d * n := by simpa [hprod.1] using hqpos
    have hdpos : 0 < d := Nat.pos_of_mul_pos_right hdnpos
    have hnpos : 0 < n := Nat.pos_of_mul_pos_left hdnpos
    apply Finset.mem_sigma.mpr
    constructor
    · apply Finset.mem_Ico.mpr
      exact
        ⟨hnpos,
          Nat.lt_add_one_iff.mpr
            ((Nat.le_mul_of_pos_left n hdpos).trans
              (hprod.1.le.trans (Nat.lt_add_one_iff.mp hqI.2)))⟩
    · apply Finset.mem_Ico.mpr
      refine ⟨hdpos, Nat.lt_add_one_iff.mpr ?_⟩
      apply (Nat.le_div_iff_mul_le hnpos).mpr
      exact hprod.1.le.trans (Nat.lt_add_one_iff.mp hqI.2)
  · intro z₁ hz₁ z₂ hz₂ heq
    rcases z₁ with ⟨q₁, ⟨d₁, n₁⟩⟩
    rcases z₂ with ⟨q₂, ⟨d₂, n₂⟩⟩
    have hp₁ :=
      (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp hz₁).2).1
    have hp₂ :=
      (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp hz₂).2).1
    cases heq
    have hq : q₁ = q₂ := hp₁.symm.trans hp₂
    subst q₂
    rfl
  · intro z hz
    rcases z with ⟨n, d⟩
    have hz' := Finset.mem_sigma.mp hz
    have hnI := Finset.mem_Ico.mp hz'.1
    have hdI := Finset.mem_Ico.mp hz'.2
    have hnpos : 0 < n := hnI.1
    have hdpos : 0 < d := hdI.1
    have hmul : d * n ≤ N :=
      (Nat.le_div_iff_mul_le hnpos).mp (Nat.lt_add_one_iff.mp hdI.2)
    let q := d * n
    let x : ℕ × ℕ := (d, n)
    have hqmem : q ∈ Finset.Ico 1 (N + 1) :=
      Finset.mem_Ico.mpr
        ⟨Nat.mul_pos hdpos hnpos, Nat.lt_add_one_iff.mpr hmul⟩
    have hxmem : x ∈ q.divisorsAntidiagonal := by
      apply Nat.mem_divisorsAntidiagonal.mpr
      exact ⟨rfl, Nat.ne_of_gt (Nat.mul_pos hdpos hnpos)⟩
    refine ⟨⟨q, x⟩, Finset.mem_sigma.mpr ⟨hqmem, hxmem⟩, ?_⟩
    rfl
  · intro z hz
    rfl

theorem finiteMertens_eq_sum_Ico (N : ℕ) :
    finiteMertens N =
      ∑ d ∈ Finset.Ico 1 (N + 1), ArithmeticFunction.moebius d := by
  rw [finiteMertens, Fin.sum_univ_eq_sum_range
    (fun k => ArithmeticFunction.moebius (k + 1))]
  refine Finset.sum_nbij (fun k => k + 1) ?_ ?_ ?_ ?_
  · intro k hk
    apply Finset.mem_Ico.mpr
    exact ⟨Nat.le_add_left 1 k, Nat.add_lt_add_right (Finset.mem_range.mp hk) 1⟩
  · intro a ha b hb hab
    exact Nat.add_right_cancel (by simpa only using hab)
  · intro d hd
    have hdI := Finset.mem_Ico.mp hd
    refine ⟨d - 1, Finset.mem_range.mpr ?_, ?_⟩
    · omega
    · exact Nat.sub_add_cancel hdI.1
  · intro k hk
    rfl

theorem finiteMertens_cast_eq_sum_Ico (N : ℕ) :
    (finiteMertens N : ℂ) =
      ∑ d ∈ Finset.Ico 1 (N + 1), (ArithmeticFunction.moebius d : ℂ) := by
  exact_mod_cast finiteMertens_eq_sum_Ico N

theorem farey_sum_eq_mertens_transform (f : ℚ → ℂ) (N : ℕ) :
    fareySum f N =
      ∑ n ∈ Finset.Ico 1 (N + 1),
        (finiteMertens (N / n) : ℂ) * fareyFullBlock f n := by
  rw [fareySum_eq_sum_reducedBlocks]
  calc
    (∑ q ∈ Finset.Ico 1 (N + 1), fareyReducedBlock f q) =
        ∑ q ∈ Finset.Ico 1 (N + 1),
          ∑ x ∈ q.divisorsAntidiagonal,
            (ArithmeticFunction.moebius x.1 : ℂ) * fareyFullBlock f x.2 := by
              apply Finset.sum_congr rfl
              intro q hq
              exact
                (fareyReducedBlock_eq_moebiusAntidiagonal f
                  (Finset.mem_Ico.mp hq).1).symm
    _ = ∑ n ∈ Finset.Ico 1 (N + 1),
          ∑ d ∈ Finset.Ico 1 (N / n + 1),
            (ArithmeticFunction.moebius d : ℂ) * fareyFullBlock f n :=
      sum_Ico_divisorsAntidiagonal_eq_sum_Ico_div
        (fun d n => (ArithmeticFunction.moebius d : ℂ) * fareyFullBlock f n) N
    _ = ∑ n ∈ Finset.Ico 1 (N + 1),
          (finiteMertens (N / n) : ℂ) * fareyFullBlock f n := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [← Finset.sum_mul, ← finiteMertens_cast_eq_sum_Ico]

private theorem fareyRoot_pow_eq_one {n : ℕ} (hn : 0 < n) :
    Complex.exp (2 * Real.pi * Complex.I / (n : ℂ)) ^ n = 1 := by
  rw [← Complex.exp_nat_mul]
  have harg :
      (n : ℂ) * (2 * Real.pi * Complex.I / (n : ℂ)) =
        2 * Real.pi * Complex.I := by
    field_simp [Nat.ne_of_gt hn]
  rw [harg, Complex.exp_two_pi_mul_I]

private theorem fareyRoot_ne_one {n : ℕ} (hn : 1 < n) :
    Complex.exp (2 * Real.pi * Complex.I / (n : ℂ)) ≠ 1 := by
  intro hroot
  have hdiv : n ∣ 1 := by
    apply
      (Complex.exp_two_pi_mul_I_mul_div_eq_one_iff
        (k := 1) (N := n) (Nat.ne_of_gt (lt_trans Nat.zero_lt_one hn))).mp
    simpa only [Nat.cast_one, mul_one] using hroot
  exact (Nat.not_le_of_gt hn) (Nat.le_of_dvd Nat.zero_lt_one hdiv)

private theorem fareyRoot_geom_sum_eq_zero {n : ℕ} (hn : 1 < n) :
    ∑ k ∈ Finset.range n,
      Complex.exp (2 * Real.pi * Complex.I / (n : ℂ)) ^ k = 0 := by
  let z := Complex.exp (2 * Real.pi * Complex.I / (n : ℂ))
  have hmul := geom_sum_mul z n
  have hzpow : z ^ n = 1 := fareyRoot_pow_eq_one (lt_trans Nat.zero_lt_one hn)
  have hzsub : z - 1 ≠ 0 := sub_ne_zero.mpr (fareyRoot_ne_one hn)
  rw [hzpow, sub_self] at hmul
  exact (mul_eq_zero.mp hmul).resolve_right hzsub

@[simp] theorem fareyFullBlock_frequencyOne_one :
    fareyFullBlock fareyFrequencyOne 1 = 1 := by
  simp [fareyFullBlock, fareyFrequencyOne, Complex.exp_two_pi_mul_I]

theorem fareyFullBlock_frequencyOne_eq_zero {n : ℕ} (hn : 1 < n) :
    fareyFullBlock fareyFrequencyOne n = 0 := by
  let z := Complex.exp (2 * Real.pi * Complex.I / (n : ℂ))
  rw [fareyFullBlock]
  simp_rw [fareyFrequencyOne_div_eq_pow (lt_trans Nat.zero_lt_one hn)]
  calc
    (∑ a ∈ Finset.Ico 1 (n + 1), z ^ a) =
        ∑ k ∈ Finset.range n, z ^ (k + 1) := by
      symm
      refine Finset.sum_nbij (fun k => k + 1) ?_ ?_ ?_ ?_
      · intro k hk
        exact Finset.mem_Ico.mpr
          ⟨Nat.le_add_left 1 k, Nat.add_lt_add_right (Finset.mem_range.mp hk) 1⟩
      · intro a ha b hb hab
        exact Nat.add_right_cancel (by simpa only using hab)
      · intro a ha
        have haI := Finset.mem_Ico.mp ha
        refine ⟨a - 1, Finset.mem_range.mpr (by omega), ?_⟩
        exact Nat.sub_add_cancel haI.1
      · intro k hk
        rfl
    _ = z * ∑ k ∈ Finset.range n, z ^ k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [pow_succ']
    _ = 0 := by
      rw [fareyRoot_geom_sum_eq_zero hn, mul_zero]

theorem fareyReducedBlock_frequencyOne_eq_moebius {q : ℕ} (hq : 0 < q) :
    fareyReducedBlock fareyFrequencyOne q =
      (ArithmeticFunction.moebius q : ℂ) := by
  rw [← fareyReducedBlock_eq_moebiusAntidiagonal fareyFrequencyOne hq]
  rw [Finset.sum_eq_single (q, 1)]
  · simp
  · intro x hx hxne
    have hprod := Nat.mem_divisorsAntidiagonal.mp hx
    have hqpos : 0 < x.1 * x.2 := by simpa [hprod.1] using hq
    have hnpos : 0 < x.2 := Nat.pos_of_mul_pos_left hqpos
    have hnOne : x.2 ≠ 1 := by
      intro hn
      apply hxne
      apply Prod.ext
      · simpa [hn] using hprod.1
      · exact hn
    have hn : 1 < x.2 := by omega
    rw [fareyFullBlock_frequencyOne_eq_zero hn, mul_zero]
  · intro hnot
    exact (hnot
      (Nat.mem_divisorsAntidiagonal.mpr ⟨Nat.mul_one q, Nat.ne_of_gt hq⟩)).elim

theorem farey_frequency_one_sum_eq_finiteMertens (N : ℕ) :
    fareySum fareyFrequencyOne N = (finiteMertens N : ℂ) := by
  rw [farey_sum_eq_mertens_transform]
  by_cases hN : N = 0
  · subst N
    simp [finiteMertens]
  · rw [Finset.sum_eq_single 1]
    · simp
    · intro n hn hnOne
      have hnI := Finset.mem_Ico.mp hn
      have hnlt : 1 < n := by omega
      rw [fareyFullBlock_frequencyOne_eq_zero hnlt, mul_zero]
    · intro hnot
      exact (hnot (Finset.mem_Ico.mpr
        ⟨Nat.le_refl 1, Nat.lt_add_one_iff.mpr (Nat.one_le_iff_ne_zero.mpr hN)⟩)).elim

@[simp] theorem fareyFrequencyOneSum_zero :
    fareySum fareyFrequencyOne 0 = 0 := by
  rw [farey_frequency_one_sum_eq_finiteMertens]
  simp [finiteMertens]

@[simp] theorem fareyFrequencyOneSum_one :
    fareySum fareyFrequencyOne 1 = 1 := by
  rw [farey_frequency_one_sum_eq_finiteMertens]
  norm_num

@[simp] theorem fareyFrequencyOneSum_two :
    fareySum fareyFrequencyOne 2 = 0 := by
  rw [farey_frequency_one_sum_eq_finiteMertens]
  norm_num

theorem fareyValue_injective_on {N : ℕ} {p r : ℕ × ℕ}
    (hp : p ∈ fareyPairs N) (hr : r ∈ fareyPairs N)
    (hvalue : fareyValue p = fareyValue r) :
    p = r := by
  rcases p with ⟨q, a⟩
  rcases r with ⟨s, b⟩
  have hp' := mem_fareyPairs.mp hp
  have hr' := mem_fareyPairs.mp hr
  have hq : q ≠ 0 := Nat.ne_of_gt hp'.1
  have hs : s ≠ 0 := Nat.ne_of_gt hr'.1
  have hcrossRat : (a : ℚ) * (s : ℚ) = (b : ℚ) * (q : ℚ) := by
    apply (div_eq_div_iff (by exact_mod_cast hq) (by exact_mod_cast hs)).mp
    simpa only [fareyValue] using hvalue
  have hcross : a * s = b * q := by
    exact_mod_cast hcrossRat
  have hq_dvd_s : q ∣ s := by
    apply (hp'.2.2.2.2.symm.dvd_mul_left).mp
    rw [hcross]
    exact dvd_mul_left q b
  have hs_dvd_q : s ∣ q := by
    apply (hr'.2.2.2.2.symm.dvd_mul_left).mp
    rw [← hcross]
    exact dvd_mul_left s a
  have hqs : q = s := Nat.dvd_antisymm hq_dvd_s hs_dvd_q
  subst s
  have hab : a = b := by
    exact Nat.eq_of_mul_eq_mul_right hp'.1 (by simpa only [Nat.mul_comm] using hcross)
  subst b
  rfl

@[simp] theorem fareyPairs_zero :
    fareyPairs 0 = ∅ := by
  simp [fareyPairs]

@[simp] theorem fareyPairs_one :
    fareyPairs 1 = {(1, 1)} := by
  ext p
  rcases p with ⟨q, a⟩
  simp only [mem_fareyPairs, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · omega
  · rintro ⟨rfl, rfl⟩
    norm_num

@[simp] theorem fareyZeroNumerator_not_mem (N : ℕ) :
    (1, 0) ∉ fareyPairs N := by
  simp

@[simp] theorem fareyOneOne_mem_iff (N : ℕ) :
    (1, 1) ∈ fareyPairs N ↔ 1 ≤ N := by
  simp

@[simp] theorem fareyPairs_two :
    fareyPairs 2 = {(1, 1), (2, 1)} := by
  ext p
  rcases p with ⟨q, a⟩
  simp only [mem_fareyPairs, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · intro h
    have hq : q = 1 ∨ q = 2 := by omega
    rcases hq with rfl | rfl
    · have ha : a = 1 := by omega
      simp [ha]
    · have ha : a = 1 ∨ a = 2 := by omega
      rcases ha with rfl | rfl
      · simp
      · norm_num at h
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

@[simp] theorem fareySum_zero (f : ℚ → ℂ) :
    fareySum f 0 = 0 := by
  simp [fareySum]

@[simp] theorem fareySum_one (f : ℚ → ℂ) :
    fareySum f 1 = f 1 := by
  simp [fareySum, fareyValue]

/-- The exact finite arithmetic endpoint at the entrance to the Farey discrepancy route. -/
structure FareyMobiusWeylCertificate : Prop where
  pairMembership :
    ∀ {N q a}, (q, a) ∈ fareyPairs N ↔
      1 ≤ q ∧ q ≤ N ∧ 1 ≤ a ∧ a ≤ q ∧ Nat.Coprime a q
  reducedValueInjective :
    ∀ {N p r}, p ∈ fareyPairs N → r ∈ fareyPairs N →
      fareyValue p = fareyValue r → p = r
  pairCardinality :
    ∀ N, (fareyPairs N).card =
      ∑ q ∈ Finset.Ico 1 (N + 1), Nat.totient q
  mertensTransform :
    ∀ f N, fareySum f N =
      ∑ n ∈ Finset.Ico 1 (N + 1),
        (finiteMertens (N / n) : ℂ) * fareyFullBlock f n
  primitiveFrequencyOne :
    ∀ {q}, 0 < q →
      fareyReducedBlock fareyFrequencyOne q =
        (ArithmeticFunction.moebius q : ℂ)
  totalFrequencyOne :
    ∀ N, fareySum fareyFrequencyOne N = (finiteMertens N : ℂ)
  zeroNumeratorExcluded :
    ∀ N, (1, 0) ∉ fareyPairs N
  oneOneExactly :
    ∀ N, (1, 1) ∈ fareyPairs N ↔ 1 ≤ N

theorem fareyMobiusWeyl_endpoint :
    FareyMobiusWeylCertificate where
  pairMembership := mem_fareyPairs
  reducedValueInjective := fareyValue_injective_on
  pairCardinality := fareyPairs_card
  mertensTransform := farey_sum_eq_mertens_transform
  primitiveFrequencyOne := fareyReducedBlock_frequencyOne_eq_moebius
  totalFrequencyOne := farey_frequency_one_sum_eq_finiteMertens
  zeroNumeratorExcluded := fareyZeroNumerator_not_mem
  oneOneExactly := fareyOneOne_mem_iff

end LeanLab.Riemann
