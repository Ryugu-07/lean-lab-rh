import LeanLab.Riemann.ConreyCharacterSumRationality
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.ZetaValues

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The actual modulo-seven flat branch in Conrey's character sum

This module audits the flat-prefix branch in Conrey's 2024 character-sum route using the genuine
Legendre character modulo seven. The modulus is `7 mod 8`, outside the paper's RH-imitation family
`3 mod 8`; the scope separation is part of the formal result.
-/

open scoped BigOperators

namespace LeanLab.Riemann

noncomputable section

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- The genuine quadratic character modulo seven. -/
def conreySevenCharacter (n : ℕ) : ℤ :=
  legendreSym 7 n

/-- A concrete table for the period-seven quadratic character. -/
def conreySevenCharacterTable (n : ℕ) : ℤ :=
  match n % 7 with
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => -1
  | 4 => 1
  | 5 => -1
  | _ => -1

/-- The Legendre character modulo seven has the advertised exact period table. -/
theorem conreySevenCharacter_eq_table (n : ℕ) :
    conreySevenCharacter n = conreySevenCharacterTable n := by
  rw [conreySevenCharacter, legendreSym.mod, ← Int.natCast_mod]
  have hr : n % 7 < 7 := Nat.mod_lt _ (by decide)
  interval_cases h : n % 7 <;>
    simp only [conreySevenCharacterTable, h] <;> decide

/-- The prefix through three has the class-number mass used by the flat branch. -/
theorem conreySeven_prefixMass_three :
    conreyPrefixMass conreySevenCharacter 3 = 1 := by
  simp [conreyPrefixMass, conreySevenCharacter_eq_table, conreySevenCharacterTable,
    Finset.sum_Icc_succ_top]

/-- The first moment of the prefix through three vanishes exactly. -/
theorem conreySeven_prefixMoment_three :
    conreyPrefixMoment conreySevenCharacter 3 = 0 := by
  simp [conreyPrefixMoment, conreySevenCharacter_eq_table, conreySevenCharacterTable,
    Finset.sum_Icc_succ_top]

/-- The scale-independent value of the actual flat prefix. -/
theorem conreySeven_weightedPrefix_three (y : ℝ) :
    conreyWeightedPrefix conreySevenCharacter 3 y = 1 := by
  rw [conreyWeightedPrefix_eq_mass_of_moment_eq_zero conreySeven_prefixMoment_three,
    conreySeven_prefixMass_three]
  norm_num

/-- The discrete sine-transform constant for the modulo-seven character. -/
def conreySevenSineConstant : ℝ :=
  Real.sin (2 * Real.pi / 7) +
    Real.sin (4 * Real.pi / 7) -
      Real.sin (6 * Real.pi / 7)

private theorem conreySeven_sin_period_two (n : ℕ) :
    Real.sin (2 * Real.pi * n / 7) =
      Real.sin (2 * Real.pi * ((n % 7 : ℕ) : ℝ) / 7) := by
  have hn : (n : ℝ) = (n % 7 : ℕ) + 7 * (n / 7 : ℕ) := by
    exact_mod_cast (Nat.mod_add_div n 7).symm
  calc
    Real.sin (2 * Real.pi * n / 7) =
        Real.sin
          (2 * Real.pi * ((n % 7 : ℕ) : ℝ) / 7 +
            (n / 7 : ℕ) * (2 * Real.pi)) := by
      congr 1
      rw [hn]
      ring
    _ = Real.sin (2 * Real.pi * ((n % 7 : ℕ) : ℝ) / 7) :=
      Real.sin_add_nat_mul_two_pi _ _

private theorem conreySeven_sin_period_four (n : ℕ) :
    Real.sin (4 * Real.pi * n / 7) =
      Real.sin (4 * Real.pi * ((n % 7 : ℕ) : ℝ) / 7) := by
  have hn : (n : ℝ) = (n % 7 : ℕ) + 7 * (n / 7 : ℕ) := by
    exact_mod_cast (Nat.mod_add_div n 7).symm
  calc
    Real.sin (4 * Real.pi * n / 7) =
        Real.sin
          (4 * Real.pi * ((n % 7 : ℕ) : ℝ) / 7 +
            (2 * (n / 7) : ℕ) * (2 * Real.pi)) := by
      congr 1
      rw [hn]
      push_cast
      ring
    _ = Real.sin (4 * Real.pi * ((n % 7 : ℕ) : ℝ) / 7) :=
      Real.sin_add_nat_mul_two_pi _ _

private theorem conreySeven_sin_period_six (n : ℕ) :
    Real.sin (6 * Real.pi * n / 7) =
      Real.sin (6 * Real.pi * ((n % 7 : ℕ) : ℝ) / 7) := by
  have hn : (n : ℝ) = (n % 7 : ℕ) + 7 * (n / 7 : ℕ) := by
    exact_mod_cast (Nat.mod_add_div n 7).symm
  calc
    Real.sin (6 * Real.pi * n / 7) =
        Real.sin
          (6 * Real.pi * ((n % 7 : ℕ) : ℝ) / 7 +
            (3 * (n / 7) : ℕ) * (2 * Real.pi)) := by
      congr 1
      rw [hn]
      push_cast
      ring
    _ = Real.sin (6 * Real.pi * ((n % 7 : ℕ) : ℝ) / 7) :=
      Real.sin_add_nat_mul_two_pi _ _

/-- Exact discrete sine transform of the modulo-seven quadratic character. -/
theorem conreySevenSineConstant_mul_character (n : ℕ) :
    conreySevenSineConstant * (conreySevenCharacter n : ℝ) =
      Real.sin (2 * Real.pi * n / 7) +
        Real.sin (4 * Real.pi * n / 7) -
          Real.sin (6 * Real.pi * n / 7) := by
  rw [conreySevenCharacter_eq_table, conreySeven_sin_period_two,
    conreySeven_sin_period_four, conreySeven_sin_period_six]
  have hs8 :
      Real.sin (8 * Real.pi / 7) = -Real.sin (6 * Real.pi / 7) := by
    calc
      Real.sin (8 * Real.pi / 7) =
          Real.sin (-6 * Real.pi / 7 + (1 : ℤ) * (2 * Real.pi)) := by
        congr 1
        norm_num
        ring
      _ = Real.sin (-6 * Real.pi / 7) := Real.sin_add_int_mul_two_pi _ _
      _ = -Real.sin (6 * Real.pi / 7) := by
        rw [show -6 * Real.pi / 7 = -(6 * Real.pi / 7) by ring, Real.sin_neg]
  have hs10 :
      Real.sin (10 * Real.pi / 7) = -Real.sin (4 * Real.pi / 7) := by
    calc
      Real.sin (10 * Real.pi / 7) =
          Real.sin (-4 * Real.pi / 7 + (1 : ℤ) * (2 * Real.pi)) := by
        congr 1
        norm_num
        ring
      _ = Real.sin (-4 * Real.pi / 7) := Real.sin_add_int_mul_two_pi _ _
      _ = -Real.sin (4 * Real.pi / 7) := by
        rw [show -4 * Real.pi / 7 = -(4 * Real.pi / 7) by ring, Real.sin_neg]
  have hs12 :
      Real.sin (12 * Real.pi / 7) = -Real.sin (2 * Real.pi / 7) := by
    calc
      Real.sin (12 * Real.pi / 7) =
          Real.sin (-2 * Real.pi / 7 + (1 : ℤ) * (2 * Real.pi)) := by
        congr 1
        norm_num
        ring
      _ = Real.sin (-2 * Real.pi / 7) := Real.sin_add_int_mul_two_pi _ _
      _ = -Real.sin (2 * Real.pi / 7) := by
        rw [show -2 * Real.pi / 7 = -(2 * Real.pi / 7) by ring, Real.sin_neg]
  have hs16 :
      Real.sin (16 * Real.pi / 7) = Real.sin (2 * Real.pi / 7) := by
    calc
      Real.sin (16 * Real.pi / 7) =
          Real.sin (2 * Real.pi / 7 + (1 : ℤ) * (2 * Real.pi)) := by
        congr 1
        norm_num
        ring
      _ = Real.sin (2 * Real.pi / 7) := Real.sin_add_int_mul_two_pi _ _
  have hs18 :
      Real.sin (18 * Real.pi / 7) = Real.sin (4 * Real.pi / 7) := by
    calc
      Real.sin (18 * Real.pi / 7) =
          Real.sin (4 * Real.pi / 7 + (1 : ℤ) * (2 * Real.pi)) := by
        congr 1
        norm_num
        ring
      _ = Real.sin (4 * Real.pi / 7) := Real.sin_add_int_mul_two_pi _ _
  have hs20 :
      Real.sin (20 * Real.pi / 7) = Real.sin (6 * Real.pi / 7) := by
    calc
      Real.sin (20 * Real.pi / 7) =
          Real.sin (6 * Real.pi / 7 + (1 : ℤ) * (2 * Real.pi)) := by
        congr 1
        norm_num
        ring
      _ = Real.sin (6 * Real.pi / 7) := Real.sin_add_int_mul_two_pi _ _
  have hs24 :
      Real.sin (24 * Real.pi / 7) = -Real.sin (4 * Real.pi / 7) := by
    calc
      Real.sin (24 * Real.pi / 7) =
          Real.sin (-4 * Real.pi / 7 + (2 : ℤ) * (2 * Real.pi)) := by
        congr 1
        norm_num
        ring
      _ = Real.sin (-4 * Real.pi / 7) := Real.sin_add_int_mul_two_pi _ _
      _ = -Real.sin (4 * Real.pi / 7) := by
        rw [show -4 * Real.pi / 7 = -(4 * Real.pi / 7) by ring, Real.sin_neg]
  have hs30 :
      Real.sin (30 * Real.pi / 7) = Real.sin (2 * Real.pi / 7) := by
    calc
      Real.sin (30 * Real.pi / 7) =
          Real.sin (2 * Real.pi / 7 + (2 : ℤ) * (2 * Real.pi)) := by
        congr 1
        norm_num
        ring
      _ = Real.sin (2 * Real.pi / 7) := Real.sin_add_int_mul_two_pi _ _
  have hs36 :
      Real.sin (36 * Real.pi / 7) = -Real.sin (6 * Real.pi / 7) := by
    calc
      Real.sin (36 * Real.pi / 7) =
          Real.sin (-6 * Real.pi / 7 + (3 : ℤ) * (2 * Real.pi)) := by
        congr 1
        norm_num
        ring
      _ = Real.sin (-6 * Real.pi / 7) := Real.sin_add_int_mul_two_pi _ _
      _ = -Real.sin (6 * Real.pi / 7) := by
        rw [show -6 * Real.pi / 7 = -(6 * Real.pi / 7) by ring, Real.sin_neg]
  ring_nf at hs8 hs10 hs12 hs16 hs18 hs20 hs24 hs30 hs36
  have hr : n % 7 < 7 := Nat.mod_lt _ (by decide)
  interval_cases h : n % 7
  · simp [conreySevenCharacterTable, conreySevenSineConstant, h]
  · simp [conreySevenCharacterTable, conreySevenSineConstant, h]
  · simp [conreySevenCharacterTable, conreySevenSineConstant, h]
    ring_nf
    rw [hs8, hs12]
    ring
  · simp [conreySevenCharacterTable, conreySevenSineConstant, h]
    ring_nf
    rw [hs12, hs18]
    ring
  · simp [conreySevenCharacterTable, conreySevenSineConstant, h]
    ring_nf
    rw [hs8, hs16, hs24]
    ring
  · simp [conreySevenCharacterTable, conreySevenSineConstant, h]
    ring_nf
    rw [hs10, hs20, hs30]
    ring
  · simp [conreySevenCharacterTable, conreySevenSineConstant, h]
    ring_nf
    rw [hs12, hs24, hs36]
    ring

/-- The modulo-seven sine-transform constant is strictly positive. -/
theorem conreySevenSineConstant_pos : 0 < conreySevenSineConstant := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsin6 :
      Real.sin (6 * Real.pi / 7) = Real.sin (Real.pi / 7) := by
    calc
      Real.sin (6 * Real.pi / 7) =
          Real.sin (Real.pi - Real.pi / 7) := by
        congr 1
        ring
      _ = Real.sin (Real.pi / 7) := Real.sin_pi_sub _
  have hmem1 :
      Real.pi / 7 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith
  have hmem2 :
      2 * Real.pi / 7 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> nlinarith
  have hsin_lt :
      Real.sin (Real.pi / 7) < Real.sin (2 * Real.pi / 7) :=
    Real.strictMonoOn_sin hmem1 hmem2 (by nlinarith)
  have hsin4 : 0 < Real.sin (4 * Real.pi / 7) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith) (by nlinarith)
  rw [conreySevenSineConstant, hsin6]
  linarith

/-- One source-aligned term of the actual `q=7` Fourier sine series. -/
def conreySevenFourierTerm (x : ℝ) (n : ℕ) : ℝ :=
  (conreySevenCharacter n : ℝ) *
    Real.sin (2 * Real.pi * n * x) / (n : ℝ) ^ 2

/-- The actual Legendre-character Fourier series `f_7`. The natural-zero term is zero. -/
def conreySevenFourier (x : ℝ) : ℝ :=
  ∑' n : ℕ, conreySevenFourierTerm x n

private def conreySevenCosineTerm (u : ℝ) (n : ℕ) : ℝ :=
  1 / (n : ℝ) ^ 2 * Real.cos (2 * Real.pi * n * u)

private def conreySecondBernoulli (u : ℝ) : ℝ :=
  u ^ 2 - u + 1 / 6

private theorem conreySevenCosineTerm_hasSum {u : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    HasSum (conreySevenCosineTerm u)
      (Real.pi ^ 2 * conreySecondBernoulli u) := by
  convert hasSum_one_div_nat_pow_mul_cos (k := 1) (by norm_num) hu using 1
  · funext n
    rw [conreySevenCosineTerm]
  · norm_num [conreySecondBernoulli, Polynomial.bernoulli, Finset.sum_range_succ]
    ring

private theorem conreySin_mul_sin_shift (a b : ℝ) :
    Real.sin a * Real.sin b =
      (Real.cos (b - a) - Real.cos (b + a)) / 2 := by
  rw [Real.cos_sub, Real.cos_add]
  ring

/-- Product-to-sum form of one sine-transformed character-series term. -/
theorem conreySevenSineConstant_mul_fourierTerm (x : ℝ) (n : ℕ) :
    conreySevenSineConstant * conreySevenFourierTerm x n =
      (conreySevenCosineTerm (x - 1 / 7) n -
          conreySevenCosineTerm (x + 1 / 7) n +
          conreySevenCosineTerm (x - 2 / 7) n -
          conreySevenCosineTerm (x + 2 / 7) n -
          conreySevenCosineTerm (x - 3 / 7) n +
          conreySevenCosineTerm (x + 3 / 7) n) / 2 := by
  rw [conreySevenFourierTerm]
  calc
    conreySevenSineConstant *
        ((conreySevenCharacter n : ℝ) * Real.sin (2 * Real.pi * n * x) /
          (n : ℝ) ^ 2) =
        (conreySevenSineConstant * (conreySevenCharacter n : ℝ)) *
          Real.sin (2 * Real.pi * n * x) / (n : ℝ) ^ 2 := by ring
    _ = (Real.sin (2 * Real.pi * n / 7) +
          Real.sin (4 * Real.pi * n / 7) -
          Real.sin (6 * Real.pi * n / 7)) *
          Real.sin (2 * Real.pi * n * x) / (n : ℝ) ^ 2 := by
      rw [conreySevenSineConstant_mul_character]
    _ = _ := by
      rw [sub_mul, add_mul]
      rw [conreySin_mul_sin_shift, conreySin_mul_sin_shift, conreySin_mul_sin_shift]
      simp only [conreySevenCosineTerm]
      ring_nf

private theorem conreySevenCosineCombination_hasSum_zero
    (x : ℝ) (hx : x ∈ Set.Icc (3 / 7 : ℝ) (4 / 7 : ℝ)) :
    HasSum
      (fun n =>
        (conreySevenCosineTerm (x - 1 / 7) n -
            conreySevenCosineTerm (x + 1 / 7) n +
            conreySevenCosineTerm (x - 2 / 7) n -
            conreySevenCosineTerm (x + 2 / 7) n -
            conreySevenCosineTerm (x - 3 / 7) n +
            conreySevenCosineTerm (x + 3 / 7) n) / 2)
      0 := by
  have hm1 : x - 1 / 7 ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> norm_num at hx ⊢ <;> linarith [hx.1, hx.2]
  have hp1 : x + 1 / 7 ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> norm_num at hx ⊢ <;> linarith [hx.1, hx.2]
  have hm2 : x - 2 / 7 ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> norm_num at hx ⊢ <;> linarith [hx.1, hx.2]
  have hp2 : x + 2 / 7 ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> norm_num at hx ⊢ <;> linarith [hx.1, hx.2]
  have hm3 : x - 3 / 7 ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> norm_num at hx ⊢ <;> linarith [hx.1, hx.2]
  have hp3 : x + 3 / 7 ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> norm_num at hx ⊢ <;> linarith [hx.1, hx.2]
  have hsum :=
    (((((conreySevenCosineTerm_hasSum hm1).sub
      (conreySevenCosineTerm_hasSum hp1)).add
      (conreySevenCosineTerm_hasSum hm2)).sub
      (conreySevenCosineTerm_hasSum hp2)).sub
      (conreySevenCosineTerm_hasSum hm3)).add
      (conreySevenCosineTerm_hasSum hp3)
  have hhalf := hsum.div_const 2
  have hzero :
      (Real.pi ^ 2 * conreySecondBernoulli (x - 1 / 7) -
          Real.pi ^ 2 * conreySecondBernoulli (x + 1 / 7) +
          Real.pi ^ 2 * conreySecondBernoulli (x - 2 / 7) -
          Real.pi ^ 2 * conreySecondBernoulli (x + 2 / 7) -
          Real.pi ^ 2 * conreySecondBernoulli (x - 3 / 7) +
          Real.pi ^ 2 * conreySecondBernoulli (x + 3 / 7)) / 2 = 0 := by
    simp only [conreySecondBernoulli]
    ring
  rw [hzero] at hhalf
  exact hhalf

/-- The actual `q=7` Fourier terms sum to zero throughout the central interval. -/
theorem conreySevenFourierTerm_hasSum_zero
    (x : ℝ) (hx : x ∈ Set.Icc (3 / 7 : ℝ) (4 / 7 : ℝ)) :
    HasSum (conreySevenFourierTerm x) 0 := by
  have hscaled :
      HasSum (fun n => conreySevenSineConstant * conreySevenFourierTerm x n) 0 :=
    HasSum.congr_fun (conreySevenCosineCombination_hasSum_zero x hx) fun n =>
      conreySevenSineConstant_mul_fourierTerm x n
  have hK : conreySevenSineConstant ≠ 0 := ne_of_gt conreySevenSineConstant_pos
  simpa [hK, mul_assoc] using hscaled.mul_left conreySevenSineConstant⁻¹

/-- The genuine `q=7` Fourier series vanishes on the full interval `[3/7,4/7]`. -/
theorem conreySevenFourier_eq_zero
    (x : ℝ) (hx : x ∈ Set.Icc (3 / 7 : ℝ) (4 / 7 : ℝ)) :
    conreySevenFourier x = 0 :=
  (conreySevenFourierTerm_hasSum_zero x hx).tsum_eq

/-- The explicit irrational witness `sqrt(2)/3` lies in the flat interval. -/
theorem sqrtTwo_div_three_mem_conreySeven_flatInterval :
    Real.sqrt 2 / 3 ∈ Set.Icc (3 / 7 : ℝ) (4 / 7 : ℝ) := by
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsqrtSq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  constructor <;> norm_num <;> nlinarith

/-- The actual `q=7` Fourier series has a kernel-certified irrational zero. -/
theorem conreySevenFourier_irrational_zero :
    Irrational (Real.sqrt 2 / 3) ∧
      conreySevenFourier (Real.sqrt 2 / 3) = 0 := by
  constructor
  · exact (irrational_div_natCast_iff (x := Real.sqrt 2) (n := 3)).2
      ⟨by norm_num, irrational_sqrt_two⟩
  · exact conreySevenFourier_eq_zero _
      sqrtTwo_div_three_mem_conreySeven_flatInterval

/-- The witness modulus is in the adjacent `7 mod 8` family, not the RH-imitation family. -/
theorem conreySeven_modEight_scope :
    7 % 8 = 7 ∧ 7 % 8 ≠ 3 := by decide

/-- Aggregate certificate for the actual adjacent-family flat interval and its strict scope. -/
theorem conreySeven_actual_flat_interval_certificate :
    conreyPrefixMass conreySevenCharacter 3 = 1 ∧
      conreyPrefixMoment conreySevenCharacter 3 = 0 ∧
      (∀ x ∈ Set.Icc (3 / 7 : ℝ) (4 / 7 : ℝ),
        conreySevenFourier x = 0) ∧
      Irrational (Real.sqrt 2 / 3) ∧
      conreySevenFourier (Real.sqrt 2 / 3) = 0 ∧
      7 % 8 = 7 ∧ 7 % 8 ≠ 3 := by
  refine ⟨conreySeven_prefixMass_three, conreySeven_prefixMoment_three,
    ?_, conreySevenFourier_irrational_zero.1,
    conreySevenFourier_irrational_zero.2, conreySeven_modEight_scope⟩
  intro x hx
  exact conreySevenFourier_eq_zero x hx

end

end LeanLab.Riemann
