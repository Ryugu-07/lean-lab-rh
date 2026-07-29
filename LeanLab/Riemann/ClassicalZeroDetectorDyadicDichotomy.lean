import LeanLab.Riemann.ClassicalZeroDetectorContourShift
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The dyadic Type-I/Type-II zero-detector dichotomy

This file formalizes the finite truncation and powers-of-two partition in Maynard--Pratt,
Appendix C, Lemma 23.  Every block contains the actual truncated-Mobius smoothed terms, and
the remainder is the actual shifted inverse-Mellin line.
-/

namespace LeanLab.Riemann

open Complex Filter Real Set Topology
open scoped BigOperators

noncomputable section

/-- The actual smoothed detector tail after the finite cutoff `K`. -/
def classicalDetectorFarTail
    (M K : ℕ) (Y : ℝ) (rho : ℂ) : ℂ :=
  ∑' n : ℕ, classicalDetectorSmoothedTerm M Y rho (n + K)

/-- The number of powers-of-two indices needed to cover every positive integer below `K`. -/
def classicalDetectorDyadicIndexCount (K : ℕ) : ℕ :=
  Nat.log 2 K + 1

/-- Assign an integer to its binary logarithmic block, truncated only outside the source
middle range. -/
def classicalDetectorDyadicIndex (K n : ℕ) :
    Fin (classicalDetectorDyadicIndexCount K) :=
  ⟨min (Nat.log 2 n) (Nat.log 2 K),
    Nat.lt_succ_of_le (min_le_right _ _)⟩

theorem classicalDetectorDyadicIndex_val_of_le
    {K n : ℕ} (hnK : n ≤ K) :
    (classicalDetectorDyadicIndex K n : ℕ) = Nat.log 2 n := by
  rw [classicalDetectorDyadicIndex]
  simp only
  rw [min_eq_left (Nat.log_monotone hnK)]

/-- One actual powers-of-two block in the finite middle range `M < n < K`. -/
def classicalDetectorDyadicBlock
    (M K : ℕ) (Y : ℝ) (rho : ℂ)
    (j : Fin (classicalDetectorDyadicIndexCount K)) : ℂ :=
  ∑ n ∈ Finset.Ico (M + 1) K,
    if classicalDetectorDyadicIndex K n = j then
      classicalDetectorSmoothedTerm M Y rho n
    else 0

theorem classicalDetectorDyadicBlock_membership_range
    {M K n : ℕ} {j : Fin (classicalDetectorDyadicIndexCount K)}
    (hn : n ∈ Finset.Ico (M + 1) K)
    (hj : classicalDetectorDyadicIndex K n = j) :
    2 ^ (j : ℕ) ≤ n ∧ n < 2 ^ ((j : ℕ) + 1) := by
  have hn0 : n ≠ 0 := by
    have hnLower := (Finset.mem_Ico.mp hn).1
    omega
  have hindex :
      (j : ℕ) = Nat.log 2 n := by
    rw [← hj]
    exact classicalDetectorDyadicIndex_val_of_le
      (Finset.mem_Ico.mp hn).2.le
  constructor
  · rw [hindex]
    exact Nat.pow_log_le_self 2 hn0
  · rw [hindex]
    simpa only [Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self Nat.one_lt_two n

/-- Summing the binary-logarithmic fibers recovers the exact finite source middle range. -/
theorem sum_classicalDetectorDyadicBlock_eq_middle
    (M K : ℕ) (Y : ℝ) (rho : ℂ) :
    (∑ j : Fin (classicalDetectorDyadicIndexCount K),
        classicalDetectorDyadicBlock M K Y rho j) =
      ∑ n ∈ Finset.Ico (M + 1) K,
        classicalDetectorSmoothedTerm M Y rho n := by
  classical
  simp only [classicalDetectorDyadicBlock]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  simp

/-- The divisor sum itself gives the source coefficient bound before the coarser linear bound
used by the contour-shift module. -/
theorem norm_classicalDetectorCoefficient_le_card_divisors
    (M n : ℕ) :
    ‖classicalDetectorCoefficient M n‖ ≤ n.divisors.card := by
  rw [classicalDetectorCoefficient_eq_divisorSum]
  calc
    ‖∑ d ∈ n.divisors,
        if d ≤ M then ((ArithmeticFunction.moebius d : ℤ) : ℂ) else 0‖
        ≤ ∑ d ∈ n.divisors,
            ‖if d ≤ M then
              ((ArithmeticFunction.moebius d : ℤ) : ℂ) else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _d ∈ n.divisors, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d _
      split_ifs
      · rw [Complex.norm_intCast]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
      · norm_num
    _ = n.divisors.card := by simp

/-- Exact finite truncation of the actual smoothed series after the coefficient gap. -/
theorem classicalDetectorSmoothedSeries_eq_head_add_middle_add_farTail
    {M K : ℕ} (hM : 1 ≤ M) (hMK : M + 1 ≤ K)
    {rho : ℂ} (hrhoRe : 0 < rho.re)
    {Y : ℝ} (hY : 0 < Y) :
    classicalDetectorSmoothedSeries M Y rho =
      Complex.exp (-(1 / Y : ℝ)) +
        (∑ n ∈ Finset.Ico (M + 1) K,
          classicalDetectorSmoothedTerm M Y rho n) +
        classicalDetectorFarTail M K Y rho := by
  let f := classicalDetectorSmoothedTerm M Y rho
  have hf : Summable f :=
    summable_classicalDetectorSmoothedTerm_of_re_pos M hrhoRe hY
  have hhead :
      (∑ n ∈ Finset.range (M + 1), f n) =
        Complex.exp (-(1 / Y : ℝ)) := by
    rw [Finset.sum_eq_single 1]
    · exact classicalDetectorSmoothedTerm_one hM Y rho
    · intro n hn hn1
      have hnlt : n < M + 1 := Finset.mem_range.mp hn
      rcases eq_or_ne n 0 with rfl | hn0
      · simp [f, classicalDetectorSmoothedTerm, LSeries.term]
      · exact classicalDetectorSmoothedTerm_eq_zero
          (by omega) (by omega) Y rho
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (by omega))).elim
  have hsplit := hf.sum_add_tsum_nat_add K
  rw [classicalDetectorSmoothedSeries]
  calc
    (∑' n : ℕ, f n) =
        (∑ n ∈ Finset.range K, f n) +
          ∑' n : ℕ, f (n + K) := hsplit.symm
    _ = ((∑ n ∈ Finset.range (M + 1), f n) +
          ∑ n ∈ Finset.Ico (M + 1) K, f n) +
          ∑' n : ℕ, f (n + K) := by
      rw [Finset.sum_range_add_sum_Ico f hMK]
    _ = Complex.exp (-(1 / Y : ℝ)) +
          (∑ n ∈ Finset.Ico (M + 1) K,
            classicalDetectorSmoothedTerm M Y rho n) +
          classicalDetectorFarTail M K Y rho := by
      rw [hhead]
      rfl

/-- The combined finite-truncation error after moving the retained zeta-pole residue to the
left side of the source identity. -/
def classicalDetectorDyadicError
    (M K : ℕ) (Y : ℝ) (rho : ℂ) : ℂ :=
  (Complex.exp (-(1 / Y : ℝ)) - 1) +
    classicalDetectorFarTail M K Y rho -
    ((Y : ℂ) ^ (1 - rho) * Complex.Gamma (1 - rho) *
      classicalDetectorMollifier M 1)

/-- The exact source identity with an actual finite dyadic family and the actual shifted
inverse-Mellin remainder. -/
theorem classicalDetectorDyadic_shifted_identity
    {M K : ℕ} (hM : 1 ≤ M) (hMK : M + 1 ≤ K)
    {rho : ℂ} (hrho : IsNontrivialZero rho)
    (hbeta : 1 / 2 < rho.re) {Y : ℝ} (hY : 0 < Y) :
    (1 : ℂ) + classicalDetectorDyadicError M K Y rho +
        (∑ j : Fin (classicalDetectorDyadicIndexCount K),
          classicalDetectorDyadicBlock M K Y rho j) =
      classicalDetectorMellinLineIntegral M rho Y (1 / 2 - rho.re) := by
  have hfinite :=
    classicalDetectorSmoothedSeries_eq_head_add_middle_add_farTail
      hM hMK (nontrivial_zero_re_pos hrho) hY
  have hshift :=
    classicalDetectorSmoothedSeries_eq_residue_add_shifted
      M hrho hbeta hY
  rw [sum_classicalDetectorDyadicBlock_eq_middle]
  rw [classicalDetectorDyadicError]
  linear_combination hfinite.symm + hshift

/-- The source-strength finite detector keeps the remainder threshold `1/3` and distributes
only the last third among the finite block family. -/
theorem exists_source_large_block_or_remainder
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (block : ι → ℂ) (error remainder : ℂ)
    (hidentity : (1 : ℂ) + error + ∑ i, block i = remainder)
    (herror : ‖error‖ ≤ 1 / 3) :
    (1 / 3 : ℝ) ≤ ‖remainder‖ ∨
      ∃ i, 1 / (3 * Fintype.card ι : ℝ) ≤ ‖block i‖ := by
  by_contra h
  push Not at h
  rcases h with ⟨hremainder, hblock⟩
  have hmass :=
    one_le_error_add_remainder_add_blockMass
      block error remainder hidentity
  have hcardPos : 0 < Fintype.card ι := Fintype.card_pos
  have hsum :
      (∑ i, ‖block i‖) ≤ (1 / 3 : ℝ) := by
    calc
      (∑ i, ‖block i‖) ≤
          (Fintype.card ι : ℝ) *
            (1 / (3 * Fintype.card ι : ℝ)) := by
        simpa using
          Finset.sum_le_card_nsmul Finset.univ (fun i => ‖block i‖)
            (1 / (3 * Fintype.card ι : ℝ))
            (fun i _ => (hblock i).le)
      _ = 1 / 3 := by
        field_simp [Nat.ne_of_gt hcardPos]
  have hupper :
      ‖error‖ + ‖remainder‖ + ∑ i, ‖block i‖ < 1 := by
    linarith
  linarith

/-- A source Type-I witness is one large actual powers-of-two coefficient block. -/
def ClassicalDetectorTypeI
    (M K : ℕ) (Y : ℝ) (rho : ℂ) : Prop :=
  ∃ j : Fin (classicalDetectorDyadicIndexCount K),
    1 / (3 * classicalDetectorDyadicIndexCount K : ℝ) ≤
      ‖classicalDetectorDyadicBlock M K Y rho j‖

/-- A source Type-II witness is a large actual shifted inverse-Mellin integral. -/
def ClassicalDetectorTypeII
    (M : ℕ) (Y : ℝ) (rho : ℂ) : Prop :=
  (1 / 3 : ℝ) ≤
    ‖classicalDetectorMellinLineIntegral M rho Y (1 / 2 - rho.re)‖

theorem norm_classicalDetectorDyadicError_le
    (M K : ℕ) {Y : ℝ} (rho : ℂ) :
    ‖classicalDetectorDyadicError M K Y rho‖ ≤
      ‖Complex.exp (-(1 / Y : ℝ)) - 1‖ +
        ‖classicalDetectorFarTail M K Y rho‖ +
        ‖(Y : ℂ) ^ (1 - rho) * Complex.Gamma (1 - rho) *
          classicalDetectorMollifier M 1‖ := by
  rw [classicalDetectorDyadicError]
  calc
    ‖(Complex.exp (-(1 / Y : ℝ)) - 1) +
          classicalDetectorFarTail M K Y rho -
          ((Y : ℂ) ^ (1 - rho) * Complex.Gamma (1 - rho) *
            classicalDetectorMollifier M 1)‖ ≤
        ‖(Complex.exp (-(1 / Y : ℝ)) - 1) +
          classicalDetectorFarTail M K Y rho‖ +
          ‖(Y : ℂ) ^ (1 - rho) * Complex.Gamma (1 - rho) *
            classicalDetectorMollifier M 1‖ :=
      norm_sub_le _ _
    _ ≤ (‖Complex.exp (-(1 / Y : ℝ)) - 1‖ +
          ‖classicalDetectorFarTail M K Y rho‖) +
          ‖(Y : ℂ) ^ (1 - rho) * Complex.Gamma (1 - rho) *
            classicalDetectorMollifier M 1‖ := by
      gcongr
      exact norm_add_le _ _

/-- The exact actual-zero Type-I/Type-II conclusion once the three separately auditable source
errors fit in the reserved third. -/
theorem classicalDetector_typeI_or_typeII
    {M K : ℕ} (hM : 1 ≤ M) (hMK : M + 1 ≤ K)
    {rho : ℂ} (hrho : IsNontrivialZero rho)
    (hbeta : 1 / 2 < rho.re) {Y : ℝ} (hY : 0 < Y)
    (hhead : ‖Complex.exp (-(1 / Y : ℝ)) - 1‖ ≤ 1 / 9)
    (htail : ‖classicalDetectorFarTail M K Y rho‖ ≤ 1 / 9)
    (hresidue :
      ‖(Y : ℂ) ^ (1 - rho) * Complex.Gamma (1 - rho) *
        classicalDetectorMollifier M 1‖ ≤ 1 / 9) :
    ClassicalDetectorTypeII M Y rho ∨
      ClassicalDetectorTypeI M K Y rho := by
  haveI : Nonempty (Fin (classicalDetectorDyadicIndexCount K)) :=
    Fin.pos_iff_nonempty.mp (by
      simp [classicalDetectorDyadicIndexCount])
  have herror : ‖classicalDetectorDyadicError M K Y rho‖ ≤ 1 / 3 := by
    calc
      ‖classicalDetectorDyadicError M K Y rho‖ ≤
          ‖Complex.exp (-(1 / Y : ℝ)) - 1‖ +
            ‖classicalDetectorFarTail M K Y rho‖ +
            ‖(Y : ℂ) ^ (1 - rho) * Complex.Gamma (1 - rho) *
              classicalDetectorMollifier M 1‖ :=
        norm_classicalDetectorDyadicError_le M K rho
      _ ≤ 1 / 9 + 1 / 9 + 1 / 9 := by gcongr
      _ = 1 / 3 := by norm_num
  have hdetector :=
    exists_source_large_block_or_remainder
      (fun j : Fin (classicalDetectorDyadicIndexCount K) =>
        classicalDetectorDyadicBlock M K Y rho j)
      (classicalDetectorDyadicError M K Y rho)
      (classicalDetectorMellinLineIntegral M rho Y (1 / 2 - rho.re))
      (classicalDetectorDyadic_shifted_identity hM hMK hrho hbeta hY)
      herror
  rcases hdetector with hII | hI
  · exact Or.inl hII
  · exact Or.inr (by
      simpa [ClassicalDetectorTypeI] using hI)

theorem norm_classicalDetector_headError_le
    {Y : ℝ} (hY : 0 < Y) :
    ‖Complex.exp (-(1 / Y : ℝ)) - 1‖ ≤ 1 / Y := by
  have hu : 0 < 1 / Y := one_div_pos.mpr hY
  have hexpLe : Real.exp (-(1 / Y)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hlinear := Real.add_one_le_exp (-(1 / Y))
  have hcexp :
      Complex.exp (-(1 / Y : ℝ)) =
        (Real.exp (-(1 / Y)) : ℂ) := by
    calc
      Complex.exp (-(1 / Y : ℝ)) =
          Complex.exp (((-(1 / Y) : ℝ) : ℂ)) := by
        congr 1
        norm_num
      _ = (Real.exp (-(1 / Y)) : ℂ) :=
        (Complex.ofReal_exp _).symm
  rw [hcexp]
  have hnorm :
      ‖(Real.exp (-(1 / Y)) : ℂ) - 1‖ =
        |Real.exp (-(1 / Y)) - 1| := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm]
  rw [abs_of_nonpos (by linarith)]
  linarith

theorem norm_classicalDetector_headError_le_one_ninth
    {Y : ℝ} (hY : 9 ≤ Y) :
    ‖Complex.exp (-(1 / Y : ℝ)) - 1‖ ≤ 1 / 9 := by
  have hYpos : 0 < Y := by linarith
  exact (norm_classicalDetector_headError_le hYpos).trans
    (one_div_le_one_div_of_le (by norm_num) hY)

/-- A polynomial-times-exponential majorant for every translated source-tail term. -/
theorem classicalDetector_nat_add_mul_exp_tail_majorant
    {Y : ℝ} (hY : 0 < Y) {K : ℕ} (hKY : 2 * Y ≤ K)
    (n : ℕ) :
    (n + K : ℝ) * Real.exp (-((n + K : ℝ) / Y)) ≤
      (K : ℝ) * Real.exp (-((K : ℝ) / Y)) *
        Real.exp (-(1 / (2 * Y))) ^ n := by
  have hKpos : 0 < (K : ℝ) := by
    exact lt_of_lt_of_le (by positivity) hKY
  have htwoY : 0 < 2 * Y := by positivity
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hinv :
      1 / (K : ℝ) ≤ 1 / (2 * Y) :=
    one_div_le_one_div_of_le htwoY hKY
  have hdiv :
      (n : ℝ) / K ≤ (n : ℝ) / (2 * Y) := by
    calc
      (n : ℝ) / K = (n : ℝ) * (1 / K) := by ring
      _ ≤ (n : ℝ) * (1 / (2 * Y)) :=
        mul_le_mul_of_nonneg_left hinv hn0
      _ = (n : ℝ) / (2 * Y) := by ring
  have hone :
      1 + (n : ℝ) / K ≤ Real.exp ((n : ℝ) / K) := by
    simpa only [add_comm] using Real.add_one_le_exp ((n : ℝ) / K)
  calc
    (n + K : ℝ) * Real.exp (-((n + K : ℝ) / Y)) =
        (K : ℝ) * (1 + (n : ℝ) / K) *
          Real.exp (-((n + K : ℝ) / Y)) := by
      field_simp
      ring
    _ ≤ (K : ℝ) * Real.exp ((n : ℝ) / K) *
          Real.exp (-((n + K : ℝ) / Y)) := by
      gcongr
    _ ≤ (K : ℝ) * Real.exp ((n : ℝ) / (2 * Y)) *
          Real.exp (-((n + K : ℝ) / Y)) := by
      gcongr
    _ = (K : ℝ) * Real.exp (-((K : ℝ) / Y)) *
          Real.exp (-(1 / (2 * Y))) ^ n := by
      calc
        (K : ℝ) * Real.exp ((n : ℝ) / (2 * Y)) *
              Real.exp (-((n + K : ℝ) / Y)) =
            (K : ℝ) *
              Real.exp ((n : ℝ) / (2 * Y) -
                ((n + K : ℝ) / Y)) := by
          rw [Real.exp_sub]
          rw [Real.exp_neg]
          field_simp
        _ = (K : ℝ) *
              Real.exp (-((K : ℝ) / Y) +
                (n : ℝ) * (-(1 / (2 * Y)))) := by
          congr 2
          field_simp
          ring
        _ = (K : ℝ) * Real.exp (-((K : ℝ) / Y)) *
              Real.exp ((n : ℝ) * (-(1 / (2 * Y)))) := by
          rw [Real.exp_add]
          ring
        _ = (K : ℝ) * Real.exp (-((K : ℝ) / Y)) *
              Real.exp (-(1 / (2 * Y))) ^ n := by
          rw [← Real.exp_nat_mul]

/-- The actual far tail is bounded by one explicit geometric series. -/
theorem norm_classicalDetectorFarTail_le
    (M K : ℕ) {Y : ℝ} (hY : 0 < Y)
    {rho : ℂ} (hrhoRe : 0 < rho.re)
    (hKY : 2 * Y ≤ K) :
    ‖classicalDetectorFarTail M K Y rho‖ ≤
      (K : ℝ) * Real.exp (-((K : ℝ) / Y)) *
        (1 - Real.exp (-(1 / (2 * Y))))⁻¹ := by
  let f : ℕ → ℂ := fun n =>
    classicalDetectorSmoothedTerm M Y rho (n + K)
  let q : ℝ := Real.exp (-(1 / (2 * Y)))
  let C : ℝ := (K : ℝ) * Real.exp (-((K : ℝ) / Y))
  have hf : Summable f := by
    exact (summable_classicalDetectorSmoothedTerm_of_re_pos M hrhoRe hY).comp_injective
      (fun _ _ h => Nat.add_right_cancel h)
  have hq0 : 0 ≤ q := Real.exp_nonneg _
  have hq1 : q < 1 := by
    dsimp only [q]
    rw [Real.exp_lt_one_iff]
    have hx : 0 < 1 / (2 * Y) := by positivity
    linarith
  have hmajor : Summable (fun n : ℕ => C * q ^ n) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left C
  have hterm : ∀ n : ℕ, ‖f n‖ ≤ C * q ^ n := by
    intro n
    calc
      ‖f n‖ ≤ (n + K : ℝ) *
          Real.exp (-((n + K : ℝ) / Y)) := by
        simpa [f, Nat.cast_add] using
          norm_classicalDetectorSmoothedTerm_le
            M hrhoRe Y (n + K)
      _ ≤ (K : ℝ) * Real.exp (-((K : ℝ) / Y)) *
          Real.exp (-(1 / (2 * Y))) ^ n :=
        classicalDetector_nat_add_mul_exp_tail_majorant hY hKY n
      _ = C * q ^ n := rfl
  calc
    ‖classicalDetectorFarTail M K Y rho‖ =
        ‖∑' n : ℕ, f n‖ := rfl
    _ ≤ ∑' n : ℕ, ‖f n‖ := norm_tsum_le_tsum_norm hf.norm
    _ ≤ ∑' n : ℕ, C * q ^ n :=
      hf.norm.tsum_le_tsum hterm hmajor
    _ = C * (1 - q)⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
    _ = (K : ℝ) * Real.exp (-((K : ℝ) / Y)) *
        (1 - Real.exp (-(1 / (2 * Y))))⁻¹ := rfl

theorem geometric_tail_denominator_inv_le
    {Y : ℝ} (hY : 0 < Y) :
    (1 - Real.exp (-(1 / (2 * Y))))⁻¹ ≤ 1 + 2 * Y := by
  let x : ℝ := 1 / (2 * Y)
  have hx : 0 < x := by dsimp [x]; positivity
  have hq : Real.exp (-x) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  have hden : 0 < 1 - Real.exp (-x) := sub_pos.mpr hq
  have hexp := Real.add_one_le_exp x
  have hqUpper : Real.exp (-x) ≤ 1 / (1 + x) := by
    rw [Real.exp_neg]
    simpa only [one_div, add_comm] using
      one_div_le_one_div_of_le (by positivity) hexp
  have hgap : x / (1 + x) ≤ 1 - Real.exp (-x) := by
    calc
      x / (1 + x) = 1 - 1 / (1 + x) := by
        field_simp
        ring
      _ ≤ 1 - Real.exp (-x) := sub_le_sub_left hqUpper 1
  have hfactor : 0 ≤ 1 + 1 / x := by positivity
  have hone :
      1 ≤ (1 + 1 / x) * (1 - Real.exp (-x)) := by
    calc
      1 = (1 + 1 / x) * (x / (1 + x)) := by
        field_simp
        ring
      _ ≤ (1 + 1 / x) * (1 - Real.exp (-x)) :=
        mul_le_mul_of_nonneg_left hgap hfactor
  have hinv :
      (1 - Real.exp (-x))⁻¹ ≤ 1 + 1 / x := by
    exact (inv_le_iff_one_le_mul₀ hden).2 hone
  calc
    (1 - Real.exp (-(1 / (2 * Y))))⁻¹ =
        (1 - Real.exp (-x))⁻¹ := rfl
    _ ≤ 1 + 1 / x := hinv
    _ = 1 + 2 * Y := by
      dsimp [x]
      field_simp

theorem norm_classicalDetectorFarTail_le_explicit
    (M K : ℕ) {Y : ℝ} (hY : 0 < Y)
    {rho : ℂ} (hrhoRe : 0 < rho.re)
    (hKY : 2 * Y ≤ K) :
    ‖classicalDetectorFarTail M K Y rho‖ ≤
      (K : ℝ) * (1 + 2 * Y) *
        Real.exp (-((K : ℝ) / Y)) := by
  calc
    ‖classicalDetectorFarTail M K Y rho‖ ≤
        (K : ℝ) * Real.exp (-((K : ℝ) / Y)) *
          (1 - Real.exp (-(1 / (2 * Y))))⁻¹ :=
      norm_classicalDetectorFarTail_le M K hY hrhoRe hKY
    _ ≤ (K : ℝ) * Real.exp (-((K : ℝ) / Y)) *
          (1 + 2 * Y) := by
      gcongr
      exact geometric_tail_denominator_inv_le hY
    _ = (K : ℝ) * (1 + 2 * Y) *
          Real.exp (-((K : ℝ) / Y)) := by ring

/-- Uniform source-range control of the retained translated-zeta residue. -/
theorem exists_norm_classicalDetectorRetainedResidue_le :
    ∃ p : ℝ, 0 < p ∧
      ∀ (M : ℕ) {rho : ℂ}, IsNontrivialZero rho →
        ∀ {Y : ℝ}, 0 < Y → 1 ≤ |rho.im| →
          ‖(Y : ℂ) ^ (1 - rho) * Complex.Gamma (1 - rho) *
              classicalDetectorMollifier M 1‖ ≤
            3 * (M : ℝ) * Y ^ (1 - rho.re) *
              (|rho.im| + 2) ^ p *
              Real.exp (-(Real.pi / 2) * |rho.im|) := by
  obtain ⟨p, hp, hgamma⟩ :=
    exists_norm_Gamma_classicalDetectorStrip_le
  refine ⟨p, hp, ?_⟩
  intro M rho hrho Y hY hrhoIm
  have hx :
      1 - rho.re ∈ Set.Icc (1 / 2 - rho.re) 2 := by
    constructor
    · norm_num
    · linarith [nontrivial_zero_re_pos hrho]
  have hGamma :
      ‖Complex.Gamma (1 - rho)‖ ≤
        3 * (|rho.im| + 2) ^ p *
          Real.exp (-(Real.pi / 2) * |rho.im|) := by
    have hraw :=
      hgamma hrho (1 - rho.re) (-rho.im) hx (by simpa)
    have hpoint :
        (1 - rho) =
          ((1 - rho.re : ℝ) : ℂ) + (-rho.im : ℝ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [hpoint]
    simpa using hraw
  have hpower :
      ‖(Y : ℂ) ^ (1 - rho)‖ = Y ^ (1 - rho.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hY]
    simp
  have hmollifier :
      ‖classicalDetectorMollifier M 1‖ ≤ M := by
    exact norm_classicalDetectorMollifier_le_nat M (by norm_num)
  simp only [norm_mul, hpower]
  calc
    Y ^ (1 - rho.re) * ‖Complex.Gamma (1 - rho)‖ *
          ‖classicalDetectorMollifier M 1‖ ≤
        Y ^ (1 - rho.re) *
          (3 * (|rho.im| + 2) ^ p *
            Real.exp (-(Real.pi / 2) * |rho.im|)) *
          (M : ℝ) := by
      gcongr
    _ = 3 * (M : ℝ) * Y ^ (1 - rho.re) *
          (|rho.im| + 2) ^ p *
          Real.exp (-(Real.pi / 2) * |rho.im|) := by ring

/-- One fixed Gamma-strip exponent for the whole source campaign. -/
def classicalDetectorGammaExponent : ℝ :=
  (exists_norm_classicalDetectorRetainedResidue_le).choose

theorem classicalDetectorGammaExponent_pos :
    0 < classicalDetectorGammaExponent :=
  (exists_norm_classicalDetectorRetainedResidue_le).choose_spec.1

theorem norm_classicalDetectorRetainedResidue_le
    (M : ℕ) {rho : ℂ} (hrho : IsNontrivialZero rho)
    {Y : ℝ} (hY : 0 < Y) (hrhoIm : 1 ≤ |rho.im|) :
    ‖(Y : ℂ) ^ (1 - rho) * Complex.Gamma (1 - rho) *
        classicalDetectorMollifier M 1‖ ≤
      3 * (M : ℝ) * Y ^ (1 - rho.re) *
        (|rho.im| + 2) ^ classicalDetectorGammaExponent *
        Real.exp (-(Real.pi / 2) * |rho.im|) :=
  (exists_norm_classicalDetectorRetainedResidue_le).choose_spec.2
    M hrho hY hrhoIm

/-- A source-uniform scalar majorant for the retained residue. -/
def classicalDetectorRetainedResidueMajorant (T : ℝ) : ℝ :=
  6 * 4 ^ classicalDetectorGammaExponent *
    T ^ (classicalDetectorGammaExponent + 101 / 100) *
    Real.exp (-(Real.pi / 2) * T)

theorem classicalDetectorRetainedResidueMajorant_tendsto_zero :
    Tendsto classicalDetectorRetainedResidueMajorant atTop (𝓝 0) := by
  have hb : 0 < Real.pi / 2 := by positivity
  have hcore :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (classicalDetectorGammaExponent + 101 / 100)
      (Real.pi / 2) hb
  have hconst :
      Tendsto
        (fun _ : ℝ => (6 : ℝ) *
          (4 : ℝ) ^ classicalDetectorGammaExponent)
        atTop (𝓝 ((6 : ℝ) *
          (4 : ℝ) ^ classicalDetectorGammaExponent)) :=
    tendsto_const_nhds
  change Tendsto
    (fun T : ℝ =>
      6 * 4 ^ classicalDetectorGammaExponent *
        T ^ (classicalDetectorGammaExponent + 101 / 100) *
        Real.exp (-(Real.pi / 2) * T))
    atTop (𝓝 0)
  convert hconst.mul hcore using 1
  · funext T
    ring
  · simp

theorem norm_classicalDetectorRetainedResidue_le_majorant
    {T Y : ℝ} (hT : 1 ≤ T) (hYLower : 1 ≤ Y) (hYT : Y ≤ T)
    {M : ℕ} (hM :
      (M : ℝ) ≤ 2 * T ^ (1 / 100 : ℝ))
    {rho : ℂ} (hrho : IsNontrivialZero rho)
    (hgammaLower : T ≤ |rho.im|)
    (hgammaUpper : |rho.im| ≤ 2 * T) :
    ‖(Y : ℂ) ^ (1 - rho) * Complex.Gamma (1 - rho) *
        classicalDetectorMollifier M 1‖ ≤
      classicalDetectorRetainedResidueMajorant T := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hYpos : 0 < Y := zero_lt_one.trans_le hYLower
  have himOne : 1 ≤ |rho.im| := hT.trans hgammaLower
  have hexponentUpper : 1 - rho.re ≤ 1 := by
    linarith [nontrivial_zero_re_pos hrho]
  have hYpower : Y ^ (1 - rho.re) ≤ Y := by
    calc
      Y ^ (1 - rho.re) ≤ Y ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hYLower hexponentUpper
      _ = Y := Real.rpow_one Y
  have hYpowerT : Y ^ (1 - rho.re) ≤ T :=
    hYpower.trans hYT
  have hgammaBase :
      |rho.im| + 2 ≤ 4 * T := by
    linarith
  have hgammaPower :
      (|rho.im| + 2) ^ classicalDetectorGammaExponent ≤
        (4 * T) ^ classicalDetectorGammaExponent :=
    Real.rpow_le_rpow
      (by positivity)
      hgammaBase
      classicalDetectorGammaExponent_pos.le
  have hexp :
      Real.exp (-(Real.pi / 2) * |rho.im|) ≤
        Real.exp (-(Real.pi / 2) * T) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  have hsource :=
    norm_classicalDetectorRetainedResidue_le M hrho hYpos himOne
  calc
    ‖(Y : ℂ) ^ (1 - rho) * Complex.Gamma (1 - rho) *
          classicalDetectorMollifier M 1‖ ≤
        3 * (M : ℝ) * Y ^ (1 - rho.re) *
          (|rho.im| + 2) ^ classicalDetectorGammaExponent *
          Real.exp (-(Real.pi / 2) * |rho.im|) := hsource
    _ ≤ 3 * (2 * T ^ (1 / 100 : ℝ)) * T *
          (4 * T) ^ classicalDetectorGammaExponent *
          Real.exp (-(Real.pi / 2) * T) := by
      gcongr
    _ = classicalDetectorRetainedResidueMajorant T := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hTpos.le]
      have hpow :
          T ^ (1 / 100 : ℝ) * T *
              T ^ classicalDetectorGammaExponent =
            T ^ (classicalDetectorGammaExponent + 101 / 100) := by
        calc
          T ^ (1 / 100 : ℝ) * T *
                T ^ classicalDetectorGammaExponent =
              T ^ (1 / 100 : ℝ) * T ^ (1 : ℝ) *
                T ^ classicalDetectorGammaExponent := by
            rw [Real.rpow_one]
          _ = T ^ ((1 / 100 : ℝ) + 1) *
                T ^ classicalDetectorGammaExponent := by
            rw [← Real.rpow_add hTpos]
          _ = T ^ ((1 / 100 : ℝ) + 1 +
                classicalDetectorGammaExponent) := by
            rw [← Real.rpow_add hTpos]
          _ = T ^ (classicalDetectorGammaExponent + 101 / 100) := by
            congr 1
            ring
      calc
        3 * (2 * T ^ (1 / 100 : ℝ)) * T *
              (4 ^ classicalDetectorGammaExponent *
                T ^ classicalDetectorGammaExponent) *
              Real.exp (-(Real.pi / 2) * T) =
            6 * 4 ^ classicalDetectorGammaExponent *
              (T ^ (1 / 100 : ℝ) * T *
                T ^ classicalDetectorGammaExponent) *
              Real.exp (-(Real.pi / 2) * T) := by ring
        _ = classicalDetectorRetainedResidueMajorant T := by
          rw [hpow]
          rfl

theorem eventually_norm_classicalDetectorRetainedResidue_le_one_ninth :
    ∀ᶠ T : ℝ in atTop,
      ∀ (Y : ℝ), 1 ≤ Y → Y ≤ T →
      ∀ (M : ℕ), (M : ℝ) ≤ 2 * T ^ (1 / 100 : ℝ) →
      ∀ {rho : ℂ}, IsNontrivialZero rho →
        T ≤ |rho.im| → |rho.im| ≤ 2 * T →
        ‖(Y : ℂ) ^ (1 - rho) * Complex.Gamma (1 - rho) *
            classicalDetectorMollifier M 1‖ ≤ 1 / 9 := by
  have hsmall :
      ∀ᶠ T : ℝ in atTop,
        classicalDetectorRetainedResidueMajorant T < 1 / 9 :=
    (tendsto_order.1
      classicalDetectorRetainedResidueMajorant_tendsto_zero).2
        (1 / 9) (by norm_num)
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℝ)] with T hsmallT hT
  intro Y hYLower hYT M hM rho hrho hgammaLower hgammaUpper
  exact (norm_classicalDetectorRetainedResidue_le_majorant
    hT hYLower hYT hM hrho hgammaLower hgammaUpper).trans hsmallT.le

theorem norm_classicalDetectorFarTail_le_one_ninth_of_source_scale
    {T Y : ℝ} (hT : 81 ≤ T) (hYLower : 9 ≤ Y) (hYT : Y ≤ T)
    (M : ℕ) {K : ℕ} (hKT : (K : ℝ) ≤ T)
    (hKLower : 8 * Y * Real.log T ≤ K)
    {rho : ℂ} (hrhoRe : 0 < rho.re) :
    ‖classicalDetectorFarTail M K Y rho‖ ≤ 1 / 9 := by
  have hTpos : 0 < T := by linarith
  have hYpos : 0 < Y := by linarith
  have hexpT : Real.exp 1 ≤ T := by
    exact Real.exp_one_lt_three.le.trans (by linarith)
  have hlogT : 1 ≤ Real.log T := by
    calc
      1 = Real.log (Real.exp 1) := by rw [Real.log_exp]
      _ ≤ Real.log T := Real.log_le_log (Real.exp_pos 1) hexpT
  have hKY : 2 * Y ≤ K := by
    have hYnonneg : 0 ≤ Y := hYpos.le
    calc
      2 * Y ≤ 8 * Y * Real.log T := by nlinarith
      _ ≤ K := hKLower
  have hratio :
      8 * Real.log T ≤ (K : ℝ) / Y := by
    rw [le_div_iff₀ hYpos]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hKLower
  have hexp :
      Real.exp (-((K : ℝ) / Y)) ≤ (T⁻¹) ^ (8 : ℕ) := by
    calc
      Real.exp (-((K : ℝ) / Y)) ≤
          Real.exp (-(8 * Real.log T)) := by
        exact Real.exp_le_exp.mpr (by linarith)
      _ = (T⁻¹) ^ (8 : ℕ) := by
        rw [show -(8 * Real.log T) =
            (8 : ℕ) * (-Real.log T) by norm_num]
        rw [Real.exp_nat_mul, Real.exp_neg, Real.exp_log hTpos]
  have hlinear : 1 + 2 * Y ≤ 3 * T := by
    nlinarith
  have htail :=
    norm_classicalDetectorFarTail_le_explicit
      M K hYpos hrhoRe hKY
  calc
    ‖classicalDetectorFarTail M K Y rho‖ ≤
        (K : ℝ) * (1 + 2 * Y) *
          Real.exp (-((K : ℝ) / Y)) := htail
    _ ≤ T * (3 * T) * ((T⁻¹) ^ (8 : ℕ)) := by
      gcongr
    _ = 3 / T ^ (6 : ℕ) := by
      field_simp
    _ ≤ 1 / 9 := by
      rw [div_le_iff₀ (pow_pos hTpos 6)]
      have hthree : (3 : ℝ) ≤ T := by linarith
      have hpow : (3 : ℝ) ^ (6 : ℕ) ≤ T ^ (6 : ℕ) :=
        pow_le_pow_left₀ (by norm_num) hthree 6
      norm_num at hpow ⊢
      linarith

/-- The powers-of-two family has logarithmic cardinality whenever the cutoff lies below the
height scale. -/
theorem classicalDetectorDyadicIndexCount_le_three_log
    {K : ℕ} (hK : 1 ≤ K) {T : ℝ}
    (hT : Real.exp 1 ≤ T) (hKT : (K : ℝ) ≤ T) :
    (classicalDetectorDyadicIndexCount K : ℝ) ≤
      3 * Real.log T := by
  have hTpos : 0 < T := (Real.exp_pos 1).trans_le hT
  have hlogT : 1 ≤ Real.log T := by
    calc
      1 = Real.log (Real.exp 1) := by rw [Real.log_exp]
      _ ≤ Real.log T := Real.log_le_log (Real.exp_pos 1) hT
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (zero_lt_one.trans_le hK)
  have hlogK : Real.log (K : ℝ) ≤ Real.log T :=
    Real.log_le_log hKpos hKT
  have hlogTwoPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hinvLogTwo : (Real.log 2)⁻¹ ≤ 2 := by
    apply (inv_le_iff_one_le_mul₀ hlogTwoPos).2
    nlinarith [Real.log_two_gt_d9]
  have hlogb :
      Real.logb 2 K ≤ 2 * Real.log T := by
    rw [Real.logb, div_eq_mul_inv]
    calc
      Real.log (K : ℝ) * (Real.log 2)⁻¹ ≤
          Real.log T * (Real.log 2)⁻¹ :=
        mul_le_mul_of_nonneg_right hlogK (inv_nonneg.mpr hlogTwoPos.le)
      _ ≤ Real.log T * 2 :=
        mul_le_mul_of_nonneg_left hinvLogTwo (by linarith)
      _ = 2 * Real.log T := by ring
  have hnat :
      (Nat.log 2 K : ℝ) ≤ Real.logb 2 K :=
    Real.natLog_le_logb K 2
  rw [classicalDetectorDyadicIndexCount]
  push_cast
  linarith

/-- The source logarithmic Type-I threshold obtained from the audited binary block count. -/
def ClassicalDetectorTypeILog
    (T : ℝ) (M K : ℕ) (Y : ℝ) (rho : ℂ) : Prop :=
  ∃ j : Fin (classicalDetectorDyadicIndexCount K),
    1 / (9 * Real.log T) ≤
      ‖classicalDetectorDyadicBlock M K Y rho j‖

theorem classicalDetectorTypeILog_of_typeI
    {T : ℝ} (hT : Real.exp 1 ≤ T)
    {M K : ℕ} (hK : 1 ≤ K) (hKT : (K : ℝ) ≤ T)
    {Y : ℝ} {rho : ℂ}
    (hI : ClassicalDetectorTypeI M K Y rho) :
    ClassicalDetectorTypeILog T M K Y rho := by
  rcases hI with ⟨j, hj⟩
  refine ⟨j, ?_⟩
  have hlogT : 0 < Real.log T := by
    have hTgt : 1 < T :=
      (Real.one_lt_exp_iff.mpr (by norm_num)).trans_le hT
    exact Real.log_pos hTgt
  have hcountPos :
      0 < (classicalDetectorDyadicIndexCount K : ℝ) := by
    rw [classicalDetectorDyadicIndexCount]
    positivity
  have hcount :=
    classicalDetectorDyadicIndexCount_le_three_log hK hT hKT
  have hden :
      3 * (classicalDetectorDyadicIndexCount K : ℝ) ≤
        9 * Real.log T := by linarith
  have hinv :
      1 / (9 * Real.log T) ≤
        1 / (3 * classicalDetectorDyadicIndexCount K : ℝ) :=
    one_div_le_one_div_of_le (by positivity) hden
  exact hinv.trans hj

/-- Maynard--Pratt Lemma 23 on one concrete source-valid parameter regime. The theorem is
eventual only because the fixed Gamma-strip polynomial exponent is existential; all other
thresholds are explicit. -/
theorem eventually_classicalDetector_typeILog_or_typeII :
    ∀ᶠ T : ℝ in atTop,
      ∀ (Y : ℝ), 9 ≤ Y → Y ≤ T →
      ∀ (M K : ℕ), 1 ≤ M → M + 1 ≤ K →
        (M : ℝ) ≤ 2 * T ^ (1 / 100 : ℝ) →
        (K : ℝ) ≤ T →
        8 * Y * Real.log T ≤ K →
      ∀ {rho : ℂ}, IsNontrivialZero rho →
        1 / 2 < rho.re →
        T ≤ |rho.im| → |rho.im| ≤ 2 * T →
        ClassicalDetectorTypeII M Y rho ∨
          ClassicalDetectorTypeILog T M K Y rho := by
  filter_upwards
    [eventually_norm_classicalDetectorRetainedResidue_le_one_ninth,
      eventually_ge_atTop (81 : ℝ)] with T hresidue hT
  intro Y hYLower hYT M K hM hMK hMUpper hKT hKLower
    rho hrho hbeta hgammaLower hgammaUpper
  have hYpos : 0 < Y := by linarith
  have hhead :=
    norm_classicalDetector_headError_le_one_ninth hYLower
  have htail :=
    norm_classicalDetectorFarTail_le_one_ninth_of_source_scale
      hT hYLower hYT M hKT hKLower (nontrivial_zero_re_pos hrho)
  have hres :=
    hresidue Y (by linarith) hYT M hMUpper hrho
      hgammaLower hgammaUpper
  have hdichotomy :=
    classicalDetector_typeI_or_typeII hM hMK hrho hbeta hYpos
      hhead htail hres
  rcases hdichotomy with hII | hI
  · exact Or.inl hII
  · have hexpT : Real.exp 1 ≤ T :=
      Real.exp_one_lt_three.le.trans (by linarith)
    have hK : 1 ≤ K := by omega
    exact Or.inr
      (classicalDetectorTypeILog_of_typeI hexpT hK hKT hI)

/-- The smoothing scale used in Maynard--Pratt, Appendix C, Lemma 23. -/
def classicalDetectorSourceY (T : ℝ) : ℝ :=
  Real.sqrt T

/-- The source mollifier length, with the real quantity rounded down to a natural number. -/
def classicalDetectorSourceM (T : ℝ) : ℕ :=
  ⌊2 * T ^ (1 / 100 : ℝ)⌋₊

/-- The source truncation height `Y (log T)^2 / 2`, rounded up to a natural number. -/
def classicalDetectorSourceK (T : ℝ) : ℕ :=
  ⌈Real.sqrt T * Real.log T ^ (2 : ℕ) / 2⌉₊

/-- The literal source scales eventually satisfy every hypothesis of the audited finite
detector.  This is the only place where the source's real-valued scale notation is reconciled
with natural-number Dirichlet-polynomial cutoffs. -/
theorem eventually_classicalDetectorSourceParameters :
    ∀ᶠ T : ℝ in atTop,
      9 ≤ classicalDetectorSourceY T ∧
      classicalDetectorSourceY T ≤ T ∧
      1 ≤ classicalDetectorSourceM T ∧
      classicalDetectorSourceM T + 1 ≤ classicalDetectorSourceK T ∧
      (classicalDetectorSourceM T : ℝ) ≤
        2 * T ^ (1 / 100 : ℝ) ∧
      (classicalDetectorSourceK T : ℝ) ≤ T ∧
      8 * classicalDetectorSourceY T * Real.log T ≤
        classicalDetectorSourceK T := by
  have hratio :
      Tendsto
        (fun T : ℝ =>
          Real.log T ^ (2 : ℕ) / T ^ (1 / 2 : ℝ))
        atTop (𝓝 0) := by
    simpa only [Real.rpow_two] using
      (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
        (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have hratioSmall :
      ∀ᶠ T : ℝ in atTop,
        Real.log T ^ (2 : ℕ) / T ^ (1 / 2 : ℝ) < 1 :=
    (tendsto_order.1 hratio).2 1 zero_lt_one
  filter_upwards
    [hratioSmall, eventually_ge_atTop (81 : ℝ),
      eventually_ge_atTop (Real.exp 16)] with T hratioT hT81 hTexp
  have hTpos : 0 < T := by linarith
  have hTOne : 1 ≤ T := by linarith
  have hlog : 16 ≤ Real.log T := by
    calc
      16 = Real.log (Real.exp 16) := by rw [Real.log_exp]
      _ ≤ Real.log T := Real.log_le_log (Real.exp_pos 16) hTexp
  have hsqrtPos : 0 < Real.sqrt T := Real.sqrt_pos.2 hTpos
  have hsqrtSq : Real.sqrt T * Real.sqrt T = T :=
    Real.mul_self_sqrt hTpos.le
  have hlogSq :
      Real.log T ^ (2 : ℕ) ≤ Real.sqrt T := by
    have hden : 0 < T ^ (1 / 2 : ℝ) :=
      Real.rpow_pos_of_pos hTpos _
    have hraw :
        Real.log T ^ (2 : ℕ) <
          T ^ (1 / 2 : ℝ) :=
      (div_lt_one hden).mp hratioT
    simpa only [← Real.sqrt_eq_rpow] using hraw.le
  have hsourceYLower :
      9 ≤ classicalDetectorSourceY T := by
    rw [classicalDetectorSourceY, Real.le_sqrt (by norm_num) hTpos.le]
    nlinarith
  have hsourceYUpper :
      classicalDetectorSourceY T ≤ T := by
    rw [classicalDetectorSourceY, Real.sqrt_le_iff]
    constructor
    · linarith
    · nlinarith
  have hpowerSqrt :
      T ^ (1 / 100 : ℝ) ≤ Real.sqrt T := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hTOne (by norm_num)
  have hsourceMOne :
      1 ≤ classicalDetectorSourceM T := by
    rw [classicalDetectorSourceM, Nat.one_le_floor_iff]
    have honePower :
        1 ≤ T ^ (1 / 100 : ℝ) :=
      Real.one_le_rpow hTOne (by norm_num)
    linarith
  have hsourceMUpper :
      (classicalDetectorSourceM T : ℝ) ≤
        2 * T ^ (1 / 100 : ℝ) := by
    rw [classicalDetectorSourceM]
    exact Nat.floor_le (by positivity)
  have hcutoffNonneg :
      0 ≤ Real.sqrt T * Real.log T ^ (2 : ℕ) / 2 := by
    positivity
  have hsourceKLower :
      Real.sqrt T * Real.log T ^ (2 : ℕ) / 2 ≤
        (classicalDetectorSourceK T : ℝ) := by
    rw [classicalDetectorSourceK]
    exact Nat.le_ceil _
  have hcutoffUpper :
      Real.sqrt T * Real.log T ^ (2 : ℕ) / 2 + 1 ≤ T := by
    have hmul :
        Real.sqrt T * Real.log T ^ (2 : ℕ) ≤ T := by
      calc
        Real.sqrt T * Real.log T ^ (2 : ℕ) ≤
            Real.sqrt T * Real.sqrt T :=
          mul_le_mul_of_nonneg_left hlogSq (Real.sqrt_nonneg T)
        _ = T := hsqrtSq
    nlinarith
  have hsourceKUpper :
      (classicalDetectorSourceK T : ℝ) ≤ T := by
    have hceil :
        (classicalDetectorSourceK T : ℝ) <
          Real.sqrt T * Real.log T ^ (2 : ℕ) / 2 + 1 := by
      rw [classicalDetectorSourceK]
      exact Nat.ceil_lt_add_one hcutoffNonneg
    linarith
  have hsourceScaleLower :
      8 * classicalDetectorSourceY T * Real.log T ≤
        (classicalDetectorSourceK T : ℝ) := by
    apply le_trans _ hsourceKLower
    rw [classicalDetectorSourceY]
    have hsqrtNonneg := Real.sqrt_nonneg T
    nlinarith [sq_nonneg (Real.log T)]
  have hsourceMKReal :
      (classicalDetectorSourceM T : ℝ) + 1 ≤
        (classicalDetectorSourceK T : ℝ) := by
    apply le_trans _ hsourceKLower
    calc
      (classicalDetectorSourceM T : ℝ) + 1 ≤
          2 * T ^ (1 / 100 : ℝ) + 1 := by
        linarith
      _ ≤ 3 * Real.sqrt T := by
        have hsqrtOne : 1 ≤ Real.sqrt T := by
          simpa only [Real.one_le_sqrt] using hTOne
        linarith
      _ ≤ Real.sqrt T * Real.log T ^ (2 : ℕ) / 2 := by
        have hthree :
            (3 : ℝ) ≤ Real.log T ^ (2 : ℕ) / 2 := by
          nlinarith [sq_nonneg (Real.log T)]
        calc
          3 * Real.sqrt T = Real.sqrt T * 3 := by ring
          _ ≤ Real.sqrt T * (Real.log T ^ (2 : ℕ) / 2) :=
            mul_le_mul_of_nonneg_left hthree (Real.sqrt_nonneg T)
          _ = Real.sqrt T * Real.log T ^ (2 : ℕ) / 2 := by ring
  have hsourceMK :
      classicalDetectorSourceM T + 1 ≤
        classicalDetectorSourceK T := by
    exact_mod_cast hsourceMKReal
  exact ⟨hsourceYLower, hsourceYUpper, hsourceMOne, hsourceMK,
    hsourceMUpper, hsourceKUpper, hsourceScaleLower⟩

/-- The actual Type-I/Type-II conclusion at the literal Maynard--Pratt smoothing, mollifier,
and truncation scales. -/
theorem eventually_classicalDetectorSource_typeILog_or_typeII :
    ∀ᶠ T : ℝ in atTop,
      ∀ {rho : ℂ}, IsNontrivialZero rho →
        1 / 2 < rho.re →
        T ≤ |rho.im| → |rho.im| ≤ 2 * T →
        ClassicalDetectorTypeII
            (classicalDetectorSourceM T)
            (classicalDetectorSourceY T) rho ∨
          ClassicalDetectorTypeILog T
            (classicalDetectorSourceM T)
            (classicalDetectorSourceK T)
            (classicalDetectorSourceY T) rho := by
  filter_upwards
    [eventually_classicalDetector_typeILog_or_typeII,
      eventually_classicalDetectorSourceParameters] with T hdichotomy hparameters
  rcases hparameters with
    ⟨hYLower, hYT, hMOne, hMK, hMUpper, hKT, hKLower⟩
  intro rho hrho hbeta hgammaLower hgammaUpper
  exact hdichotomy
    (classicalDetectorSourceY T) hYLower hYT
    (classicalDetectorSourceM T) (classicalDetectorSourceK T)
    hMOne hMK hMUpper hKT hKLower
    hrho hbeta hgammaLower hgammaUpper

/-- Aggregate certificate for the finite dyadic edge of the classical zero-density
detector.  It deliberately stops at the source Type-I/Type-II alternative. -/
structure ClassicalDetectorDyadicDichotomyCertificate : Prop where
  coefficientBound :
    ∀ M n : ℕ,
      ‖classicalDetectorCoefficient M n‖ ≤ n.divisors.card
  finiteCutoff :
    ∀ {M K : ℕ}, 1 ≤ M → M + 1 ≤ K →
      ∀ {rho : ℂ}, 0 < rho.re →
      ∀ {Y : ℝ}, 0 < Y →
        classicalDetectorSmoothedSeries M Y rho =
          Complex.exp (-(1 / Y : ℝ)) +
            (∑ n ∈ Finset.Ico (M + 1) K,
              classicalDetectorSmoothedTerm M Y rho n) +
            classicalDetectorFarTail M K Y rho
  exactBlockSum :
    ∀ (M K : ℕ) (Y : ℝ) (rho : ℂ),
      (∑ j : Fin (classicalDetectorDyadicIndexCount K),
          classicalDetectorDyadicBlock M K Y rho j) =
        ∑ n ∈ Finset.Ico (M + 1) K,
          classicalDetectorSmoothedTerm M Y rho n
  blockRange :
    ∀ {M K n : ℕ}
      {j : Fin (classicalDetectorDyadicIndexCount K)},
      n ∈ Finset.Ico (M + 1) K →
      classicalDetectorDyadicIndex K n = j →
        2 ^ (j : ℕ) ≤ n ∧ n < 2 ^ ((j : ℕ) + 1)
  farTail :
    ∀ (M K : ℕ) {Y : ℝ}, 0 < Y →
      ∀ {rho : ℂ}, 0 < rho.re → 2 * Y ≤ K →
        ‖classicalDetectorFarTail M K Y rho‖ ≤
          (K : ℝ) * (1 + 2 * Y) *
            Real.exp (-((K : ℝ) / Y))
  blockCount :
    ∀ {K : ℕ}, 1 ≤ K →
      ∀ {T : ℝ}, Real.exp 1 ≤ T → (K : ℝ) ≤ T →
        (classicalDetectorDyadicIndexCount K : ℝ) ≤
          3 * Real.log T
  sourceParameters :
    ∀ᶠ T : ℝ in atTop,
      9 ≤ classicalDetectorSourceY T ∧
      classicalDetectorSourceY T ≤ T ∧
      1 ≤ classicalDetectorSourceM T ∧
      classicalDetectorSourceM T + 1 ≤ classicalDetectorSourceK T ∧
      (classicalDetectorSourceM T : ℝ) ≤
        2 * T ^ (1 / 100 : ℝ) ∧
      (classicalDetectorSourceK T : ℝ) ≤ T ∧
      8 * classicalDetectorSourceY T * Real.log T ≤
        classicalDetectorSourceK T
  sourceDichotomy :
    ∀ᶠ T : ℝ in atTop,
      ∀ {rho : ℂ}, IsNontrivialZero rho →
        1 / 2 < rho.re →
        T ≤ |rho.im| → |rho.im| ≤ 2 * T →
        ClassicalDetectorTypeII
            (classicalDetectorSourceM T)
            (classicalDetectorSourceY T) rho ∨
          ClassicalDetectorTypeILog T
            (classicalDetectorSourceM T)
            (classicalDetectorSourceK T)
            (classicalDetectorSourceY T) rho

theorem classicalDetectorDyadicDichotomy_endpoint :
    ClassicalDetectorDyadicDichotomyCertificate where
  coefficientBound := norm_classicalDetectorCoefficient_le_card_divisors
  finiteCutoff := fun hM hMK _ hrhoRe _ hY =>
    classicalDetectorSmoothedSeries_eq_head_add_middle_add_farTail
      hM hMK hrhoRe hY
  exactBlockSum := sum_classicalDetectorDyadicBlock_eq_middle
  blockRange := fun hn hj =>
    classicalDetectorDyadicBlock_membership_range hn hj
  farTail := fun M K _ hY _ hrhoRe hKY =>
    norm_classicalDetectorFarTail_le_explicit
      M K hY hrhoRe hKY
  blockCount := fun hK _ hT hKT =>
    classicalDetectorDyadicIndexCount_le_three_log hK hT hKT
  sourceParameters := eventually_classicalDetectorSourceParameters
  sourceDichotomy := eventually_classicalDetectorSource_typeILog_or_typeII

end

end LeanLab.Riemann
