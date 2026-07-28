import LeanLab.Riemann.HardyCriticalLineSign
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Selberg's local sign-change producer

This module isolates the local deterministic mechanism in Selberg's critical-line method.
A finite root mollifier is squared on the critical line, so it cannot reverse the sign of the
actual real xi coordinate. A strict gap in the integral triangle inequality forces both signs
and therefore an actual critical-line zeta zero.

No Selberg moment estimate or positive-proportion conclusion is asserted.
-/

open Complex MeasureTheory Set

namespace LeanLab.Riemann

noncomputable section

/-- A finite root mollifier. Source-specific tapering can be absorbed into `coeff`. -/
def selbergRootMollifier (coeff : ℕ → ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, coeff n * (n : ℂ) ^ (-s)

/-- The nonnegative square of the root mollifier on the critical line. -/
def selbergRootSquare (coeff : ℕ → ℂ) (N : ℕ) (t : ℝ) : ℝ :=
  Complex.normSq (selbergRootMollifier coeff N (hardyCriticalLinePoint t))

/-- Selberg's squared-root-mollified version of the actual real critical-line xi coordinate. -/
def selbergMollifiedHardyXi (coeff : ℕ → ℂ) (N : ℕ) (t : ℝ) : ℝ :=
  hardyXi t * selbergRootSquare coeff N t

theorem continuous_selbergRootMollifier_criticalLine (coeff : ℕ → ℂ) (N : ℕ) :
    Continuous (fun t : ℝ =>
      selbergRootMollifier coeff N (hardyCriticalLinePoint t)) := by
  simp only [selbergRootMollifier]
  apply continuous_finsetSum
  intro n hn
  have hn0 : (n : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_zero_of_lt (Finset.mem_Icc.mp hn).1)
  have hpow : Continuous (fun t : ℝ => (n : ℂ) ^ (-hardyCriticalLinePoint t)) :=
    (continuous_iff_continuousAt.mpr fun _ => continuousAt_const_cpow hn0).comp
      continuous_hardyCriticalLinePoint.neg
  exact continuous_const.mul hpow

theorem continuous_selbergRootSquare (coeff : ℕ → ℂ) (N : ℕ) :
    Continuous (selbergRootSquare coeff N) :=
  Complex.continuous_normSq.comp
    (continuous_selbergRootMollifier_criticalLine coeff N)

theorem selbergRootSquare_nonneg (coeff : ℕ → ℂ) (N : ℕ) (t : ℝ) :
    0 ≤ selbergRootSquare coeff N t :=
  Complex.normSq_nonneg _

theorem continuous_selbergMollifiedHardyXi (coeff : ℕ → ℂ) (N : ℕ) :
    Continuous (selbergMollifiedHardyXi coeff N) :=
  continuous_hardyXi.mul (continuous_selbergRootSquare coeff N)

theorem hardyXi_pos_of_selbergMollifiedHardyXi_pos
    {coeff : ℕ → ℂ} {N : ℕ} {t : ℝ}
    (h : 0 < selbergMollifiedHardyXi coeff N t) :
    0 < hardyXi t := by
  by_contra hnot
  have hbase : hardyXi t ≤ 0 := le_of_not_gt hnot
  have hproduct :
      selbergMollifiedHardyXi coeff N t ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg hbase
      (selbergRootSquare_nonneg coeff N t)
  exact (not_lt_of_ge hproduct) h

theorem hardyXi_neg_of_selbergMollifiedHardyXi_neg
    {coeff : ℕ → ℂ} {N : ℕ} {t : ℝ}
    (h : selbergMollifiedHardyXi coeff N t < 0) :
    hardyXi t < 0 := by
  by_contra hnot
  have hbase : 0 ≤ hardyXi t := le_of_not_gt hnot
  have hproduct :
      0 ≤ selbergMollifiedHardyXi coeff N t := by
    exact mul_nonneg hbase (selbergRootSquare_nonneg coeff N t)
  exact (not_lt_of_ge hproduct) h

/-- A strict local triangle gap for a real interval integral. -/
def SelbergLocalIntegralGap (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  a < b ∧
    |∫ t in a..b, f t| < ∫ t in a..b, |f t|

/-- The strict integral triangle gap forces the function to take both strict signs. -/
theorem exists_neg_and_pos_of_localIntegralGap
    {f : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn f (Icc a b))
    (hgap : SelbergLocalIntegralGap f a b) :
    (∃ u ∈ Icc a b, f u < 0) ∧
      ∃ v ∈ Icc a b, 0 < f v := by
  rcases hgap with ⟨hab, hstrict⟩
  have _hintervalIntegrable : IntervalIntegrable f volume a b :=
    hcont.intervalIntegrable_of_Icc hab.le
  constructor
  · by_contra hnone
    push Not at hnone
    have hnonneg : ∀ x ∈ Icc a b, 0 ≤ f x := by
      intro x hx
      exact hnone x hx
    have habs :
        (∫ x in a..b, |f x|) = ∫ x in a..b, f x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hab.le] at hx
      exact abs_of_nonneg (hnonneg x hx)
    have hintegral : 0 ≤ ∫ x in a..b, f x :=
      intervalIntegral.integral_nonneg hab.le hnonneg
    rw [habs, abs_of_nonneg hintegral] at hstrict
    exact (lt_irrefl _ hstrict)
  · by_contra hnone
    push Not at hnone
    have hnonpos : ∀ x ∈ Icc a b, f x ≤ 0 := by
      intro x hx
      exact hnone x hx
    have habs :
        (∫ x in a..b, |f x|) = -(∫ x in a..b, f x) := by
      calc
        (∫ x in a..b, |f x|) =
            ∫ x in a..b, -f x := by
              apply intervalIntegral.integral_congr
              intro x hx
              rw [uIcc_of_le hab.le] at hx
              exact abs_of_nonpos (hnonpos x hx)
        _ = -(∫ x in a..b, f x) := by
          rw [intervalIntegral.integral_neg]
    have hintegral : (∫ x in a..b, f x) ≤ 0 := by
      have hnegIntegral : 0 ≤ ∫ x in a..b, -f x :=
        intervalIntegral.integral_nonneg hab.le
          (fun x hx => neg_nonneg.mpr (hnonpos x hx))
      rw [intervalIntegral.integral_neg] at hnegIntegral
      exact neg_nonneg.mp hnegIntegral
    rw [habs, abs_of_nonpos hintegral] at hstrict
    exact (lt_irrefl _ hstrict)

/-- A Selberg local triangle gap produces an actual nontrivial zeta zero strictly inside the
interval. The proof uses opposite signs of `hardyXi`, not a zero of the mollified product. -/
theorem exists_criticalLine_zero_of_selbergLocalIntegralGap
    {coeff : ℕ → ℂ} {N : ℕ} {a b : ℝ}
    (hgap : SelbergLocalIntegralGap
      (selbergMollifiedHardyXi coeff N) a b) :
    ∃ t ∈ Ioo a b,
      IsNontrivialZero (hardyCriticalLinePoint t) ∧
        OnCriticalLine (hardyCriticalLinePoint t) := by
  obtain ⟨⟨u, hu, huneg⟩, ⟨v, hv, hvpos⟩⟩ :=
    exists_neg_and_pos_of_localIntegralGap
      (continuous_selbergMollifiedHardyXi coeff N).continuousOn hgap
  have hxiU : hardyXi u < 0 :=
    hardyXi_neg_of_selbergMollifiedHardyXi_neg huneg
  have hxiV : 0 < hardyXi v :=
    hardyXi_pos_of_selbergMollifiedHardyXi_pos hvpos
  by_cases huv : u ≤ v
  · have hzeroMem : (0 : ℝ) ∈ Ioo (hardyXi u) (hardyXi v) :=
      ⟨hxiU, hxiV⟩
    obtain ⟨t, ht, hzero⟩ :=
      intermediate_value_Ioo huv continuous_hardyXi.continuousOn hzeroMem
    have htab : t ∈ Ioo a b :=
      ⟨hu.1.trans_lt ht.1, ht.2.trans_le hv.2⟩
    refine ⟨t, htab, (hardyXi_eq_zero_iff_isNontrivialZero t).mp ?_, ?_⟩
    · exact hzero
    · exact onCriticalLine_hardyCriticalLinePoint t
  · have hvu : v ≤ u := le_of_not_ge huv
    have hzeroMem : (0 : ℝ) ∈ Ioo (hardyXi u) (hardyXi v) :=
      ⟨hxiU, hxiV⟩
    obtain ⟨t, ht, hzero⟩ :=
      intermediate_value_Ioo' hvu continuous_hardyXi.continuousOn hzeroMem
    have htab : t ∈ Ioo a b :=
      ⟨hv.1.trans_lt ht.1, ht.2.trans_le hu.2⟩
    refine ⟨t, htab, (hardyXi_eq_zero_iff_isNontrivialZero t).mp ?_, ?_⟩
    · exact hzero
    · exact onCriticalLine_hardyCriticalLinePoint t

/-- Strong ordering of a finite family of open intervals. -/
def SelbergStronglySeparated {n : ℕ} (left right : Fin n → ℝ) : Prop :=
  ∀ ⦃i j : Fin n⦄, i < j → right i ≤ left j

/-- Separated detected intervals yield distinct actual critical-line zero ordinates. -/
theorem exists_injective_criticalLine_zeros_of_selbergLocalIntegralGaps
    {n : ℕ} {coeff : ℕ → ℂ} {N : ℕ}
    {left right : Fin n → ℝ}
    (hsep : SelbergStronglySeparated left right)
    (hgap : ∀ i, SelbergLocalIntegralGap
      (selbergMollifiedHardyXi coeff N) (left i) (right i)) :
    ∃ zeroOrdinate : Fin n → ℝ,
      Function.Injective zeroOrdinate ∧
        ∀ i, zeroOrdinate i ∈ Ioo (left i) (right i) ∧
          IsNontrivialZero (hardyCriticalLinePoint (zeroOrdinate i)) ∧
            OnCriticalLine (hardyCriticalLinePoint (zeroOrdinate i)) := by
  have hexists : ∀ i : Fin n, ∃ t ∈ Ioo (left i) (right i),
      IsNontrivialZero (hardyCriticalLinePoint t) ∧
        OnCriticalLine (hardyCriticalLinePoint t) := by
    intro i
    exact exists_criticalLine_zero_of_selbergLocalIntegralGap (hgap i)
  choose zeroOrdinate hmem hzero honLine using hexists
  refine ⟨zeroOrdinate, ?_, fun i => ⟨hmem i, hzero i, honLine i⟩⟩
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with hijOrder | hjiOrder
  · have hlt : zeroOrdinate i < zeroOrdinate j :=
      (hmem i).2.trans <| (hsep hijOrder).trans_lt (hmem j).1
    exact hlt.ne hij
  · have hlt : zeroOrdinate j < zeroOrdinate i :=
      (hmem j).2.trans <| (hsep hjiOrder).trans_lt (hmem i).1
    exact hlt.ne hij.symm

/-- Without the nonnegative square, a multiplier can manufacture a sign change while the base
function is everywhere nonzero. -/
theorem arbitrary_multiplier_false_sign_change :
    ∃ base multiplier : ℝ → ℝ,
      (∀ t, base t ≠ 0) ∧
        base (-1) * multiplier (-1) < 0 ∧
          0 < base 1 * multiplier 1 := by
  refine ⟨fun _ => 1, fun t => t, ?_, by norm_num, by norm_num⟩
  intro t
  norm_num

/-- The complete local deterministic endpoint of the Selberg sign-change campaign. -/
structure SelbergLocalSignChangeCertificate : Prop where
  rootContinuity :
    ∀ coeff N, Continuous (fun t : ℝ =>
      selbergRootMollifier coeff N (hardyCriticalLinePoint t))
  squareNonnegative :
    ∀ coeff N t, 0 ≤ selbergRootSquare coeff N t
  localTwoSigns :
    ∀ {f : ℝ → ℝ} {a b : ℝ}, ContinuousOn f (Icc a b) →
      SelbergLocalIntegralGap f a b →
        (∃ u ∈ Icc a b, f u < 0) ∧ ∃ v ∈ Icc a b, 0 < f v
  actualZeroConsumer :
    ∀ {coeff : ℕ → ℂ} {N : ℕ} {a b : ℝ},
      SelbergLocalIntegralGap (selbergMollifiedHardyXi coeff N) a b →
        ∃ t ∈ Ioo a b,
          IsNontrivialZero (hardyCriticalLinePoint t) ∧
            OnCriticalLine (hardyCriticalLinePoint t)
  separatedConsumer :
    ∀ {n : ℕ} {coeff : ℕ → ℂ} {N : ℕ} {left right : Fin n → ℝ},
      SelbergStronglySeparated left right →
      (∀ i, SelbergLocalIntegralGap
        (selbergMollifiedHardyXi coeff N) (left i) (right i)) →
        ∃ zeroOrdinate : Fin n → ℝ,
          Function.Injective zeroOrdinate ∧
            ∀ i, zeroOrdinate i ∈ Ioo (left i) (right i) ∧
              IsNontrivialZero (hardyCriticalLinePoint (zeroOrdinate i)) ∧
                OnCriticalLine (hardyCriticalLinePoint (zeroOrdinate i))
  arbitraryMultiplierControl :
    ∃ base multiplier : ℝ → ℝ,
      (∀ t, base t ≠ 0) ∧
        base (-1) * multiplier (-1) < 0 ∧
          0 < base 1 * multiplier 1

theorem selbergLocalSignChange_endpoint :
    SelbergLocalSignChangeCertificate where
  rootContinuity := continuous_selbergRootMollifier_criticalLine
  squareNonnegative := selbergRootSquare_nonneg
  localTwoSigns := exists_neg_and_pos_of_localIntegralGap
  actualZeroConsumer := exists_criticalLine_zero_of_selbergLocalIntegralGap
  separatedConsumer :=
    exists_injective_criticalLine_zeros_of_selbergLocalIntegralGaps
  arbitraryMultiplierControl := arbitrary_multiplier_false_sign_change

end

end LeanLab.Riemann
