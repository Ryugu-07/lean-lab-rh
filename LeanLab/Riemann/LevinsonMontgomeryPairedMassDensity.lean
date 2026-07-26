import LeanLab.Riemann.SpeiserCountingEquivalence
import LeanLab.Riemann.LiSymmetricZeroFormula
import LeanLab.Riemann.PairCorrelationHorizontalMultiplicity

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Levinson--Montgomery paired zero mass and the dense branch

This file formalizes equations (2.2)--(2.3) and the integer-height density amplification in
Levinson and Montgomery's 1974 proof of Speiser's criterion.

The mass is indexed by the actual multiplicity-bearing xi divisor.  Each zero `rho` is paired
with `1 - conj rho`, and every paired term is divided by two.  Off the critical line, the two
members of an orbit therefore reproduce the source coefficient two; on the critical line, the
fixed-value pair contributes exactly once.
-/

namespace LeanLab.Riemann

open Complex Function Set
open scoped BigOperators ComplexConjugate Topology

noncomputable section

def lmConjEquiv : RiemannXiDivisorZeroIndex ≃ RiemannXiDivisorZeroIndex :=
  divisorZeroIndexConjEquiv differentiable_riemannXi
    ⟨1, riemannXi_one_ne_zero⟩ riemannXi_conj

/-- The multiplicity-preserving source pairing `rho |-> 1 - conj rho`. -/
def levinsonMontgomeryPairedZeroEquiv :
    RiemannXiDivisorZeroIndex ≃ RiemannXiDivisorZeroIndex :=
  riemannXiDivisorZeroReflectEquiv.trans lmConjEquiv

@[simp] theorem lmConjEquiv_val (p : RiemannXiDivisorZeroIndex) :
    riemannXiDivisorZeroValue (lmConjEquiv p) =
      conj (riemannXiDivisorZeroValue p) := by
  rfl

@[simp] theorem levinsonMontgomeryPairedZeroEquiv_val
    (p : RiemannXiDivisorZeroIndex) :
    riemannXiDivisorZeroValue (levinsonMontgomeryPairedZeroEquiv p) =
      1 - conj (riemannXiDivisorZeroValue p) := by
  simp [levinsonMontgomeryPairedZeroEquiv]

/-- Half of the real reciprocal sum over one functional-equation pair. -/
def levinsonMontgomeryPairedReciprocalTerm
    (s : ℂ) (p : RiemannXiDivisorZeroIndex) : ℝ :=
  ((1 / (s - riemannXiDivisorZeroValue p) +
      1 / (s - riemannXiDivisorZeroValue
        (levinsonMontgomeryPairedZeroEquiv p))).re) / 2

/-- One globally averaged term of the Levinson--Montgomery mass `I₁(s)`. -/
def levinsonMontgomeryPairedKernel
    (s : ℂ) (p : RiemannXiDivisorZeroIndex) : ℝ :=
  let rho := riemannXiDivisorZeroValue p
  ((s.im - rho.im) ^ 2 + (s.re - 1 / 2) ^ 2 - (rho.re - 1 / 2) ^ 2) /
    (Complex.normSq (s - rho) *
      Complex.normSq (s - riemannXiDivisorZeroValue
        (levinsonMontgomeryPairedZeroEquiv p)))

theorem levinsonMontgomeryPairedReciprocalTerm_eq
    (s : ℂ) (p : RiemannXiDivisorZeroIndex)
    (hp : s ≠ riemannXiDivisorZeroValue p)
    (hq : s ≠ riemannXiDivisorZeroValue
      (levinsonMontgomeryPairedZeroEquiv p)) :
    levinsonMontgomeryPairedReciprocalTerm s p =
      -(1 / 2 - s.re) * levinsonMontgomeryPairedKernel s p := by
  rw [levinsonMontgomeryPairedReciprocalTerm, levinsonMontgomeryPairedKernel]
  simp only [one_div, add_re, inv_re, sub_re, one_re,
    levinsonMontgomeryPairedZeroEquiv_val,
    Complex.conj_re, Complex.conj_im, sub_im, one_im, zero_sub, neg_neg,
    Complex.normSq_apply]
  have hpNorm : (s.re - (riemannXiDivisorZeroValue p).re) ^ 2 +
      (s.im - (riemannXiDivisorZeroValue p).im) ^ 2 ≠ 0 := by
    simpa [Complex.normSq_apply, pow_two] using
      (Complex.normSq_eq_zero.not.mpr (sub_ne_zero.mpr hp))
  have hqNorm : (s.re - (1 - (riemannXiDivisorZeroValue p).re)) ^ 2 +
      (s.im - (riemannXiDivisorZeroValue p).im) ^ 2 ≠ 0 := by
    have h := Complex.normSq_eq_zero.not.mpr (sub_ne_zero.mpr hq)
    simpa [Complex.normSq_apply, pow_two] using h
  field_simp [hpNorm, hqNorm]
  ring

theorem summable_re_inv_riemannXiDivisorZeroValue :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      (1 / riemannXiDivisorZeroValue p).re) := by
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_)
    summable_riemannXiDivisorZeroIndex_norm_inv_sq
  · rw [one_div, Complex.inv_re]
    exact div_nonneg (speiser_nontrivial_zero_re_pos
      (riemannXiDivisorZeroIndex_val_isNontrivialZero p)).le
      (Complex.normSq_nonneg _)
  · let rho := riemannXiDivisorZeroValue p
    have hrhoZero := riemannXiDivisorZeroIndex_val_isNontrivialZero p
    have hrho0 : rho ≠ 0 :=
      Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p
    have hnorm : 0 < ‖rho‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hrho0)
    rw [one_div, Complex.inv_re, Complex.normSq_eq_norm_sq]
    calc
      rho.re / ‖rho‖ ^ 2 ≤ 1 / ‖rho‖ ^ 2 := by
        exact (div_le_div_iff_of_pos_right hnorm).2
          (nontrivial_zero_re_lt_one hrhoZero).le
      _ = ‖rho‖⁻¹ ^ 2 := by rw [one_div, inv_pow]

theorem summable_levinsonMontgomeryPairedReciprocalTerm
    {s : ℂ} (hxi : riemannXi s ≠ 0) :
    Summable (levinsonMontgomeryPairedReciprocalTerm s) := by
  have hs : s ∈ riemannXiNonzeroSet := hxi
  have hlog := summable_riemannXiLogDerivZeroTerm_of_mem_nonzeroSet hs
  have hlogRe : Summable (fun p : RiemannXiDivisorZeroIndex =>
      (riemannXiLogDerivZeroTerm p s).re) := by
    simpa [Function.comp_def] using
      hlog.map Complex.reCLM Complex.reCLM.continuous
  have hlogPairRe : Summable (fun p : RiemannXiDivisorZeroIndex =>
      (riemannXiLogDerivZeroTerm
        (levinsonMontgomeryPairedZeroEquiv p) s).re) :=
    hlogRe.comp_injective levinsonMontgomeryPairedZeroEquiv.injective
  have hinvPairRe : Summable (fun p : RiemannXiDivisorZeroIndex =>
      (1 / riemannXiDivisorZeroValue
        (levinsonMontgomeryPairedZeroEquiv p)).re) :=
    summable_re_inv_riemannXiDivisorZeroValue.comp_injective
      levinsonMontgomeryPairedZeroEquiv.injective
  refine (hlogRe.add hlogPairRe |>.sub
    summable_re_inv_riemannXiDivisorZeroValue |>.sub hinvPairRe).mul_left (1 / 2) |>.congr ?_
  intro p
  simp only [levinsonMontgomeryPairedReciprocalTerm,
    riemannXiLogDerivZeroTerm, add_re]
  ring

theorem summable_levinsonMontgomeryPairedKernel
    {s : ℂ} (hsRe : s.re < 1 / 2)
    (hxi : riemannXi s ≠ 0) :
    Summable (levinsonMontgomeryPairedKernel s) := by
  have ha : 1 / 2 - s.re ≠ 0 := ne_of_gt (sub_pos.mpr hsRe)
  have hscaled :=
    (summable_levinsonMontgomeryPairedReciprocalTerm hxi).mul_left
      (-(1 / (1 / 2 - s.re)))
  refine hscaled.congr (fun p => ?_)
  have hp : s ≠ riemannXiDivisorZeroValue p := by
    intro h
    apply hxi
    rw [h]
    exact riemannXi_eq_zero_of_isNontrivialZero
      (riemannXiDivisorZeroIndex_val_isNontrivialZero p)
  have hq : s ≠ riemannXiDivisorZeroValue
      (levinsonMontgomeryPairedZeroEquiv p) := by
    intro h
    apply hxi
    rw [h]
    exact riemannXi_eq_zero_of_isNontrivialZero
      (riemannXiDivisorZeroIndex_val_isNontrivialZero
        (levinsonMontgomeryPairedZeroEquiv p))
  rw [levinsonMontgomeryPairedReciprocalTerm_eq s p hp hq]
  have ha2 : 1 - 2 * s.re ≠ 0 := by linarith
  field_simp [ha, ha2]

/-- The convergent real paired reciprocal zero sum in equation (2.3). -/
def levinsonMontgomeryRealPairedZeroSum (s : ℂ) : ℝ :=
  ∑' p : RiemannXiDivisorZeroIndex,
    levinsonMontgomeryPairedReciprocalTerm s p

/-- The multiplicity-bearing paired zero mass `I₁(s)` from equation (2.2). -/
def levinsonMontgomeryPairedZeroMass (s : ℂ) : ℝ :=
  ∑' p : RiemannXiDivisorZeroIndex,
    levinsonMontgomeryPairedKernel s p

theorem levinsonMontgomery_real_paired_zero_sum_eq
    {s : ℂ} (_hsRe : s.re < 1 / 2)
    (hxi : riemannXi s ≠ 0) :
    levinsonMontgomeryRealPairedZeroSum s =
      -(1 / 2 - s.re) * levinsonMontgomeryPairedZeroMass s := by
  rw [levinsonMontgomeryRealPairedZeroSum,
    levinsonMontgomeryPairedZeroMass]
  calc
    (∑' p : RiemannXiDivisorZeroIndex,
        levinsonMontgomeryPairedReciprocalTerm s p) =
        ∑' p : RiemannXiDivisorZeroIndex,
          (-(1 / 2 - s.re) * levinsonMontgomeryPairedKernel s p) := by
      apply tsum_congr
      intro p
      apply levinsonMontgomeryPairedReciprocalTerm_eq
      · intro h
        apply hxi
        rw [h]
        exact riemannXi_eq_zero_of_isNontrivialZero
          (riemannXiDivisorZeroIndex_val_isNontrivialZero p)
      · intro h
        apply hxi
        rw [h]
        exact riemannXi_eq_zero_of_isNontrivialZero
          (riemannXiDivisorZeroIndex_val_isNontrivialZero
            (levinsonMontgomeryPairedZeroEquiv p))
    _ = -(1 / 2 - s.re) *
        ∑' p : RiemannXiDivisorZeroIndex,
          levinsonMontgomeryPairedKernel s p := by
      rw [tsum_mul_left]

theorem exists_upperLeft_zero_abs_im_sub_lt_half_of_pairedMass_neg
    {s : ℂ} (_hsRe : s.re < 1 / 2) (hsIm : 1 ≤ s.im)
    (hxi : riemannXi s ≠ 0)
    (hmass : levinsonMontgomeryPairedZeroMass s < 0) :
    ∃ rho : ℂ, IsNontrivialZero rho ∧
      0 < rho.re ∧ rho.re < 1 / 2 ∧ |s.im - rho.im| < 1 / 2 := by
  have hneg : ∃ p : RiemannXiDivisorZeroIndex,
      levinsonMontgomeryPairedKernel s p < 0 := by
    by_contra h
    push Not at h
    exact (not_lt_of_ge (tsum_nonneg h)) hmass
  obtain ⟨p, hpNeg⟩ := hneg
  let rho := riemannXiDivisorZeroValue p
  have hrhoZero : IsNontrivialZero rho :=
    riemannXiDivisorZeroIndex_val_isNontrivialZero p
  have hrhoPos : 0 < rho.re := speiser_nontrivial_zero_re_pos hrhoZero
  have hrhoLt : rho.re < 1 := nontrivial_zero_re_lt_one hrhoZero
  have hp : s ≠ rho := by
    intro h
    apply hxi
    rw [h]
    exact riemannXi_eq_zero_of_isNontrivialZero hrhoZero
  have hq : s ≠ riemannXiDivisorZeroValue
      (levinsonMontgomeryPairedZeroEquiv p) := by
    intro h
    apply hxi
    rw [h]
    exact riemannXi_eq_zero_of_isNontrivialZero
      (riemannXiDivisorZeroIndex_val_isNontrivialZero
        (levinsonMontgomeryPairedZeroEquiv p))
  have hden : 0 <
      Complex.normSq (s - rho) *
        Complex.normSq (s - riemannXiDivisorZeroValue
          (levinsonMontgomeryPairedZeroEquiv p)) :=
    mul_pos (Complex.normSq_pos.mpr (sub_ne_zero.mpr hp))
      (Complex.normSq_pos.mpr (sub_ne_zero.mpr hq))
  have hnum :
      (s.im - rho.im) ^ 2 + (s.re - 1 / 2) ^ 2 -
          (rho.re - 1 / 2) ^ 2 < 0 := by
    by_contra h
    have hnonneg : 0 ≤
        (s.im - rho.im) ^ 2 + (s.re - 1 / 2) ^ 2 -
          (rho.re - 1 / 2) ^ 2 := le_of_not_gt h
    have hkernelNonneg := div_nonneg hnonneg hden.le
    exact (not_lt_of_ge hkernelNonneg)
      (by simpa [levinsonMontgomeryPairedKernel, rho] using hpNeg)
  have hySq : (s.im - rho.im) ^ 2 < (1 / 2 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (s.re - 1 / 2), sq_nonneg rho.re,
      sq_nonneg (1 - rho.re)]
  have hy : |s.im - rho.im| < 1 / 2 :=
    abs_lt_of_sq_lt_sq hySq (by norm_num)
  have hrhoIm : 0 < rho.im := by
    have hyBounds := abs_lt.mp hy
    linarith
  by_cases hleft : rho.re < 1 / 2
  · exact ⟨rho, hrhoZero, hrhoPos, hleft, hy⟩
  · have hlineNe : rho.re ≠ 1 / 2 := by
      intro hline
      rw [hline] at hnum
      nlinarith [sq_nonneg (s.im - rho.im), sq_nonneg (s.re - 1 / 2)]
    have hright : 1 / 2 < rho.re :=
      lt_of_le_of_ne (le_of_not_gt hleft) hlineNe.symm
    let q := riemannXiDivisorZeroValue
      (levinsonMontgomeryPairedZeroEquiv p)
    have hqZero : IsNontrivialZero q :=
      riemannXiDivisorZeroIndex_val_isNontrivialZero
        (levinsonMontgomeryPairedZeroEquiv p)
    have hqRe : q.re = 1 - rho.re := by simp [q, rho]
    have hqIm : q.im = rho.im := by simp [q, rho]
    refine ⟨q, hqZero, ?_, ?_, ?_⟩
    · rw [hqRe]
      linarith
    · rw [hqRe]
      linarith
    · rw [hqIm]
      exact hy

/-- A point to the left of the critical line at integer height. -/
def levinsonMontgomeryIntegerPoint (sigma : ℝ) (n : ℕ) : ℂ :=
  (sigma : ℂ) + (n : ℂ) * I

@[simp] theorem levinsonMontgomeryIntegerPoint_re (sigma : ℝ) (n : ℕ) :
    (levinsonMontgomeryIntegerPoint sigma n).re = sigma := by
  simp [levinsonMontgomeryIntegerPoint]

@[simp] theorem levinsonMontgomeryIntegerPoint_im (sigma : ℝ) (n : ℕ) :
    (levinsonMontgomeryIntegerPoint sigma n).im = n := by
  simp [levinsonMontgomeryIntegerPoint]

def LevinsonMontgomeryPairedMassNegativeAtIntegers : Prop :=
  ∃ n0 : ℕ, 1 ≤ n0 ∧ ∀ n : ℕ, n0 ≤ n →
    ∃ sigma : ℝ, 0 < sigma ∧ sigma < 1 / 2 ∧
      riemannXi (levinsonMontgomeryIntegerPoint sigma n) ≠ 0 ∧
      levinsonMontgomeryPairedZeroMass
        (levinsonMontgomeryIntegerPoint sigma n) < 0

theorem levinsonMontgomeryDenseBranch_of_pairedMassNegativeAtIntegers
    (hmass : LevinsonMontgomeryPairedMassNegativeAtIntegers) :
    ∃ T0 : ℝ, ∀ T : ℝ, T0 ≤ T →
      T / 2 < (speiserUpperLeftZetaZeroCount T : ℝ) := by
  classical
  rcases hmass with ⟨n0, hn0, hmass⟩
  let I0 := {n : ℕ // n0 ≤ n}
  have hwitness : ∀ n : I0, ∃ rho : ℂ, IsNontrivialZero rho ∧
      0 < rho.re ∧ rho.re < 1 / 2 ∧ |(n : ℝ) - rho.im| < 1 / 2 := by
    intro n
    obtain ⟨sigma, hsigmaPos, hsigma, hxi, hneg⟩ := hmass n n.2
    have hsIm : 1 ≤ (levinsonMontgomeryIntegerPoint sigma n).im := by
      rw [levinsonMontgomeryIntegerPoint_im]
      exact_mod_cast hn0.trans n.2
    simpa using
      exists_upperLeft_zero_abs_im_sub_lt_half_of_pairedMass_neg
        (by simpa using hsigma) hsIm hxi hneg
  choose rho hrhoZero hrhoPos hrhoLeft hrhoNear using hwitness
  let rhoNat : ℕ → ℂ := fun n =>
    if hn : n0 ≤ n then rho ⟨n, hn⟩ else 0
  have rhoNat_spec (n : ℕ) (hn : n0 ≤ n) :
      IsNontrivialZero (rhoNat n) ∧ 0 < (rhoNat n).re ∧
        (rhoNat n).re < 1 / 2 ∧ |(n : ℝ) - (rhoNat n).im| < 1 / 2 := by
    simp only [rhoNat, dif_pos hn]
    exact ⟨hrhoZero ⟨n, hn⟩, hrhoPos ⟨n, hn⟩,
      hrhoLeft ⟨n, hn⟩, hrhoNear ⟨n, hn⟩⟩
  have rhoNat_injective :
      Set.InjOn rhoNat {n : ℕ | n0 ≤ n} := by
    intro n hn m hm hEq
    simp only [Set.mem_setOf_eq] at hn hm
    have hnNear := (rhoNat_spec n hn).2.2.2
    have hmNear := (rhoNat_spec m hm).2.2.2
    have hnBounds := abs_lt.mp hnNear
    have hmBounds := abs_lt.mp hmNear
    rw [hEq] at hnBounds
    by_contra hne
    rcases lt_or_gt_of_ne hne with hnm | hmn
    · have hcast : (n : ℝ) + 1 ≤ (m : ℝ) := by
        exact_mod_cast (Nat.succ_le_iff.mpr hnm)
      linarith
    · have hcast : (m : ℝ) + 1 ≤ (n : ℝ) := by
        exact_mod_cast (Nat.succ_le_iff.mpr hmn)
      linarith
  refine ⟨2 * (n0 : ℝ) + 4, fun T hT => ?_⟩
  have hTpos : 0 < T := by
    have hn0Real : 0 ≤ (n0 : ℝ) := Nat.cast_nonneg n0
    linarith
  let N : ℕ := ⌊T⌋₊
  have hfloorLe : (N : ℝ) ≤ T := by
    exact Nat.floor_le hTpos.le
  have hfloorLower : T < (N : ℝ) + 1 := by
    simpa [N] using Nat.lt_floor_add_one T
  have hn0NReal : (n0 : ℝ) ≤ (N : ℝ) := by
    linarith
  have hn0N : n0 ≤ N := by
    exact_mod_cast hn0NReal
  let selected : Finset ℂ := (Finset.Ico n0 N).image rhoNat
  have hselectedCard : selected.card = N - n0 := by
    rw [show selected = (Finset.Ico n0 N).image rhoNat by rfl]
    rw [Finset.card_image_iff.mpr]
    · simp
    · intro n hn m hm hEq
      apply rhoNat_injective
      · exact (Finset.mem_Ico.mp hn).1
      · exact (Finset.mem_Ico.mp hm).1
      · exact hEq
  have hselectedSubset :
      selected ⊆ speiserUpperLeftZetaZeroFinset T := by
    intro z hz
    rw [show selected = (Finset.Ico n0 N).image rhoNat by rfl,
      Finset.mem_image] at hz
    obtain ⟨n, hn, rfl⟩ := hz
    have hnData := Finset.mem_Ico.mp hn
    have hspec := rhoNat_spec n hnData.1
    have hheight : (rhoNat n).im < T := by
      have hnearBounds := abs_lt.mp hspec.2.2.2
      have hnCast : (n : ℝ) + 1 ≤ (N : ℝ) := by
        exact_mod_cast (Nat.succ_le_iff.mpr hnData.2)
      linarith
    exact mem_speiserUpperLeftZetaZeroFinset.mpr
      ⟨⟨⟨by
          have hnearBounds := abs_lt.mp hspec.2.2.2
          have hnOne : (1 : ℝ) ≤ n := by
            exact_mod_cast hn0.trans hnData.1
          linarith,
        hspec.2.1, hspec.2.2.1⟩, hheight⟩, hspec.1⟩
  have hcardLeCount : selected.card ≤ speiserUpperLeftZetaZeroCount T := by
    unfold speiserUpperLeftZetaZeroCount
    calc
      selected.card = ∑ z ∈ selected, 1 := by simp
      _ ≤ ∑ z ∈ selected, burnolZetaZeroMultiplicity z := by
        apply Finset.sum_le_sum
        intro z hz
        exact burnolZetaZeroMultiplicity_pos
          ((mem_speiserUpperLeftZetaZeroFinset.mp
            (hselectedSubset hz)).2)
      _ ≤ ∑ z ∈ speiserUpperLeftZetaZeroFinset T,
          burnolZetaZeroMultiplicity z :=
        Finset.sum_le_sum_of_subset_of_nonneg hselectedSubset (by intros; omega)
  have hdomainLarge : T / 2 < ((N - n0 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hn0N]
    linarith
  rw [← hselectedCard] at hdomainLarge
  exact hdomainLarge.trans_le (by exact_mod_cast hcardLeCount)

end

end LeanLab.Riemann
