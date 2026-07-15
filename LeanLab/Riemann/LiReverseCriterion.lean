import LeanLab.Riemann.LiSymmetricZeroFormula
import Mathlib.Analysis.Complex.Circle

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The reverse Li criterion

This module formalizes the Bombieri-Lagarias large-index argument for the project-local
multiplicity-bearing xi zero divisor.
-/

open Complex Filter Function Set Topology
open scoped BigOperators ComplexConjugate Topology

namespace LeanLab.Riemann

noncomputable section

/-- Finitely many unit complex phases return simultaneously near `1` at arbitrarily large even
powers. This replaces conjugate-pair/cosine bookkeeping in the classical power-sum proof. -/
theorem exists_even_gt_forall_circle_pow_dist_one_lt
    {ι : Type*} [Finite ι] (u : ι → Circle) (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, N < n ∧ Even n ∧ ∀ i : ι, dist (u i ^ n) 1 < ε := by
  letI := Fintype.ofFinite ι
  let x : ℕ → (ι → Circle) := fun n i => u i ^ (2 * n)
  obtain ⟨a, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq x
  have hshift : Tendsto (fun k => x (φ (k + (N + 1)))) atTop (𝓝 a) := by
    simpa [Function.comp_def] using hlim.comp (tendsto_add_atTop_nat (N + 1))
  have hquot :
      Tendsto (fun k => x (φ (k + (N + 1))) * (x (φ k))⁻¹) atTop (𝓝 1) := by
    simpa using hshift.mul hlim.inv
  obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.1 hquot) ε hε
  let d : ℕ := φ (K + (N + 1)) - φ K
  let n : ℕ := 2 * d
  have hgap : N + 1 + φ K ≤ φ (K + (N + 1)) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      hφ.add_le_nat (N + 1) K
  have hd : N < d := by
    dsimp only [d]
    omega
  have hn : N < n := by
    dsimp only [n]
    omega
  have hEven : Even n := by
    exact ⟨d, by simp [n, two_mul]⟩
  refine ⟨n, hn, hEven, ?_⟩
  have hdistPi := (dist_pi_lt_iff hε).1 (hK K le_rfl)
  intro i
  have hφle : φ K ≤ φ (K + (N + 1)) := by omega
  have hpow :
      u i ^ n = x (φ (K + (N + 1))) i * (x (φ K) i)⁻¹ := by
    dsimp only [n, d, x]
    rw [show 2 * (φ (K + (N + 1)) - φ K) =
        2 * φ (K + (N + 1)) - 2 * φ K by omega]
    rw [pow_sub _ (Nat.mul_le_mul_left 2 hφle)]
  rw [hpow]
  exact hdistPi i

/-- The Mobius transform appearing in the raw Li zero term. -/
def liZeroTransform (ρ : ℂ) : ℂ :=
  1 - 1 / ρ

theorem liZeroTransform_eq_sub_div {ρ : ℂ} (hρ : ρ ≠ 0) :
    liZeroTransform ρ = (ρ - 1) / ρ := by
  calc
    liZeroTransform ρ = ρ / ρ - 1 / ρ := by rw [liZeroTransform, div_self hρ]
    _ = (ρ - 1) / ρ := (sub_div ρ 1 ρ).symm

theorem liZeroTransform_ne_zero {ρ : ℂ} (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1) :
    liZeroTransform ρ ≠ 0 := by
  rw [liZeroTransform_eq_sub_div hρ0]
  exact div_ne_zero (sub_ne_zero.mpr hρ1) hρ0

theorem norm_liZeroTransform_le_one_iff {ρ : ℂ} (hρ : ρ ≠ 0) :
    ‖liZeroTransform ρ‖ ≤ 1 ↔ 1 / 2 ≤ ρ.re := by
  rw [← not_lt, ← Complex.one_lt_normSq_iff, not_lt]
  rw [liZeroTransform_eq_sub_div hρ, Complex.normSq_div]
  have hden : 0 < Complex.normSq ρ := Complex.normSq_pos.mpr hρ
  rw [div_le_one hden]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re, Complex.sub_im,
    Complex.one_im]
  constructor <;> intro h <;> nlinarith

theorem one_lt_norm_liZeroTransform_iff {ρ : ℂ} (hρ : ρ ≠ 0) :
    1 < ‖liZeroTransform ρ‖ ↔ ρ.re < 1 / 2 := by
  rw [← not_le, norm_liZeroTransform_le_one_iff hρ, not_le]

theorem liZeroTransform_one_sub {ρ : ℂ} (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1) :
    liZeroTransform (1 - ρ) = (liZeroTransform ρ)⁻¹ := by
  rw [liZeroTransform_eq_sub_div (sub_ne_zero.mpr hρ1.symm),
    liZeroTransform_eq_sub_div hρ0]
  have hρsub : ρ - 1 ≠ 0 := sub_ne_zero.mpr hρ1
  have honeSub : 1 - ρ ≠ 0 := sub_ne_zero.mpr hρ1.symm
  field_simp [hρ0, hρsub, honeSub]
  ring

theorem isNontrivialZero_one_sub {ρ : ℂ} (hρ : IsNontrivialZero ρ) :
    IsNontrivialZero (1 - ρ) := by
  rw [isNontrivialZero_iff_riemannXi_eq_zero]
  rw [riemannXi_one_sub]
  exact (isNontrivialZero_iff_riemannXi_eq_zero ρ).mp hρ

theorem nontrivial_zero_re_pos {ρ : ℂ} (hρ : IsNontrivialZero ρ) :
    0 < ρ.re := by
  have hreflect := nontrivial_zero_re_lt_one (isNontrivialZero_one_sub hρ)
  simp only [Complex.sub_re, Complex.one_re] at hreflect
  linarith

theorem riemannXiDivisorZeroValue_ne_one (p : RiemannXiDivisorZeroIndex) :
    riemannXiDivisorZeroValue p ≠ 1 :=
  (sub_ne_zero.mp (one_sub_riemannXiDivisorZeroValue_ne_zero p)).symm

/-- The reflection-invariant size of the two reciprocal Li transforms in one xi-zero orbit. -/
def riemannXiLiOrbitRadius (p : RiemannXiDivisorZeroIndex) : ℝ :=
  max ‖liZeroTransform (riemannXiDivisorZeroValue p)‖
    ‖(liZeroTransform (riemannXiDivisorZeroValue p))⁻¹‖

theorem riemannXiLiOrbitRadius_reflect (p : RiemannXiDivisorZeroIndex) :
    riemannXiLiOrbitRadius (riemannXiDivisorZeroReflectEquiv p) =
      riemannXiLiOrbitRadius p := by
  have hp0 : riemannXiDivisorZeroValue p ≠ 0 :=
    Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p
  have hp1 := riemannXiDivisorZeroValue_ne_one p
  have hq0 := liZeroTransform_ne_zero hp0 hp1
  simp only [riemannXiLiOrbitRadius, riemannXiDivisorZeroReflectEquiv_apply,
    riemannXiDivisorZeroValue_reflect, liZeroTransform_one_sub hp0 hp1, inv_inv]
  rw [max_comm]

theorem one_le_riemannXiLiOrbitRadius (p : RiemannXiDivisorZeroIndex) :
    1 ≤ riemannXiLiOrbitRadius p := by
  have hp0 : riemannXiDivisorZeroValue p ≠ 0 :=
    Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p
  have hp1 := riemannXiDivisorZeroValue_ne_one p
  have hq0 := liZeroTransform_ne_zero hp0 hp1
  by_cases hq : 1 ≤ ‖liZeroTransform (riemannXiDivisorZeroValue p)‖
  · exact hq.trans (le_max_left _ _)
  · have hqpos : 0 < ‖liZeroTransform (riemannXiDivisorZeroValue p)‖ :=
      norm_pos_iff.mpr hq0
    have hinv : 1 < ‖(liZeroTransform (riemannXiDivisorZeroValue p))⁻¹‖ := by
      rw [norm_inv]
      exact (one_lt_inv₀ hqpos).2 (lt_of_not_ge hq)
    exact hinv.le.trans (le_max_right _ _)

theorem one_lt_riemannXiLiOrbitRadius_of_re_ne_half
    (p : RiemannXiDivisorZeroIndex)
    (hp : (riemannXiDivisorZeroValue p).re ≠ 1 / 2) :
    1 < riemannXiLiOrbitRadius p := by
  have hp0 : riemannXiDivisorZeroValue p ≠ 0 :=
    Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p
  have hp1 := riemannXiDivisorZeroValue_ne_one p
  rcases lt_or_gt_of_ne hp with hpLeft | hpRight
  · exact (one_lt_norm_liZeroTransform_iff hp0).2 hpLeft |>.trans_le
      (le_max_left _ _)
  · have hreflect : (1 - riemannXiDivisorZeroValue p).re < 1 / 2 := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have hreflect0 : 1 - riemannXiDivisorZeroValue p ≠ 0 :=
      sub_ne_zero.mpr hp1.symm
    have hlarge := (one_lt_norm_liZeroTransform_iff hreflect0).2 hreflect
    rw [liZeroTransform_one_sub hp0 hp1] at hlarge
    exact hlarge.trans_le (le_max_right _ _)

theorem norm_liZeroTransform_lt_of_one_div_sub_one_lt_norm
    {ρ : ℂ} {c : ℝ} (hc : 1 < c) (hρ : 1 / (c - 1) < ‖ρ‖) :
    ‖liZeroTransform ρ‖ < c := by
  have hρpos : 0 < ‖ρ‖ := lt_trans (by positivity : 0 < 1 / (c - 1)) hρ
  have hcpos : 0 < c - 1 := sub_pos.mpr hc
  have hinv : 1 / ‖ρ‖ < c - 1 := by
    rw [div_lt_iff₀ hρpos]
    have hmul := (div_lt_iff₀ hcpos).1 hρ
    nlinarith
  calc
    ‖liZeroTransform ρ‖ = ‖1 - 1 / ρ‖ := rfl
    _ ≤ ‖(1 : ℂ)‖ + ‖1 / ρ‖ := norm_sub_le _ _
    _ = 1 + 1 / ‖ρ‖ := by simp
    _ < c := by linarith

theorem eventually_riemannXiLiOrbitRadius_lt {c : ℝ} (hc : 1 < c) :
    ∀ᶠ p : RiemannXiDivisorZeroIndex in Filter.cofinite,
      riemannXiLiOrbitRadius p < c := by
  let B : ℝ := 1 / (c - 1)
  have hlarge : ∀ᶠ p : RiemannXiDivisorZeroIndex in Filter.cofinite,
      B < ‖riemannXiDivisorZeroValue p‖ := by
    have hfin :
        ({p : RiemannXiDivisorZeroIndex |
          ‖riemannXiDivisorZeroValue p‖ ≤ B} : Set _).Finite := by
      exact Complex.Hadamard.divisorZeroIndex₀_norm_le_finite
        (f := riemannXi) (U := (Set.univ : Set ℂ)) B (by simp)
    filter_upwards [hfin.eventually_cofinite_notMem] with p hp
    exact lt_of_not_ge (by simpa using hp)
  have hlargeReflect : ∀ᶠ p : RiemannXiDivisorZeroIndex in Filter.cofinite,
      B < ‖1 - riemannXiDivisorZeroValue p‖ := by
    have hreflect :=
      riemannXiDivisorZeroReflectEquiv.injective.tendsto_cofinite.eventually hlarge
    simpa only [riemannXiDivisorZeroReflectEquiv_apply,
      riemannXiDivisorZeroValue_reflect] using hreflect
  filter_upwards [hlarge, hlargeReflect] with p hp hpReflect
  have hp0 : riemannXiDivisorZeroValue p ≠ 0 :=
    Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p
  have hp1 := riemannXiDivisorZeroValue_ne_one p
  have hleft : ‖liZeroTransform (riemannXiDivisorZeroValue p)‖ < c :=
    norm_liZeroTransform_lt_of_one_div_sub_one_lt_norm hc hp
  have hright : ‖(liZeroTransform (riemannXiDivisorZeroValue p))⁻¹‖ < c := by
    rw [← liZeroTransform_one_sub hp0 hp1]
    exact norm_liZeroTransform_lt_of_one_div_sub_one_lt_norm hc hpReflect
  exact max_lt hleft hright

theorem finite_riemannXiLiOrbitRadius_superlevel {c : ℝ} (hc : 1 < c) :
    ({p : RiemannXiDivisorZeroIndex | c ≤ riemannXiLiOrbitRadius p} : Set _).Finite := by
  simpa only [not_lt] using
    (Filter.eventually_cofinite.mp (eventually_riemannXiLiOrbitRadius_lt hc))

theorem norm_one_sub_pow_le
    (z : ℂ) (m : ℕ) (_hm : 0 < m) (r : ℝ) (hr : 1 ≤ r) (hz : ‖z‖ ≤ r) :
    ‖1 - z ^ m‖ ≤ (m : ℝ) * r ^ (m - 1) * ‖1 - z‖ := by
  rw [← geom_sum_mul_neg]
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖∑ i ∈ Finset.range m, z ^ i‖ ≤
        ∑ i ∈ Finset.range m, ‖z ^ i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range m, r ^ (m - 1) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_pow]
      exact (pow_le_pow_left₀ (norm_nonneg z) hz i).trans
        (pow_le_pow_right₀ hr (Nat.le_sub_one_of_lt (Finset.mem_range.mp hi)))
    _ = (m : ℝ) * r ^ (m - 1) := by simp

theorem norm_liRawZeroTerm_le
    (m : ℕ) (hm : 0 < m) (ρ : ℂ) (r : ℝ) (hr : 1 ≤ r)
    (hρ : ‖liZeroTransform ρ‖ ≤ r) :
    ‖liRawZeroTerm m ρ‖ ≤
      (m : ℝ) * r ^ (m - 1) * ‖1 / ρ‖ := by
  have h := norm_one_sub_pow_le (liZeroTransform ρ) m hm r hr hρ
  simpa [liRawZeroTerm, liZeroTransform] using h

/-- A summable quadratic weight for both values in a reflection orbit. -/
def riemannXiLiReciprocalSqWeight (p : RiemannXiDivisorZeroIndex) : ℝ :=
  ‖riemannXiDivisorZeroValue p‖⁻¹ ^ (2 : ℕ) +
    ‖1 - riemannXiDivisorZeroValue p‖⁻¹ ^ (2 : ℕ)

theorem summable_riemannXiLiReciprocalSqWeight :
    Summable riemannXiLiReciprocalSqWeight := by
  have hleft := summable_riemannXiDivisorZeroIndex_norm_inv_sq
  have hreflect : Summable (fun p : RiemannXiDivisorZeroIndex =>
      ‖riemannXiDivisorZeroValue (riemannXiDivisorZeroReflectEquiv p)‖⁻¹ ^
        (2 : ℕ)) :=
    hleft.comp_injective riemannXiDivisorZeroReflectEquiv.injective
  change Summable (fun p : RiemannXiDivisorZeroIndex =>
    ‖riemannXiDivisorZeroValue p‖⁻¹ ^ (2 : ℕ) +
      ‖1 - riemannXiDivisorZeroValue p‖⁻¹ ^ (2 : ℕ))
  exact hleft.add (by
    simpa only [riemannXiDivisorZeroReflectEquiv_apply,
      riemannXiDivisorZeroValue_reflect] using hreflect)

theorem riemannXiLiReciprocalSqWeight_nonneg (p : RiemannXiDivisorZeroIndex) :
    0 ≤ riemannXiLiReciprocalSqWeight p := by
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem norm_riemannXiSymmetrizedLiZeroTerm_le
    (n : ℕ) (p : RiemannXiDivisorZeroIndex) :
    ‖riemannXiSymmetrizedLiZeroTerm n p‖ ≤
      ((n + 1 : ℕ) : ℝ) ^ (2 : ℕ) * riemannXiLiOrbitRadius p ^ (n + 1) *
        riemannXiLiReciprocalSqWeight p := by
  let m : ℕ := n + 1
  let ρ : ℂ := riemannXiDivisorZeroValue p
  let q : ℂ := liZeroTransform ρ
  let r : ℝ := riemannXiLiOrbitRadius p
  have hm : 0 < m := by simp [m]
  have hρ0 : ρ ≠ 0 := Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p
  have hρ1 : ρ ≠ 1 := riemannXiDivisorZeroValue_ne_one p
  have hq0 : q ≠ 0 := liZeroTransform_ne_zero hρ0 hρ1
  have hr : 1 ≤ r := one_le_riemannXiLiOrbitRadius p
  have hqLeft : ‖q‖ ≤ r := le_max_left _ _
  have hqRight : ‖q⁻¹‖ ≤ r := le_max_right _ _
  have hreflect : liZeroTransform (1 - ρ) = q⁻¹ :=
    liZeroTransform_one_sub hρ0 hρ1
  have hproduct :
      liRawZeroTerm m ρ + liRawZeroTerm m (1 - ρ) =
        liRawZeroTerm m ρ * liRawZeroTerm m (1 - ρ) :=
    liRawZeroTerm_add_reflect_eq_mul m hρ0 hρ1
  have hweight :
      ‖1 / ρ‖ ^ (2 : ℕ) + ‖1 / (1 - ρ)‖ ^ (2 : ℕ) =
        riemannXiLiReciprocalSqWeight p := by
    simp [riemannXiLiReciprocalSqWeight, ρ, one_div]
  have hab (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
      a * b ≤ a ^ (2 : ℕ) + b ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (a - b)]
  by_cases hq : ‖q‖ ≤ 1
  · have hA := norm_liRawZeroTerm_le m hm ρ 1 le_rfl hq
    have hB := norm_liRawZeroTerm_le m hm (1 - ρ) r hr (by
      rw [hreflect]
      exact hqRight)
    have hpow : r ^ (m - 1) ≤ r ^ m :=
      pow_le_pow_right₀ hr (Nat.sub_le m 1)
    have hAB := mul_le_mul hA hB (norm_nonneg _) (by positivity)
    have hab' := hab ‖1 / ρ‖ ‖1 / (1 - ρ)‖ (norm_nonneg _) (norm_nonneg _)
    calc
      ‖riemannXiSymmetrizedLiZeroTerm n p‖ =
          (‖liRawZeroTerm m ρ‖ * ‖liRawZeroTerm m (1 - ρ)‖) / 2 := by
        rw [riemannXiSymmetrizedLiZeroTerm, show n + 1 = m by rfl, hproduct,
          norm_div, norm_mul, norm_ofNat]
      _ ≤ ‖liRawZeroTerm m ρ‖ * ‖liRawZeroTerm m (1 - ρ)‖ := by
        exact div_le_self (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
      _ ≤ ((m : ℝ) * 1 ^ (m - 1) * ‖1 / ρ‖) *
          ((m : ℝ) * r ^ (m - 1) * ‖1 / (1 - ρ)‖) := hAB
      _ = (m : ℝ) ^ (2 : ℕ) * r ^ (m - 1) *
          (‖1 / ρ‖ * ‖1 / (1 - ρ)‖) := by ring
      _ ≤ (m : ℝ) ^ (2 : ℕ) * r ^ m *
          (‖1 / ρ‖ * ‖1 / (1 - ρ)‖) := by
        gcongr
      _ ≤ (m : ℝ) ^ (2 : ℕ) * r ^ m *
          (‖1 / ρ‖ ^ (2 : ℕ) + ‖1 / (1 - ρ)‖ ^ (2 : ℕ)) := by
        gcongr
      _ = ((n + 1 : ℕ) : ℝ) ^ (2 : ℕ) *
          riemannXiLiOrbitRadius p ^ (n + 1) *
            riemannXiLiReciprocalSqWeight p := by
        rw [hweight]
  · have hqOne : ‖q⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      exact (inv_le_one₀ (norm_pos_iff.mpr hq0)).2 (le_of_not_ge hq)
    have hA := norm_liRawZeroTerm_le m hm ρ r hr hqLeft
    have hB := norm_liRawZeroTerm_le m hm (1 - ρ) 1 le_rfl (by
      rw [hreflect]
      exact hqOne)
    have hpow : r ^ (m - 1) ≤ r ^ m :=
      pow_le_pow_right₀ hr (Nat.sub_le m 1)
    have hAB := mul_le_mul hA hB (norm_nonneg _) (by positivity)
    have hab' := hab ‖1 / ρ‖ ‖1 / (1 - ρ)‖ (norm_nonneg _) (norm_nonneg _)
    calc
      ‖riemannXiSymmetrizedLiZeroTerm n p‖ =
          (‖liRawZeroTerm m ρ‖ * ‖liRawZeroTerm m (1 - ρ)‖) / 2 := by
        rw [riemannXiSymmetrizedLiZeroTerm, show n + 1 = m by rfl, hproduct,
          norm_div, norm_mul, norm_ofNat]
      _ ≤ ‖liRawZeroTerm m ρ‖ * ‖liRawZeroTerm m (1 - ρ)‖ := by
        exact div_le_self (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
      _ ≤ ((m : ℝ) * r ^ (m - 1) * ‖1 / ρ‖) *
          ((m : ℝ) * 1 ^ (m - 1) * ‖1 / (1 - ρ)‖) := hAB
      _ = (m : ℝ) ^ (2 : ℕ) * r ^ (m - 1) *
          (‖1 / ρ‖ * ‖1 / (1 - ρ)‖) := by ring
      _ ≤ (m : ℝ) ^ (2 : ℕ) * r ^ m *
          (‖1 / ρ‖ * ‖1 / (1 - ρ)‖) := by
        gcongr
      _ ≤ (m : ℝ) ^ (2 : ℕ) * r ^ m *
          (‖1 / ρ‖ ^ (2 : ℕ) + ‖1 / (1 - ρ)‖ ^ (2 : ℕ)) := by
        gcongr
      _ = ((n + 1 : ℕ) : ℝ) ^ (2 : ℕ) *
          riemannXiLiOrbitRadius p ^ (n + 1) *
            riemannXiLiReciprocalSqWeight p := by
        rw [hweight]

/-- Outside a chosen finite main set, the whole paired Li series is controlled by the largest
remaining orbit radius and one fixed summable quadratic zero weight. -/
theorem norm_tsum_indicator_compl_riemannXiSymmetrizedLiZeroTerm_le
    (n : ℕ) (s : Set RiemannXiDivisorZeroIndex) (c : ℝ) (hc : 0 ≤ c)
    (hs : ∀ p, p ∉ s → riemannXiLiOrbitRadius p ≤ c) :
    ‖∑' p, sᶜ.indicator (riemannXiSymmetrizedLiZeroTerm n) p‖ ≤
      ((n + 1 : ℕ) : ℝ) ^ (2 : ℕ) * c ^ (n + 1) *
        ∑' p, riemannXiLiReciprocalSqWeight p := by
  let A : ℝ := ((n + 1 : ℕ) : ℝ) ^ (2 : ℕ) * c ^ (n + 1)
  have hterm : Summable (sᶜ.indicator (riemannXiSymmetrizedLiZeroTerm n)) :=
    (summable_riemannXiSymmetrizedLiZeroTerm n).indicator _
  have hmajor : Summable (fun p : RiemannXiDivisorZeroIndex =>
      A * riemannXiLiReciprocalSqWeight p) :=
    summable_riemannXiLiReciprocalSqWeight.mul_left A
  have hpoint (p : RiemannXiDivisorZeroIndex) :
      ‖sᶜ.indicator (riemannXiSymmetrizedLiZeroTerm n) p‖ ≤
        A * riemannXiLiReciprocalSqWeight p := by
    by_cases hp : p ∈ s
    · rw [Set.indicator_of_notMem (by simpa using hp)]
      simpa [A] using mul_nonneg
          (mul_nonneg (sq_nonneg (((n + 1 : ℕ) : ℝ))) (pow_nonneg hc (n + 1)))
          (riemannXiLiReciprocalSqWeight_nonneg p)
    · rw [Set.indicator_of_mem (by simpa using hp)]
      calc
        ‖riemannXiSymmetrizedLiZeroTerm n p‖ ≤
            ((n + 1 : ℕ) : ℝ) ^ (2 : ℕ) *
              riemannXiLiOrbitRadius p ^ (n + 1) *
                riemannXiLiReciprocalSqWeight p :=
          norm_riemannXiSymmetrizedLiZeroTerm_le n p
        _ ≤ ((n + 1 : ℕ) : ℝ) ^ (2 : ℕ) * c ^ (n + 1) *
              riemannXiLiReciprocalSqWeight p := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀
                (zero_le_one.trans (one_le_riemannXiLiOrbitRadius p)) (hs p hp) _)
              (sq_nonneg (((n + 1 : ℕ) : ℝ))))
            (riemannXiLiReciprocalSqWeight_nonneg p)
        _ = A * riemannXiLiReciprocalSqWeight p := rfl
  calc
    ‖∑' p, sᶜ.indicator (riemannXiSymmetrizedLiZeroTerm n) p‖ ≤
        ∑' p, ‖sᶜ.indicator (riemannXiSymmetrizedLiZeroTerm n) p‖ :=
      norm_tsum_le_tsum_norm hterm.norm
    _ ≤ ∑' p, A * riemannXiLiReciprocalSqWeight p :=
      hterm.norm.tsum_le_tsum hpoint hmajor
    _ = A * ∑' p, riemannXiLiReciprocalSqWeight p := tsum_mul_left
    _ = ((n + 1 : ℕ) : ℝ) ^ (2 : ℕ) * c ^ (n + 1) *
          ∑' p, riemannXiLiReciprocalSqWeight p := rfl

/-- Choose the member of a reciprocal Li-transform pair whose norm is at least one. -/
def riemannXiLiDominantTransform (p : RiemannXiDivisorZeroIndex) : ℂ :=
  let q := liZeroTransform (riemannXiDivisorZeroValue p)
  if ‖q‖ ≤ 1 then q⁻¹ else q

theorem riemannXiLiDominantTransform_ne_zero (p : RiemannXiDivisorZeroIndex) :
    riemannXiLiDominantTransform p ≠ 0 := by
  have hp0 : riemannXiDivisorZeroValue p ≠ 0 :=
    Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p
  have hp1 := riemannXiDivisorZeroValue_ne_one p
  have hq0 := liZeroTransform_ne_zero hp0 hp1
  simp only [riemannXiLiDominantTransform]
  split <;> simp [hq0]

theorem norm_riemannXiLiDominantTransform (p : RiemannXiDivisorZeroIndex) :
    ‖riemannXiLiDominantTransform p‖ = riemannXiLiOrbitRadius p := by
  let q := liZeroTransform (riemannXiDivisorZeroValue p)
  have hp0 : riemannXiDivisorZeroValue p ≠ 0 :=
    Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p
  have hp1 := riemannXiDivisorZeroValue_ne_one p
  have hq0 : q ≠ 0 := liZeroTransform_ne_zero hp0 hp1
  have hqpos : 0 < ‖q‖ := norm_pos_iff.mpr hq0
  by_cases hq : ‖q‖ ≤ 1
  · have honeInv : 1 ≤ ‖q⁻¹‖ := by
      rw [norm_inv]
      exact (one_le_inv₀ hqpos).2 hq
    have hle : ‖q‖ ≤ ‖q⁻¹‖ := hq.trans honeInv
    have hq' : ‖liZeroTransform (riemannXiDivisorZeroValue p)‖ ≤ 1 := by
      simpa only [q] using hq
    rw [riemannXiLiDominantTransform, if_pos hq', riemannXiLiOrbitRadius,
      max_eq_right (by simpa only [q] using hle)]
  · have hone : 1 < ‖q‖ := lt_of_not_ge hq
    have hinv : ‖q⁻¹‖ < 1 := by
      rw [norm_inv]
      exact (inv_lt_one₀ hqpos).2 hone
    have hle : ‖q⁻¹‖ ≤ ‖q‖ := hinv.le.trans hone.le
    have hq' : ¬‖liZeroTransform (riemannXiDivisorZeroValue p)‖ ≤ 1 := by
      simpa only [q] using hq
    rw [riemannXiLiDominantTransform, if_neg hq', riemannXiLiOrbitRadius,
      max_eq_left (by simpa only [q] using hle)]

/-- The paired zero term is the symmetric power expression in the dominant transform. -/
theorem riemannXiSymmetrizedLiZeroTerm_eq_dominant
    (n : ℕ) (p : RiemannXiDivisorZeroIndex) :
    riemannXiSymmetrizedLiZeroTerm n p =
      1 - (riemannXiLiDominantTransform p ^ (n + 1) +
        (riemannXiLiDominantTransform p)⁻¹ ^ (n + 1)) / 2 := by
  let ρ := riemannXiDivisorZeroValue p
  let q := liZeroTransform ρ
  have hρ0 : ρ ≠ 0 := Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p
  have hρ1 : ρ ≠ 1 := riemannXiDivisorZeroValue_ne_one p
  have hq0 : q ≠ 0 := liZeroTransform_ne_zero hρ0 hρ1
  have hreflect : liZeroTransform (1 - ρ) = q⁻¹ :=
    liZeroTransform_one_sub hρ0 hρ1
  change ((1 - q ^ (n + 1)) +
      (1 - liZeroTransform (1 - ρ) ^ (n + 1))) / 2 = _
  rw [hreflect]
  change ((1 - q ^ (n + 1)) + (1 - q⁻¹ ^ (n + 1))) / 2 =
    1 - ((if ‖q‖ ≤ 1 then q⁻¹ else q) ^ (n + 1) +
      (if ‖q‖ ≤ 1 then q⁻¹ else q)⁻¹ ^ (n + 1)) / 2
  by_cases hq : ‖q‖ ≤ 1
  · simp only [if_pos hq, inv_inv]
    ring
  · simp only [if_neg hq]
    ring

/-- The unit phase of the dominant reciprocal pair. -/
def riemannXiLiDominantPhase (p : RiemannXiDivisorZeroIndex) : Circle :=
  ⟨riemannXiLiDominantTransform p / (riemannXiLiOrbitRadius p : ℂ), by
    have hr : 0 < riemannXiLiOrbitRadius p :=
      zero_lt_one.trans_le (one_le_riemannXiLiOrbitRadius p)
    have hnorm : ‖riemannXiLiDominantTransform p /
        (riemannXiLiOrbitRadius p : ℂ)‖ = 1 := by
      rw [norm_div, norm_riemannXiLiDominantTransform]
      simp [abs_of_pos hr, hr.ne']
    simpa [Submonoid.unitSphere] using mem_sphere_zero_iff_norm.mpr hnorm⟩

@[simp]
theorem coe_riemannXiLiDominantPhase (p : RiemannXiDivisorZeroIndex) :
    (riemannXiLiDominantPhase p : ℂ) =
      riemannXiLiDominantTransform p / (riemannXiLiOrbitRadius p : ℂ) :=
  rfl

theorem three_quarters_mul_orbitRadius_pow_lt_dominant_pow_re
    (p : RiemannXiDivisorZeroIndex) (m : ℕ)
    (hphase : dist (riemannXiLiDominantPhase p ^ m) 1 < 1 / 4) :
    3 / 4 * riemannXiLiOrbitRadius p ^ m <
      (riemannXiLiDominantTransform p ^ m).re := by
  let d := riemannXiLiDominantTransform p
  let r := riemannXiLiOrbitRadius p
  let u := riemannXiLiDominantPhase p
  have hr : 0 < r := zero_lt_one.trans_le (one_le_riemannXiLiOrbitRadius p)
  have hdist : ‖((u ^ m : Circle) : ℂ) - 1‖ < 1 / 4 := by
    have hphaseU : dist (u ^ m) 1 < 1 / 4 := by
      simpa only [u] using hphase
    change dist (((u ^ m : Circle) : ℂ)) ((1 : Circle) : ℂ) < 1 / 4 at hphaseU
    simpa only [Circle.coe_one, Complex.dist_eq] using hphaseU
  have hrePhase : 3 / 4 < (((u ^ m : Circle) : ℂ)).re := by
    have habs := Complex.abs_re_le_norm ((((u ^ m : Circle) : ℂ)) - 1)
    have hlt := habs.trans_lt hdist
    simp only [Complex.sub_re, Complex.one_re] at hlt
    linarith [(abs_lt.mp hlt).1]
  have hrecover0 : riemannXiLiDominantTransform p =
      (riemannXiLiOrbitRadius p : ℂ) * (riemannXiLiDominantPhase p : ℂ) := by
    rw [coe_riemannXiLiDominantPhase]
    have hrC : (riemannXiLiOrbitRadius p : ℂ) ≠ 0 := by
      exact_mod_cast (zero_lt_one.trans_le (one_le_riemannXiLiOrbitRadius p)).ne'
    field_simp [hrC]
  have hmul := mul_lt_mul_of_pos_left hrePhase (pow_pos hr m)
  have hpowRe : (riemannXiLiDominantTransform p ^ m).re =
      riemannXiLiOrbitRadius p ^ m *
        (((riemannXiLiDominantPhase p ^ m : Circle) : ℂ)).re := by
    rw [hrecover0, mul_pow, ← Complex.ofReal_pow, ← Circle.coe_pow,
      Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [hpowRe]
  simpa only [r, u, mul_comm] using hmul

theorem riemannXiSymmetrizedLiZeroTerm_re_le_of_phase_close
    (n : ℕ) (p : RiemannXiDivisorZeroIndex)
    (hphase : dist (riemannXiLiDominantPhase p ^ (n + 1)) 1 < 1 / 4) :
    (riemannXiSymmetrizedLiZeroTerm n p).re ≤
      3 / 2 - 3 / 8 * riemannXiLiOrbitRadius p ^ (n + 1) := by
  let d := riemannXiLiDominantTransform p
  let r := riemannXiLiOrbitRadius p
  let m := n + 1
  have hr : 1 ≤ r := one_le_riemannXiLiOrbitRadius p
  have hrpos : 0 < r := zero_lt_one.trans_le hr
  have hdre : 3 / 4 * r ^ m < (d ^ m).re :=
    three_quarters_mul_orbitRadius_pow_lt_dominant_pow_re p m hphase
  have hnormInv : ‖d⁻¹ ^ m‖ ≤ 1 := by
    rw [norm_pow, norm_inv, norm_riemannXiLiDominantTransform]
    exact pow_le_one₀ (inv_nonneg.mpr hrpos.le) ((inv_le_one₀ hrpos).2 hr)
  have hinvRe : -1 ≤ (d⁻¹ ^ m).re := by
    have habs := Complex.abs_re_le_norm (d⁻¹ ^ m)
    have hneg := neg_abs_le (d⁻¹ ^ m).re
    linarith
  have hRe :
      (riemannXiSymmetrizedLiZeroTerm n p).re =
        1 - ((d ^ m).re + (d⁻¹ ^ m).re) / 2 := by
    rw [riemannXiSymmetrizedLiZeroTerm_eq_dominant]
    norm_num [d, m]
  rw [hRe]
  linarith

theorem sum_toFinset_add_tsum_indicator_compl_eq_tsum
    {f : RiemannXiDivisorZeroIndex → ℂ} (hf : Summable f)
    {s : Set RiemannXiDivisorZeroIndex} (hs : s.Finite) :
    (∑ p ∈ hs.toFinset, f p) + ∑' p, sᶜ.indicator f p = ∑' p, f p := by
  rw [sum_eq_tsum_indicator]
  simp only [hs.coe_toFinset]
  rw [← (hf.indicator s).tsum_add (hf.indicator sᶜ)]
  apply tsum_congr
  intro p
  by_cases hp : p ∈ s <;> simp [hp]

/-- A fixed quadratic factor times a smaller exponential is eventually dominated by the larger
exponential, with the explicit margin used in the Li contradiction. -/
theorem eventually_sq_mul_pow_mul_lt_three_sixteenths_mul_pow
    (c R W : ℝ) (hc : 0 < c) (hcR : c < R) :
    ∀ᶠ m : ℕ in atTop,
      (m : ℝ) ^ (2 : ℕ) * c ^ m * W < 3 / 16 * R ^ m := by
  have hR : 0 < R := hc.trans hcR
  have hratio : 1 < R / c := (one_lt_div hc).2 hcR
  have htendsto : Tendsto
      (fun m : ℕ => W * ((m : ℝ) ^ (2 : ℕ) / (R / c) ^ m))
      atTop (𝓝 0) :=
    by simpa using
      (tendsto_pow_const_div_const_pow_of_one_lt 2 hratio).const_mul W
  filter_upwards [htendsto.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 3 / 16))]
    with m hm
  have hidentity :
      ((m : ℝ) ^ (2 : ℕ) * c ^ m * W) / R ^ m =
        W * ((m : ℝ) ^ (2 : ℕ) / (R / c) ^ m) := by
    rw [div_pow]
    field_simp [hc.ne', hR.ne']
  apply (div_lt_iff₀ (pow_pos hR m)).1
  rw [hidentity]
  exact hm

/-- One xi divisor zero off the critical line forces a negative real Li coefficient. This is the
Bombieri--Lagarias contradiction specialized to the project's multiplicity-bearing zero divisor. -/
theorem exists_liCoefficientCandidate_re_neg_of_divisorZero_re_ne_half
    (p₀ : RiemannXiDivisorZeroIndex)
    (hp₀ : (riemannXiDivisorZeroValue p₀).re ≠ 1 / 2) :
    ∃ n : ℕ, (liCoefficientCandidate n).re < 0 := by
  classical
  let R : ℝ := riemannXiLiOrbitRadius p₀
  let c : ℝ := (1 + R) / 2
  let W : ℝ := ∑' p, riemannXiLiReciprocalSqWeight p
  have hR : 1 < R := one_lt_riemannXiLiOrbitRadius_of_re_ne_half p₀ hp₀
  have hRpos : 0 < R := zero_lt_one.trans hR
  have hcOne : 1 < c := by
    dsimp only [c]
    linarith
  have hcpos : 0 < c := zero_lt_one.trans hcOne
  have hcR : c < R := by
    dsimp only [c]
    linarith
  let s : Set RiemannXiDivisorZeroIndex :=
    {p | c ≤ riemannXiLiOrbitRadius p}
  have hsFinite : s.Finite := by
    simpa only [s] using finite_riemannXiLiOrbitRadius_superlevel hcOne
  letI : Fintype s := hsFinite.fintype
  have hp₀s : p₀ ∈ s := by
    change c ≤ R
    exact hcR.le
  have hRpow : ∀ᶠ m : ℕ in atTop, 8 ≤ R ^ m :=
    (tendsto_pow_atTop_atTop_of_one_lt hR).eventually_ge_atTop 8
  have hcpow : ∀ᶠ m : ℕ in atTop, 4 ≤ c ^ m :=
    (tendsto_pow_atTop_atTop_of_one_lt hcOne).eventually_ge_atTop 4
  have htail : ∀ᶠ m : ℕ in atTop,
      (m : ℝ) ^ (2 : ℕ) * c ^ m * W < 3 / 16 * R ^ m :=
    eventually_sq_mul_pow_mul_lt_three_sixteenths_mul_pow c R W hcpos hcR
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hRpow.and (hcpow.and htail))
  let u : s → Circle := fun p => riemannXiLiDominantPhase p.1
  obtain ⟨m, hmN, _hmEven, hphase⟩ :=
    exists_even_gt_forall_circle_pow_dist_one_lt u N
      (by norm_num : (0 : ℝ) < 1 / 4)
  have hmLarge := hN m hmN.le
  have hmpos : 0 < m := lt_of_le_of_lt (Nat.zero_le N) hmN
  let n : ℕ := m - 1
  have hn : n + 1 = m := by
    exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hmpos))
  have hphaseAt (p : RiemannXiDivisorZeroIndex) (hp : p ∈ s) :
      dist (riemannXiLiDominantPhase p ^ (n + 1)) 1 < 1 / 4 := by
    rw [hn]
    exact hphase ⟨p, hp⟩
  have htermNonpos (p : RiemannXiDivisorZeroIndex) (hp : p ∈ s) :
      (riemannXiSymmetrizedLiZeroTerm n p).re ≤ 0 := by
    have hbound := riemannXiSymmetrizedLiZeroTerm_re_le_of_phase_close
      n p (hphaseAt p hp)
    rw [hn] at hbound
    have hcp : c ≤ riemannXiLiOrbitRadius p := hp
    have hpow : c ^ m ≤ riemannXiLiOrbitRadius p ^ m :=
      pow_le_pow_left₀ hcpos.le hcp m
    nlinarith [hmLarge.2.1]
  have hp₀term :
      (riemannXiSymmetrizedLiZeroTerm n p₀).re ≤ -(3 / 16 * R ^ m) := by
    have hbound := riemannXiSymmetrizedLiZeroTerm_re_le_of_phase_close
      n p₀ (hphaseAt p₀ hp₀s)
    rw [hn] at hbound
    nlinarith [hmLarge.1]
  let S : Finset RiemannXiDivisorZeroIndex := hsFinite.toFinset
  have hp₀S : p₀ ∈ S := by
    simpa only [S, hsFinite.mem_toFinset] using hp₀s
  have herase :
      ∑ p ∈ S.erase p₀, (riemannXiSymmetrizedLiZeroTerm n p).re ≤ 0 := by
    apply Finset.sum_nonpos
    intro p hp
    apply htermNonpos p
    have hpS : p ∈ S := (Finset.mem_erase.mp hp).2
    simpa only [S, hsFinite.mem_toFinset] using hpS
  have hfiniteReal :
      ∑ p ∈ S, (riemannXiSymmetrizedLiZeroTerm n p).re ≤
        -(3 / 16 * R ^ m) := by
    rw [← Finset.sum_erase_add S
      (fun p => (riemannXiSymmetrizedLiZeroTerm n p).re) hp₀S]
    exact add_le_of_nonpos_of_le herase hp₀term
  have hfinite :
      (∑ p ∈ S, riemannXiSymmetrizedLiZeroTerm n p).re ≤
        -(3 / 16 * R ^ m) := by
    simpa only [Complex.re_sum] using hfiniteReal
  let tail : ℂ :=
    ∑' p, sᶜ.indicator (riemannXiSymmetrizedLiZeroTerm n) p
  have houtside : ∀ p, p ∉ s → riemannXiLiOrbitRadius p ≤ c := by
    intro p hp
    exact (lt_of_not_ge hp).le
  have htailNormLe : ‖tail‖ ≤ (m : ℝ) ^ (2 : ℕ) * c ^ m * W := by
    have h := norm_tsum_indicator_compl_riemannXiSymmetrizedLiZeroTerm_le
      n s c hcpos.le houtside
    rw [hn] at h
    exact h
  have htailNorm : ‖tail‖ < 3 / 16 * R ^ m :=
    htailNormLe.trans_lt hmLarge.2.2
  have hdecomp :
      (∑ p ∈ S, riemannXiSymmetrizedLiZeroTerm n p) + tail =
        ∑' p, riemannXiSymmetrizedLiZeroTerm n p := by
    simpa only [S, tail] using
      sum_toFinset_add_tsum_indicator_compl_eq_tsum
        (summable_riemannXiSymmetrizedLiZeroTerm n) hsFinite
  have htotal :
      (∑' p, riemannXiSymmetrizedLiZeroTerm n p).re < 0 := by
    rw [← hdecomp, Complex.add_re]
    have htailRe := Complex.re_le_norm tail
    nlinarith
  refine ⟨n, ?_⟩
  rw [liCoefficientCandidate_eq_tsum_riemannXiSymmetrizedLiZeroTerm]
  exact htotal

/-- Reverse Li criterion for the derivative-defined project coefficients. -/
theorem riemannHypothesis_of_forall_liCoefficientCandidate_re_nonneg
    (hLi : ∀ n : ℕ, 0 ≤ (liCoefficientCandidate n).re) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_nontrivial_zeros_on_line]
  intro ρ hρ
  rw [OnCriticalLine]
  obtain ⟨p, hp⟩ := exists_riemannXiDivisorZeroIndex_of_isNontrivialZero hρ
  by_contra hline
  have hpLine : (riemannXiDivisorZeroValue p).re ≠ 1 / 2 := by
    simpa only [hp] using hline
  obtain ⟨n, hn⟩ :=
    exists_liCoefficientCandidate_re_neg_of_divisorZero_re_ne_half p hpLine
  exact (not_lt_of_ge (hLi n)) hn

/-- Exact all-index Li nonnegativity criterion for `Mathlib.RiemannHypothesis`. -/
theorem riemannHypothesis_iff_forall_liCoefficientCandidate_re_nonneg :
    RiemannHypothesis ↔ ∀ n : ℕ, 0 ≤ (liCoefficientCandidate n).re := by
  constructor
  · intro hRH n
    exact RiemannHypothesis.liCoefficientCandidate_re_nonneg hRH n
  · exact riemannHypothesis_of_forall_liCoefficientCandidate_re_nonneg

end

end LeanLab.Riemann
