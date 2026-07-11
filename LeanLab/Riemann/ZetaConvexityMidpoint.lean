import LeanLab.Riemann.ZetaConvexity
import Mathlib.Analysis.Calculus.Deriv.Star
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.ZetaFiniteOrder

set_option linter.style.header false

/-!
# Corrected midpoint interpolation for the zeta convexity bound

This file formalizes the midpoint symmetrization from Fiori's correction of the
polynomial-boundary Phragmen-Lindelof argument. Integer powers avoid complex real powers inside
the analytic auxiliary function.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace LeanLab.Riemann

/-- The Schwarz reflection of an entire function. -/
def holomorphicReflection (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (starRingEnd ℂ) (f ((starRingEnd ℂ) z))

theorem differentiable_holomorphicReflection {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ (holomorphicReflection f) := by
  intro z
  change DifferentiableAt ℂ ((starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ)) z
  simpa only [Complex.conj_conj] using (hf ((starRingEnd ℂ) z)).conj_conj

/-- Fiori's corrected analytic quotient for left and right boundary powers `13/8` and `9/8`. -/
def fioriMidpointQuotient (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (f z) ^ 8 * (holomorphicReflection f (1 - z)) ^ 8 /
    (((1 : ℂ) + z) ^ 13 * ((2 : ℂ) - z) ^ 9)

private theorem closure_verticalStrip_zero_one_subset :
    closure (Complex.re ⁻¹' Set.Ioo (0 : ℝ) 1) ⊆ Complex.re ⁻¹' Set.Icc (0 : ℝ) 1 := by
  apply closure_minimal
  · exact preimage_mono Set.Ioo_subset_Icc_self
  · exact isClosed_Icc.preimage Complex.continuous_re

private theorem fioriMidpointDenominator_ne_zero
    {z : ℂ} (hz : z ∈ closure (Complex.re ⁻¹' Set.Ioo (0 : ℝ) 1)) :
    ((1 : ℂ) + z) ^ 13 * ((2 : ℂ) - z) ^ 9 ≠ 0 := by
  have hz' := closure_verticalStrip_zero_one_subset hz
  simp only [mem_preimage, mem_Icc] at hz'
  apply mul_ne_zero (pow_ne_zero _ ?_) (pow_ne_zero _ ?_)
  · intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith [hz'.1]
  · intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith [hz'.2]

/-- The corrected quotient is differentiable in the open strip and continuous on its closure. -/
theorem diffContOnCl_fioriMidpointQuotient {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    DiffContOnCl ℂ (fioriMidpointQuotient f)
      (Complex.re ⁻¹' Set.Ioo (0 : ℝ) 1) := by
  have hreflect : Differentiable ℂ (fun z : ℂ ↦ holomorphicReflection f (1 - z)) := by
    intro z
    exact (differentiable_holomorphicReflection hf (1 - z)).comp z
      (differentiableAt_const (c := (1 : ℂ)).sub differentiableAt_id)
  have hnum : Differentiable ℂ
      (fun z : ℂ ↦ (f z) ^ 8 * (holomorphicReflection f (1 - z)) ^ 8) :=
    hf.pow 8 |>.mul (hreflect.pow 8)
  have hden : Differentiable ℂ
      (fun z : ℂ ↦ ((1 : ℂ) + z) ^ 13 * ((2 : ℂ) - z) ^ 9) :=
    ((differentiable_const (c := (1 : ℂ)).add differentiable_id).pow 13).mul
      ((differentiable_const (c := (2 : ℂ)).sub differentiable_id).pow 9)
  constructor
  · intro z hz
    change DifferentiableWithinAt ℂ
      (fun z : ℂ ↦ (f z) ^ 8 * (holomorphicReflection f (1 - z)) ^ 8 /
        (((1 : ℂ) + z) ^ 13 * ((2 : ℂ) - z) ^ 9)) _ z
    exact ((hnum z).div (hden z)
      (fioriMidpointDenominator_ne_zero (subset_closure hz))).differentiableWithinAt
  · exact hnum.continuous.continuousOn.div₀ hden.continuous.continuousOn
      (fun z hz ↦ fioriMidpointDenominator_ne_zero hz)

private theorem norm_holomorphicReflection_one_sub_mul_I (f : ℂ → ℂ) (t : ℝ) :
    ‖holomorphicReflection f ((1 : ℂ) - t * Complex.I)‖ =
      ‖f ((1 : ℂ) + t * Complex.I)‖ := by
  rw [holomorphicReflection, Complex.norm_conj]
  congr 2
  apply Complex.ext <;> simp

private theorem norm_holomorphicReflection_one_sub_one_add_mul_I
    (f : ℂ → ℂ) (t : ℝ) :
    ‖holomorphicReflection f (1 - ((1 : ℂ) + t * Complex.I))‖ =
      ‖f (t * Complex.I)‖ := by
  rw [holomorphicReflection, Complex.norm_conj]
  congr 2
  apply Complex.ext <;> simp

private theorem norm_one_sub_mul_I_eq_norm_one_add_mul_I (t : ℝ) :
    ‖(1 : ℂ) - t * Complex.I‖ = ‖(1 : ℂ) + t * Complex.I‖ := by
  rw [Complex.norm_def, Complex.norm_def]
  congr 1
  simp [Complex.normSq_apply]

private theorem norm_two_sub_mul_I_eq_norm_two_add_mul_I (t : ℝ) :
    ‖(2 : ℂ) - t * Complex.I‖ = ‖(2 : ℂ) + t * Complex.I‖ := by
  rw [Complex.norm_def, Complex.norm_def]
  congr 1
  simp [Complex.normSq_apply]

private theorem norm_one_sub_mul_I_le_norm_two_add_mul_I (t : ℝ) :
    ‖(1 : ℂ) - t * Complex.I‖ ≤ ‖(2 : ℂ) + t * Complex.I‖ := by
  rw [Complex.norm_def, Complex.norm_def]
  apply Real.sqrt_le_sqrt
  simp [Complex.normSq_apply]
  norm_num

/-- On the left edge, the two factors match the denominator powers exactly. -/
theorem norm_fioriMidpointQuotient_mul_I_le
    {f : ℂ → ℂ} {A B : ℝ} (hA : 0 ≤ A) (_hB : 0 ≤ B)
    (hleft : ∀ t : ℝ, ‖f (t * Complex.I)‖ ^ 8 ≤
      A * ‖(1 : ℂ) + t * Complex.I‖ ^ 13)
    (hright : ∀ t : ℝ, ‖f ((1 : ℂ) + t * Complex.I)‖ ^ 8 ≤
      B * ‖(2 : ℂ) + t * Complex.I‖ ^ 9)
    (t : ℝ) :
    ‖fioriMidpointQuotient f (t * Complex.I)‖ ≤ A * B := by
  have hden_pos :
      0 < ‖(1 : ℂ) + t * Complex.I‖ ^ 13 *
        ‖(2 : ℂ) + t * Complex.I‖ ^ 9 := by
    apply mul_pos <;> apply pow_pos <;> rw [norm_pos_iff] <;> intro h
    all_goals have hre := congrArg Complex.re h
    all_goals norm_num at hre
  rw [fioriMidpointQuotient, norm_div, norm_mul, norm_mul, norm_pow, norm_pow,
    norm_pow, norm_pow, norm_holomorphicReflection_one_sub_mul_I,
    norm_two_sub_mul_I_eq_norm_two_add_mul_I]
  rw [div_le_iff₀ hden_pos]
  calc
    ‖f (t * Complex.I)‖ ^ 8 * ‖f ((1 : ℂ) + t * Complex.I)‖ ^ 8
        ≤ (A * ‖(1 : ℂ) + t * Complex.I‖ ^ 13) *
            (B * ‖(2 : ℂ) + t * Complex.I‖ ^ 9) := by
      exact mul_le_mul (hleft t) (hright t) (by positivity) (by positivity)
    _ = A * B *
        (‖(1 : ℂ) + t * Complex.I‖ ^ 13 *
          ‖(2 : ℂ) + t * Complex.I‖ ^ 9) := by ring

/-- On the right edge, monotonicity of `|Q+z|` in `Re(z)` compensates for the swapped powers. -/
theorem norm_fioriMidpointQuotient_one_add_mul_I_le
    {f : ℂ → ℂ} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hleft : ∀ t : ℝ, ‖f (t * Complex.I)‖ ^ 8 ≤
      A * ‖(1 : ℂ) + t * Complex.I‖ ^ 13)
    (hright : ∀ t : ℝ, ‖f ((1 : ℂ) + t * Complex.I)‖ ^ 8 ≤
      B * ‖(2 : ℂ) + t * Complex.I‖ ^ 9)
    (t : ℝ) :
    ‖fioriMidpointQuotient f ((1 : ℂ) + t * Complex.I)‖ ≤ A * B := by
  let a : ℝ := ‖(1 : ℂ) - t * Complex.I‖
  let b : ℝ := ‖(2 : ℂ) + t * Complex.I‖
  have ha_nonneg : 0 ≤ a := norm_nonneg _
  have hb_nonneg : 0 ≤ b := norm_nonneg _
  have hab : a ≤ b := norm_one_sub_mul_I_le_norm_two_add_mul_I t
  have hpower : a ^ 13 * b ^ 9 ≤ b ^ 13 * a ^ 9 := by
    calc
      a ^ 13 * b ^ 9 = (a ^ 9 * b ^ 9) * a ^ 4 := by ring
      _ ≤ (a ^ 9 * b ^ 9) * b ^ 4 := by gcongr
      _ = b ^ 13 * a ^ 9 := by ring
  have hden_pos : 0 < b ^ 13 * a ^ 9 := by
    apply mul_pos <;> apply pow_pos <;> rw [norm_pos_iff]
    · intro h
      have hre := congrArg Complex.re h
      norm_num at hre
    · intro h
      have hre := congrArg Complex.re h
      norm_num at hre
  rw [fioriMidpointQuotient, norm_div, norm_mul, norm_mul, norm_pow, norm_pow,
    norm_pow, norm_pow, norm_holomorphicReflection_one_sub_one_add_mul_I]
  rw [show (1 : ℂ) + ((1 : ℂ) + t * Complex.I) = 2 + t * Complex.I by ring,
    show (2 : ℂ) - ((1 : ℂ) + t * Complex.I) = 1 - t * Complex.I by ring]
  change ‖f ((1 : ℂ) + t * Complex.I)‖ ^ 8 * ‖f (t * Complex.I)‖ ^ 8 /
      (b ^ 13 * a ^ 9) ≤ A * B
  rw [div_le_iff₀ hden_pos]
  calc
    ‖f ((1 : ℂ) + t * Complex.I)‖ ^ 8 * ‖f (t * Complex.I)‖ ^ 8
        ≤ (B * b ^ 9) * (A * a ^ 13) := by
      exact mul_le_mul (by simpa [b] using hright t)
        (by simpa [a, norm_one_sub_mul_I_eq_norm_one_add_mul_I] using hleft t)
        (by positivity) (by positivity)
    _ = A * B * (a ^ 13 * b ^ 9) := by ring
    _ ≤ A * B * (b ^ 13 * a ^ 9) := by
      exact mul_le_mul_of_nonneg_left hpower (mul_nonneg hA hB)

/-- The vertical-strip principle applied to Fiori's corrected quotient. The growth premise remains
explicit here and must be discharged for every application. -/
theorem norm_fioriMidpointQuotient_le_of_growth
    {f : ℂ → ℂ} {A B : ℝ} (hf : Differentiable ℂ f) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hleft : ∀ t : ℝ, ‖f (t * Complex.I)‖ ^ 8 ≤
      A * ‖(1 : ℂ) + t * Complex.I‖ ^ 13)
    (hright : ∀ t : ℝ, ‖f ((1 : ℂ) + t * Complex.I)‖ ^ 8 ≤
      B * ‖(2 : ℂ) + t * Complex.I‖ ^ 9)
    (hgrowth : ∃ c < Real.pi, ∃ D : ℝ,
      fioriMidpointQuotient f =O[
        comap (_root_.abs ∘ Complex.im) atTop ⊓
          Filter.principal (Complex.re ⁻¹' Set.Ioo (0 : ℝ) 1)]
        fun z ↦ Real.exp (D * Real.exp (c * |z.im|)))
    {z : ℂ} (hz_re : z.re ∈ Set.Icc (0 : ℝ) 1) :
    ‖fioriMidpointQuotient f z‖ ≤ A * B := by
  apply PhragmenLindelof.vertical_strip (a := (0 : ℝ)) (b := (1 : ℝ))
    (diffContOnCl_fioriMidpointQuotient hf)
  · simpa using hgrowth
  · intro w hw
    have hw_eq : w = w.im * Complex.I := by
      apply Complex.ext <;> simp [hw]
    rw [hw_eq]
    exact norm_fioriMidpointQuotient_mul_I_le hA hB hleft hright w.im
  · intro w hw
    have hw_eq : w = (1 : ℂ) + w.im * Complex.I := by
      apply Complex.ext <;> simp [hw]
    rw [hw_eq]
    exact norm_fioriMidpointQuotient_one_add_mul_I_le hA hB hleft hright w.im
  · exact hz_re.1
  · exact hz_re.2

/-- An asymptotic `13/8` bound gives the integer-power boundary datum on the whole left edge. -/
theorem exists_fiori_left_boundary_constant
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hasym : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖f (t * Complex.I)‖ ≤ C * (1 + |t|) ^ (13 / 8 : ℝ)) :
    ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ,
      ‖f (t * Complex.I)‖ ^ 8 ≤ A * ‖(1 : ℂ) + t * Complex.I‖ ^ 13 := by
  obtain ⟨C, hC, hasym⟩ := hasym
  have hline : Continuous (fun t : ℝ ↦ f (t * Complex.I)) := by
    exact hf.continuous.comp (Complex.continuous_ofReal.mul continuous_const)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hline.continuousOn
  let A : ℝ := max 1 (max (M ^ 8) (C ^ 8 * 2 ^ 13))
  have hA_pos : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hA_nonneg : 0 ≤ A := hA_pos.le
  have hM_le_A : M ^ 8 ≤ A := (le_max_left _ _).trans (le_max_right _ _)
  have hC_le_A : C ^ 8 * 2 ^ 13 ≤ A :=
    (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨A, hA_pos, ?_⟩
  intro t
  by_cases ht : 1 ≤ |t|
  · let x : ℝ := 1 + |t|
    let b : ℝ := ‖(1 : ℂ) + t * Complex.I‖
    have hx_pos : 0 < x := by dsimp only [x]; positivity
    have hx_nonneg : 0 ≤ x := hx_pos.le
    have hb_nonneg : 0 ≤ b := norm_nonneg _
    have him : |t| ≤ b := by
      dsimp only [b]
      simpa using Complex.abs_im_le_norm ((1 : ℂ) + t * Complex.I)
    have hre : 1 ≤ b := by
      dsimp only [b]
      simpa using Complex.abs_re_le_norm ((1 : ℂ) + t * Complex.I)
    have hxb : x ≤ 2 * b := by
      dsimp only [x]
      linarith
    have hpow_asym :
        (C * x ^ (13 / 8 : ℝ)) ^ 8 = C ^ 8 * x ^ 13 := by
      rw [mul_pow]
      congr 1
      rw [← Real.rpow_mul_natCast hx_nonneg]
      norm_num
    have hxb_pow : x ^ 13 ≤ (2 * b) ^ 13 := by gcongr
    calc
      ‖f (t * Complex.I)‖ ^ 8 ≤ (C * x ^ (13 / 8 : ℝ)) ^ 8 := by
        gcongr
        simpa only [x] using hasym t ht
      _ = C ^ 8 * x ^ 13 := hpow_asym
      _ ≤ C ^ 8 * (2 * b) ^ 13 := by
        exact mul_le_mul_of_nonneg_left hxb_pow (by positivity)
      _ = (C ^ 8 * 2 ^ 13) * b ^ 13 := by ring
      _ ≤ A * b ^ 13 := by
        exact mul_le_mul_of_nonneg_right hC_le_A (by positivity)
      _ = A * ‖(1 : ℂ) + t * Complex.I‖ ^ 13 := rfl
  · have ht_mem : t ∈ Set.Icc (-1 : ℝ) 1 := by
      rw [mem_Icc]
      have ht_abs : |t| < 1 := lt_of_not_ge ht
      rw [abs_lt] at ht_abs
      exact ⟨ht_abs.1.le, ht_abs.2.le⟩
    have hfM : ‖f (t * Complex.I)‖ ≤ M := hM t ht_mem
    have hbase : 1 ≤ ‖(1 : ℂ) + t * Complex.I‖ := by
      simpa using Complex.abs_re_le_norm ((1 : ℂ) + t * Complex.I)
    calc
      ‖f (t * Complex.I)‖ ^ 8 ≤ M ^ 8 := by gcongr
      _ ≤ A := hM_le_A
      _ = A * 1 := by ring
      _ ≤ A * ‖(1 : ℂ) + t * Complex.I‖ ^ 13 := by
        exact mul_le_mul_of_nonneg_left (one_le_pow₀ hbase) hA_nonneg

/-- An asymptotic `9/8` bound gives the integer-power boundary datum on the whole right edge. -/
theorem exists_fiori_right_boundary_constant
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hasym : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖f ((1 : ℂ) + t * Complex.I)‖ ≤ C * (1 + |t|) ^ (9 / 8 : ℝ)) :
    ∃ B : ℝ, 0 < B ∧ ∀ t : ℝ,
      ‖f ((1 : ℂ) + t * Complex.I)‖ ^ 8 ≤
        B * ‖(2 : ℂ) + t * Complex.I‖ ^ 9 := by
  obtain ⟨C, hC, hasym⟩ := hasym
  have hline : Continuous (fun t : ℝ ↦ f ((1 : ℂ) + t * Complex.I)) := by
    exact hf.continuous.comp
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hline.continuousOn
  let B : ℝ := max 1 (max (M ^ 8) (C ^ 8 * 2 ^ 9))
  have hB_pos : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hB_nonneg : 0 ≤ B := hB_pos.le
  have hM_le_B : M ^ 8 ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hC_le_B : C ^ 8 * 2 ^ 9 ≤ B :=
    (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨B, hB_pos, ?_⟩
  intro t
  by_cases ht : 1 ≤ |t|
  · let x : ℝ := 1 + |t|
    let b : ℝ := ‖(2 : ℂ) + t * Complex.I‖
    have hx_pos : 0 < x := by dsimp only [x]; positivity
    have hx_nonneg : 0 ≤ x := hx_pos.le
    have hb_nonneg : 0 ≤ b := norm_nonneg _
    have him : |t| ≤ b := by
      dsimp only [b]
      simpa using Complex.abs_im_le_norm ((2 : ℂ) + t * Complex.I)
    have hre : 1 ≤ b := by
      dsimp only [b]
      have h := Complex.abs_re_le_norm ((2 : ℂ) + t * Complex.I)
      norm_num at h
      linarith
    have hxb : x ≤ 2 * b := by
      dsimp only [x]
      linarith
    have hpow_asym :
        (C * x ^ (9 / 8 : ℝ)) ^ 8 = C ^ 8 * x ^ 9 := by
      rw [mul_pow]
      congr 1
      rw [← Real.rpow_mul_natCast hx_nonneg]
      norm_num
    have hxb_pow : x ^ 9 ≤ (2 * b) ^ 9 := by gcongr
    calc
      ‖f ((1 : ℂ) + t * Complex.I)‖ ^ 8 ≤
          (C * x ^ (9 / 8 : ℝ)) ^ 8 := by
        gcongr
        simpa only [x] using hasym t ht
      _ = C ^ 8 * x ^ 9 := hpow_asym
      _ ≤ C ^ 8 * (2 * b) ^ 9 := by
        exact mul_le_mul_of_nonneg_left hxb_pow (by positivity)
      _ = (C ^ 8 * 2 ^ 9) * b ^ 9 := by ring
      _ ≤ B * b ^ 9 := by
        exact mul_le_mul_of_nonneg_right hC_le_B (by positivity)
      _ = B * ‖(2 : ℂ) + t * Complex.I‖ ^ 9 := rfl
  · have ht_mem : t ∈ Set.Icc (-1 : ℝ) 1 := by
      rw [mem_Icc]
      have ht_abs : |t| < 1 := lt_of_not_ge ht
      rw [abs_lt] at ht_abs
      exact ⟨ht_abs.1.le, ht_abs.2.le⟩
    have hfM : ‖f ((1 : ℂ) + t * Complex.I)‖ ≤ M := hM t ht_mem
    have hbase : 1 ≤ ‖(2 : ℂ) + t * Complex.I‖ := by
      have h := Complex.abs_re_le_norm ((2 : ℂ) + t * Complex.I)
      norm_num at h
      linarith
    calc
      ‖f ((1 : ℂ) + t * Complex.I)‖ ^ 8 ≤ M ^ 8 := by gcongr
      _ ≤ B := hM_le_B
      _ = B * 1 := by ring
      _ ≤ B * ‖(2 : ℂ) + t * Complex.I‖ ^ 9 := by
        exact mul_le_mul_of_nonneg_left (one_le_pow₀ hbase) hB_nonneg

theorem zetaPoleRemoved_eq_zetaTimesSMinusOne_entire :
    zetaPoleRemoved = Complex.zetaTimesSMinusOne_entire := by
  exact Complex.eq_zetaTimesSMinusOne_entire_of_eq_on_compl_singleton
    zetaPoleRemoved_one (fun _ hs ↦ zetaPoleRemoved_eq hs)

/-- The audited finite-order theorem gives a direct global exponential bound for the project's
pole-removed zeta function. -/
theorem exists_norm_zetaPoleRemoved_le_exp_sq :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
      ‖zetaPoleRemoved z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (2 : ℝ)) := by
  obtain ⟨C, hC, hgrowth⟩ := Complex.zeta_minus_pole_entire_growth
  refine ⟨C, hC, ?_⟩
  intro z
  rw [zetaPoleRemoved_eq_zetaTimesSMinusOne_entire]
  have hlog := hgrowth z
  have hexp := (Real.exp_le_exp.mpr hlog)
  rw [Real.exp_log (by positivity)] at hexp
  exact (le_add_of_nonneg_left (by norm_num)).trans hexp

private theorem norm_le_one_add_abs_im_of_re_mem_Icc
    {z : ℂ} (hz : z.re ∈ Set.Icc (0 : ℝ) 1) :
    ‖z‖ ≤ 1 + |z.im| := by
  calc
    ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ 1 + |z.im| := by
      rw [abs_of_nonneg hz.1]
      linarith [hz.2]

/-- Pointwise finite-order control of Fiori's quotient throughout the closed strip. -/
theorem norm_fioriMidpointQuotient_zetaPoleRemoved_le_exp_sq
    {C : ℝ} (hC : 0 < C)
    (hgrowth : ∀ z : ℂ,
      ‖zetaPoleRemoved z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (2 : ℝ)))
    {z : ℂ} (hz : z.re ∈ Set.Icc (0 : ℝ) 1) :
    ‖fioriMidpointQuotient zetaPoleRemoved z‖ ≤
      Real.exp (16 * C * (2 + |z.im|) ^ (2 : ℝ)) := by
  let w : ℂ := (starRingEnd ℂ) (1 - z)
  have hw_re : w.re ∈ Set.Icc (0 : ℝ) 1 := by
    change 0 ≤ 1 - z.re ∧ 1 - z.re ≤ 1
    constructor <;> linarith [hz.1, hz.2]
  have hw_im : w.im = z.im := by simp [w]
  have hz_norm : ‖z‖ ≤ 1 + |z.im| := norm_le_one_add_abs_im_of_re_mem_Icc hz
  have hw_norm : ‖w‖ ≤ 1 + |z.im| := by
    rw [← hw_im]
    exact norm_le_one_add_abs_im_of_re_mem_Icc hw_re
  have hbase_nonneg : 0 ≤ 2 + |z.im| := by positivity
  have hz_growth :
      ‖zetaPoleRemoved z‖ ≤ Real.exp (C * (2 + |z.im|) ^ (2 : ℝ)) := by
    exact (hgrowth z).trans (Real.exp_le_exp.mpr <| mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)) hC.le)
  have hw_growth :
      ‖zetaPoleRemoved w‖ ≤ Real.exp (C * (2 + |z.im|) ^ (2 : ℝ)) := by
    exact (hgrowth w).trans (Real.exp_le_exp.mpr <| mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)) hC.le)
  have hreflect :
      ‖holomorphicReflection zetaPoleRemoved (1 - z)‖ = ‖zetaPoleRemoved w‖ := by
    rw [holomorphicReflection, Complex.norm_conj]
  have hden_one :
      1 ≤ ‖(1 : ℂ) + z‖ ^ 13 * ‖(2 : ℂ) - z‖ ^ 9 := by
    have hleft : 1 ≤ ‖(1 : ℂ) + z‖ := by
      have h := Complex.abs_re_le_norm ((1 : ℂ) + z)
      have hnonneg : 0 ≤ ((1 : ℂ) + z).re := by simp; linarith [hz.1]
      rw [abs_of_nonneg hnonneg] at h
      norm_num at h
      linarith [hz.1]
    have hright : 1 ≤ ‖(2 : ℂ) - z‖ := by
      have h := Complex.abs_re_le_norm ((2 : ℂ) - z)
      have hnonneg : 0 ≤ ((2 : ℂ) - z).re := by simp; linarith [hz.2]
      rw [abs_of_nonneg hnonneg] at h
      norm_num at h
      linarith [hz.2]
    nlinarith [one_le_pow₀ hleft (n := 13), one_le_pow₀ hright (n := 9)]
  rw [fioriMidpointQuotient, norm_div, norm_mul, norm_mul, norm_pow, norm_pow,
    norm_pow, norm_pow, hreflect]
  calc
    ‖zetaPoleRemoved z‖ ^ 8 * ‖zetaPoleRemoved w‖ ^ 8 /
        (‖(1 : ℂ) + z‖ ^ 13 * ‖(2 : ℂ) - z‖ ^ 9)
        ≤ ‖zetaPoleRemoved z‖ ^ 8 * ‖zetaPoleRemoved w‖ ^ 8 :=
      div_le_self (by positivity) hden_one
    _ ≤ (Real.exp (C * (2 + |z.im|) ^ (2 : ℝ))) ^ 8 *
        (Real.exp (C * (2 + |z.im|) ^ (2 : ℝ))) ^ 8 := by gcongr
    _ = Real.exp (16 * C * (2 + |z.im|) ^ (2 : ℝ)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring

/-- The corrected zeta quotient satisfies the exact double-exponential growth premise of the
vertical-strip Phragmen-Lindelof theorem. -/
theorem fioriMidpointQuotient_zetaPoleRemoved_growth :
    ∃ c < Real.pi, ∃ D : ℝ,
      fioriMidpointQuotient zetaPoleRemoved =O[
        comap (_root_.abs ∘ Complex.im) atTop ⊓
          Filter.principal (Complex.re ⁻¹' Set.Ioo (0 : ℝ) 1)]
        fun z ↦ Real.exp (D * Real.exp (c * |z.im|)) := by
  obtain ⟨C, hC, hgrowth⟩ := exists_norm_zetaPoleRemoved_le_exp_sq
  let K : ℝ := 64 * C
  have hK : 0 < K := mul_pos (by norm_num) hC
  have hsmall := (Real.isLittleO_pow_exp_atTop (n := 2)).def (inv_pos.mpr hK)
  have hev_real : ∀ᶠ T : ℝ in atTop,
      16 * C * (2 + T) ^ (2 : ℝ) ≤ Real.exp T := by
    filter_upwards [hsmall, eventually_ge_atTop (2 : ℝ)] with T hsmall_T hT
    have hsmall_T' : T ^ 2 ≤ K⁻¹ * Real.exp T := by
      simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg T),
        abs_of_pos (Real.exp_pos T)] using hsmall_T
    have hK_bound : K * T ^ 2 ≤ Real.exp T := by
      calc
        K * T ^ 2 ≤ K * (K⁻¹ * Real.exp T) :=
          mul_le_mul_of_nonneg_left hsmall_T' hK.le
        _ = Real.exp T := by field_simp
    have hsq : (2 + T) ^ (2 : ℝ) ≤ 4 * T ^ 2 := by
      rw [Real.rpow_two]
      nlinarith [sq_nonneg T]
    calc
      16 * C * (2 + T) ^ (2 : ℝ) ≤ 64 * C * T ^ 2 := by
        calc
          16 * C * (2 + T) ^ (2 : ℝ) ≤ 16 * C * (4 * T ^ 2) :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
          _ = 64 * C * T ^ 2 := by ring
      _ = K * T ^ 2 := rfl
      _ ≤ Real.exp T := hK_bound
  have hev_complex : ∀ᶠ z : ℂ in comap (_root_.abs ∘ Complex.im) atTop,
      16 * C * (2 + |z.im|) ^ (2 : ℝ) ≤ Real.exp |z.im| := by
    exact tendsto_comap.eventually hev_real
  refine ⟨1, by linarith [Real.pi_gt_three], 1, ?_⟩
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, ?_⟩
  rw [eventually_inf_principal]
  filter_upwards [hev_complex] with z hdom hz
  have hz_closed : z.re ∈ Set.Icc (0 : ℝ) 1 := ⟨hz.1.le, hz.2.le⟩
  calc
    ‖fioriMidpointQuotient zetaPoleRemoved z‖
        ≤ Real.exp (16 * C * (2 + |z.im|) ^ (2 : ℝ)) :=
      norm_fioriMidpointQuotient_zetaPoleRemoved_le_exp_sq hC hgrowth hz_closed
    _ ≤ Real.exp (Real.exp |z.im|) := Real.exp_le_exp.mpr hdom
    _ = 1 * ‖Real.exp (1 * Real.exp (1 * |z.im|))‖ := by
      simp [Real.norm_eq_abs]

private theorem norm_three_halves_sub_mul_I_eq_add (t : ℝ) :
    ‖(3 / 2 : ℂ) - t * Complex.I‖ = ‖(3 / 2 : ℂ) + t * Complex.I‖ := by
  rw [Complex.norm_def, Complex.norm_def]
  congr 1
  simp [Complex.normSq_apply]

/-- Fiori's quotient bound at the midpoint, before taking the sixteenth root. -/
theorem exists_norm_zetaPoleRemoved_criticalLine_pow_sixteen_le :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ t : ℝ,
      ‖zetaPoleRemoved ((1 / 2 : ℂ) + t * Complex.I)‖ ^ 16 ≤
        A * B * ‖(3 / 2 : ℂ) + t * Complex.I‖ ^ 22 := by
  obtain ⟨A, hA, hleft⟩ := exists_fiori_left_boundary_constant
    differentiable_zetaPoleRemoved exists_norm_zetaPoleRemoved_mul_I_le_rpow
  obtain ⟨B, hB, hright⟩ := exists_fiori_right_boundary_constant
    differentiable_zetaPoleRemoved exists_norm_zetaPoleRemoved_one_add_mul_I_le_rpow
  refine ⟨A, B, hA, hB, ?_⟩
  intro t
  let s : ℂ := (1 / 2 : ℂ) + t * Complex.I
  let b : ℝ := ‖(3 / 2 : ℂ) + t * Complex.I‖
  have hs_re : s.re ∈ Set.Icc (0 : ℝ) 1 := by
    norm_num [s, Complex.div_re, Complex.normSq]
  have hq := norm_fioriMidpointQuotient_le_of_growth
    differentiable_zetaPoleRemoved hA.le hB.le hleft hright
    fioriMidpointQuotient_zetaPoleRemoved_growth hs_re
  have hreflect :
      ‖holomorphicReflection zetaPoleRemoved (1 - s)‖ = ‖zetaPoleRemoved s‖ := by
    rw [holomorphicReflection, Complex.norm_conj]
    congr 2
    apply Complex.ext <;> norm_num [s, Complex.div_re, Complex.normSq]
  have hleft_arg : (1 : ℂ) + s = (3 / 2 : ℂ) + t * Complex.I := by
    simp only [s]
    ring
  have hright_arg : (2 : ℂ) - s = (3 / 2 : ℂ) - t * Complex.I := by
    simp only [s]
    ring
  have hden_pos : 0 < b ^ 22 := by
    apply pow_pos
    dsimp only [b]
    rw [norm_pos_iff]
    intro h
    have hre := congrArg Complex.re h
    norm_num [Complex.div_re, Complex.normSq] at hre
  rw [fioriMidpointQuotient, norm_div, norm_mul, norm_mul, norm_pow, norm_pow,
    norm_pow, norm_pow, hreflect, hleft_arg, hright_arg,
    norm_three_halves_sub_mul_I_eq_add] at hq
  change ‖zetaPoleRemoved s‖ ^ 8 * ‖zetaPoleRemoved s‖ ^ 8 /
      (b ^ 13 * b ^ 9) ≤ A * B at hq
  rw [← pow_add, ← pow_add] at hq
  norm_num at hq
  exact (div_le_iff₀ hden_pos).mp hq

/-- Taking the sixteenth root gives the midpoint exponent `11/8` for the pole-removed zeta
function. -/
theorem exists_norm_zetaPoleRemoved_criticalLine_le_rpow :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖zetaPoleRemoved ((1 / 2 : ℂ) + t * Complex.I)‖ ≤
        C * (1 + |t|) ^ (11 / 8 : ℝ) := by
  obtain ⟨A, B, hA, hB, hpow⟩ :=
    exists_norm_zetaPoleRemoved_criticalLine_pow_sixteen_le
  let D : ℝ := (A * B) ^ (1 / 16 : ℝ) * (2 : ℝ) ^ (11 / 8 : ℝ)
  have hAB : 0 < A * B := mul_pos hA hB
  have hD : 0 < D := mul_pos (Real.rpow_pos_of_pos hAB _) (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨D, hD, ?_⟩
  intro t
  let y : ℝ := ‖zetaPoleRemoved ((1 / 2 : ℂ) + t * Complex.I)‖
  let b : ℝ := ‖(3 / 2 : ℂ) + t * Complex.I‖
  let x : ℝ := 1 + |t|
  have hy_nonneg : 0 ≤ y := norm_nonneg _
  have hb_nonneg : 0 ≤ b := norm_nonneg _
  have hx_pos : 0 < x := by dsimp only [x]; positivity
  have hb_le : b ≤ 2 * x := by
    calc
      b ≤ |(((3 / 2 : ℂ) + t * Complex.I).re)| +
          |(((3 / 2 : ℂ) + t * Complex.I).im)| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = 3 / 2 + |t| := by norm_num [Complex.div_re, Complex.normSq]
      _ ≤ 2 * x := by dsimp only [x]; linarith [abs_nonneg t]
  have hroot := Real.rpow_le_rpow (pow_nonneg hy_nonneg 16)
    (by simpa only [y, b] using hpow t) (show (0 : ℝ) ≤ 1 / 16 by norm_num)
  have hleft_root : (y ^ 16) ^ (1 / 16 : ℝ) = y := by
    simpa using Real.pow_rpow_inv_natCast hy_nonneg (show (16 : ℕ) ≠ 0 by norm_num)
  have hright_root :
      (A * B * b ^ 22) ^ (1 / 16 : ℝ) =
        (A * B) ^ (1 / 16 : ℝ) * b ^ (11 / 8 : ℝ) := by
    rw [Real.mul_rpow hAB.le (pow_nonneg hb_nonneg 22)]
    congr 1
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hb_nonneg]
    norm_num
  rw [hleft_root, hright_root] at hroot
  calc
    y ≤ (A * B) ^ (1 / 16 : ℝ) * b ^ (11 / 8 : ℝ) := hroot
    _ ≤ (A * B) ^ (1 / 16 : ℝ) * (2 * x) ^ (11 / 8 : ℝ) := by
      gcongr
    _ = D * x ^ (11 / 8 : ℝ) := by
      rw [Real.mul_rpow (by norm_num) hx_pos.le]
      simp only [D]
      ring
    _ = D * (1 + |t|) ^ (11 / 8 : ℝ) := rfl

/-- An unconditional critical-line zeta bound with exponent `3/8`, strictly below the `L²`
threshold `1/2` needed in the fixed Burnol/Baez-Duarte route. -/
theorem exists_norm_riemannZeta_criticalLine_le_rpow :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖riemannZeta ((1 / 2 : ℂ) + t * Complex.I)‖ ≤
        C * (1 + |t|) ^ (3 / 8 : ℝ) := by
  obtain ⟨C, hC, hpoleRemoved⟩ := exists_norm_zetaPoleRemoved_criticalLine_le_rpow
  refine ⟨2 * C, mul_pos (by norm_num) hC, ?_⟩
  intro t ht
  let s : ℂ := (1 / 2 : ℂ) + t * Complex.I
  let x : ℝ := 1 + |t|
  have hx_pos : 0 < x := by dsimp only [x]; positivity
  have ht_pos : 0 < |t| := zero_lt_one.trans_le ht
  have hs_ne : s ≠ 1 := by
    intro hs
    have hre := congrArg Complex.re hs
    norm_num [s, Complex.div_re, Complex.normSq] at hre
  have hfactor : |t| ≤ ‖s - 1‖ := by
    calc
      |t| = |(s - 1).im| := by
        congr 1
        simp [s, Complex.normSq]
      _ ≤ ‖s - 1‖ := Complex.abs_im_le_norm (s - 1)
  have hpole := hpoleRemoved t
  rw [zetaPoleRemoved_eq hs_ne, norm_mul] at hpole
  have hprod : |t| * ‖riemannZeta s‖ ≤ C * x ^ (11 / 8 : ℝ) := by
    calc
      |t| * ‖riemannZeta s‖ ≤ ‖s - 1‖ * ‖riemannZeta s‖ :=
        mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)
      _ ≤ C * x ^ (11 / 8 : ℝ) := by simpa only [s, x] using hpole
  have hzeta_div :
      ‖riemannZeta s‖ ≤ C * x ^ (11 / 8 : ℝ) / |t| := by
    rw [le_div_iff₀ ht_pos]
    simpa [mul_comm] using hprod
  have hx_abs : x / |t| ≤ 2 := by
    rw [div_le_iff₀ ht_pos]
    dsimp only [x]
    linarith
  have hx_split : x ^ (11 / 8 : ℝ) = x ^ (3 / 8 : ℝ) * x := by
    calc
      x ^ (11 / 8 : ℝ) = x ^ ((3 / 8 : ℝ) + 1) := by norm_num
      _ = x ^ (3 / 8 : ℝ) * x ^ (1 : ℝ) := Real.rpow_add hx_pos _ _
      _ = x ^ (3 / 8 : ℝ) * x := by rw [Real.rpow_one]
  calc
    ‖riemannZeta ((1 / 2 : ℂ) + t * Complex.I)‖
        ≤ C * x ^ (11 / 8 : ℝ) / |t| := by simpa only [s] using hzeta_div
    _ = (C * x ^ (3 / 8 : ℝ)) * (x / |t|) := by rw [hx_split]; ring
    _ ≤ (C * x ^ (3 / 8 : ℝ)) * 2 := by
      exact mul_le_mul_of_nonneg_left hx_abs (by positivity)
    _ = 2 * C * x ^ (3 / 8 : ℝ) := by ring
    _ = 2 * C * (1 + |t|) ^ (3 / 8 : ℝ) := rfl

end LeanLab.Riemann
