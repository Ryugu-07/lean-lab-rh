import LeanLab.Riemann.M2GramGeometry
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option linter.style.header false

/-!
# A local obstruction for the sparse Baez-Duarte family

This file is the single proof batch preregistered as
`CAMPAIGN-20260715-SPARSE-OBSTRUCTION-01`. It constructs an explicit compactly supported vector
orthogonal to every normalized kernel indexed by `(2^24)^j`, but not to the exact target. The
result excludes only this sparse closed span; it says nothing negative about the full natural
Baez-Duarte criterion.
-/

noncomputable section

open Complex MeasureTheory Set
open scoped ENNReal InnerProductSpace Real

namespace LeanLab.Riemann

/-- A compactly supported linear piece used in the separating witness. -/
def sparseTargetWitnessPiece (a b c x : Real) : Real :=
  (Ioc a b).indicator (fun y => c * y) x

theorem sparseTargetWitnessPiece_memLp (a b c : Real) :
    MemLp (sparseTargetWitnessPiece a b c) (2 : ENNReal)
      (volume.restrict (Ioi (0 : Real))) := by
  have hstrong : StronglyMeasurable (sparseTargetWitnessPiece a b c) := by
    exact (continuous_const.mul continuous_id).stronglyMeasurable.indicator measurableSet_Ioc
  rw [memLp_two_iff_integrable_sq hstrong.aestronglyMeasurable]
  have hlocal : IntegrableOn (fun x : Real => (c * x) ^ 2) (Ioc a b) volume :=
    ((continuous_const.mul continuous_id).pow 2).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  have hfull : Integrable ((Ioc a b).indicator (fun x : Real => (c * x) ^ 2)) volume :=
    hlocal.integrable_indicator measurableSet_Ioc
  have hrestricted := hfull.mono_measure (Measure.restrict_le_self :
    volume.restrict (Ioi (0 : Real)) <= volume)
  refine hrestricted.congr (ae_of_all _ fun x => ?_)
  by_cases hx : x ∈ Ioc a b <;>
    simp [sparseTargetWitnessPiece, hx]

/-- The three-piece real witness as an actual `L2(0,infinity)` element. -/
def sparseTargetWitnessRealL2 : positiveHalfLineL2 :=
  (sparseTargetWitnessPiece_memLp (1 / 2) (2 / 3) 118).toLp
      (sparseTargetWitnessPiece (1 / 2) (2 / 3) 118) +
    (sparseTargetWitnessPiece_memLp (1 / 3) (2 / 5) (-925)).toLp
      (sparseTargetWitnessPiece (1 / 3) (2 / 5) (-925)) +
    (sparseTargetWitnessPiece_memLp (1 / 4) (2 / 7) 1176).toLp
      (sparseTargetWitnessPiece (1 / 4) (2 / 7) 1176)

/-- The separating witness in the exact complex Hilbert space used by the RH criterion. -/
def sparseTargetWitnessL2 : positiveHalfLineComplexL2 :=
  baezDuarteOfRealLp sparseTargetWitnessRealL2

theorem sparseTargetWitnessPiece_toLp_coeFn (a b c : Real) :
    (sparseTargetWitnessPiece_memLp a b c).toLp (sparseTargetWitnessPiece a b c)
      =ᵐ[volume.restrict (Ioi (0 : Real))] sparseTargetWitnessPiece a b c :=
  MemLp.coeFn_toLp (sparseTargetWitnessPiece_memLp a b c)

theorem inner_baezDuarteKernelL2_sparseTargetWitnessPiece_eq_integral
    (n : baezDuartePositiveNatIndex) (a b c : Real) :
    ⟪baezDuarteKernelL2 n,
        (sparseTargetWitnessPiece_memLp a b c).toLp
          (sparseTargetWitnessPiece a b c)⟫_Real =
      ∫ x : Real,
        fractionalPartKernel (((n : Nat) : Real)⁻¹) x *
          sparseTargetWitnessPiece a b c x ∂
            (volume.restrict (Ioi (0 : Real))) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [baezDuarteKernelL2_coeFn n,
    sparseTargetWitnessPiece_toLp_coeFn a b c] with x hk hw
  simp [hk, hw, RCLike.inner_apply, mul_comm]

theorem inner_baezDuarteTargetL2_sparseTargetWitnessPiece_eq_integral
    (a b c : Real) :
    ⟪baezDuarteTargetL2,
        (sparseTargetWitnessPiece_memLp a b c).toLp
          (sparseTargetWitnessPiece a b c)⟫_Real =
      ∫ x : Real, baezDuarteTargetFunction x * sparseTargetWitnessPiece a b c x ∂
        (volume.restrict (Ioi (0 : Real))) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [baezDuarteTargetL2_coeFn,
    sparseTargetWitnessPiece_toLp_coeFn a b c] with x ht hw
  simp [ht, hw, RCLike.inner_apply, mul_comm]

theorem integral_mul_sparseTargetWitnessPiece_of_eq_div
    (f : Real -> Real) (r a b c : Real) (ha : 0 < a) (hab : a <= b)
    (hf : ∀ x ∈ Ioc a b, f x = r / x) :
    (∫ x : Real, f x * sparseTargetWitnessPiece a b c x ∂
        (volume.restrict (Ioi (0 : Real)))) = r * c * (b - a) := by
  have hsubset : Ioc a b <= Ioi (0 : Real) := by
    intro x hx
    exact lt_trans ha hx.1
  calc
    (∫ x : Real, f x * sparseTargetWitnessPiece a b c x ∂
        (volume.restrict (Ioi (0 : Real)))) =
        ∫ x : Real, (Ioc a b).indicator (fun _ => r * c) x ∂
          (volume.restrict (Ioi (0 : Real))) := by
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ Ioc a b
      · have hx0 : x ≠ 0 := (lt_trans ha hx.1).ne'
        rw [hf x hx]
        simp [sparseTargetWitnessPiece, hx]
        field_simp
      · simp [sparseTargetWitnessPiece, hx]
    _ = ∫ _ : Real in a..b, r * c := by
      rw [integral_indicator measurableSet_Ioc,
        Measure.restrict_restrict_of_subset hsubset,
        intervalIntegral.integral_of_le hab]
    _ = r * c * (b - a) := by
      rw [intervalIntegral.integral_const]
      simp [smul_eq_mul]
      ring

theorem integral_mul_sparseTargetWitnessPiece_of_eq_div_sub
    (f : Real -> Real) (k a b c : Real) (ha : 0 < a) (hab : a <= b)
    (hf : ∀ x ∈ Ioc a b, f x = 1 / x - k) :
    (∫ x : Real, f x * sparseTargetWitnessPiece a b c x ∂
        (volume.restrict (Ioi (0 : Real)))) =
      c * (b - a) - k * c * ((b ^ 2 - a ^ 2) / 2) := by
  have hsubset : Ioc a b <= Ioi (0 : Real) := by
    intro x hx
    exact lt_trans ha hx.1
  calc
    (∫ x : Real, f x * sparseTargetWitnessPiece a b c x ∂
        (volume.restrict (Ioi (0 : Real)))) =
        ∫ x : Real, (Ioc a b).indicator
          (fun x => c - k * c * x) x ∂
            (volume.restrict (Ioi (0 : Real))) := by
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ Ioc a b
      · have hx0 : x ≠ 0 := (lt_trans ha hx.1).ne'
        rw [hf x hx]
        simp [sparseTargetWitnessPiece, hx]
        field_simp
      · simp [sparseTargetWitnessPiece, hx]
    _ = ∫ x : Real in a..b, c - k * c * x := by
      rw [integral_indicator measurableSet_Ioc,
        Measure.restrict_restrict_of_subset hsubset,
        intervalIntegral.integral_of_le hab]
    _ = c * (b - a) - k * c * ((b ^ 2 - a ^ 2) / 2) := by
      have hc : IntervalIntegrable (fun _ : Real => c) volume a b :=
        intervalIntegrable_const
      have hlin : IntervalIntegrable (fun x : Real => k * c * x) volume a b :=
        (by fun_prop : Continuous (fun x : Real => k * c * x)).intervalIntegrable a b
      rw [intervalIntegral.integral_sub hc hlin,
        intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
        integral_id]
      simp [smul_eq_mul]
      ring

theorem integral_target_mul_sparseTargetWitnessPiece
    (a b c : Real) (ha : 0 < a) (hb : b <= 1) (hab : a <= b) :
    (∫ x : Real, baezDuarteTargetFunction x * sparseTargetWitnessPiece a b c x ∂
        (volume.restrict (Ioi (0 : Real)))) =
      c * ((b ^ 2 - a ^ 2) / 2) := by
  have hsubset : Ioc a b <= Ioi (0 : Real) := by
    intro x hx
    exact lt_trans ha hx.1
  calc
    (∫ x : Real, baezDuarteTargetFunction x * sparseTargetWitnessPiece a b c x ∂
        (volume.restrict (Ioi (0 : Real)))) =
        ∫ x : Real, (Ioc a b).indicator (fun x => c * x) x ∂
          (volume.restrict (Ioi (0 : Real))) := by
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ Ioc a b
      · have htarget : baezDuarteTargetFunction x = 1 := by
          simp [baezDuarteTargetFunction, lt_trans ha hx.1, hx.2.trans hb]
        simp [sparseTargetWitnessPiece, hx, htarget]
      · simp [sparseTargetWitnessPiece, hx]
    _ = ∫ x : Real in a..b, c * x := by
      rw [integral_indicator measurableSet_Ioc,
        Measure.restrict_restrict_of_subset hsubset,
        intervalIntegral.integral_of_le hab]
    _ = c * ((b ^ 2 - a ^ 2) / 2) := by
      rw [intervalIntegral.integral_const_mul, integral_id]

theorem fractionalPartKernel_one_eq_div_sub_nat
    (k : Nat) {x : Real}
    (hlower : (k : Real) <= 1 / x) (hupper : 1 / x < k + 1) :
    fractionalPartKernel 1 x = 1 / x - k := by
  rw [fractionalPartKernel]
  calc
    Int.fract (1 / x) = Int.fract (1 / x - ((k : Int) : Real)) :=
      (Int.fract_sub_intCast (1 / x) (k : Int)).symm
    _ = 1 / x - ((k : Int) : Real) := by
      apply Int.fract_eq_self.mpr
      norm_num
      have hlower' : (k : Real) <= x⁻¹ := by
        simpa [one_div] using hlower
      have hupper' : x⁻¹ < (k : Real) + 1 := by
        simpa [one_div] using hupper
      constructor <;> linarith
    _ = 1 / x - (k : Real) := by norm_num

theorem fractionalPartKernel_one_eq_on_sparseInterval_one
    {x : Real} (hx : x ∈ Ioc (1 / 2 : Real) (2 / 3)) :
    fractionalPartKernel 1 x = 1 / x - 1 := by
  have hx0 : 0 < x := by linarith [hx.1]
  simpa only [Nat.cast_one] using fractionalPartKernel_one_eq_div_sub_nat 1 (by
    apply (le_div_iff₀ hx0).2
    norm_num at hx ⊢
    nlinarith [hx.2]) (by
    apply (div_lt_iff₀ hx0).2
    norm_num at hx ⊢
    nlinarith [hx.1])

theorem one_eq_neg_fractionalPartKernel_add_div_on_sparseInterval_one
    {x : Real} (hx : x ∈ Ioc (1 / 2 : Real) (2 / 3)) :
    (1 : Real) = -fractionalPartKernel 1 x + 1 / x := by
  rw [fractionalPartKernel_one_eq_on_sparseInterval_one hx]
  ring

theorem fractionalPartKernel_one_eq_on_sparseInterval_two
    {x : Real} (hx : x ∈ Ioc (1 / 3 : Real) (2 / 5)) :
    fractionalPartKernel 1 x = 1 / x - 2 := by
  have hx0 : 0 < x := by linarith [hx.1]
  apply fractionalPartKernel_one_eq_div_sub_nat 2
  · apply (le_div_iff₀ hx0).2
    norm_num at hx ⊢
    nlinarith [hx.2]
  · apply (div_lt_iff₀ hx0).2
    norm_num at hx ⊢
    nlinarith [hx.1]

theorem fractionalPartKernel_one_eq_on_sparseInterval_three
    {x : Real} (hx : x ∈ Ioc (1 / 4 : Real) (2 / 7)) :
    fractionalPartKernel 1 x = 1 / x - 3 := by
  have hx0 : 0 < x := by linarith [hx.1]
  apply fractionalPartKernel_one_eq_div_sub_nat 3
  · apply (le_div_iff₀ hx0).2
    norm_num at hx ⊢
    nlinarith [hx.2]
  · apply (div_lt_iff₀ hx0).2
    norm_num at hx ⊢
    nlinarith [hx.1]

theorem sparseTarget_two_piece_moment_determinant :
    (1 / 6 : Real) * (11 / 225) - (1 / 15) * (7 / 72) = 1 / 600 := by
  norm_num

theorem sparseGramIndex_succ_gt_four (d : Nat) :
    4 < (sparseGramIndex (d + 1) : Nat) := by
  have hpow : 1 <= sparseGramBase ^ d := one_le_pow₀ (by
    norm_num [sparseGramBase])
  have hbase : 4 < sparseGramBase := by norm_num [sparseGramBase]
  have hmul : sparseGramBase <= sparseGramBase * sparseGramBase ^ d := by
    simpa using Nat.mul_le_mul_left sparseGramBase hpow
  simpa [sparseGramIndex, pow_succ, mul_comm] using hbase.trans_le hmul

theorem fractionalPartKernel_sparseGramIndex_succ_eq_div
    (d : Nat) {x : Real} (hx : (1 : Real) / 4 < x) :
    fractionalPartKernel
        ((((sparseGramIndex (d + 1) : Nat) : Real))⁻¹) x =
      (((sparseGramIndex (d + 1) : Nat) : Real))⁻¹ / x := by
  let N : Real := ((sparseGramIndex (d + 1) : Nat) : Real)
  have hN4 : 4 < N := by
    dsimp [N]
    exact_mod_cast sparseGramIndex_succ_gt_four d
  have hN0 : 0 < N := lt_trans (by norm_num) hN4
  have hx0 : 0 < x := lt_trans (by norm_num) hx
  rw [fractionalPartKernel, Int.fract_eq_self.mpr]
  constructor
  · exact div_nonneg (inv_nonneg.mpr hN0.le) hx0.le
  · apply (div_lt_one hx0).2
    have hinv : N⁻¹ < (1 : Real) / 4 := by
      simpa [one_div] using
        one_div_lt_one_div_of_lt (by norm_num : (0 : Real) < 4) hN4
    exact hinv.trans hx

theorem inner_baezDuarteKernelL2_sparseTargetWitnessRealL2_eq_zero
    (j : Nat) :
    ⟪baezDuarteKernelL2 (sparseGramIndex j), sparseTargetWitnessRealL2⟫_Real = 0 := by
  cases j with
  | zero =>
      simp only [sparseTargetWitnessRealL2, inner_add_right]
      rw [inner_baezDuarteKernelL2_sparseTargetWitnessPiece_eq_integral,
        inner_baezDuarteKernelL2_sparseTargetWitnessPiece_eq_integral,
        inner_baezDuarteKernelL2_sparseTargetWitnessPiece_eq_integral]
      simp only [sparseGramIndex, pow_zero, Nat.cast_one, inv_one]
      rw [integral_mul_sparseTargetWitnessPiece_of_eq_div_sub
          (fractionalPartKernel 1) 1 (1 / 2) (2 / 3) 118 (by norm_num) (by norm_num)
          (fun x hx => fractionalPartKernel_one_eq_on_sparseInterval_one hx),
        integral_mul_sparseTargetWitnessPiece_of_eq_div_sub
          (fractionalPartKernel 1) 2 (1 / 3) (2 / 5) (-925) (by norm_num) (by norm_num)
          (fun x hx => fractionalPartKernel_one_eq_on_sparseInterval_two hx),
        integral_mul_sparseTargetWitnessPiece_of_eq_div_sub
          (fractionalPartKernel 1) 3 (1 / 4) (2 / 7) 1176 (by norm_num) (by norm_num)
          (fun x hx => fractionalPartKernel_one_eq_on_sparseInterval_three hx)]
      norm_num
  | succ d =>
      simp only [sparseTargetWitnessRealL2, inner_add_right]
      rw [inner_baezDuarteKernelL2_sparseTargetWitnessPiece_eq_integral,
        inner_baezDuarteKernelL2_sparseTargetWitnessPiece_eq_integral,
        inner_baezDuarteKernelL2_sparseTargetWitnessPiece_eq_integral]
      let r : Real := (((sparseGramIndex (d + 1) : Nat) : Real))⁻¹
      rw [integral_mul_sparseTargetWitnessPiece_of_eq_div
          (fractionalPartKernel r) r (1 / 2) (2 / 3) 118 (by norm_num) (by norm_num)
          (fun x hx => fractionalPartKernel_sparseGramIndex_succ_eq_div d (by
            nlinarith [hx.1])),
        integral_mul_sparseTargetWitnessPiece_of_eq_div
          (fractionalPartKernel r) r (1 / 3) (2 / 5) (-925) (by norm_num) (by norm_num)
          (fun x hx => fractionalPartKernel_sparseGramIndex_succ_eq_div d (by
            nlinarith [hx.1])),
        integral_mul_sparseTargetWitnessPiece_of_eq_div
          (fractionalPartKernel r) r (1 / 4) (2 / 7) 1176 (by norm_num) (by norm_num)
          (fun x hx => fractionalPartKernel_sparseGramIndex_succ_eq_div d hx.1)]
      ring

theorem inner_baezDuarteTargetL2_sparseTargetWitnessRealL2 :
    ⟪baezDuarteTargetL2, sparseTargetWitnessRealL2⟫_Real = 1 / 9 := by
  simp only [sparseTargetWitnessRealL2, inner_add_right]
  rw [inner_baezDuarteTargetL2_sparseTargetWitnessPiece_eq_integral,
    inner_baezDuarteTargetL2_sparseTargetWitnessPiece_eq_integral,
    inner_baezDuarteTargetL2_sparseTargetWitnessPiece_eq_integral,
    integral_target_mul_sparseTargetWitnessPiece (1 / 2) (2 / 3) 118
      (by norm_num) (by norm_num) (by norm_num),
    integral_target_mul_sparseTargetWitnessPiece (1 / 3) (2 / 5) (-925)
      (by norm_num) (by norm_num) (by norm_num),
    integral_target_mul_sparseTargetWitnessPiece (1 / 4) (2 / 7) 1176
      (by norm_num) (by norm_num) (by norm_num)]
  norm_num

theorem inner_baezDuarteOfRealLp_eq_ofReal_inner
    (f g : positiveHalfLineL2) :
    ⟪baezDuarteOfRealLp f, baezDuarteOfRealLp g⟫_Complex =
      (⟪f, g⟫_Real : Complex) := by
  rw [L2.inner_def, L2.inner_def, <- integral_complex_ofReal]
  refine integral_congr_ae ?_
  filter_upwards [baezDuarteOfRealLp_coeFn f,
    baezDuarteOfRealLp_coeFn g] with x hf hg
  simp [hf, hg, RCLike.inner_apply, mul_comm]

theorem inner_sparseGramKernel_sparseTargetWitness_eq_zero (j : Nat) :
    ⟪baezDuarteNormalizedComplexKernelL2 (sparseGramIndex j),
        sparseTargetWitnessL2⟫_Complex = 0 := by
  rw [baezDuarteNormalizedComplexKernelL2, sparseTargetWitnessL2,
    inner_smul_left, baezDuarteComplexKernelL2,
    inner_baezDuarteOfRealLp_eq_ofReal_inner,
    inner_baezDuarteKernelL2_sparseTargetWitnessRealL2_eq_zero]
  simp

theorem inner_target_sparseTargetWitness :
    ⟪baezDuarteComplexTargetL2, sparseTargetWitnessL2⟫_Complex =
      (1 / 9 : Complex) := by
  rw [baezDuarteComplexTargetL2, sparseTargetWitnessL2,
    inner_baezDuarteOfRealLp_eq_ofReal_inner,
    inner_baezDuarteTargetL2_sparseTargetWitnessRealL2]
  norm_num

/-- The complex span of the normalized sparse kernel family. -/
def sparseGramKernelSpan : Submodule Complex positiveHalfLineComplexL2 :=
  Submodule.span Complex
    (Set.range fun j : Nat =>
      baezDuarteNormalizedComplexKernelL2 (sparseGramIndex j))

/-- The closed span ruled out as an exact target-coupling mechanism. -/
def sparseGramKernelClosure : Submodule Complex positiveHalfLineComplexL2 :=
  sparseGramKernelSpan.topologicalClosure

theorem sparseTargetWitnessL2_mem_sparseGramKernelSpan_orthogonal :
    sparseTargetWitnessL2 ∈ sparseGramKernelSpanᗮ := by
  rw [Submodule.mem_orthogonal]
  intro u hu
  refine Submodule.span_induction
    (p := fun u _ => ⟪u, sparseTargetWitnessL2⟫_Complex = 0)
    ?gen ?zero ?add ?smul hu
  · rintro _ ⟨j, rfl⟩
    exact inner_sparseGramKernel_sparseTargetWitness_eq_zero j
  · simp
  · intro x y hx hy hx0 hy0
    simp [inner_add_left, hx0, hy0]
  · intro c x hx hx0
    simp [inner_smul_left, hx0]

theorem sparseTargetWitnessL2_mem_sparseGramKernelClosure_orthogonal :
    sparseTargetWitnessL2 ∈ sparseGramKernelClosureᗮ := by
  simpa [sparseGramKernelClosure, Submodule.orthogonal_closure] using
    sparseTargetWitnessL2_mem_sparseGramKernelSpan_orthogonal

/-- The exact Baez-Duarte target is not in the closed span of the `(2^24)^j` subfamily. -/
theorem baezDuarteComplexTargetL2_not_mem_sparseGramKernelClosure :
    baezDuarteComplexTargetL2 ∉ sparseGramKernelClosure := by
  intro htarget
  have hzero :
      ⟪baezDuarteComplexTargetL2, sparseTargetWitnessL2⟫_Complex = 0 :=
    Submodule.inner_right_of_mem_orthogonal htarget
      sparseTargetWitnessL2_mem_sparseGramKernelClosure_orthogonal
  rw [inner_target_sparseTargetWitness] at hzero
  norm_num at hzero

end LeanLab.Riemann
