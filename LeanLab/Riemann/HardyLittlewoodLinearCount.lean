import LeanLab.Riemann.SelbergLocalSignChange
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Hardy--Littlewood's exceptional-set count bridge

This module formalizes the deterministic and measure-theoretic inference in sections 2.8--2.9
of Hardy--Littlewood (1921). Two second-moment estimates make a bad set small; every interval
pair not wholly charged to that bad set supplies a distinct critical-line zero.

The source-specific second-moment estimates and the construction of Hardy's normalized real
coordinate remain explicit hypotheses. No unconditional linear zero count is asserted.
-/

open Complex MeasureTheory Set

namespace LeanLab.Riemann

noncomputable section

/-- The integral of a real coordinate over a moving interval of length `H`. -/
def hardyLittlewoodWindowIntegral (X : ℝ → ℝ) (H t : ℝ) : ℝ :=
  ∫ u in t..t + H, X u

/-- The integral of the absolute value over a moving interval of length `H`. -/
def hardyLittlewoodAbsWindowIntegral (X : ℝ → ℝ) (H t : ℝ) : ℝ :=
  ∫ u in t..t + H, |X u|

theorem hardyLittlewoodWindowIntegral_intervalIntegrable
    {X : ℝ → ℝ} (hX : Continuous X) (a b : ℝ) :
    IntervalIntegrable X volume a b :=
  hX.intervalIntegrable a b

theorem continuous_hardyLittlewoodWindowIntegral
    {X : ℝ → ℝ} (hX : Continuous X) (H : ℝ) :
    Continuous (hardyLittlewoodWindowIntegral X H) := by
  let primitive : ℝ → ℝ := fun t => ∫ u in 0..t, X u
  have hprimitive : Continuous primitive :=
    intervalIntegral.continuous_primitive
      (μ := volume) (fun a b => hX.intervalIntegrable a b) 0
  have hwindow :
      hardyLittlewoodWindowIntegral X H =
        fun t => primitive (t + H) - primitive t := by
    funext t
    have hadd :=
      intervalIntegral.integral_add_adjacent_intervals
        (μ := volume) (hX.intervalIntegrable 0 t)
        (hX.intervalIntegrable t (t + H))
    simp only [hardyLittlewoodWindowIntegral, primitive]
    linarith
  rw [hwindow]
  exact (hprimitive.comp (continuous_id.add continuous_const)).sub hprimitive

theorem continuous_hardyLittlewoodAbsWindowIntegral
    {X : ℝ → ℝ} (hX : Continuous X) (H : ℝ) :
    Continuous (hardyLittlewoodAbsWindowIntegral X H) := by
  change Continuous (hardyLittlewoodWindowIntegral (fun t => |X t|) H)
  exact continuous_hardyLittlewoodWindowIntegral hX.abs H

/-- The Hardy--Littlewood error-term exceptional set. -/
def hardyLittlewoodErrorBadSet (psi : ℝ → ℝ) (threshold : ℝ) : Set ℝ :=
  {t | threshold < |psi t|}

/-- The Hardy--Littlewood moving-integral exceptional set. -/
def hardyLittlewoodWindowBadSet (X : ℝ → ℝ) (H threshold : ℝ) : Set ℝ :=
  {t | threshold ≤ |hardyLittlewoodWindowIntegral X H t|}

/-- The union of the two exceptional sets. -/
def hardyLittlewoodBadSet
    (X psi : ℝ → ℝ) (H threshold : ℝ) : Set ℝ :=
  hardyLittlewoodErrorBadSet psi threshold ∪
    hardyLittlewoodWindowBadSet X H threshold

theorem measurableSet_hardyLittlewoodErrorBadSet
    {psi : ℝ → ℝ} (hpsi : Measurable psi) (threshold : ℝ) :
    MeasurableSet (hardyLittlewoodErrorBadSet psi threshold) := by
  exact measurableSet_lt measurable_const hpsi.abs

theorem measurableSet_hardyLittlewoodWindowBadSet
    {X : ℝ → ℝ} (hX : Continuous X) (H threshold : ℝ) :
    MeasurableSet (hardyLittlewoodWindowBadSet X H threshold) := by
  exact measurableSet_le measurable_const
    (continuous_hardyLittlewoodWindowIntegral hX H).measurable.abs

theorem measurableSet_hardyLittlewoodBadSet
    {X psi : ℝ → ℝ} (hX : Continuous X) (hpsi : Measurable psi)
    (H threshold : ℝ) :
    MeasurableSet (hardyLittlewoodBadSet X psi H threshold) :=
  (measurableSet_hardyLittlewoodErrorBadSet hpsi threshold).union
    (measurableSet_hardyLittlewoodWindowBadSet hX H threshold)

/-- Denominator-free Chebyshev bound for a strict square threshold. -/
theorem hardyLittlewood_markov_square_strict
    {alpha : Type*} [MeasurableSpace alpha] {mu : Measure alpha}
    {f : alpha → ℝ} (hf : Measurable f) {threshold : ℝ}
    (hthreshold : 0 ≤ threshold) {moment : ENNReal}
    (hmoment :
      (∫⁻ x, ENNReal.ofReal (|f x| ^ 2) ∂mu) ≤ moment) :
    ENNReal.ofReal (threshold ^ 2) *
        mu {x | threshold < |f x|} ≤ moment := by
  have hmeas :
      Measurable (fun x => ENNReal.ofReal (|f x| ^ 2)) :=
    (hf.abs.pow_const 2).ennreal_ofReal
  have hsubset :
      {x | threshold < |f x|} ⊆
        {x | ENNReal.ofReal (threshold ^ 2) ≤
          ENNReal.ofReal (|f x| ^ 2)} := by
    intro x hx
    apply ENNReal.ofReal_le_ofReal
    exact (sq_le_sq₀ hthreshold (abs_nonneg (f x))).mpr hx.le
  calc
    ENNReal.ofReal (threshold ^ 2) *
          mu {x | threshold < |f x|} ≤
        ENNReal.ofReal (threshold ^ 2) *
          mu {x | ENNReal.ofReal (threshold ^ 2) ≤
            ENNReal.ofReal (|f x| ^ 2)} :=
      by
        gcongr
    _ ≤ ∫⁻ x, ENNReal.ofReal (|f x| ^ 2) ∂mu :=
      mul_meas_ge_le_lintegral hmeas _
    _ ≤ moment := hmoment

/-- Denominator-free Chebyshev bound for a non-strict square threshold. -/
theorem hardyLittlewood_markov_square
    {alpha : Type*} [MeasurableSpace alpha] {mu : Measure alpha}
    {f : alpha → ℝ} (hf : Measurable f) {threshold : ℝ}
    (hthreshold : 0 ≤ threshold) {moment : ENNReal}
    (hmoment :
      (∫⁻ x, ENNReal.ofReal (|f x| ^ 2) ∂mu) ≤ moment) :
    ENNReal.ofReal (threshold ^ 2) *
        mu {x | threshold ≤ |f x|} ≤ moment := by
  have hmeas :
      Measurable (fun x => ENNReal.ofReal (|f x| ^ 2)) :=
    (hf.abs.pow_const 2).ennreal_ofReal
  have hsubset :
      {x | threshold ≤ |f x|} ⊆
        {x | ENNReal.ofReal (threshold ^ 2) ≤
          ENNReal.ofReal (|f x| ^ 2)} := by
    intro x hx
    apply ENNReal.ofReal_le_ofReal
    exact (sq_le_sq₀ hthreshold (abs_nonneg (f x))).mpr hx
  calc
    ENNReal.ofReal (threshold ^ 2) *
          mu {x | threshold ≤ |f x|} ≤
        ENNReal.ofReal (threshold ^ 2) *
          mu {x | ENNReal.ofReal (threshold ^ 2) ≤
            ENNReal.ofReal (|f x| ^ 2)} :=
      by
        gcongr
    _ ≤ ∫⁻ x, ENNReal.ofReal (|f x| ^ 2) ∂mu :=
      mul_meas_ge_le_lintegral hmeas _
    _ ≤ moment := hmoment

/-- The source's two moment estimates give its two exact denominator-free bad-set bounds. -/
theorem hardyLittlewood_two_badSet_bounds
    {X psi : ℝ → ℝ} (hX : Continuous X) (hpsi : Measurable psi)
    {mu : Measure ℝ} {A H B C T : ℝ}
    (hthreshold : 0 ≤ A * H / 2)
    (hpsiMoment :
      (∫⁻ t, ENNReal.ofReal (|psi t| ^ 2) ∂mu) ≤
        ENNReal.ofReal (B * T))
    (hwindowMoment :
      (∫⁻ t, ENNReal.ofReal
        (|hardyLittlewoodWindowIntegral X H t| ^ 2) ∂mu) ≤
          ENNReal.ofReal (C * H * T)) :
    ENNReal.ofReal ((A * H / 2) ^ 2) *
        mu (hardyLittlewoodErrorBadSet psi (A * H / 2)) ≤
          ENNReal.ofReal (B * T) ∧
      ENNReal.ofReal ((A * H / 2) ^ 2) *
        mu (hardyLittlewoodWindowBadSet X H (A * H / 2)) ≤
          ENNReal.ofReal (C * H * T) := by
  constructor
  · exact hardyLittlewood_markov_square_strict hpsi hthreshold hpsiMoment
  · exact hardyLittlewood_markov_square
      (continuous_hardyLittlewoodWindowIntegral hX H).measurable
      hthreshold hwindowMoment

/-- The two source moment estimates combine into a bound for the union of the bad sets, without
dividing in `ℝ≥0∞`. -/
theorem hardyLittlewood_badSet_union_bound
    {X psi : ℝ → ℝ} (hX : Continuous X) (hpsi : Measurable psi)
    {mu : Measure ℝ} {A H B C T : ℝ}
    (hthreshold : 0 ≤ A * H / 2)
    (hpsiMoment :
      (∫⁻ t, ENNReal.ofReal (|psi t| ^ 2) ∂mu) ≤
        ENNReal.ofReal (B * T))
    (hwindowMoment :
      (∫⁻ t, ENNReal.ofReal
        (|hardyLittlewoodWindowIntegral X H t| ^ 2) ∂mu) ≤
          ENNReal.ofReal (C * H * T)) :
    ENNReal.ofReal ((A * H / 2) ^ 2) *
        mu (hardyLittlewoodBadSet X psi H (A * H / 2)) ≤
      ENNReal.ofReal (B * T) + ENNReal.ofReal (C * H * T) := by
  obtain ⟨herror, hwindow⟩ :=
    hardyLittlewood_two_badSet_bounds hX hpsi hthreshold
      hpsiMoment hwindowMoment
  have hunion :
      mu (hardyLittlewoodBadSet X psi H (A * H / 2)) ≤
        mu (hardyLittlewoodErrorBadSet psi (A * H / 2)) +
          mu (hardyLittlewoodWindowBadSet X H (A * H / 2)) := by
    simpa only [hardyLittlewoodBadSet] using
      (measure_union_le
        (μ := mu)
        (hardyLittlewoodErrorBadSet psi (A * H / 2))
        (hardyLittlewoodWindowBadSet X H (A * H / 2)))
  calc
    ENNReal.ofReal ((A * H / 2) ^ 2) *
          mu (hardyLittlewoodBadSet X psi H (A * H / 2)) ≤
        ENNReal.ofReal ((A * H / 2) ^ 2) *
          (mu (hardyLittlewoodErrorBadSet psi (A * H / 2)) +
            mu (hardyLittlewoodWindowBadSet X H (A * H / 2))) :=
      by
        gcongr
    _ =
        ENNReal.ofReal ((A * H / 2) ^ 2) *
            mu (hardyLittlewoodErrorBadSet psi (A * H / 2)) +
          ENNReal.ofReal ((A * H / 2) ^ 2) *
            mu (hardyLittlewoodWindowBadSet X H (A * H / 2)) := by
      rw [mul_add]
    _ ≤ ENNReal.ofReal (B * T) + ENNReal.ofReal (C * H * T) :=
      add_le_add herror hwindow

/-- Outside the union of the source's two bad sets, its lower estimate gives the strict
triangle gap needed for a sign change. -/
theorem hardyLittlewood_localIntegralGap_of_not_mem_badSet
    {X psi : ℝ → ℝ} {A H t : ℝ}
    (hH : 0 < H)
    (hlower :
      A * H - |psi t| ≤ hardyLittlewoodAbsWindowIntegral X H t)
    (ht :
      t ∉ hardyLittlewoodBadSet X psi H (A * H / 2)) :
    SelbergLocalIntegralGap X t (t + H) := by
  have htError :
      t ∉ hardyLittlewoodErrorBadSet psi (A * H / 2) :=
    fun h => ht (Or.inl h)
  have htWindow :
      t ∉ hardyLittlewoodWindowBadSet X H (A * H / 2) :=
    fun h => ht (Or.inr h)
  have hpsi : |psi t| ≤ A * H / 2 := by
    simpa only [hardyLittlewoodErrorBadSet, mem_setOf_eq, not_lt] using htError
  have hwindow :
      |hardyLittlewoodWindowIntegral X H t| < A * H / 2 := by
    simpa only [hardyLittlewoodWindowBadSet, mem_setOf_eq, not_le] using htWindow
  constructor
  · linarith
  · simpa only [hardyLittlewoodWindowIntegral,
      hardyLittlewoodAbsWindowIntegral] using
      hwindow.trans_le (hlower.trans' (by linarith))

/-- A continuous real coordinate whose zeros are exactly the actual critical-line zeta zeros. -/
structure HardyLittlewoodZeroCoordinate (X : ℝ → ℝ) : Prop where
  continuous : Continuous X
  zero_iff :
    ∀ t, X t = 0 ↔ IsNontrivialZero (hardyCriticalLinePoint t)

/-- A strict triangle gap for an exact zero coordinate gives an actual zeta zero in the open
window. -/
theorem exists_criticalLine_zero_of_hardyLittlewoodLocalGap
    {X : ℝ → ℝ} (hcoord : HardyLittlewoodZeroCoordinate X)
    {a b : ℝ} (hgap : SelbergLocalIntegralGap X a b) :
    ∃ t ∈ Ioo a b,
      IsNontrivialZero (hardyCriticalLinePoint t) ∧
        OnCriticalLine (hardyCriticalLinePoint t) := by
  obtain ⟨⟨u, hu, huneg⟩, ⟨v, hv, hvpos⟩⟩ :=
    exists_neg_and_pos_of_localIntegralGap
      hcoord.continuous.continuousOn hgap
  by_cases huv : u ≤ v
  · have hzeroMem : (0 : ℝ) ∈ Ioo (X u) (X v) :=
      ⟨huneg, hvpos⟩
    obtain ⟨t, ht, hzero⟩ :=
      intermediate_value_Ioo huv hcoord.continuous.continuousOn hzeroMem
    have htab : t ∈ Ioo a b :=
      ⟨hu.1.trans_lt ht.1, ht.2.trans_le hv.2⟩
    exact ⟨t, htab, (hcoord.zero_iff t).mp hzero,
      onCriticalLine_hardyCriticalLinePoint t⟩
  · have hvu : v ≤ u := le_of_not_ge huv
    have hzeroMem : (0 : ℝ) ∈ Ioo (X u) (X v) :=
      ⟨huneg, hvpos⟩
    obtain ⟨t, ht, hzero⟩ :=
      intermediate_value_Ioo' hvu hcoord.continuous.continuousOn hzeroMem
    have htab : t ∈ Ioo a b :=
      ⟨hv.1.trans_lt ht.1, ht.2.trans_le hu.2⟩
    exact ⟨t, htab, (hcoord.zero_iff t).mp hzero,
      onCriticalLine_hardyCriticalLinePoint t⟩

/-- Left endpoint of the `i`-th adjacent interval pair. -/
def hardyLittlewoodPairLeft {n : ℕ} (base H : ℝ) (i : Fin n) : ℝ :=
  base + 2 * (i.1 : ℝ) * H

/-- The first length-`H` interval in the `i`-th pair. -/
def hardyLittlewoodFirstBlock {n : ℕ} (base H : ℝ) (i : Fin n) : Set ℝ :=
  Ico (hardyLittlewoodPairLeft base H i)
    (hardyLittlewoodPairLeft base H i + H)

/-- The open length-`2H` block containing the `i`-th adjacent pair. -/
def hardyLittlewoodPairBlock {n : ℕ} (base H : ℝ) (i : Fin n) : Set ℝ :=
  Ioo (hardyLittlewoodPairLeft base H i)
    (hardyLittlewoodPairLeft base H i + 2 * H)

theorem measurableSet_hardyLittlewoodFirstBlock
    {n : ℕ} (base H : ℝ) (i : Fin n) :
    MeasurableSet (hardyLittlewoodFirstBlock base H i) :=
  measurableSet_Ico

theorem hardyLittlewoodFirstBlock_volume
    {n : ℕ} (base : ℝ) {H : ℝ} (_hH : 0 ≤ H) (i : Fin n) :
    volume (hardyLittlewoodFirstBlock base H i) =
      ENNReal.ofReal H := by
  rw [hardyLittlewoodFirstBlock, Real.volume_Ico]
  congr 1
  ring

theorem hardyLittlewoodFirstBlocks_pairwiseDisjoint
    {n : ℕ} (base : ℝ) {H : ℝ} (hH : 0 ≤ H) :
    Set.univ.PairwiseDisjoint
      (hardyLittlewoodFirstBlock (n := n) base H) := by
  intro i _ j _ hij
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · apply Set.disjoint_left.2
    intro x hxi hxj
    have hnat : i.1 + 1 ≤ j.1 := Nat.succ_le_iff.mpr hijlt
    have hcast : (i.1 : ℝ) + 1 ≤ (j.1 : ℝ) := by
      exact_mod_cast hnat
    have hright :
        hardyLittlewoodPairLeft base H i + H ≤
          hardyLittlewoodPairLeft base H j := by
      simp only [hardyLittlewoodPairLeft]
      nlinarith
    exact (not_lt_of_ge (hright.trans hxj.1)) hxi.2
  · apply Set.disjoint_left.2
    intro x hxi hxj
    have hnat : j.1 + 1 ≤ i.1 := Nat.succ_le_iff.mpr hjilt
    have hcast : (j.1 : ℝ) + 1 ≤ (i.1 : ℝ) := by
      exact_mod_cast hnat
    have hright :
        hardyLittlewoodPairLeft base H j + H ≤
          hardyLittlewoodPairLeft base H i := by
      simp only [hardyLittlewoodPairLeft]
      nlinarith
    exact (not_lt_of_ge (hright.trans hxi.1)) hxj.2

theorem hardyLittlewoodPairBlocks_pairwiseDisjoint
    {n : ℕ} (base : ℝ) {H : ℝ} (hH : 0 ≤ H) :
    Set.univ.PairwiseDisjoint
      (hardyLittlewoodPairBlock (n := n) base H) := by
  intro i _ j _ hij
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · apply Set.disjoint_left.2
    intro x hxi hxj
    have hnat : i.1 + 1 ≤ j.1 := Nat.succ_le_iff.mpr hijlt
    have hcast : (i.1 : ℝ) + 1 ≤ (j.1 : ℝ) := by
      exact_mod_cast hnat
    have hright :
        hardyLittlewoodPairLeft base H i + 2 * H ≤
          hardyLittlewoodPairLeft base H j := by
      simp only [hardyLittlewoodPairLeft]
      nlinarith
    exact (lt_asymm hxi.2 (hright.trans_lt hxj.1))
  · apply Set.disjoint_left.2
    intro x hxi hxj
    have hnat : j.1 + 1 ≤ i.1 := Nat.succ_le_iff.mpr hjilt
    have hcast : (j.1 : ℝ) + 1 ≤ (i.1 : ℝ) := by
      exact_mod_cast hnat
    have hright :
        hardyLittlewoodPairLeft base H j + 2 * H ≤
          hardyLittlewoodPairLeft base H i := by
      simp only [hardyLittlewoodPairLeft]
      nlinarith
    exact (lt_asymm hxj.2 (hright.trans_lt hxi.1))

/-- If all `n` adjacent pairs fit between `T` and `2T`, every first block lies in that source
range. -/
theorem hardyLittlewoodFirstBlock_subset_sourceRange
    {n : ℕ} {T H : ℝ} (hH : 0 ≤ H)
    (hfit : 2 * (n : ℝ) * H ≤ T) (i : Fin n) :
    hardyLittlewoodFirstBlock T H i ⊆ Icc T (2 * T) := by
  intro x hx
  have hiNonneg : (0 : ℝ) ≤ (i.1 : ℝ) := by positivity
  have hin : i.1 + 1 ≤ n := Nat.succ_le_iff.mpr i.2
  have hinCast : (i.1 : ℝ) + 1 ≤ (n : ℝ) := by
    exact_mod_cast hin
  have hleft :
      T ≤ hardyLittlewoodPairLeft T H i := by
    simp only [hardyLittlewoodPairLeft]
    nlinarith
  have hright :
      hardyLittlewoodPairLeft T H i + H ≤ 2 * T := by
    simp only [hardyLittlewoodPairLeft]
    nlinarith
  exact ⟨hleft.trans hx.1, hx.2.le.trans hright⟩

/-- On a first block contained in `[T,2T]`, restriction to the source range preserves its exact
Lebesgue measure `H`. -/
theorem hardyLittlewoodFirstBlock_restrict_sourceRange
    {n : ℕ} {T H : ℝ} (hH : 0 ≤ H)
    (hfit : 2 * (n : ℝ) * H ≤ T) (i : Fin n) :
    (volume.restrict (Icc T (2 * T)))
        (hardyLittlewoodFirstBlock T H i) =
      ENNReal.ofReal H := by
  rw [Measure.restrict_apply
    (measurableSet_hardyLittlewoodFirstBlock T H i)]
  rw [inter_eq_self_of_subset_left
    (hardyLittlewoodFirstBlock_subset_sourceRange hH hfit i)]
  exact hardyLittlewoodFirstBlock_volume T hH i

/-- Indices whose whole first block is charged to the bad set. -/
noncomputable def hardyLittlewoodFailedIndices
    {n : ℕ} (base H : ℝ) (bad : Set ℝ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter
    (fun i => hardyLittlewoodFirstBlock base H i ⊆ bad)

/-- Indices whose first block contains a start outside the bad set. -/
noncomputable def hardyLittlewoodGoodIndices
    {n : ℕ} (base H : ℝ) (bad : Set ℝ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter
    (fun i => ¬ hardyLittlewoodFirstBlock base H i ⊆ bad)

@[simp] theorem mem_hardyLittlewoodFailedIndices
    {n : ℕ} {base H : ℝ} {bad : Set ℝ} {i : Fin n} :
    i ∈ hardyLittlewoodFailedIndices base H bad ↔
      hardyLittlewoodFirstBlock base H i ⊆ bad := by
  classical
  simp [hardyLittlewoodFailedIndices]

@[simp] theorem mem_hardyLittlewoodGoodIndices
    {n : ℕ} {base H : ℝ} {bad : Set ℝ} {i : Fin n} :
    i ∈ hardyLittlewoodGoodIndices base H bad ↔
      ¬ hardyLittlewoodFirstBlock base H i ⊆ bad := by
  classical
  simp [hardyLittlewoodGoodIndices]

theorem hardyLittlewood_failed_card_add_good_card
    {n : ℕ} (base H : ℝ) (bad : Set ℝ) :
    (hardyLittlewoodFailedIndices (n := n) base H bad).card +
        (hardyLittlewoodGoodIndices (n := n) base H bad).card = n := by
  classical
  simpa [hardyLittlewoodFailedIndices, hardyLittlewoodGoodIndices] using
    (Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n)))
      (p := fun i => hardyLittlewoodFirstBlock base H i ⊆ bad))

/-- Every failed pair charges one disjoint first block to the exceptional set. -/
theorem hardyLittlewood_failed_card_mul_le_measure
    {n : ℕ} {mu : Measure ℝ} (base H : ℝ) (bad : Set ℝ)
    (hdisjoint :
      Set.univ.PairwiseDisjoint
        (hardyLittlewoodFirstBlock (n := n) base H))
    (hblock :
      ∀ i : Fin n, mu (hardyLittlewoodFirstBlock base H i) =
        ENNReal.ofReal H) :
    ((hardyLittlewoodFailedIndices (n := n) base H bad).card : ENNReal) *
        ENNReal.ofReal H ≤ mu bad := by
  classical
  let failed := hardyLittlewoodFailedIndices (n := n) base H bad
  let charged : Set ℝ :=
    ⋃ i ∈ failed, hardyLittlewoodFirstBlock base H i
  have hcharged : charged ⊆ bad := by
    intro x hx
    simp only [charged, mem_iUnion] at hx
    obtain ⟨i, hi, hxi⟩ := hx
    exact (mem_hardyLittlewoodFailedIndices.mp hi) hxi
  have hd :
      PairwiseDisjoint (↑failed)
        (hardyLittlewoodFirstBlock (n := n) base H) := by
    intro i _ j _ hij
    exact hdisjoint (by simp) (by simp) hij
  have hm :
      mu charged =
        ∑ i ∈ failed, mu (hardyLittlewoodFirstBlock base H i) := by
    exact measure_biUnion_finset hd
      (fun i _ => measurableSet_hardyLittlewoodFirstBlock base H i)
  calc
    (failed.card : ENNReal) * ENNReal.ofReal H =
        ∑ i ∈ failed, mu (hardyLittlewoodFirstBlock base H i) := by
      simp [hblock, mul_comm]
    _ = mu charged := hm.symm
    _ ≤ mu bad := measure_mono hcharged

theorem hardyLittlewood_failed_card_le_of_measure_le
    {n b : ℕ} {mu : Measure ℝ} {base H : ℝ} {bad : Set ℝ}
    (hH : 0 < H)
    (hcharge :
      ((hardyLittlewoodFailedIndices (n := n) base H bad).card : ENNReal) *
          ENNReal.ofReal H ≤ mu bad)
    (hsmall : mu bad ≤ (b : ENNReal) * ENNReal.ofReal H) :
    (hardyLittlewoodFailedIndices (n := n) base H bad).card ≤ b := by
  have hmul :
      ((hardyLittlewoodFailedIndices (n := n) base H bad).card : ENNReal) *
          ENNReal.ofReal H ≤
        (b : ENNReal) * ENNReal.ofReal H :=
    hcharge.trans hsmall
  have hH0 : ENNReal.ofReal H ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hH
  have hHtop : ENNReal.ofReal H ≠ (⊤ : ENNReal) :=
    ENNReal.ofReal_ne_top
  have hcast :
      ((hardyLittlewoodFailedIndices (n := n) base H bad).card : ENNReal) ≤
        (b : ENNReal) :=
    (ENNReal.mul_le_mul_iff_left hH0 hHtop).mp hmul
  exact_mod_cast hcast

/-- A small exceptional-set measure gives a natural-number lower bound for good pairs. -/
theorem hardyLittlewood_good_card_lower_bound
    {n b : ℕ} {mu : Measure ℝ} {base H : ℝ} {bad : Set ℝ}
    (hbn : b ≤ n) (hH : 0 < H)
    (hcharge :
      ((hardyLittlewoodFailedIndices (n := n) base H bad).card : ENNReal) *
          ENNReal.ofReal H ≤ mu bad)
    (hsmall : mu bad ≤ (b : ENNReal) * ENNReal.ofReal H) :
    n - b ≤ (hardyLittlewoodGoodIndices (n := n) base H bad).card := by
  have hfailed :
      (hardyLittlewoodFailedIndices (n := n) base H bad).card ≤ b :=
    hardyLittlewood_failed_card_le_of_measure_le hH hcharge hsmall
  have hpartition :=
    hardyLittlewood_failed_card_add_good_card
      (n := n) base H bad
  omega

/-- Every good pair supplies one actual zeta zero, and disjoint pair blocks make the selected
ordinates injective. -/
theorem exists_injective_criticalLine_zeros_of_hardyLittlewoodGoodPairs
    {n : ℕ} {X psi : ℝ → ℝ}
    (hcoord : HardyLittlewoodZeroCoordinate X)
    {base A H : ℝ} (hH : 0 < H) {bad : Set ℝ}
    (hbad :
      bad = hardyLittlewoodBadSet X psi H (A * H / 2))
    (hlower :
      ∀ i : Fin n, ∀ t ∈ hardyLittlewoodFirstBlock base H i, t ∉ bad →
        A * H - |psi t| ≤ hardyLittlewoodAbsWindowIntegral X H t) :
    ∃ zeroOrdinate :
        {i : Fin n // i ∈ hardyLittlewoodGoodIndices base H bad} → ℝ,
      Function.Injective zeroOrdinate ∧
        ∀ i,
          zeroOrdinate i ∈ hardyLittlewoodPairBlock base H i.1 ∧
            IsNontrivialZero
              (hardyCriticalLinePoint (zeroOrdinate i)) ∧
              OnCriticalLine
                (hardyCriticalLinePoint (zeroOrdinate i)) := by
  have hexists :
      ∀ i : {i : Fin n // i ∈ hardyLittlewoodGoodIndices base H bad},
        ∃ z ∈ hardyLittlewoodPairBlock base H i.1,
          IsNontrivialZero (hardyCriticalLinePoint z) ∧
            OnCriticalLine (hardyCriticalLinePoint z) := by
    intro i
    have hnotSubset :
        ¬ hardyLittlewoodFirstBlock base H i.1 ⊆ bad :=
      mem_hardyLittlewoodGoodIndices.mp i.2
    rw [not_subset] at hnotSubset
    obtain ⟨t, htFirst, htBad⟩ := hnotSubset
    have hgap :
        SelbergLocalIntegralGap X t (t + H) := by
      apply hardyLittlewood_localIntegralGap_of_not_mem_badSet
        hH (hlower i.1 t htFirst htBad)
      simpa only [← hbad] using htBad
    obtain ⟨z, hz, hzero, honLine⟩ :=
      exists_criticalLine_zero_of_hardyLittlewoodLocalGap hcoord hgap
    have hzPair :
        z ∈ hardyLittlewoodPairBlock base H i.1 := by
      constructor
      · exact htFirst.1.trans_lt hz.1
      · have htUpper :
            t < hardyLittlewoodPairLeft base H i.1 + H :=
          htFirst.2
        change z <
          hardyLittlewoodPairLeft base H i.1 + 2 * H
        have hshift :
            t + H <
              hardyLittlewoodPairLeft base H i.1 + 2 * H := by
          linarith
        exact hz.2.trans hshift
    exact ⟨z, hzPair, hzero, honLine⟩
  choose zeroOrdinate hmem hzero honLine using hexists
  refine ⟨zeroOrdinate, ?_, fun i => ⟨hmem i, hzero i, honLine i⟩⟩
  intro i j hij
  by_contra hne
  have hvalNe : i.1 ≠ j.1 := by
    intro hval
    apply hne
    exact Subtype.ext hval
  have hdisjoint :=
    hardyLittlewoodPairBlocks_pairwiseDisjoint
      (n := n) base hH.le (by simp) (by simp) hvalNe
  have hjmem :
      zeroOrdinate i ∈ hardyLittlewoodPairBlock base H j.1 := by
    rw [hij]
    exact hmem j
  exact Set.disjoint_left.mp hdisjoint (hmem i) hjmem

/-- The finite source-shaped Hardy--Littlewood inference. The two moment estimates and the
absolute-integral lower estimate remain hypotheses; the conclusion is the exact natural count
and an injective family of actual critical-line zeros. -/
theorem hardyLittlewood_source_finite_count
    {n b : ℕ} {X psi : ℝ → ℝ}
    (hcoord : HardyLittlewoodZeroCoordinate X)
    (hpsi : Measurable psi)
    {A B C T H : ℝ} (hH : 0 < H)
    (hfit : 2 * (n : ℝ) * H ≤ T)
    (hbn : b ≤ n)
    (hthreshold : 0 < A * H / 2)
    (hpsiMoment :
      (∫⁻ t, ENNReal.ofReal (|psi t| ^ 2)
        ∂(volume.restrict (Icc T (2 * T)))) ≤
          ENNReal.ofReal (B * T))
    (hwindowMoment :
      (∫⁻ t, ENNReal.ofReal
        (|hardyLittlewoodWindowIntegral X H t| ^ 2)
          ∂(volume.restrict (Icc T (2 * T)))) ≤
            ENNReal.ofReal (C * H * T))
    (hlower :
      ∀ t ∈ Icc T (2 * T),
        t ∉ hardyLittlewoodBadSet X psi H (A * H / 2) →
        A * H - |psi t| ≤ hardyLittlewoodAbsWindowIntegral X H t)
    (hbudget :
      ENNReal.ofReal (B * T) + ENNReal.ofReal (C * H * T) ≤
        ENNReal.ofReal ((A * H / 2) ^ 2) *
          ((b : ENNReal) * ENNReal.ofReal H)) :
    n - b ≤
        (hardyLittlewoodGoodIndices
          (n := n) T H
          (hardyLittlewoodBadSet X psi H (A * H / 2))).card ∧
      ∃ zeroOrdinate :
          {i : Fin n //
            i ∈ hardyLittlewoodGoodIndices T H
              (hardyLittlewoodBadSet X psi H (A * H / 2))} → ℝ,
        Function.Injective zeroOrdinate ∧
          ∀ i,
            zeroOrdinate i ∈ hardyLittlewoodPairBlock T H i.1 ∧
              IsNontrivialZero
                (hardyCriticalLinePoint (zeroOrdinate i)) ∧
                OnCriticalLine
                  (hardyCriticalLinePoint (zeroOrdinate i)) := by
  let mu : Measure ℝ := volume.restrict (Icc T (2 * T))
  let bad : Set ℝ :=
    hardyLittlewoodBadSet X psi H (A * H / 2)
  have hscaled :
      ENNReal.ofReal ((A * H / 2) ^ 2) * mu bad ≤
        ENNReal.ofReal (B * T) + ENNReal.ofReal (C * H * T) := by
    exact hardyLittlewood_badSet_union_bound
      hcoord.continuous hpsi hthreshold.le hpsiMoment hwindowMoment
  have hscaledSmall :
      ENNReal.ofReal ((A * H / 2) ^ 2) * mu bad ≤
        ENNReal.ofReal ((A * H / 2) ^ 2) *
          ((b : ENNReal) * ENNReal.ofReal H) :=
    hscaled.trans hbudget
  have hepsilonPos : 0 < (A * H / 2) ^ 2 :=
    sq_pos_of_pos hthreshold
  have hepsilon0 :
      ENNReal.ofReal ((A * H / 2) ^ 2) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hepsilonPos
  have hepsilonTop :
      ENNReal.ofReal ((A * H / 2) ^ 2) ≠ (⊤ : ENNReal) :=
    ENNReal.ofReal_ne_top
  have hsmall :
      mu bad ≤ (b : ENNReal) * ENNReal.ofReal H :=
    (ENNReal.mul_le_mul_iff_right hepsilon0 hepsilonTop).mp
      hscaledSmall
  have hcharge :
      ((hardyLittlewoodFailedIndices (n := n) T H bad).card :
          ENNReal) * ENNReal.ofReal H ≤ mu bad := by
    apply hardyLittlewood_failed_card_mul_le_measure T H bad
    · exact hardyLittlewoodFirstBlocks_pairwiseDisjoint T hH.le
    · intro i
      exact hardyLittlewoodFirstBlock_restrict_sourceRange
        hH.le hfit i
  have hcount :
      n - b ≤
        (hardyLittlewoodGoodIndices (n := n) T H bad).card :=
    hardyLittlewood_good_card_lower_bound
      hbn hH hcharge hsmall
  constructor
  · exact hcount
  · exact
      exists_injective_criticalLine_zeros_of_hardyLittlewoodGoodPairs
        hcoord hH rfl (fun i t htFirst htBad =>
          hlower t
            (hardyLittlewoodFirstBlock_subset_sourceRange
              hH.le hfit i htFirst)
            htBad)

/-- If at most half of `2m` first blocks can be charged, at least `m` disjoint pair blocks
supply actual critical-line zeros. -/
theorem hardyLittlewood_positiveHalf_corollary
    {m : ℕ} {mu : Measure ℝ} {X psi : ℝ → ℝ}
    (hcoord : HardyLittlewoodZeroCoordinate X)
    {base A H : ℝ} (hH : 0 < H) {bad : Set ℝ}
    (hbad :
      bad = hardyLittlewoodBadSet X psi H (A * H / 2))
    (hlower :
      ∀ i : Fin (2 * m),
        ∀ t ∈ hardyLittlewoodFirstBlock base H i, t ∉ bad →
        A * H - |psi t| ≤ hardyLittlewoodAbsWindowIntegral X H t)
    (hcharge :
      ((hardyLittlewoodFailedIndices (n := 2 * m) base H bad).card :
          ENNReal) * ENNReal.ofReal H ≤ mu bad)
    (hsmall : mu bad < (m : ENNReal) * ENNReal.ofReal H) :
    m ≤ (hardyLittlewoodGoodIndices
        (n := 2 * m) base H bad).card ∧
      ∃ zeroOrdinate :
          {i : Fin (2 * m) //
            i ∈ hardyLittlewoodGoodIndices base H bad} → ℝ,
        Function.Injective zeroOrdinate ∧
          ∀ i,
            zeroOrdinate i ∈ hardyLittlewoodPairBlock base H i.1 ∧
              IsNontrivialZero
                (hardyCriticalLinePoint (zeroOrdinate i)) ∧
                OnCriticalLine
                  (hardyCriticalLinePoint (zeroOrdinate i)) := by
  constructor
  · have hbound :=
      hardyLittlewood_good_card_lower_bound
        (n := 2 * m) (b := m) (mu := mu)
        (base := base) (H := H) (bad := bad)
        (by omega) hH hcharge hsmall.le
    omega
  · exact
      exists_injective_criticalLine_zeros_of_hardyLittlewoodGoodPairs
        hcoord hH hbad hlower

/-- The finite set of sampled left endpoints. -/
noncomputable def hardyLittlewoodEndpointSet
    {n : ℕ} (base H : ℝ) : Set ℝ :=
  ↑((Finset.univ : Finset (Fin n)).image
    (hardyLittlewoodPairLeft base H))

theorem hardyLittlewoodPairLeft_mem_endpointSet
    {n : ℕ} (base H : ℝ) (i : Fin n) :
    hardyLittlewoodPairLeft base H i ∈
      hardyLittlewoodEndpointSet (n := n) base H := by
  classical
  simp [hardyLittlewoodEndpointSet]

/-- Negative control: all sampled endpoints fit in a null set. -/
theorem hardyLittlewoodEndpointSet_volume_zero
    {n : ℕ} (base H : ℝ) :
    volume (hardyLittlewoodEndpointSet (n := n) base H) = 0 := by
  apply Set.Finite.measure_zero
  exact ((Finset.univ : Finset (Fin n)).image
    (hardyLittlewoodPairLeft base H)).finite_toSet

/-- The compiled deterministic endpoint of the Hardy--Littlewood linear-count campaign. -/
structure HardyLittlewoodLinearCountCertificate : Prop where
  windowContinuous :
    ∀ {X : ℝ → ℝ}, Continuous X → ∀ H,
      Continuous (hardyLittlewoodWindowIntegral X H)
  absWindowContinuous :
    ∀ {X : ℝ → ℝ}, Continuous X → ∀ H,
      Continuous (hardyLittlewoodAbsWindowIntegral X H)
  strictMarkov :
    ∀ {alpha : Type} [MeasurableSpace alpha] {mu : Measure alpha}
      {f : alpha → ℝ}, Measurable f → ∀ {threshold : ℝ},
      0 ≤ threshold → ∀ {moment : ENNReal},
      (∫⁻ x, ENNReal.ofReal (|f x| ^ 2) ∂mu) ≤ moment →
      ENNReal.ofReal (threshold ^ 2) *
        mu {x | threshold < |f x|} ≤ moment
  nonstrictMarkov :
    ∀ {alpha : Type} [MeasurableSpace alpha] {mu : Measure alpha}
      {f : alpha → ℝ}, Measurable f → ∀ {threshold : ℝ},
      0 ≤ threshold → ∀ {moment : ENNReal},
      (∫⁻ x, ENNReal.ofReal (|f x| ^ 2) ∂mu) ≤ moment →
      ENNReal.ofReal (threshold ^ 2) *
        mu {x | threshold ≤ |f x|} ≤ moment
  outsideBadSetGap :
    ∀ {X psi : ℝ → ℝ} {A H t : ℝ},
      A * H - |psi t| ≤ hardyLittlewoodAbsWindowIntegral X H t →
      0 < H →
      t ∉ hardyLittlewoodBadSet X psi H (A * H / 2) →
      SelbergLocalIntegralGap X t (t + H)
  failedPairCharge :
    ∀ {n : ℕ} {mu : Measure ℝ} (base H : ℝ) (bad : Set ℝ),
      Set.univ.PairwiseDisjoint
        (hardyLittlewoodFirstBlock (n := n) base H) →
      (∀ i : Fin n, mu (hardyLittlewoodFirstBlock base H i) =
        ENNReal.ofReal H) →
      ((hardyLittlewoodFailedIndices (n := n) base H bad).card : ENNReal) *
        ENNReal.ofReal H ≤ mu bad
  goodPairCount :
    ∀ {n b : ℕ} {mu : Measure ℝ} {base H : ℝ} {bad : Set ℝ},
      b ≤ n → 0 < H →
      ((hardyLittlewoodFailedIndices (n := n) base H bad).card :
          ENNReal) * ENNReal.ofReal H ≤ mu bad →
      mu bad ≤ (b : ENNReal) * ENNReal.ofReal H →
      n - b ≤ (hardyLittlewoodGoodIndices (n := n) base H bad).card
  exactZeroConsumer :
    ∀ {n : ℕ} {X psi : ℝ → ℝ},
      HardyLittlewoodZeroCoordinate X →
      ∀ {base A H : ℝ}, 0 < H → ∀ {bad : Set ℝ},
      bad = hardyLittlewoodBadSet X psi H (A * H / 2) →
      (∀ i : Fin n, ∀ t ∈ hardyLittlewoodFirstBlock base H i, t ∉ bad →
        A * H - |psi t| ≤ hardyLittlewoodAbsWindowIntegral X H t) →
      ∃ zeroOrdinate :
          {i : Fin n // i ∈ hardyLittlewoodGoodIndices base H bad} → ℝ,
        Function.Injective zeroOrdinate ∧
          ∀ i,
            zeroOrdinate i ∈ hardyLittlewoodPairBlock base H i.1 ∧
              IsNontrivialZero
                (hardyCriticalLinePoint (zeroOrdinate i)) ∧
                OnCriticalLine
                  (hardyCriticalLinePoint (zeroOrdinate i))
  sourceFiniteCount :
    ∀ {n b : ℕ} {X psi : ℝ → ℝ},
      HardyLittlewoodZeroCoordinate X →
      Measurable psi →
      ∀ {A B C T H : ℝ}, 0 < H →
      2 * (n : ℝ) * H ≤ T →
      b ≤ n →
      0 < A * H / 2 →
      (∫⁻ t, ENNReal.ofReal (|psi t| ^ 2)
        ∂(volume.restrict (Icc T (2 * T)))) ≤
          ENNReal.ofReal (B * T) →
      (∫⁻ t, ENNReal.ofReal
        (|hardyLittlewoodWindowIntegral X H t| ^ 2)
          ∂(volume.restrict (Icc T (2 * T)))) ≤
            ENNReal.ofReal (C * H * T) →
      (∀ t ∈ Icc T (2 * T),
        t ∉ hardyLittlewoodBadSet X psi H (A * H / 2) →
        A * H - |psi t| ≤ hardyLittlewoodAbsWindowIntegral X H t) →
      ENNReal.ofReal (B * T) + ENNReal.ofReal (C * H * T) ≤
        ENNReal.ofReal ((A * H / 2) ^ 2) *
          ((b : ENNReal) * ENNReal.ofReal H) →
      n - b ≤
          (hardyLittlewoodGoodIndices
            (n := n) T H
            (hardyLittlewoodBadSet X psi H (A * H / 2))).card ∧
        ∃ zeroOrdinate :
            {i : Fin n //
              i ∈ hardyLittlewoodGoodIndices T H
                (hardyLittlewoodBadSet X psi H (A * H / 2))} → ℝ,
          Function.Injective zeroOrdinate ∧
            ∀ i,
              zeroOrdinate i ∈ hardyLittlewoodPairBlock T H i.1 ∧
                IsNontrivialZero
                  (hardyCriticalLinePoint (zeroOrdinate i)) ∧
                  OnCriticalLine
                    (hardyCriticalLinePoint (zeroOrdinate i))
  endpointControl :
    ∀ {n : ℕ} (base H : ℝ),
      volume (hardyLittlewoodEndpointSet (n := n) base H) = 0 ∧
        ∀ i : Fin n,
          hardyLittlewoodPairLeft base H i ∈
            hardyLittlewoodEndpointSet (n := n) base H

theorem hardyLittlewoodLinearCount_endpoint :
    HardyLittlewoodLinearCountCertificate where
  windowContinuous := continuous_hardyLittlewoodWindowIntegral
  absWindowContinuous := continuous_hardyLittlewoodAbsWindowIntegral
  strictMarkov := hardyLittlewood_markov_square_strict
  nonstrictMarkov := hardyLittlewood_markov_square
  outsideBadSetGap := fun hlower hH ht =>
    hardyLittlewood_localIntegralGap_of_not_mem_badSet hH hlower ht
  failedPairCharge := hardyLittlewood_failed_card_mul_le_measure
  goodPairCount := hardyLittlewood_good_card_lower_bound
  exactZeroConsumer :=
    exists_injective_criticalLine_zeros_of_hardyLittlewoodGoodPairs
  sourceFiniteCount := hardyLittlewood_source_finite_count
  endpointControl := fun base H =>
    ⟨hardyLittlewoodEndpointSet_volume_zero base H,
      hardyLittlewoodPairLeft_mem_endpointSet base H⟩

end

end LeanLab.Riemann
