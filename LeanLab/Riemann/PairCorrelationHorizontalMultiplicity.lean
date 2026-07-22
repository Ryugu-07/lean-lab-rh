import LeanLab.Riemann.SpeiserCountingEquivalence

set_option linter.style.header false

/-!
# Pair correlation and horizontal multiplicity

This module reconstructs the finite combinatorial hinge in the horizontal-multiplicity form of
the pair-correlation route. The index type represents zeros with analytic multiplicity already
expanded: two indices may therefore have the same complex value.
-/

open Complex Filter Set
open scoped BigOperators ComplexConjugate Topology

namespace LeanLab.Riemann

noncomputable section

section FinitePopulation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Number of multiplicity copies on the horizontal line through `z i`. -/
def horizontalMultiplicity (z : ι → ℂ) (i : ι) : ℕ :=
  (Finset.univ.filter fun j ↦ (z j).im = (z i).im).card

/-- Ordered equal-ordinate pair count, including the diagonal. -/
def horizontalPairCount (z : ι → ℂ) : ℕ :=
  ∑ i, horizontalMultiplicity z i

/-- Number of multiplicity copies whose horizontal fiber is a singleton. -/
def horizontalSingletonCount (z : ι → ℂ) : ℕ :=
  ∑ i, if horizontalMultiplicity z i = 1 then 1 else 0

/-- Number of copies that are both on the critical line and alone on their horizontal fiber. -/
def simpleCriticalCount (z : ι → ℂ) : ℕ :=
  ∑ i, if horizontalMultiplicity z i = 1 ∧ (z i).re = 1 / 2 then 1 else 0

/-- Excess ordered equal-ordinate pairs over the unavoidable diagonal. -/
def horizontalExcess (z : ι → ℂ) : ℕ :=
  ∑ i, (horizontalMultiplicity z i - 1)

omit [DecidableEq ι] in
theorem horizontalMultiplicity_pos (z : ι → ℂ) (i : ι) :
    0 < horizontalMultiplicity z i := by
  classical
  rw [horizontalMultiplicity, Finset.card_pos]
  exact ⟨i, by simp⟩

omit [DecidableEq ι] in
theorem horizontalPairCount_eq_card_add_excess (z : ι → ℂ) :
    horizontalPairCount z = Fintype.card ι + horizontalExcess z := by
  classical
  rw [horizontalPairCount, horizontalExcess, Fintype.card_eq_sum_ones,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hpos := horizontalMultiplicity_pos z i
  omega

omit [DecidableEq ι] in
theorem horizontalMultiplicity_eq_one_of_pairCount_eq_card (z : ι → ℂ)
    (hcount : horizontalPairCount z = Fintype.card ι) (i : ι) :
    horizontalMultiplicity z i = 1 := by
  classical
  have hexcess : horizontalExcess z = 0 := by
    rw [horizontalPairCount_eq_card_add_excess] at hcount
    omega
  have hterm : horizontalMultiplicity z i - 1 = 0 := by
    have hle : horizontalMultiplicity z i - 1 ≤ horizontalExcess z := by
      rw [horizontalExcess]
      exact Finset.single_le_sum
        (s := Finset.univ) (f := fun j ↦ horizontalMultiplicity z j - 1)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    rw [hexcess] at hle
    exact Nat.eq_zero_of_le_zero hle
  have hpos := horizontalMultiplicity_pos z i
  omega

/-- A permutation realizing the same-height functional-equation reflection. -/
def IsCriticalReflection (z : ι → ℂ) (r : Equiv.Perm ι) : Prop :=
  ∀ i, z (r i) = 1 - conj (z i)

omit [Fintype ι] [DecidableEq ι] in
theorem criticalReflection_im_eq {z : ι → ℂ} {r : Equiv.Perm ι}
    (hreflect : IsCriticalReflection z r) (i : ι) :
    (z (r i)).im = (z i).im := by
  rw [hreflect i]
  simp

omit [DecidableEq ι] in
theorem criticalReflection_fixed_of_horizontalMultiplicity_eq_one
    {z : ι → ℂ} {r : Equiv.Perm ι} (hreflect : IsCriticalReflection z r) (i : ι)
    (hsingle : horizontalMultiplicity z i = 1) :
    r i = i := by
  classical
  let fiber := Finset.univ.filter fun j ↦ (z j).im = (z i).im
  have hcard : fiber.card = 1 := by
    simpa [fiber, horizontalMultiplicity] using hsingle
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
  have hi : i ∈ fiber := by simp [fiber]
  have hri : r i ∈ fiber := by
    simp [fiber, criticalReflection_im_eq hreflect i]
  have hi_eq : i = a := by simpa [ha] using hi
  have hri_eq : r i = a := by simpa [ha] using hri
  exact hri_eq.trans hi_eq.symm

omit [DecidableEq ι] in
theorem criticalReflection_re_eq_half_of_horizontalMultiplicity_eq_one
    {z : ι → ℂ} {r : Equiv.Perm ι} (hreflect : IsCriticalReflection z r) (i : ι)
    (hsingle : horizontalMultiplicity z i = 1) :
    (z i).re = 1 / 2 := by
  have hfixed := criticalReflection_fixed_of_horizontalMultiplicity_eq_one hreflect i hsingle
  have hvalue := hreflect i
  rw [hfixed] at hvalue
  have hre := congrArg Complex.re hvalue
  simp at hre
  linarith

omit [DecidableEq ι] in
theorem horizontalSingletonCount_eq_simpleCriticalCount
    {z : ι → ℂ} {r : Equiv.Perm ι} (hreflect : IsCriticalReflection z r) :
    horizontalSingletonCount z = simpleCriticalCount z := by
  classical
  unfold horizontalSingletonCount simpleCriticalCount
  apply Finset.sum_congr rfl
  intro i _
  by_cases hsingle : horizontalMultiplicity z i = 1
  · have hcritical :=
      criticalReflection_re_eq_half_of_horizontalMultiplicity_eq_one hreflect i hsingle
    simp [hsingle, hcritical]
  · simp [hsingle]

omit [DecidableEq ι] in
theorem two_mul_card_le_horizontalSingletonCount_add_horizontalPairCount (z : ι → ℂ) :
    2 * Fintype.card ι ≤ horizontalSingletonCount z + horizontalPairCount z := by
  classical
  have hpoint : ∀ i : ι,
      2 ≤ (if horizontalMultiplicity z i = 1 then 1 else 0) + horizontalMultiplicity z i := by
    intro i
    have hpos := horizontalMultiplicity_pos z i
    by_cases hsingle : horizontalMultiplicity z i = 1
    · simp [hsingle]
    · simp [hsingle]
      omega
  have hsum := Finset.sum_le_sum fun i (_hi : i ∈ Finset.univ) ↦ hpoint i
  calc
    2 * Fintype.card ι = ∑ _i : ι, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ i : ι, ((if horizontalMultiplicity z i = 1 then 1 else 0) +
        horizontalMultiplicity z i) := hsum
    _ = horizontalSingletonCount z + horizontalPairCount z := by
      rw [Finset.sum_add_distrib]
      rfl

omit [DecidableEq ι] in
/-- The finite combinatorial inequality used by the horizontal-multiplicity argument. -/
theorem two_mul_card_le_simpleCriticalCount_add_horizontalPairCount
    {z : ι → ℂ} {r : Equiv.Perm ι} (hreflect : IsCriticalReflection z r) :
    2 * Fintype.card ι ≤ simpleCriticalCount z + horizontalPairCount z := by
  rw [← horizontalSingletonCount_eq_simpleCriticalCount hreflect]
  exact two_mul_card_le_horizontalSingletonCount_add_horizontalPairCount z

omit [DecidableEq ι] in
/-- Exact absence of horizontal excess forces every multiplicity copy to be simple and critical. -/
theorem all_critical_of_horizontalPairCount_eq_card
    {z : ι → ℂ} {r : Equiv.Perm ι} (hreflect : IsCriticalReflection z r)
    (hcount : horizontalPairCount z = Fintype.card ι) (i : ι) :
    horizontalMultiplicity z i = 1 ∧ (z i).re = 1 / 2 := by
  have hsingle := horizontalMultiplicity_eq_one_of_pairCount_eq_card z hcount i
  exact ⟨hsingle,
    criticalReflection_re_eq_half_of_horizontalMultiplicity_eq_one hreflect i hsingle⟩

end FinitePopulation

section PersistentExceptionModel

/-- Two reflected off-line points together with `n` distinct simple critical points. -/
abbrev PccExceptionalIndex (n : ℕ) := Bool ⊕ Fin n

def pccExceptionalValue (n : ℕ) : PccExceptionalIndex n → ℂ
  | Sum.inl false => ⟨1 / 4, 1⟩
  | Sum.inl true => ⟨3 / 4, 1⟩
  | Sum.inr k => ⟨1 / 2, (k : ℕ) + 2⟩

def pccBoolNotEquiv : Bool ≃ Bool where
  toFun b := !b
  invFun b := !b
  left_inv b := by cases b <;> rfl
  right_inv b := by cases b <;> rfl

def pccExceptionalReflection (n : ℕ) : Equiv.Perm (PccExceptionalIndex n) :=
  Equiv.sumCongr pccBoolNotEquiv (Equiv.refl (Fin n))

theorem pccExceptional_isCriticalReflection (n : ℕ) :
    IsCriticalReflection (pccExceptionalValue n) (pccExceptionalReflection n) := by
  intro i
  rcases i with b | k
  · cases b <;> apply Complex.ext <;>
      norm_num [pccExceptionalValue, pccExceptionalReflection, pccBoolNotEquiv]
  · apply Complex.ext <;>
      norm_num [pccExceptionalValue, pccExceptionalReflection, pccBoolNotEquiv]

-- The finite case split deliberately lets `simp` normalize the concrete ordinate equalities.
set_option linter.flexible false in
theorem pccExceptional_horizontalMultiplicity_inl (n : ℕ) (b : Bool) :
    horizontalMultiplicity (pccExceptionalValue n) (Sum.inl b) = 2 := by
  classical
  have hfilter :
      (Finset.univ.filter fun j : PccExceptionalIndex n ↦
        (pccExceptionalValue n j).im = (pccExceptionalValue n (Sum.inl b)).im) =
        ({Sum.inl false, Sum.inl true} : Finset (PccExceptionalIndex n)) := by
    ext j
    rcases j with b' | k
    · cases b <;> cases b' <;> simp [pccExceptionalValue]
    · cases b <;> simp [pccExceptionalValue]
      all_goals
        intro h
        have hkNat : 2 ≤ (k : ℕ) + 2 := by omega
        have hk : (2 : ℝ) ≤ (k : ℕ) + 2 := by exact_mod_cast hkNat
        linarith
  rw [horizontalMultiplicity, hfilter]
  simp

-- The finite case split deliberately lets `simp` normalize the concrete ordinate equalities.
set_option linter.flexible false in
theorem pccExceptional_horizontalMultiplicity_inr (n : ℕ) (k : Fin n) :
    horizontalMultiplicity (pccExceptionalValue n) (Sum.inr k) = 1 := by
  classical
  have hfilter :
      (Finset.univ.filter fun j : PccExceptionalIndex n ↦
        (pccExceptionalValue n j).im = (pccExceptionalValue n (Sum.inr k)).im) =
        ({Sum.inr k} : Finset (PccExceptionalIndex n)) := by
    ext j
    rcases j with b | l
    · cases b <;> simp [pccExceptionalValue]
      all_goals
        intro h
        have hkNat : 2 ≤ (k : ℕ) + 2 := by omega
        have hk : (2 : ℝ) ≤ (k : ℕ) + 2 := by exact_mod_cast hkNat
        linarith
    · simp [pccExceptionalValue, Fin.ext_iff]
  rw [horizontalMultiplicity, hfilter]
  simp

@[simp] theorem pccExceptional_card (n : ℕ) :
    Fintype.card (PccExceptionalIndex n) = n + 2 := by
  simp [PccExceptionalIndex, Nat.add_comm]

theorem pccExceptional_horizontalPairCount (n : ℕ) :
    horizontalPairCount (pccExceptionalValue n) = n + 4 := by
  classical
  simp [horizontalPairCount, pccExceptional_horizontalMultiplicity_inl,
    pccExceptional_horizontalMultiplicity_inr]
  omega

theorem pccExceptional_simpleCriticalCount (n : ℕ) :
    simpleCriticalCount (pccExceptionalValue n) = n := by
  classical
  rw [← horizontalSingletonCount_eq_simpleCriticalCount
    (pccExceptional_isCriticalReflection n)]
  let e : Fin n ↪ PccExceptionalIndex n :=
    ⟨Sum.inr, fun _ _ h ↦ Sum.inr.inj h⟩
  have hfilter :
      (Finset.univ.filter fun i : PccExceptionalIndex n ↦
        horizontalMultiplicity (pccExceptionalValue n) i = 1) =
        Finset.univ.map e := by
    ext i
    rcases i with b | k
    · cases b <;>
        simp [pccExceptional_horizontalMultiplicity_inl, e]
    · simp [pccExceptional_horizontalMultiplicity_inr, e]
  unfold horizontalSingletonCount
  rw [show (∑ i : PccExceptionalIndex n,
      if horizontalMultiplicity (pccExceptionalValue n) i = 1 then 1 else 0) =
      (Finset.univ.filter fun i : PccExceptionalIndex n ↦
        horizontalMultiplicity (pccExceptionalValue n) i = 1).card by simp]
  rw [hfilter]
  simp [e]

theorem pccExceptional_has_offLine (n : ℕ) :
    ∃ i : PccExceptionalIndex n, (pccExceptionalValue n i).re ≠ 1 / 2 := by
  exact ⟨Sum.inl false, by norm_num [pccExceptionalValue]⟩

def pccExceptionalPairRatio (n : ℕ) : ℝ :=
  horizontalPairCount (pccExceptionalValue n) / Fintype.card (PccExceptionalIndex n)

def pccExceptionalCriticalRatio (n : ℕ) : ℝ :=
  simpleCriticalCount (pccExceptionalValue n) / Fintype.card (PccExceptionalIndex n)

theorem pccExceptionalPairRatio_eq (n : ℕ) :
    pccExceptionalPairRatio n = ((n : ℝ) + 4) / ((n : ℝ) + 2) := by
  simp [pccExceptionalPairRatio, pccExceptional_horizontalPairCount]
  ring

theorem pccExceptionalCriticalRatio_eq (n : ℕ) :
    pccExceptionalCriticalRatio n = (n : ℝ) / ((n : ℝ) + 2) := by
  simp [pccExceptionalCriticalRatio, pccExceptional_simpleCriticalCount]
  ring

theorem pccExceptional_pairRatio_tendsto_one :
    Tendsto pccExceptionalPairRatio atTop (nhds 1) := by
  have h := tendsto_add_mul_div_add_mul_atTop_nhds
    (𝕜 := ℝ) 4 2 1 (d := 1) one_ne_zero
  have h' : Tendsto (fun k : ℕ ↦ (4 + 1 * (k : ℝ)) / (2 + 1 * (k : ℝ)))
      atTop (nhds (1 : ℝ)) := by simpa using h
  apply h'.congr'
  filter_upwards with n
  rw [pccExceptionalPairRatio_eq]
  ring

theorem pccExceptional_criticalRatio_tendsto_one :
    Tendsto pccExceptionalCriticalRatio atTop (nhds 1) := by
  have h := tendsto_natCast_div_add_atTop (𝕜 := ℝ) 2
  exact h.congr' (Eventually.of_forall fun n ↦ (pccExceptionalCriticalRatio_eq n).symm)

end PersistentExceptionModel

section ActualZetaZeros

/-- Distinct positive-height nontrivial zeta-zero values up to height `T`. -/
def pccPositiveZetaZeroSet (T : ℝ) : Set ℂ :=
  {s | IsNontrivialZero s ∧ 0 < s.im ∧ s.im ≤ T}

theorem finite_pccPositiveZetaZeroSet (T : ℝ) :
    (pccPositiveZetaZeroSet T).Finite := by
  let K : Set ℂ := Metric.closedBall 0 (|T| + 2)
  have hK : IsCompact K := isCompact_closedBall 0 (|T| + 2)
  apply (compact_inter_nontrivialZeros_finite hK).subset
  intro s hs
  refine ⟨?_, hs.1⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hrePos : 0 < s.re := speiser_nontrivial_zero_re_pos hs.1
  have hreLt : s.re < 1 := nontrivial_zero_re_lt_one hs.1
  have hreAbs : |s.re| ≤ 1 := by
    rw [abs_of_pos hrePos]
    linarith
  have himAbs : |s.im| ≤ |T| := by
    rw [abs_of_pos hs.2.1]
    exact hs.2.2.trans (le_abs_self T)
  calc
    ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
    _ ≤ |T| + 2 := by linarith

def pccPositiveZetaZeroFinset (T : ℝ) : Finset ℂ :=
  (finite_pccPositiveZetaZeroSet T).toFinset

@[simp] theorem mem_pccPositiveZetaZeroFinset {T : ℝ} {s : ℂ} :
    s ∈ pccPositiveZetaZeroFinset T ↔
      IsNontrivialZero s ∧ 0 < s.im ∧ s.im ≤ T := by
  classical
  simp [pccPositiveZetaZeroFinset, pccPositiveZetaZeroSet]

/-- Multiplicity copies of positive-height nontrivial zeros, using the entire xi divisor. -/
abbrev PccPositiveZetaZeroIndex (T : ℝ) :=
  Σ s : {s // s ∈ pccPositiveZetaZeroFinset T}, Fin (riemannXiZeroMultiplicity s.1)

def pccPositiveZetaZeroValue (T : ℝ) : PccPositiveZetaZeroIndex T → ℂ :=
  fun p ↦ p.1.1

/-- The local analytic unit relating the project xi function to zeta away from `0` and `1`. -/
def riemannXiZetaUnit (s : ℂ) : ℂ :=
  s * (s - 1) / 2 * ((Gammaℝ s)⁻¹)⁻¹

theorem analyticAt_riemannXiZetaUnit_of_isNontrivialZero {s : ℂ}
    (hs : IsNontrivialZero s) :
    AnalyticAt ℂ riemannXiZetaUnit s := by
  have hinv : AnalyticAt ℂ (fun z : ℂ ↦ (Gammaℝ z)⁻¹) s :=
    differentiable_Gammaℝ_inv.analyticAt s
  have hinvNe : (Gammaℝ s)⁻¹ ≠ 0 :=
    inv_ne_zero (Gammaℝ_ne_zero_of_isNontrivialZero hs)
  have hgamma : AnalyticAt ℂ (fun z : ℂ ↦ ((Gammaℝ z)⁻¹)⁻¹) s :=
    hinv.inv hinvNe
  have hpoly : AnalyticAt ℂ (fun z : ℂ ↦ z * (z - 1) / 2) s := by
    fun_prop
  exact hpoly.mul hgamma

theorem riemannXiZetaUnit_ne_zero_of_isNontrivialZero {s : ℂ}
    (hs : IsNontrivialZero s) :
    riemannXiZetaUnit s ≠ 0 := by
  have hs0 : s ≠ 0 := ne_zero_of_isNontrivialZero hs
  have hs1 : s ≠ 1 := hs.2.2
  have hgamma : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_isNontrivialZero hs
  simp only [riemannXiZetaUnit, inv_inv]
  exact mul_ne_zero
    (div_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) (by norm_num)) hgamma

theorem eventually_riemannXi_eq_unit_mul_riemannZeta {s : ℂ}
    (hs : IsNontrivialZero s) :
    riemannXi =ᶠ[nhds s] riemannXiZetaUnit * riemannZeta := by
  have hs0 : s ≠ 0 := ne_zero_of_isNontrivialZero hs
  have hs1 : s ≠ 1 := hs.2.2
  have hunit := analyticAt_riemannXiZetaUnit_of_isNontrivialZero hs
  have hunitNe := riemannXiZetaUnit_ne_zero_of_isNontrivialZero hs
  have hgamma : ∀ᶠ z in nhds s, Gammaℝ z ≠ 0 := by
    have hevent := hunit.continuousAt.eventually_ne hunitNe
    filter_upwards [hevent] with z hz
    have hz' : (z ≠ 0 ∧ z - 1 ≠ 0) ∧ Gammaℝ z ≠ 0 := by
      simpa [riemannXiZetaUnit] using hz
    exact hz'.2
  filter_upwards [continuousAt_id.eventually_ne hs0,
    continuousAt_id.eventually_ne hs1, hgamma] with z hz0 hz1 hzGamma
  have hz0' : z ≠ 0 := by simpa using hz0
  have hz1' : z ≠ 1 := by simpa using hz1
  rw [riemannXi_eq_mul_completedRiemannZeta hz0' hz1']
  change z * (z - 1) / 2 * completedRiemannZeta z =
    riemannXiZetaUnit z * riemannZeta z
  rw [riemannZeta_def_of_ne_zero hz0']
  simp only [riemannXiZetaUnit, inv_inv]
  field_simp

theorem burnolZetaZeroMultiplicity_eq_riemannXiZeroMultiplicity
    {s : ℂ} (hs : IsNontrivialZero s) :
    burnolZetaZeroMultiplicity s = riemannXiZeroMultiplicity s := by
  have hzeta : AnalyticAt ℂ riemannZeta s :=
    analyticOn_riemannZeta s (by simpa using hs.2.2)
  have hunit := analyticAt_riemannXiZetaUnit_of_isNontrivialZero hs
  have hunitOrder : analyticOrderAt riemannXiZetaUnit s = 0 :=
    analyticOrderAt_eq_zero.mpr
      (Or.inr (riemannXiZetaUnit_ne_zero_of_isNontrivialZero hs))
  have horder : analyticOrderAt riemannXi s = analyticOrderAt riemannZeta s := by
    calc
      analyticOrderAt riemannXi s =
          analyticOrderAt (riemannXiZetaUnit * riemannZeta) s := by
        apply analyticOrderAt_congr
        exact eventually_riemannXi_eq_unit_mul_riemannZeta hs
      _ = analyticOrderAt riemannXiZetaUnit s + analyticOrderAt riemannZeta s :=
        analyticOrderAt_mul hunit hzeta
      _ = analyticOrderAt riemannZeta s := by rw [hunitOrder, zero_add]
  exact (congrArg ENat.toNat horder).symm

theorem riemannXiZeroMultiplicity_conj (s : ℂ) :
    riemannXiZeroMultiplicity (conj s) = riemannXiZeroMultiplicity s := by
  exact analyticOrderNatAt_conj_eq differentiable_riemannXi
    ⟨1, riemannXi_one_ne_zero⟩ riemannXi_conj s

theorem riemannXiZeroMultiplicity_one_sub_conj (s : ℂ) :
    riemannXiZeroMultiplicity (1 - conj s) = riemannXiZeroMultiplicity s := by
  rw [riemannXiZeroMultiplicity_one_sub, riemannXiZeroMultiplicity_conj]

def pccPositiveZetaZeroReflect (T : ℝ)
    (s : {s // s ∈ pccPositiveZetaZeroFinset T}) :
    {s // s ∈ pccPositiveZetaZeroFinset T} := by
  refine ⟨1 - conj s.1, mem_pccPositiveZetaZeroFinset.mpr ⟨?_, ?_, ?_⟩⟩
  · exact isNontrivialZero_one_sub_conj
      (mem_pccPositiveZetaZeroFinset.mp s.2).1
  · simpa using (mem_pccPositiveZetaZeroFinset.mp s.2).2.1
  · simpa using (mem_pccPositiveZetaZeroFinset.mp s.2).2.2

@[simp] theorem pccPositiveZetaZeroReflect_val (T : ℝ)
    (s : {s // s ∈ pccPositiveZetaZeroFinset T}) :
    (pccPositiveZetaZeroReflect T s).1 = 1 - conj s.1 := by
  rfl

theorem pccPositiveZetaZeroReflect_involutive (T : ℝ) :
    Function.Involutive (pccPositiveZetaZeroReflect T) := by
  intro s
  apply Subtype.ext
  simp [pccPositiveZetaZeroReflect]

def pccPositiveZetaZeroIndexReflect (T : ℝ)
    (p : PccPositiveZetaZeroIndex T) : PccPositiveZetaZeroIndex T := by
  let hmult := riemannXiZeroMultiplicity_one_sub_conj p.1.1
  exact ⟨pccPositiveZetaZeroReflect T p.1, Fin.cast hmult.symm p.2⟩

@[simp] theorem pccPositiveZetaZeroIndexReflect_val (T : ℝ)
    (p : PccPositiveZetaZeroIndex T) :
    pccPositiveZetaZeroValue T (pccPositiveZetaZeroIndexReflect T p) =
      1 - conj (pccPositiveZetaZeroValue T p) := by
  rfl

theorem pccPositiveZetaZeroIndexReflect_involutive (T : ℝ) :
    Function.Involutive (pccPositiveZetaZeroIndexReflect T) := by
  intro p
  apply Sigma.ext
  · apply Subtype.ext
    simp [pccPositiveZetaZeroIndexReflect, pccPositiveZetaZeroReflect]
  · rw [Fin.heq_ext_iff]
    · simp [pccPositiveZetaZeroIndexReflect]
    · simp [pccPositiveZetaZeroIndexReflect, pccPositiveZetaZeroReflect]

def pccPositiveZetaZeroIndexReflection (T : ℝ) :
    Equiv.Perm (PccPositiveZetaZeroIndex T) where
  toFun := pccPositiveZetaZeroIndexReflect T
  invFun := pccPositiveZetaZeroIndexReflect T
  left_inv := pccPositiveZetaZeroIndexReflect_involutive T
  right_inv := pccPositiveZetaZeroIndexReflect_involutive T

theorem pccPositiveZetaZero_isCriticalReflection (T : ℝ) :
    IsCriticalReflection (pccPositiveZetaZeroValue T)
      (pccPositiveZetaZeroIndexReflection T) := by
  intro p
  rfl

def pccPositiveZetaZeroCount (T : ℝ) : ℕ :=
  Fintype.card (PccPositiveZetaZeroIndex T)

def pccPositiveZetaHorizontalPairCount (T : ℝ) : ℕ :=
  horizontalPairCount (pccPositiveZetaZeroValue T)

/-- An exact, cofinal strengthening of horizontal multiplicity density one. -/
def PccExactHorizontalPairCountCofinal : Prop :=
  ∀ B : ℝ, ∃ T : ℝ, B < T ∧
    pccPositiveZetaHorizontalPairCount T = pccPositiveZetaZeroCount T

theorem positive_nontrivialZero_re_eq_half_of_exactHorizontalPairCountCofinal
    (hexact : PccExactHorizontalPairCountCofinal) {s : ℂ}
    (hs : IsNontrivialZero s) (hsIm : 0 < s.im) :
    s.re = 1 / 2 := by
  obtain ⟨T, hsT, hcount⟩ := hexact s.im
  have hsMem : s ∈ pccPositiveZetaZeroFinset T :=
    mem_pccPositiveZetaZeroFinset.mpr ⟨hs, hsIm, hsT.le⟩
  have hsMult : 0 < riemannXiZeroMultiplicity s :=
    (riemannXiZeroMultiplicity_pos_iff s).mpr hs
  let sIndex : {s // s ∈ pccPositiveZetaZeroFinset T} := ⟨s, hsMem⟩
  let p : PccPositiveZetaZeroIndex T := ⟨sIndex, ⟨0, hsMult⟩⟩
  have hcount' : horizontalPairCount (pccPositiveZetaZeroValue T) =
      Fintype.card (PccPositiveZetaZeroIndex T) := by
    simpa [pccPositiveZetaHorizontalPairCount, pccPositiveZetaZeroCount] using hcount
  have hp := all_critical_of_horizontalPairCount_eq_card
    (pccPositiveZetaZero_isCriticalReflection T) hcount' p
  simpa [p, sIndex, pccPositiveZetaZeroValue] using hp.2

/-- Exact cofinal disappearance of horizontal excess is a genuine last-exception RH localizer. -/
theorem riemannHypothesis_of_exactHorizontalPairCountCofinal
    (hexact : PccExactHorizontalPairCountCofinal) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_nontrivial_zeros_on_line]
  intro s hs
  rw [OnCriticalLine]
  rcases lt_trichotomy s.im 0 with hsNeg | hsZero | hsPos
  · have hconjZero : IsNontrivialZero (conj s) := isNontrivialZero_conj hs
    have hconjIm : 0 < (conj s).im := by simp [hsNeg]
    have hcritical :=
      positive_nontrivialZero_re_eq_half_of_exactHorizontalPairCountCofinal
        hexact hconjZero hconjIm
    simpa using hcritical
  · exact (criticalStripRealAxisZeroFree s hs hsZero).elim
  · exact positive_nontrivialZero_re_eq_half_of_exactHorizontalPairCountCofinal
      hexact hs hsPos

end ActualZetaZeros

end

end LeanLab.Riemann
