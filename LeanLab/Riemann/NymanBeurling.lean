import LeanLab.Riemann.Basic

set_option linter.style.header false

/-!
# Nyman-Beurling route scaffolding

This file contains only small, compiled infrastructure for the Nyman-Beurling
route. The first step is to package the fractional-part kernels as honest
`L²` objects on the unit interval.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace LeanLab.Riemann

/-- The real Hilbert space `L²(0, 1)` used by the local Nyman-Beurling scaffold. -/
abbrev unitIntervalL2 : Type :=
  Lp ℝ (2 : ℝ≥0∞) (volume.restrict (Set.Ioo (0 : ℝ) 1))

/-- The basic fractional-part kernel used in the Nyman-Beurling route. -/
def fractionalPartKernel (a x : ℝ) : ℝ :=
  Int.fract (a / x)

theorem measurable_fractionalPartKernel (a : ℝ) :
    Measurable (fractionalPartKernel a) := by
  change Measurable (fun x : ℝ => Int.fract (a / x))
  exact Measurable.fract (measurable_const.div measurable_id)

theorem fractionalPartKernel_nonneg (a x : ℝ) :
    0 ≤ fractionalPartKernel a x := by
  simp [fractionalPartKernel]

theorem fractionalPartKernel_lt_one (a x : ℝ) :
    fractionalPartKernel a x < 1 := by
  simpa [fractionalPartKernel] using Int.fract_lt_one (a / x)

theorem norm_fractionalPartKernel_le_one (a x : ℝ) :
    ‖fractionalPartKernel a x‖ ≤ (1 : ℝ) := by
  rw [Real.norm_eq_abs]
  rw [abs_of_nonneg (fractionalPartKernel_nonneg a x)]
  exact (fractionalPartKernel_lt_one a x).le

theorem fractionalPartKernel_memLp_unitInterval (a : ℝ) (p : ℝ≥0∞) :
    MemLp (fractionalPartKernel a) p (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
  refine MemLp.of_bound ?_ 1 ?_
  · exact (measurable_fractionalPartKernel a).aestronglyMeasurable
  · exact ae_of_all _ (fun x => norm_fractionalPartKernel_le_one a x)

theorem fractionalPartKernel_memLp_two_unitInterval (a : ℝ) :
    MemLp (fractionalPartKernel a) (2 : ℝ≥0∞)
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
  exact fractionalPartKernel_memLp_unitInterval a 2

/-- The same kernel as an element of `L²(0, 1)`. -/
def fractionalPartKernelL2 (a : ℝ) : unitIntervalL2 :=
  (fractionalPartKernel_memLp_two_unitInterval a).toLp (fractionalPartKernel a)

theorem fractionalPartKernelL2_coeFn (a : ℝ) :
    fractionalPartKernelL2 a =ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 1)] fractionalPartKernel a := by
  exact MemLp.coeFn_toLp (fractionalPartKernel_memLp_two_unitInterval a)

/-- The constant-one function used as a target vector in the unit-interval `L²` space. -/
def unitIntervalOne (_ : ℝ) : ℝ :=
  1

theorem measurable_unitIntervalOne :
    Measurable unitIntervalOne := by
  exact measurable_const

theorem unitIntervalOne_memLp_two_unitInterval :
    MemLp unitIntervalOne (2 : ℝ≥0∞)
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
  refine MemLp.of_bound ?_ 1 ?_
  · exact measurable_unitIntervalOne.aestronglyMeasurable
  · exact ae_of_all _ (fun x => by
      simp [unitIntervalOne])

/-- The constant-one function as an element of `L²(0, 1)`. -/
def unitIntervalOneL2 : unitIntervalL2 :=
  unitIntervalOne_memLp_two_unitInterval.toLp unitIntervalOne

theorem unitIntervalOneL2_coeFn :
    unitIntervalOneL2 =ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 1)] unitIntervalOne := by
  exact MemLp.coeFn_toLp unitIntervalOne_memLp_two_unitInterval

theorem unitIntervalOneL2_coeFn_const :
    unitIntervalOneL2 =ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 1)] fun _ : ℝ => (1 : ℝ) := by
  change unitIntervalOneL2 =ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 1)] unitIntervalOne
  exact unitIntervalOneL2_coeFn

/-- The real span of the packaged fractional-part kernels in `L²(0, 1)`. -/
def nymanBeurlingKernelSpan : Submodule ℝ unitIntervalL2 :=
  Submodule.span ℝ (Set.range fractionalPartKernelL2)

theorem fractionalPartKernelL2_mem_nymanBeurlingKernelSpan (a : ℝ) :
    fractionalPartKernelL2 a ∈ nymanBeurlingKernelSpan := by
  exact Submodule.subset_span ⟨a, rfl⟩

theorem range_fractionalPartKernelL2_subset_nymanBeurlingKernelSpan :
    Set.range fractionalPartKernelL2 ⊆ nymanBeurlingKernelSpan := by
  intro f hf
  exact Submodule.subset_span hf

theorem nymanBeurlingKernelSpan_le {S : Submodule ℝ unitIntervalL2}
    (hS : ∀ a : ℝ, fractionalPartKernelL2 a ∈ S) :
    nymanBeurlingKernelSpan ≤ S := by
  exact Submodule.span_le.mpr (by
    rintro _ ⟨a, rfl⟩
    exact hS a)

/-- Unit-interval parameters used by the restricted Nyman-Beurling scaffold. -/
def nymanBeurlingRestrictedParameterSet : Set ℝ :=
  {a : ℝ | 0 < a ∧ a ≤ 1}

/-- Packaged kernels whose parameters lie in the restricted unit interval. -/
def nymanBeurlingRestrictedKernelSet : Set unitIntervalL2 :=
  fractionalPartKernelL2 '' nymanBeurlingRestrictedParameterSet

/-- The packaged kernel map indexed by restricted unit-interval parameters. -/
def restrictedFractionalPartKernelL2
    (a : nymanBeurlingRestrictedParameterSet) : unitIntervalL2 :=
  fractionalPartKernelL2 (a : ℝ)

/-- Positive natural indices for the Baez-Duarte restricted-parameter bridge. -/
abbrev baezDuartePositiveNatIndex : Type :=
  {n : ℕ // 0 < n}

theorem baezDuarte_reciprocal_mem_restricted
    (n : baezDuartePositiveNatIndex) :
    0 < (((n : ℕ) : ℝ)⁻¹) ∧ (((n : ℕ) : ℝ)⁻¹) ≤ 1 := by
  have hnpos_nat : 0 < (n : ℕ) := n.property
  have hnpos_real : 0 < ((n : ℕ) : ℝ) := Nat.cast_pos.mpr hnpos_nat
  have hone_nat : 1 ≤ (n : ℕ) := Nat.succ_le_of_lt hnpos_nat
  have hone_real : (1 : ℝ) ≤ ((n : ℕ) : ℝ) := by
    exact_mod_cast hone_nat
  exact ⟨inv_pos.mpr hnpos_real, inv_le_one_of_one_le₀ hone_real⟩

/-- Positive natural indices mapped to the restricted parameter `1 / n`. -/
def baezDuarteReciprocalParameter
    (n : baezDuartePositiveNatIndex) : nymanBeurlingRestrictedParameterSet :=
  ⟨(((n : ℕ) : ℝ)⁻¹), baezDuarte_reciprocal_mem_restricted n⟩

/-- The reciprocal map is injective, so finite natural coefficients can be
transported by support. -/
def baezDuarteReciprocalEmbedding :
    baezDuartePositiveNatIndex ↪ nymanBeurlingRestrictedParameterSet where
  toFun := baezDuarteReciprocalParameter
  inj' := by
    intro m n hmn
    apply Subtype.ext
    have hrec :
        (((m : ℕ) : ℝ)⁻¹) = (((n : ℕ) : ℝ)⁻¹) := by
      exact congr_arg Subtype.val hmn
    have hcast : ((m : ℕ) : ℝ) = ((n : ℕ) : ℝ) := by
      calc
        ((m : ℕ) : ℝ) = (((m : ℕ) : ℝ)⁻¹)⁻¹ := by rw [inv_inv]
        _ = (((n : ℕ) : ℝ)⁻¹)⁻¹ := by rw [hrec]
        _ = ((n : ℕ) : ℝ) := by rw [inv_inv]
    exact_mod_cast hcast

theorem nymanBeurlingRestrictedKernelSet_eq_range :
    nymanBeurlingRestrictedKernelSet = Set.range restrictedFractionalPartKernelL2 := by
  ext f
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨(a : ℝ), a.property, rfl⟩

/-- The real span of the restricted fractional-part kernels in `L²(0, 1)`. -/
def nymanBeurlingRestrictedKernelSpan : Submodule ℝ unitIntervalL2 :=
  Submodule.span ℝ nymanBeurlingRestrictedKernelSet

theorem fractionalPartKernelL2_mem_nymanBeurlingRestrictedKernelSet {a : ℝ}
    (ha0 : 0 < a) (ha1 : a ≤ 1) :
    fractionalPartKernelL2 a ∈ nymanBeurlingRestrictedKernelSet := by
  exact ⟨a, ⟨ha0, ha1⟩, rfl⟩

theorem fractionalPartKernelL2_mem_nymanBeurlingRestrictedKernelSpan {a : ℝ}
    (ha0 : 0 < a) (ha1 : a ≤ 1) :
    fractionalPartKernelL2 a ∈ nymanBeurlingRestrictedKernelSpan := by
  exact Submodule.subset_span
    (fractionalPartKernelL2_mem_nymanBeurlingRestrictedKernelSet ha0 ha1)

theorem nymanBeurlingRestrictedKernelSpan_le :
    nymanBeurlingRestrictedKernelSpan ≤ nymanBeurlingKernelSpan := by
  rw [nymanBeurlingRestrictedKernelSpan, nymanBeurlingRestrictedKernelSet]
  exact Submodule.span_le.mpr (by
    rintro _ ⟨a, _ha, rfl⟩
    exact fractionalPartKernelL2_mem_nymanBeurlingKernelSpan a)

theorem mem_nymanBeurlingRestrictedKernelSpan_iff_exists_finsupp_sum
    (g : unitIntervalL2) :
    g ∈ nymanBeurlingRestrictedKernelSpan ↔
      ∃ c : nymanBeurlingRestrictedParameterSet →₀ ℝ,
        (c.sum fun a r => r • fractionalPartKernelL2 (a : ℝ)) = g := by
  rw [nymanBeurlingRestrictedKernelSpan, nymanBeurlingRestrictedKernelSet_eq_range]
  simpa [restrictedFractionalPartKernelL2] using
    (Finsupp.mem_span_range_iff_exists_finsupp
      (v := restrictedFractionalPartKernelL2) (x := g))

/-- The topological closure of the Nyman-Beurling kernel span in `L²(0, 1)`. -/
def nymanBeurlingKernelClosure : Submodule ℝ unitIntervalL2 :=
  nymanBeurlingKernelSpan.topologicalClosure

theorem nymanBeurlingKernelSpan_le_closure :
    nymanBeurlingKernelSpan ≤ nymanBeurlingKernelClosure := by
  exact Submodule.le_topologicalClosure nymanBeurlingKernelSpan

theorem isClosed_nymanBeurlingKernelClosure :
    IsClosed (nymanBeurlingKernelClosure : Set unitIntervalL2) := by
  exact Submodule.isClosed_topologicalClosure nymanBeurlingKernelSpan

theorem nymanBeurlingKernelClosure_coe :
    (nymanBeurlingKernelClosure : Set unitIntervalL2) =
      closure (nymanBeurlingKernelSpan : Set unitIntervalL2) := by
  exact Submodule.topologicalClosure_coe nymanBeurlingKernelSpan

/-- The topological closure of the restricted Nyman-Beurling kernel span in `L²(0, 1)`. -/
def nymanBeurlingRestrictedKernelClosure : Submodule ℝ unitIntervalL2 :=
  nymanBeurlingRestrictedKernelSpan.topologicalClosure

theorem nymanBeurlingRestrictedKernelSpan_le_closure :
    nymanBeurlingRestrictedKernelSpan ≤ nymanBeurlingRestrictedKernelClosure := by
  exact Submodule.le_topologicalClosure nymanBeurlingRestrictedKernelSpan

theorem isClosed_nymanBeurlingRestrictedKernelClosure :
    IsClosed (nymanBeurlingRestrictedKernelClosure : Set unitIntervalL2) := by
  exact Submodule.isClosed_topologicalClosure nymanBeurlingRestrictedKernelSpan

theorem nymanBeurlingRestrictedKernelClosure_coe :
    (nymanBeurlingRestrictedKernelClosure : Set unitIntervalL2) =
      closure (nymanBeurlingRestrictedKernelSpan : Set unitIntervalL2) := by
  exact Submodule.topologicalClosure_coe nymanBeurlingRestrictedKernelSpan

theorem nymanBeurlingRestrictedKernelClosure_le :
    nymanBeurlingRestrictedKernelClosure ≤ nymanBeurlingKernelClosure := by
  exact Submodule.topologicalClosure_mono nymanBeurlingRestrictedKernelSpan_le

theorem fractionalPartKernelL2_mem_nymanBeurlingKernelClosure (a : ℝ) :
    fractionalPartKernelL2 a ∈ nymanBeurlingKernelClosure := by
  exact nymanBeurlingKernelSpan_le_closure
    (fractionalPartKernelL2_mem_nymanBeurlingKernelSpan a)

theorem fractionalPartKernelL2_mem_nymanBeurlingRestrictedKernelClosure {a : ℝ}
    (ha0 : 0 < a) (ha1 : a ≤ 1) :
    fractionalPartKernelL2 a ∈ nymanBeurlingRestrictedKernelClosure := by
  exact nymanBeurlingRestrictedKernelSpan_le_closure
    (fractionalPartKernelL2_mem_nymanBeurlingRestrictedKernelSpan ha0 ha1)

/-- Project-local Hilbert-space density statement for the restricted kernel span. -/
def nymanBeurlingRestrictedKernelDense : Prop :=
  Dense (nymanBeurlingRestrictedKernelSpan : Set unitIntervalL2)

theorem nymanBeurlingRestrictedKernelDense_iff_closure_eq_top :
    nymanBeurlingRestrictedKernelDense ↔ nymanBeurlingRestrictedKernelClosure = ⊤ := by
  dsimp [nymanBeurlingRestrictedKernelDense, nymanBeurlingRestrictedKernelClosure]
  exact Submodule.dense_iff_topologicalClosure_eq_top

theorem nymanBeurlingRestrictedKernelDense_iff_forall_mem_closure :
    nymanBeurlingRestrictedKernelDense ↔
      ∀ f : unitIntervalL2, f ∈ nymanBeurlingRestrictedKernelClosure := by
  constructor
  · intro h f
    change f ∈ (nymanBeurlingRestrictedKernelClosure : Set unitIntervalL2)
    rw [nymanBeurlingRestrictedKernelClosure_coe]
    exact h f
  · intro h f
    have hf : f ∈ (nymanBeurlingRestrictedKernelClosure : Set unitIntervalL2) := h f
    rwa [nymanBeurlingRestrictedKernelClosure_coe] at hf

theorem unitIntervalOneL2_mem_restrictedClosure_of_nymanBeurlingRestrictedKernelDense
    (h : nymanBeurlingRestrictedKernelDense) :
    unitIntervalOneL2 ∈ nymanBeurlingRestrictedKernelClosure := by
  exact (nymanBeurlingRestrictedKernelDense_iff_forall_mem_closure.mp h) unitIntervalOneL2

theorem unitIntervalOneL2_mem_restrictedClosure_iff_forall_exists_dist_lt :
    unitIntervalOneL2 ∈ nymanBeurlingRestrictedKernelClosure ↔
      ∀ ε : ℝ, 0 < ε →
        ∃ g : unitIntervalL2, g ∈ nymanBeurlingRestrictedKernelSpan ∧
          dist unitIntervalOneL2 g < ε := by
  change unitIntervalOneL2 ∈ (nymanBeurlingRestrictedKernelClosure : Set unitIntervalL2) ↔
    ∀ ε : ℝ, 0 < ε →
      ∃ g : unitIntervalL2, g ∈ (nymanBeurlingRestrictedKernelSpan : Set unitIntervalL2) ∧
        dist unitIntervalOneL2 g < ε
  rw [nymanBeurlingRestrictedKernelClosure_coe]
  exact Metric.mem_closure_iff

theorem exists_nymanBeurlingRestrictedKernelSpan_dist_unitIntervalOneL2_lt_of_restrictedDense
    (h : nymanBeurlingRestrictedKernelDense) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : unitIntervalL2, g ∈ nymanBeurlingRestrictedKernelSpan ∧
      dist unitIntervalOneL2 g < ε := by
  exact (unitIntervalOneL2_mem_restrictedClosure_iff_forall_exists_dist_lt.mp
    (unitIntervalOneL2_mem_restrictedClosure_of_nymanBeurlingRestrictedKernelDense h)) ε hε

theorem exists_restricted_finsupp_sum_dist_unitIntervalOneL2_lt_of_dense
    (h : nymanBeurlingRestrictedKernelDense) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : nymanBeurlingRestrictedParameterSet →₀ ℝ,
      dist unitIntervalOneL2 (c.sum fun a r => r • fractionalPartKernelL2 (a : ℝ)) < ε := by
  rcases exists_nymanBeurlingRestrictedKernelSpan_dist_unitIntervalOneL2_lt_of_restrictedDense
      h hε with
    ⟨g, hgspan, hgdist⟩
  rcases (mem_nymanBeurlingRestrictedKernelSpan_iff_exists_finsupp_sum g).mp hgspan with
    ⟨c, hc⟩
  exact ⟨c, by simpa [hc] using hgdist⟩

theorem exists_restricted_finsupp_sum_norm_sub_lt_of_dense
    (h : nymanBeurlingRestrictedKernelDense) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : nymanBeurlingRestrictedParameterSet →₀ ℝ,
      ‖unitIntervalOneL2 - (c.sum fun a r => r • fractionalPartKernelL2 (a : ℝ))‖ < ε := by
  simpa [dist_eq_norm] using
    exists_restricted_finsupp_sum_dist_unitIntervalOneL2_lt_of_dense h hε

/-- Project-local Hilbert-space density statement for the Nyman-Beurling kernel span. -/
def nymanBeurlingKernelDense : Prop :=
  Dense (nymanBeurlingKernelSpan : Set unitIntervalL2)

theorem nymanBeurlingKernelDense_iff_closure_eq_top :
    nymanBeurlingKernelDense ↔ nymanBeurlingKernelClosure = ⊤ := by
  dsimp [nymanBeurlingKernelDense, nymanBeurlingKernelClosure]
  exact Submodule.dense_iff_topologicalClosure_eq_top

theorem nymanBeurlingKernelDense_iff_forall_mem_closure :
    nymanBeurlingKernelDense ↔ ∀ f : unitIntervalL2, f ∈ nymanBeurlingKernelClosure := by
  constructor
  · intro h f
    change f ∈ (nymanBeurlingKernelClosure : Set unitIntervalL2)
    rw [nymanBeurlingKernelClosure_coe]
    exact h f
  · intro h f
    have hf : f ∈ (nymanBeurlingKernelClosure : Set unitIntervalL2) := h f
    rwa [nymanBeurlingKernelClosure_coe] at hf

theorem nymanBeurlingKernelDense_of_restricted
    (h : nymanBeurlingRestrictedKernelDense) :
    nymanBeurlingKernelDense := by
  exact nymanBeurlingKernelDense_iff_forall_mem_closure.mpr (fun f =>
    nymanBeurlingRestrictedKernelClosure_le
      ((nymanBeurlingRestrictedKernelDense_iff_forall_mem_closure.mp h) f))

theorem unitIntervalOneL2_mem_closure_of_nymanBeurlingKernelDense
    (h : nymanBeurlingKernelDense) :
    unitIntervalOneL2 ∈ nymanBeurlingKernelClosure := by
  exact (nymanBeurlingKernelDense_iff_forall_mem_closure.mp h) unitIntervalOneL2

theorem unitIntervalOneL2_mem_closure_iff_forall_exists_dist_lt :
    unitIntervalOneL2 ∈ nymanBeurlingKernelClosure ↔
      ∀ ε : ℝ, 0 < ε →
        ∃ g : unitIntervalL2, g ∈ nymanBeurlingKernelSpan ∧
          dist unitIntervalOneL2 g < ε := by
  change unitIntervalOneL2 ∈ (nymanBeurlingKernelClosure : Set unitIntervalL2) ↔
    ∀ ε : ℝ, 0 < ε →
      ∃ g : unitIntervalL2, g ∈ (nymanBeurlingKernelSpan : Set unitIntervalL2) ∧
        dist unitIntervalOneL2 g < ε
  rw [nymanBeurlingKernelClosure_coe]
  exact Metric.mem_closure_iff

theorem mem_nymanBeurlingKernelSpan_iff_exists_finsupp_sum (g : unitIntervalL2) :
    g ∈ nymanBeurlingKernelSpan ↔
      ∃ c : ℝ →₀ ℝ, (c.sum fun a r => r • fractionalPartKernelL2 a) = g := by
  rw [nymanBeurlingKernelSpan]
  exact Finsupp.mem_span_range_iff_exists_finsupp

theorem unitIntervalOneL2_mem_closure_iff_forall_exists_finsupp_sum_dist_lt :
    unitIntervalOneL2 ∈ nymanBeurlingKernelClosure ↔
      ∀ ε : ℝ, 0 < ε →
        ∃ c : ℝ →₀ ℝ,
          dist unitIntervalOneL2 (c.sum fun a r => r • fractionalPartKernelL2 a) < ε := by
  constructor
  · intro h ε hε
    rcases (unitIntervalOneL2_mem_closure_iff_forall_exists_dist_lt.mp h) ε hε with
      ⟨g, hgspan, hgdist⟩
    rcases (mem_nymanBeurlingKernelSpan_iff_exists_finsupp_sum g).mp hgspan with ⟨c, hc⟩
    exact ⟨c, by rwa [hc]⟩
  · intro h
    exact unitIntervalOneL2_mem_closure_iff_forall_exists_dist_lt.mpr (fun ε hε => by
      rcases h ε hε with ⟨c, hcdist⟩
      refine ⟨c.sum fun a r => r • fractionalPartKernelL2 a, ?_, hcdist⟩
      exact (mem_nymanBeurlingKernelSpan_iff_exists_finsupp_sum _).mpr ⟨c, rfl⟩)

theorem unitIntervalOneL2_mem_closure_iff_forall_exists_finsupp_sum_norm_sub_lt :
    unitIntervalOneL2 ∈ nymanBeurlingKernelClosure ↔
      ∀ ε : ℝ, 0 < ε →
        ∃ c : ℝ →₀ ℝ,
          ‖unitIntervalOneL2 - (c.sum fun a r => r • fractionalPartKernelL2 a)‖ < ε := by
  simpa [dist_eq_norm] using unitIntervalOneL2_mem_closure_iff_forall_exists_finsupp_sum_dist_lt

theorem exists_nymanBeurlingKernelSpan_dist_unitIntervalOneL2_lt_of_dense
    (h : nymanBeurlingKernelDense) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : unitIntervalL2, g ∈ nymanBeurlingKernelSpan ∧
      dist unitIntervalOneL2 g < ε := by
  exact (unitIntervalOneL2_mem_closure_iff_forall_exists_dist_lt.mp
    (unitIntervalOneL2_mem_closure_of_nymanBeurlingKernelDense h)) ε hε

theorem exists_finsupp_sum_fractionalPartKernelL2_dist_unitIntervalOneL2_lt_of_dense
    (h : nymanBeurlingKernelDense) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ →₀ ℝ,
      dist unitIntervalOneL2 (c.sum fun a r => r • fractionalPartKernelL2 a) < ε := by
  exact (unitIntervalOneL2_mem_closure_iff_forall_exists_finsupp_sum_dist_lt.mp
    (unitIntervalOneL2_mem_closure_of_nymanBeurlingKernelDense h)) ε hε

theorem exists_finsupp_sum_fractionalPartKernelL2_norm_sub_lt_of_dense
    (h : nymanBeurlingKernelDense) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ →₀ ℝ,
      ‖unitIntervalOneL2 - (c.sum fun a r => r • fractionalPartKernelL2 a)‖ < ε := by
  simpa [dist_eq_norm] using
    exists_finsupp_sum_fractionalPartKernelL2_dist_unitIntervalOneL2_lt_of_dense h hε

theorem finsupp_sum_fractionalPartKernelL2_coeFn (c : ℝ →₀ ℝ) :
    (c.sum fun a r => r • fractionalPartKernelL2 a)
      =ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 1)]
        fun x : ℝ => c.sum fun a r => r * fractionalPartKernel a x := by
  classical
  rw [Finsupp.sum]
  change (∑ a ∈ c.support, ((c a • fractionalPartKernelL2 a : unitIntervalL2) : ℝ → ℝ))
      =ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 1)]
        fun x : ℝ => ∑ a ∈ c.support, c a * fractionalPartKernel a x
  refine (eventuallyEq_sum
    (s := c.support) (l := ae (volume.restrict (Set.Ioo (0 : ℝ) 1)))
    (fun a _ha => by
      refine (Lp.coeFn_smul (c a) (fractionalPartKernelL2 a)).trans ?_
      exact (fractionalPartKernelL2_coeFn a).const_smul (c a))).trans ?_
  exact ae_of_all _ fun x => by
    simp [Pi.smul_apply, Finset.sum_apply]

theorem unitIntervalOneL2_sub_finsupp_sum_fractionalPartKernelL2_coeFn
    (c : ℝ →₀ ℝ) :
    (unitIntervalOneL2 - (c.sum fun a r => r • fractionalPartKernelL2 a))
      =ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 1)]
        fun x : ℝ => 1 - c.sum fun a r => r * fractionalPartKernel a x := by
  classical
  refine (Lp.coeFn_sub unitIntervalOneL2
    (c.sum fun a r => r • fractionalPartKernelL2 a)).trans ?_
  rw [Finsupp.sum]
  change (↑↑unitIntervalOneL2 -
          ↑↑(∑ a ∈ c.support, c a • fractionalPartKernelL2 a : unitIntervalL2))
      =ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 1)]
        fun x : ℝ => (1 : ℝ) - ∑ a ∈ c.support, c a * fractionalPartKernel a x
  have hsum :
      (↑↑(∑ a ∈ c.support, c a • fractionalPartKernelL2 a : unitIntervalL2))
        =ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 1)]
          fun x : ℝ => ∑ a ∈ c.support, c a * fractionalPartKernel a x := by
    refine (Lp.coeFn_fun_finsetSum c.support fun a =>
      c a • fractionalPartKernelL2 a).trans ?_
    have hfun :
        (fun x : ℝ => ∑ a ∈ c.support,
            ((c a • fractionalPartKernelL2 a : unitIntervalL2) : ℝ → ℝ) x)
          =ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 1)]
            (∑ a ∈ c.support,
              ((c a • fractionalPartKernelL2 a : unitIntervalL2) : ℝ → ℝ)) := by
      exact ae_of_all _ fun x => by
        simp [Finset.sum_apply]
    refine hfun.trans ?_
    refine (eventuallyEq_sum
      (s := c.support) (l := ae (volume.restrict (Set.Ioo (0 : ℝ) 1)))
      (fun a _ha => by
        refine (Lp.coeFn_smul (c a) (fractionalPartKernelL2 a)).trans ?_
        exact (fractionalPartKernelL2_coeFn a).const_smul (c a))).trans ?_
    exact ae_of_all _ fun x => by
      simp [Pi.smul_apply, Finset.sum_apply]
  refine (unitIntervalOneL2_coeFn_const.sub hsum).trans ?_
  exact ae_of_all _ fun x => by
    rfl

theorem restricted_finsupp_sum_fractionalPartKernelL2_coeFn
    (c : nymanBeurlingRestrictedParameterSet →₀ ℝ) :
    (c.sum fun a r => r • fractionalPartKernelL2 (a : ℝ))
      =ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 1)]
        fun x : ℝ => c.sum fun a r => r * fractionalPartKernel (a : ℝ) x := by
  classical
  rw [Finsupp.sum]
  change (∑ a ∈ c.support,
      ((c a • fractionalPartKernelL2 (a : ℝ) : unitIntervalL2) : ℝ → ℝ))
      =ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 1)]
        fun x : ℝ => ∑ a ∈ c.support, c a * fractionalPartKernel (a : ℝ) x
  refine (eventuallyEq_sum
    (s := c.support) (l := ae (volume.restrict (Set.Ioo (0 : ℝ) 1)))
    (fun a _ha => by
      refine (Lp.coeFn_smul (c a) (fractionalPartKernelL2 (a : ℝ))).trans ?_
      exact (fractionalPartKernelL2_coeFn (a : ℝ)).const_smul (c a))).trans ?_
  exact ae_of_all _ fun x => by
    simp [Pi.smul_apply, Finset.sum_apply]

theorem unitIntervalOneL2_sub_restricted_finsupp_sum_fractionalPartKernelL2_coeFn
    (c : nymanBeurlingRestrictedParameterSet →₀ ℝ) :
    (unitIntervalOneL2 - (c.sum fun a r => r • fractionalPartKernelL2 (a : ℝ)))
      =ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 1)]
        fun x : ℝ => 1 - c.sum fun a r => r * fractionalPartKernel (a : ℝ) x := by
  classical
  refine (Lp.coeFn_sub unitIntervalOneL2
    (c.sum fun a r => r • fractionalPartKernelL2 (a : ℝ))).trans ?_
  rw [Finsupp.sum]
  change (↑↑unitIntervalOneL2 -
          ↑↑(∑ a ∈ c.support,
            c a • fractionalPartKernelL2 (a : ℝ) : unitIntervalL2))
      =ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 1)]
        fun x : ℝ => (1 : ℝ) -
          ∑ a ∈ c.support, c a * fractionalPartKernel (a : ℝ) x
  have hsum :
      (↑↑(∑ a ∈ c.support,
          c a • fractionalPartKernelL2 (a : ℝ) : unitIntervalL2))
        =ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 1)]
          fun x : ℝ => ∑ a ∈ c.support, c a * fractionalPartKernel (a : ℝ) x := by
    refine (Lp.coeFn_fun_finsetSum c.support fun a =>
      c a • fractionalPartKernelL2 (a : ℝ)).trans ?_
    have hfun :
        (fun x : ℝ => ∑ a ∈ c.support,
            ((c a • fractionalPartKernelL2 (a : ℝ) : unitIntervalL2) : ℝ → ℝ) x)
          =ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 1)]
            (∑ a ∈ c.support,
              ((c a • fractionalPartKernelL2 (a : ℝ) : unitIntervalL2) : ℝ → ℝ)) := by
      exact ae_of_all _ fun x => by
        simp [Finset.sum_apply]
    refine hfun.trans ?_
    refine (eventuallyEq_sum
      (s := c.support) (l := ae (volume.restrict (Set.Ioo (0 : ℝ) 1)))
      (fun a _ha => by
        refine (Lp.coeFn_smul (c a) (fractionalPartKernelL2 (a : ℝ))).trans ?_
        exact (fractionalPartKernelL2_coeFn (a : ℝ)).const_smul (c a))).trans ?_
    exact ae_of_all _ fun x => by
      simp [Pi.smul_apply, Finset.sum_apply]
  refine (unitIntervalOneL2_coeFn_const.sub hsum).trans ?_
  exact ae_of_all _ fun x => by
    rfl

theorem unitIntervalL2_norm_sq_eq_integral_mul_self (f : unitIntervalL2) :
    ‖f‖ ^ 2 =
      ∫ x : ℝ, f x * f x ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
  rw [norm_sq_eq_re_inner (𝕜 := ℝ) f, L2.inner_def]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp [Real.norm_eq_abs, sq]

theorem norm_sub_finsupp_sum_fractionalPartKernelL2_sq_eq_integral_mul_self
    (c : ℝ →₀ ℝ) :
    ‖unitIntervalOneL2 - (c.sum fun a r => r • fractionalPartKernelL2 a)‖ ^ 2 =
      ∫ x : ℝ,
        (unitIntervalOneL2 - (c.sum fun a r => r • fractionalPartKernelL2 a)) x *
          (unitIntervalOneL2 - (c.sum fun a r => r • fractionalPartKernelL2 a)) x ∂
            (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
  exact unitIntervalL2_norm_sq_eq_integral_mul_self
    (unitIntervalOneL2 - (c.sum fun a r => r • fractionalPartKernelL2 a))

theorem norm_sub_restricted_finsupp_sum_sq_eq_integral_mul_self
    (c : nymanBeurlingRestrictedParameterSet →₀ ℝ) :
    ‖unitIntervalOneL2 - (c.sum fun a r => r • fractionalPartKernelL2 (a : ℝ))‖ ^ 2 =
      ∫ x : ℝ,
        (unitIntervalOneL2 -
            (c.sum fun a r => r • fractionalPartKernelL2 (a : ℝ))) x *
          (unitIntervalOneL2 -
            (c.sum fun a r => r • fractionalPartKernelL2 (a : ℝ))) x ∂
            (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
  exact unitIntervalL2_norm_sq_eq_integral_mul_self
    (unitIntervalOneL2 - (c.sum fun a r => r • fractionalPartKernelL2 (a : ℝ)))

theorem norm_sub_finsupp_sum_fractionalPartKernelL2_sq_eq_integral_concrete
    (c : ℝ →₀ ℝ) :
    ‖unitIntervalOneL2 - (c.sum fun a r => r • fractionalPartKernelL2 a)‖ ^ 2 =
      ∫ x : ℝ,
        (1 - c.sum fun a r => r * fractionalPartKernel a x) *
          (1 - c.sum fun a r => r * fractionalPartKernel a x) ∂
            (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
  rw [norm_sub_finsupp_sum_fractionalPartKernelL2_sq_eq_integral_mul_self]
  refine integral_congr_ae
    ((unitIntervalOneL2_sub_finsupp_sum_fractionalPartKernelL2_coeFn c).mono ?_)
  intro x hx
  simpa using congrArg (fun y : ℝ => y * y) hx

theorem norm_sub_restricted_finsupp_sum_sq_eq_integral_concrete
    (c : nymanBeurlingRestrictedParameterSet →₀ ℝ) :
    ‖unitIntervalOneL2 - (c.sum fun a r => r • fractionalPartKernelL2 (a : ℝ))‖ ^ 2 =
      ∫ x : ℝ,
        (1 - c.sum fun a r => r * fractionalPartKernel (a : ℝ) x) *
          (1 - c.sum fun a r => r * fractionalPartKernel (a : ℝ) x) ∂
            (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
  rw [norm_sub_restricted_finsupp_sum_sq_eq_integral_mul_self]
  refine integral_congr_ae
    ((unitIntervalOneL2_sub_restricted_finsupp_sum_fractionalPartKernelL2_coeFn c).mono ?_)
  intro x hx
  simpa using congrArg (fun y : ℝ => y * y) hx

theorem exists_finsupp_integral_one_sub_sum_fractionalPartKernel_sq_lt_of_dense
    (h : nymanBeurlingKernelDense) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ →₀ ℝ,
      (∫ x : ℝ,
        (1 - c.sum fun a r => r * fractionalPartKernel a x) *
          (1 - c.sum fun a r => r * fractionalPartKernel a x) ∂
            (volume.restrict (Set.Ioo (0 : ℝ) 1))) < ε ^ 2 := by
  rcases exists_finsupp_sum_fractionalPartKernelL2_norm_sub_lt_of_dense h hε with
    ⟨c, hc⟩
  refine ⟨c, ?_⟩
  rw [← norm_sub_finsupp_sum_fractionalPartKernelL2_sq_eq_integral_concrete c]
  exact (sq_lt_sq₀ (norm_nonneg _) hε.le).mpr hc

theorem exists_restricted_finsupp_integral_sq_lt_of_dense
    (h : nymanBeurlingRestrictedKernelDense) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : nymanBeurlingRestrictedParameterSet →₀ ℝ,
      (∫ x : ℝ,
        (1 - c.sum fun a r => r * fractionalPartKernel (a : ℝ) x) *
          (1 - c.sum fun a r => r * fractionalPartKernel (a : ℝ) x) ∂
            (volume.restrict (Set.Ioo (0 : ℝ) 1))) < ε ^ 2 := by
  rcases exists_restricted_finsupp_sum_norm_sub_lt_of_dense h hε with
    ⟨c, hc⟩
  refine ⟨c, ?_⟩
  rw [← norm_sub_restricted_finsupp_sum_sq_eq_integral_concrete c]
  exact (sq_lt_sq₀ (norm_nonneg _) hε.le).mpr hc

theorem exists_restricted_finsupp_integral_lt_of_dense_tolerance
    (h : nymanBeurlingRestrictedKernelDense) {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : nymanBeurlingRestrictedParameterSet →₀ ℝ,
      (∫ x : ℝ,
        (1 - c.sum fun a r => r * fractionalPartKernel (a : ℝ) x) *
          (1 - c.sum fun a r => r * fractionalPartKernel (a : ℝ) x) ∂
            (volume.restrict (Set.Ioo (0 : ℝ) 1))) < δ := by
  rcases exists_restricted_finsupp_integral_sq_lt_of_dense h
      (Real.sqrt_pos_of_pos hδ) with
    ⟨c, hc⟩
  refine ⟨c, ?_⟩
  simpa [Real.sq_sqrt hδ.le] using hc

theorem exists_restricted_finsupp_of_baezDuarte_finsupp
    (c : baezDuartePositiveNatIndex →₀ ℝ) :
    ∃ d : nymanBeurlingRestrictedParameterSet →₀ ℝ,
      ∀ x : ℝ,
        d.sum (fun a r => r * fractionalPartKernel (a : ℝ) x) =
          c.sum fun n r => r * fractionalPartKernel (((n : ℕ) : ℝ)⁻¹) x := by
  classical
  let d : nymanBeurlingRestrictedParameterSet →₀ ℝ :=
    c.embDomain baezDuarteReciprocalEmbedding
  refine ⟨d, ?_⟩
  intro x
  simpa [d, baezDuarteReciprocalEmbedding, baezDuarteReciprocalParameter] using
    Finsupp.sum_embDomain (v := c) (f := baezDuarteReciprocalEmbedding)
      (g := fun a r => r * fractionalPartKernel (a : ℝ) x)

theorem exists_restricted_finsupp_integral_lt_of_baezDuarte
    {δ : ℝ}
    (h : ∃ c : baezDuartePositiveNatIndex →₀ ℝ,
      (∫ x : ℝ,
        (1 - c.sum fun n r => r * fractionalPartKernel (((n : ℕ) : ℝ)⁻¹) x) *
          (1 - c.sum fun n r => r * fractionalPartKernel (((n : ℕ) : ℝ)⁻¹) x) ∂(volume.restrict
            (Set.Ioo (0 : ℝ) 1))) < δ) :
    ∃ d : nymanBeurlingRestrictedParameterSet →₀ ℝ,
      (∫ x : ℝ,
        (1 - d.sum fun a r => r * fractionalPartKernel (a : ℝ) x) *
          (1 - d.sum fun a r => r * fractionalPartKernel (a : ℝ) x) ∂(volume.restrict
            (Set.Ioo (0 : ℝ) 1))) < δ := by
  rcases h with ⟨c, hc⟩
  rcases exists_restricted_finsupp_of_baezDuarte_finsupp c with ⟨d, hdsum⟩
  refine ⟨d, ?_⟩
  have hint :
      (∫ x : ℝ,
        (1 - d.sum fun a r => r * fractionalPartKernel (a : ℝ) x) *
          (1 - d.sum fun a r => r * fractionalPartKernel (a : ℝ) x) ∂(volume.restrict
            (Set.Ioo (0 : ℝ) 1))) =
        ∫ x : ℝ,
          (1 - c.sum fun n r => r * fractionalPartKernel (((n : ℕ) : ℝ)⁻¹) x) *
            (1 - c.sum fun n r => r * fractionalPartKernel (((n : ℕ) : ℝ)⁻¹) x) ∂(volume.restrict
              (Set.Ioo (0 : ℝ) 1)) := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp [hdsum x]
  simpa [hint] using hc

theorem exists_real_finsupp_of_restricted_finsupp
    (c : nymanBeurlingRestrictedParameterSet →₀ ℝ) :
    ∃ d : ℝ →₀ ℝ,
      (∀ a ∈ d.support, 0 < a ∧ a ≤ 1) ∧
        ∀ x : ℝ,
          d.sum (fun a r => r * fractionalPartKernel a x) =
            c.sum fun a r => r * fractionalPartKernel (a : ℝ) x := by
  classical
  let emb : nymanBeurlingRestrictedParameterSet ↪ ℝ :=
    Function.Embedding.subtype nymanBeurlingRestrictedParameterSet
  let d : ℝ →₀ ℝ := c.embDomain emb
  refine ⟨d, ?_, ?_⟩
  · intro a ha
    have ha' : a ∈ c.support.map emb := by
      simpa [d] using ha
    rcases Finset.mem_map.mp ha' with ⟨b, _hb, rfl⟩
    change 0 < (b : ℝ) ∧ (b : ℝ) ≤ 1
    exact b.property
  · intro x
    change (c.embDomain emb).sum (fun a r => r * fractionalPartKernel a x) =
      c.sum (fun a r => r * fractionalPartKernel (emb a) x)
    exact Finsupp.sum_embDomain (v := c) (f := emb)
      (g := fun a r => r * fractionalPartKernel a x)

theorem exists_real_finsupp_integral_lt_of_restricted
    {δ : ℝ}
    (h : ∃ c : nymanBeurlingRestrictedParameterSet →₀ ℝ,
      (∫ x : ℝ,
        (1 - c.sum fun a r => r * fractionalPartKernel (a : ℝ) x) *
          (1 - c.sum fun a r => r * fractionalPartKernel (a : ℝ) x) ∂(volume.restrict
            (Set.Ioo (0 : ℝ) 1))) < δ) :
    ∃ d : ℝ →₀ ℝ,
      (∀ a ∈ d.support, 0 < a ∧ a ≤ 1) ∧
        (∫ x : ℝ,
          (1 - d.sum fun a r => r * fractionalPartKernel a x) *
            (1 - d.sum fun a r => r * fractionalPartKernel a x) ∂(volume.restrict
              (Set.Ioo (0 : ℝ) 1))) < δ := by
  rcases h with ⟨c, hc⟩
  rcases exists_real_finsupp_of_restricted_finsupp c with ⟨d, hdsupp, hdsum⟩
  refine ⟨d, hdsupp, ?_⟩
  have hint :
      (∫ x : ℝ,
        (1 - d.sum fun a r => r * fractionalPartKernel a x) *
          (1 - d.sum fun a r => r * fractionalPartKernel a x) ∂(volume.restrict
            (Set.Ioo (0 : ℝ) 1))) =
        ∫ x : ℝ,
          (1 - c.sum fun a r => r * fractionalPartKernel (a : ℝ) x) *
            (1 - c.sum fun a r => r * fractionalPartKernel (a : ℝ) x) ∂(volume.restrict
              (Set.Ioo (0 : ℝ) 1)) := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp [hdsum x]
  simpa [hint] using hc

theorem exists_finsupp_integral_one_sub_sum_fractionalPartKernel_sq_lt_of_dense_tolerance
    (h : nymanBeurlingKernelDense) {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ →₀ ℝ,
      (∫ x : ℝ,
        (1 - c.sum fun a r => r * fractionalPartKernel a x) *
          (1 - c.sum fun a r => r * fractionalPartKernel a x) ∂
            (volume.restrict (Set.Ioo (0 : ℝ) 1))) < δ := by
  rcases exists_finsupp_integral_one_sub_sum_fractionalPartKernel_sq_lt_of_dense h
      (Real.sqrt_pos_of_pos hδ) with
    ⟨c, hc⟩
  refine ⟨c, ?_⟩
  simpa [Real.sq_sqrt hδ.le] using hc

def nymanBeurlingConcreteApprox : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ c : ℝ →₀ ℝ,
      (∫ x : ℝ,
        (1 - c.sum fun a r => r * fractionalPartKernel a x) *
          (1 - c.sum fun a r => r * fractionalPartKernel a x) ∂
            (volume.restrict (Set.Ioo (0 : ℝ) 1))) < δ

/-- Allowing arbitrary real parameters makes the unrestricted approximation
predicate unconditional: opposite parameters sum to one almost everywhere. -/
theorem nymanBeurlingConcreteApprox_unconditional :
    nymanBeurlingConcreteApprox := by
  intro δ hδ
  let c : ℝ →₀ ℝ := Finsupp.single 1 1 + Finsupp.single (-1) 1
  refine ⟨c, ?_⟩
  let exceptional : Set ℝ := Set.range fun z : ℤ => ((z : ℝ)⁻¹)
  have hexceptional_countable : exceptional.Countable := Set.countable_range _
  have hexceptional_zero :
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) exceptional = 0 :=
    hexceptional_countable.measure_zero _
  have hae_not_exceptional :
      ∀ᵐ x ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)), x ∉ exceptional :=
    measure_eq_zero_iff_ae_notMem.mp hexceptional_zero
  have hintegrand :
      (fun x : ℝ =>
        (1 - c.sum fun a r => r * fractionalPartKernel a x) *
          (1 - c.sum fun a r => r * fractionalPartKernel a x))
        =ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 1)] 0 := by
    filter_upwards [hae_not_exceptional] with x hx
    have hfract : Int.fract (1 / x) ≠ 0 := by
      intro hzero
      rcases Int.fract_eq_zero_iff.mp hzero with ⟨z, hz⟩
      apply hx
      refine ⟨z, ?_⟩
      simpa [one_div] using congrArg Inv.inv hz
    have hkernels :
        fractionalPartKernel 1 x + fractionalPartKernel (-1) x = 1 := by
      rw [fractionalPartKernel, fractionalPartKernel]
      have hneg : (-1 : ℝ) / x = -(1 / x) := by ring
      rw [hneg, Int.fract_neg hfract]
      ring
    have hsum : c.sum (fun a r => r * fractionalPartKernel a x) = 1 := by
      change ((Finsupp.single (1 : ℝ) (1 : ℝ) + Finsupp.single (-1 : ℝ) (1 : ℝ)).sum
        fun a r => r * fractionalPartKernel a x) = 1
      rw [Finsupp.sum_add_index' (by simp) (by intros; ring)]
      rw [Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
      simpa using hkernels
    simp [hsum]
  rw [integral_congr_ae hintegrand]
  simpa using hδ

/-- Concrete approximation with all active parameters in the unit interval. -/
def nymanBeurlingRestrictedConcreteApprox : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ c : ℝ →₀ ℝ,
      (∀ a ∈ c.support, 0 < a ∧ a ≤ 1) ∧
        (∫ x : ℝ,
          (1 - c.sum fun a r => r * fractionalPartKernel a x) *
            (1 - c.sum fun a r => r * fractionalPartKernel a x) ∂
              (volume.restrict (Set.Ioo (0 : ℝ) 1))) < δ

/-- Concrete approximation using only Baez-Duarte positive natural reciprocal parameters. -/
def nymanBeurlingBaezDuarteConcreteApprox : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ c : baezDuartePositiveNatIndex →₀ ℝ,
      (∫ x : ℝ,
        (1 - c.sum fun n r => r * fractionalPartKernel (((n : ℕ) : ℝ)⁻¹) x) *
          (1 - c.sum fun n r => r * fractionalPartKernel (((n : ℕ) : ℝ)⁻¹) x) ∂(volume.restrict
            (Set.Ioo (0 : ℝ) 1))) < δ

theorem nymanBeurlingConcreteApprox_of_restricted
    (h : nymanBeurlingRestrictedConcreteApprox) :
    nymanBeurlingConcreteApprox := by
  intro δ hδ
  rcases h δ hδ with ⟨c, _hc_support, hc⟩
  exact ⟨c, hc⟩

theorem nymanBeurlingRestrictedConcreteApprox_of_baezDuarte
    (h : nymanBeurlingBaezDuarteConcreteApprox) :
    nymanBeurlingRestrictedConcreteApprox := by
  intro δ hδ
  exact exists_real_finsupp_integral_lt_of_restricted
    (exists_restricted_finsupp_integral_lt_of_baezDuarte (h δ hδ))

theorem nymanBeurlingRestrictedConcreteApprox_of_restrictedKernelDense
    (h : nymanBeurlingRestrictedKernelDense) :
    nymanBeurlingRestrictedConcreteApprox := by
  intro δ hδ
  exact exists_real_finsupp_integral_lt_of_restricted
    (exists_restricted_finsupp_integral_lt_of_dense_tolerance h hδ)

theorem nymanBeurlingConcreteApprox_of_dense
    (h : nymanBeurlingKernelDense) :
    nymanBeurlingConcreteApprox := by
  intro δ hδ
  exact exists_finsupp_integral_one_sub_sum_fractionalPartKernel_sq_lt_of_dense_tolerance h hδ

theorem nymanBeurlingConcreteApprox_of_restrictedKernelDense
    (h : nymanBeurlingRestrictedKernelDense) :
    nymanBeurlingConcreteApprox := by
  exact nymanBeurlingConcreteApprox_of_dense (nymanBeurlingKernelDense_of_restricted h)

theorem nymanBeurlingKernelDense_iff_orthogonal_eq_bot :
    nymanBeurlingKernelDense ↔ nymanBeurlingKernelSpanᗮ = ⊥ := by
  rw [nymanBeurlingKernelDense_iff_closure_eq_top, nymanBeurlingKernelClosure]
  exact Submodule.topologicalClosure_eq_top_iff

theorem mem_nymanBeurlingKernelSpan_orthogonal_iff (f : unitIntervalL2) :
    f ∈ nymanBeurlingKernelSpanᗮ ↔ ∀ a : ℝ, ⟪fractionalPartKernelL2 a, f⟫_ℝ = 0 := by
  constructor
  · intro hf a
    exact Submodule.inner_right_of_mem_orthogonal
      (fractionalPartKernelL2_mem_nymanBeurlingKernelSpan a) hf
  · intro hf
    rw [Submodule.mem_orthogonal]
    intro u hu
    refine Submodule.span_induction (p := fun u _ => ⟪u, f⟫_ℝ = 0) ?gen ?zero ?add ?smul hu
    · rintro _ ⟨a, rfl⟩
      exact hf a
    · simp
    · intro x y hx hy hx0 hy0
      simp [inner_add_left, hx0, hy0]
    · intro c x hx hx0
      simp [inner_smul_left, hx0]

theorem nymanBeurlingKernelDense_iff_forall_inner_eq_zero_imp_eq_zero :
    nymanBeurlingKernelDense ↔
      ∀ f : unitIntervalL2, (∀ a : ℝ, ⟪fractionalPartKernelL2 a, f⟫_ℝ = 0) → f = 0 := by
  rw [nymanBeurlingKernelDense_iff_orthogonal_eq_bot]
  constructor
  · intro h f hf
    have horth : f ∈ nymanBeurlingKernelSpanᗮ :=
      (mem_nymanBeurlingKernelSpan_orthogonal_iff f).2 hf
    have hbot : f ∈ (⊥ : Submodule ℝ unitIntervalL2) := by
      rwa [h] at horth
    simpa using hbot
  · intro h
    exact (Submodule.eq_bot_iff nymanBeurlingKernelSpanᗮ).mpr (fun f hf =>
      h f ((mem_nymanBeurlingKernelSpan_orthogonal_iff f).1 hf))

theorem inner_fractionalPartKernelL2_eq_integral (a : ℝ) (f : unitIntervalL2) :
    ⟪fractionalPartKernelL2 a, f⟫_ℝ =
      ∫ x : ℝ, fractionalPartKernel a x * f x ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
  rw [L2.inner_def]
  refine integral_congr_ae ((fractionalPartKernelL2_coeFn a).mono ?_)
  intro x hx
  change ⟪(fractionalPartKernelL2 a : unitIntervalL2) x, f x⟫_ℝ =
    fractionalPartKernel a x * f x
  rw [hx]
  simp [mul_comm]

theorem nymanBeurlingKernelDense_iff_forall_integral_eq_zero_imp_eq_zero :
    nymanBeurlingKernelDense ↔
      ∀ f : unitIntervalL2,
        (∀ a : ℝ,
          (∫ x : ℝ, fractionalPartKernel a x * f x ∂
            (volume.restrict (Set.Ioo (0 : ℝ) 1))) = 0) → f = 0 := by
  rw [nymanBeurlingKernelDense_iff_forall_inner_eq_zero_imp_eq_zero]
  constructor
  · intro h f hf
    exact h f (fun a => by
      rw [inner_fractionalPartKernelL2_eq_integral]
      exact hf a)
  · intro h f hf
    exact h f (fun a => by
      rw [← inner_fractionalPartKernelL2_eq_integral]
      exact hf a)

end LeanLab.Riemann
