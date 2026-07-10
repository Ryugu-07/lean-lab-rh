import LeanLab.Riemann.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option linter.style.header false

/-!
# Nyman-Beurling route scaffolding

This file contains compiled infrastructure for the Nyman-Beurling route. It
packages fractional-part kernels on the unit interval and the source-aligned
positive-natural family in `L²(0, infinity)`.
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

theorem finsupp_sum_mem_nymanBeurlingRestrictedKernelSpan
    (c : ℝ →₀ ℝ) (hc : ∀ a ∈ c.support, 0 < a ∧ a ≤ 1) :
    c.sum (fun a r => r • fractionalPartKernelL2 a) ∈
      nymanBeurlingRestrictedKernelSpan := by
  classical
  rw [Finsupp.sum]
  exact Submodule.sum_mem _ (fun a ha =>
    Submodule.smul_mem _ (c a)
      (fractionalPartKernelL2_mem_nymanBeurlingRestrictedKernelSpan
        (hc a ha).1 (hc a ha).2))

/-- Above the unit interval, a restricted finite kernel combination is its
coefficient-parameter moment divided by `x`. -/
theorem restricted_finsupp_sum_eq_moment_div_of_one_lt
    (c : ℝ →₀ ℝ) (hc : ∀ a ∈ c.support, 0 < a ∧ a ≤ 1)
    {x : ℝ} (hx : 1 < x) :
    c.sum (fun a r => r * fractionalPartKernel a x) =
      (c.sum fun a r => r * a) / x := by
  classical
  rw [Finsupp.sum, Finsupp.sum]
  calc
    (∑ a ∈ c.support, c a * fractionalPartKernel a x) =
        ∑ a ∈ c.support, (c a * a) / x := by
      refine Finset.sum_congr rfl (fun a ha => ?_)
      have ha_bounds := hc a ha
      have hx0 : 0 < x := lt_trans zero_lt_one hx
      have hfract : fractionalPartKernel a x = a / x := by
        rw [fractionalPartKernel, Int.fract_eq_self.mpr]
        exact ⟨(div_pos ha_bounds.1 hx0).le,
          (div_lt_one hx0).mpr (lt_of_le_of_lt ha_bounds.2 hx)⟩
      rw [hfract]
      ring
    _ = (∑ a ∈ c.support, c a * a) / x := by
      rw [Finset.sum_div]

theorem integral_Ioi_moment_div_mul_self (m : ℝ) :
    (∫ x : ℝ in Set.Ioi 1, (m / x) * (m / x)) = m ^ 2 := by
  have hrpow {x : ℝ} (hx : 0 < x) :
      x ^ (-2 : ℝ) = (x ^ (2 : ℕ))⁻¹ := by
    rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hx.le]
    exact congrArg Inv.inv (Real.rpow_natCast x 2)
  have hbase :
      (∫ x : ℝ in Set.Ioi 1, x ^ (-2 : ℝ)) = 1 := by
    have h :=
      integral_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) (c := (1 : ℝ)) (by norm_num)
    norm_num at h
    calc
      (∫ x : ℝ in Set.Ioi 1, x ^ (-2 : ℝ)) =
          ∫ x : ℝ in Set.Ioi 1, (x ^ (2 : ℕ))⁻¹ := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
        exact hrpow (lt_trans zero_lt_one hx)
      _ = 1 := h
  calc
    (∫ x : ℝ in Set.Ioi 1, (m / x) * (m / x)) =
        ∫ x : ℝ in Set.Ioi 1, m ^ 2 * x ^ (-2 : ℝ) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
      rw [hrpow (lt_trans zero_lt_one hx)]
      simp [div_eq_mul_inv, ← inv_pow]
      ring
    _ = m ^ 2 * ∫ x : ℝ in Set.Ioi 1, x ^ (-2 : ℝ) := by
      rw [integral_const_mul]
    _ = m ^ 2 := by rw [hbase, mul_one]

/-- The omitted `(1, infinity)` tail is exactly the square of the
coefficient-parameter moment. -/
theorem restricted_finsupp_tail_error_eq_moment_sq
    (c : ℝ →₀ ℝ) (hc : ∀ a ∈ c.support, 0 < a ∧ a ≤ 1) :
    (∫ x : ℝ in Set.Ioi 1,
      (c.sum fun a r => r * fractionalPartKernel a x) *
        (c.sum fun a r => r * fractionalPartKernel a x)) =
      (c.sum fun a r => r * a) ^ 2 := by
  calc
    (∫ x : ℝ in Set.Ioi 1,
      (c.sum fun a r => r * fractionalPartKernel a x) *
        (c.sum fun a r => r * fractionalPartKernel a x)) =
        ∫ x : ℝ in Set.Ioi 1,
          ((c.sum fun a r => r * a) / x) * ((c.sum fun a r => r * a) / x) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
      rw [restricted_finsupp_sum_eq_moment_div_of_one_lt c hc hx]
    _ = (c.sum fun a r => r * a) ^ 2 :=
      integral_Ioi_moment_div_mul_self _

/-- The reciprocal coefficient moment for positive-natural Baez-Duarte
approximants. -/
def baezDuarteReciprocalMoment
    (c : baezDuartePositiveNatIndex →₀ ℝ) : ℝ :=
  c.sum fun n r => r * (((n : ℕ) : ℝ)⁻¹)

/-- The squared approximation error on `(0, 1)` for a positive-natural
Baez-Duarte finite sum. -/
def baezDuarteUnitIntervalError
    (c : baezDuartePositiveNatIndex →₀ ℝ) : ℝ :=
  ∫ x : ℝ,
    (1 - c.sum fun n r => r * fractionalPartKernel (((n : ℕ) : ℝ)⁻¹) x) *
      (1 - c.sum fun n r => r * fractionalPartKernel (((n : ℕ) : ℝ)⁻¹) x) ∂
        (volume.restrict (Set.Ioo (0 : ℝ) 1))

/-- The full-line Baez-Duarte finite error split at `1`: the target is one
on `(0, 1)` and zero on `(1, infinity)`. -/
def baezDuarteSplitFullLineError
    (c : baezDuartePositiveNatIndex →₀ ℝ) : ℝ :=
  baezDuarteUnitIntervalError c +
    ∫ x : ℝ in Set.Ioi 1,
      (c.sum fun n r => r * fractionalPartKernel (((n : ℕ) : ℝ)⁻¹) x) *
        (c.sum fun n r => r * fractionalPartKernel (((n : ℕ) : ℝ)⁻¹) x)

theorem baezDuarte_finsupp_sum_eq_reciprocalMoment_div_of_one_lt
    (c : baezDuartePositiveNatIndex →₀ ℝ) {x : ℝ} (hx : 1 < x) :
    c.sum (fun n r => r * fractionalPartKernel (((n : ℕ) : ℝ)⁻¹) x) =
      baezDuarteReciprocalMoment c / x := by
  classical
  rw [baezDuarteReciprocalMoment, Finsupp.sum, Finsupp.sum]
  calc
    (∑ n ∈ c.support,
      c n * fractionalPartKernel (((n : ℕ) : ℝ)⁻¹) x) =
        ∑ n ∈ c.support, (c n * (((n : ℕ) : ℝ)⁻¹)) / x := by
      refine Finset.sum_congr rfl (fun n _hn => ?_)
      have hn_bounds := baezDuarte_reciprocal_mem_restricted n
      have hx0 : 0 < x := lt_trans zero_lt_one hx
      have hfract :
          fractionalPartKernel (((n : ℕ) : ℝ)⁻¹) x =
            (((n : ℕ) : ℝ)⁻¹) / x := by
        rw [fractionalPartKernel, Int.fract_eq_self.mpr]
        exact ⟨(div_pos hn_bounds.1 hx0).le,
          (div_lt_one hx0).mpr (lt_of_le_of_lt hn_bounds.2 hx)⟩
      rw [hfract]
      ring
    _ = (∑ n ∈ c.support, c n * (((n : ℕ) : ℝ)⁻¹)) / x := by
      rw [Finset.sum_div]

theorem baezDuarte_finsupp_tail_error_eq_reciprocalMoment_sq
    (c : baezDuartePositiveNatIndex →₀ ℝ) :
    (∫ x : ℝ in Set.Ioi 1,
      (c.sum fun n r => r * fractionalPartKernel (((n : ℕ) : ℝ)⁻¹) x) *
        (c.sum fun n r => r * fractionalPartKernel (((n : ℕ) : ℝ)⁻¹) x)) =
      baezDuarteReciprocalMoment c ^ 2 := by
  calc
    (∫ x : ℝ in Set.Ioi 1,
      (c.sum fun n r => r * fractionalPartKernel (((n : ℕ) : ℝ)⁻¹) x) *
        (c.sum fun n r => r * fractionalPartKernel (((n : ℕ) : ℝ)⁻¹) x)) =
        ∫ x : ℝ in Set.Ioi 1,
          (baezDuarteReciprocalMoment c / x) *
            (baezDuarteReciprocalMoment c / x) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
      rw [baezDuarte_finsupp_sum_eq_reciprocalMoment_div_of_one_lt c hx]
    _ = baezDuarteReciprocalMoment c ^ 2 :=
      integral_Ioi_moment_div_mul_self _

theorem baezDuarteSplitFullLineError_eq_unitInterval_add_moment_sq
    (c : baezDuartePositiveNatIndex →₀ ℝ) :
    baezDuarteSplitFullLineError c =
      baezDuarteUnitIntervalError c + baezDuarteReciprocalMoment c ^ 2 := by
  rw [baezDuarteSplitFullLineError,
    baezDuarte_finsupp_tail_error_eq_reciprocalMoment_sq]

/-- Positive-natural Baez-Duarte approximation with the full-line tail
retained in split integral form. -/
def nymanBeurlingBaezDuarteFullLineConcreteApprox : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ c : baezDuartePositiveNatIndex →₀ ℝ,
      baezDuarteSplitFullLineError c < δ

theorem nymanBeurlingBaezDuarteFullLineConcreteApprox_iff :
    nymanBeurlingBaezDuarteFullLineConcreteApprox ↔
      ∀ δ : ℝ, 0 < δ →
        ∃ c : baezDuartePositiveNatIndex →₀ ℝ,
          baezDuarteUnitIntervalError c + baezDuarteReciprocalMoment c ^ 2 < δ := by
  constructor
  · intro h δ hδ
    rcases h δ hδ with ⟨c, hc⟩
    exact ⟨c, by rwa [baezDuarteSplitFullLineError_eq_unitInterval_add_moment_sq] at hc⟩
  · intro h δ hδ
    rcases h δ hδ with ⟨c, hc⟩
    exact ⟨c, by rwa [baezDuarteSplitFullLineError_eq_unitInterval_add_moment_sq]⟩

/-- The real Hilbert space `L²(0, infinity)` used by the Baez-Duarte criterion. -/
abbrev positiveHalfLineL2 : Type :=
  Lp ℝ (2 : ℝ≥0∞) (volume.restrict (Set.Ioi (0 : ℝ)))

/-- The indicator of `(0, 1]`, viewed as a real-valued function. -/
def baezDuarteTargetFunction (x : ℝ) : ℝ :=
  Set.Ioc (0 : ℝ) 1 |>.indicator (fun _ => 1) x

theorem baezDuarteTargetFunction_memLp_two_positiveHalfLine :
    MemLp baezDuarteTargetFunction (2 : ℝ≥0∞)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  change MemLp (Set.Ioc (0 : ℝ) 1 |>.indicator (fun _ => (1 : ℝ)))
    (2 : ℝ≥0∞) (volume.restrict (Set.Ioi (0 : ℝ)))
  apply memLp_indicator_const
  · exact measurableSet_Ioc
  · right
    simp

/-- A fractional-part kernel with parameter in `(0, 1]` belongs to the
full positive-half-line `L²` space. -/
theorem fractionalPartKernel_memLp_two_positiveHalfLine
    {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    MemLp (fractionalPartKernel a) (2 : ℝ≥0∞)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  rw [memLp_two_iff_integrable_sq
    (measurable_fractionalPartKernel a).aestronglyMeasurable]
  change IntegrableOn (fun x : ℝ => fractionalPartKernel a x ^ 2)
    (Set.Ioi (0 : ℝ)) volume
  rw [← Set.Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  apply IntegrableOn.union
  · have hlocal :
        MemLp (fractionalPartKernel a) (2 : ℝ≥0∞)
          (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
      refine MemLp.of_bound
        (measurable_fractionalPartKernel a).aestronglyMeasurable 1 ?_
      exact ae_of_all _ (fun x => norm_fractionalPartKernel_le_one a x)
    exact (memLp_two_iff_integrable_sq
      (measurable_fractionalPartKernel a).aestronglyMeasurable).mp hlocal
  · have hbase : IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ)) (Set.Ioi 1) volume :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
    have hscaled :
        IntegrableOn (fun x : ℝ => a ^ 2 * x ^ (-2 : ℝ)) (Set.Ioi 1) volume :=
      hbase.const_mul (a ^ 2)
    refine hscaled.congr_fun ?_ measurableSet_Ioi
    intro x hx
    change a ^ 2 * x ^ (-2 : ℝ) = fractionalPartKernel a x ^ 2
    have hx0 : 0 < x := lt_trans zero_lt_one hx
    have hfract : fractionalPartKernel a x = a / x := by
      rw [fractionalPartKernel, Int.fract_eq_self.mpr]
      exact ⟨(div_pos ha0 hx0).le,
        (div_lt_one hx0).mpr (lt_of_le_of_lt ha1 hx)⟩
    rw [hfract]
    have hrpow : x ^ (-2 : ℝ) = (x ^ (2 : ℕ))⁻¹ := by
      rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hx0.le]
      exact congrArg Inv.inv (Real.rpow_natCast x 2)
    rw [hrpow]
    field_simp

/-- The target indicator as an element of `L²(0, infinity)`. -/
def baezDuarteTargetL2 : positiveHalfLineL2 :=
  baezDuarteTargetFunction_memLp_two_positiveHalfLine.toLp
    baezDuarteTargetFunction

theorem baezDuarteTargetL2_coeFn :
    baezDuarteTargetL2
      =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] baezDuarteTargetFunction := by
  exact MemLp.coeFn_toLp baezDuarteTargetFunction_memLp_two_positiveHalfLine

/-- The positive-natural reciprocal kernel as an element of
`L²(0, infinity)`. -/
def baezDuarteKernelL2
    (n : baezDuartePositiveNatIndex) : positiveHalfLineL2 :=
  (fractionalPartKernel_memLp_two_positiveHalfLine
    (baezDuarte_reciprocal_mem_restricted n).1
    (baezDuarte_reciprocal_mem_restricted n).2).toLp
      (fractionalPartKernel (((n : ℕ) : ℝ)⁻¹))

theorem baezDuarteKernelL2_coeFn (n : baezDuartePositiveNatIndex) :
    baezDuarteKernelL2 n
      =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        fractionalPartKernel (((n : ℕ) : ℝ)⁻¹) := by
  exact MemLp.coeFn_toLp
    (fractionalPartKernel_memLp_two_positiveHalfLine
      (baezDuarte_reciprocal_mem_restricted n).1
      (baezDuarte_reciprocal_mem_restricted n).2)

/-- The real finite span of the positive-natural Baez-Duarte kernels. -/
def baezDuarteKernelSpan : Submodule ℝ positiveHalfLineL2 :=
  Submodule.span ℝ (Set.range baezDuarteKernelL2)

/-- The closure of the positive-natural kernel span in `L²(0, infinity)`. -/
def baezDuarteKernelClosure : Submodule ℝ positiveHalfLineL2 :=
  baezDuarteKernelSpan.topologicalClosure

theorem baezDuarteKernelClosure_coe :
    (baezDuarteKernelClosure : Set positiveHalfLineL2) =
      closure (baezDuarteKernelSpan : Set positiveHalfLineL2) := by
  exact Submodule.topologicalClosure_coe baezDuarteKernelSpan

theorem mem_baezDuarteKernelSpan_iff_exists_finsupp_sum
    (g : positiveHalfLineL2) :
    g ∈ baezDuarteKernelSpan ↔
      ∃ c : baezDuartePositiveNatIndex →₀ ℝ,
        (c.sum fun n r => r • baezDuarteKernelL2 n) = g := by
  rw [baezDuarteKernelSpan]
  exact Finsupp.mem_span_range_iff_exists_finsupp

theorem baezDuarteTargetL2_mem_closure_iff_norm :
    baezDuarteTargetL2 ∈ baezDuarteKernelClosure ↔
      ∀ ε : ℝ, 0 < ε →
        ∃ c : baezDuartePositiveNatIndex →₀ ℝ,
          ‖baezDuarteTargetL2 -
            (c.sum fun n r => r • baezDuarteKernelL2 n)‖ < ε := by
  constructor
  · intro h ε hε
    have hmetric :
        baezDuarteTargetL2 ∈ closure
          (baezDuarteKernelSpan : Set positiveHalfLineL2) := by
      rwa [← baezDuarteKernelClosure_coe]
    rcases (Metric.mem_closure_iff.mp hmetric) ε hε with ⟨g, hgspan, hgdist⟩
    rcases (mem_baezDuarteKernelSpan_iff_exists_finsupp_sum g).mp hgspan with
      ⟨c, hc⟩
    exact ⟨c, by simpa [dist_eq_norm, hc] using hgdist⟩
  · intro h
    have hmetric :
        baezDuarteTargetL2 ∈ closure
          (baezDuarteKernelSpan : Set positiveHalfLineL2) := by
      exact Metric.mem_closure_iff.mpr (fun ε hε => by
        rcases h ε hε with ⟨c, hc⟩
        refine ⟨c.sum fun n r => r • baezDuarteKernelL2 n, ?_, ?_⟩
        · exact (mem_baezDuarteKernelSpan_iff_exists_finsupp_sum _).mpr ⟨c, rfl⟩
        · simpa [dist_eq_norm] using hc)
    change baezDuarteTargetL2 ∈ (baezDuarteKernelClosure : Set positiveHalfLineL2)
    rw [baezDuarteKernelClosure_coe]
    exact hmetric

theorem baezDuarte_finsupp_sum_kernelL2_coeFn
    (c : baezDuartePositiveNatIndex →₀ ℝ) :
    (↑↑(c.sum fun n r => r • baezDuarteKernelL2 n) : ℝ → ℝ)
      =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        fun x : ℝ => c.sum fun n r =>
          r * fractionalPartKernel (((n : ℕ) : ℝ)⁻¹) x := by
  classical
  rw [Finsupp.sum]
  refine (Lp.coeFn_fun_finsetSum c.support fun n =>
    c n • baezDuarteKernelL2 n).trans ?_
  have hfun :
      (fun x : ℝ => ∑ n ∈ c.support,
          ((c n • baezDuarteKernelL2 n : positiveHalfLineL2) : ℝ → ℝ) x)
        =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
          (∑ n ∈ c.support,
            ((c n • baezDuarteKernelL2 n : positiveHalfLineL2) : ℝ → ℝ)) := by
    exact ae_of_all _ fun x => by
      simp [Finset.sum_apply]
  refine hfun.trans ?_
  refine (eventuallyEq_sum
    (s := c.support) (l := ae (volume.restrict (Set.Ioi (0 : ℝ))))
    (fun n _hn => by
      refine (Lp.coeFn_smul (c n) (baezDuarteKernelL2 n)).trans ?_
      exact (baezDuarteKernelL2_coeFn n).const_smul (c n))).trans ?_
  exact ae_of_all _ fun x => by
    simp [Pi.smul_apply, Finset.sum_apply, Finsupp.sum]

theorem baezDuarteTarget_sub_finsupp_sum_coeFn
    (c : baezDuartePositiveNatIndex →₀ ℝ) :
    (baezDuarteTargetL2 -
        (c.sum fun n r => r • baezDuarteKernelL2 n))
      =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        fun x : ℝ => baezDuarteTargetFunction x -
          c.sum fun n r => r * fractionalPartKernel (((n : ℕ) : ℝ)⁻¹) x := by
  refine (Lp.coeFn_sub baezDuarteTargetL2
    (c.sum fun n r => r • baezDuarteKernelL2 n)).trans ?_
  exact baezDuarteTargetL2_coeFn.sub
    (baezDuarte_finsupp_sum_kernelL2_coeFn c)

theorem positiveHalfLineL2_norm_sq_eq_integral_mul_self
    (f : positiveHalfLineL2) :
    ‖f‖ ^ 2 = ∫ x : ℝ, f x * f x ∂
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  rw [norm_sq_eq_re_inner (𝕜 := ℝ) f, L2.inner_def]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp [Real.norm_eq_abs, sq]

/-- The squared whole-space error before splitting the positive half-line at
`1`. -/
def baezDuarteWholeLineError
    (c : baezDuartePositiveNatIndex →₀ ℝ) : ℝ :=
  ∫ x : ℝ,
    (baezDuarteTargetFunction x -
      c.sum fun n r => r * fractionalPartKernel (((n : ℕ) : ℝ)⁻¹) x) ^ 2 ∂
        (volume.restrict (Set.Ioi (0 : ℝ)))

theorem norm_sub_baezDuarte_sum_sq_eq_wholeLineError
    (c : baezDuartePositiveNatIndex →₀ ℝ) :
    ‖baezDuarteTargetL2 -
      (c.sum fun n r => r • baezDuarteKernelL2 n)‖ ^ 2 =
        baezDuarteWholeLineError c := by
  rw [positiveHalfLineL2_norm_sq_eq_integral_mul_self]
  rw [baezDuarteWholeLineError]
  refine integral_congr_ae
    ((baezDuarteTarget_sub_finsupp_sum_coeFn c).mono ?_)
  intro x hx
  simpa [pow_two] using congrArg (fun y : ℝ => y * y) hx

/-- The actual `L²(0, infinity)` error is exactly the split finite error from
the source-aligned predicate. -/
theorem baezDuarteWholeLineError_eq_split
    (c : baezDuartePositiveNatIndex →₀ ℝ) :
    baezDuarteWholeLineError c = baezDuarteSplitFullLineError c := by
  let F : ℝ → ℝ := fun x =>
    (baezDuarteTargetFunction x -
      c.sum fun n r => r * fractionalPartKernel (((n : ℕ) : ℝ)⁻¹) x) ^ 2
  let fL2 : positiveHalfLineL2 :=
    baezDuarteTargetL2 -
      (c.sum fun n r => r • baezDuarteKernelL2 n)
  have hrep : (fun x : ℝ => fL2 x ^ 2)
      =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] F := by
    filter_upwards [baezDuarteTarget_sub_finsupp_sum_coeFn c] with x hx
    exact congrArg (fun y : ℝ => y ^ 2) hx
  have hF : Integrable F (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have hf : Integrable (fun x : ℝ => fL2 x ^ 2)
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
      (memLp_two_iff_integrable_sq (Lp.memLp fL2).1).mp (Lp.memLp fL2)
    exact hf.congr hrep
  have hIoc : Integrable F (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    hF.mono_measure (Measure.restrict_mono (by intro x hx; exact hx.1) le_rfl)
  have hIoi : Integrable F (volume.restrict (Set.Ioi (1 : ℝ))) :=
    hF.mono_measure (Measure.restrict_mono
      (by intro x hx
          change (1 : ℝ) < x at hx
          exact lt_trans zero_lt_one hx) le_rfl)
  have hmeasure :
      volume.restrict (Set.Ioi (0 : ℝ)) =
        volume.restrict (Set.Ioc (0 : ℝ) 1) +
          volume.restrict (Set.Ioi (1 : ℝ)) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
    exact Measure.restrict_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
  rw [baezDuarteWholeLineError]
  change (∫ x : ℝ, F x ∂(volume.restrict (Set.Ioi (0 : ℝ)))) = _
  rw [hmeasure, integral_add_measure hIoc hIoi]
  rw [baezDuarteSplitFullLineError]
  congr 1
  · rw [baezDuarteUnitIntervalError]
    rw [← integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
    simp [F, baezDuarteTargetFunction, hx, pow_two]
  · refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    change (1 : ℝ) < x at hx
    simp [F, baezDuarteTargetFunction, not_le_of_gt hx, pow_two]

/-- The real whole-space closure formulation and the source-aligned positive
tolerance formulation are equivalent. -/
theorem baezDuarteTargetL2_mem_closure_iff_fullLineConcreteApprox :
    baezDuarteTargetL2 ∈ baezDuarteKernelClosure ↔
      nymanBeurlingBaezDuarteFullLineConcreteApprox := by
  constructor
  · intro h δ hδ
    have hsqrt : 0 < Real.sqrt δ := Real.sqrt_pos_of_pos hδ
    rcases (baezDuarteTargetL2_mem_closure_iff_norm.mp h)
        (Real.sqrt δ) hsqrt with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [← baezDuarteWholeLineError_eq_split c,
      ← norm_sub_baezDuarte_sum_sq_eq_wholeLineError c]
    have hsq := (sq_lt_sq₀ (norm_nonneg _) hsqrt.le).mpr hc
    simpa [Real.sq_sqrt hδ.le] using hsq
  · intro h
    exact baezDuarteTargetL2_mem_closure_iff_norm.mpr (fun ε hε => by
      rcases h (ε ^ 2) (sq_pos_of_pos hε) with ⟨c, hc⟩
      refine ⟨c, ?_⟩
      have hsq :
          ‖baezDuarteTargetL2 -
            (c.sum fun n r => r • baezDuarteKernelL2 n)‖ ^ 2 < ε ^ 2 := by
        rwa [norm_sub_baezDuarte_sum_sq_eq_wholeLineError,
          baezDuarteWholeLineError_eq_split]
      exact (sq_lt_sq₀ (norm_nonneg _) hε.le).mp hsq)

/-- The restricted positive-tolerance predicate is exactly constant-one
membership in the closure of the restricted kernel span. -/
theorem unitIntervalOneL2_mem_restrictedClosure_iff_concreteApprox :
    unitIntervalOneL2 ∈ nymanBeurlingRestrictedKernelClosure ↔
      nymanBeurlingRestrictedConcreteApprox := by
  constructor
  · intro hclosure δ hδ
    have hsqrt : 0 < Real.sqrt δ := Real.sqrt_pos_of_pos hδ
    rcases (unitIntervalOneL2_mem_restrictedClosure_iff_forall_exists_dist_lt.mp
        hclosure) (Real.sqrt δ) hsqrt with
      ⟨g, hgspan, hgdist⟩
    rcases (mem_nymanBeurlingRestrictedKernelSpan_iff_exists_finsupp_sum g).mp
        hgspan with
      ⟨c, hc⟩
    have hnorm :
        ‖unitIntervalOneL2 -
          (c.sum fun a r => r • fractionalPartKernelL2 (a : ℝ))‖ < Real.sqrt δ := by
      simpa [dist_eq_norm, hc] using hgdist
    have hintegral :
        (∫ x : ℝ,
          (1 - c.sum fun a r => r * fractionalPartKernel (a : ℝ) x) *
            (1 - c.sum fun a r => r * fractionalPartKernel (a : ℝ) x) ∂
              (volume.restrict (Set.Ioo (0 : ℝ) 1))) < δ := by
      rw [← norm_sub_restricted_finsupp_sum_sq_eq_integral_concrete c]
      have hsq := (sq_lt_sq₀ (norm_nonneg _) hsqrt.le).mpr hnorm
      simpa [Real.sq_sqrt hδ.le] using hsq
    exact exists_real_finsupp_integral_lt_of_restricted ⟨c, hintegral⟩
  · intro hconcrete
    exact unitIntervalOneL2_mem_restrictedClosure_iff_forall_exists_dist_lt.mpr
      (fun ε hε => by
        rcases hconcrete (ε ^ 2) (sq_pos_of_pos hε) with ⟨c, hcsupport, hcintegral⟩
        let g : unitIntervalL2 :=
          c.sum fun a r => r • fractionalPartKernelL2 a
        refine ⟨g, finsupp_sum_mem_nymanBeurlingRestrictedKernelSpan c hcsupport, ?_⟩
        have hsq :
            ‖unitIntervalOneL2 - g‖ ^ 2 < ε ^ 2 := by
          dsimp [g]
          rw [norm_sub_finsupp_sum_fractionalPartKernelL2_sq_eq_integral_concrete c]
          exact hcintegral
        have hnorm : ‖unitIntervalOneL2 - g‖ < ε :=
          (sq_lt_sq₀ (norm_nonneg _) hε.le).mp hsq
        simpa [dist_eq_norm] using hnorm)

/-- Concrete approximation using only Baez-Duarte positive natural reciprocal parameters. -/
def nymanBeurlingBaezDuarteConcreteApprox : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ c : baezDuartePositiveNatIndex →₀ ℝ,
      (∫ x : ℝ,
        (1 - c.sum fun n r => r * fractionalPartKernel (((n : ℕ) : ℝ)⁻¹) x) *
          (1 - c.sum fun n r => r * fractionalPartKernel (((n : ℕ) : ℝ)⁻¹) x) ∂(volume.restrict
            (Set.Ioo (0 : ℝ) 1))) < δ

theorem nymanBeurlingBaezDuarteConcreteApprox_of_fullLine
    (h : nymanBeurlingBaezDuarteFullLineConcreteApprox) :
    nymanBeurlingBaezDuarteConcreteApprox := by
  intro δ hδ
  rcases h δ hδ with ⟨c, hc⟩
  have hsplit :
      baezDuarteUnitIntervalError c + baezDuarteReciprocalMoment c ^ 2 < δ := by
    rwa [baezDuarteSplitFullLineError_eq_unitInterval_add_moment_sq] at hc
  have hlocal : baezDuarteUnitIntervalError c < δ := by
    nlinarith [sq_nonneg (baezDuarteReciprocalMoment c)]
  exact ⟨c, by simpa [baezDuarteUnitIntervalError] using hlocal⟩

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
