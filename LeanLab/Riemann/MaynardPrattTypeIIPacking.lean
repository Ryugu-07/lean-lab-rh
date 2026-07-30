import LeanLab.Riemann.MaynardPrattTypeIIRarity

set_option linter.style.header false

/-!
# Maynard--Pratt Type-II multiplicity packing

This file separates the finite greedy-packing argument from its open analytic local-zero-count
producer. The population consists of analytic-multiplicity copies, so repeated zero values are
never collapsed by passing to a set of complex numbers.
-/

namespace LeanLab.Riemann

open Complex Set
open scoped BigOperators

noncomputable section

section FinitePacking

variable {alpha : Type*}

/-- A finite family is separated at scale `H` through a real coordinate `z`. -/
def IsOrdinateSeparated
    (S : Finset alpha) (z : alpha → ℝ) (H : ℝ) : Prop :=
  (S : Set alpha).Pairwise fun i j => H ≤ |z i - z j|

/-- A selected family covers a finite population at the strict scale `H`. -/
def IsOrdinateCover
    (S U : Finset alpha) (z : alpha → ℝ) (H : ℝ) : Prop :=
  ∀ i ∈ U, ∃ j ∈ S, |z i - z j| < H

/-- Greedy finite packing: a positive-radius separated subfamily covers the entire finite
population. -/
theorem exists_ordinateSeparated_cover
    (U : Finset alpha) (z : alpha → ℝ) {H : ℝ} (hH : 0 < H) :
    ∃ S : Finset alpha,
      S ⊆ U ∧ IsOrdinateSeparated S z H ∧
        IsOrdinateCover S U z H := by
  classical
  induction U using Finset.induction_on with
  | empty =>
      refine ⟨∅, by simp, ?_, ?_⟩
      · simp [IsOrdinateSeparated]
      · simp [IsOrdinateCover]
  | @insert a U ha ih =>
      obtain ⟨S, hSU, hsep, hcover⟩ := ih
      by_cases haCover : ∃ j ∈ S, |z a - z j| < H
      · refine ⟨S, hSU.trans (Finset.subset_insert a U), hsep, ?_⟩
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hiU
        · exact haCover
        · exact hcover i hiU
      · have haS : a ∉ S := fun haMem => ha (hSU haMem)
        refine ⟨insert a S, ?_, ?_, ?_⟩
        · exact Finset.insert_subset_iff.mpr
            ⟨Finset.mem_insert_self a U,
              hSU.trans (Finset.subset_insert a U)⟩
        · rw [IsOrdinateSeparated, Finset.coe_insert,
            Set.pairwise_insert_of_notMem haS]
          refine ⟨hsep, ?_⟩
          intro j hj
          have hfar : H ≤ |z a - z j| := by
            exact le_of_not_gt fun hclose => haCover ⟨j, hj, hclose⟩
          exact ⟨hfar, by simpa only [abs_sub_comm] using hfar⟩
        · intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hiU
          · exact ⟨_, Finset.mem_insert_self _ _, by simpa using hH⟩
          · obtain ⟨j, hj, hij⟩ := hcover i hiU
            exact ⟨j, Finset.mem_insert_of_mem hj, hij⟩

/-- A cover by neighborhoods of cardinality at most `L` bounds the full population by
`L * card S`. -/
theorem card_le_mul_card_of_ordinateCover
    {U S : Finset alpha} {z : alpha → ℝ} {H : ℝ} {L : ℕ}
    (hcover : IsOrdinateCover S U z H)
    (hlocal :
      ∀ j ∈ S, (U.filter fun i => |z i - z j| < H).card ≤ L) :
    U.card ≤ L * S.card := by
  classical
  let ball : alpha → Finset alpha :=
    fun j => U.filter fun i => |z i - z j| < H
  have hsubset : U ⊆ S.biUnion ball := by
    intro i hi
    obtain ⟨j, hj, hij⟩ := hcover i hi
    exact Finset.mem_biUnion.mpr
      ⟨j, hj, Finset.mem_filter.mpr ⟨hi, hij⟩⟩
  calc
    U.card ≤ (S.biUnion ball).card := Finset.card_le_card hsubset
    _ ≤ ∑ j ∈ S, (ball j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ S, L := by
      apply Finset.sum_le_sum
      intro j hj
      exact hlocal j hj
    _ = L * S.card := by simp [Nat.mul_comm]

/-- Combined finite separated-packing theorem. The local occupancy bound remains an explicit
premise. -/
theorem exists_ordinateSeparated_card_control
    (U : Finset alpha) (z : alpha → ℝ) {H : ℝ} (hH : 0 < H) {L : ℕ}
    (hlocal :
      ∀ j ∈ U, (U.filter fun i => |z i - z j| < H).card ≤ L) :
    ∃ S : Finset alpha,
      S ⊆ U ∧ IsOrdinateSeparated S z H ∧
        IsOrdinateCover S U z H ∧ U.card ≤ L * S.card := by
  obtain ⟨S, hSU, hsep, hcover⟩ :=
    exists_ordinateSeparated_cover U z hH
  refine ⟨S, hSU, hsep, hcover, ?_⟩
  apply card_le_mul_card_of_ordinateCover hcover
  intro j hj
  exact hlocal j (hSU hj)

end FinitePacking

/-- The zero value carried by one analytic-multiplicity Type-II index. -/
def maynardPrattTypeIIZeroValue
    (T sigma : ℝ) : MaynardPrattTypeIIZeroIndex T sigma → ℂ :=
  fun i => i.1.1

/-- Multiplicity occupancy in one strict ordinate neighborhood. -/
def maynardPrattTypeIILocalMultiplicityCount
    (T sigma H : ℝ) (center : MaynardPrattTypeIIZeroIndex T sigma) : ℕ :=
  (Finset.univ.filter fun i : MaynardPrattTypeIIZeroIndex T sigma =>
    |(maynardPrattTypeIIZeroValue T sigma i).im -
      (maynardPrattTypeIIZeroValue T sigma center).im| < H).card

/-- Multiplicity-aware source packing. The sole analytic premise is the displayed local
occupancy bound; no `O(log T)` estimate is hidden in the conclusion. -/
theorem exists_maynardPrattTypeIISeparated_card_control
    (T sigma : ℝ) {H : ℝ} (hH : 0 < H) {L : ℕ}
    (hlocal :
      ∀ center : MaynardPrattTypeIIZeroIndex T sigma,
        maynardPrattTypeIILocalMultiplicityCount T sigma H center ≤ L) :
    ∃ S : Finset (MaynardPrattTypeIIZeroIndex T sigma),
      IsOrdinateSeparated S
          (fun i => (maynardPrattTypeIIZeroValue T sigma i).im) H ∧
      IsOrdinateCover S Finset.univ
          (fun i => (maynardPrattTypeIIZeroValue T sigma i).im) H ∧
      maynardPrattTypeIIZeroCount T sigma ≤ L * S.card := by
  obtain ⟨S, hS, hsep, hcover, hcard⟩ :=
    exists_ordinateSeparated_card_control
      (Finset.univ : Finset (MaynardPrattTypeIIZeroIndex T sigma))
      (fun i => (maynardPrattTypeIIZeroValue T sigma i).im) hH
      (fun center _ => hlocal center)
  refine ⟨S, hsep, hcover, ?_⟩
  simpa only [maynardPrattTypeIIZeroCount, Finset.card_univ] using hcard

end

end LeanLab.Riemann
