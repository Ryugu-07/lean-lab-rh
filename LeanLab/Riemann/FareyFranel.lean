import LeanLab.Riemann.FareyMobiusWeyl
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

set_option linter.style.header false

/-!
# The ordered Farey discrepancy and Franel's finite quadratic

The source convention is the positive Farey sequence: `0 < a <= q <= N`. Thus `0 / 1` is
absent, `1 / 1` occurs once, and ranks are one-based.
-/

namespace LeanLab.Riemann

open scoped BigOperators

/-- The duplicate-free rational values of the positive Farey pairs of order `N`. -/
def fareyValues (N : ℕ) : Finset ℚ :=
  (fareyPairs N).image fareyValue

/-- The positive Farey values in increasing rational order. -/
def fareyOrderedValues (N : ℕ) : List ℚ :=
  (fareyValues N).sort

/-- The source cardinality `Phi(N)`. -/
def fareyPhi (N : ℕ) : ℕ :=
  (fareyPairs N).card

/-- The one-based lower-set rank of a rational value among the positive Farey values. -/
def fareyRankValue (N : ℕ) (x : ℚ) : ℕ :=
  ((fareyValues N).filter fun y => y ≤ x).card

/-- The one-based rank of a registered denominator--numerator pair. -/
def fareyRank (N : ℕ) (p : ℕ × ℕ) : ℕ :=
  fareyRankValue N (fareyValue p)

/-- Franel's signed discrepancy for a positive Farey pair. -/
def fareyDiscrepancy (N : ℕ) (p : ℕ × ℕ) : ℚ :=
  fareyValue p - (fareyRank N p : ℚ) / (fareyPhi N : ℚ)

/-- The exact finite sum of squared one-based Farey discrepancies. -/
def fareySquaredDiscrepancy (N : ℕ) : ℚ :=
  ∑ p ∈ fareyPairs N, fareyDiscrepancy N p ^ 2

/-- The number of terminal positive numerator-block points `a/n` at most `xi`. -/
def fareyCompleteCount (n : ℕ) (xi : ℚ) : ℕ :=
  ((Finset.Ico 1 (n + 1)).filter fun a : ℕ => (a : ℚ) / (n : ℚ) ≤ xi).card

/-- The exact terminal-block remainder `n*xi - #{1 <= a <= n | a/n <= xi}`. -/
def fareyBlockRemainder (n : ℕ) (xi : ℚ) : ℚ :=
  (n : ℚ) * xi - (fareyCompleteCount n xi : ℚ)

/-- The source endpoint convention `B₁(n*xi) = remainder(n,xi) - 1/2`. -/
def fareyCenteredRemainder (n : ℕ) (xi : ℚ) : ℚ :=
  fareyBlockRemainder n xi - 1 / 2

/-- The Mertens coefficient occurring at the block of length `n`. -/
def fareyMertensWeight (N n : ℕ) : ℚ :=
  (finiteMertens (N / n) : ℚ)

/-- The finite correlation of two terminal-block remainders over the actual Farey values. -/
def fareyRemainderCorrelation (N m n : ℕ) : ℚ :=
  ∑ p ∈ fareyPairs N,
    fareyBlockRemainder m (fareyValue p) *
      fareyBlockRemainder n (fareyValue p)

/-- The centered Bernoulli correlation over the actual positive Farey points. -/
def fareyCenteredCorrelation (N m n : ℕ) : ℚ :=
  ∑ p ∈ fareyPairs N,
    fareyCenteredRemainder m (fareyValue p) *
      fareyCenteredRemainder n (fareyValue p)

/-- The complete centered block, the modified generalized Dedekind sum `s₁₁(ab/c)`. -/
def fareyDedekindBlock (a b c : ℕ) : ℚ :=
  ∑ k ∈ Finset.Ico 1 (c + 1),
    fareyCenteredRemainder a ((k : ℚ) / (c : ℚ)) *
      fareyCenteredRemainder b ((k : ℚ) / (c : ℚ))

/-- The exact right side of the source three-term relation. -/
def fareyDedekindThreeTermRhs (a b c : ℕ) : ℚ :=
  1 / 12 *
      ((Nat.gcd a b : ℚ) ^ 2 * (c : ℚ) / ((a : ℚ) * (b : ℚ)) +
        (Nat.gcd b c : ℚ) ^ 2 * (a : ℚ) / ((b : ℚ) * (c : ℚ)) +
        (Nat.gcd c a : ℚ) ^ 2 * (b : ℚ) / ((c : ℚ) * (a : ℚ))) +
    (Nat.gcd (Nat.gcd a b) c : ℚ) / 2

/-- Kanemitsu--Yoshimoto Lemma 8, retained as an unproved source statement. -/
def FareyDedekindThreeTerm : Prop :=
  ∀ a b c : ℕ, 1 ≤ a → 1 ≤ b → 1 ≤ c →
    fareyDedekindBlock a b c +
        fareyDedekindBlock b c a +
        fareyDedekindBlock c a b =
      fareyDedekindThreeTermRhs a b c

/-- The double Mertens quadratic before the source gcd-kernel collapse. -/
def fareyMertensCorrelationQuadratic (N : ℕ) : ℚ :=
  ∑ m ∈ Finset.Ico 1 (N + 1),
    ∑ n ∈ Finset.Ico 1 (N + 1),
      fareyMertensWeight N m * fareyMertensWeight N n *
        fareyRemainderCorrelation N m n

/-- The centered double Mertens quadratic in the source proof. -/
def fareyMertensCenteredQuadratic (N : ℕ) : ℚ :=
  ∑ a ∈ Finset.Ico 1 (N + 1),
    ∑ b ∈ Finset.Ico 1 (N + 1),
      fareyMertensWeight N a * fareyMertensWeight N b *
        fareyCenteredCorrelation N a b

/-- The triple Mertens/Dedekind form obtained from the centered quadratic by Lemma 7. -/
def fareyMertensDedekindTriple (N : ℕ) : ℚ :=
  ∑ a ∈ Finset.Ico 1 (N + 1),
    ∑ b ∈ Finset.Ico 1 (N + 1),
      ∑ c ∈ Finset.Ico 1 (N + 1),
        fareyMertensWeight N a * fareyMertensWeight N b *
          fareyMertensWeight N c * fareyDedekindBlock a b c

/-- The closed double Mertens/gcd kernel in Franel's formula. -/
def fareyMertensGcdKernel (N : ℕ) : ℚ :=
  ∑ m ∈ Finset.Ico 1 (N + 1),
    ∑ n ∈ Finset.Ico 1 (N + 1),
      fareyMertensWeight N m * fareyMertensWeight N n *
        (Nat.gcd m n : ℚ) ^ 2 / ((m : ℚ) * (n : ℚ))

@[simp] theorem mem_fareyValues {N : ℕ} {x : ℚ} :
    x ∈ fareyValues N ↔ ∃ p ∈ fareyPairs N, fareyValue p = x := by
  simp [fareyValues]

theorem card_fareyValues (N : ℕ) :
    (fareyValues N).card = fareyPhi N := by
  rw [fareyValues, fareyPhi]
  exact Finset.card_image_iff.mpr fun p hp q hq =>
    fareyValue_injective_on hp hq

@[simp] theorem length_fareyOrderedValues (N : ℕ) :
    (fareyOrderedValues N).length = fareyPhi N := by
  rw [fareyOrderedValues, Finset.length_sort, card_fareyValues]

@[simp] theorem mem_fareyOrderedValues {N : ℕ} {x : ℚ} :
    x ∈ fareyOrderedValues N ↔ x ∈ fareyValues N := by
  simp [fareyOrderedValues]

theorem fareyOrderedValues_sorted (N : ℕ) :
    (fareyOrderedValues N).SortedLT := by
  exact Finset.sortedLT_sort (fareyValues N)

theorem fareyOrderedValues_nodup (N : ℕ) :
    (fareyOrderedValues N).Nodup :=
  (fareyOrderedValues_sorted N).nodup

theorem fareyRankValue_orderEmb (N : ℕ) (i : Fin (fareyPhi N)) :
    fareyRankValue N
        ((fareyValues N).orderEmbOfFin (card_fareyValues N) i) =
      (i : ℕ) + 1 := by
  let e : Fin (fareyPhi N) ↪o ℚ :=
    (fareyValues N).orderEmbOfFin (card_fareyValues N)
  have he : Finset.image e Finset.univ = fareyValues N := by
    simp [e]
  change ((fareyValues N).filter fun y => y ≤ e i).card = (i : ℕ) + 1
  rw [← he, Finset.filter_image]
  rw [Finset.card_image_iff.mpr
    e.injective.injOn]
  have hfilter :
      (Finset.univ.filter fun j => e j ≤ e i) = Finset.Iic i := by
    ext j
    simp [OrderEmbedding.le_iff_le]
  rw [hfilter]
  simp

theorem fareyRankValue_get_ordered (N : ℕ) (i : Fin (fareyPhi N)) :
    fareyRankValue N
        ((fareyOrderedValues N).get
          (Fin.cast (length_fareyOrderedValues N).symm i)) =
      (i : ℕ) + 1 := by
  simpa [fareyOrderedValues, Finset.orderEmbOfFin_apply] using
    fareyRankValue_orderEmb N i

theorem fareyRankValue_le (N : ℕ) (x : ℚ) :
    fareyRankValue N x ≤ fareyPhi N := by
  rw [fareyRankValue, ← card_fareyValues]
  exact Finset.card_filter_le _ _

theorem fareyRank_le (N : ℕ) (p : ℕ × ℕ) :
    fareyRank N p ≤ fareyPhi N :=
  fareyRankValue_le N (fareyValue p)

theorem fareyRankValue_pos {N : ℕ} {x : ℚ} (hx : x ∈ fareyValues N) :
    0 < fareyRankValue N x := by
  rw [fareyRankValue, Finset.card_pos]
  exact ⟨x, Finset.mem_filter.mpr ⟨hx, le_rfl⟩⟩

theorem fareyRank_pos {N : ℕ} {p : ℕ × ℕ} (hp : p ∈ fareyPairs N) :
    0 < fareyRank N p := by
  apply fareyRankValue_pos
  exact mem_fareyValues.mpr ⟨p, hp, rfl⟩

theorem fareyRankValue_injectiveOn (N : ℕ) :
    Set.InjOn (fareyRankValue N) ↑(fareyValues N) := by
  intro x hx y hy hxy
  let e : Fin (fareyPhi N) ↪o ℚ :=
    (fareyValues N).orderEmbOfFin (card_fareyValues N)
  have hxRange : x ∈ Set.range e := by
    rw [Finset.range_orderEmbOfFin]
    exact hx
  have hyRange : y ∈ Set.range e := by
    rw [Finset.range_orderEmbOfFin]
    exact hy
  obtain ⟨i, rfl⟩ := hxRange
  obtain ⟨j, rfl⟩ := hyRange
  have hij : (i : ℕ) + 1 = (j : ℕ) + 1 := by
    simpa [e, fareyRankValue_orderEmb] using hxy
  have : i = j := Fin.ext (Nat.add_right_cancel hij)
  exact congrArg e this

theorem fareyRank_injectiveOn (N : ℕ) :
    Set.InjOn (fareyRank N) ↑(fareyPairs N) := by
  intro p hp q hq hpq
  apply fareyValue_injective_on hp hq
  apply fareyRankValue_injectiveOn N
  · exact mem_fareyValues.mpr ⟨p, hp, rfl⟩
  · exact mem_fareyValues.mpr ⟨q, hq, rfl⟩
  exact hpq

theorem image_fareyRankValue (N : ℕ) :
    (fareyValues N).image (fareyRankValue N) =
      Finset.Ico 1 (fareyPhi N + 1) := by
  ext k
  simp only [Finset.mem_image, Finset.mem_Ico]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact
      ⟨fareyRankValue_pos hx, Nat.lt_add_one_iff.mpr (fareyRankValue_le N x)⟩
  · intro hk
    let i : Fin (fareyPhi N) := ⟨k - 1, by omega⟩
    refine
      ⟨(fareyValues N).orderEmbOfFin (card_fareyValues N) i,
        Finset.orderEmbOfFin_mem (fareyValues N) (card_fareyValues N) i, ?_⟩
    rw [fareyRankValue_orderEmb]
    simp only [i]
    omega

theorem image_fareyRank (N : ℕ) :
    (fareyPairs N).image (fareyRank N) =
      Finset.Ico 1 (fareyPhi N + 1) := by
  rw [← image_fareyRankValue]
  ext k
  simp [fareyValues, fareyRank]

theorem fareyRank_one_one {N : ℕ} (hN : 1 ≤ N) :
    fareyRank N (1, 1) = fareyPhi N := by
  have hone : (1, 1) ∈ fareyPairs N :=
    (fareyOneOne_mem_iff N).mpr hN
  have hmax : ∀ p ∈ fareyPairs N, fareyValue p ≤ fareyValue (1, 1) := by
    rintro ⟨q, a⟩ hp
    simp only [fareyValue, Nat.cast_one, div_one]
    exact (div_le_one (by
      exact_mod_cast fareyPairs_denominator_pos hp)).mpr
        (by exact_mod_cast fareyPairs_numerator_le_denominator hp)
  have hfilter :
      (fareyValues N).filter
          (fun x => x ≤ fareyValue (1, 1)) =
        fareyValues N := by
    apply Finset.filter_eq_self.mpr
    intro x hx
    obtain ⟨p, hp, rfl⟩ := mem_fareyValues.mp hx
    exact hmax p hp
  rw [fareyRank, fareyRankValue, hfilter, card_fareyValues]

@[simp] theorem fareyDiscrepancy_one_one {N : ℕ} (hN : 1 ≤ N) :
    fareyDiscrepancy N (1, 1) = 0 := by
  have hPhiPos : 0 < fareyPhi N := by
    rw [fareyPhi, Finset.card_pos]
    exact ⟨(1, 1), (fareyOneOne_mem_iff N).mpr hN⟩
  have hPhi : (fareyPhi N : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hPhiPos
  rw [fareyDiscrepancy, fareyRank_one_one hN]
  simp [fareyValue, hPhi]

@[simp] theorem fareyCompleteCount_zero (n : ℕ) :
    fareyCompleteCount n 0 = 0 := by
  rw [fareyCompleteCount, Finset.card_eq_zero]
  ext a
  simp only [Finset.mem_filter, Finset.mem_Ico, Finset.notMem_empty, iff_false]
  rintro ⟨ha, hdiv⟩
  have hn : 0 < n := lt_of_lt_of_le ha.1 (Nat.lt_add_one_iff.mp ha.2)
  have haRat : (0 : ℚ) < (a : ℚ) := by exact_mod_cast ha.1
  have hnRat : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  exact (not_le_of_gt (div_pos haRat hnRat)) hdiv

@[simp] theorem fareyCompleteCount_one (n : ℕ) :
    fareyCompleteCount n 1 = n := by
  rw [fareyCompleteCount]
  have hfilter :
      (Finset.Ico 1 (n + 1)).filter (fun a : ℕ => (a : ℚ) / (n : ℚ) ≤ 1) =
        Finset.Ico 1 (n + 1) := by
    apply Finset.filter_eq_self.mpr
    intro a ha
    have haI := Finset.mem_Ico.mp ha
    by_cases hn : n = 0
    · subst n
      omega
    · apply (div_le_one (by exact_mod_cast (Nat.zero_lt_of_ne_zero hn))).mpr
      exact_mod_cast Nat.lt_add_one_iff.mp haI.2
  rw [hfilter, Nat.card_Ico]
  omega

@[simp] theorem fareyBlockRemainder_zero (n : ℕ) :
    fareyBlockRemainder n 0 = 0 := by
  simp [fareyBlockRemainder]

@[simp] theorem fareyBlockRemainder_one (n : ℕ) :
    fareyBlockRemainder n 1 = 0 := by
  simp [fareyBlockRemainder]

@[simp] theorem fareyCenteredRemainder_zero (n : ℕ) :
    fareyCenteredRemainder n 0 = -1 / 2 := by
  norm_num [fareyCenteredRemainder]

@[simp] theorem fareyCenteredRemainder_one (n : ℕ) :
    fareyCenteredRemainder n 1 = -1 / 2 := by
  norm_num [fareyCenteredRemainder]

/-- The exact lower-interval indicator used to specialize the compiled Farey transform. -/
def fareyLEIndicator (xi : ℚ) (x : ℚ) : ℂ :=
  if x ≤ xi then 1 else 0

/-- The endpoint test used to recover `∑ M(⌊N/n⌋) = 1`. -/
def fareyEndpointIndicator (x : ℚ) : ℂ :=
  if x = 1 then 1 else 0

theorem fareyRankValue_eq_pair_filter_card (N : ℕ) (xi : ℚ) :
    fareyRankValue N xi =
      ((fareyPairs N).filter fun p => fareyValue p ≤ xi).card := by
  have hvalues :
      (fareyValues N).filter (fun x => x ≤ xi) =
        ((fareyPairs N).filter fun p => fareyValue p ≤ xi).image fareyValue := by
    ext x
    simp only [fareyValues, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨p, hp, rfl⟩, hle⟩
      exact ⟨p, ⟨hp, hle⟩, rfl⟩
    · rintro ⟨p, ⟨hp, hle⟩, rfl⟩
      exact ⟨⟨p, hp, rfl⟩, hle⟩
  rw [fareyRankValue, hvalues]
  exact Finset.card_image_iff.mpr fun p hp q hq =>
    fareyValue_injective_on (Finset.mem_filter.mp hp).1
      (Finset.mem_filter.mp hq).1

theorem fareySum_leIndicator (N : ℕ) (xi : ℚ) :
    fareySum (fareyLEIndicator xi) N = (fareyRankValue N xi : ℂ) := by
  rw [fareySum, fareyRankValue_eq_pair_filter_card]
  simp [fareyLEIndicator]

theorem fareyFullBlock_leIndicator (n : ℕ) (xi : ℚ) :
    fareyFullBlock (fareyLEIndicator xi) n = (fareyCompleteCount n xi : ℂ) := by
  rw [fareyFullBlock, fareyCompleteCount]
  simp [fareyLEIndicator]

theorem fareySum_endpointIndicator {N : ℕ} (hN : 1 ≤ N) :
    fareySum fareyEndpointIndicator N = 1 := by
  rw [fareySum]
  calc
    (∑ p ∈ fareyPairs N, fareyEndpointIndicator (fareyValue p)) =
        fareyEndpointIndicator (fareyValue (1, 1)) := by
      apply Finset.sum_eq_single_of_mem (1, 1)
        ((fareyOneOne_mem_iff N).mpr hN)
      rintro p hp hne
      have hvalue : fareyValue p ≠ 1 := by
        intro h
        apply hne
        apply fareyValue_injective_on hp ((fareyOneOne_mem_iff N).mpr hN)
        simpa [fareyValue] using h
      simp [fareyEndpointIndicator, hvalue]
    _ = 1 := by
      simp [fareyEndpointIndicator, fareyValue]

theorem fareyFullBlock_endpointIndicator {n : ℕ} (hn : 1 ≤ n) :
    fareyFullBlock fareyEndpointIndicator n = 1 := by
  rw [fareyFullBlock]
  calc
    (∑ a ∈ Finset.Ico 1 (n + 1),
        fareyEndpointIndicator ((a : ℚ) / (n : ℚ))) =
        fareyEndpointIndicator ((n : ℚ) / (n : ℚ)) := by
      apply Finset.sum_eq_single_of_mem n
        (Finset.mem_Ico.mpr ⟨hn, Nat.lt_add_one n⟩)
      intro a ha hne
      have hnRat : (n : ℚ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hn)
      have hvalue : (a : ℚ) / (n : ℚ) ≠ 1 := by
        intro h
        apply hne
        exact_mod_cast (div_eq_one_iff_eq hnRat).mp h
      simp [fareyEndpointIndicator, hvalue]
    _ = 1 := by
      simp [fareyEndpointIndicator, Nat.ne_of_gt hn]

theorem fareyRankValue_cast_eq_mertens_completeCount (N : ℕ) (xi : ℚ) :
    (fareyRankValue N xi : ℂ) =
      ∑ n ∈ Finset.Ico 1 (N + 1),
        (finiteMertens (N / n) : ℂ) * (fareyCompleteCount n xi : ℂ) := by
  rw [← fareySum_leIndicator, farey_sum_eq_mertens_transform]
  apply Finset.sum_congr rfl
  intro n hn
  rw [fareyFullBlock_leIndicator]

theorem fareyPhi_cast_eq_mertens_blocks (N : ℕ) :
    (fareyPhi N : ℂ) =
      ∑ n ∈ Finset.Ico 1 (N + 1),
        (finiteMertens (N / n) : ℂ) * (n : ℂ) := by
  have hsum :
      fareySum (fun _ : ℚ => (1 : ℂ)) N = (fareyPhi N : ℂ) := by
    rw [fareySum, fareyPhi]
    simp
  rw [← hsum, farey_sum_eq_mertens_transform]
  apply Finset.sum_congr rfl
  intro n hn
  simp [fareyFullBlock]

theorem fareyRankValue_eq_mertens_completeCount (N : ℕ) (xi : ℚ) :
    (fareyRankValue N xi : ℚ) =
      ∑ n ∈ Finset.Ico 1 (N + 1),
        fareyMertensWeight N n * (fareyCompleteCount n xi : ℚ) := by
  apply Rat.cast_injective (α := ℂ)
  simpa [fareyMertensWeight] using
    fareyRankValue_cast_eq_mertens_completeCount N xi

theorem fareyPhi_eq_mertens_blocks (N : ℕ) :
    (fareyPhi N : ℚ) =
      ∑ n ∈ Finset.Ico 1 (N + 1),
        fareyMertensWeight N n * (n : ℚ) := by
  apply Rat.cast_injective (α := ℂ)
  simpa [fareyMertensWeight] using fareyPhi_cast_eq_mertens_blocks N

theorem fareyMertensWeight_sum_cast {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Ico 1 (N + 1),
        (finiteMertens (N / n) : ℂ)) = 1 := by
  rw [← fareySum_endpointIndicator hN,
    farey_sum_eq_mertens_transform]
  apply Finset.sum_congr rfl
  intro n hn
  rw [fareyFullBlock_endpointIndicator (Finset.mem_Ico.mp hn).1]
  ring

theorem fareyMertensWeight_sum {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Ico 1 (N + 1), fareyMertensWeight N n) = 1 := by
  apply Rat.cast_injective (α := ℂ)
  simpa [fareyMertensWeight] using fareyMertensWeight_sum_cast hN

theorem fareyCenteredCorrelation_cast_eq_mertens_dedekind
    (N a b : ℕ) :
    (fareyCenteredCorrelation N a b : ℂ) =
      ∑ c ∈ Finset.Ico 1 (N + 1),
        (finiteMertens (N / c) : ℂ) * (fareyDedekindBlock a b c : ℂ) := by
  calc
    (fareyCenteredCorrelation N a b : ℂ) =
        fareySum
          (fun xi =>
            (fareyCenteredRemainder a xi : ℂ) *
              (fareyCenteredRemainder b xi : ℂ)) N := by
      simp [fareyCenteredCorrelation, fareySum]
    _ =
        ∑ c ∈ Finset.Ico 1 (N + 1),
          (finiteMertens (N / c) : ℂ) *
            fareyFullBlock
              (fun xi =>
                (fareyCenteredRemainder a xi : ℂ) *
                  (fareyCenteredRemainder b xi : ℂ)) c :=
      farey_sum_eq_mertens_transform _ _
    _ =
        ∑ c ∈ Finset.Ico 1 (N + 1),
          (finiteMertens (N / c) : ℂ) *
            (fareyDedekindBlock a b c : ℂ) := by
      apply Finset.sum_congr rfl
      intro c hc
      congr 1
      simp [fareyFullBlock, fareyDedekindBlock]

theorem fareyCenteredCorrelation_eq_mertens_dedekind
    (N a b : ℕ) :
    fareyCenteredCorrelation N a b =
      ∑ c ∈ Finset.Ico 1 (N + 1),
        fareyMertensWeight N c * fareyDedekindBlock a b c := by
  apply Rat.cast_injective (α := ℂ)
  simpa [fareyMertensWeight] using
    fareyCenteredCorrelation_cast_eq_mertens_dedekind N a b

theorem fareyDedekindBlock_comm (a b c : ℕ) :
    fareyDedekindBlock a b c = fareyDedekindBlock b a c := by
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem fareyMertensCenteredQuadratic_eq_dedekindTriple (N : ℕ) :
    fareyMertensCenteredQuadratic N =
      fareyMertensDedekindTriple N := by
  rw [fareyMertensCenteredQuadratic, fareyMertensDedekindTriple]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [fareyCenteredCorrelation_eq_mertens_dedekind]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  ring

theorem fareyMertens_remainder_sum_eq (N : ℕ) (xi : ℚ) :
    (∑ n ∈ Finset.Ico 1 (N + 1),
        fareyMertensWeight N n * fareyBlockRemainder n xi) =
      (fareyPhi N : ℚ) * xi - (fareyRankValue N xi : ℚ) := by
  calc
    (∑ n ∈ Finset.Ico 1 (N + 1),
        fareyMertensWeight N n * fareyBlockRemainder n xi) =
        (∑ n ∈ Finset.Ico 1 (N + 1),
            fareyMertensWeight N n * (n : ℚ)) * xi -
          ∑ n ∈ Finset.Ico 1 (N + 1),
            fareyMertensWeight N n * (fareyCompleteCount n xi : ℚ) := by
              simp only [fareyBlockRemainder, mul_sub, Finset.sum_sub_distrib,
                Finset.sum_mul, mul_assoc]
    _ = (fareyPhi N : ℚ) * xi - (fareyRankValue N xi : ℚ) := by
      rw [← fareyPhi_eq_mertens_blocks,
        ← fareyRankValue_eq_mertens_completeCount]

theorem fareyMertens_remainder_sum_eq_centered
    {N : ℕ} (hN : 1 ≤ N) (xi : ℚ) :
    (∑ n ∈ Finset.Ico 1 (N + 1),
        fareyMertensWeight N n * fareyBlockRemainder n xi) =
      (∑ n ∈ Finset.Ico 1 (N + 1),
          fareyMertensWeight N n * fareyCenteredRemainder n xi) +
        1 / 2 := by
  calc
    (∑ n ∈ Finset.Ico 1 (N + 1),
        fareyMertensWeight N n * fareyBlockRemainder n xi) =
        ∑ n ∈ Finset.Ico 1 (N + 1),
          fareyMertensWeight N n *
            (fareyCenteredRemainder n xi + 1 / 2) := by
      apply Finset.sum_congr rfl
      intro n hn
      simp [fareyCenteredRemainder]
    _ =
        (∑ n ∈ Finset.Ico 1 (N + 1),
            fareyMertensWeight N n * fareyCenteredRemainder n xi) +
          ∑ n ∈ Finset.Ico 1 (N + 1),
            fareyMertensWeight N n * (1 / 2) := by
      simp only [mul_add, Finset.sum_add_distrib]
    _ =
        (∑ n ∈ Finset.Ico 1 (N + 1),
            fareyMertensWeight N n * fareyCenteredRemainder n xi) +
          1 / 2 := by
      rw [← Finset.sum_mul, fareyMertensWeight_sum hN]
      ring

theorem fareyDiscrepancy_eq_mertens_remainder
    {N : ℕ} {p : ℕ × ℕ} (hp : p ∈ fareyPairs N) :
    fareyDiscrepancy N p =
      (1 / (fareyPhi N : ℚ)) *
        ∑ n ∈ Finset.Ico 1 (N + 1),
          fareyMertensWeight N n *
            fareyBlockRemainder n (fareyValue p) := by
  have hPhiPos : 0 < fareyPhi N := by
    rw [fareyPhi, Finset.card_pos]
    exact ⟨p, hp⟩
  have hPhi : (fareyPhi N : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hPhiPos
  rw [fareyMertens_remainder_sum_eq]
  simp only [fareyDiscrepancy, fareyRank]
  field_simp

theorem fareyDiscrepancy_eq_centered_mertens
    {N : ℕ} {p : ℕ × ℕ} (hN : 1 ≤ N) (hp : p ∈ fareyPairs N) :
    fareyDiscrepancy N p =
      (1 / (fareyPhi N : ℚ)) *
        ((∑ n ∈ Finset.Ico 1 (N + 1),
            fareyMertensWeight N n *
              fareyCenteredRemainder n (fareyValue p)) +
          1 / 2) := by
  rw [fareyDiscrepancy_eq_mertens_remainder hp,
    fareyMertens_remainder_sum_eq_centered hN]

theorem fareyPhi_sq_mul_discrepancy_sq
    {N : ℕ} {p : ℕ × ℕ} (hp : p ∈ fareyPairs N) :
    (fareyPhi N : ℚ) ^ 2 * fareyDiscrepancy N p ^ 2 =
      (∑ n ∈ Finset.Ico 1 (N + 1),
          fareyMertensWeight N n *
            fareyBlockRemainder n (fareyValue p)) ^ 2 := by
  have hPhiPos : 0 < fareyPhi N := by
    rw [fareyPhi, Finset.card_pos]
    exact ⟨p, hp⟩
  have hPhi : (fareyPhi N : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hPhiPos
  rw [fareyDiscrepancy_eq_mertens_remainder hp]
  field_simp

theorem fareyRemainder_square_sum_eq_correlation (N : ℕ) :
    (∑ p ∈ fareyPairs N,
        (∑ n ∈ Finset.Ico 1 (N + 1),
            fareyMertensWeight N n *
              fareyBlockRemainder n (fareyValue p)) ^ 2) =
      fareyMertensCorrelationQuadratic N := by
  have hsquare (p : ℕ × ℕ) :
      (∑ n ∈ Finset.Ico 1 (N + 1),
          fareyMertensWeight N n *
            fareyBlockRemainder n (fareyValue p)) ^ 2 =
        ∑ m ∈ Finset.Ico 1 (N + 1),
          ∑ n ∈ Finset.Ico 1 (N + 1),
            fareyMertensWeight N m * fareyMertensWeight N n *
              (fareyBlockRemainder m (fareyValue p) *
                fareyBlockRemainder n (fareyValue p)) := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  calc
    (∑ p ∈ fareyPairs N,
        (∑ n ∈ Finset.Ico 1 (N + 1),
            fareyMertensWeight N n *
              fareyBlockRemainder n (fareyValue p)) ^ 2) =
        ∑ p ∈ fareyPairs N,
          ∑ m ∈ Finset.Ico 1 (N + 1),
            ∑ n ∈ Finset.Ico 1 (N + 1),
              fareyMertensWeight N m * fareyMertensWeight N n *
                (fareyBlockRemainder m (fareyValue p) *
                  fareyBlockRemainder n (fareyValue p)) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact hsquare p
    _ =
        ∑ m ∈ Finset.Ico 1 (N + 1),
          ∑ n ∈ Finset.Ico 1 (N + 1),
            ∑ p ∈ fareyPairs N,
              fareyMertensWeight N m * fareyMertensWeight N n *
                (fareyBlockRemainder m (fareyValue p) *
                  fareyBlockRemainder n (fareyValue p)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.sum_comm]
    _ = fareyMertensCorrelationQuadratic N := by
      rw [fareyMertensCorrelationQuadratic]
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      rw [fareyRemainderCorrelation, Finset.mul_sum]

theorem fareyPhi_sq_mul_squaredDiscrepancy_eq_correlation (N : ℕ) :
    (fareyPhi N : ℚ) ^ 2 * fareySquaredDiscrepancy N =
      fareyMertensCorrelationQuadratic N := by
  rw [fareySquaredDiscrepancy, Finset.mul_sum,
    ← fareyRemainder_square_sum_eq_correlation]
  apply Finset.sum_congr rfl
  intro p hp
  exact fareyPhi_sq_mul_discrepancy_sq hp

@[simp] theorem fareyPairs_three :
    fareyPairs 3 = {(1, 1), (2, 1), (3, 1), (3, 2)} := by
  ext p
  rcases p with ⟨q, a⟩
  simp only [mem_fareyPairs, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq]
  constructor
  · rintro ⟨hq, hq3, ha, haq, hcop⟩
    interval_cases q <;> interval_cases a <;> norm_num at *
  · intro h
    rcases h with h | h | h | h
    all_goals rcases h with ⟨rfl, rfl⟩
    all_goals norm_num

@[simp] theorem fareyPhi_zero :
    fareyPhi 0 = 0 := by
  simp [fareyPhi]

@[simp] theorem fareyPhi_one :
    fareyPhi 1 = 1 := by
  simp [fareyPhi]

@[simp] theorem fareyPhi_two :
    fareyPhi 2 = 2 := by
  simp [fareyPhi]

@[simp] theorem fareyPhi_three :
    fareyPhi 3 = 4 := by
  simp [fareyPhi]

@[simp] theorem fareySquaredDiscrepancy_zero :
    fareySquaredDiscrepancy 0 = 0 := by
  norm_num [fareySquaredDiscrepancy, fareyPairs]

@[simp] theorem fareySquaredDiscrepancy_one :
    fareySquaredDiscrepancy 1 = 0 := by
  norm_num [fareySquaredDiscrepancy, fareyDiscrepancy, fareyRank,
    fareyRankValue, fareyPhi, fareyValues, fareyValue,
    Finset.filter_insert, Finset.filter_singleton]

@[simp] theorem fareySquaredDiscrepancy_two :
    fareySquaredDiscrepancy 2 = 0 := by
  norm_num [fareySquaredDiscrepancy, fareyDiscrepancy, fareyRank,
    fareyRankValue, fareyPhi, fareyValues, fareyValue,
    Finset.filter_insert, Finset.filter_singleton]

@[simp] theorem fareySquaredDiscrepancy_three :
    fareySquaredDiscrepancy 3 = 1 / 72 := by
  norm_num [fareySquaredDiscrepancy, fareyDiscrepancy, fareyRank,
    fareyRankValue, fareyPhi, fareyValues, fareyValue,
    Finset.filter_insert, Finset.filter_singleton]

@[simp] theorem fareyMertensGcdKernel_one :
    fareyMertensGcdKernel 1 = 1 := by
  norm_num [fareyMertensGcdKernel, fareyMertensWeight]

@[simp] theorem fareyMertensGcdKernel_two :
    fareyMertensGcdKernel 2 = 1 := by
  norm_num [fareyMertensGcdKernel, fareyMertensWeight,
    Finset.sum_Ico_succ_top]

@[simp] theorem fareyMertensGcdKernel_three :
    fareyMertensGcdKernel 3 = 5 / 3 := by
  norm_num [fareyMertensGcdKernel, fareyMertensWeight,
    Finset.sum_Ico_succ_top]

theorem fareyFranel_control_one :
    fareySquaredDiscrepancy 1 =
      1 / (12 * (fareyPhi 1 : ℚ)) *
        (fareyMertensGcdKernel 1 - 1) := by
  norm_num

theorem fareyFranel_control_two :
    fareySquaredDiscrepancy 2 =
      1 / (12 * (fareyPhi 2 : ℚ)) *
        (fareyMertensGcdKernel 2 - 1) := by
  norm_num

theorem fareyFranel_control_three :
    fareySquaredDiscrepancy 3 =
      1 / (12 * (fareyPhi 3 : ℚ)) *
        (fareyMertensGcdKernel 3 - 1) := by
  norm_num

theorem fareyDedekindThreeTerm_control_one :
    fareyDedekindBlock 1 1 1 +
        fareyDedekindBlock 1 1 1 +
        fareyDedekindBlock 1 1 1 =
      fareyDedekindThreeTermRhs 1 1 1 := by
  norm_num [fareyDedekindBlock, fareyDedekindThreeTermRhs,
    fareyCenteredRemainder, fareyBlockRemainder, fareyCompleteCount,
    Finset.sum_Ico_succ_top, Finset.filter_insert, Finset.filter_singleton]

theorem fareyDedekindThreeTerm_control_one_two_three :
    fareyDedekindBlock 1 2 3 +
        fareyDedekindBlock 2 3 1 +
        fareyDedekindBlock 3 1 2 =
      fareyDedekindThreeTermRhs 1 2 3 := by
  norm_num [fareyDedekindBlock, fareyDedekindThreeTermRhs,
    fareyCenteredRemainder, fareyBlockRemainder, fareyCompleteCount,
    show Finset.Ico 1 3 = {1, 2} by decide,
    show Finset.Ico 1 4 = {1, 2, 3} by decide,
    Finset.sum_Ico_succ_top, Finset.filter_insert, Finset.filter_singleton]

theorem fareyDedekindThreeTerm_control_two :
    fareyDedekindBlock 2 2 2 +
        fareyDedekindBlock 2 2 2 +
        fareyDedekindBlock 2 2 2 =
      fareyDedekindThreeTermRhs 2 2 2 := by
  norm_num [fareyDedekindBlock, fareyDedekindThreeTermRhs,
    fareyCenteredRemainder, fareyBlockRemainder, fareyCompleteCount,
    show Finset.Ico 1 3 = {1, 2} by decide,
    Finset.sum_Ico_succ_top, Finset.filter_insert, Finset.filter_singleton]

/-- Aggregate certificate for the compiled portion of the Franel source reconstruction. -/
structure FareyFranelCorrelationCertificate : Prop where
  orderedRank :
    ∀ (N : ℕ) (i : Fin (fareyPhi N)),
      fareyRankValue N
          ((fareyOrderedValues N).get
            (Fin.cast (length_fareyOrderedValues N).symm i)) =
        (i : ℕ) + 1
  rankImage :
    ∀ N : ℕ,
      (fareyPairs N).image (fareyRank N) =
        Finset.Ico 1 (fareyPhi N + 1)
  terminalDiscrepancy :
    ∀ {N : ℕ}, 1 ≤ N → fareyDiscrepancy N (1, 1) = 0
  pointwiseMertens :
    ∀ {N : ℕ} {p : ℕ × ℕ}, p ∈ fareyPairs N →
      fareyDiscrepancy N p =
        (1 / (fareyPhi N : ℚ)) *
          ∑ n ∈ Finset.Ico 1 (N + 1),
            fareyMertensWeight N n *
              fareyBlockRemainder n (fareyValue p)
  centeredPointwise :
    ∀ {N : ℕ} {p : ℕ × ℕ}, 1 ≤ N → p ∈ fareyPairs N →
      fareyDiscrepancy N p =
        (1 / (fareyPhi N : ℚ)) *
          ((∑ n ∈ Finset.Ico 1 (N + 1),
              fareyMertensWeight N n *
                fareyCenteredRemainder n (fareyValue p)) +
            1 / 2)
  squaredCorrelation :
    ∀ N : ℕ,
      (fareyPhi N : ℚ) ^ 2 * fareySquaredDiscrepancy N =
        fareyMertensCorrelationQuadratic N
  sourceLemmaSeven :
    ∀ N a b : ℕ,
      fareyCenteredCorrelation N a b =
        ∑ c ∈ Finset.Ico 1 (N + 1),
          fareyMertensWeight N c * fareyDedekindBlock a b c
  endpointMertens :
    ∀ {N : ℕ}, 1 ≤ N →
      (∑ n ∈ Finset.Ico 1 (N + 1), fareyMertensWeight N n) = 1
  franelControls :
    fareySquaredDiscrepancy 1 =
        1 / (12 * (fareyPhi 1 : ℚ)) *
          (fareyMertensGcdKernel 1 - 1) ∧
      fareySquaredDiscrepancy 2 =
        1 / (12 * (fareyPhi 2 : ℚ)) *
          (fareyMertensGcdKernel 2 - 1) ∧
      fareySquaredDiscrepancy 3 =
        1 / (12 * (fareyPhi 3 : ℚ)) *
          (fareyMertensGcdKernel 3 - 1)
  dedekindControls :
    fareyDedekindBlock 1 1 1 +
          fareyDedekindBlock 1 1 1 +
          fareyDedekindBlock 1 1 1 =
        fareyDedekindThreeTermRhs 1 1 1 ∧
      fareyDedekindBlock 1 2 3 +
          fareyDedekindBlock 2 3 1 +
          fareyDedekindBlock 3 1 2 =
        fareyDedekindThreeTermRhs 1 2 3 ∧
      fareyDedekindBlock 2 2 2 +
          fareyDedekindBlock 2 2 2 +
          fareyDedekindBlock 2 2 2 =
        fareyDedekindThreeTermRhs 2 2 2

theorem fareyFranelCorrelation_endpoint :
    FareyFranelCorrelationCertificate where
  orderedRank := fareyRankValue_get_ordered
  rankImage := image_fareyRank
  terminalDiscrepancy := fareyDiscrepancy_one_one
  pointwiseMertens := fareyDiscrepancy_eq_mertens_remainder
  centeredPointwise := fareyDiscrepancy_eq_centered_mertens
  squaredCorrelation := fareyPhi_sq_mul_squaredDiscrepancy_eq_correlation
  sourceLemmaSeven := fareyCenteredCorrelation_eq_mertens_dedekind
  endpointMertens := fareyMertensWeight_sum
  franelControls :=
    ⟨fareyFranel_control_one, fareyFranel_control_two,
      fareyFranel_control_three⟩
  dedekindControls :=
    ⟨fareyDedekindThreeTerm_control_one,
      fareyDedekindThreeTerm_control_one_two_three,
      fareyDedekindThreeTerm_control_two⟩

end LeanLab.Riemann
