import LeanLab.Riemann.RedhefferMertensDeterminant
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Data.Nat.Log
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

set_option linter.style.header false

/-!
# The characteristic polynomial of the Redheffer matrix

This file reconstructs Vaughan's ordered-factor expansion of the Redheffer characteristic
polynomial. The row transform is performed over `ℤ[X]` after clearing every power of `X - 1`,
so the unit eigenvalue and its algebraic multiplicity are retained.
-/

namespace LeanLab.Riemann

open scoped BigOperators
open Polynomial

/-- The number of ordered factorizations of `m` into `k` factors at least two.

The recursion splits off the last factor. At depth zero only the empty product `m = 1` is
counted. -/
def redhefferOrderedFactorCount : ℕ → ℕ → ℕ
  | 0, m => if m = 1 then 1 else 0
  | k + 1, m =>
      ∑ d ∈ Finset.range m, if d ∣ m then redhefferOrderedFactorCount k d else 0

@[simp] theorem redhefferOrderedFactorCount_zero (m : ℕ) :
    redhefferOrderedFactorCount 0 m = if m = 1 then 1 else 0 := by
  rfl

theorem redhefferOrderedFactorCount_succ (k m : ℕ) :
    redhefferOrderedFactorCount (k + 1) m =
      ∑ d ∈ Finset.range m,
        if d ∣ m then redhefferOrderedFactorCount k d else 0 := by
  rfl

@[simp] theorem redhefferOrderedFactorCount_zero_right (k : ℕ) :
    redhefferOrderedFactorCount k 0 = 0 := by
  cases k with
  | zero => simp [redhefferOrderedFactorCount]
  | succ k => simp [redhefferOrderedFactorCount]

@[simp] theorem redhefferOrderedFactorCount_one_succ (k : ℕ) :
    redhefferOrderedFactorCount (k + 1) 1 = 0 := by
  simp [redhefferOrderedFactorCount]

theorem redhefferOrderedFactorCount_one_of_one_lt {m : ℕ} (hm : 1 < m) :
    redhefferOrderedFactorCount 1 m = 1 := by
  simp only [redhefferOrderedFactorCount_succ, redhefferOrderedFactorCount_zero]
  rw [Finset.sum_eq_single 1]
  · simp
  · intro d hd hd1
    simp only [Finset.mem_range] at hd
    simp [hd1]
  · simp [hm]

theorem redhefferOrderedFactorCount_eq_zero_of_lt_pow_two {k m : ℕ}
    (hm : m < 2 ^ k) :
    redhefferOrderedFactorCount k m = 0 := by
  induction k generalizing m with
  | zero =>
      have : m = 0 := by simpa using hm
      subst m
      simp
  | succ k ih =>
      rw [redhefferOrderedFactorCount_succ]
      apply Finset.sum_eq_zero
      intro d hd
      simp only [Finset.mem_range] at hd
      by_cases hdiv : d ∣ m
      · have hmpos : 0 < m := by omega
        have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdiv hmpos
        obtain ⟨c, rfl⟩ := hdiv
        have hc : 1 < c := (Nat.lt_mul_iff_one_lt_right hdpos).mp hd
        have htwo : 2 * d ≤ d * c := by
          simpa [Nat.mul_comm] using Nat.mul_le_mul_left d hc
        have hpow : d < 2 ^ k := by
          rw [pow_succ] at hm
          omega
        simp [ih hpow]
      · simp [hdiv]

theorem redhefferOrderedFactorCount_eq_zero_above_log {N k m : ℕ}
    (hm : m ≤ N) (hk : Nat.log 2 N < k) :
    redhefferOrderedFactorCount k m = 0 := by
  apply redhefferOrderedFactorCount_eq_zero_of_lt_pow_two
  exact hm.trans_lt (Nat.lt_pow_of_log_lt Nat.one_lt_two hk)

theorem redhefferOrderedFactorCount_pow_two_pos (k : ℕ) :
    0 < redhefferOrderedFactorCount k (2 ^ k) := by
  induction k with
  | zero => simp [redhefferOrderedFactorCount]
  | succ k ih =>
      rw [redhefferOrderedFactorCount_succ]
      have hmem : 2 ^ k ∈ Finset.range (2 ^ (k + 1)) := by
        simp only [Finset.mem_range, pow_succ]
        have hpos : 0 < 2 ^ k := pow_pos (by norm_num : (0 : ℕ) < 2) _
        omega
      have hdiv : 2 ^ k ∣ 2 ^ (k + 1) := by
        rw [pow_succ]
        exact dvd_mul_right _ _
      have hle :
          redhefferOrderedFactorCount k (2 ^ k) ≤
            ∑ d ∈ Finset.range (2 ^ (k + 1)),
              if d ∣ 2 ^ (k + 1) then redhefferOrderedFactorCount k d else 0 := by
        have hsingle :=
          Finset.single_le_sum
            (s := Finset.range (2 ^ (k + 1)))
            (f := fun d =>
              if d ∣ 2 ^ (k + 1) then redhefferOrderedFactorCount k d else 0)
            (fun d hd => Nat.zero_le _)
            hmem
        simpa [hdiv] using hsingle
      exact ih.trans_le hle

/-- Vaughan's coefficient `S_k(N)`, the number of ordered `k`-factor products at most `N`. -/
def redhefferFactorSum (k N : ℕ) : ℕ :=
  ∑ m : Fin N, redhefferOrderedFactorCount k (m.1 + 1)

theorem redhefferFactorSum_eq_zero_above_log {N k : ℕ}
    (hk : Nat.log 2 N < k) :
    redhefferFactorSum k N = 0 := by
  apply Finset.sum_eq_zero
  intro m hm
  apply redhefferOrderedFactorCount_eq_zero_above_log
  · exact Nat.succ_le_iff.mpr m.isLt
  · exact hk

theorem redhefferFactorSum_log_pos {N : ℕ} (hN : N ≠ 0) :
    0 < redhefferFactorSum (Nat.log 2 N) N := by
  let L := Nat.log 2 N
  have hpow : 2 ^ L ≤ N := Nat.pow_log_le_self 2 hN
  have hpowPos : 0 < 2 ^ L := pow_pos (by norm_num : (0 : ℕ) < 2) _
  let m : Fin N := ⟨2 ^ L - 1, by omega⟩
  have hmval : m.1 + 1 = 2 ^ L := by
    dsimp [m]
    omega
  have hsingle :
      redhefferOrderedFactorCount L (m.1 + 1) ≤
        ∑ a : Fin N, redhefferOrderedFactorCount L (a.1 + 1) :=
    Finset.single_le_sum
      (f := fun a : Fin N => redhefferOrderedFactorCount L (a.1 + 1))
      (fun a ha => Nat.zero_le _) (Finset.mem_univ m)
  rw [hmval] at hsingle
  exact (redhefferOrderedFactorCount_pow_two_pos L).trans_le hsingle

/-- The shifted polynomial variable `z = X - 1`. -/
noncomputable def redhefferShift : ℤ[X] := X - 1

/-- The sum over nontrivial proper factors used by Vaughan's row recursion. -/
noncomputable def redhefferProperFactorSum (f : ℕ → ℤ[X]) (m : ℕ) : ℤ[X] :=
  ∑ d ∈ Finset.range m, if 1 < d ∧ d ∣ m then f d else 0

/-- The depth-`L` numerator of Vaughan's rational row coefficient at the positive index `m`.

Recursively, the new coefficient is appended at degree zero. This is the denominator-cleared
form of `sum_{k=1}^L D_k(m) * (lambda-1)^(-k)`. -/
noncomputable def redhefferFactorPolynomial : ℕ → ℕ → ℤ[X]
  | 0, _ => 0
  | L + 1, m =>
      redhefferShift * redhefferFactorPolynomial L m +
        C (redhefferOrderedFactorCount (L + 1) m : ℤ)

@[simp] theorem redhefferFactorPolynomial_zero (m : ℕ) :
    redhefferFactorPolynomial 0 m = 0 := by
  rfl

theorem redhefferFactorPolynomial_succ (L m : ℕ) :
    redhefferFactorPolynomial (L + 1) m =
      redhefferShift * redhefferFactorPolynomial L m +
        C (redhefferOrderedFactorCount (L + 1) m : ℤ) := by
  rfl

@[simp] theorem redhefferFactorPolynomial_one (L : ℕ) :
    redhefferFactorPolynomial L 1 = 0 := by
  induction L with
  | zero => rfl
  | succ L ih =>
      rw [redhefferFactorPolynomial_succ, ih]
      simp

private theorem redhefferOrderedFactorCount_succ_succ (k m : ℕ) :
    redhefferOrderedFactorCount (k + 2) m =
      ∑ d ∈ Finset.range m,
        if 1 < d ∧ d ∣ m then redhefferOrderedFactorCount (k + 1) d else 0 := by
  rw [show k + 2 = (k + 1) + 1 by omega, redhefferOrderedFactorCount_succ]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [Finset.mem_range] at hd
  rcases d with _ | _ | d
  · simp
  · simp
  · simp

private theorem redhefferProperFactorSum_factorPolynomial_succ (L m : ℕ) :
    redhefferProperFactorSum (redhefferFactorPolynomial (L + 1)) m =
      redhefferShift *
          redhefferProperFactorSum (redhefferFactorPolynomial L) m +
        C (redhefferOrderedFactorCount (L + 2) m : ℤ) := by
  simp only [redhefferProperFactorSum]
  simp_rw [redhefferFactorPolynomial_succ]
  rw [redhefferOrderedFactorCount_succ_succ]
  push_cast
  simp only [map_sum]
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases h : 1 < d ∧ d ∣ m
  · simp [h]
  · simp [h]

theorem redhefferFactorPolynomial_eq_leading_add_properSum (L m : ℕ) :
    redhefferFactorPolynomial (L + 1) m =
      C (redhefferOrderedFactorCount 1 m : ℤ) * redhefferShift ^ L +
        redhefferProperFactorSum (redhefferFactorPolynomial L) m := by
  induction L with
  | zero =>
      simp [redhefferFactorPolynomial_succ, redhefferProperFactorSum]
  | succ L ih =>
      rw [redhefferFactorPolynomial_succ, ih,
        redhefferProperFactorSum_factorPolynomial_succ]
      rw [pow_succ]
      ring

theorem redhefferShift_mul_factorPolynomial {L m : ℕ}
    (hm : 1 < m) (hvanish : redhefferOrderedFactorCount (L + 1) m = 0) :
    redhefferShift * redhefferFactorPolynomial L m =
      redhefferShift ^ L +
        redhefferProperFactorSum (redhefferFactorPolynomial L) m := by
  have hrec := redhefferFactorPolynomial_succ L m
  have hsource := redhefferFactorPolynomial_eq_leading_add_properSum L m
  rw [hvanish, Int.ofNat_zero, C_0, add_zero] at hrec
  rw [redhefferOrderedFactorCount_one_of_one_lt hm, Int.ofNat_one, C_1, one_mul] at hsource
  exact hrec.symm.trans hsource

/-- Vaughan's reduced characteristic factor for the order-`n+1` Redheffer matrix. -/
noncomputable def redhefferReducedPolynomial (n : ℕ) : ℤ[X] :=
  let L := Nat.log 2 (n + 1)
  redhefferShift ^ (L + 1) -
    ∑ j : Fin n, redhefferFactorPolynomial L (j.1 + 2)

/-- The denominator-free first-row transform used on the Redheffer characteristic matrix. -/
noncomputable def redhefferCharpolyEliminator (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ[X] :=
  let L := Nat.log 2 (n + 1)
  fun i j =>
    if i = 0 then
      if j = 0 then redhefferShift ^ L
      else redhefferFactorPolynomial L (j.1 + 1)
    else if i = j then 1 else 0

theorem redhefferCharpolyEliminator_blockTriangular (n : ℕ) :
    (redhefferCharpolyEliminator n).BlockTriangular id := by
  intro i j hji
  have hi : i ≠ 0 := by
    intro hi
    subst i
    simp at hji
  have hij : i ≠ j := ne_of_gt hji
  simp [redhefferCharpolyEliminator, hi, hij]

theorem det_redhefferCharpolyEliminator (n : ℕ) :
    (redhefferCharpolyEliminator n).det =
      redhefferShift ^ Nat.log 2 (n + 1) := by
  rw [Matrix.det_of_upperTriangular (redhefferCharpolyEliminator_blockTriangular n)]
  rw [Fin.prod_univ_succ]
  simp [redhefferCharpolyEliminator]

private theorem redhefferTail_charmatrix (n : ℕ) :
    ((redhefferMatrix n).charmatrix.submatrix Fin.succ Fin.succ) =
      (redhefferTail n).charmatrix := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [redhefferTail]
  · have hsucc : i.succ ≠ j.succ := fun h => hij (Fin.succ_injective n h)
    simp [Matrix.charmatrix_apply_ne, redhefferTail, hij, hsucc]

private theorem det_redhefferTail_charmatrix (n : ℕ) :
    ((redhefferMatrix n).charmatrix.submatrix Fin.succ Fin.succ).det =
      redhefferShift ^ n := by
  rw [redhefferTail_charmatrix]
  change (redhefferTail n).charpoly = _
  rw [Matrix.charpoly_of_upperTriangular _ (redhefferTail_blockTriangular n)]
  calc
    ∏ i : Fin n, (X - C (redhefferTail n i i)) =
        ∏ _i : Fin n, redhefferShift := by
          apply Finset.prod_congr rfl
          intro i hi
          simp [redhefferShift, redhefferTail, redhefferMatrix]
    _ = redhefferShift ^ n := by simp

private theorem det_redhefferCharpolyEliminated (n : ℕ) :
    (((redhefferMatrix n).charmatrix.updateRow 0
      (Pi.single 0 (redhefferReducedPolynomial n)))).det =
        redhefferReducedPolynomial n * redhefferShift ^ n := by
  have hzeroSuccAbove :
      (0 : Fin (n + 1)).succAbove = (Fin.succ : Fin n → Fin (n + 1)) := by
    funext i
    rfl
  have hminor :
      ((((redhefferMatrix n).charmatrix.updateRow 0
        (Pi.single 0 (redhefferReducedPolynomial n)))).submatrix
          Fin.succ Fin.succ).det = redhefferShift ^ n := by
    rw [show
      (((redhefferMatrix n).charmatrix.updateRow 0
        (Pi.single 0 (redhefferReducedPolynomial n)))).submatrix Fin.succ Fin.succ =
          (redhefferMatrix n).charmatrix.submatrix Fin.succ Fin.succ by
      ext i j
      simp [Matrix.updateRow]]
    exact det_redhefferTail_charmatrix n
  rw [Matrix.det_succ_row_zero]
  rw [Finset.sum_eq_single 0]
  · simp only [Fin.val_zero, pow_zero, one_mul, Matrix.updateRow_self,
      Pi.single_eq_same]
    rw [hzeroSuccAbove, hminor]
  · intro j hj hj0
    simp [Matrix.updateRow_self, hj0]
  · simp

private theorem finiteTailProperFactorSum_eq (n m : ℕ) (f : ℕ → ℤ[X])
    (hmN : m ≤ n + 1) :
    (∑ k : Fin n,
      if k.1 + 2 < m ∧ k.1 + 2 ∣ m then f (k.1 + 2) else 0) =
        redhefferProperFactorSum f m := by
  rw [Fin.sum_univ_eq_sum_range
    (fun k => if k + 2 < m ∧ k + 2 ∣ m then f (k + 2) else 0),
    redhefferProperFactorSum]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_nbij (fun k => k + 2) ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_filter] at hk ⊢
    exact ⟨Finset.mem_range.mpr hk.2.1, ⟨by omega, hk.2.2⟩⟩
  · intro a ha b hb hab
    exact Nat.add_right_cancel hab
  · intro d hd
    change d ∈ (Finset.range m).filter (fun a => 1 < a ∧ a ∣ m) at hd
    rw [Finset.mem_filter] at hd
    have hdm : d < m := Finset.mem_range.mp hd.1
    refine ⟨d - 2, ?_, ?_⟩
    · change d - 2 ∈
        (Finset.range n).filter (fun a => a + 2 < m ∧ a + 2 ∣ m)
      rw [Finset.mem_filter]
      constructor
      · rw [Finset.mem_range]
        omega
      · simpa only [Nat.sub_add_cancel (by omega : 2 ≤ d)] using
          ⟨hdm, hd.2.2⟩
    · exact Nat.sub_add_cancel (by omega : 2 ≤ d)
  · intro k hk
    rfl

private theorem finiteTailOffDiagonalFactorSum_eq (n : ℕ) (j : Fin (n + 1))
    (f : ℕ → ℤ[X]) :
    (∑ k : Fin n,
      if k.succ ≠ j ∧ k.1 + 2 ∣ j.1 + 1 then f (k.1 + 2) else 0) =
        redhefferProperFactorSum f (j.1 + 1) := by
  rw [← finiteTailProperFactorSum_eq n (j.1 + 1) f (by omega)]
  apply Finset.sum_congr rfl
  intro k hk
  have hmpos : 0 < j.1 + 1 := by omega
  have hiff :
      (k.succ ≠ j ∧ k.1 + 2 ∣ j.1 + 1) ↔
        (k.1 + 2 < j.1 + 1 ∧ k.1 + 2 ∣ j.1 + 1) := by
    constructor
    · intro h
      refine ⟨?_, h.2⟩
      have hle := Nat.le_of_dvd hmpos h.2
      have hne : k.1 + 2 ≠ j.1 + 1 := by
        intro heq
        apply h.1
        exact Fin.ext (by
          simp only [Fin.val_succ]
          omega)
      omega
    · intro h
      refine ⟨?_, h.2⟩
      intro heq
      have hval := Fin.mk.inj heq
      omega
  simp only [hiff]

private theorem redhefferFactorPolynomial_tail_charmatrix (n : ℕ)
    (j : Fin (n + 1)) (hj : j ≠ 0) :
    let L := Nat.log 2 (n + 1)
    (∑ k : Fin n,
      redhefferFactorPolynomial L (k.1 + 2) *
        (redhefferMatrix n).charmatrix k.succ j) =
      redhefferFactorPolynomial L (j.1 + 1) * redhefferShift -
        redhefferProperFactorSum (redhefferFactorPolynomial L) (j.1 + 1) := by
  let L := Nat.log 2 (n + 1)
  let p : Fin n := Fin.pred j hj
  have hp : p.succ = j := Fin.succ_pred j hj
  have heq (k : Fin n) : k.succ = j ↔ k = p := by
    rw [← hp]
    exact Fin.succ_inj
  have hneq (k : Fin n) : k ≠ p ↔ k.succ ≠ j :=
    (not_congr (heq k)).symm
  have hpval : p.1 + 2 = j.1 + 1 := by
    have h := congrArg Fin.val hp
    simp only [Fin.val_succ] at h
    omega
  have hentry (k : Fin n) :
      (redhefferMatrix n).charmatrix k.succ j =
        if k.succ = j then redhefferShift
        else if k.1 + 2 ∣ j.1 + 1 then -1 else 0 := by
    by_cases hkj : k.succ = j
    · rw [hkj, Matrix.charmatrix_apply_eq]
      simp [redhefferShift, redhefferMatrix]
    · rw [Matrix.charmatrix_apply_ne _ _ _ hkj]
      by_cases hdiv : k.1 + 2 ∣ j.1 + 1
      · simp [redhefferMatrix, hj, hkj, hdiv, Nat.add_assoc]
      · simp [redhefferMatrix, hj, hkj, hdiv, Nat.add_assoc]
  simp_rw [hentry]
  calc
    (∑ k : Fin n,
      redhefferFactorPolynomial L (k.1 + 2) *
        (if k.succ = j then redhefferShift
          else if k.1 + 2 ∣ j.1 + 1 then -1 else 0)) =
        ∑ k : Fin n,
          ((if k = p then
              redhefferFactorPolynomial L (j.1 + 1) * redhefferShift else 0) -
            (if k ≠ p ∧ k.1 + 2 ∣ j.1 + 1 then
              redhefferFactorPolynomial L (k.1 + 2) else 0)) := by
          apply Finset.sum_congr rfl
          intro k hk
          by_cases hkp : k = p
          · subst k
            simp [hp, hpval]
          · have hsucc : k.succ ≠ j := (hneq k).mp hkp
            by_cases hdiv : k.1 + 2 ∣ j.1 + 1
            · simp [hkp, hsucc, hdiv]
            · simp [hkp, hsucc, hdiv]
    _ =
        (∑ k : Fin n,
          if k = p then
            redhefferFactorPolynomial L (j.1 + 1) * redhefferShift else 0) -
        ∑ k : Fin n,
          if k ≠ p ∧ k.1 + 2 ∣ j.1 + 1 then
            redhefferFactorPolynomial L (k.1 + 2) else 0 := by
          rw [Finset.sum_sub_distrib]
    _ = redhefferFactorPolynomial L (j.1 + 1) * redhefferShift -
        redhefferProperFactorSum (redhefferFactorPolynomial L) (j.1 + 1) := by
          rw [show
            (∑ k : Fin n,
              if k ≠ p ∧ k.1 + 2 ∣ j.1 + 1 then
                redhefferFactorPolynomial L (k.1 + 2) else 0) =
                redhefferProperFactorSum
                  (redhefferFactorPolynomial L) (j.1 + 1) by
              simpa only [hneq] using
                finiteTailOffDiagonalFactorSum_eq n j
                  (redhefferFactorPolynomial L)]
          simp

theorem redhefferCharpolyEliminator_mul_charmatrix (n : ℕ) :
    redhefferCharpolyEliminator n * (redhefferMatrix n).charmatrix =
      (redhefferMatrix n).charmatrix.updateRow 0
        (Pi.single 0 (redhefferReducedPolynomial n)) := by
  ext i j : 1
  by_cases hi : i = 0
  · subst i
    by_cases hj : j = 0
    · subst j
      rw [Matrix.mul_apply, Fin.sum_univ_succ]
      simp [redhefferCharpolyEliminator, redhefferReducedPolynomial,
        redhefferShift, redhefferMatrix, pow_succ, Nat.add_assoc]
      ring
    · let L := Nat.log 2 (n + 1)
      have hm : 1 < j.1 + 1 := by
        have hjval : j.1 ≠ 0 := by
          intro h
          apply hj
          apply Fin.ext
          simpa using h
        omega
      have hmN : j.1 + 1 ≤ n + 1 := by omega
      have hvanish :
          redhefferOrderedFactorCount (L + 1) (j.1 + 1) = 0 := by
        apply redhefferOrderedFactorCount_eq_zero_above_log hmN
        dsimp [L]
        omega
      have hrow := redhefferShift_mul_factorPolynomial hm hvanish
      have htail := redhefferFactorPolynomial_tail_charmatrix n j hj
      dsimp [L] at hrow htail
      rw [Matrix.mul_apply, Fin.sum_univ_succ]
      simp only [redhefferCharpolyEliminator, if_pos, Fin.succ_ne_zero, if_false,
        Fin.val_succ, Nat.add_assoc, Matrix.updateRow_self, Pi.single_eq_of_ne hj]
      rw [htail]
      have hentry :
          (redhefferMatrix n).charmatrix 0 j = -1 := by
        rw [Matrix.charmatrix_apply_ne _ _ _ (fun h => hj h.symm)]
        simp [redhefferMatrix, hj]
      rw [hentry]
      rw [mul_neg, mul_one,
        mul_comm (redhefferFactorPolynomial (Nat.log 2 (n + 1)) (j.1 + 1))
          redhefferShift,
        hrow]
      ring
  · rw [Matrix.mul_apply]
    simp [redhefferCharpolyEliminator, Matrix.updateRow, hi]

/-- Vaughan's exact characteristic-polynomial factorization. -/
theorem charpoly_redhefferMatrix (n : ℕ) :
    (redhefferMatrix n).charpoly =
      redhefferShift ^ (n - Nat.log 2 (n + 1)) *
        redhefferReducedPolynomial n := by
  let L := Nat.log 2 (n + 1)
  change (redhefferMatrix n).charpoly =
    redhefferShift ^ (n - L) * redhefferReducedPolynomial n
  have hL : L ≤ n := by
    have hlt := Nat.log_lt_self 2 (Nat.succ_ne_zero n)
    have : L < n + 1 := by
      simpa [L, Nat.succ_eq_add_one] using hlt
    omega
  have hdet :=
    congrArg Matrix.det (redhefferCharpolyEliminator_mul_charmatrix n)
  rw [Matrix.det_mul, det_redhefferCharpolyEliminator,
    det_redhefferCharpolyEliminated] at hdet
  change redhefferShift ^ L * (redhefferMatrix n).charpoly =
    redhefferReducedPolynomial n * redhefferShift ^ n at hdet
  have hpow :
      redhefferShift ^ n =
        redhefferShift ^ L * redhefferShift ^ (n - L) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow] at hdet
  have hshift : redhefferShift ^ L ≠ 0 := by
    exact pow_ne_zero L (X_sub_C_ne_zero (1 : ℤ))
  apply mul_left_cancel₀ hshift
  calc
    redhefferShift ^ L * (redhefferMatrix n).charpoly =
        redhefferReducedPolynomial n *
          (redhefferShift ^ L * redhefferShift ^ (n - L)) := hdet
    _ = redhefferShift ^ L *
        (redhefferShift ^ (n - L) * redhefferReducedPolynomial n) := by ring

@[simp] theorem eval_one_redhefferFactorPolynomial_succ (L m : ℕ) :
    (redhefferFactorPolynomial (L + 1) m).eval 1 =
      redhefferOrderedFactorCount (L + 1) m := by
  rw [redhefferFactorPolynomial_succ]
  simp [redhefferShift]

private theorem redhefferFactorSum_succ_order (k n : ℕ) :
    redhefferFactorSum (k + 1) (n + 1) =
      ∑ j : Fin n, redhefferOrderedFactorCount (k + 1) (j.1 + 2) := by
  rw [redhefferFactorSum, Fin.sum_univ_succ]
  simp

theorem eval_one_redhefferReducedPolynomial {n : ℕ} (hn : 0 < n) :
    (redhefferReducedPolynomial n).eval 1 =
      -(redhefferFactorSum (Nat.log 2 (n + 1)) (n + 1) : ℤ) := by
  have hlog : 0 < Nat.log 2 (n + 1) := by
    exact Nat.log_pos Nat.one_lt_two (by omega)
  obtain ⟨L, hL⟩ := Nat.exists_eq_succ_of_ne_zero hlog.ne'
  rw [redhefferReducedPolynomial]
  simp only [hL, eval_sub, eval_pow, eval_finsetSum,
    eval_one_redhefferFactorPolynomial_succ]
  simp [redhefferShift, redhefferFactorSum_succ_order]

theorem redhefferReducedPolynomial_eval_one_ne_zero {n : ℕ} (hn : 0 < n) :
    (redhefferReducedPolynomial n).eval 1 ≠ 0 := by
  rw [eval_one_redhefferReducedPolynomial hn]
  have hpos :=
    redhefferFactorSum_log_pos (N := n + 1) (by omega)
  exact neg_ne_zero.mpr (Int.ofNat_ne_zero.mpr hpos.ne')

theorem redhefferReducedPolynomial_ne_zero {n : ℕ} (hn : 0 < n) :
    redhefferReducedPolynomial n ≠ 0 := by
  intro h
  apply redhefferReducedPolynomial_eval_one_ne_zero hn
  rw [h, eval_zero]

/-- For order at least two, the algebraic multiplicity of the unit eigenvalue is exact. -/
theorem rootMultiplicity_one_charpoly_redhefferMatrix {n : ℕ} (hn : 0 < n) :
    (redhefferMatrix n).charpoly.rootMultiplicity 1 =
      n - Nat.log 2 (n + 1) := by
  rw [charpoly_redhefferMatrix, mul_comm]
  change rootMultiplicity 1
    (redhefferReducedPolynomial n *
      (X - C (1 : ℤ)) ^ (n - Nat.log 2 (n + 1))) =
        n - Nat.log 2 (n + 1)
  rw [rootMultiplicity_mul_X_sub_C_pow
    (redhefferReducedPolynomial_ne_zero hn)]
  rw [rootMultiplicity_eq_zero
    (show ¬(redhefferReducedPolynomial n).IsRoot 1 by
      simpa [Polynomial.IsRoot] using redhefferReducedPolynomial_eval_one_ne_zero hn)]
  simp

theorem eval_zero_charpoly_redhefferMatrix (n : ℕ) :
    (redhefferMatrix n).charpoly.eval 0 =
      (-1) ^ (n + 1) * finiteMertens (n + 1) := by
  rw [Matrix.eval_charpoly]
  have hzero :
      Matrix.scalar (Fin (n + 1)) (0 : ℤ) - redhefferMatrix n =
        -(redhefferMatrix n) := by
    ext i j
    simp
  rw [hzero, Matrix.det_neg, det_redhefferMatrix_eq_finiteMertens]
  simp

theorem redhefferFactorPolynomial_expansion (L m : ℕ) :
    redhefferFactorPolynomial L m =
      ∑ r ∈ Finset.range L,
        C (redhefferOrderedFactorCount (r + 1) m : ℤ) *
          redhefferShift ^ (L - r - 1) := by
  induction L with
  | zero => simp
  | succ L ih =>
      rw [redhefferFactorPolynomial_succ, ih, Finset.mul_sum,
        Finset.sum_range_succ]
      congr 1
      · apply Finset.sum_congr rfl
        intro r hr
        have hrL : r < L := Finset.mem_range.mp hr
        rw [show L + 1 - r - 1 = (L - r - 1) + 1 by omega, pow_succ']
        ring
      · simp

/-- Vaughan's displayed coefficient form of the reduced characteristic factor. -/
noncomputable def redhefferSourceReducedPolynomial (n : ℕ) : ℤ[X] :=
  let L := Nat.log 2 (n + 1)
  redhefferShift ^ (L + 1) -
    ∑ r ∈ Finset.range L,
      C (redhefferFactorSum (r + 1) (n + 1) : ℤ) *
        redhefferShift ^ (L - r - 1)

theorem redhefferReducedPolynomial_eq_source (n : ℕ) :
    redhefferReducedPolynomial n = redhefferSourceReducedPolynomial n := by
  rw [redhefferReducedPolynomial, redhefferSourceReducedPolynomial]
  congr 1
  simp_rw [redhefferFactorPolynomial_expansion]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [← Finset.sum_mul]
  congr 1
  rw [← map_sum]
  congr 1
  norm_cast
  exact (redhefferFactorSum_succ_order r n).symm

theorem charpoly_redhefferMatrix_source (n : ℕ) :
    (redhefferMatrix n).charpoly =
      redhefferShift ^ (n - Nat.log 2 (n + 1)) *
        redhefferSourceReducedPolynomial n := by
  rw [charpoly_redhefferMatrix, redhefferReducedPolynomial_eq_source]

theorem charpoly_redheffer_order_one :
    (redhefferMatrix 0).charpoly = redhefferShift := by
  rw [charpoly_redhefferMatrix]
  norm_num [redhefferReducedPolynomial, redhefferShift]

theorem charpoly_redheffer_order_two :
    (redhefferMatrix 1).charpoly = redhefferShift ^ 2 - 1 := by
  rw [charpoly_redhefferMatrix]
  norm_num [redhefferReducedPolynomial, redhefferFactorPolynomial,
    redhefferOrderedFactorCount, redhefferShift, Fin.sum_univ_one,
    Finset.sum_range_succ]

theorem charpoly_redheffer_order_three :
    (redhefferMatrix 2).charpoly =
      redhefferShift * (redhefferShift ^ 2 - 2) := by
  rw [charpoly_redhefferMatrix]
  norm_num [redhefferReducedPolynomial, redhefferFactorPolynomial,
    redhefferOrderedFactorCount, redhefferShift, Fin.sum_univ_two,
    Finset.sum_range_succ]

theorem charpoly_redheffer_order_four :
    (redhefferMatrix 3).charpoly =
      redhefferShift * (redhefferShift ^ 3 - 3 * redhefferShift - 1) := by
  rw [charpoly_redhefferMatrix]
  norm_num [redhefferReducedPolynomial, redhefferFactorPolynomial,
    redhefferOrderedFactorCount, redhefferShift, Fin.sum_univ_three,
    Finset.sum_range_succ]
  left
  ring

theorem rootMultiplicity_one_charpoly_redheffer_order_one :
    (redhefferMatrix 0).charpoly.rootMultiplicity 1 = 1 := by
  rw [charpoly_redheffer_order_one]
  exact rootMultiplicity_X_sub_C_self

/-- The complete source-level Redheffer characteristic-polynomial certificate. -/
structure RedhefferCharacteristicPolynomialCertificate : Prop where
  orderedSupport :
    ∀ {k m : ℕ}, m < 2 ^ k → redhefferOrderedFactorCount k m = 0
  sourceFactorization :
    ∀ n : ℕ,
      (redhefferMatrix n).charpoly =
        redhefferShift ^ (n - Nat.log 2 (n + 1)) *
          redhefferSourceReducedPolynomial n
  exactUnitMultiplicity :
    ∀ {n : ℕ}, 0 < n →
      (redhefferMatrix n).charpoly.rootMultiplicity 1 =
        n - Nat.log 2 (n + 1)
  orderOneBoundary :
    (redhefferMatrix 0).charpoly.rootMultiplicity 1 = 1
  mertensCompatibility :
    ∀ n : ℕ,
      (redhefferMatrix n).charpoly.eval 0 =
        (-1) ^ (n + 1) * finiteMertens (n + 1)
  lowOrders :
    (redhefferMatrix 0).charpoly = redhefferShift ∧
    (redhefferMatrix 1).charpoly = redhefferShift ^ 2 - 1 ∧
    (redhefferMatrix 2).charpoly =
      redhefferShift * (redhefferShift ^ 2 - 2) ∧
    (redhefferMatrix 3).charpoly =
      redhefferShift * (redhefferShift ^ 3 - 3 * redhefferShift - 1)

theorem redhefferCharacteristicPolynomial_endpoint :
    RedhefferCharacteristicPolynomialCertificate where
  orderedSupport := redhefferOrderedFactorCount_eq_zero_of_lt_pow_two
  sourceFactorization := charpoly_redhefferMatrix_source
  exactUnitMultiplicity := rootMultiplicity_one_charpoly_redhefferMatrix
  orderOneBoundary := rootMultiplicity_one_charpoly_redheffer_order_one
  mertensCompatibility := eval_zero_charpoly_redhefferMatrix
  lowOrders := ⟨charpoly_redheffer_order_one, charpoly_redheffer_order_two,
    charpoly_redheffer_order_three, charpoly_redheffer_order_four⟩

end LeanLab.Riemann
