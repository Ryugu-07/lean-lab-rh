import LeanLab.Riemann.LevinsonMontgomeryHeightTenBoundaryNeighborhood
import LeanLab.Riemann.LevinsonMontgomeryEulerMaclaurinSecond

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Height-ten top-edge transport

This module develops a phase-preserving transport backend for the unresolved height-ten
horizontal in the Levinson--Montgomery certificate. The first layer transfers the pointwise
second Euler--Maclaurin derivative error to a second-derivative error by Cauchy's estimate.
-/

namespace LeanLab.Riemann

open Complex Filter Finset Real Set
open scoped BigOperators ComplexConjugate Topology

noncomputable section

/-- The finite second-derivative center obtained by differentiating the explicit second
Euler--Maclaurin derivative formula. -/
def eulerMaclaurinTwoZetaSecondFiniteFormula (s : ℂ) (N : ℕ) : ℂ :=
  deriv (fun w => eulerMaclaurinTwoZetaDerivFiniteFormula w N) s

/-- Explicit phase-preserving formula for the second derivative of the second Euler--Maclaurin
center. -/
def eulerMaclaurinTwoZetaSecondExplicitFormula (s : ℂ) (N : ℕ) : ℂ :=
  let L : ℂ := ((Real.log (N : ℝ) : ℝ) : ℂ)
  let d : ℂ := 1 - s
  let p : ℂ := (N : ℂ) ^ (1 - s)
  let q : ℂ := (N : ℂ) ^ (-s)
  let r : ℂ := (N : ℂ) ^ (-s - 1)
  (∑ n ∈ range N,
      ((((Real.log ((n : ℝ) + 1) : ℝ) : ℂ)) ^ 2) *
        (((n : ℂ) + 1) ^ (-s))) -
    p * (L ^ 2 * d ^ 2 - 2 * L * d + 2) / d ^ 3 -
    q * L ^ 2 / 2 +
    r * (s * L ^ 2 - 2 * L) / 12

theorem eulerMaclaurinTwoZetaSecondFiniteFormula_eq_explicit
    (s : ℂ) (hsOne : s ≠ 1) {N : ℕ} (hN : 1 ≤ N) :
    eulerMaclaurinTwoZetaSecondFiniteFormula s N =
      eulerMaclaurinTwoZetaSecondExplicitFormula s N := by
  let L : ℂ := ((Real.log (N : ℝ) : ℝ) : ℂ)
  let d : ℂ → ℂ := fun w => 1 - w
  let p : ℂ → ℂ := fun w => (N : ℂ) ^ (1 - w)
  let q : ℂ → ℂ := fun w => (N : ℂ) ^ (-w)
  let r : ℂ → ℂ := fun w => (N : ℂ) ^ (-w - 1)
  let sumD : ℂ → ℂ := fun w =>
    ∑ n ∈ range N,
      -(((Real.log ((n : ℝ) + 1) : ℝ) : ℂ)) *
        (((n : ℂ) + 1) ^ (-w))
  let Fprime : ℂ → ℂ := fun w =>
    p w * (1 - L * d w) / d w ^ 2
  let Gprime : ℂ → ℂ := fun w => q w * L * (-1) / 2
  let Hprime : ℂ → ℂ := fun w => (r w - w * r w * L) / 12
  have hNzero : (N : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_zero_of_lt hN)
  have hdNe : d s ≠ 0 := by
    dsimp only [d]
    exact sub_ne_zero.mpr hsOne.symm
  have hsumD : HasDerivAt sumD
      (∑ n ∈ range N,
        ((((Real.log ((n : ℝ) + 1) : ℝ) : ℂ)) ^ 2) *
          (((n : ℂ) + 1) ^ (-s))) s := by
    dsimp only [sumD]
    apply HasDerivAt.fun_sum
    intro n _hn
    have hbase : (n : ℂ) + 1 ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      norm_num at hre
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hneg : HasDerivAt (fun w : ℂ => -w) (-1) s := by
      exact (hasDerivAt_id s).neg.congr_of_eventuallyEq
        (Eventually.of_forall fun _w => rfl)
    have hraw := hneg.const_cpow (Or.inl hbase)
    have hlog : Complex.log ((n : ℂ) + 1) =
        (((Real.log ((n : ℝ) + 1) : ℝ) : ℂ)) := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
      rw [show (n : ℂ) + 1 = (((n : ℝ) + 1 : ℝ) : ℂ) by norm_num,
        ← Complex.ofReal_log hn0]
    have hterm := hraw.const_mul
      (-(((Real.log ((n : ℝ) + 1) : ℝ) : ℂ)))
    apply hterm.congr_deriv
    rw [hlog]
    ring
  have hd : HasDerivAt d (-1) s := by
    simpa only [d, Function.id_def] using
      (hasDerivAt_id s).const_sub (1 : ℂ)
  have hp : HasDerivAt p (-L * p s) s := by
    dsimp only [p]
    have hraw := hd.const_cpow (Or.inl hNzero)
    have hlog : Complex.log (N : ℂ) = L := by
      dsimp only [L]
      rw [show (N : ℂ) = ((N : ℝ) : ℂ) by norm_num,
        ← Complex.ofReal_log (Nat.cast_nonneg N)]
    apply hraw.congr_deriv
    rw [hlog]
    ring
  have hq : HasDerivAt q (-L * q s) s := by
    dsimp only [q]
    have hneg : HasDerivAt (fun w : ℂ => -w) (-1) s := by
      exact (hasDerivAt_id s).neg.congr_of_eventuallyEq
        (Eventually.of_forall fun _w => rfl)
    have hraw := hneg.const_cpow (Or.inl hNzero)
    have hlog : Complex.log (N : ℂ) = L := by
      dsimp only [L]
      rw [show (N : ℂ) = ((N : ℝ) : ℂ) by norm_num,
        ← Complex.ofReal_log (Nat.cast_nonneg N)]
    apply hraw.congr_deriv
    rw [hlog]
    ring
  have hrpow : HasDerivAt r (-L * r s) s := by
    dsimp only [r]
    have hnegOne : HasDerivAt (fun w : ℂ => -w - 1) (-1) s := by
      exact ((hasDerivAt_id s).neg.sub_const (1 : ℂ)).congr_of_eventuallyEq
        (Eventually.of_forall fun _w => rfl)
    have hraw := hnegOne.const_cpow (Or.inl hNzero)
    have hlog : Complex.log (N : ℂ) = L := by
      dsimp only [L]
      rw [show (N : ℂ) = ((N : ℝ) : ℂ) by norm_num,
        ← Complex.ofReal_log (Nat.cast_nonneg N)]
    apply hraw.congr_deriv
    rw [hlog]
    ring
  have hF : HasDerivAt Fprime
      (p s * (L ^ 2 * d s ^ 2 - 2 * L * d s + 2) / d s ^ 3) s := by
    have ha : HasDerivAt (fun w => 1 - L * d w) L s := by
      have hraw := (hasDerivAt_const (x := s) (c := (1 : ℂ))).sub
        (hd.const_mul L)
      apply (hraw.congr_of_eventuallyEq (Eventually.of_forall fun w => by
        simp only [Pi.sub_apply])).congr_deriv
      ring
    have hraw := (hp.mul ha).div (hd.pow 2) (pow_ne_zero 2 hdNe)
    simp only [Pi.mul_apply, Pi.pow_apply] at hraw
    apply (hraw.congr_of_eventuallyEq (Eventually.of_forall fun w => by
      simp only [Fprime]
      rfl)).congr_deriv
    field_simp [hdNe]
    ring
  have hG : HasDerivAt Gprime (q s * L ^ 2 / 2) s := by
    have hraw := ((hq.mul_const L).mul_const (-1 : ℂ)).div_const 2
    apply (hraw.congr_of_eventuallyEq (Eventually.of_forall fun _w => rfl)).congr_deriv
    ring
  have hH : HasDerivAt Hprime (r s * (s * L ^ 2 - 2 * L) / 12) s := by
    have hraw := (hrpow.sub
      (((hasDerivAt_id s).mul hrpow).mul_const L)).div_const 12
    apply (hraw.congr_of_eventuallyEq (Eventually.of_forall fun _w => rfl)).congr_deriv
    simp only [Function.id_def]
    ring
  have htotal := ((hsumD.sub hF).sub hG).add hH
  have htotal' : HasDerivAt
      (fun w => eulerMaclaurinTwoZetaDerivFiniteFormula w N)
      ((∑ n ∈ range N,
          ((((Real.log ((n : ℝ) + 1) : ℝ) : ℂ)) ^ 2) *
            (((n : ℂ) + 1) ^ (-s))) -
        p s * (L ^ 2 * d s ^ 2 - 2 * L * d s + 2) / d s ^ 3 -
        q s * L ^ 2 / 2 +
        r s * (s * L ^ 2 - 2 * L) / 12) s := by
    apply htotal.congr_of_eventuallyEq
    exact Eventually.of_forall fun w => by
      change eulerMaclaurinTwoZetaDerivFiniteFormula w N =
        sumD w - Fprime w - Gprime w + Hprime w
      simp only [sumD, Fprime, Gprime, Hprime, p, q, r, d, L]
      unfold eulerMaclaurinTwoZetaDerivFiniteFormula
        eulerMaclaurinOneZetaDerivFiniteFormula
        eulerMaclaurinTwoCorrectionDerivFiniteFormula
      simp only [div_eq_mul_inv]
      ring
  unfold eulerMaclaurinTwoZetaSecondFiniteFormula
  rw [htotal'.deriv]
  simp only [eulerMaclaurinTwoZetaSecondExplicitFormula, L, d, p, q, r]

/-- Rational phase-preserving center for the squared-log partial sum at `1/2-10i`. -/
def heightTenRoundedLogSqCpowSum : ℂ :=
  ∑ n ∈ range 30,
    (((binaryLogCenter (heightTenBinaryIndex (n + 1)) 12 (n + 1) : ℝ) : ℂ) ^ 2) *
      heightTenRoundedCpowCenter (n + 1)

/-- Rational center for the complete second-corrected second derivative at the reflected
height-ten endpoint. -/
def heightTenRoundedEulerZetaSecondApprox : ℂ :=
  let L : ℂ :=
    ((binaryLogCenter (heightTenBinaryIndex 30) 12 (30 : ℝ) : ℝ) : ℂ)
  let R : ℂ := heightTenRoundedCpowCenter 30
  let d : ℂ := 1 - heightTenReflectedEndpoint
  heightTenRoundedLogSqCpowSum -
    ((30 : ℂ) * R) * (L ^ 2 * d ^ 2 - 2 * L * d + 2) / d ^ 3 -
    R * L ^ 2 / 2 +
    (R / 30) * (heightTenReflectedEndpoint * L ^ 2 - 2 * L) / 12

/-- Short rational coordinates for the exact rational second-derivative center. -/
def heightTenCompactEulerZetaSecondApprox : ℂ :=
  ((226793895365 / 1000000000000 : ℝ) : ℂ) +
    ((-75092382469 / 1000000000000 : ℝ) : ℂ) * I

private def heightTenRoundedLogSqCpowChunk (offset : ℕ) : ℂ :=
  ∑ n ∈ range 10,
    (((binaryLogCenter (heightTenBinaryIndex (n + offset + 1)) 12
      (n + offset + 1) : ℝ) : ℂ) ^ 2) *
      heightTenRoundedCpowCenter (n + offset + 1)

private def heightTenCompactLogSqCpowChunk : ℕ → ℂ
  | 0 => ((-1617618639404 / 1000000000000 : ℝ) : ℂ) +
      ((-223959088107 / 1000000000000 : ℝ) : ℂ) * I
  | 10 => ((-1850656018910 / 1000000000000 : ℝ) : ℂ) +
      ((-1746103425606 / 1000000000000 : ℝ) : ℂ) * I
  | 20 => ((5431263175049 / 1000000000000 : ℝ) : ℂ) +
      ((8110038283148 / 1000000000000 : ℝ) : ℂ) * I
  | _ => 0

private theorem norm_heightTenRoundedLogSqCpowChunk_zero_sub_compact_le :
    ‖heightTenRoundedLogSqCpowChunk 0 -
        heightTenCompactLogSqCpowChunk 0‖ ≤ (1 / 1000000000 : ℝ) := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  norm_num [heightTenRoundedLogSqCpowChunk, heightTenCompactLogSqCpowChunk,
    heightTenRoundedCpowCenter, heightTenBinaryIndex, binaryLogCenter,
    logAtanhPartial, Complex.mul_re, Complex.mul_im, Finset.sum_range_succ,
    pow_succ]

private theorem norm_heightTenRoundedLogSqCpowChunk_ten_sub_compact_le :
    ‖heightTenRoundedLogSqCpowChunk 10 -
        heightTenCompactLogSqCpowChunk 10‖ ≤ (1 / 1000000000 : ℝ) := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  norm_num [heightTenRoundedLogSqCpowChunk, heightTenCompactLogSqCpowChunk,
    heightTenRoundedCpowCenter, heightTenBinaryIndex, binaryLogCenter,
    logAtanhPartial, Complex.mul_re, Complex.mul_im, Finset.sum_range_succ,
    pow_succ]

private theorem norm_heightTenRoundedLogSqCpowChunk_twenty_sub_compact_le :
    ‖heightTenRoundedLogSqCpowChunk 20 -
        heightTenCompactLogSqCpowChunk 20‖ ≤ (1 / 1000000000 : ℝ) := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  norm_num [heightTenRoundedLogSqCpowChunk, heightTenCompactLogSqCpowChunk,
    heightTenRoundedCpowCenter, heightTenBinaryIndex, binaryLogCenter,
    logAtanhPartial, Complex.mul_re, Complex.mul_im, Finset.sum_range_succ,
    pow_succ]

private theorem heightTenRoundedLogSqCpowSum_eq_chunks :
    heightTenRoundedLogSqCpowSum =
      heightTenRoundedLogSqCpowChunk 0 +
        heightTenRoundedLogSqCpowChunk 10 +
          heightTenRoundedLogSqCpowChunk 20 := by
  unfold heightTenRoundedLogSqCpowSum heightTenRoundedLogSqCpowChunk
  rw [show 30 = 20 + 10 by norm_num, Finset.sum_range_add,
    show 20 = 10 + 10 by norm_num, Finset.sum_range_add]
  simp only [Nat.add_zero, Nat.add_comm, Nat.add_left_comm, Nat.cast_add,
    Nat.cast_ofNat]
  norm_num

private def heightTenCompactLogSqCpowSum : ℂ :=
  heightTenCompactLogSqCpowChunk 0 +
    heightTenCompactLogSqCpowChunk 10 +
      heightTenCompactLogSqCpowChunk 20

private theorem norm_heightTenRoundedLogSqCpowSum_sub_compact_le :
    ‖heightTenRoundedLogSqCpowSum - heightTenCompactLogSqCpowSum‖ ≤
      (3 / 1000000000 : ℝ) := by
  rw [heightTenRoundedLogSqCpowSum_eq_chunks]
  have hid :
      heightTenRoundedLogSqCpowChunk 0 + heightTenRoundedLogSqCpowChunk 10 +
          heightTenRoundedLogSqCpowChunk 20 - heightTenCompactLogSqCpowSum =
        (heightTenRoundedLogSqCpowChunk 0 - heightTenCompactLogSqCpowChunk 0) +
          (heightTenRoundedLogSqCpowChunk 10 - heightTenCompactLogSqCpowChunk 10) +
            (heightTenRoundedLogSqCpowChunk 20 -
              heightTenCompactLogSqCpowChunk 20) := by
    unfold heightTenCompactLogSqCpowSum
    ring
  rw [hid]
  calc
    ‖(heightTenRoundedLogSqCpowChunk 0 - heightTenCompactLogSqCpowChunk 0) +
        (heightTenRoundedLogSqCpowChunk 10 - heightTenCompactLogSqCpowChunk 10) +
          (heightTenRoundedLogSqCpowChunk 20 -
            heightTenCompactLogSqCpowChunk 20)‖ ≤
        ‖heightTenRoundedLogSqCpowChunk 0 - heightTenCompactLogSqCpowChunk 0‖ +
          ‖heightTenRoundedLogSqCpowChunk 10 - heightTenCompactLogSqCpowChunk 10‖ +
            ‖heightTenRoundedLogSqCpowChunk 20 -
              heightTenCompactLogSqCpowChunk 20‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ 1 / 1000000000 + 1 / 1000000000 + 1 / 1000000000 := by
      gcongr
      · exact norm_heightTenRoundedLogSqCpowChunk_zero_sub_compact_le
      · exact norm_heightTenRoundedLogSqCpowChunk_ten_sub_compact_le
      · exact norm_heightTenRoundedLogSqCpowChunk_twenty_sub_compact_le
    _ = 3 / 1000000000 := by norm_num

private def heightTenChunkedEulerZetaSecondApprox : ℂ :=
  let L : ℂ :=
    ((binaryLogCenter (heightTenBinaryIndex 30) 12 (30 : ℝ) : ℝ) : ℂ)
  let R : ℂ := heightTenRoundedCpowCenter 30
  let d : ℂ := 1 - heightTenReflectedEndpoint
  heightTenCompactLogSqCpowSum -
    ((30 : ℂ) * R) * (L ^ 2 * d ^ 2 - 2 * L * d + 2) / d ^ 3 -
    R * L ^ 2 / 2 +
    (R / 30) * (heightTenReflectedEndpoint * L ^ 2 - 2 * L) / 12

private theorem norm_heightTenRoundedEulerZetaSecondApprox_sub_chunked_le :
    ‖heightTenRoundedEulerZetaSecondApprox -
        heightTenChunkedEulerZetaSecondApprox‖ ≤ (3 / 1000000000 : ℝ) := by
  unfold heightTenRoundedEulerZetaSecondApprox
    heightTenChunkedEulerZetaSecondApprox
  rw [show
    heightTenRoundedLogSqCpowSum -
          (30 : ℂ) * heightTenRoundedCpowCenter 30 *
              (((binaryLogCenter (heightTenBinaryIndex 30) 12 (30 : ℝ) : ℝ) : ℂ) ^ 2 *
                  (1 - heightTenReflectedEndpoint) ^ 2 -
                2 *
                    ((binaryLogCenter (heightTenBinaryIndex 30) 12 (30 : ℝ) : ℝ) : ℂ) *
                  (1 - heightTenReflectedEndpoint) +
                2) /
            (1 - heightTenReflectedEndpoint) ^ 3 -
          heightTenRoundedCpowCenter 30 *
              ((binaryLogCenter (heightTenBinaryIndex 30) 12 (30 : ℝ) : ℝ) : ℂ) ^ 2 /
            2 +
        heightTenRoundedCpowCenter 30 / 30 *
              (heightTenReflectedEndpoint *
                    ((binaryLogCenter (heightTenBinaryIndex 30) 12 (30 : ℝ) : ℝ) : ℂ) ^ 2 -
                2 *
                  ((binaryLogCenter (heightTenBinaryIndex 30) 12 (30 : ℝ) : ℝ) : ℂ)) /
            12 -
      (heightTenCompactLogSqCpowSum -
          (30 : ℂ) * heightTenRoundedCpowCenter 30 *
              (((binaryLogCenter (heightTenBinaryIndex 30) 12 (30 : ℝ) : ℝ) : ℂ) ^ 2 *
                  (1 - heightTenReflectedEndpoint) ^ 2 -
                2 *
                    ((binaryLogCenter (heightTenBinaryIndex 30) 12 (30 : ℝ) : ℝ) : ℂ) *
                  (1 - heightTenReflectedEndpoint) +
                2) /
            (1 - heightTenReflectedEndpoint) ^ 3 -
          heightTenRoundedCpowCenter 30 *
              ((binaryLogCenter (heightTenBinaryIndex 30) 12 (30 : ℝ) : ℝ) : ℂ) ^ 2 /
            2 +
        heightTenRoundedCpowCenter 30 / 30 *
              (heightTenReflectedEndpoint *
                    ((binaryLogCenter (heightTenBinaryIndex 30) 12 (30 : ℝ) : ℝ) : ℂ) ^ 2 -
                2 *
                  ((binaryLogCenter (heightTenBinaryIndex 30) 12 (30 : ℝ) : ℝ) : ℂ)) /
            12) =
      heightTenRoundedLogSqCpowSum - heightTenCompactLogSqCpowSum by ring]
  exact norm_heightTenRoundedLogSqCpowSum_sub_compact_le

private theorem norm_heightTenChunkedEulerZetaSecondApprox_lt_sixTwentyFifths :
    ‖heightTenChunkedEulerZetaSecondApprox‖ < (6 / 25 : ℝ) := by
  apply (sq_lt_sq₀ (norm_nonneg _) (by norm_num)).mp
  rw [← Complex.normSq_eq_norm_sq]
  norm_num [heightTenChunkedEulerZetaSecondApprox,
    heightTenCompactLogSqCpowSum, heightTenCompactLogSqCpowChunk,
    heightTenRoundedCpowCenter, heightTenBinaryIndex, binaryLogCenter,
    logAtanhPartial, heightTenReflectedEndpoint, Complex.normSq_apply,
    Complex.div_re, Complex.div_im, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, pow_succ]

theorem norm_heightTenRoundedEulerZetaSecondApprox_lt_oneQuarter :
    ‖heightTenRoundedEulerZetaSecondApprox‖ < (1 / 4 : ℝ) := by
  calc
    ‖heightTenRoundedEulerZetaSecondApprox‖ ≤
        ‖heightTenRoundedEulerZetaSecondApprox -
            heightTenChunkedEulerZetaSecondApprox‖ +
          ‖heightTenChunkedEulerZetaSecondApprox‖ := by
      simpa only [sub_add_cancel] using norm_add_le
        (heightTenRoundedEulerZetaSecondApprox -
          heightTenChunkedEulerZetaSecondApprox)
        heightTenChunkedEulerZetaSecondApprox
    _ < 3 / 1000000000 + 6 / 25 :=
      add_lt_add_of_le_of_lt
        norm_heightTenRoundedEulerZetaSecondApprox_sub_chunked_le
        norm_heightTenChunkedEulerZetaSecondApprox_lt_sixTwentyFifths
    _ < 1 / 4 := by norm_num

private theorem norm_log_sq_mul_cpow_reflectedEndpoint_sub_rounded_le
    {u : ℕ} (hu1 : 1 ≤ u) (hu30 : u ≤ 30) :
    ‖((((Real.log u : ℝ) : ℂ) ^ 2) *
          (u : ℂ) ^ (-heightTenReflectedEndpoint)) -
        ((((binaryLogCenter (heightTenBinaryIndex u) 12 u : ℝ) : ℂ) ^ 2) *
          heightTenRoundedCpowCenter u)‖ ≤
      (1 / 100000000 : ℝ) := by
  let P : ℂ := (u : ℂ) ^ (-heightTenReflectedEndpoint)
  let R : ℂ := heightTenRoundedCpowCenter u
  let l : ℝ := Real.log u
  let L : ℝ := binaryLogCenter (heightTenBinaryIndex u) 12 u
  have hdata := heightTen_binaryLog_data hu1 hu30
  have hPR : ‖P - R‖ ≤ (1 / 5000000000 : ℝ) := by
    simpa only [P, R] using
      norm_cpow_reflectedEndpoint_sub_heightTenRoundedCpowCenter_le hu1 hu30
  have hR : ‖R‖ ≤ (1 : ℝ) := by
    simpa only [R] using norm_heightTenRoundedCpowCenter_le_one hu1 hu30
  have hP : ‖P‖ ≤ 1 + (1 / 5000000000 : ℝ) := by
    calc
      ‖P‖ ≤ ‖R‖ + ‖R - P‖ := norm_le_norm_add_norm_sub R P
      _ = ‖R‖ + ‖P - R‖ := by rw [norm_sub_rev]
      _ ≤ 1 + (1 / 5000000000 : ℝ) := add_le_add hR hPR
  have hlL : |l - L| ≤ (1 / 1000000000000000000 : ℝ) := by
    simpa only [l, L] using hdata.2.2
  have hL : |L| ≤ (7 / 2 : ℝ) := by
    simpa only [L] using hdata.2.1
  have hl : |l| ≤ (4 : ℝ) := by
    calc
      |l| = |(l - L) + L| := by ring_nf
      _ ≤ |l - L| + |L| := abs_add_le _ _
      _ ≤ 1 / 1000000000000000000 + 7 / 2 := add_le_add hlL hL
      _ ≤ 4 := by norm_num
  have hsq : |l ^ 2 - L ^ 2| ≤ (1 / 100000000000000000 : ℝ) := by
    rw [show l ^ 2 - L ^ 2 = (l - L) * (l + L) by ring, abs_mul]
    calc
      |l - L| * |l + L| ≤
          (1 / 1000000000000000000 : ℝ) * (|l| + |L|) := by
        gcongr
        exact abs_add_le _ _
      _ ≤ (1 / 1000000000000000000 : ℝ) * (4 + 7 / 2) := by gcongr
      _ ≤ 1 / 100000000000000000 := by norm_num
  have hid :
      (((l : ℂ) ^ 2) * P) - (((L : ℂ) ^ 2) * R) =
        (((l ^ 2 - L ^ 2 : ℝ) : ℂ) * P) +
          ((L : ℂ) ^ 2) * (P - R) := by
    norm_num only [Complex.ofReal_sub, Complex.ofReal_pow]
    ring
  change ‖(((l : ℂ) ^ 2) * P - ((L : ℂ) ^ 2) * R)‖ ≤ _
  rw [hid]
  calc
    ‖(((l ^ 2 - L ^ 2 : ℝ) : ℂ) * P) +
        ((L : ℂ) ^ 2) * (P - R)‖ ≤
        ‖(((l ^ 2 - L ^ 2 : ℝ) : ℂ) * P)‖ +
          ‖((L : ℂ) ^ 2) * (P - R)‖ := norm_add_le _ _
    _ = |l ^ 2 - L ^ 2| * ‖P‖ + |L| ^ 2 * ‖P - R‖ := by
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ (1 / 100000000000000000 : ℝ) * (1 + 1 / 5000000000) +
        (7 / 2) ^ 2 * (1 / 5000000000) := by gcongr
    _ ≤ 1 / 100000000 := by norm_num

private theorem norm_logSqCpowSum_reflectedEndpoint_sub_rounded_le :
    ‖(∑ n ∈ range 30,
          ((((Real.log ((n : ℝ) + 1) : ℝ) : ℂ) ^ 2) *
            (((n : ℂ) + 1) ^ (-heightTenReflectedEndpoint)))) -
        heightTenRoundedLogSqCpowSum‖ ≤ (3 / 10000000 : ℝ) := by
  unfold heightTenRoundedLogSqCpowSum
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ n ∈ range 30,
        ((((Real.log ((n : ℝ) + 1) : ℝ) : ℂ) ^ 2) *
            (((n : ℂ) + 1) ^ (-heightTenReflectedEndpoint)) -
          (((binaryLogCenter (heightTenBinaryIndex (n + 1)) 12
            (n + 1) : ℝ) : ℂ) ^ 2) *
              heightTenRoundedCpowCenter (n + 1))‖ ≤
        ∑ _n ∈ range 30, (1 / 100000000 : ℝ) := by
      refine (norm_sum_le _ _).trans ?_
      apply Finset.sum_le_sum
      intro n hn
      simp only [Finset.mem_range] at hn
      simpa only [Nat.cast_add, Nat.cast_one] using
        norm_log_sq_mul_cpow_reflectedEndpoint_sub_rounded_le
          (u := n + 1) (by omega) (by omega)
    _ = 3 / 10000000 := by norm_num

private theorem norm_eulerMaclaurinTwoZetaSecondExplicit_reflectedEndpoint_sub_rounded_le :
    ‖eulerMaclaurinTwoZetaSecondExplicitFormula heightTenReflectedEndpoint 30 -
        heightTenRoundedEulerZetaSecondApprox‖ ≤ (1 / 1000000 : ℝ) := by
  let P : ℂ := ((30 : ℕ) : ℂ) ^ (-heightTenReflectedEndpoint)
  let R : ℂ := heightTenRoundedCpowCenter 30
  let l : ℝ := Real.log 30
  let L : ℝ := binaryLogCenter (heightTenBinaryIndex 30) 12 (30 : ℝ)
  let d : ℂ := 1 - heightTenReflectedEndpoint
  have hdata := heightTen_binaryLog_data (u := 30) (by norm_num) (by norm_num)
  have hPR : ‖P - R‖ ≤ (1 / 5000000000 : ℝ) := by
    simpa only [P, R, Nat.cast_ofNat] using
      norm_cpow_reflectedEndpoint_sub_heightTenRoundedCpowCenter_le
        (u := 30) (by norm_num) (by norm_num)
  have hR : ‖R‖ ≤ (1 : ℝ) := by
    simpa only [R] using
      norm_heightTenRoundedCpowCenter_le_one (u := 30) (by norm_num) (by norm_num)
  have hP : ‖P‖ ≤ 1 + (1 / 5000000000 : ℝ) := by
    calc
      ‖P‖ ≤ ‖R‖ + ‖R - P‖ := norm_le_norm_add_norm_sub R P
      _ = ‖R‖ + ‖P - R‖ := by rw [norm_sub_rev]
      _ ≤ 1 + (1 / 5000000000 : ℝ) := add_le_add hR hPR
  have hlL : |l - L| ≤ (1 / 1000000000000000000 : ℝ) := by
    simpa only [l, L, Nat.cast_ofNat] using hdata.2.2
  have hL : |L| ≤ (7 / 2 : ℝ) := by
    simpa only [L, Nat.cast_ofNat] using hdata.2.1
  have hl : |l| ≤ (4 : ℝ) := by
    calc
      |l| = |(l - L) + L| := by ring_nf
      _ ≤ |l - L| + |L| := abs_add_le _ _
      _ ≤ 1 / 1000000000000000000 + 7 / 2 := add_le_add hlL hL
      _ ≤ 4 := by norm_num
  have hsq : |l ^ 2 - L ^ 2| ≤ (1 / 100000000000000000 : ℝ) := by
    rw [show l ^ 2 - L ^ 2 = (l - L) * (l + L) by ring, abs_mul]
    calc
      |l - L| * |l + L| ≤
          (1 / 1000000000000000000 : ℝ) * (|l| + |L|) := by
        gcongr
        exact abs_add_le _ _
      _ ≤ (1 / 1000000000000000000 : ℝ) * (4 + 7 / 2) := by gcongr
      _ ≤ 1 / 100000000000000000 := by norm_num
  have hd : ‖d‖ ≤ (11 : ℝ) := by
    dsimp only [d]
    apply (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mp
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [heightTenReflectedEndpoint, Complex.normSq_apply]
  have hdInv : ‖d⁻¹‖ ≤ (1 / 10 : ℝ) := by
    have hdLower : (10 : ℝ) ≤ ‖d‖ := by
      calc
        10 = |d.im| := by norm_num [d, heightTenReflectedEndpoint]
        _ ≤ ‖d‖ := Complex.abs_im_le_norm d
    rw [norm_inv]
    simpa only [one_div] using
      one_div_le_one_div_of_le (by norm_num) hdLower
  let Kl : ℂ := ((l : ℂ) ^ 2) * d ^ 2 - 2 * (l : ℂ) * d + 2
  let KL : ℂ := ((L : ℂ) ^ 2) * d ^ 2 - 2 * (L : ℂ) * d + 2
  have hKl : ‖Kl‖ ≤ (2026 : ℝ) := by
    dsimp only [Kl]
    calc
      ‖(l : ℂ) ^ 2 * d ^ 2 - 2 * (l : ℂ) * d + 2‖ ≤
          ‖(l : ℂ) ^ 2 * d ^ 2‖ + ‖2 * (l : ℂ) * d‖ + ‖(2 : ℂ)‖ := by
        calc
          ‖(l : ℂ) ^ 2 * d ^ 2 - 2 * (l : ℂ) * d + 2‖ ≤
              ‖(l : ℂ) ^ 2 * d ^ 2 - 2 * (l : ℂ) * d‖ + ‖(2 : ℂ)‖ :=
            norm_add_le _ _
          _ ≤ (‖(l : ℂ) ^ 2 * d ^ 2‖ + ‖2 * (l : ℂ) * d‖) + ‖(2 : ℂ)‖ := by
            gcongr
            exact norm_sub_le _ _
      _ = |l| ^ 2 * ‖d‖ ^ 2 + 2 * |l| * ‖d‖ + 2 := by
        rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow,
          Complex.norm_real, Real.norm_eq_abs]
        norm_num
      _ ≤ 4 ^ 2 * 11 ^ 2 + 2 * 4 * 11 + 2 := by gcongr
      _ = 2026 := by norm_num
  have hKdiff : ‖Kl - KL‖ ≤ (1 / 10000000000000 : ℝ) := by
    have hid : Kl - KL =
        (((l ^ 2 - L ^ 2 : ℝ) : ℂ) * d ^ 2) -
          2 * (((l - L : ℝ) : ℂ)) * d := by
      dsimp only [Kl, KL]
      norm_num only [Complex.ofReal_sub, Complex.ofReal_pow]
      ring
    rw [hid]
    calc
      ‖(((l ^ 2 - L ^ 2 : ℝ) : ℂ) * d ^ 2) -
          2 * (((l - L : ℝ) : ℂ)) * d‖ ≤
          ‖(((l ^ 2 - L ^ 2 : ℝ) : ℂ) * d ^ 2)‖ +
            ‖2 * (((l - L : ℝ) : ℂ)) * d‖ := norm_sub_le _ _
      _ = |l ^ 2 - L ^ 2| * ‖d‖ ^ 2 + 2 * |l - L| * ‖d‖ := by
        rw [norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_real,
          Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs]
        norm_num
      _ ≤ (1 / 100000000000000000 : ℝ) * 11 ^ 2 +
          2 * (1 / 1000000000000000000) * 11 := by gcongr
      _ ≤ 1 / 10000000000000 := by norm_num
  have hmain :
      ‖((30 : ℂ) * P) * Kl / d ^ 3 - ((30 : ℂ) * R) * KL / d ^ 3‖ ≤
        (1 / 10000000 : ℝ) := by
    have hid :
        ((30 : ℂ) * P) * Kl / d ^ 3 - ((30 : ℂ) * R) * KL / d ^ 3 =
          (30 : ℂ) * ((P - R) * Kl + R * (Kl - KL)) / d ^ 3 := by ring
    rw [hid, div_eq_mul_inv, ← inv_pow, norm_mul, norm_mul, norm_pow]
    rw [show ‖(30 : ℂ)‖ = (30 : ℝ) by norm_num]
    calc
      30 * ‖(P - R) * Kl + R * (Kl - KL)‖ * ‖d⁻¹‖ ^ 3 ≤
          30 * (‖P - R‖ * ‖Kl‖ + ‖R‖ * ‖Kl - KL‖) * ‖d⁻¹‖ ^ 3 := by
        gcongr
        calc
          ‖(P - R) * Kl + R * (Kl - KL)‖ ≤
              ‖(P - R) * Kl‖ + ‖R * (Kl - KL)‖ := norm_add_le _ _
          _ = ‖P - R‖ * ‖Kl‖ + ‖R‖ * ‖Kl - KL‖ := by rw [norm_mul, norm_mul]
      _ ≤ 30 * ((1 / 5000000000 : ℝ) * 2026 +
          1 * (1 / 10000000000000)) * (1 / 10) ^ 3 := by gcongr
      _ ≤ 1 / 10000000 := by norm_num
  have hhalf :
      ‖P * (l : ℂ) ^ 2 / 2 - R * (L : ℂ) ^ 2 / 2‖ ≤
        (1 / 100000000 : ℝ) := by
    have hthirty :=
      norm_log_sq_mul_cpow_reflectedEndpoint_sub_rounded_le
        (u := 30) (by norm_num) (by norm_num)
    change ‖(l : ℂ) ^ 2 * P - (L : ℂ) ^ 2 * R‖ ≤
      (1 / 100000000 : ℝ) at hthirty
    calc
      ‖P * (l : ℂ) ^ 2 / 2 - R * (L : ℂ) ^ 2 / 2‖ =
          ‖((l : ℂ) ^ 2 * P - (L : ℂ) ^ 2 * R) / 2‖ := by
        congr 1
        ring
      _ ≤ (1 / 100000000 : ℝ) / 2 := by
        rw [norm_div, Complex.norm_ofNat]
        gcongr
      _ ≤ 1 / 100000000 := by norm_num
  let Jl : ℂ := heightTenReflectedEndpoint * (l : ℂ) ^ 2 - 2 * (l : ℂ)
  let JL : ℂ := heightTenReflectedEndpoint * (L : ℂ) ^ 2 - 2 * (L : ℂ)
  have hsNorm : ‖heightTenReflectedEndpoint‖ ≤ (11 : ℝ) := by
    calc
      ‖heightTenReflectedEndpoint‖ ≤
          ‖(((1 / 2 : ℝ) : ℂ))‖ + ‖(10 : ℂ) * I‖ := by
        simpa only [heightTenReflectedEndpoint] using
          norm_sub_le (((1 / 2 : ℝ) : ℂ)) ((10 : ℂ) * I)
      _ ≤ 11 := by norm_num
  have hJl : ‖Jl‖ ≤ (184 : ℝ) := by
    dsimp only [Jl]
    calc
      ‖heightTenReflectedEndpoint * (l : ℂ) ^ 2 - 2 * (l : ℂ)‖ ≤
          ‖heightTenReflectedEndpoint * (l : ℂ) ^ 2‖ + ‖2 * (l : ℂ)‖ :=
        norm_sub_le _ _
      _ = ‖heightTenReflectedEndpoint‖ * |l| ^ 2 + 2 * |l| := by
        rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
        norm_num
      _ ≤ 11 * 4 ^ 2 + 2 * 4 := by gcongr
      _ = 184 := by norm_num
  have hJdiff : ‖Jl - JL‖ ≤ (1 / 1000000000000000 : ℝ) := by
    have hid : Jl - JL =
        heightTenReflectedEndpoint * (((l ^ 2 - L ^ 2 : ℝ) : ℂ)) -
          2 * (((l - L : ℝ) : ℂ)) := by
      dsimp only [Jl, JL]
      norm_num only [Complex.ofReal_sub, Complex.ofReal_pow]
      ring
    rw [hid]
    calc
      ‖heightTenReflectedEndpoint * (((l ^ 2 - L ^ 2 : ℝ) : ℂ)) -
          2 * (((l - L : ℝ) : ℂ))‖ ≤
          ‖heightTenReflectedEndpoint * (((l ^ 2 - L ^ 2 : ℝ) : ℂ))‖ +
            ‖2 * (((l - L : ℝ) : ℂ))‖ := norm_sub_le _ _
      _ = ‖heightTenReflectedEndpoint‖ * |l ^ 2 - L ^ 2| +
          2 * |l - L| := by
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          Complex.norm_real, Real.norm_eq_abs]
        norm_num
      _ ≤ 11 * (1 / 100000000000000000 : ℝ) +
          2 * (1 / 1000000000000000000) := by gcongr
      _ ≤ 1 / 1000000000000000 := by norm_num
  have hcorrection :
      ‖(P / 30) * Jl / 12 - (R / 30) * JL / 12‖ ≤
        (1 / 100000000 : ℝ) := by
    have hid :
        (P / 30) * Jl / 12 - (R / 30) * JL / 12 =
          ((P - R) * Jl + R * (Jl - JL)) / (30 * 12) := by ring
    rw [hid, norm_div]
    rw [show ‖(30 * 12 : ℂ)‖ = (360 : ℝ) by norm_num]
    calc
      ‖(P - R) * Jl + R * (Jl - JL)‖ / 360 ≤
          (‖P - R‖ * ‖Jl‖ + ‖R‖ * ‖Jl - JL‖) / 360 := by
        gcongr
        calc
          ‖(P - R) * Jl + R * (Jl - JL)‖ ≤
              ‖(P - R) * Jl‖ + ‖R * (Jl - JL)‖ := norm_add_le _ _
          _ = ‖P - R‖ * ‖Jl‖ + ‖R‖ * ‖Jl - JL‖ := by rw [norm_mul, norm_mul]
      _ ≤ ((1 / 5000000000 : ℝ) * 184 +
          1 * (1 / 1000000000000000)) / 360 := by gcongr
      _ ≤ 1 / 100000000 := by norm_num
  have hsum := norm_logSqCpowSum_reflectedEndpoint_sub_rounded_le
  have hpowOne :
      ((30 : ℕ) : ℂ) ^ (1 - heightTenReflectedEndpoint) =
        ((30 : ℕ) : ℂ) * P := by
    dsimp only [P]
    rw [show (1 : ℂ) - heightTenReflectedEndpoint =
        (1 : ℂ) + (-heightTenReflectedEndpoint) by ring,
      Complex.cpow_add _ _ (by norm_num), Complex.cpow_one]
  have hpowNegOne :
      ((30 : ℕ) : ℂ) ^ (-heightTenReflectedEndpoint - 1) = P / 30 := by
    dsimp only [P]
    rw [show -heightTenReflectedEndpoint - (1 : ℂ) =
        -heightTenReflectedEndpoint + (-1 : ℂ) by ring,
      Complex.cpow_add _ _ (by norm_num), Complex.cpow_neg_one]
    ring
  rw [eulerMaclaurinTwoZetaSecondExplicitFormula]
  rw [hpowOne, hpowNegOne]
  change ‖((∑ n ∈ range 30,
          ((((Real.log ((n : ℝ) + 1) : ℝ) : ℂ) ^ 2) *
            (((n : ℂ) + 1) ^ (-heightTenReflectedEndpoint)))) -
        ((30 : ℂ) * P) * Kl / d ^ 3 - P * (l : ℂ) ^ 2 / 2 +
          (P / 30) * Jl / 12) -
      (heightTenRoundedLogSqCpowSum - ((30 : ℂ) * R) * KL / d ^ 3 -
        R * (L : ℂ) ^ 2 / 2 + (R / 30) * JL / 12)‖ ≤ _
  have hid :
      ((∑ n ∈ range 30,
            ((((Real.log ((n : ℝ) + 1) : ℝ) : ℂ) ^ 2) *
              (((n : ℂ) + 1) ^ (-heightTenReflectedEndpoint)))) -
          ((30 : ℂ) * P) * Kl / d ^ 3 - P * (l : ℂ) ^ 2 / 2 +
            (P / 30) * Jl / 12) -
        (heightTenRoundedLogSqCpowSum - ((30 : ℂ) * R) * KL / d ^ 3 -
          R * (L : ℂ) ^ 2 / 2 + (R / 30) * JL / 12) =
      ((∑ n ∈ range 30,
          ((((Real.log ((n : ℝ) + 1) : ℝ) : ℂ) ^ 2) *
            (((n : ℂ) + 1) ^ (-heightTenReflectedEndpoint)))) -
          heightTenRoundedLogSqCpowSum) -
        (((30 : ℂ) * P) * Kl / d ^ 3 - ((30 : ℂ) * R) * KL / d ^ 3) -
        (P * (l : ℂ) ^ 2 / 2 - R * (L : ℂ) ^ 2 / 2) +
        ((P / 30) * Jl / 12 - (R / 30) * JL / 12) := by ring
  rw [hid]
  calc
    ‖((∑ n ∈ range 30,
          ((((Real.log ((n : ℝ) + 1) : ℝ) : ℂ) ^ 2) *
            (((n : ℂ) + 1) ^ (-heightTenReflectedEndpoint)))) -
          heightTenRoundedLogSqCpowSum) -
        (((30 : ℂ) * P) * Kl / d ^ 3 - ((30 : ℂ) * R) * KL / d ^ 3) -
        (P * (l : ℂ) ^ 2 / 2 - R * (L : ℂ) ^ 2 / 2) +
        ((P / 30) * Jl / 12 - (R / 30) * JL / 12)‖ ≤
        ‖(∑ n ∈ range 30,
          ((((Real.log ((n : ℝ) + 1) : ℝ) : ℂ) ^ 2) *
            (((n : ℂ) + 1) ^ (-heightTenReflectedEndpoint)))) -
          heightTenRoundedLogSqCpowSum‖ +
        ‖((30 : ℂ) * P) * Kl / d ^ 3 - ((30 : ℂ) * R) * KL / d ^ 3‖ +
        ‖P * (l : ℂ) ^ 2 / 2 - R * (L : ℂ) ^ 2 / 2‖ +
        ‖(P / 30) * Jl / 12 - (R / 30) * JL / 12‖ := by
      calc
        ‖_‖ ≤ ‖((∑ n ∈ range 30,
            ((((Real.log ((n : ℝ) + 1) : ℝ) : ℂ) ^ 2) *
              (((n : ℂ) + 1) ^ (-heightTenReflectedEndpoint)))) -
            heightTenRoundedLogSqCpowSum) -
          (((30 : ℂ) * P) * Kl / d ^ 3 - ((30 : ℂ) * R) * KL / d ^ 3) -
          (P * (l : ℂ) ^ 2 / 2 - R * (L : ℂ) ^ 2 / 2)‖ +
          ‖(P / 30) * Jl / 12 - (R / 30) * JL / 12‖ := norm_add_le _ _
        _ ≤ (‖(∑ n ∈ range 30,
              ((((Real.log ((n : ℝ) + 1) : ℝ) : ℂ) ^ 2) *
                (((n : ℂ) + 1) ^ (-heightTenReflectedEndpoint)))) -
              heightTenRoundedLogSqCpowSum‖ +
            ‖((30 : ℂ) * P) * Kl / d ^ 3 - ((30 : ℂ) * R) * KL / d ^ 3‖ +
            ‖P * (l : ℂ) ^ 2 / 2 - R * (L : ℂ) ^ 2 / 2‖) +
          ‖(P / 30) * Jl / 12 - (R / 30) * JL / 12‖ := by
            exact add_le_add
              ((norm_sub_le _ _).trans
                (add_le_add (norm_sub_le _ _) (le_refl _)))
              (le_refl _)
    _ ≤ 3 / 10000000 + 1 / 10000000 + 1 / 100000000 +
        1 / 100000000 := by gcongr
    _ ≤ 1 / 1000000 := by norm_num

private theorem differentiableAt_eulerMaclaurinTwoZetaDerivFiniteFormula
    {s : ℂ} (hsOne : s ≠ 1) {N : ℕ} (hN : 1 ≤ N) :
    DifferentiableAt ℂ (fun w => eulerMaclaurinTwoZetaDerivFiniteFormula w N) s := by
  unfold eulerMaclaurinTwoZetaDerivFiniteFormula
    eulerMaclaurinOneZetaDerivFiniteFormula
    eulerMaclaurinTwoCorrectionDerivFiniteFormula
  have hNzero : (N : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_zero_of_lt hN)
  have hsum : DifferentiableAt ℂ
      (fun w => ∑ n ∈ range N,
        -(((Real.log ((n : ℝ) + 1) : ℝ) : ℂ)) *
          (((n : ℂ) + 1) ^ (-w))) s := by
    apply DifferentiableAt.fun_sum
    intro n _hn
    have hbase : (n : ℂ) + 1 ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      norm_num at hre
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    exact (differentiableAt_id.neg.const_cpow (Or.inl hbase)).const_mul
      (-(((Real.log ((n : ℝ) + 1) : ℝ) : ℂ)))
  have hpowOne : DifferentiableAt ℂ (fun w : ℂ => (N : ℂ) ^ (1 - w)) s :=
    (differentiableAt_const (c := (1 : ℂ))).sub differentiableAt_id |>.const_cpow
      (Or.inl hNzero)
  have hpowNeg : DifferentiableAt ℂ (fun w : ℂ => (N : ℂ) ^ (-w)) s :=
    differentiableAt_id.neg.const_cpow (Or.inl hNzero)
  have hpowNegOne : DifferentiableAt ℂ (fun w : ℂ => (N : ℂ) ^ (-w - 1)) s :=
    (differentiableAt_id.neg.sub_const (1 : ℂ)).const_cpow (Or.inl hNzero)
  have hden : DifferentiableAt ℂ (fun w : ℂ => 1 - w) s := by fun_prop
  have hdenNe : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr hsOne.symm
  have hmain : DifferentiableAt ℂ (fun w : ℂ =>
      (((N : ℂ) ^ (1 - w) * (((Real.log (N : ℝ) : ℝ) : ℂ)) * (-1) * (1 - w) -
          (N : ℂ) ^ (1 - w) * (-1)) / (1 - w) ^ 2)) s := by
    have hfirst := (((hpowOne.mul_const
      (((Real.log (N : ℝ) : ℝ) : ℂ))).mul_const (-1 : ℂ)).mul hden)
    have hsecond := hpowOne.mul_const (-1 : ℂ)
    exact (hfirst.sub hsecond).div (hden.pow 2) (pow_ne_zero 2 hdenNe)
  have hhalf : DifferentiableAt ℂ (fun w : ℂ =>
      ((N : ℂ) ^ (-w) * (((Real.log (N : ℝ) : ℝ) : ℂ)) * (-1)) / 2) s := by
    have hlog := hpowNeg.mul_const (((Real.log (N : ℝ) : ℝ) : ℂ))
    have hneg := hlog.mul_const (-1 : ℂ)
    exact hneg.div_const 2
  have htwo : DifferentiableAt ℂ (fun w : ℂ =>
      ((N : ℂ) ^ (-w - 1) -
        w * (N : ℂ) ^ (-w - 1) * (((Real.log (N : ℝ) : ℝ) : ℂ))) / 12) s := by
    exact (hpowNegOne.sub
      ((differentiableAt_id.mul hpowNegOne).mul_const
        (((Real.log (N : ℝ) : ℝ) : ℂ)))).div_const 12
  exact ((hsum.sub hmain).sub hhalf).add htwo

/-- Cauchy's estimate turns the uniform first-derivative Euler--Maclaurin error on a circle into
an error ball for the actual second zeta derivative at its center. -/
theorem norm_deriv_deriv_riemannZeta_sub_eulerMaclaurinTwoZetaSecondFiniteFormula_le
    (s : ℂ) {r C : ℝ} (hr : 0 < r)
    (hballRe : r < s.re) (hballOne : r < dist s 1)
    {N : ℕ} (hN : 1 ≤ N)
    (hC : ∀ z ∈ Metric.sphere s r,
      eulerMaclaurinTwoZetaDerivError z N ≤ C) :
    ‖deriv (deriv riemannZeta) s -
        eulerMaclaurinTwoZetaSecondFiniteFormula s N‖ ≤ C / r := by
  let U : Set ℂ := {z | 0 < z.re ∧ z ≠ 1}
  let f : ℂ → ℂ := fun z =>
    deriv riemannZeta z - eulerMaclaurinTwoZetaDerivFiniteFormula z N
  have hclosed : Metric.closedBall s r ⊆ U := by
    intro z hz
    have hnorm : ‖z - s‖ ≤ r := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
    have hreDiff : |z.re - s.re| ≤ r :=
      (Complex.abs_re_le_norm (z - s)).trans hnorm
    have hzRe : 0 < z.re := by
      have hleft := (abs_le.mp hreDiff).1
      linarith
    have hsz : dist s z ≤ r := by
      simpa [dist_comm] using hz
    have hzOne : z ≠ 1 := by
      intro h
      have hsOneLe : dist s 1 ≤ r := by simpa [h] using hsz
      linarith
    exact ⟨hzRe, hzOne⟩
  have hopen : IsOpen U := by
    exact (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_compl_singleton)
  have hdiffOn : DifferentiableOn ℂ f U := by
    intro z hz
    have hzeta : DifferentiableAt ℂ (deriv riemannZeta) z :=
      (analyticOnNhd_deriv_riemannZeta z hz.2).differentiableAt
    have hfinite : DifferentiableAt ℂ
        (fun w => eulerMaclaurinTwoZetaDerivFiniteFormula w N) z :=
      differentiableAt_eulerMaclaurinTwoZetaDerivFiniteFormula hz.2 hN
    exact (hzeta.sub hfinite).differentiableWithinAt
  have hdiffCl : DiffContOnCl ℂ f (Metric.ball s r) :=
    hdiffOn.diffContOnCl_ball hclosed
  have hsphere : ∀ z ∈ Metric.sphere s r, ‖f z‖ ≤ C := by
    intro z hz
    have hzClosed : z ∈ Metric.closedBall s r :=
      Metric.sphere_subset_closedBall hz
    have hzU := hclosed hzClosed
    have herror :=
      norm_deriv_riemannZeta_sub_eulerMaclaurinTwoZetaDerivApprox_le_of_re_pos
        hzU.2 hzU.1 hN
    rw [eulerMaclaurinTwoZetaDerivApprox_eq_finiteFormula
      z hzU.2 hzU.1 hN] at herror
    exact herror.trans (hC z hz)
  have hCauchy : ‖deriv f s‖ ≤ C / r :=
    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hdiffCl hsphere
  have hsClosed : s ∈ Metric.closedBall s r := by
    simp [hr.le]
  have hsU := hclosed hsClosed
  have hzetaAt : DifferentiableAt ℂ (deriv riemannZeta) s :=
    (analyticOnNhd_deriv_riemannZeta s hsU.2).differentiableAt
  have hfiniteAt :=
    differentiableAt_eulerMaclaurinTwoZetaDerivFiniteFormula hsU.2 hN
  simpa only [f, deriv_fun_sub hzetaAt hfiniteAt,
    eulerMaclaurinTwoZetaSecondFiniteFormula] using hCauchy

theorem heightTenReflectedEndpoint_circle_derivError_le_oneTenth
    {z : ℂ} (hz : z ∈ Metric.sphere heightTenReflectedEndpoint (1 / 4 : ℝ)) :
    eulerMaclaurinTwoZetaDerivError z 30 ≤ (1 / 10 : ℝ) := by
  have hnormDiff : ‖z - heightTenReflectedEndpoint‖ = (1 / 4 : ℝ) := by
    simpa only [Metric.mem_sphere, dist_eq_norm] using hz
  have hreDiff : |z.re - heightTenReflectedEndpoint.re| ≤ (1 / 4 : ℝ) :=
    (Complex.abs_re_le_norm (z - heightTenReflectedEndpoint)).trans hnormDiff.le
  have hzRe : (1 / 4 : ℝ) ≤ z.re := by
    have hleft := (abs_le.mp hreDiff).1
    norm_num [heightTenReflectedEndpoint] at hleft ⊢
    linarith
  have hsNorm : ‖heightTenReflectedEndpoint‖ ≤ (21 / 2 : ℝ) := by
    apply (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mp
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [heightTenReflectedEndpoint, Complex.normSq_apply]
  have hzNorm : ‖z‖ ≤ (11 : ℝ) := by
    calc
      ‖z‖ = ‖(z - heightTenReflectedEndpoint) + heightTenReflectedEndpoint‖ := by ring_nf
      _ ≤ ‖z - heightTenReflectedEndpoint‖ + ‖heightTenReflectedEndpoint‖ :=
        norm_add_le _ _
      _ ≤ 1 / 4 + 21 / 2 := add_le_add hnormDiff.le hsNorm
      _ ≤ 11 := by norm_num
  have hzOneNorm : ‖z + 1‖ ≤ (12 : ℝ) := by
    calc
      ‖z + 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 12 := by norm_num at ⊢; linarith
  have hzTwoNorm : ‖z + 2‖ ≤ (13 : ℝ) := by
    calc
      ‖z + 2‖ ≤ ‖z‖ + ‖(2 : ℂ)‖ := norm_add_le _ _
      _ ≤ 13 := by norm_num at ⊢; linarith
  have hpoly : ‖3 * z ^ 2 + 6 * z + 2‖ ≤ (431 : ℝ) := by
    calc
      ‖3 * z ^ 2 + 6 * z + 2‖ ≤
          ‖3 * z ^ 2‖ + ‖6 * z‖ + ‖(2 : ℂ)‖ := by
        exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
      _ = 3 * ‖z‖ ^ 2 + 6 * ‖z‖ + 2 := by
        rw [norm_mul, norm_mul, norm_pow]
        norm_num
      _ ≤ 3 * 11 ^ 2 + 6 * 11 + 2 := by gcongr
      _ = 431 := by norm_num
  have hcubic : ‖z * (z + 1) * (z + 2)‖ ≤ (1716 : ℝ) := by
    rw [norm_mul, norm_mul]
    calc
      ‖z‖ * ‖z + 1‖ * ‖z + 2‖ ≤ 11 * 12 * 13 := by gcongr
      _ = 1716 := by norm_num
  have hpow : (30 : ℝ) ^ (-z.re - 2) ≤ (1 / 900 : ℝ) := by
    calc
      (30 : ℝ) ^ (-z.re - 2) ≤ (30 : ℝ) ^ (-2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 1 / 900 := by
        norm_num [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 30), Real.rpow_two]
  have hden : (2 : ℝ) ≤ z.re + 2 := by linarith
  have hdenPos : (0 : ℝ) < z.re + 2 := by linarith
  have hdenInv : (z.re + 2)⁻¹ ≤ (1 / 2 : ℝ) := by
    simpa only [one_div] using
      one_div_le_one_div_of_le (by norm_num) hden
  have hdenSqInv : 1 / (z.re + 2) ^ 2 ≤ (1 / 4 : ℝ) := by
    rw [one_div, ← inv_pow]
    calc
      (z.re + 2)⁻¹ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by gcongr
      _ = 1 / 4 := by norm_num
  have hlogNonneg : (0 : ℝ) ≤ Real.log 30 := Real.log_nonneg (by norm_num)
  have hlogDiv : Real.log 30 / (z.re + 2) ≤ (341 / 200 : ℝ) := by
    rw [div_eq_mul_inv]
    calc
      Real.log 30 * (z.re + 2)⁻¹ ≤ (341 / 100 : ℝ) * (1 / 2) := by
        gcongr
        exact log_thirty_lt_threeHundredFortyOne_div_oneHundred.le
      _ = 341 / 200 := by norm_num
  have htailOne :
      (1 / 48 : ℝ) * ((30 : ℝ) ^ (-z.re - 2) / (z.re + 2)) ≤
        (1 / 48 : ℝ) * ((1 / 900) * (1 / 2)) := by
    rw [div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact mul_le_mul hpow hdenInv (inv_nonneg.mpr hdenPos.le) (by norm_num)
  have htailTwo :
      (1 / 48 : ℝ) * ((30 : ℝ) ^ (-(z.re + 2)) *
          (Real.log 30 / (z.re + 2) + 1 / (z.re + 2) ^ 2)) ≤
        (1 / 48 : ℝ) * ((1 / 900) * ((341 / 200) + 1 / 4)) := by
    have hpow' : (30 : ℝ) ^ (-(z.re + 2)) ≤ (1 / 900 : ℝ) := by
      rw [show -(z.re + 2) = -z.re - 2 by ring]
      exact hpow
    gcongr
  unfold eulerMaclaurinTwoZetaDerivError
  calc
    ‖3 * z ^ 2 + 6 * z + 2‖ *
          ((1 / 48 : ℝ) * ((30 : ℝ) ^ (-z.re - 2) / (z.re + 2))) +
        ‖z * (z + 1) * (z + 2)‖ *
          ((1 / 48 : ℝ) * ((30 : ℝ) ^ (-(z.re + 2)) *
            (Real.log 30 / (z.re + 2) + 1 / (z.re + 2) ^ 2))) ≤
        431 * ((1 / 48 : ℝ) * ((1 / 900) * (1 / 2))) +
          1716 * ((1 / 48 : ℝ) * ((1 / 900) * ((341 / 200) + 1 / 4))) := by
      gcongr
    _ ≤ 1 / 10 := by norm_num

theorem norm_eulerMaclaurinTwoZetaSecondFiniteFormula_heightTenReflectedEndpoint_lt :
    ‖eulerMaclaurinTwoZetaSecondFiniteFormula heightTenReflectedEndpoint 30‖ <
      (13 / 50 : ℝ) := by
  have hsOne : heightTenReflectedEndpoint ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    norm_num [heightTenReflectedEndpoint] at him
  rw [eulerMaclaurinTwoZetaSecondFiniteFormula_eq_explicit
    heightTenReflectedEndpoint hsOne (by norm_num)]
  calc
    ‖eulerMaclaurinTwoZetaSecondExplicitFormula heightTenReflectedEndpoint 30‖ ≤
        ‖eulerMaclaurinTwoZetaSecondExplicitFormula heightTenReflectedEndpoint 30 -
            heightTenRoundedEulerZetaSecondApprox‖ +
          ‖heightTenRoundedEulerZetaSecondApprox‖ := by
      simpa only [sub_add_cancel] using norm_add_le
        (eulerMaclaurinTwoZetaSecondExplicitFormula heightTenReflectedEndpoint 30 -
          heightTenRoundedEulerZetaSecondApprox)
        heightTenRoundedEulerZetaSecondApprox
    _ < 1 / 1000000 + 1 / 4 :=
      add_lt_add_of_le_of_lt
        norm_eulerMaclaurinTwoZetaSecondExplicit_reflectedEndpoint_sub_rounded_le
        norm_heightTenRoundedEulerZetaSecondApprox_lt_oneQuarter
    _ < 13 / 50 := by norm_num

theorem norm_deriv_deriv_riemannZeta_heightTenReflectedEndpoint_lt :
    ‖deriv (deriv riemannZeta) heightTenReflectedEndpoint‖ < (33 / 50 : ℝ) := by
  have hballRe : (1 / 4 : ℝ) < heightTenReflectedEndpoint.re := by
    norm_num [heightTenReflectedEndpoint]
  have hballOne : (1 / 4 : ℝ) < dist heightTenReflectedEndpoint 1 := by
    have himLower : (10 : ℝ) ≤ ‖heightTenReflectedEndpoint - 1‖ := by
      calc
        10 = |(heightTenReflectedEndpoint - 1).im| := by
          norm_num [heightTenReflectedEndpoint]
        _ ≤ ‖heightTenReflectedEndpoint - 1‖ := Complex.abs_im_le_norm _
    rw [dist_eq_norm]
    linarith
  have herror :=
    norm_deriv_deriv_riemannZeta_sub_eulerMaclaurinTwoZetaSecondFiniteFormula_le
      heightTenReflectedEndpoint (r := (1 / 4 : ℝ)) (C := (1 / 10 : ℝ))
      (by norm_num) hballRe hballOne (N := 30) (by norm_num)
      (fun z hz => heightTenReflectedEndpoint_circle_derivError_le_oneTenth hz)
  calc
    ‖deriv (deriv riemannZeta) heightTenReflectedEndpoint‖ ≤
        ‖deriv (deriv riemannZeta) heightTenReflectedEndpoint -
            eulerMaclaurinTwoZetaSecondFiniteFormula heightTenReflectedEndpoint 30‖ +
          ‖eulerMaclaurinTwoZetaSecondFiniteFormula heightTenReflectedEndpoint 30‖ := by
      simpa only [sub_add_cancel] using norm_add_le
        (deriv (deriv riemannZeta) heightTenReflectedEndpoint -
          eulerMaclaurinTwoZetaSecondFiniteFormula heightTenReflectedEndpoint 30)
        (eulerMaclaurinTwoZetaSecondFiniteFormula heightTenReflectedEndpoint 30)
    _ < 2 / 5 + 13 / 50 := by
      have herror' :
          ‖deriv (deriv riemannZeta) heightTenReflectedEndpoint -
              eulerMaclaurinTwoZetaSecondFiniteFormula
                heightTenReflectedEndpoint 30‖ ≤ (2 / 5 : ℝ) := by
        norm_num at herror ⊢
        exact herror
      exact add_lt_add_of_le_of_lt herror'
        norm_eulerMaclaurinTwoZetaSecondFiniteFormula_heightTenReflectedEndpoint_lt
    _ = 33 / 50 := by norm_num

end

end LeanLab.Riemann
