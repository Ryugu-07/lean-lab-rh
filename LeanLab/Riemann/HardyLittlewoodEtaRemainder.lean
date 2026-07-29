import LeanLab.Riemann.BaezDuarteMellin
import LeanLab.Riemann.HardyLittlewoodEtaAbelTransfer
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Hardy--Littlewood's uniform eta remainder

This module attacks Lemma 3 of Hardy--Littlewood (1921). The finite core treats the alternating
logarithmic phase by inverse-difference summation. No eta remainder or analytic identification
is assumed.
-/

open Complex Filter Finset Real Set Topology
open scoped BigOperators

namespace LeanLab.Riemann

noncomputable section

/-- The unit-modulus part of the literal alternating eta term. -/
def hardyLittlewoodEtaUnitPhase (t : ℝ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else
    ((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) *
      Complex.exp ((-(t * Real.log n) : ℝ) * Complex.I))

/-- The positive logarithmic increment from `n` to `n+1`. -/
def hardyLittlewoodEtaLogIncrement (n : ℕ) : ℝ :=
  Real.log (n + 1 : ℝ) - Real.log (n : ℝ)

/-- The change in logarithmic phase between consecutive eta terms. -/
def hardyLittlewoodEtaPhaseIncrement (t : ℝ) (n : ℕ) : ℝ :=
  t * hardyLittlewoodEtaLogIncrement n

/-- The exact consecutive ratio of the unit phases. -/
def hardyLittlewoodEtaPhaseRatio (t : ℝ) (n : ℕ) : ℂ :=
  -Complex.exp
    ((-hardyLittlewoodEtaPhaseIncrement t n : ℝ) * Complex.I)

/-- The inverse-difference coefficient used to telescope a phase block. -/
def hardyLittlewoodEtaInverseDifference (t : ℝ) (n : ℕ) : ℂ :=
  (1 - hardyLittlewoodEtaPhaseRatio t n)⁻¹

theorem norm_hardyLittlewoodEtaUnitPhase
    (t : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    ‖hardyLittlewoodEtaUnitPhase t n‖ = 1 := by
  rw [hardyLittlewoodEtaUnitPhase, if_neg (by omega), norm_mul]
  have hre :
      (((-(t * Real.log n) : ℝ) : ℂ) * Complex.I).re = 0 := by
    change (-(t * Real.log n) : ℝ) * 0 - 0 * 1 = 0
    ring
  rw [Complex.norm_real, Real.norm_eq_abs, abs_pow, abs_neg, abs_one, one_pow,
    one_mul, Complex.norm_exp, hre, Real.exp_zero]

theorem hardyLittlewoodEtaLogIncrement_eq_log_div
    {n : ℕ} (hn : 1 ≤ n) :
    hardyLittlewoodEtaLogIncrement n =
      Real.log (((n : ℝ) + 1) / n) := by
  rw [hardyLittlewoodEtaLogIncrement,
    Real.log_div (by positivity : (n : ℝ) + 1 ≠ 0)
      (by positivity : (n : ℝ) ≠ 0)]

theorem hardyLittlewoodEtaLogIncrement_pos
    {n : ℕ} (hn : 1 ≤ n) :
    0 < hardyLittlewoodEtaLogIncrement n := by
  unfold hardyLittlewoodEtaLogIncrement
  have hnpos : (0 : ℝ) < n := by positivity
  have hn1pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hlt : (n : ℝ) < (n : ℝ) + 1 := by norm_num
  exact sub_pos.mpr (Real.strictMonoOn_log hnpos hn1pos hlt)

theorem hardyLittlewoodEtaLogIncrement_le_inv
    {n : ℕ} (hn : 1 ≤ n) :
    hardyLittlewoodEtaLogIncrement n ≤ (n : ℝ)⁻¹ := by
  rw [hardyLittlewoodEtaLogIncrement_eq_log_div hn]
  have hlog :=
    Real.log_le_sub_one_of_pos
      (show 0 < ((n : ℝ) + 1) / n by positivity)
  calc
    Real.log (((n : ℝ) + 1) / n)
        ≤ ((n : ℝ) + 1) / n - 1 := hlog
    _ = (n : ℝ)⁻¹ := by
      field_simp
      ring

theorem hardyLittlewoodEtaLogIncrement_antitone
    {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    hardyLittlewoodEtaLogIncrement n ≤
      hardyLittlewoodEtaLogIncrement m := by
  have hn : 1 ≤ n := hm.trans hmn
  rw [hardyLittlewoodEtaLogIncrement_eq_log_div hm,
    hardyLittlewoodEtaLogIncrement_eq_log_div hn]
  have hnratio : (0 : ℝ) < ((n : ℝ) + 1) / n := by positivity
  have hmratio : (0 : ℝ) < ((m : ℝ) + 1) / m := by positivity
  apply Real.strictMonoOn_log.monotoneOn hnratio hmratio
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < n)
    (by positivity : (0 : ℝ) < m)).2
  have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
  nlinarith

theorem abs_hardyLittlewoodEtaPhaseIncrement_le
    (t : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    |hardyLittlewoodEtaPhaseIncrement t n| ≤
      |t| * (n : ℝ)⁻¹ := by
  rw [hardyLittlewoodEtaPhaseIncrement, abs_mul,
    abs_of_pos (hardyLittlewoodEtaLogIncrement_pos hn)]
  exact mul_le_mul_of_nonneg_left
    (hardyLittlewoodEtaLogIncrement_le_inv hn) (abs_nonneg t)

/-- The unit-circle exponential is one-Lipschitz with respect to its real angle. -/
theorem norm_exp_mul_I_sub_exp_mul_I_le (x y : ℝ) :
    ‖Complex.exp (x * Complex.I) -
        Complex.exp (y * Complex.I)‖ ≤ |x - y| := by
  have hfactor :
      Complex.exp (x * Complex.I) -
          Complex.exp (y * Complex.I) =
        Complex.exp (y * Complex.I) *
          (Complex.exp ((x - y) * Complex.I) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    ring
  have hnorm :
      ‖Complex.exp (y * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [hfactor, norm_mul, hnorm, one_mul]
  have hchord :=
    Real.norm_exp_I_mul_ofReal_sub_one_le (x := x - y)
  have harg :
      ((x : ℂ) - (y : ℂ)) * Complex.I =
        Complex.I * ((x - y : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  rw [harg]
  simpa only [Real.norm_eq_abs] using hchord

theorem norm_hardyLittlewoodEtaPhaseRatio_sub_le
    (t : ℝ) (m n : ℕ) :
    ‖hardyLittlewoodEtaPhaseRatio t m -
        hardyLittlewoodEtaPhaseRatio t n‖ ≤
      |hardyLittlewoodEtaPhaseIncrement t m -
        hardyLittlewoodEtaPhaseIncrement t n| := by
  unfold hardyLittlewoodEtaPhaseRatio
  rw [← neg_sub, norm_neg]
  simpa only [neg_sub_neg, abs_sub_comm] using
    norm_exp_mul_I_sub_exp_mul_I_le
      (-hardyLittlewoodEtaPhaseIncrement t m)
      (-hardyLittlewoodEtaPhaseIncrement t n)

theorem norm_one_sub_hardyLittlewoodEtaPhaseRatio_ge_one
    (t : ℝ) (n : ℕ)
    (hphase : |hardyLittlewoodEtaPhaseIncrement t n| ≤ 1) :
    1 ≤ ‖1 - hardyLittlewoodEtaPhaseRatio t n‖ := by
  let e : ℂ :=
    Complex.exp
      ((-hardyLittlewoodEtaPhaseIncrement t n : ℝ) * Complex.I)
  have hchord : ‖e - 1‖ ≤ 1 := by
    calc
      ‖e - 1‖ ≤ |-hardyLittlewoodEtaPhaseIncrement t n - 0| := by
        simpa [e] using
          norm_exp_mul_I_sub_exp_mul_I_le
            (-hardyLittlewoodEtaPhaseIncrement t n) 0
      _ = |hardyLittlewoodEtaPhaseIncrement t n| := by simp
      _ ≤ 1 := hphase
  have htwo : (2 : ℝ) ≤ ‖(1 : ℂ) + e‖ + ‖e - 1‖ := by
    calc
      (2 : ℝ) = ‖(2 : ℂ)‖ := by norm_num
      _ = ‖((1 : ℂ) + e) + (1 - e)‖ := by congr 1; ring
      _ ≤ ‖(1 : ℂ) + e‖ + ‖1 - e‖ := norm_add_le _ _
      _ = ‖(1 : ℂ) + e‖ + ‖e - 1‖ := by
        rw [← norm_neg (1 - e)]
        congr 2
        ring
  unfold hardyLittlewoodEtaPhaseRatio
  rw [sub_neg_eq_add]
  change 1 ≤ ‖(1 : ℂ) + e‖
  linarith

theorem norm_hardyLittlewoodEtaInverseDifference_le_one
    (t : ℝ) (n : ℕ)
    (hphase : |hardyLittlewoodEtaPhaseIncrement t n| ≤ 1) :
    ‖hardyLittlewoodEtaInverseDifference t n‖ ≤ 1 := by
  rw [hardyLittlewoodEtaInverseDifference, norm_inv]
  exact inv_le_one_of_one_le₀
    (norm_one_sub_hardyLittlewoodEtaPhaseRatio_ge_one t n hphase)

/-- The literal eta term factors into a decreasing real amplitude and the unit phase. -/
theorem hardyLittlewoodEtaSourceTerm_eq_rpow_smul_unitPhase
    (sigma t : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    hardyLittlewoodEtaSourceTerm (sigma + t * Complex.I) n =
      (n : ℝ) ^ (-sigma) • hardyLittlewoodEtaUnitPhase t n := by
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hsplit :
      (n : ℂ) ^ (-(sigma + t * Complex.I)) =
        (((n : ℝ) ^ (-sigma) : ℝ) : ℂ) *
          Complex.exp ((-(t * Real.log n) : ℝ) * Complex.I) := by
    rw [show -(sigma + t * Complex.I) =
        ((-sigma : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * Complex.I by
      apply Complex.ext <;> simp]
    rw [Complex.cpow_add _ _ hnC]
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
    congr 1
    rw [Complex.cpow_def_of_ne_zero hnC]
    simp only [← Complex.natCast_log]
    congr 1
    apply Complex.ext <;> simp <;> ring
  rw [hardyLittlewoodEtaSourceTerm, if_neg (by omega),
    hardyLittlewoodEtaUnitPhase, if_neg (by omega), hsplit]
  change _ = (((n : ℝ) ^ (-sigma) : ℝ) : ℂ) *
    (((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) *
      Complex.exp ((-(t * Real.log n) : ℝ) * Complex.I)))
  ring

/-- The defined ratio is the exact ratio between consecutive actual unit phases. -/
theorem hardyLittlewoodEtaUnitPhase_succ
    (t : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    hardyLittlewoodEtaUnitPhase t (n + 1) =
      hardyLittlewoodEtaPhaseRatio t n *
        hardyLittlewoodEtaUnitPhase t n := by
  rw [hardyLittlewoodEtaUnitPhase, if_neg (by omega),
    hardyLittlewoodEtaUnitPhase, if_neg (by omega),
    hardyLittlewoodEtaPhaseRatio, hardyLittlewoodEtaPhaseIncrement,
    hardyLittlewoodEtaLogIncrement]
  have hsign :
      ((((-1 : ℝ) ^ (n + 1 + 1) : ℝ) : ℂ)) =
        -((((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ)) := by
    rw [pow_succ]
    norm_num
  rw [hsign]
  have hexp :
      Complex.exp ((-(t * Real.log (n + 1)) : ℝ) * Complex.I) =
        Complex.exp
            ((-(t * (Real.log ((n : ℝ) + 1) - Real.log n)) : ℝ) *
              Complex.I) *
      Complex.exp ((-(t * Real.log n) : ℝ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    apply Complex.ext
    · simp
    · simp
      ring
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_num
  rw [hcast]
  rw [hexp]
  ring

theorem abs_hardyLittlewoodEtaPhaseIncrement_le_one
    (t : ℝ) {N n : ℕ} (hN : 1 ≤ N)
    (ht : |t| ≤ N) (hNn : N ≤ n) :
    |hardyLittlewoodEtaPhaseIncrement t n| ≤ 1 := by
  have hn : 1 ≤ n := hN.trans hNn
  have htR : |t| ≤ (N : ℝ) := by exact_mod_cast ht
  have hNnR : (N : ℝ) ≤ n := by exact_mod_cast hNn
  calc
    |hardyLittlewoodEtaPhaseIncrement t n|
        ≤ |t| * (n : ℝ)⁻¹ :=
      abs_hardyLittlewoodEtaPhaseIncrement_le t hn
    _ ≤ (N : ℝ) * (n : ℝ)⁻¹ := by gcongr
    _ ≤ (n : ℝ) * (n : ℝ)⁻¹ := by gcongr
    _ = 1 := mul_inv_cancel₀ (by positivity)

/-- Inverse-difference summation rewrites each actual phase as one telescoping difference. -/
theorem hardyLittlewoodEtaUnitPhase_eq_inverseDifference_mul_sub
    (t : ℝ) {N n : ℕ} (hN : 1 ≤ N)
    (ht : |t| ≤ N) (hNn : N ≤ n) :
    hardyLittlewoodEtaUnitPhase t n =
      hardyLittlewoodEtaInverseDifference t n *
        (hardyLittlewoodEtaUnitPhase t n -
          hardyLittlewoodEtaUnitPhase t (n + 1)) := by
  have hn : 1 ≤ n := hN.trans hNn
  have hphase :=
    abs_hardyLittlewoodEtaPhaseIncrement_le_one t hN ht hNn
  have hdenNorm :=
    norm_one_sub_hardyLittlewoodEtaPhaseRatio_ge_one t n hphase
  have hden :
      (1 - hardyLittlewoodEtaPhaseRatio t n : ℂ) ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hdenNorm
    linarith
  rw [hardyLittlewoodEtaUnitPhase_succ t hn,
    hardyLittlewoodEtaInverseDifference]
  rw [← one_sub_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hden, one_mul]

theorem one_sub_hardyLittlewoodEtaPhaseRatio_ne_zero
    (t : ℝ) (n : ℕ)
    (hphase : |hardyLittlewoodEtaPhaseIncrement t n| ≤ 1) :
    (1 - hardyLittlewoodEtaPhaseRatio t n : ℂ) ≠ 0 := by
  have hnorm :=
    norm_one_sub_hardyLittlewoodEtaPhaseRatio_ge_one t n hphase
  intro hzero
  rw [hzero, norm_zero] at hnorm
  linarith

theorem norm_hardyLittlewoodEtaInverseDifference_sub_le
    (t : ℝ) (m n : ℕ)
    (hm : |hardyLittlewoodEtaPhaseIncrement t m| ≤ 1)
    (hn : |hardyLittlewoodEtaPhaseIncrement t n| ≤ 1) :
    ‖hardyLittlewoodEtaInverseDifference t m -
        hardyLittlewoodEtaInverseDifference t n‖ ≤
      |hardyLittlewoodEtaPhaseIncrement t m -
        hardyLittlewoodEtaPhaseIncrement t n| := by
  have hdm := one_sub_hardyLittlewoodEtaPhaseRatio_ne_zero t m hm
  have hdn := one_sub_hardyLittlewoodEtaPhaseRatio_ne_zero t n hn
  rw [hardyLittlewoodEtaInverseDifference,
    hardyLittlewoodEtaInverseDifference, inv_sub_inv' hdm hdn]
  calc
    ‖(1 - hardyLittlewoodEtaPhaseRatio t m)⁻¹ *
          ((1 - hardyLittlewoodEtaPhaseRatio t n) -
            (1 - hardyLittlewoodEtaPhaseRatio t m)) *
          (1 - hardyLittlewoodEtaPhaseRatio t n)⁻¹‖
        = ‖(1 - hardyLittlewoodEtaPhaseRatio t m)⁻¹‖ *
            ‖(1 - hardyLittlewoodEtaPhaseRatio t n) -
              (1 - hardyLittlewoodEtaPhaseRatio t m)‖ *
            ‖(1 - hardyLittlewoodEtaPhaseRatio t n)⁻¹‖ := by
          rw [norm_mul, norm_mul]
    _ ≤ 1 *
          ‖(1 - hardyLittlewoodEtaPhaseRatio t n) -
            (1 - hardyLittlewoodEtaPhaseRatio t m)‖ * 1 := by
      gcongr
      · exact norm_hardyLittlewoodEtaInverseDifference_le_one t m hm
      · exact norm_hardyLittlewoodEtaInverseDifference_le_one t n hn
    _ = ‖hardyLittlewoodEtaPhaseRatio t m -
          hardyLittlewoodEtaPhaseRatio t n‖ := by
      have hinner :
          (1 - hardyLittlewoodEtaPhaseRatio t n) -
              (1 - hardyLittlewoodEtaPhaseRatio t m) =
            hardyLittlewoodEtaPhaseRatio t m -
              hardyLittlewoodEtaPhaseRatio t n := by ring
      rw [one_mul, mul_one, hinner]
    _ ≤ |hardyLittlewoodEtaPhaseIncrement t m -
          hardyLittlewoodEtaPhaseIncrement t n| :=
      norm_hardyLittlewoodEtaPhaseRatio_sub_le t m n

theorem abs_hardyLittlewoodEtaPhaseIncrement_succ_sub
    (t : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    |hardyLittlewoodEtaPhaseIncrement t (n + 1) -
        hardyLittlewoodEtaPhaseIncrement t n| =
      |t| * (hardyLittlewoodEtaLogIncrement n -
        hardyLittlewoodEtaLogIncrement (n + 1)) := by
  have hmono :
      hardyLittlewoodEtaLogIncrement (n + 1) ≤
        hardyLittlewoodEtaLogIncrement n :=
    hardyLittlewoodEtaLogIncrement_antitone hn (by omega)
  rw [hardyLittlewoodEtaPhaseIncrement,
    hardyLittlewoodEtaPhaseIncrement, ← mul_sub, abs_mul,
    abs_of_nonpos (sub_nonpos.mpr hmono)]
  ring

/-- The inverse-difference coefficients have total variation at most one in the source range. -/
theorem sum_norm_hardyLittlewoodEtaInverseDifference_sub_le_one
    (t : ℝ) {N K : ℕ} (hN : 1 ≤ N) (ht : |t| ≤ N) :
    (∑ j ∈ range K,
      ‖hardyLittlewoodEtaInverseDifference t (N + j + 1) -
        hardyLittlewoodEtaInverseDifference t (N + j)‖) ≤ 1 := by
  have hterm :
      ∀ j ∈ range K,
        ‖hardyLittlewoodEtaInverseDifference t (N + j + 1) -
            hardyLittlewoodEtaInverseDifference t (N + j)‖ ≤
          |t| * (hardyLittlewoodEtaLogIncrement (N + j) -
            hardyLittlewoodEtaLogIncrement (N + j + 1)) := by
    intro j hj
    have hNj : N ≤ N + j := by omega
    have hNj1 : N ≤ N + j + 1 := by omega
    have hphase :=
      abs_hardyLittlewoodEtaPhaseIncrement_le_one t hN ht hNj
    have hphase1 :=
      abs_hardyLittlewoodEtaPhaseIncrement_le_one t hN ht hNj1
    calc
      ‖hardyLittlewoodEtaInverseDifference t (N + j + 1) -
          hardyLittlewoodEtaInverseDifference t (N + j)‖
          ≤ |hardyLittlewoodEtaPhaseIncrement t (N + j + 1) -
              hardyLittlewoodEtaPhaseIncrement t (N + j)| :=
        norm_hardyLittlewoodEtaInverseDifference_sub_le
          t (N + j + 1) (N + j) hphase1 hphase
      _ = |t| * (hardyLittlewoodEtaLogIncrement (N + j) -
            hardyLittlewoodEtaLogIncrement (N + j + 1)) :=
        abs_hardyLittlewoodEtaPhaseIncrement_succ_sub t (hN.trans hNj)
  have htel :
      (∑ j ∈ range K,
        (hardyLittlewoodEtaLogIncrement (N + j) -
          hardyLittlewoodEtaLogIncrement (N + j + 1))) =
        hardyLittlewoodEtaLogIncrement N -
          hardyLittlewoodEtaLogIncrement (N + K) := by
    simpa only [Nat.add_assoc, Nat.add_zero] using
      (Finset.sum_range_sub'
        (fun j => hardyLittlewoodEtaLogIncrement (N + j)) K)
  calc
    (∑ j ∈ range K,
        ‖hardyLittlewoodEtaInverseDifference t (N + j + 1) -
          hardyLittlewoodEtaInverseDifference t (N + j)‖)
        ≤ ∑ j ∈ range K,
            |t| * (hardyLittlewoodEtaLogIncrement (N + j) -
              hardyLittlewoodEtaLogIncrement (N + j + 1)) :=
      Finset.sum_le_sum hterm
    _ = |t| * (hardyLittlewoodEtaLogIncrement N -
          hardyLittlewoodEtaLogIncrement (N + K)) := by
      rw [← Finset.mul_sum, htel]
    _ ≤ |t| * hardyLittlewoodEtaLogIncrement N := by
      have hpos := hardyLittlewoodEtaLogIncrement_pos
        (hN.trans (Nat.le_add_right N K))
      nlinarith [abs_nonneg t]
    _ ≤ |t| * (N : ℝ)⁻¹ := by
      gcongr
      exact hardyLittlewoodEtaLogIncrement_le_inv hN
    _ ≤ (N : ℝ) * (N : ℝ)⁻¹ := by
      gcongr
    _ = 1 := mul_inv_cancel₀ (by positivity)

theorem sum_range_hardyLittlewoodEtaUnitPhase_sub_succ
    (t : ℝ) (N K : ℕ) :
    (∑ j ∈ range K,
      (hardyLittlewoodEtaUnitPhase t (N + j) -
        hardyLittlewoodEtaUnitPhase t (N + j + 1))) =
      hardyLittlewoodEtaUnitPhase t N -
        hardyLittlewoodEtaUnitPhase t (N + K) := by
  simpa only [Nat.add_assoc, Nat.add_zero] using
    (Finset.sum_range_sub'
      (fun j => hardyLittlewoodEtaUnitPhase t (N + j)) K)

/-- Every actual logarithmic unit-phase block is uniformly bounded in the source range. -/
theorem norm_hardyLittlewoodEtaUnitPhaseShiftedPrefix_le_four
    (t : ℝ) {N K : ℕ} (hN : 1 ≤ N) (ht : |t| ≤ N) :
    ‖hardyLittlewoodShiftedPrefix
        (hardyLittlewoodEtaUnitPhase t) N K‖ ≤ 4 := by
  by_cases hK : K = 0
  · subst K
    simp [hardyLittlewoodShiftedPrefix]
  let f : ℕ → ℂ :=
    fun j => hardyLittlewoodEtaInverseDifference t (N + 1 + j)
  let g : ℕ → ℂ :=
    fun j =>
      hardyLittlewoodEtaUnitPhase t (N + 1 + j) -
        hardyLittlewoodEtaUnitPhase t (N + 1 + j + 1)
  let G : ℕ → ℂ := fun k => ∑ j ∈ range k, g j
  have hG_eq :
      ∀ k : ℕ, G k =
        hardyLittlewoodEtaUnitPhase t (N + 1) -
          hardyLittlewoodEtaUnitPhase t (N + 1 + k) := by
    intro k
    dsimp only [G, g]
    exact sum_range_hardyLittlewoodEtaUnitPhase_sub_succ t (N + 1) k
  have hG :
      ∀ k : ℕ, ‖G k‖ ≤ 2 := by
    intro k
    rw [hG_eq]
    calc
      ‖hardyLittlewoodEtaUnitPhase t (N + 1) -
          hardyLittlewoodEtaUnitPhase t (N + 1 + k)‖
          ≤ ‖hardyLittlewoodEtaUnitPhase t (N + 1)‖ +
              ‖hardyLittlewoodEtaUnitPhase t (N + 1 + k)‖ :=
        norm_sub_le _ _
      _ = 2 := by
        rw [norm_hardyLittlewoodEtaUnitPhase t (by omega),
          norm_hardyLittlewoodEtaUnitPhase t (by omega)]
        norm_num
  have hrewrite :
      hardyLittlewoodShiftedPrefix
          (hardyLittlewoodEtaUnitPhase t) N K =
        ∑ j ∈ range K, f j • g j := by
    unfold hardyLittlewoodShiftedPrefix
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only [f, g]
    simp only [smul_eq_mul]
    simpa only [Nat.add_assoc] using
      (hardyLittlewoodEtaUnitPhase_eq_inverseDifference_mul_sub
        t hN ht (show N ≤ N + 1 + j by omega))
  have hparts :
      (∑ j ∈ range K, f j • g j) =
        f (K - 1) • G K -
          ∑ j ∈ range (K - 1), (f (j + 1) - f j) • G (j + 1) := by
    simpa only [G] using (Finset.sum_range_by_parts f g K)
  have hendpoint :
      ‖f (K - 1)‖ ≤ 1 := by
    dsimp only [f]
    apply norm_hardyLittlewoodEtaInverseDifference_le_one
    exact abs_hardyLittlewoodEtaPhaseIncrement_le_one
      t hN ht (by omega)
  have hvariation :
      (∑ j ∈ range (K - 1), ‖f (j + 1) - f j‖) ≤ 1 := by
    have ht' : |t| ≤ (N + 1 : ℕ) := by
      exact_mod_cast (ht.trans (by exact_mod_cast (Nat.le_succ N)))
    simpa only [f, Nat.add_assoc] using
      (sum_norm_hardyLittlewoodEtaInverseDifference_sub_le_one
        t (N := N + 1) (K := K - 1) (by omega) ht')
  rw [hrewrite, hparts]
  calc
    ‖f (K - 1) • G K -
        ∑ j ∈ range (K - 1), (f (j + 1) - f j) • G (j + 1)‖
        ≤ ‖f (K - 1) • G K‖ +
            ‖∑ j ∈ range (K - 1), (f (j + 1) - f j) • G (j + 1)‖ :=
      norm_sub_le _ _
    _ ≤ ‖f (K - 1)‖ * ‖G K‖ +
          ∑ j ∈ range (K - 1),
            ‖f (j + 1) - f j‖ * ‖G (j + 1)‖ := by
      rw [norm_smul]
      apply add_le_add (le_refl _)
      calc
        ‖∑ j ∈ range (K - 1), (f (j + 1) - f j) • G (j + 1)‖
            ≤ ∑ j ∈ range (K - 1),
                ‖(f (j + 1) - f j) • G (j + 1)‖ :=
          norm_sum_le _ _
        _ = ∑ j ∈ range (K - 1),
              ‖f (j + 1) - f j‖ * ‖G (j + 1)‖ := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [norm_smul]
    _ ≤ 1 * 2 +
          ∑ j ∈ range (K - 1),
            ‖f (j + 1) - f j‖ * 2 := by
      apply add_le_add
      · exact mul_le_mul hendpoint (hG K) (norm_nonneg _) (by norm_num)
      · apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (hG (j + 1)) (norm_nonneg _)
    _ ≤ 4 := by
      rw [← Finset.sum_mul]
      nlinarith

/-- A generic decreasing nonnegative weight preserves a uniform shifted-prefix bound. -/
theorem norm_hardyLittlewoodShiftedWeightedBlock_le_of_antitone
    (w : ℕ → ℝ) (a : ℕ → ℂ) (N K : ℕ) (B : ℝ)
    (hB : 0 ≤ B)
    (hw_nonneg : ∀ n : ℕ, N + 1 ≤ n → 0 ≤ w n)
    (hw_antitone :
      ∀ m n : ℕ, N + 1 ≤ m → m ≤ n → w n ≤ w m)
    (hprefix :
      ∀ k : ℕ, k ≤ K →
        ‖hardyLittlewoodShiftedPrefix a N k‖ ≤ B) :
    ‖hardyLittlewoodShiftedWeightedBlock w a N K‖ ≤
      w (N + 1) * B := by
  by_cases hK : K = 0
  · subst K
    simp only [hardyLittlewoodShiftedWeightedBlock, range_zero, sum_empty, norm_zero]
    exact mul_nonneg (hw_nonneg (N + 1) le_rfl) hB
  have hKpos : 0 < K := Nat.pos_of_ne_zero hK
  rw [hardyLittlewood_shiftedWeightedBlock_eq_abel_decreasing]
  have hendIndex : N + 1 + (K - 1) = N + K := by omega
  have htel :
      (∑ j ∈ range (K - 1),
        (w (N + 1 + j) - w (N + 1 + (j + 1)))) =
        w (N + 1) - w (N + K) := by
    have hraw :=
      Finset.sum_range_sub' (fun j => w (N + 1 + j)) (K - 1)
    simpa only [hendIndex] using hraw
  calc
    ‖w (N + 1 + (K - 1)) •
          hardyLittlewoodShiftedPrefix a N K +
        ∑ j ∈ range (K - 1),
          (w (N + 1 + j) - w (N + 1 + (j + 1))) •
            hardyLittlewoodShiftedPrefix a N (j + 1)‖
        ≤ ‖w (N + 1 + (K - 1)) •
              hardyLittlewoodShiftedPrefix a N K‖ +
            ∑ j ∈ range (K - 1),
              ‖(w (N + 1 + j) - w (N + 1 + (j + 1))) •
                  hardyLittlewoodShiftedPrefix a N (j + 1)‖ := by
          exact (norm_add_le _ _).trans
            (add_le_add_right (norm_sum_le _ _) _)
    _ ≤ w (N + K) * B +
          ∑ j ∈ range (K - 1),
            (w (N + 1 + j) - w (N + 1 + (j + 1))) * B := by
      apply add_le_add
      · have hwend :
            0 ≤ w (N + 1 + (K - 1)) :=
          hw_nonneg (N + 1 + (K - 1)) (by omega)
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hwend, hendIndex]
        exact mul_le_mul_of_nonneg_left (hprefix K le_rfl)
          (hw_nonneg (N + K) (by omega))
      · apply Finset.sum_le_sum
        intro j hj
        have hjlt : j < K - 1 := mem_range.mp hj
        have hdiff :
            0 ≤ w (N + 1 + j) - w (N + 1 + (j + 1)) := by
          apply sub_nonneg.mpr
          exact hw_antitone (N + 1 + j) (N + 1 + (j + 1))
            (by omega) (by omega)
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hdiff]
        exact mul_le_mul_of_nonneg_left
          (hprefix (j + 1) (by omega)) hdiff
    _ = w (N + 1) * B := by
      rw [← Finset.sum_mul, htel]
      ring

def hardyLittlewoodEtaPowerWeight (sigma : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (-sigma)

theorem hardyLittlewoodEtaPowerWeight_pos
    (sigma : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    0 < hardyLittlewoodEtaPowerWeight sigma n := by
  exact Real.rpow_pos_of_pos (by positivity) _

theorem hardyLittlewoodEtaPowerWeight_antitone
    {sigma : ℝ} (hsigma : 0 < sigma)
    {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    hardyLittlewoodEtaPowerWeight sigma n ≤
      hardyLittlewoodEtaPowerWeight sigma m := by
  unfold hardyLittlewoodEtaPowerWeight
  exact Real.rpow_le_rpow_of_nonpos
    (by positivity)
    (by exact_mod_cast hmn)
    (by linarith)

theorem hardyLittlewoodEtaShiftedPrefix_eq_powerWeightedBlock
    (sigma t : ℝ) (N K : ℕ) :
    hardyLittlewoodShiftedPrefix
        (hardyLittlewoodEtaSourceTerm (sigma + t * Complex.I)) N K =
      hardyLittlewoodShiftedWeightedBlock
        (hardyLittlewoodEtaPowerWeight sigma)
        (hardyLittlewoodEtaUnitPhase t) N K := by
  unfold hardyLittlewoodShiftedPrefix
  unfold hardyLittlewoodShiftedWeightedBlock
  apply Finset.sum_congr rfl
  intro j hj
  exact hardyLittlewoodEtaSourceTerm_eq_rpow_smul_unitPhase
    sigma t (show 1 ≤ N + 1 + j by omega)

/-- The actual eta block has the source-uniform `N^(-sigma)` order with no `abs(s)` loss. -/
theorem norm_hardyLittlewoodEtaShiftedPrefix_le_four_mul_rpow
    (sigma t : ℝ) {N K : ℕ}
    (hsigma : 0 < sigma) (hN : 1 ≤ N) (ht : |t| ≤ N) :
    ‖hardyLittlewoodShiftedPrefix
        (hardyLittlewoodEtaSourceTerm (sigma + t * Complex.I)) N K‖ ≤
      4 * (N : ℝ) ^ (-sigma) := by
  rw [hardyLittlewoodEtaShiftedPrefix_eq_powerWeightedBlock]
  calc
    ‖hardyLittlewoodShiftedWeightedBlock
        (hardyLittlewoodEtaPowerWeight sigma)
        (hardyLittlewoodEtaUnitPhase t) N K‖
        ≤ hardyLittlewoodEtaPowerWeight sigma (N + 1) * 4 := by
      apply norm_hardyLittlewoodShiftedWeightedBlock_le_of_antitone
        (hB := by norm_num)
      · intro n hn
        exact (hardyLittlewoodEtaPowerWeight_pos sigma
          (le_trans (by omega) hn)).le
      · intro m n hm hmn
        exact hardyLittlewoodEtaPowerWeight_antitone hsigma
          (le_trans (by omega) hm) hmn
      · intro k hk
        exact norm_hardyLittlewoodEtaUnitPhaseShiftedPrefix_le_four
          t hN ht
    _ ≤ (N : ℝ) ^ (-sigma) * 4 := by
      gcongr
      exact hardyLittlewoodEtaPowerWeight_antitone hsigma hN (by omega)
    _ = 4 * (N : ℝ) ^ (-sigma) := by ring

/-- The difference of two ordered eta partial sums has the same source-uniform bound. -/
theorem norm_hardyLittlewoodEtaPartialSum_sub_le_four_mul_rpow
    (sigma t : ℝ) {N M : ℕ}
    (hsigma : 0 < sigma) (hN : 1 ≤ N) (ht : |t| ≤ N)
    (hNM : N ≤ M) :
    ‖hardyLittlewoodEtaPartialSum (sigma + t * Complex.I) M -
        hardyLittlewoodEtaPartialSum (sigma + t * Complex.I) N‖ ≤
      4 * (N : ℝ) ^ (-sigma) := by
  have hM : N + (M - N) = M := by omega
  rw [← hM, hardyLittlewoodEtaPartialSum_add_sub]
  exact norm_hardyLittlewoodEtaShiftedPrefix_le_four_mul_rpow
    sigma t hsigma hN ht

/-- The naturally ordered eta partial sums are Cauchy throughout the positive half-plane. -/
theorem cauchySeq_hardyLittlewoodEtaPartialSum
    (sigma t : ℝ) (hsigma : 0 < sigma) :
    CauchySeq
      (hardyLittlewoodEtaPartialSum (sigma + t * Complex.I)) := by
  let b : ℕ → ℝ := fun n => 4 * (n : ℝ) ^ (-sigma)
  have hb : Tendsto b atTop (𝓝 0) := by
    have hpow :
        Tendsto (fun n : ℕ => (n : ℝ) ^ (-sigma))
          atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hsigma).comp
        tendsto_natCast_atTop_atTop
    simpa only [b, mul_zero] using hpow.const_mul 4
  rw [Metric.cauchySeq_iff]
  intro epsilon hepsilon
  have hevent : ∀ᶠ n in atTop, b n < epsilon :=
    hb.eventually (gt_mem_nhds hepsilon)
  obtain ⟨R, hR⟩ := eventually_atTop.1 hevent
  refine ⟨max 1 (max ⌈|t|⌉₊ R), ?_⟩
  intro m hm n hn
  have hmOne : 1 ≤ m := (le_max_left 1 (max ⌈|t|⌉₊ R)).trans hm
  have hnOne : 1 ≤ n := (le_max_left 1 (max ⌈|t|⌉₊ R)).trans hn
  have hmCeil : ⌈|t|⌉₊ ≤ m :=
    (le_max_of_le_right (le_max_left ⌈|t|⌉₊ R)).trans hm
  have hnCeil : ⌈|t|⌉₊ ≤ n :=
    (le_max_of_le_right (le_max_left ⌈|t|⌉₊ R)).trans hn
  have hmT : |t| ≤ (m : ℝ) :=
    (Nat.le_ceil |t|).trans (by exact_mod_cast hmCeil)
  have hnT : |t| ≤ (n : ℝ) :=
    (Nat.le_ceil |t|).trans (by exact_mod_cast hnCeil)
  have hmR : R ≤ m :=
    (le_max_of_le_right (le_max_right ⌈|t|⌉₊ R)).trans hm
  have hnR : R ≤ n :=
    (le_max_of_le_right (le_max_right ⌈|t|⌉₊ R)).trans hn
  rcases le_total m n with hmn | hnm
  · rw [dist_comm, dist_eq_norm]
    exact lt_of_le_of_lt
      (norm_hardyLittlewoodEtaPartialSum_sub_le_four_mul_rpow
        sigma t hsigma hmOne hmT hmn)
      (hR m hmR)
  · rw [dist_eq_norm]
    exact lt_of_le_of_lt
      (norm_hardyLittlewoodEtaPartialSum_sub_le_four_mul_rpow
        sigma t hsigma hnOne hnT hnm)
      (hR n hnR)

/-- The canonical ordered value of the eta source series. -/
def hardyLittlewoodEtaSeriesValue (s : ℂ) : ℂ :=
  Filter.limUnder atTop (hardyLittlewoodEtaPartialSum s)

theorem tendsto_hardyLittlewoodEtaPartialSum
    (sigma t : ℝ) (hsigma : 0 < sigma) :
    Tendsto
      (hardyLittlewoodEtaPartialSum (sigma + t * Complex.I))
      atTop
      (𝓝 (hardyLittlewoodEtaSeriesValue
        (sigma + t * Complex.I))) := by
  exact (cauchySeq_hardyLittlewoodEtaPartialSum sigma t hsigma).tendsto_limUnder

theorem tendsto_hardyLittlewoodEtaPartialSum_of_re_pos
    (s : ℂ) (hs : 0 < s.re) :
    Tendsto (hardyLittlewoodEtaPartialSum s) atTop
      (𝓝 (hardyLittlewoodEtaSeriesValue s)) := by
  have hs_eq : (s.re : ℂ) + s.im * Complex.I = s := by
    apply Complex.ext <;> simp
  simpa only [hs_eq] using
    tendsto_hardyLittlewoodEtaPartialSum s.re s.im hs

/-- Hardy--Littlewood's ordered eta remainder, with a constant uniform in the source range. -/
theorem norm_hardyLittlewoodEtaSeriesValue_sub_partialSum_le
    (s : ℂ) (hs : 0 < s.re) {N : ℕ}
    (hN : 1 ≤ N) (ht : |s.im| ≤ N) :
    ‖hardyLittlewoodEtaSeriesValue s -
        hardyLittlewoodEtaPartialSum s N‖ ≤
      4 * (N : ℝ) ^ (-s.re) := by
  have hnorm :
      Tendsto
        (fun M => ‖hardyLittlewoodEtaPartialSum s M -
          hardyLittlewoodEtaPartialSum s N‖)
        atTop
        (𝓝 ‖hardyLittlewoodEtaSeriesValue s -
          hardyLittlewoodEtaPartialSum s N‖) :=
    ((tendsto_hardyLittlewoodEtaPartialSum_of_re_pos s hs).sub_const _).norm
  apply le_of_tendsto hnorm
  filter_upwards [eventually_atTop.2 ⟨N, fun _ hM => hM⟩] with M hM
  have hs_eq : (s.re : ℂ) + s.im * Complex.I = s := by
    apply Complex.ext <;> simp
  simpa only [hs_eq] using
    (norm_hardyLittlewoodEtaPartialSum_sub_le_four_mul_rpow
      s.re s.im hs hN ht hM)

/-- The ordered eta partial sums converge locally uniformly on the positive half-plane. -/
theorem tendstoLocallyUniformlyOn_hardyLittlewoodEtaPartialSum :
    TendstoLocallyUniformlyOn
      (fun N s => hardyLittlewoodEtaPartialSum s N)
      hardyLittlewoodEtaSeriesValue atTop
      {s : ℂ | 0 < s.re} := by
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro epsilon hepsilon x hx
  change 0 < x.re at hx
  let sigma0 : ℝ := x.re / 2
  let r : ℝ := x.re / 2
  have hsigma0 : 0 < sigma0 := by
    dsimp only [sigma0]
    linarith
  have hr : 0 < r := by
    dsimp only [r]
    linarith
  let b : ℕ → ℝ := fun n => 4 * (n : ℝ) ^ (-sigma0)
  have hb : Tendsto b atTop (𝓝 0) := by
    have hpow :
        Tendsto (fun n : ℕ => (n : ℝ) ^ (-sigma0))
          atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hsigma0).comp
        tendsto_natCast_atTop_atTop
    simpa only [b, mul_zero] using hpow.const_mul 4
  have hevent : ∀ᶠ n in atTop, b n < epsilon :=
    hb.eventually (gt_mem_nhds hepsilon)
  obtain ⟨R, hR⟩ := eventually_atTop.1 hevent
  refine ⟨Metric.ball x r,
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x hr), ?_⟩
  refine eventually_atTop.2
    ⟨max 1 (max ⌈|x.im| + r⌉₊ R), ?_⟩
  intro n hn y hy
  have hnOne : 1 ≤ n :=
    (le_max_left 1 (max ⌈|x.im| + r⌉₊ R)).trans hn
  have hnCeil : ⌈|x.im| + r⌉₊ ≤ n :=
    (le_max_of_le_right
      (le_max_left ⌈|x.im| + r⌉₊ R)).trans hn
  have hnR : R ≤ n :=
    (le_max_of_le_right
      (le_max_right ⌈|x.im| + r⌉₊ R)).trans hn
  have hdist : ‖y - x‖ < r := by
    have hdist' := Metric.mem_ball.mp hy
    simpa only [dist_eq_norm] using hdist'
  have hreDiff : |y.re - x.re| < r := by
    exact (Complex.abs_re_le_norm (y - x)).trans_lt hdist
  have himDiff : |y.im - x.im| < r := by
    exact (Complex.abs_im_le_norm (y - x)).trans_lt hdist
  have hyRe : sigma0 < y.re := by
    have hleft := (abs_lt.mp hreDiff).1
    dsimp only [sigma0, r] at hleft ⊢
    linarith
  have hyIm : |y.im| < |x.im| + r := by
    calc
      |y.im| = |(y.im - x.im) + x.im| := by ring_nf
      _ ≤ |y.im - x.im| + |x.im| := abs_add_le _ _
      _ < r + |x.im| := by linarith
      _ = |x.im| + r := by ring
  have hheight : |y.im| ≤ (n : ℝ) := by
    exact hyIm.le.trans
      ((Nat.le_ceil (|x.im| + r)).trans
        (by exact_mod_cast hnCeil))
  have hpow :
      (n : ℝ) ^ (-y.re) ≤ (n : ℝ) ^ (-sigma0) := by
    exact Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hnOne) (by linarith)
  rw [dist_eq_norm]
  exact
    (norm_hardyLittlewoodEtaSeriesValue_sub_partialSum_le
      y (hsigma0.trans hyRe) hnOne hheight).trans_lt
      ((mul_le_mul_of_nonneg_left hpow (by norm_num)).trans_lt
        (by simpa only [b] using hR n hnR))

theorem differentiable_hardyLittlewoodEtaPartialSum (N : ℕ) :
    Differentiable ℂ (fun s => hardyLittlewoodEtaPartialSum s N) := by
  unfold hardyLittlewoodEtaPartialSum
  apply Differentiable.fun_sum
  intro n hn
  by_cases hn0 : n = 0
  · simp [hn0, hardyLittlewoodEtaSourceTerm]
  · simp only [hardyLittlewoodEtaSourceTerm, hn0, if_false]
    have hn0C : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
    exact (differentiable_const
        (c := (((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ))).mul
      (differentiable_id.neg.const_cpow (Or.inl hn0C))

/-- The canonical ordered eta series is holomorphic on the positive half-plane. -/
theorem differentiableOn_hardyLittlewoodEtaSeriesValue :
    DifferentiableOn ℂ hardyLittlewoodEtaSeriesValue
      {s : ℂ | 0 < s.re} := by
  exact
    tendstoLocallyUniformlyOn_hardyLittlewoodEtaPartialSum.differentiableOn
      (Eventually.of_forall fun N =>
        (differentiable_hardyLittlewoodEtaPartialSum N).differentiableOn)
      (isOpen_lt continuous_const Complex.continuous_re)

theorem hardyLittlewoodEtaSourceTerm_succ
    (s : ℂ) (n : ℕ) :
    hardyLittlewoodEtaSourceTerm s (n + 1) =
      (-1 : ℂ) ^ n * ((n + 1 : ℕ) : ℂ) ^ (-s) := by
  rw [hardyLittlewoodEtaSourceTerm_eq s (by omega)]
  simp only [Nat.add_sub_cancel]
  norm_cast

/-- In the absolutely convergent half-plane, the canonical ordered series is the classical
Dirichlet eta function. -/
theorem hardyLittlewoodEtaSeriesValue_eq_hardyLittlewoodEta_of_one_lt_re
    (s : ℂ) (hs : 1 < s.re) :
    hardyLittlewoodEtaSeriesValue s = hardyLittlewoodEta s := by
  let g : ℕ → ℂ := fun n => ((n + 1 : ℕ) : ℂ) ^ (-s)
  let a : ℕ → ℂ := fun n => (-1 : ℂ) ^ n * g n
  have hbase :
      Summable (fun n : ℕ => 1 / (n : ℂ) ^ s) :=
    Complex.summable_one_div_nat_cpow.mpr hs
  have hshift :
      Summable (fun n : ℕ => 1 / (n + 1 : ℂ) ^ s) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr hbase
  have hG : Summable g := by
    simpa only [g, Complex.cpow_neg, one_div, Nat.cast_add,
      Nat.cast_one] using hshift
  have hA : Summable a := by
    exact hG.alternating
  have hEvenG : Summable (fun k => g (2 * k)) :=
    hG.comp_injective (mul_right_injective₀ (by norm_num : (2 : ℕ) ≠ 0))
  have hOddG : Summable (fun k => g (2 * k + 1)) :=
    hG.comp_injective (fun _ _ h => by omega)
  have hEvenA : Summable (fun k => a (2 * k)) :=
    hA.comp_injective (mul_right_injective₀ (by norm_num : (2 : ℕ) ≠ 0))
  have hOddA : Summable (fun k => a (2 * k + 1)) :=
    hA.comp_injective (fun _ _ h => by omega)
  have hsplitG :
      (∑' k : ℕ, g (2 * k)) +
          (∑' k : ℕ, g (2 * k + 1)) =
        ∑' k : ℕ, g k :=
    tsum_even_add_odd hEvenG hOddG
  have hEvenAeq :
      (fun k => a (2 * k)) = fun k => g (2 * k) := by
    funext k
    simp only [a, pow_mul, neg_one_sq, one_pow, one_mul]
  have hOddAeq :
      (fun k => a (2 * k + 1)) =
        fun k => -g (2 * k + 1) := by
    funext k
    simp only [a, pow_add, pow_mul, neg_one_sq, one_pow, pow_one,
      one_mul, neg_mul]
  have hsplitA :
      (∑' k : ℕ, a (2 * k)) +
          (∑' k : ℕ, a (2 * k + 1)) =
        ∑' k : ℕ, a k :=
    tsum_even_add_odd hEvenA hOddA
  have hoddPoint :
      ∀ k : ℕ, g (2 * k + 1) =
        (2 : ℂ) ^ (-s) * g k := by
    intro k
    dsimp only [g]
    have hindex : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
    rw [hindex]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      (Complex.natCast_mul_natCast_cpow 2 (k + 1) (-s))
  have hoddTsum :
      (∑' k : ℕ, g (2 * k + 1)) =
        (2 : ℂ) ^ (-s) * ∑' k : ℕ, g k := by
    calc
      (∑' k : ℕ, g (2 * k + 1)) =
          ∑' k : ℕ, (2 : ℂ) ^ (-s) * g k :=
        tsum_congr hoddPoint
      _ = (2 : ℂ) ^ (-s) * ∑' k : ℕ, g k :=
        tsum_mul_left
  have hGValue :
      (∑' k : ℕ, g k) = riemannZeta s := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    symm
    apply tsum_congr
    intro n
    simp only [g, Complex.cpow_neg, one_div, Nat.cast_add, Nat.cast_one]
  have hAValue :
      (∑' k : ℕ, a k) = hardyLittlewoodEta s := by
    calc
      (∑' k : ℕ, a k) =
          (∑' k : ℕ, a (2 * k)) +
            ∑' k : ℕ, a (2 * k + 1) :=
        hsplitA.symm
      _ = (∑' k : ℕ, g (2 * k)) -
            ∑' k : ℕ, g (2 * k + 1) := by
        rw [hEvenAeq, hOddAeq, tsum_neg]
        ring
      _ = (∑' k : ℕ, g k) -
            2 * ∑' k : ℕ, g (2 * k + 1) := by
        rw [← hsplitG]
        ring
      _ = riemannZeta s -
            2 * ((2 : ℂ) ^ (-s) * riemannZeta s) := by
        rw [hoddTsum, hGValue]
      _ = hardyLittlewoodEta s := by
        rw [hardyLittlewoodEta,
          show (1 : ℂ) - s = 1 + (-s) by ring,
          Complex.cpow_add _ _ (by norm_num), Complex.cpow_one]
        ring
  have hSourceShift :
      Summable (fun n => hardyLittlewoodEtaSourceTerm s (n + 1)) := by
    simpa only [hardyLittlewoodEtaSourceTerm_succ, a] using hA
  have hSource : Summable (hardyLittlewoodEtaSourceTerm s) :=
    (summable_nat_add_iff 1).mp hSourceShift
  have hSourceTsum :
      (∑' n : ℕ, hardyLittlewoodEtaSourceTerm s n) =
        hardyLittlewoodEta s := by
    calc
      (∑' n : ℕ, hardyLittlewoodEtaSourceTerm s n) =
          ∑' n : ℕ, hardyLittlewoodEtaSourceTerm s (n + 1) := by
        have hsum := hSource.sum_add_tsum_nat_add 1
        have hzero : hardyLittlewoodEtaSourceTerm s 0 = 0 := by
          simp [hardyLittlewoodEtaSourceTerm]
        rw [sum_range_one, hzero, zero_add] at hsum
        exact hsum.symm
      _ = ∑' n : ℕ, a n := by
        apply tsum_congr
        intro n
        exact hardyLittlewoodEtaSourceTerm_succ s n
      _ = hardyLittlewoodEta s := hAValue
  have hTsum :
      Tendsto
        (fun N => ∑ n ∈ range N, hardyLittlewoodEtaSourceTerm s n)
        atTop
        (𝓝 (∑' n : ℕ, hardyLittlewoodEtaSourceTerm s n)) :=
    hSource.tendsto_sum_tsum_nat
  have hPartialTsum :
      Tendsto (hardyLittlewoodEtaPartialSum s) atTop
        (𝓝 (∑' n : ℕ, hardyLittlewoodEtaSourceTerm s n)) := by
    unfold hardyLittlewoodEtaPartialSum
    simpa only [Function.comp_def] using
      hTsum.comp (tendsto_add_atTop_nat 1)
  have hValue :
      hardyLittlewoodEtaSeriesValue s =
        ∑' n : ℕ, hardyLittlewoodEtaSourceTerm s n :=
    tendsto_nhds_unique
      (tendsto_hardyLittlewoodEtaPartialSum_of_re_pos s (by linarith))
      hPartialTsum
  exact hValue.trans hSourceTsum

/-- The project eta normalization is holomorphic on the positive half-plane away from the zeta
pole. -/
theorem differentiableOn_hardyLittlewoodEta_positive :
    DifferentiableOn ℂ hardyLittlewoodEta zetaAbelPositiveDomain := by
  intro s hs
  have hpow :
      DifferentiableAt ℂ (fun z : ℂ => (2 : ℂ) ^ (1 - z)) s :=
    ((differentiableAt_const (c := (1 : ℂ))).sub differentiableAt_id).const_cpow
      (Or.inl (by norm_num))
  have hfactor :
      DifferentiableAt ℂ (fun z : ℂ => 1 - (2 : ℂ) ^ (1 - z)) s :=
    (differentiableAt_const (c := (1 : ℂ))).sub hpow
  change DifferentiableWithinAt ℂ
    (fun z : ℂ => (1 - (2 : ℂ) ^ (1 - z)) * riemannZeta z)
    zetaAbelPositiveDomain s
  exact
    (hfactor.mul (differentiableAt_riemannZeta hs.1)).differentiableWithinAt

/-- The ordered eta series agrees with the project eta normalization on the full positive
half-plane, with the zeta pole removed. -/
theorem hardyLittlewoodEtaSeriesValue_eq_hardyLittlewoodEta
    (s : ℂ) (hs_ne : s ≠ 1) (hs_re : 0 < s.re) :
    hardyLittlewoodEtaSeriesValue s = hardyLittlewoodEta s := by
  have hSeries :
      AnalyticOnNhd ℂ hardyLittlewoodEtaSeriesValue
        zetaAbelPositiveDomain := by
    apply DifferentiableOn.analyticOnNhd
    · exact differentiableOn_hardyLittlewoodEtaSeriesValue.mono
        (fun _ hz => hz.2)
    · exact isOpen_zetaAbelPositiveDomain
  have hEta :
      AnalyticOnNhd ℂ hardyLittlewoodEta
        zetaAbelPositiveDomain :=
    differentiableOn_hardyLittlewoodEta_positive.analyticOnNhd
      isOpen_zetaAbelPositiveDomain
  have hEq :
      hardyLittlewoodEtaSeriesValue =ᶠ[𝓝 (2 : ℂ)]
        hardyLittlewoodEta := by
    have hopen : IsOpen {w : ℂ | 1 < w.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    filter_upwards
      [hopen.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with w hw
    exact hardyLittlewoodEtaSeriesValue_eq_hardyLittlewoodEta_of_one_lt_re w hw
  exact
    (AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      hSeries hEta isPreconnected_zetaAbelPositiveDomain
      two_mem_zetaAbelPositiveDomain hEq) ⟨hs_ne, hs_re⟩

/-- Hardy--Littlewood's Lemma 3 remainder for the project's eta normalization. -/
theorem norm_hardyLittlewoodEta_sub_partialSum_le
    (s : ℂ) (hs_ne : s ≠ 1) (hs_re : 0 < s.re) {N : ℕ}
    (hN : 1 ≤ N) (ht : |s.im| ≤ N) :
    ‖hardyLittlewoodEta s - hardyLittlewoodEtaPartialSum s N‖ ≤
      4 * (N : ℝ) ^ (-s.re) := by
  rw [← hardyLittlewoodEtaSeriesValue_eq_hardyLittlewoodEta s hs_ne hs_re]
  exact norm_hardyLittlewoodEtaSeriesValue_sub_partialSum_le
    s hs_re hN ht

/-- Critical-line specialization of the source eta remainder. -/
theorem norm_hardyLittlewoodEtaCritical_sub_partialSum_le
    (t : ℝ) {N : ℕ} (hN : 1 ≤ N) (ht : |t| ≤ N) :
    ‖hardyLittlewoodEtaCritical t -
        hardyLittlewoodEtaPartialSum (hardyCriticalLinePoint t) N‖ ≤
      4 * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hne : hardyCriticalLinePoint t ≠ (1 : ℂ) := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
  have ht' : |(hardyCriticalLinePoint t).im| ≤ (N : ℝ) := by
    simpa only [hardyCriticalLinePoint_im] using ht
  simpa only [hardyLittlewoodEtaCritical, hardyCriticalLinePoint_re,
    hardyCriticalLinePoint_im] using
    (norm_hardyLittlewoodEta_sub_partialSum_le
      (hardyCriticalLinePoint t) hne (by norm_num) hN ht')

/-- The proved eta remainder discharges the source premise of the existing Lemma 4 Abel
transfer. -/
theorem exists_hardyLittlewoodThetaValue_of_re_pos
    (s : ℂ) (hs_ne : s ≠ 1) (hs_re : 0 < s.re) :
    ∃ thetaValue : ℂ,
      Tendsto (hardyLittlewoodThetaPartialSum s) atTop (𝓝 thetaValue) ∧
      ∀ N : ℕ, max 2 ⌈|s.im|⌉₊ ≤ N →
        ‖thetaValue - hardyLittlewoodThetaPartialSum s N‖ ≤
          8 * (Real.log 2)⁻¹ * (N : ℝ) ^ (-s.re) := by
  let N0 : ℕ := max 2 ⌈|s.im|⌉₊
  have hN0 : 2 ≤ N0 := le_max_left _ _
  have hremainder :
      ∀ n : ℕ, N0 ≤ n →
        ‖hardyLittlewoodEta s -
            hardyLittlewoodEtaPartialSum s n‖ ≤
          4 * (n : ℝ) ^ (-s.re) := by
    intro n hn
    have hnOne : 1 ≤ n := by
      exact (by omega : 1 ≤ N0).trans hn
    have hceil : ⌈|s.im|⌉₊ ≤ n :=
      (le_max_right 2 ⌈|s.im|⌉₊).trans hn
    have ht : |s.im| ≤ (n : ℝ) :=
      (Nat.le_ceil |s.im|).trans (by exact_mod_cast hceil)
    exact norm_hardyLittlewoodEta_sub_partialSum_le
      s hs_ne hs_re hnOne ht
  obtain ⟨thetaValue, htheta, hbound⟩ :=
    exists_hardyLittlewoodThetaValue_of_etaRemainder
      s (hardyLittlewoodEta s) s.re 4 N0
      hs_re (by norm_num) hN0 hremainder
  refine ⟨thetaValue, htheta, ?_⟩
  intro N hN
  change N0 ≤ N at hN
  calc
    ‖thetaValue - hardyLittlewoodThetaPartialSum s N‖
        ≤ 2 * (Real.log 2)⁻¹ * 4 * (N : ℝ) ^ (-s.re) :=
      hbound N hN
    _ = 8 * (Real.log 2)⁻¹ * (N : ℝ) ^ (-s.re) := by ring

/-- Aggregate certificate for the formalized Hardy--Littlewood Lemma 3 chain. -/
structure HardyLittlewoodEtaRemainderCertificate : Prop where
  inverseVariation :
    ∀ (t : ℝ) (N K : ℕ), 1 ≤ N → |t| ≤ N →
      (∑ j ∈ range K,
        ‖hardyLittlewoodEtaInverseDifference t (N + j + 1) -
          hardyLittlewoodEtaInverseDifference t (N + j)‖) ≤ 1
  phaseBlock :
    ∀ (t : ℝ) (N K : ℕ), 1 ≤ N → |t| ≤ N →
      ‖hardyLittlewoodShiftedPrefix
        (hardyLittlewoodEtaUnitPhase t) N K‖ ≤ 4
  etaBlock :
    ∀ (sigma t : ℝ) (N K : ℕ), 0 < sigma → 1 ≤ N → |t| ≤ N →
      ‖hardyLittlewoodShiftedPrefix
        (hardyLittlewoodEtaSourceTerm
          (sigma + t * Complex.I)) N K‖ ≤
        4 * (N : ℝ) ^ (-sigma)
  locallyUniform :
    TendstoLocallyUniformlyOn
      (fun N s => hardyLittlewoodEtaPartialSum s N)
      hardyLittlewoodEtaSeriesValue atTop
      {s : ℂ | 0 < s.re}
  identification :
    ∀ s : ℂ, s ≠ 1 → 0 < s.re →
      hardyLittlewoodEtaSeriesValue s = hardyLittlewoodEta s
  etaRemainder :
    ∀ (s : ℂ) (N : ℕ), s ≠ 1 → 0 < s.re → 1 ≤ N → |s.im| ≤ N →
      ‖hardyLittlewoodEta s - hardyLittlewoodEtaPartialSum s N‖ ≤
        4 * (N : ℝ) ^ (-s.re)
  criticalLine :
    ∀ (t : ℝ) (N : ℕ), 1 ≤ N → |t| ≤ N →
      ‖hardyLittlewoodEtaCritical t -
          hardyLittlewoodEtaPartialSum
            (hardyCriticalLinePoint t) N‖ ≤
        4 * (N : ℝ) ^ (-(1 / 2 : ℝ))
  thetaTransfer :
    ∀ (s : ℂ), s ≠ 1 → 0 < s.re →
      ∃ thetaValue : ℂ,
        Tendsto (hardyLittlewoodThetaPartialSum s) atTop (𝓝 thetaValue) ∧
        ∀ N : ℕ, max 2 ⌈|s.im|⌉₊ ≤ N →
          ‖thetaValue - hardyLittlewoodThetaPartialSum s N‖ ≤
            8 * (Real.log 2)⁻¹ * (N : ℝ) ^ (-s.re)

theorem hardyLittlewoodEtaRemainder_endpoint :
    HardyLittlewoodEtaRemainderCertificate where
  inverseVariation := by
    intro t N K hN ht
    exact sum_norm_hardyLittlewoodEtaInverseDifference_sub_le_one
      t hN ht
  phaseBlock := by
    intro t N K hN ht
    exact norm_hardyLittlewoodEtaUnitPhaseShiftedPrefix_le_four
      t hN ht
  etaBlock := by
    intro sigma t N K hsigma hN ht
    exact norm_hardyLittlewoodEtaShiftedPrefix_le_four_mul_rpow
      sigma t hsigma hN ht
  locallyUniform :=
    tendstoLocallyUniformlyOn_hardyLittlewoodEtaPartialSum
  identification :=
    hardyLittlewoodEtaSeriesValue_eq_hardyLittlewoodEta
  etaRemainder := by
    intro s N hs_ne hs_re hN ht
    exact norm_hardyLittlewoodEta_sub_partialSum_le
      s hs_ne hs_re hN ht
  criticalLine := by
    intro t N hN ht
    exact norm_hardyLittlewoodEtaCritical_sub_partialSum_le
      t hN ht
  thetaTransfer :=
    exists_hardyLittlewoodThetaValue_of_re_pos

end

end LeanLab.Riemann
