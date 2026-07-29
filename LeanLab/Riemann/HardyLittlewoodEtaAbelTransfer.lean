import LeanLab.Riemann.ChebyshevMellin
import LeanLab.Riemann.HardyLittlewoodFiniteMeanSquare
import Mathlib.Analysis.SpecificLimits.Normed

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Hardy--Littlewood eta-to-Theta Abel transfer

This module formalizes the discrete Abel step from Lemma 3 to Lemma 4 in
Hardy--Littlewood (1921). The uniform eta remainder is an explicit premise. No eta remainder,
primitive identification, or infinite-series mean square is asserted here.
-/

open Complex Finset Filter Real Set Topology

namespace LeanLab.Riemann

noncomputable section

/-- The literal one-indexed alternating source term `(-1)^(n-1) n^(-s)`, with a harmless zero
at index zero. The exponent `n+1` has the same parity as `n-1` on the source range. -/
def hardyLittlewoodEtaSourceTerm (s : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else
    (((-1 : ℝ) ^ (n + 1) : ℝ) : ℂ) * (n : ℂ) ^ (-s)

theorem hardyLittlewoodEtaSourceTerm_eq
    (s : ℂ) {n : ℕ} (hn : 1 ≤ n) :
    hardyLittlewoodEtaSourceTerm s n =
      (((-1 : ℝ) ^ (n - 1) : ℝ) : ℂ) * (n : ℂ) ^ (-s) := by
  rw [hardyLittlewoodEtaSourceTerm, if_neg (by omega)]
  have hexponent : n + 1 = (n - 1) + 2 := by omega
  rw [hexponent, pow_add]
  norm_num

/-- The naturally ordered eta partial sum through index `N`. -/
def hardyLittlewoodEtaPartialSum (s : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ range (N + 1), hardyLittlewoodEtaSourceTerm s n

/-- The reciprocal-log weight used in Hardy--Littlewood's `Theta` series. -/
def hardyLittlewoodThetaLogWeight (n : ℕ) : ℝ :=
  if 2 ≤ n then (Real.log (n : ℝ))⁻¹ else 0

/-- The naturally ordered logarithmically weighted source partial sum through index `N`. -/
def hardyLittlewoodThetaPartialSum (s : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ range (N + 1),
    hardyLittlewoodThetaLogWeight n • hardyLittlewoodEtaSourceTerm s n

/-- The first `K` terms strictly after index `N`. -/
def hardyLittlewoodShiftedPrefix
    (a : ℕ → ℂ) (N K : ℕ) : ℂ :=
  ∑ j ∈ range K, a (N + 1 + j)

/-- A weighted block consisting of the first `K` terms strictly after index `N`. -/
def hardyLittlewoodShiftedWeightedBlock
    (w : ℕ → ℝ) (a : ℕ → ℂ) (N K : ℕ) : ℂ :=
  ∑ j ∈ range K, w (N + 1 + j) • a (N + 1 + j)

/-- Exact finite Abel summation for a shifted block, with the endpoint convention inherited
from `Finset.sum_range_by_parts`. -/
theorem hardyLittlewood_shiftedWeightedBlock_eq_abel
    (w : ℕ → ℝ) (a : ℕ → ℂ) (N K : ℕ) :
    hardyLittlewoodShiftedWeightedBlock w a N K =
      w (N + 1 + (K - 1)) • hardyLittlewoodShiftedPrefix a N K -
        ∑ j ∈ range (K - 1),
          (w (N + 1 + (j + 1)) - w (N + 1 + j)) •
            hardyLittlewoodShiftedPrefix a N (j + 1) := by
  simpa only [hardyLittlewoodShiftedWeightedBlock,
    hardyLittlewoodShiftedPrefix] using
      (Finset.sum_range_by_parts
        (fun j => w (N + 1 + j))
        (fun j => a (N + 1 + j)) K)

/-- The same identity with positive decreasing-weight differences. -/
theorem hardyLittlewood_shiftedWeightedBlock_eq_abel_decreasing
    (w : ℕ → ℝ) (a : ℕ → ℂ) (N K : ℕ) :
    hardyLittlewoodShiftedWeightedBlock w a N K =
      w (N + 1 + (K - 1)) • hardyLittlewoodShiftedPrefix a N K +
        ∑ j ∈ range (K - 1),
          (w (N + 1 + j) - w (N + 1 + (j + 1))) •
            hardyLittlewoodShiftedPrefix a N (j + 1) := by
  rw [hardyLittlewood_shiftedWeightedBlock_eq_abel]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [← neg_smul, neg_sub]

/-- An eta partial-sum increment is exactly the corresponding shifted source block. -/
theorem hardyLittlewoodEtaPartialSum_add_sub
    (s : ℂ) (N K : ℕ) :
    hardyLittlewoodEtaPartialSum s (N + K) -
        hardyLittlewoodEtaPartialSum s N =
      hardyLittlewoodShiftedPrefix (hardyLittlewoodEtaSourceTerm s) N K := by
  have hle : N + 1 ≤ N + K + 1 := by omega
  have hsplit :=
    Finset.sum_Ico_eq_sub (hardyLittlewoodEtaSourceTerm s) hle
  rw [Finset.sum_Ico_eq_sum_range] at hsplit
  have hsub : N + K + 1 - (N + 1) = K := by omega
  rw [hsub] at hsplit
  simpa only [hardyLittlewoodEtaPartialSum,
    hardyLittlewoodShiftedPrefix] using hsplit.symm

/-- A Theta partial-sum increment is the reciprocal-log weighted shifted eta block. -/
theorem hardyLittlewoodThetaPartialSum_add_sub
    (s : ℂ) (N K : ℕ) :
    hardyLittlewoodThetaPartialSum s (N + K) -
        hardyLittlewoodThetaPartialSum s N =
      hardyLittlewoodShiftedWeightedBlock hardyLittlewoodThetaLogWeight
        (hardyLittlewoodEtaSourceTerm s) N K := by
  have hle : N + 1 ≤ N + K + 1 := by omega
  have hsplit :=
    Finset.sum_Ico_eq_sub
      (fun n => hardyLittlewoodThetaLogWeight n •
        hardyLittlewoodEtaSourceTerm s n) hle
  rw [Finset.sum_Ico_eq_sum_range] at hsplit
  have hsub : N + K + 1 - (N + 1) = K := by omega
  rw [hsub] at hsplit
  simpa only [hardyLittlewoodThetaPartialSum,
    hardyLittlewoodShiftedWeightedBlock] using hsplit.symm

theorem hardyLittlewoodThetaLogWeight_eq
    {n : ℕ} (hn : 2 ≤ n) :
    hardyLittlewoodThetaLogWeight n =
      (Real.log (n : ℝ))⁻¹ := by
  simp [hardyLittlewoodThetaLogWeight, hn]

theorem hardyLittlewoodThetaLogWeight_pos
    {n : ℕ} (hn : 2 ≤ n) :
    0 < hardyLittlewoodThetaLogWeight n := by
  rw [hardyLittlewoodThetaLogWeight_eq hn]
  exact inv_pos.mpr (Real.log_pos (by exact_mod_cast hn))

/-- Reciprocal logarithm is decreasing on the source index range. -/
theorem hardyLittlewoodThetaLogWeight_antitoneOn
    {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) :
    hardyLittlewoodThetaLogWeight n ≤
      hardyLittlewoodThetaLogWeight m := by
  have hn : 2 ≤ n := hm.trans hmn
  rw [hardyLittlewoodThetaLogWeight_eq hm,
    hardyLittlewoodThetaLogWeight_eq hn]
  simpa only [one_div] using
    (one_div_le_one_div_of_le
      (Real.log_pos (by exact_mod_cast hm))
      (Real.strictMonoOn_log.monotoneOn
        (show (0 : ℝ) < m by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hm))
        (show (0 : ℝ) < n by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hn))
        (by exact_mod_cast hmn)))

theorem hardyLittlewoodThetaLogWeight_diff_nonneg
    {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ hardyLittlewoodThetaLogWeight n -
      hardyLittlewoodThetaLogWeight (n + 1) := by
  exact sub_nonneg.mpr
    (hardyLittlewoodThetaLogWeight_antitoneOn hn (by omega))

theorem tendsto_hardyLittlewoodThetaLogWeight :
    Tendsto hardyLittlewoodThetaLogWeight atTop (𝓝 0) := by
  have hraw :
      Tendsto (fun n : ℕ => (Real.log (n : ℝ))⁻¹)
        atTop (𝓝 0) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  apply Tendsto.congr' _ hraw
  filter_upwards [eventually_atTop.2 ⟨2, fun _ hn => hn⟩] with n hn
  exact (hardyLittlewoodThetaLogWeight_eq hn).symm

/-- A bounded family of unweighted shifted partial blocks gives the sharp decreasing-weight
bound for every finite reciprocal-log weighted block. -/
theorem norm_hardyLittlewoodShiftedThetaBlock_le
    (a : ℕ → ℂ) (N K : ℕ) (B : ℝ)
    (hN : 2 ≤ N) (hB : 0 ≤ B)
    (hprefix :
      ∀ k : ℕ, k ≤ K →
        ‖hardyLittlewoodShiftedPrefix a N k‖ ≤ B) :
    ‖hardyLittlewoodShiftedWeightedBlock
        hardyLittlewoodThetaLogWeight a N K‖ ≤
      hardyLittlewoodThetaLogWeight (N + 1) * B := by
  by_cases hK : K = 0
  · subst K
    simp only [hardyLittlewoodShiftedWeightedBlock, range_zero, sum_empty, norm_zero]
    exact mul_nonneg
      (hardyLittlewoodThetaLogWeight_pos (by omega)).le hB
  have hKpos : 0 < K := Nat.pos_of_ne_zero hK
  rw [hardyLittlewood_shiftedWeightedBlock_eq_abel_decreasing]
  have hendIndex : N + 1 + (K - 1) = N + K := by omega
  have htel :
      (∑ j ∈ range (K - 1),
        (hardyLittlewoodThetaLogWeight (N + 1 + j) -
          hardyLittlewoodThetaLogWeight (N + 1 + (j + 1)))) =
        hardyLittlewoodThetaLogWeight (N + 1) -
          hardyLittlewoodThetaLogWeight (N + K) := by
    have hraw :=
      Finset.sum_range_sub'
        (fun j => hardyLittlewoodThetaLogWeight (N + 1 + j)) (K - 1)
    simpa only [hendIndex] using hraw
  calc
    ‖hardyLittlewoodThetaLogWeight (N + 1 + (K - 1)) •
          hardyLittlewoodShiftedPrefix a N K +
        ∑ j ∈ range (K - 1),
          (hardyLittlewoodThetaLogWeight (N + 1 + j) -
              hardyLittlewoodThetaLogWeight (N + 1 + (j + 1))) •
            hardyLittlewoodShiftedPrefix a N (j + 1)‖
        ≤ ‖hardyLittlewoodThetaLogWeight (N + 1 + (K - 1)) •
              hardyLittlewoodShiftedPrefix a N K‖ +
            ∑ j ∈ range (K - 1),
              ‖(hardyLittlewoodThetaLogWeight (N + 1 + j) -
                    hardyLittlewoodThetaLogWeight (N + 1 + (j + 1))) •
                  hardyLittlewoodShiftedPrefix a N (j + 1)‖ := by
          exact (norm_add_le _ _).trans
            (add_le_add_right (norm_sum_le _ _) _)
    _ ≤ hardyLittlewoodThetaLogWeight (N + K) * B +
          ∑ j ∈ range (K - 1),
            (hardyLittlewoodThetaLogWeight (N + 1 + j) -
                hardyLittlewoodThetaLogWeight (N + 1 + (j + 1))) * B := by
      apply add_le_add
      · rw [norm_smul, Real.norm_eq_abs, abs_of_pos
          (hardyLittlewoodThetaLogWeight_pos (by omega))]
        rw [hendIndex]
        exact mul_le_mul_of_nonneg_left (hprefix K le_rfl)
          (hardyLittlewoodThetaLogWeight_pos (by omega)).le
      · apply Finset.sum_le_sum
        intro j hj
        have hjlt : j < K - 1 := mem_range.mp hj
        have hdiff :
            0 ≤ hardyLittlewoodThetaLogWeight (N + 1 + j) -
              hardyLittlewoodThetaLogWeight (N + 1 + (j + 1)) := by
          apply sub_nonneg.mpr
          apply hardyLittlewoodThetaLogWeight_antitoneOn (by omega)
          omega
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hdiff]
        exact mul_le_mul_of_nonneg_left
          (hprefix (j + 1) (by omega)) hdiff
    _ = hardyLittlewoodThetaLogWeight (N + 1) * B := by
      rw [← Finset.sum_mul, htel]
      ring

theorem hardyLittlewoodThetaLogWeight_le_inv_log_two
    {n : ℕ} (hn : 2 ≤ n) :
    hardyLittlewoodThetaLogWeight n ≤ (Real.log 2)⁻¹ := by
  calc
    hardyLittlewoodThetaLogWeight n ≤
        hardyLittlewoodThetaLogWeight 2 :=
      hardyLittlewoodThetaLogWeight_antitoneOn (by norm_num) hn
    _ = (Real.log 2)⁻¹ :=
      hardyLittlewoodThetaLogWeight_eq (by norm_num)

/-- Two eta remainders control every unweighted block between their endpoints. -/
theorem norm_hardyLittlewoodEtaShiftedPrefix_le
    (s etaValue : ℂ) (sigma Ceta : ℝ) (N0 N K : ℕ)
    (hsigma : 0 < sigma) (hCeta : 0 ≤ Ceta)
    (hN0 : 2 ≤ N0) (hN : N0 ≤ N)
    (hremainder :
      ∀ n : ℕ, N0 ≤ n →
        ‖etaValue - hardyLittlewoodEtaPartialSum s n‖ ≤
          Ceta * (n : ℝ) ^ (-sigma)) :
    ‖hardyLittlewoodShiftedPrefix
        (hardyLittlewoodEtaSourceTerm s) N K‖ ≤
      2 * Ceta * (N : ℝ) ^ (-sigma) := by
  have hNtwo : 2 ≤ N := hN0.trans hN
  have hNK : N0 ≤ N + K := hN.trans (Nat.le_add_right N K)
  have hpow :
      ((N + K : ℕ) : ℝ) ^ (-sigma) ≤
        (N : ℝ) ^ (-sigma) := by
    exact Real.rpow_le_rpow_of_nonpos
      (by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hNtwo))
      (by exact_mod_cast (Nat.le_add_right N K))
      (by linarith)
  rw [← hardyLittlewoodEtaPartialSum_add_sub]
  have hrewrite :
      hardyLittlewoodEtaPartialSum s (N + K) -
          hardyLittlewoodEtaPartialSum s N =
        (etaValue - hardyLittlewoodEtaPartialSum s N) -
          (etaValue - hardyLittlewoodEtaPartialSum s (N + K)) := by
    ring
  rw [hrewrite]
  calc
    ‖(etaValue - hardyLittlewoodEtaPartialSum s N) -
          (etaValue - hardyLittlewoodEtaPartialSum s (N + K))‖
        ≤ ‖etaValue - hardyLittlewoodEtaPartialSum s N‖ +
            ‖etaValue - hardyLittlewoodEtaPartialSum s (N + K)‖ :=
      norm_sub_le _ _
    _ ≤ Ceta * (N : ℝ) ^ (-sigma) +
          Ceta * ((N + K : ℕ) : ℝ) ^ (-sigma) :=
      add_le_add (hremainder N hN) (hremainder (N + K) hNK)
    _ ≤ Ceta * (N : ℝ) ^ (-sigma) +
          Ceta * (N : ℝ) ^ (-sigma) := by
      gcongr
    _ = 2 * Ceta * (N : ℝ) ^ (-sigma) := by ring

/-- Hardy--Littlewood Lemma 3's eta remainder controls every finite reciprocal-log block with
the same power of the starting index. -/
theorem norm_hardyLittlewoodEtaShiftedThetaBlock_le
    (s etaValue : ℂ) (sigma Ceta : ℝ) (N0 N K : ℕ)
    (hsigma : 0 < sigma) (hCeta : 0 ≤ Ceta)
    (hN0 : 2 ≤ N0) (hN : N0 ≤ N)
    (hremainder :
      ∀ n : ℕ, N0 ≤ n →
        ‖etaValue - hardyLittlewoodEtaPartialSum s n‖ ≤
          Ceta * (n : ℝ) ^ (-sigma)) :
    ‖hardyLittlewoodShiftedWeightedBlock
        hardyLittlewoodThetaLogWeight
        (hardyLittlewoodEtaSourceTerm s) N K‖ ≤
      2 * (Real.log 2)⁻¹ * Ceta * (N : ℝ) ^ (-sigma) := by
  have hNtwo : 2 ≤ N := hN0.trans hN
  have hB : 0 ≤ 2 * Ceta * (N : ℝ) ^ (-sigma) := by positivity
  calc
    ‖hardyLittlewoodShiftedWeightedBlock
        hardyLittlewoodThetaLogWeight
        (hardyLittlewoodEtaSourceTerm s) N K‖
        ≤ hardyLittlewoodThetaLogWeight (N + 1) *
            (2 * Ceta * (N : ℝ) ^ (-sigma)) := by
      apply norm_hardyLittlewoodShiftedThetaBlock_le
        (hN := hNtwo) (hB := hB)
      intro k hk
      exact norm_hardyLittlewoodEtaShiftedPrefix_le
        s etaValue sigma Ceta N0 N k hsigma hCeta hN0 hN hremainder
    _ ≤ (Real.log 2)⁻¹ *
          (2 * Ceta * (N : ℝ) ^ (-sigma)) := by
      gcongr
      exact hardyLittlewoodThetaLogWeight_le_inv_log_two (by omega)
    _ = 2 * (Real.log 2)⁻¹ * Ceta * (N : ℝ) ^ (-sigma) := by ring

/-- The difference between two ordered Theta partial sums inherits the eta remainder at the
earlier endpoint. -/
theorem norm_hardyLittlewoodThetaPartialSum_sub_le
    (s etaValue : ℂ) (sigma Ceta : ℝ) (N0 N M : ℕ)
    (hsigma : 0 < sigma) (hCeta : 0 ≤ Ceta)
    (hN0 : 2 ≤ N0) (hN : N0 ≤ N) (hNM : N ≤ M)
    (hremainder :
      ∀ n : ℕ, N0 ≤ n →
        ‖etaValue - hardyLittlewoodEtaPartialSum s n‖ ≤
          Ceta * (n : ℝ) ^ (-sigma)) :
    ‖hardyLittlewoodThetaPartialSum s M -
        hardyLittlewoodThetaPartialSum s N‖ ≤
      2 * (Real.log 2)⁻¹ * Ceta * (N : ℝ) ^ (-sigma) := by
  have hM : N + (M - N) = M := by omega
  rw [← hM, hardyLittlewoodThetaPartialSum_add_sub]
  exact norm_hardyLittlewoodEtaShiftedThetaBlock_le
    s etaValue sigma Ceta N0 N (M - N)
      hsigma hCeta hN0 hN hremainder

/-- A uniform positive-power eta remainder makes the ordered Theta partial sums Cauchy. -/
theorem cauchySeq_hardyLittlewoodThetaPartialSum
    (s etaValue : ℂ) (sigma Ceta : ℝ) (N0 : ℕ)
    (hsigma : 0 < sigma) (hCeta : 0 ≤ Ceta)
    (hN0 : 2 ≤ N0)
    (hremainder :
      ∀ n : ℕ, N0 ≤ n →
        ‖etaValue - hardyLittlewoodEtaPartialSum s n‖ ≤
          Ceta * (n : ℝ) ^ (-sigma)) :
    CauchySeq (hardyLittlewoodThetaPartialSum s) := by
  let b : ℕ → ℝ := fun n =>
    2 * (Real.log 2)⁻¹ * Ceta * (n : ℝ) ^ (-sigma)
  have hb : Tendsto b atTop (𝓝 0) := by
    have hpow :
        Tendsto (fun n : ℕ => (n : ℝ) ^ (-sigma))
          atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hsigma).comp
        tendsto_natCast_atTop_atTop
    simpa only [b, mul_zero] using
      hpow.const_mul (2 * (Real.log 2)⁻¹ * Ceta)
  rw [Metric.cauchySeq_iff]
  intro epsilon hepsilon
  have hevent : ∀ᶠ n in atTop, b n < epsilon :=
    hb.eventually (gt_mem_nhds hepsilon)
  obtain ⟨R, hR⟩ := eventually_atTop.1 hevent
  refine ⟨max N0 R, ?_⟩
  intro m hm n hn
  have hmN0 : N0 ≤ m := (le_max_left N0 R).trans hm
  have hnN0 : N0 ≤ n := (le_max_left N0 R).trans hn
  have hmR : R ≤ m := (le_max_right N0 R).trans hm
  have hnR : R ≤ n := (le_max_right N0 R).trans hn
  rcases le_total m n with hmn | hnm
  · rw [dist_comm, dist_eq_norm]
    exact lt_of_le_of_lt
      (norm_hardyLittlewoodThetaPartialSum_sub_le
        s etaValue sigma Ceta N0 m n hsigma hCeta hN0 hmN0 hmn hremainder)
      (hR m hmR)
  · rw [dist_eq_norm]
    exact lt_of_le_of_lt
      (norm_hardyLittlewoodThetaPartialSum_sub_le
        s etaValue sigma Ceta N0 n m hsigma hCeta hN0 hnN0 hnm hremainder)
      (hR n hnR)

/-- The source Lemma 3 remainder implies ordered convergence of the logarithmically weighted
Theta series and preserves the power `N^(-sigma)`. -/
theorem exists_hardyLittlewoodThetaValue_of_etaRemainder
    (s etaValue : ℂ) (sigma Ceta : ℝ) (N0 : ℕ)
    (hsigma : 0 < sigma) (hCeta : 0 ≤ Ceta)
    (hN0 : 2 ≤ N0)
    (hremainder :
      ∀ n : ℕ, N0 ≤ n →
        ‖etaValue - hardyLittlewoodEtaPartialSum s n‖ ≤
          Ceta * (n : ℝ) ^ (-sigma)) :
    ∃ thetaValue : ℂ,
      Tendsto (hardyLittlewoodThetaPartialSum s) atTop (𝓝 thetaValue) ∧
      ∀ N : ℕ, N0 ≤ N →
        ‖thetaValue - hardyLittlewoodThetaPartialSum s N‖ ≤
          2 * (Real.log 2)⁻¹ * Ceta * (N : ℝ) ^ (-sigma) := by
  obtain ⟨thetaValue, htheta⟩ :=
    cauchySeq_tendsto_of_complete
      (cauchySeq_hardyLittlewoodThetaPartialSum
        s etaValue sigma Ceta N0 hsigma hCeta hN0 hremainder)
  refine ⟨thetaValue, htheta, ?_⟩
  intro N hN
  have hnorm :
      Tendsto
        (fun M => ‖hardyLittlewoodThetaPartialSum s M -
          hardyLittlewoodThetaPartialSum s N‖)
        atTop
        (𝓝 ‖thetaValue - hardyLittlewoodThetaPartialSum s N‖) :=
    (htheta.sub_const _).norm
  apply le_of_tendsto hnorm
  filter_upwards [eventually_atTop.2 ⟨N, fun _ hM => hM⟩] with M hM
  exact norm_hardyLittlewoodThetaPartialSum_sub_le
    s etaValue sigma Ceta N0 N M hsigma hCeta hN0 hN hM hremainder

/-- One eta remainder constant uniform in any parameter family gives one Theta remainder
constant uniform in the same family. The limit value may depend on the parameter. -/
theorem hardyLittlewoodTheta_uniform_of_eta_uniform
    {ι : Type*} (sourcePoint etaValue : ι → ℂ)
    (sigma Ceta : ℝ) (N0 : ℕ)
    (hsigma : 0 < sigma) (hCeta : 0 ≤ Ceta)
    (hN0 : 2 ≤ N0)
    (hremainder :
      ∀ q : ι, ∀ n : ℕ, N0 ≤ n →
        ‖etaValue q - hardyLittlewoodEtaPartialSum (sourcePoint q) n‖ ≤
          Ceta * (n : ℝ) ^ (-sigma)) :
    ∀ q : ι, ∃ thetaValue : ℂ,
      Tendsto (hardyLittlewoodThetaPartialSum (sourcePoint q))
        atTop (𝓝 thetaValue) ∧
      ∀ N : ℕ, N0 ≤ N →
        ‖thetaValue -
            hardyLittlewoodThetaPartialSum (sourcePoint q) N‖ ≤
          2 * (Real.log 2)⁻¹ * Ceta * (N : ℝ) ^ (-sigma) := by
  intro q
  exact exists_hardyLittlewoodThetaValue_of_etaRemainder
    (sourcePoint q) (etaValue q) sigma Ceta N0
      hsigma hCeta hN0 (hremainder q)

def hardyLittlewoodEtaAbelTransferConstant : ℝ :=
  2 * (Real.log 2)⁻¹

theorem hardyLittlewoodEtaAbelTransferConstant_pos :
    0 < hardyLittlewoodEtaAbelTransferConstant := by
  unfold hardyLittlewoodEtaAbelTransferConstant
  exact mul_pos (by norm_num) (inv_pos.mpr (Real.log_pos one_lt_two))

/-- Aggregate certificate for the exact Hardy--Littlewood Lemma 3 to Lemma 4 transfer. -/
structure HardyLittlewoodEtaAbelTransferCertificate : Prop where
  sourceTerm :
    ∀ (s : ℂ) (n : ℕ), 1 ≤ n →
      hardyLittlewoodEtaSourceTerm s n =
        (((-1 : ℝ) ^ (n - 1) : ℝ) : ℂ) * (n : ℂ) ^ (-s)
  finiteAbel :
    ∀ (w : ℕ → ℝ) (a : ℕ → ℂ) (N K : ℕ),
      hardyLittlewoodShiftedWeightedBlock w a N K =
        w (N + 1 + (K - 1)) • hardyLittlewoodShiftedPrefix a N K +
          ∑ j ∈ range (K - 1),
            (w (N + 1 + j) - w (N + 1 + (j + 1))) •
              hardyLittlewoodShiftedPrefix a N (j + 1)
  transfer :
    ∀ (s etaValue : ℂ) (sigma Ceta : ℝ) (N0 : ℕ),
      0 < sigma → 0 ≤ Ceta → 2 ≤ N0 →
      (∀ n : ℕ, N0 ≤ n →
        ‖etaValue - hardyLittlewoodEtaPartialSum s n‖ ≤
          Ceta * (n : ℝ) ^ (-sigma)) →
      ∃ thetaValue : ℂ,
        Tendsto (hardyLittlewoodThetaPartialSum s) atTop (𝓝 thetaValue) ∧
        ∀ N : ℕ, N0 ≤ N →
          ‖thetaValue - hardyLittlewoodThetaPartialSum s N‖ ≤
            hardyLittlewoodEtaAbelTransferConstant *
              Ceta * (N : ℝ) ^ (-sigma)

theorem hardyLittlewoodEtaAbelTransfer_endpoint :
    HardyLittlewoodEtaAbelTransferCertificate where
  sourceTerm := hardyLittlewoodEtaSourceTerm_eq
  finiteAbel := hardyLittlewood_shiftedWeightedBlock_eq_abel_decreasing
  transfer := by
    intro s etaValue sigma Ceta N0 hsigma hCeta hN0 hremainder
    simpa only [hardyLittlewoodEtaAbelTransferConstant] using
      exists_hardyLittlewoodThetaValue_of_etaRemainder
        s etaValue sigma Ceta N0 hsigma hCeta hN0 hremainder

end

end LeanLab.Riemann
