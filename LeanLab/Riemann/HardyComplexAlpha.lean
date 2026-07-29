import LeanLab.Riemann.HardyThetaInversion
import LeanLab.Riemann.ZetaConvexityMidpoint
import LeanLab.Riemann.LevinsonMontgomeryLogDerivMassBridge
import LeanLab.Riemann.BaezDuarteZetaRatio
import LeanLab.Riemann.BettinGonekInverseMellinConvolution
import LeanLab.Riemann.WeilCompactLaplaceArithmeticFormula
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.LocallyUniformLimit

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Hardy's complex-alpha equation

This file reconstructs the analytic continuation from Hardy's positive-real
Cahen--Mellin equation to equation (2) of his 1914 proof.
-/

open Complex Filter MeasureTheory Real Set Topology
open scoped Topology

namespace LeanLab.Riemann

noncomputable section

/-- The exact exponential weight needed for Hardy's alpha strip. -/
def hardyXiExponentialWeight (a t : ℝ) : ℝ :=
  Real.exp (a * |t|) * ‖hardyXi (2 * t)‖ /
    (1 / 4 + 4 * t ^ 2)

/-- The exact half-line Gamma formula retains the full `pi / 2` decay rate. -/
theorem norm_Gamma_half_add_mul_I_le_exp_pi (t : ℝ) :
    ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ≤
      3 * Real.exp (-(Real.pi / 2) * |t|) := by
  have hsq :
      ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ^ 2 =
        Real.pi / Real.cosh (Real.pi * t) := by
    simpa [Real.cosh_neg] using
      norm_Gamma_half_sub_mul_I_sq (-t)
  have hcoshPos : 0 < Real.cosh (Real.pi * t) :=
    Real.cosh_pos _
  have hexpPos : 0 < Real.exp (Real.pi * |t|) :=
    Real.exp_pos _
  have hcosh :
      Real.exp (Real.pi * |t|) ≤
        2 * Real.cosh (Real.pi * t) := by
    rw [Real.cosh_eq]
    ring_nf
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht]
      exact le_add_of_nonneg_right (Real.exp_nonneg _)
    · rw [abs_of_nonpos ht]
      ring_nf
      exact le_add_of_nonneg_left (Real.exp_nonneg _)
  have hsqExp :
      ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ^ 2 ≤
        8 * Real.exp (-(Real.pi * |t|)) := by
    rw [hsq]
    calc
      Real.pi / Real.cosh (Real.pi * t) ≤
          (2 * Real.pi) / Real.exp (Real.pi * |t|) := by
        apply (div_le_div_iff₀ hcoshPos hexpPos).2
        nlinarith [Real.pi_pos]
      _ = 2 * Real.pi * Real.exp (-(Real.pi * |t|)) := by
        rw [div_eq_mul_inv, ← Real.exp_neg]
      _ ≤ 8 * Real.exp (-(Real.pi * |t|)) := by
        gcongr
        linarith [Real.pi_le_four]
  have hnormNonneg :
      0 ≤ ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ :=
    norm_nonneg _
  have hmajorNonneg :
      0 ≤ 3 * Real.exp (-(Real.pi / 2) * |t|) := by
    positivity
  apply (sq_le_sq₀ hnormNonneg hmajorNonneg).mp
  calc
    ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ ^ 2
        ≤ 8 * Real.exp (-(Real.pi * |t|)) := hsqExp
    _ ≤ (3 * Real.exp (-(Real.pi / 2) * |t|)) ^ 2 := by
      have hexpSq :
          Real.exp (-(Real.pi / 2) * |t|) ^ 2 =
            Real.exp (-(Real.pi * |t|)) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      rw [mul_pow, hexpSq]
      nlinarith [Real.exp_pos (-(Real.pi * |t|))]

/-- A polynomial loss transports the exact half-line Gamma decay to `Re z = 1/4`. -/
theorem exists_norm_Gamma_quarter_add_mul_I_le_rpow_mul_exp :
    ∃ p : ℝ, 0 < p ∧ ∀ t : ℝ,
      ‖Complex.Gamma (((1 / 4 : ℝ) : ℂ) + t * Complex.I)‖ ≤
        12 * (|t| + 2) ^ p *
          Real.exp (-(Real.pi / 2) * |t|) := by
  obtain ⟨C, hC, hratio⟩ :=
    exists_norm_Gamma_div_le_rpow_of_re_mem_Icc
      (1 / 2 : ℝ) (5 / 4 : ℝ) (by norm_num)
  let p : ℝ := C * (3 / 4)
  have hp : 0 < p := by
    dsimp only [p]
    positivity
  refine ⟨p, hp, fun t => ?_⟩
  let z0 : ℂ := ((1 / 2 : ℝ) : ℂ) + t * Complex.I
  let zq : ℂ := ((1 / 4 : ℝ) : ℂ) + t * Complex.I
  let δ : ℝ := 3 / 4
  have hratioBound :
      ‖Complex.Gamma (z0 + δ) / Complex.Gamma z0‖ ≤
        (|z0.im| + 2) ^ p := by
    have hsource := hratio z0 δ (by simp [z0]) (by norm_num [z0, δ])
      (by norm_num)
    simpa only [p] using hsource
  have hz0Gamma : Complex.Gamma z0 ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    simp [z0]
  have hzq : zq ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [zq] at hre
  have hzqNorm : (1 / 4 : ℝ) ≤ ‖zq‖ := by
    calc
      (1 / 4 : ℝ) = |zq.re| := by simp [zq]
      _ ≤ ‖zq‖ := Complex.abs_re_le_norm zq
  have hshift :
      zq + 1 = z0 + δ := by
    dsimp [zq, z0, δ]
    push_cast
    ring
  have hquarter :
      ‖Complex.Gamma zq‖ ≤ 4 * ‖Complex.Gamma (z0 + δ)‖ := by
    have hrec :
        ‖Complex.Gamma (z0 + δ)‖ =
          ‖zq‖ * ‖Complex.Gamma zq‖ := by
      rw [← hshift, Complex.Gamma_add_one zq hzq, norm_mul]
    have hmul :
        (1 / 4 : ℝ) * ‖Complex.Gamma zq‖ ≤
          ‖Complex.Gamma (z0 + δ)‖ := by
      rw [hrec]
      exact mul_le_mul_of_nonneg_right hzqNorm (norm_nonneg _)
    linarith
  have hshiftBound :
      ‖Complex.Gamma (z0 + δ)‖ ≤
        (|t| + 2) ^ p *
          ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ := by
    calc
      ‖Complex.Gamma (z0 + δ)‖ =
          ‖(Complex.Gamma (z0 + δ) / Complex.Gamma z0) *
            Complex.Gamma z0‖ := by
        rw [div_mul_cancel₀ _ hz0Gamma]
      _ = ‖Complex.Gamma (z0 + δ) / Complex.Gamma z0‖ *
          ‖Complex.Gamma z0‖ := norm_mul _ _
      _ ≤ (|z0.im| + 2) ^ p * ‖Complex.Gamma z0‖ :=
        mul_le_mul_of_nonneg_right hratioBound (norm_nonneg _)
      _ = (|t| + 2) ^ p *
          ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖ := by
        simp [z0]
  calc
    ‖Complex.Gamma (((1 / 4 : ℝ) : ℂ) + t * Complex.I)‖
        = ‖Complex.Gamma zq‖ := rfl
    _ ≤ 4 * ‖Complex.Gamma (z0 + δ)‖ := hquarter
    _ ≤ 4 * ((|t| + 2) ^ p *
        ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + t * Complex.I)‖) := by
      gcongr
    _ ≤ 4 * ((|t| + 2) ^ p *
        (3 * Real.exp (-(Real.pi / 2) * |t|))) := by
      gcongr
      exact norm_Gamma_half_add_mul_I_le_exp_pi t
    _ = 12 * (|t| + 2) ^ p *
        Real.exp (-(Real.pi / 2) * |t|) := by ring

/-- The completed critical-line xi function has polynomial times exact `pi / 2`
exponential decay. -/
theorem exists_norm_hardyXi_two_mul_le_pow_mul_exp :
    ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, ∀ t : ℝ, 1 < |t| →
      ‖hardyXi (2 * t)‖ ≤
        K * |t| ^ N * Real.exp (-(Real.pi / 2) * |t|) := by
  obtain ⟨p, hp, hgammaQuarter⟩ :=
    exists_norm_Gamma_quarter_add_mul_I_le_rpow_mul_exp
  obtain ⟨Czeta, hCzeta, hzeta⟩ :=
    exists_norm_riemannZeta_criticalLine_le_rpow
  let M : ℕ := ⌈p⌉₊
  let K : ℝ := 180 * Czeta * 3 ^ M
  refine ⟨K, by positivity, M + 3, fun t ht => ?_⟩
  let x : ℝ := |t|
  let s : ℂ := ((1 / 2 : ℝ) : ℂ) + (2 * t) * Complex.I
  have hx : 1 < x := ht
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hM : p ≤ (M : ℝ) := by
    exact Nat.le_ceil p
  have hbaseOne : 1 ≤ x + 2 := by linarith
  have hbaseThree : x + 2 ≤ 3 * x := by linarith
  have hgammaPow :
      (x + 2) ^ p ≤ 3 ^ M * x ^ M := by
    calc
      (x + 2) ^ p ≤ (x + 2) ^ (M : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hbaseOne hM
      _ = (x + 2) ^ M := Real.rpow_natCast _ _
      _ ≤ (3 * x) ^ M :=
        pow_le_pow_left₀ (by positivity) hbaseThree M
      _ = 3 ^ M * x ^ M := by rw [mul_pow]
  have hgamma :
      ‖Complex.Gamma (((1 / 4 : ℝ) : ℂ) + t * Complex.I)‖ ≤
        (12 * 3 ^ M) * x ^ M *
          Real.exp (-(Real.pi / 2) * x) := by
    calc
      ‖Complex.Gamma (((1 / 4 : ℝ) : ℂ) + t * Complex.I)‖
          ≤ 12 * (x + 2) ^ p *
              Real.exp (-(Real.pi / 2) * x) := by
        simpa only [x] using hgammaQuarter t
      _ ≤ 12 * (3 ^ M * x ^ M) *
          Real.exp (-(Real.pi / 2) * x) := by
        gcongr
      _ = (12 * 3 ^ M) * x ^ M *
          Real.exp (-(Real.pi / 2) * x) := by ring
  have hpiFactor :
      ‖((Real.pi : ℂ) ^ (-s / 2))‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    have hre : (-s / 2).re = -(1 / 4 : ℝ) := by
      norm_num [s, div_eq_mul_inv]
    rw [hre]
    exact Real.rpow_le_one_of_one_le_of_nonpos
      (le_trans (by norm_num : (1 : ℝ) ≤ 2) Real.two_le_pi) (by norm_num)
  have hsHalf :
      s / 2 = ((1 / 4 : ℝ) : ℂ) + t * Complex.I := by
    dsimp only [s]
    push_cast
    ring
  have hgammaR :
      ‖Complex.Gammaℝ s‖ ≤
        (12 * 3 ^ M) * x ^ M *
          Real.exp (-(Real.pi / 2) * x) := by
    rw [Complex.Gammaℝ_def, norm_mul, hsHalf]
    calc
      ‖((Real.pi : ℂ) ^ (-s / 2))‖ *
            ‖Complex.Gamma (((1 / 4 : ℝ) : ℂ) + t * Complex.I)‖
          ≤ 1 * ‖Complex.Gamma
              (((1 / 4 : ℝ) : ℂ) + t * Complex.I)‖ := by
        gcongr
      _ ≤ (12 * 3 ^ M) * x ^ M *
          Real.exp (-(Real.pi / 2) * x) := by simpa using hgamma
  have htwoAbs : |2 * t| = 2 * x := by
    simp [x, abs_mul]
  have htwoLarge : 1 ≤ |2 * t| := by
    rw [htwoAbs]
    linarith
  have hzetaRaw := hzeta (2 * t) htwoLarge
  have hzetaBaseOne : 1 ≤ 1 + |2 * t| :=
    le_add_of_nonneg_right (abs_nonneg _)
  have hzetaExponent :
      (1 + |2 * t|) ^ (3 / 8 : ℝ) ≤ 1 + |2 * t| := by
    calc
      (1 + |2 * t|) ^ (3 / 8 : ℝ)
          ≤ (1 + |2 * t|) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hzetaBaseOne (by norm_num)
      _ = 1 + |2 * t| := Real.rpow_one _
  have hzetaLinear : 1 + |2 * t| ≤ 3 * x := by
    rw [htwoAbs]
    linarith
  have hzetaBound :
      ‖riemannZeta s‖ ≤ 3 * Czeta * x := by
    calc
      ‖riemannZeta s‖ =
          ‖riemannZeta (((1 / 2 : ℝ) : ℂ) +
            (2 * t) * Complex.I)‖ := rfl
      _ ≤ Czeta * (1 + |2 * t|) ^ (3 / 8 : ℝ) := by
        have harg :
            (((1 / 2 : ℝ) : ℂ) + (2 * t) * Complex.I) =
              (1 / 2 : ℂ) + ((2 * t : ℝ) : ℂ) * Complex.I := by
          push_cast
          ring
        rw [harg]
        exact hzetaRaw
      _ ≤ Czeta * (1 + |2 * t|) := by
        gcongr
      _ ≤ Czeta * (3 * x) :=
        mul_le_mul_of_nonneg_left hzetaLinear hCzeta.le
      _ = 3 * Czeta * x := by ring
  have hsNorm : ‖s‖ ≤ 3 * x := by
    calc
      ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ = 1 / 2 + 2 * x := by
        simp [s, x, abs_mul]
      _ ≤ 3 * x := by linarith
  have hsOneNorm : ‖s - 1‖ ≤ 3 * x := by
    calc
      ‖s - 1‖ ≤ |(s - 1).re| + |(s - 1).im| :=
        Complex.norm_le_abs_re_add_abs_im (s - 1)
      _ = 1 / 2 + 2 * x := by
        norm_num [s, x, abs_mul]
      _ ≤ 3 * x := by linarith
  have hfactor :
      ‖s * (s - 1) / 2‖ ≤ 5 * x ^ 2 := by
    rw [norm_div, norm_mul]
    norm_num
    have hprod := mul_le_mul hsNorm hsOneNorm (norm_nonneg _) (by positivity)
    nlinarith [sq_nonneg x]
  have hsPos : 0 < s.re := by simp [s]
  have hsOne : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [s] at hre
  have hxiFactor :=
    riemannXi_eq_factor_mul_GammaR_mul_riemannZeta_of_re_pos hsPos hsOne
  have hcoord :
      ((hardyXi (2 * t) : ℝ) : ℂ) = riemannXi s := by
    rw [← hardyCriticalXi_eq_ofReal]
    unfold hardyCriticalXi hardyCriticalLinePoint
    congr 1
    dsimp only [s]
    push_cast
    ring
  calc
    ‖hardyXi (2 * t)‖ = ‖riemannXi s‖ := by
      rw [← hcoord]
      simp
    _ = ‖s * (s - 1) / 2‖ * ‖Complex.Gammaℝ s‖ *
        ‖riemannZeta s‖ := by
      rw [hxiFactor]
      simp only [norm_mul]
    _ ≤ (5 * x ^ 2) *
        ((12 * 3 ^ M) * x ^ M *
          Real.exp (-(Real.pi / 2) * x)) *
        (3 * Czeta * x) := by
      gcongr
    _ = K * x ^ (M + 3) *
        Real.exp (-(Real.pi / 2) * x) := by
      dsimp only [K]
      rw [pow_add]
      ring
    _ = K * |t| ^ (M + 3) *
        Real.exp (-(Real.pi / 2) * |t|) := rfl

private theorem pow_mul_exp_neg_mul_le_factorial_mul_inv_sq
    (N : ℕ) {b x : ℝ} (hb : 0 < b) (hx : 0 < x) :
    x ^ N * Real.exp (-b * x) ≤
      ((N + 2).factorial : ℝ) *
        (b ^ (N + 2))⁻¹ * x⁻¹ ^ (2 : ℕ) := by
  have hfactorial :
      0 < ((N + 2).factorial : ℝ) := by positivity
  have hseries :=
    Real.pow_div_factorial_le_exp (b * x) (mul_nonneg hb.le hx.le) (N + 2)
  have hpow :
      (b * x) ^ (N + 2) ≤
        ((N + 2).factorial : ℝ) * Real.exp (b * x) := by
    simpa [mul_comm] using (div_le_iff₀ hfactorial).mp hseries
  have hscale :
      0 ≤ Real.exp (-b * x) * (b ^ (N + 2))⁻¹ *
        x⁻¹ ^ (2 : ℕ) := by positivity
  have hscaled := mul_le_mul_of_nonneg_right hpow hscale
  calc
    x ^ N * Real.exp (-b * x) =
        (b * x) ^ (N + 2) *
          (Real.exp (-b * x) * (b ^ (N + 2))⁻¹ *
            x⁻¹ ^ (2 : ℕ)) := by
      rw [mul_pow, pow_add]
      field_simp [hb.ne', hx.ne']
      ring
    _ ≤ (((N + 2).factorial : ℝ) * Real.exp (b * x)) *
        (Real.exp (-b * x) * (b ^ (N + 2))⁻¹ *
          x⁻¹ ^ (2 : ℕ)) := hscaled
    _ = ((N + 2).factorial : ℝ) *
        (b ^ (N + 2))⁻¹ * x⁻¹ ^ (2 : ℕ) := by
      have hexp :
          Real.exp (b * x) * Real.exp (-b * x) = 1 := by
        rw [← Real.exp_add]
        simp
      rw [show
        ((N + 2).factorial : ℝ) * Real.exp (b * x) *
              (Real.exp (-b * x) * (b ^ (N + 2))⁻¹ *
                x⁻¹ ^ (2 : ℕ)) =
            ((N + 2).factorial : ℝ) *
              (Real.exp (b * x) * Real.exp (-b * x)) *
              (b ^ (N + 2))⁻¹ * x⁻¹ ^ (2 : ℕ) by ring,
        hexp]
      ring

theorem continuous_hardyXiExponentialWeight (a : ℝ) :
    Continuous (hardyXiExponentialWeight a) := by
  unfold hardyXiExponentialWeight
  apply Continuous.div
  · exact (by fun_prop : Continuous fun t : ℝ => Real.exp (a * |t|)).mul
      (continuous_hardyXi.comp (by fun_prop)).norm
  · fun_prop
  · intro t
    positivity

/-- Every exponential weight strictly inside Hardy's source strip is integrable. -/
theorem integrable_hardyXiExponentialWeight
    {a : ℝ} (ha : a < Real.pi / 2) :
    Integrable (hardyXiExponentialWeight a) := by
  obtain ⟨K, hK, N, hxi⟩ :=
    exists_norm_hardyXi_two_mul_le_pow_mul_exp
  let b : ℝ := Real.pi / 2 - a
  have hb : 0 < b := sub_pos.mpr ha
  let C : ℝ :=
    K * ((N + 2).factorial : ℝ) * (b ^ (N + 2))⁻¹
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  apply integrable_of_continuous_norm_le_abs_inv_sq
    (continuous_hardyXiExponentialWeight a) hC
  intro t ht
  let x : ℝ := |t|
  have hx : 1 < x := ht
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hxSq : 1 < x ^ 2 := by
    nlinarith [sq_nonneg (x - 1)]
  have htSq : t ^ 2 = x ^ 2 := by
    simp [x]
  have hden : 1 ≤ (1 / 4 : ℝ) + 4 * t ^ 2 := by
    rw [htSq]
    linarith
  have hdenPos : 0 < (1 / 4 : ℝ) + 4 * t ^ 2 := by positivity
  have hxiBound := hxi t ht
  have hnonneg : 0 ≤ hardyXiExponentialWeight a t := by
    unfold hardyXiExponentialWeight
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  calc
    hardyXiExponentialWeight a t
        ≤ Real.exp (a * x) *
            (K * x ^ N * Real.exp (-(Real.pi / 2) * x)) /
              (1 / 4 + 4 * t ^ 2) := by
      unfold hardyXiExponentialWeight
      apply div_le_div_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left hxiBound (Real.exp_nonneg _)
      · exact hdenPos.le
    _ ≤ Real.exp (a * x) *
        (K * x ^ N * Real.exp (-(Real.pi / 2) * x)) := by
      apply (div_le_iff₀ hdenPos).2
      have hnum :
          0 ≤ Real.exp (a * x) *
            (K * x ^ N * Real.exp (-(Real.pi / 2) * x)) := by
        positivity
      nlinarith
    _ = K * (x ^ N * Real.exp (-b * x)) := by
      have hexp :
          Real.exp (a * x) *
              Real.exp (-(Real.pi / 2) * x) =
            Real.exp (-b * x) := by
        rw [← Real.exp_add]
        congr 1
        dsimp only [b]
        ring
      rw [show
        Real.exp (a * x) *
            (K * x ^ N * Real.exp (-(Real.pi / 2) * x)) =
          K * x ^ N *
            (Real.exp (a * x) *
              Real.exp (-(Real.pi / 2) * x)) by ring, hexp]
      ring
    _ ≤ K * (((N + 2).factorial : ℝ) *
        (b ^ (N + 2))⁻¹ * x⁻¹ ^ (2 : ℕ)) := by
      exact mul_le_mul_of_nonneg_left
        (pow_mul_exp_neg_mul_le_factorial_mul_inv_sq N hb hx0) hK.le
    _ = C * |t|⁻¹ ^ (2 : ℕ) := by
      dsimp only [C, x]
      ring

private theorem pow_mul_exp_neg_mul_le_factorial
    (m : ℕ) {b x : ℝ} (hb : 0 < b) (hx : 0 ≤ x) :
    x ^ m * Real.exp (-b * x) ≤
      (m.factorial : ℝ) * (b ^ m)⁻¹ := by
  have hfactorial : 0 < (m.factorial : ℝ) := by positivity
  have hseries :=
    Real.pow_div_factorial_le_exp (b * x) (mul_nonneg hb.le hx) m
  have hpow :
      (b * x) ^ m ≤ (m.factorial : ℝ) * Real.exp (b * x) := by
    simpa [mul_comm] using (div_le_iff₀ hfactorial).mp hseries
  have hscale :
      0 ≤ Real.exp (-b * x) * (b ^ m)⁻¹ := by positivity
  have hscaled := mul_le_mul_of_nonneg_right hpow hscale
  calc
    x ^ m * Real.exp (-b * x) =
        (b * x) ^ m *
          (Real.exp (-b * x) * (b ^ m)⁻¹) := by
      rw [mul_pow]
      field_simp [hb.ne']
    _ ≤ ((m.factorial : ℝ) * Real.exp (b * x)) *
        (Real.exp (-b * x) * (b ^ m)⁻¹) := hscaled
    _ = (m.factorial : ℝ) * (b ^ m)⁻¹ := by
      have hexp :
          Real.exp (b * x) * Real.exp (-b * x) = 1 := by
        rw [← Real.exp_add]
        simp
      rw [show
        (m.factorial : ℝ) * Real.exp (b * x) *
              (Real.exp (-b * x) * (b ^ m)⁻¹) =
            (m.factorial : ℝ) *
              (Real.exp (b * x) * Real.exp (-b * x)) *
              (b ^ m)⁻¹ by ring,
        hexp]
      ring

/-- Polynomial losses are absorbed by the unused width of Hardy's strip. -/
theorem integrable_abs_pow_mul_hardyXiExponentialWeight
    (m : ℕ) {a : ℝ} (ha : a < Real.pi / 2) :
    Integrable (fun t : ℝ => |t| ^ m * hardyXiExponentialWeight a t) := by
  let a' : ℝ := (a + Real.pi / 2) / 2
  let b : ℝ := a' - a
  have ha' : a' < Real.pi / 2 := by
    dsimp only [a']
    linarith
  have hb : 0 < b := by
    dsimp only [b, a']
    linarith
  let C : ℝ := (m.factorial : ℝ) * (b ^ m)⁻¹
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hmajor :
      Integrable (fun t : ℝ => C * hardyXiExponentialWeight a' t) :=
    (integrable_hardyXiExponentialWeight ha').const_mul C
  refine Integrable.mono' hmajor ?_ (ae_of_all _ fun t => ?_)
  · exact
      ((by fun_prop : Continuous fun t : ℝ => |t| ^ m).mul
        (continuous_hardyXiExponentialWeight a)).aestronglyMeasurable
  let x : ℝ := |t|
  have hx : 0 ≤ x := abs_nonneg t
  have hweight :
      hardyXiExponentialWeight a t =
        Real.exp (-b * x) * hardyXiExponentialWeight a' t := by
    unfold hardyXiExponentialWeight
    have hexp :
        Real.exp (a * x) =
          Real.exp (-b * x) * Real.exp (a' * x) := by
      rw [← Real.exp_add]
      congr 1
      dsimp only [b]
      ring
    rw [hexp]
    ring
  have hpoly :
      x ^ m * Real.exp (-b * x) ≤ C := by
    exact pow_mul_exp_neg_mul_le_factorial m hb hx
  have hweightNonneg :
      0 ≤ hardyXiExponentialWeight a' t := by
    unfold hardyXiExponentialWeight
    positivity
  rw [hweight]
  dsimp only [x] at hpoly
  rw [show
    |t| ^ m *
          (Real.exp (-b * |t|) *
            hardyXiExponentialWeight a' t) =
        (|t| ^ m * Real.exp (-b * |t|)) *
          hardyXiExponentialWeight a' t by ring]
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (mul_nonneg (pow_nonneg (abs_nonneg t) _)
      (Real.exp_nonneg _)) hweightNonneg)]
  exact mul_le_mul_of_nonneg_right hpoly hweightNonneg

private def hardyXiInteriorKernel (alpha : ℂ) (t : ℝ) : ℂ :=
  (Complex.exp (alpha * (t : ℂ)) +
      Complex.exp (-alpha * (t : ℂ))) *
    (hardyXi (2 * t) : ℂ) / (1 / 4 + 4 * t ^ 2)

private theorem continuous_hardyXiInteriorKernel (alpha : ℂ) :
    Continuous (hardyXiInteriorKernel alpha) := by
  unfold hardyXiInteriorKernel
  apply Continuous.div
  · have hExp : Continuous fun t : ℝ =>
        Complex.exp (alpha * (t : ℂ)) +
          Complex.exp (-alpha * (t : ℂ)) := by
      fun_prop
    have hXi : Continuous fun t : ℝ => (hardyXi (2 * t) : ℂ) :=
      Complex.continuous_ofReal.comp
        (continuous_hardyXi.comp (by fun_prop))
    exact hExp.mul hXi
  · exact continuous_const.add
      (continuous_const.mul (Complex.continuous_ofReal.pow 2))
  · intro t
    rw [show
      (1 / 4 + 4 * (t : ℂ) ^ 2 : ℂ) =
        (((1 / 4 : ℝ) + 4 * t ^ 2 : ℝ) : ℂ) by
          push_cast
          ring]
    exact_mod_cast (show (1 / 4 : ℝ) + 4 * t ^ 2 ≠ 0 by positivity)

private theorem norm_hardyXiInteriorKernel_le
    (alpha : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    ‖hardyXiInteriorKernel alpha t‖ ≤
      2 * hardyXiExponentialWeight |alpha.re| t := by
  have hden : 0 < (1 / 4 : ℝ) + 4 * t ^ 2 := by positivity
  have htAbs : |t| = t := abs_of_nonneg ht
  have hpos :
      alpha.re * t ≤ |alpha.re| * |t| := by
    rw [htAbs]
    exact mul_le_mul_of_nonneg_right (le_abs_self alpha.re) ht
  have hneg :
      -alpha.re * t ≤ |alpha.re| * |t| := by
    rw [htAbs]
    exact mul_le_mul_of_nonneg_right (neg_le_abs alpha.re) ht
  have hsum :
      ‖Complex.exp (alpha * (t : ℂ)) +
          Complex.exp (-alpha * (t : ℂ))‖ ≤
        2 * Real.exp (|alpha.re| * |t|) := by
    calc
      ‖Complex.exp (alpha * (t : ℂ)) +
          Complex.exp (-alpha * (t : ℂ))‖
          ≤ ‖Complex.exp (alpha * (t : ℂ))‖ +
              ‖Complex.exp (-alpha * (t : ℂ))‖ :=
        norm_add_le _ _
      _ = Real.exp (alpha.re * t) +
          Real.exp (-alpha.re * t) := by
        rw [Complex.norm_exp, Complex.norm_exp]
        simp
      _ ≤ Real.exp (|alpha.re| * |t|) +
          Real.exp (|alpha.re| * |t|) := by
        gcongr
      _ = 2 * Real.exp (|alpha.re| * |t|) := by ring
  have hdenNorm :
      ‖(1 / 4 + 4 * (t : ℂ) ^ 2 : ℂ)‖ =
        (1 / 4 : ℝ) + 4 * t ^ 2 := by
    rw [show
      (1 / 4 + 4 * (t : ℂ) ^ 2 : ℂ) =
        (((1 / 4 : ℝ) + 4 * t ^ 2 : ℝ) : ℂ) by
          push_cast
          ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hden]
  unfold hardyXiInteriorKernel hardyXiExponentialWeight
  rw [norm_div, norm_mul, hdenNorm]
  rw [show
    2 *
          (Real.exp (|alpha.re| * |t|) *
            ‖hardyXi (2 * t)‖ /
              ((1 / 4 : ℝ) + 4 * t ^ 2)) =
        (2 * Real.exp (|alpha.re| * |t|) *
            ‖hardyXi (2 * t)‖) /
          ((1 / 4 : ℝ) + 4 * t ^ 2) by ring]
  apply div_le_div_of_nonneg_right _ hden.le
  rw [Complex.norm_real]
  calc
    ‖Complex.exp (alpha * (t : ℂ)) +
          Complex.exp (-alpha * (t : ℂ))‖ *
        |hardyXi (2 * t)|
        ≤ (2 * Real.exp (|alpha.re| * |t|)) *
            |hardyXi (2 * t)| :=
      mul_le_mul_of_nonneg_right hsum (abs_nonneg _)
    _ = 2 *
        (Real.exp (|alpha.re| * |t|) *
          |hardyXi (2 * t)|) := by ring
    _ = 2 * Real.exp (|alpha.re| * |t|) *
        ‖hardyXi (2 * t)‖ := by
      rw [Real.norm_eq_abs]
      ring

theorem integrableOn_hardyXiInteriorKernel
    {alpha : ℂ} (halpha : alpha ∈ hardyAlphaStrip) :
    IntegrableOn (hardyXiInteriorKernel alpha) (Ioi (0 : ℝ)) := by
  have ha : |alpha.re| < Real.pi / 2 := halpha
  have hmajor :
      IntegrableOn
        (fun t : ℝ => 2 * hardyXiExponentialWeight |alpha.re| t)
        (Ioi (0 : ℝ)) :=
    ((integrable_hardyXiExponentialWeight ha).const_mul 2).integrableOn
  refine Integrable.mono' hmajor
    (continuous_hardyXiInteriorKernel alpha).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards with t ht
  have hbound :=
    norm_hardyXiInteriorKernel_le alpha (le_of_lt ht)
  have hmajorNonneg :
      0 ≤ 2 * hardyXiExponentialWeight |alpha.re| t := by
    unfold hardyXiExponentialWeight
    positivity
  simpa [Real.norm_eq_abs, abs_of_nonneg hmajorNonneg] using hbound

private def hardyXiInteriorKernelDeriv (alpha : ℂ) (t : ℝ) : ℂ :=
  (Complex.exp (alpha * (t : ℂ)) * (t : ℂ) +
      Complex.exp (-alpha * (t : ℂ)) * (-(t : ℂ))) *
    (hardyXi (2 * t) : ℂ) / (1 / 4 + 4 * t ^ 2)

private theorem hasDerivAt_hardyXiInteriorKernel
    (alpha : ℂ) (t : ℝ) :
    HasDerivAt (fun beta : ℂ => hardyXiInteriorKernel beta t)
      (hardyXiInteriorKernelDeriv alpha t) alpha := by
  have hpos :
      HasDerivAt
        (fun beta : ℂ => Complex.exp (beta * (t : ℂ)))
        (Complex.exp (alpha * (t : ℂ)) * (t : ℂ)) alpha :=
    (Complex.hasDerivAt_exp _).comp alpha
      (by
        simpa only [id_eq, one_mul] using
          (hasDerivAt_id alpha).mul_const (t : ℂ))
  have hneg :
      HasDerivAt
        (fun beta : ℂ => Complex.exp (-beta * (t : ℂ)))
        (Complex.exp (-alpha * (t : ℂ)) * (-(t : ℂ))) alpha := by
    exact (Complex.hasDerivAt_exp _).comp alpha
      (by
        simpa only [id_eq, neg_one_mul] using
          (hasDerivAt_neg alpha).mul_const (t : ℂ))
  have hsum := hpos.add hneg
  have hmul :=
    hsum.mul_const (hardyXi (2 * t) : ℂ)
  have hdiv :=
    hmul.div_const (1 / 4 + 4 * (t : ℂ) ^ 2)
  unfold hardyXiInteriorKernel hardyXiInteriorKernelDeriv
  simpa only [Pi.add_apply] using hdiv

private theorem continuous_hardyXiInteriorKernelDeriv (alpha : ℂ) :
    Continuous (hardyXiInteriorKernelDeriv alpha) := by
  unfold hardyXiInteriorKernelDeriv
  apply Continuous.div
  · have hExp : Continuous fun t : ℝ =>
        Complex.exp (alpha * (t : ℂ)) * (t : ℂ) +
          Complex.exp (-alpha * (t : ℂ)) * (-(t : ℂ)) := by
      fun_prop
    have hXi : Continuous fun t : ℝ => (hardyXi (2 * t) : ℂ) :=
      Complex.continuous_ofReal.comp
        (continuous_hardyXi.comp (by fun_prop))
    exact hExp.mul hXi
  · exact continuous_const.add
      (continuous_const.mul (Complex.continuous_ofReal.pow 2))
  · intro t
    rw [show
      (1 / 4 + 4 * (t : ℂ) ^ 2 : ℂ) =
        (((1 / 4 : ℝ) + 4 * t ^ 2 : ℝ) : ℂ) by
          push_cast
          ring]
    exact_mod_cast (show (1 / 4 : ℝ) + 4 * t ^ 2 ≠ 0 by positivity)

private theorem hardyXiExponentialWeight_mono
    {a c t : ℝ} (hac : a ≤ c) :
    hardyXiExponentialWeight a t ≤
      hardyXiExponentialWeight c t := by
  unfold hardyXiExponentialWeight
  have hden : 0 ≤ (1 / 4 : ℝ) + 4 * t ^ 2 := by positivity
  apply div_le_div_of_nonneg_right _ hden
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right hac (abs_nonneg t))

private theorem norm_hardyXiInteriorKernelDeriv_le
    (alpha : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    ‖hardyXiInteriorKernelDeriv alpha t‖ ≤
      2 * |t| * hardyXiExponentialWeight |alpha.re| t := by
  have hden : 0 < (1 / 4 : ℝ) + 4 * t ^ 2 := by positivity
  have htAbs : |t| = t := abs_of_nonneg ht
  have hpos :
      alpha.re * t ≤ |alpha.re| * |t| := by
    rw [htAbs]
    exact mul_le_mul_of_nonneg_right (le_abs_self alpha.re) ht
  have hneg :
      -alpha.re * t ≤ |alpha.re| * |t| := by
    rw [htAbs]
    exact mul_le_mul_of_nonneg_right (neg_le_abs alpha.re) ht
  have hnum :
      ‖Complex.exp (alpha * (t : ℂ)) * (t : ℂ) +
          Complex.exp (-alpha * (t : ℂ)) * (-(t : ℂ))‖ ≤
        2 * |t| * Real.exp (|alpha.re| * |t|) := by
    calc
      ‖Complex.exp (alpha * (t : ℂ)) * (t : ℂ) +
          Complex.exp (-alpha * (t : ℂ)) * (-(t : ℂ))‖
          ≤ ‖Complex.exp (alpha * (t : ℂ)) * (t : ℂ)‖ +
              ‖Complex.exp (-alpha * (t : ℂ)) * (-(t : ℂ))‖ :=
        norm_add_le _ _
      _ = Real.exp (alpha.re * t) * |t| +
          Real.exp (-alpha.re * t) * |t| := by
        rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp,
          norm_neg, Complex.norm_real, Real.norm_eq_abs]
        simp
      _ ≤ Real.exp (|alpha.re| * |t|) * |t| +
          Real.exp (|alpha.re| * |t|) * |t| := by
        gcongr
      _ = 2 * |t| * Real.exp (|alpha.re| * |t|) := by ring
  have hdenNorm :
      ‖(1 / 4 + 4 * (t : ℂ) ^ 2 : ℂ)‖ =
        (1 / 4 : ℝ) + 4 * t ^ 2 := by
    rw [show
      (1 / 4 + 4 * (t : ℂ) ^ 2 : ℂ) =
        (((1 / 4 : ℝ) + 4 * t ^ 2 : ℝ) : ℂ) by
          push_cast
          ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hden]
  unfold hardyXiInteriorKernelDeriv hardyXiExponentialWeight
  rw [norm_div, norm_mul, hdenNorm]
  rw [show
    2 * |t| *
          (Real.exp (|alpha.re| * |t|) *
            ‖hardyXi (2 * t)‖ /
              ((1 / 4 : ℝ) + 4 * t ^ 2)) =
        (2 * |t| * Real.exp (|alpha.re| * |t|) *
            ‖hardyXi (2 * t)‖) /
          ((1 / 4 : ℝ) + 4 * t ^ 2) by ring]
  apply div_le_div_of_nonneg_right _ hden.le
  rw [Complex.norm_real]
  exact mul_le_mul_of_nonneg_right hnum (norm_nonneg _)

theorem differentiableAt_hardyXiInteriorIntegral
    {alpha : ℂ} (halpha : alpha ∈ hardyAlphaStrip) :
    DifferentiableAt ℂ hardyXiInteriorIntegral alpha := by
  let a : ℝ := (|alpha.re| + Real.pi / 2) / 2
  have halphaA : |alpha.re| < a := by
    dsimp only [a]
    have hstrip : |alpha.re| < Real.pi / 2 := halpha
    linarith
  have ha : a < Real.pi / 2 := by
    dsimp only [a]
    have hstrip : |alpha.re| < Real.pi / 2 := halpha
    linarith
  let s : Set ℂ := {beta : ℂ | |beta.re| < a}
  have hsOpen : IsOpen s := by
    exact isOpen_lt Complex.continuous_re.abs continuous_const
  have hs : s ∈ 𝓝 alpha :=
    hsOpen.mem_nhds halphaA
  have hFMeas :
      ∀ᶠ beta : ℂ in 𝓝 alpha,
        AEStronglyMeasurable (hardyXiInteriorKernel beta)
          (volume.restrict (Ioi (0 : ℝ))) :=
    Filter.Eventually.of_forall fun beta =>
      (continuous_hardyXiInteriorKernel beta).aestronglyMeasurable
  have hFInt :
      Integrable (hardyXiInteriorKernel alpha)
        (volume.restrict (Ioi (0 : ℝ))) :=
    integrableOn_hardyXiInteriorKernel halpha
  have hF'Meas :
      AEStronglyMeasurable (hardyXiInteriorKernelDeriv alpha)
        (volume.restrict (Ioi (0 : ℝ))) :=
    (continuous_hardyXiInteriorKernelDeriv alpha).aestronglyMeasurable
  have hBound :
      ∀ᵐ t : ℝ ∂volume.restrict (Ioi (0 : ℝ)),
        ∀ beta ∈ s,
          ‖hardyXiInteriorKernelDeriv beta t‖ ≤
            2 * |t| * hardyXiExponentialWeight a t := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with t ht
    intro beta hbeta
    calc
      ‖hardyXiInteriorKernelDeriv beta t‖
          ≤ 2 * |t| *
              hardyXiExponentialWeight |beta.re| t :=
        norm_hardyXiInteriorKernelDeriv_le beta (le_of_lt ht)
      _ ≤ 2 * |t| * hardyXiExponentialWeight a t := by
        gcongr
        exact hardyXiExponentialWeight_mono (le_of_lt hbeta)
  have hBoundInt :
      Integrable
        (fun t : ℝ =>
          2 * |t| * hardyXiExponentialWeight a t)
        (volume.restrict (Ioi (0 : ℝ))) := by
    change IntegrableOn
      (fun t : ℝ =>
        2 * |t| * hardyXiExponentialWeight a t)
      (Ioi (0 : ℝ)) volume
    have hfull :=
      (integrable_abs_pow_mul_hardyXiExponentialWeight 1 ha).const_mul 2
    simpa [pow_one, mul_assoc] using hfull.integrableOn
  have hDiff :
      ∀ᵐ t : ℝ ∂volume.restrict (Ioi (0 : ℝ)),
        ∀ beta ∈ s,
          HasDerivAt (fun gamma : ℂ =>
            hardyXiInteriorKernel gamma t)
            (hardyXiInteriorKernelDeriv beta t) beta :=
    Filter.Eventually.of_forall fun t beta _ =>
      hasDerivAt_hardyXiInteriorKernel beta t
  have hIntegral :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Ioi (0 : ℝ)))
      (F := hardyXiInteriorKernel)
      (F' := hardyXiInteriorKernelDeriv)
      (bound := fun t : ℝ =>
        2 * |t| * hardyXiExponentialWeight a t)
      hs hFMeas hFInt hF'Meas hBound hBoundInt hDiff
  change DifferentiableAt ℂ
    (fun beta : ℂ =>
      ∫ t : ℝ in Ioi 0, hardyXiInteriorKernel beta t) alpha
  exact hIntegral.2.differentiableAt

theorem isOpen_hardyAlphaStrip : IsOpen hardyAlphaStrip := by
  exact isOpen_lt Complex.continuous_re.abs continuous_const

theorem differentiableOn_hardyXiInteriorIntegral :
    DifferentiableOn ℂ hardyXiInteriorIntegral hardyAlphaStrip :=
  fun _ halpha =>
    (differentiableAt_hardyXiInteriorIntegral halpha).differentiableWithinAt

theorem analyticOnNhd_hardyXiInteriorIntegral :
    AnalyticOnNhd ℂ hardyXiInteriorIntegral hardyAlphaStrip :=
  (analyticOnNhd_iff_differentiableOn isOpen_hardyAlphaStrip).2
    differentiableOn_hardyXiInteriorIntegral

/-- Hardy's theta side in the upper-half-plane normalization used by Mathlib. -/
def hardyThetaAlpha (alpha : ℂ) : ℂ :=
  jacobiTheta (Complex.I * Complex.exp (Complex.I * alpha))

theorem hardyThetaTau_im_pos
    {alpha : ℂ} (halpha : alpha ∈ hardyAlphaStrip) :
    0 < (Complex.I * Complex.exp (Complex.I * alpha)).im := by
  have hstrip : |alpha.re| < Real.pi / 2 := halpha
  have hcos : 0 < Real.cos alpha.re := by
    apply Real.cos_pos_of_mem_Ioo
    exact ⟨(abs_lt.mp hstrip).1, (abs_lt.mp hstrip).2⟩
  rw [Complex.mul_im, Complex.I_re, zero_mul, Complex.I_im,
    one_mul, Complex.exp_re]
  simpa using mul_pos (Real.exp_pos _) hcos

theorem differentiableAt_hardyThetaAlpha
    {alpha : ℂ} (halpha : alpha ∈ hardyAlphaStrip) :
    DifferentiableAt ℂ hardyThetaAlpha alpha := by
  unfold hardyThetaAlpha
  have hinner :
      DifferentiableAt ℂ
        (fun beta : ℂ =>
          Complex.I * Complex.exp (Complex.I * beta)) alpha := by
    fun_prop
  exact (differentiableAt_jacobiTheta
    (hardyThetaTau_im_pos halpha)).comp alpha hinner

theorem differentiableOn_hardyThetaAlpha :
    DifferentiableOn ℂ hardyThetaAlpha hardyAlphaStrip :=
  fun _ halpha =>
    (differentiableAt_hardyThetaAlpha halpha).differentiableWithinAt

theorem analyticOnNhd_hardyThetaAlpha :
    AnalyticOnNhd ℂ hardyThetaAlpha hardyAlphaStrip :=
  (analyticOnNhd_iff_differentiableOn isOpen_hardyAlphaStrip).2
    differentiableOn_hardyThetaAlpha

theorem hardyThetaSeries_eq_jacobiTheta
    {y : ℂ} (hy : 0 < y.re) :
    hardyThetaSeries y =
      jacobiTheta (Complex.I * y / Real.pi) := by
  have hIm :
      (Complex.I * y / Real.pi).im = y.re / Real.pi := by
    norm_num [Complex.div_im, Complex.mul_im]
    field_simp [Real.pi_ne_zero]
  have hTau : 0 < (Complex.I * y / Real.pi).im := by
    rw [hIm]
    exact div_pos hy Real.pi_pos
  unfold hardyThetaSeries
  rw [jacobiTheta_eq_tsum_nat hTau]
  congr 1
  congr 1
  apply tsum_congr
  intro n
  apply congrArg Complex.exp
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp [hpi]
  rw [Complex.I_sq]
  ring

theorem hardyThetaSeries_pi_exp_eq_hardyThetaAlpha
    {alpha : ℂ} (halpha : alpha ∈ hardyAlphaStrip) :
    hardyThetaSeries
        ((Real.pi : ℂ) *
          Complex.exp (Complex.I * alpha)) =
      hardyThetaAlpha alpha := by
  have hReExp :
      0 < (Complex.exp (Complex.I * alpha)).re := by
    have hTau := hardyThetaTau_im_pos halpha
    simpa [Complex.mul_im] using hTau
  have hy :
      0 < ((Real.pi : ℂ) *
        Complex.exp (Complex.I * alpha)).re := by
    rw [Complex.mul_re]
    norm_num
    exact mul_pos Real.pi_pos hReExp
  rw [hardyThetaSeries_eq_jacobiTheta hy]
  unfold hardyThetaAlpha
  congr 1
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  field_simp [hpi]

theorem hardyThetaSeries_pi_mul_eq_evenKernel
    {x : ℝ} (hx : 0 < x) :
    hardyThetaSeries (((Real.pi * x : ℝ) : ℂ)) =
      (HurwitzZeta.evenKernel 0 x : ℂ) := by
  have hy :
      0 < (((Real.pi * x : ℝ) : ℂ)).re := by
    norm_num
    exact mul_pos Real.pi_pos hx
  rw [hardyThetaSeries_eq_jacobiTheta hy]
  have harg :
      Complex.I * ((Real.pi * x : ℝ) : ℂ) /
          (Real.pi : ℂ) =
        Complex.I * (x : ℂ) := by
    have hpi : (Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp [hpi]
  rw [harg, jacobiTheta_eq_jacobiTheta₂]
  simpa [HurwitzZeta.evenKernel_eq_cosKernel_of_zero] using
    (HurwitzZeta.cosKernel_def 0 x).symm

private def hardyXiOscillatoryKernel (y t : ℝ) : ℂ :=
  Complex.exp
      (Complex.I * ((y * t : ℝ) : ℂ)) *
    (hardyXi (2 * t) : ℂ) /
      (((1 / 4 : ℝ) + 4 * t ^ 2 : ℝ) : ℂ)

private theorem continuous_hardyXiOscillatoryKernel (y : ℝ) :
    Continuous (hardyXiOscillatoryKernel y) := by
  unfold hardyXiOscillatoryKernel
  apply Continuous.div
  · exact (by fun_prop : Continuous fun t : ℝ =>
      Complex.exp
          (Complex.I * ((y * t : ℝ) : ℂ))).mul
        (Complex.continuous_ofReal.comp
          (continuous_hardyXi.comp (by fun_prop)))
  · exact Complex.continuous_ofReal.comp (by fun_prop)
  · intro t
    exact Complex.ofReal_ne_zero.mpr (by positivity)

private theorem norm_hardyXiOscillatoryKernel
    (y t : ℝ) :
    ‖hardyXiOscillatoryKernel y t‖ =
      hardyXiExponentialWeight 0 t := by
  have hden : 0 < (1 / 4 : ℝ) + 4 * t ^ 2 := by positivity
  unfold hardyXiOscillatoryKernel hardyXiExponentialWeight
  rw [norm_div, norm_mul, Complex.norm_exp, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hden]
  norm_num [Complex.mul_re]

private theorem integrable_hardyXiOscillatoryKernel (y : ℝ) :
    Integrable (hardyXiOscillatoryKernel y) := by
  refine Integrable.mono'
    (integrable_hardyXiExponentialWeight
      (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 2))
    (continuous_hardyXiOscillatoryKernel y).aestronglyMeasurable ?_
  exact ae_of_all _ fun t => by
    rw [norm_hardyXiOscillatoryKernel]

private theorem hardyXiOscillatoryKernel_add_neg
    (y t : ℝ) :
    hardyXiOscillatoryKernel y t +
        hardyXiOscillatoryKernel y (-t) =
      hardyXiInteriorKernel
        (Complex.I * (y : ℂ)) t := by
  unfold hardyXiOscillatoryKernel hardyXiInteriorKernel
  rw [show 2 * -t = -(2 * t) by ring, hardyXi_even (2 * t)]
  push_cast
  ring_nf

private theorem integral_hardyXiOscillatoryKernel_eq_interior
    (y : ℝ) :
    (∫ t : ℝ, hardyXiOscillatoryKernel y t) =
      hardyXiInteriorIntegral
        (Complex.I * (y : ℂ)) := by
  have hfull := integrable_hardyXiOscillatoryKernel y
  have hnegative :
      (∫ t : ℝ in Iic 0,
          hardyXiOscillatoryKernel y t) =
        ∫ t : ℝ in Ioi 0,
          hardyXiOscillatoryKernel y (-t) := by
    symm
    simpa only [neg_zero] using
      integral_comp_neg_Ioi 0
        (hardyXiOscillatoryKernel y)
  change
    (∫ t : ℝ, hardyXiOscillatoryKernel y t) =
      ∫ t : ℝ in Ioi 0,
        hardyXiInteriorKernel
          (Complex.I * (y : ℂ)) t
  rw [← integral_add_compl measurableSet_Ioi hfull, compl_Ioi,
    hnegative]
  rw [← integral_add hfull.integrableOn hfull.comp_neg.integrableOn]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  exact hardyXiOscillatoryKernel_add_neg y t

private theorem exp_neg_cpow_hardy_line
    (y t : ℝ) :
    ((Real.exp (-y) : ℝ) : ℂ) ^
        (-(((1 / 4 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) =
      Complex.exp (((y / 4 : ℝ) : ℂ)) *
        Complex.exp
          (Complex.I * ((y * t : ℝ) : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))]
  rw [← Complex.ofReal_log (Real.exp_pos (-y)).le,
    Real.log_exp]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem hardyXiPositiveRealIntegral_exp_neg
    (y : ℝ) :
    hardyXiPositiveRealIntegral (Real.exp (-y)) =
      (((2 / Real.pi : ℝ) : ℂ)) *
        Complex.exp (((y / 4 : ℝ) : ℂ)) *
          hardyXiInteriorIntegral
            (Complex.I * (y : ℂ)) := by
  have hcore :
      (∫ t : ℝ,
          ((Real.exp (-y) : ℝ) : ℂ) ^
              (-(((1 / 4 : ℝ) : ℂ) +
                (t : ℂ) * Complex.I)) *
            (4 * (hardyXi (2 * t) : ℂ) /
              (((1 / 4 : ℝ) + 4 * t ^ 2 : ℝ) : ℂ))) =
        (4 : ℂ) * Complex.exp (((y / 4 : ℝ) : ℂ)) *
          ∫ t : ℝ, hardyXiOscillatoryKernel y t := by
    calc
      (∫ t : ℝ,
          ((Real.exp (-y) : ℝ) : ℂ) ^
              (-(((1 / 4 : ℝ) : ℂ) +
                (t : ℂ) * Complex.I)) *
            (4 * (hardyXi (2 * t) : ℂ) /
              (((1 / 4 : ℝ) + 4 * t ^ 2 : ℝ) : ℂ)))
          =
        ∫ t : ℝ,
          ((4 : ℂ) * Complex.exp (((y / 4 : ℝ) : ℂ))) *
            hardyXiOscillatoryKernel y t := by
        apply integral_congr_ae
        exact ae_of_all _ fun t => by
          dsimp only
          rw [exp_neg_cpow_hardy_line]
          unfold hardyXiOscillatoryKernel
          ring
      _ = (4 : ℂ) * Complex.exp (((y / 4 : ℝ) : ℂ)) *
          ∫ t : ℝ, hardyXiOscillatoryKernel y t := by
        rw [integral_const_mul]
  unfold hardyXiPositiveRealIntegral
  rw [hcore, integral_hardyXiOscillatoryKernel_eq_interior]
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp [hpi]
  ring

private theorem exp_neg_cpow_neg_half (y : ℝ) :
    ((Real.exp (-y) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) =
      Complex.exp (((y / 2 : ℝ) : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))]
  rw [← Complex.ofReal_log (Real.exp_pos (-y)).le,
    Real.log_exp]
  congr 1
  push_cast
  ring

theorem hardyEquationTwo_imaginary (y : ℝ) :
    1 + Complex.exp (((y / 2 : ℝ) : ℂ)) -
        (((2 / Real.pi : ℝ) : ℂ)) *
          Complex.exp (((y / 4 : ℝ) : ℂ)) *
            hardyXiInteriorIntegral
              (Complex.I * (y : ℂ)) =
      hardyThetaAlpha (Complex.I * (y : ℂ)) := by
  let alpha : ℂ := Complex.I * (y : ℂ)
  have halpha : alpha ∈ hardyAlphaStrip := by
    change |alpha.re| < Real.pi / 2
    dsimp only [alpha]
    norm_num [Complex.mul_re]
    linarith [Real.pi_pos]
  have hExp :
      Complex.exp (Complex.I * alpha) =
        (Real.exp (-y) : ℂ) := by
    calc
      Complex.exp (Complex.I * alpha) =
          Complex.exp (((-y : ℝ) : ℂ)) := by
        congr 1
        dsimp only [alpha]
        push_cast
        rw [← mul_assoc, Complex.I_mul_I]
        ring
      _ = (Real.exp (-y) : ℂ) :=
        (Complex.ofReal_exp (-y)).symm
  have htheta :
      (HurwitzZeta.evenKernel 0 (Real.exp (-y)) : ℂ) =
        hardyThetaAlpha alpha := by
    rw [← hardyThetaSeries_pi_mul_eq_evenKernel
      (Real.exp_pos (-y))]
    convert
      (hardyThetaSeries_pi_exp_eq_hardyThetaAlpha halpha) using 1
    rw [hExp]
    push_cast
    rfl
  have hsource :=
    hardyCahenMellinInversion (x := Real.exp (-y))
      (Real.exp_pos (-y))
  rw [exp_neg_cpow_neg_half,
    hardyXiPositiveRealIntegral_exp_neg, htheta] at hsource
  simpa only [alpha] using hsource

/-- The left side of Hardy's equation (2), with all source constants exposed. -/
def hardyEquationTwoLeft (alpha : ℂ) : ℂ :=
  1 + Complex.exp (-(Complex.I * alpha) / 2) -
    (((2 / Real.pi : ℝ) : ℂ)) *
      Complex.exp (-(Complex.I * alpha) / 4) *
        hardyXiInteriorIntegral alpha

theorem hardyEquationTwoLeft_imaginary (y : ℝ) :
    hardyEquationTwoLeft (Complex.I * (y : ℂ)) =
      hardyThetaAlpha (Complex.I * (y : ℂ)) := by
  have hhalf :
      -(Complex.I * (Complex.I * (y : ℂ))) / 2 =
        ((y / 2 : ℝ) : ℂ) := by
    rw [← mul_assoc, Complex.I_mul_I]
    push_cast
    ring
  have hquarter :
      -(Complex.I * (Complex.I * (y : ℂ))) / 4 =
        ((y / 4 : ℝ) : ℂ) := by
    rw [← mul_assoc, Complex.I_mul_I]
    push_cast
    ring
  unfold hardyEquationTwoLeft
  rw [hhalf, hquarter]
  exact hardyEquationTwo_imaginary y

theorem differentiableOn_hardyEquationTwoLeft :
    DifferentiableOn ℂ hardyEquationTwoLeft hardyAlphaStrip := by
  intro alpha halpha
  have hInterior :=
    differentiableAt_hardyXiInteriorIntegral halpha
  have hExpHalf :
      DifferentiableAt ℂ
        (fun beta : ℂ =>
          Complex.exp (-(Complex.I * beta) / 2)) alpha := by
    fun_prop
  have hExpQuarter :
      DifferentiableAt ℂ
        (fun beta : ℂ =>
          Complex.exp (-(Complex.I * beta) / 4)) alpha := by
    fun_prop
  have hleft :
      DifferentiableAt ℂ hardyEquationTwoLeft alpha := by
    unfold hardyEquationTwoLeft
    exact (differentiableAt_const (c := (1 : ℂ)).add hExpHalf).sub
      ((differentiableAt_const
        (c := (((2 / Real.pi : ℝ) : ℂ))).mul
          hExpQuarter).mul hInterior)
  exact hleft.differentiableWithinAt

theorem analyticOnNhd_hardyEquationTwoLeft :
    AnalyticOnNhd ℂ hardyEquationTwoLeft hardyAlphaStrip :=
  (analyticOnNhd_iff_differentiableOn isOpen_hardyAlphaStrip).2
    differentiableOn_hardyEquationTwoLeft

theorem convex_hardyAlphaStrip :
    Convex ℝ hardyAlphaStrip := by
  rw [show
    hardyAlphaStrip =
      {alpha : ℂ | -(Real.pi / 2) < alpha.re} ∩
        {alpha : ℂ | alpha.re < Real.pi / 2} by
      ext alpha
      simp [hardyAlphaStrip, abs_lt]]
  exact
    (convex_halfSpace_re_gt (-(Real.pi / 2))).inter
      (convex_halfSpace_re_lt (Real.pi / 2))

theorem isPreconnected_hardyAlphaStrip :
    IsPreconnected hardyAlphaStrip :=
  convex_hardyAlphaStrip.isPreconnected

/-- Hardy's exact equation (2) throughout the source strip. -/
theorem hardyEquationTwo
    {alpha : ℂ} (halpha : alpha ∈ hardyAlphaStrip) :
    hardyEquationTwoLeft alpha = hardyThetaAlpha alpha := by
  have hzero : (0 : ℂ) ∈ hardyAlphaStrip := by
    change |(0 : ℂ).re| < Real.pi / 2
    norm_num
    exact Real.pi_pos
  let y : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hy :
      Filter.Tendsto y Filter.atTop (𝓝 0) := by
    dsimp only [y]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hyComplex :
      Filter.Tendsto (fun n => (y n : ℂ))
        Filter.atTop (𝓝 (0 : ℂ)) := by
    change Filter.Tendsto (Complex.ofReal ∘ y)
      Filter.atTop (𝓝 (Complex.ofReal 0))
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp hy
  have hAlpha :
      Filter.Tendsto
        (fun n => Complex.I * (y n : ℂ))
        Filter.atTop (𝓝 (0 : ℂ)) := by
    simpa using
      (tendsto_const_nhds.mul hyComplex :
        Filter.Tendsto
          (fun n => Complex.I * (y n : ℂ))
          Filter.atTop (𝓝 (Complex.I * 0)))
  have hPunctured :
      ∀ᶠ n in Filter.atTop,
        Complex.I * (y n : ℂ) ∈
          ({(0 : ℂ)} : Set ℂ)ᶜ :=
    Filter.Eventually.of_forall fun n => by
      simp only [mem_compl_iff, mem_singleton_iff]
      exact mul_ne_zero Complex.I_ne_zero
        (Complex.ofReal_ne_zero.mpr (by
          dsimp only [y]
          positivity))
  have hAlphaWithin :
      Filter.Tendsto
        (fun n => Complex.I * (y n : ℂ))
        Filter.atTop
        (𝓝[({(0 : ℂ)} : Set ℂ)ᶜ] (0 : ℂ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hAlpha, hPunctured⟩
  have heqAtTop :
      ∃ᶠ n in Filter.atTop,
        hardyEquationTwoLeft
            (Complex.I * (y n : ℂ)) =
          hardyThetaAlpha
            (Complex.I * (y n : ℂ)) :=
    (Filter.Eventually.of_forall fun n =>
      hardyEquationTwoLeft_imaginary (y n)).frequently
  have heqFrequently :
      ∃ᶠ beta in 𝓝[≠] (0 : ℂ),
        hardyEquationTwoLeft beta =
          hardyThetaAlpha beta :=
    hAlphaWithin.frequently heqAtTop
  exact
    (AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq
      analyticOnNhd_hardyEquationTwoLeft
      analyticOnNhd_hardyThetaAlpha
      isPreconnected_hardyAlphaStrip hzero
      heqFrequently) halpha

end

end LeanLab.Riemann
