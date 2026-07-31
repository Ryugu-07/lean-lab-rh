import LeanLab.Riemann.LevinsonMontgomeryEulerMaclaurin
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Proof-producing transcendental enclosures for the height-ten certificate

This module packages rationally checkable remainder bounds for logarithms and complex
exponentials.  The intended consumer evaluates the finite Euler--Maclaurin centers using only
finite sums and then transfers the resulting balls to the actual zeta function.
-/

open Complex Finset Real
open scoped BigOperators

namespace LeanLab.Riemann

noncomputable section

/-- The odd atanh polynomial, normalized to approximate `log ((1+x)/(1-x))`. -/
def logAtanhPartial (n : ℕ) (x : ℝ) : ℝ :=
  2 * ∑ k ∈ range n, x ^ (2 * k + 1) / (2 * k + 1)

/-- A rational atanh polynomial encloses the logarithm of a positive ratio. -/
theorem abs_log_div_sub_logAtanhPartial_le
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    |Real.log (a / b) -
        logAtanhPartial n ((a - b) / (a + b))| ≤
      2 * (|(a - b) / (a + b)| ^ (2 * n + 1) /
        (1 - ((a - b) / (a + b)) ^ 2)) := by
  let x : ℝ := (a - b) / (a + b)
  have hab : 0 < a + b := add_pos ha hb
  have hx : |x| < 1 := by
    rw [abs_lt]
    constructor
    · rw [lt_div_iff₀ hab]
      linarith
    · rw [div_lt_one hab]
      linarith
  have hratio : (1 + x) / (1 - x) = a / b := by
    dsimp only [x]
    field_simp [ha.ne', hb.ne', hab.ne']
    ring
  have hraw := Real.sum_range_sub_log_div_le hx n
  rw [hratio] at hraw
  unfold logAtanhPartial
  calc
    |Real.log (a / b) -
        2 * ∑ k ∈ range n, x ^ (2 * k + 1) / (2 * k + 1)| =
        2 * |1 / 2 * Real.log (a / b) -
          ∑ k ∈ range n, x ^ (2 * k + 1) / (2 * k + 1)| := by
      rw [show Real.log (a / b) -
          2 * ∑ k ∈ range n, x ^ (2 * k + 1) / (2 * k + 1) =
        2 * (1 / 2 * Real.log (a / b) -
          ∑ k ∈ range n, x ^ (2 * k + 1) / (2 * k + 1)) by ring,
        abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ 2 * (|x| ^ (2 * n + 1) / (1 - x ^ 2)) :=
      mul_le_mul_of_nonneg_left hraw (by norm_num)

/-- The finite complex exponential Taylor polynomial. -/
def complexExpTaylor (n : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ range n, z ^ k / k.factorial

/-- Taylor's complex exponential remainder with a supplied rational norm majorant. -/
theorem norm_complex_exp_sub_taylor_le
    {z : ℂ} {B : ℝ} (hB : ‖z‖ ≤ B) {n : ℕ}
    (hsmall : B / n.succ ≤ 1 / 2) :
    ‖Complex.exp z - complexExpTaylor n z‖ ≤
      B ^ n / n.factorial * 2 := by
  have hden : (0 : ℝ) ≤ n.succ := by positivity
  have hzsmall : ‖z‖ / n.succ ≤ 1 / 2 :=
    (div_le_div_of_nonneg_right hB hden).trans hsmall
  have hraw := Complex.exp_bound' (x := z) (n := n) hzsmall
  unfold complexExpTaylor
  exact hraw.trans (by
    gcongr)

/-- If the exponent itself is known only within a ball, a Taylor polynomial at the ball center
still gives a certified enclosure.  The nonpositive real part makes the perturbation factor at
most one. -/
theorem norm_complex_exp_sub_taylor_of_near
    {x q : ℂ} {delta B : ℝ}
    (hnear : ‖x - q‖ ≤ delta) (hdelta : delta ≤ 1)
    (hqRe : q.re ≤ 0) (hB : ‖q‖ ≤ B) {n : ℕ}
    (hsmall : B / n.succ ≤ 1 / 2) :
    ‖Complex.exp x - complexExpTaylor n q‖ ≤
      2 * delta + B ^ n / n.factorial * 2 := by
  have hdiffOne : ‖x - q‖ ≤ 1 := hnear.trans hdelta
  have hlocal := Complex.norm_exp_sub_one_le hdiffOne
  have hqExp : ‖Complex.exp q‖ ≤ 1 := by
    rw [Complex.norm_exp]
    exact Real.exp_le_one_iff.mpr hqRe
  have hexpDiff : ‖Complex.exp x - Complex.exp q‖ ≤ 2 * delta := by
    have hid :
        Complex.exp x - Complex.exp q =
          Complex.exp q * (Complex.exp (x - q) - 1) := by
      rw [mul_sub, mul_one, ← Complex.exp_add]
      congr 2
      ring
    rw [hid, norm_mul]
    calc
      ‖Complex.exp q‖ * ‖Complex.exp (x - q) - 1‖ ≤
          1 * (2 * ‖x - q‖) :=
        mul_le_mul hqExp hlocal (norm_nonneg _) (by norm_num)
      _ ≤ 2 * delta := by nlinarith [norm_nonneg (x - q)]
  have htaylor := norm_complex_exp_sub_taylor_le hB hsmall
  calc
    ‖Complex.exp x - complexExpTaylor n q‖ ≤
        ‖Complex.exp x - Complex.exp q‖ +
          ‖Complex.exp q - complexExpTaylor n q‖ := by
      simpa only [sub_add_sub_cancel] using
        norm_add_le (Complex.exp x - Complex.exp q)
          (Complex.exp q - complexExpTaylor n q)
    _ ≤ 2 * delta + B ^ n / n.factorial * 2 :=
      add_le_add hexpDiff htaylor

/-- A certified logarithm ball and a norm bound for the exponent produce a certified complex
power enclosure. -/
theorem norm_ofReal_cpow_sub_taylor_of_log_near
    {u : ℝ} (hu : 0 < u) {s : ℂ} {L e S B : ℝ}
    (hlog : |Real.log u - L| ≤ e) (hs : ‖s‖ ≤ S)
    (hqRe : (((L : ℝ) : ℂ) * (-s)).re ≤ 0)
    (hdelta : e * S ≤ 1)
    (hB : ‖((L : ℝ) : ℂ) * (-s)‖ ≤ B) {n : ℕ}
    (hsmall : B / n.succ ≤ 1 / 2) :
    ‖(u : ℂ) ^ (-s) -
        complexExpTaylor n (((L : ℝ) : ℂ) * (-s))‖ ≤
      2 * (e * S) + B ^ n / n.factorial * 2 := by
  let x : ℂ := ((Real.log u : ℝ) : ℂ) * (-s)
  let q : ℂ := ((L : ℝ) : ℂ) * (-s)
  have hnear : ‖x - q‖ ≤ e * S := by
    calc
      ‖x - q‖ = |Real.log u - L| * ‖s‖ := by
        rw [show x - q = (((Real.log u - L : ℝ) : ℂ)) * (-s) by
          simp only [x, q, Complex.ofReal_sub]
          ring,
          norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_neg]
      _ ≤ e * S :=
        mul_le_mul hlog hs (norm_nonneg s) ((abs_nonneg _).trans hlog)
  have h := norm_complex_exp_sub_taylor_of_near
    (x := x) (q := q) hnear hdelta hqRe hB hsmall
  have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  rw [Complex.cpow_def_of_ne_zero huC, ← Complex.ofReal_log hu.le]
  simpa only [x, q, mul_comm] using h

/-- Closed rational smoke certificate for the logarithm backend. -/
theorem abs_log_two_sub_logAtanhPartial_eight_le :
    |Real.log 2 - logAtanhPartial 8 (1 / 3)| ≤ 1 / 10000000 := by
  have h := abs_log_div_sub_logAtanhPartial_le
    (a := (2 : ℝ)) (b := (1 : ℝ)) (by norm_num) (by norm_num) 8
  norm_num at h ⊢
  exact h.trans (by norm_num)

/-- Closed rational smoke certificate for a complex exponential at height-ten scale. -/
theorem norm_exp_heightTenScale_sub_taylor_eighty_le :
    ‖Complex.exp (((-1 / 2 : ℝ) : ℂ) + (10 : ℂ) * I) -
        complexExpTaylor 80 (((-1 / 2 : ℝ) : ℂ) + (10 : ℂ) * I)‖ ≤
      1 / 100000000000000000000 := by
  let q : ℂ := (((-1 / 2 : ℝ) : ℂ) + (10 : ℂ) * I)
  have hq : ‖q‖ ≤ (11 : ℝ) := by
    calc
      ‖q‖ ≤ ‖(((-1 / 2 : ℝ) : ℂ))‖ + ‖(10 : ℂ) * I‖ := by
        simpa only [q] using
          norm_add_le (((-1 / 2 : ℝ) : ℂ)) ((10 : ℂ) * I)
      _ = 21 / 2 := by norm_num
      _ ≤ 11 := by norm_num
  have h := norm_complex_exp_sub_taylor_le
    (z := q) (B := (11 : ℝ)) hq (n := 80) (by norm_num)
  change ‖Complex.exp q - complexExpTaylor 80 q‖ ≤ _
  exact h.trans (by norm_num)

end

end LeanLab.Riemann
