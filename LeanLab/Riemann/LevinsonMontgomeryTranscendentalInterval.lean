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

/-- Binary range reduction for a positive logarithm.  The fixed order `24` handles `log 2`,
while `ratioOrder` only sees the ratio between `u` and a nearby power of two. -/
def binaryLogCenter (k ratioOrder : ℕ) (u : ℝ) : ℝ :=
  (k : ℝ) * logAtanhPartial 24 (1 / 3) +
    logAtanhPartial ratioOrder ((u - 2 ^ k) / (u + 2 ^ k))

/-- Explicit error radius for `binaryLogCenter`. -/
def binaryLogError (k ratioOrder : ℕ) (u : ℝ) : ℝ :=
  (k : ℝ) *
      (2 * (|(1 / 3 : ℝ)| ^ (2 * 24 + 1) / (1 - (1 / 3 : ℝ) ^ 2))) +
    2 * (|(u - 2 ^ k) / (u + 2 ^ k)| ^ (2 * ratioOrder + 1) /
      (1 - ((u - 2 ^ k) / (u + 2 ^ k)) ^ 2))

/-- A nearby power of two gives a short rational certificate for `log u`. -/
theorem abs_log_sub_binaryLogCenter_le
    {u : ℝ} (hu : 0 < u) (k ratioOrder : ℕ) :
    |Real.log u - binaryLogCenter k ratioOrder u| ≤
      binaryLogError k ratioOrder u := by
  have hpow : (0 : ℝ) < 2 ^ k := pow_pos (by norm_num) k
  have htwo :
      |Real.log 2 - logAtanhPartial 24 (1 / 3)| ≤
        2 * (|(1 / 3 : ℝ)| ^ (2 * 24 + 1) / (1 - (1 / 3 : ℝ) ^ 2)) := by
    convert abs_log_div_sub_logAtanhPartial_le
      (a := (2 : ℝ)) (b := (1 : ℝ)) (by norm_num) (by norm_num) 24 using 1 <;>
      norm_num
  have hratio := abs_log_div_sub_logAtanhPartial_le
    (a := u) (b := (2 : ℝ) ^ k) hu hpow ratioOrder
  have hlogIdentity :
      Real.log u = (k : ℝ) * Real.log 2 + Real.log (u / (2 : ℝ) ^ k) := by
    rw [Real.log_div hu.ne' hpow.ne', Real.log_pow]
    ring
  rw [hlogIdentity]
  unfold binaryLogCenter binaryLogError
  calc
    |(k : ℝ) * Real.log 2 + Real.log (u / 2 ^ k) -
        ((k : ℝ) * logAtanhPartial 24 (1 / 3) +
          logAtanhPartial ratioOrder ((u - 2 ^ k) / (u + 2 ^ k)))| =
        |(k : ℝ) * (Real.log 2 - logAtanhPartial 24 (1 / 3)) +
          (Real.log (u / 2 ^ k) -
            logAtanhPartial ratioOrder ((u - 2 ^ k) / (u + 2 ^ k)))| := by
      congr 1
      ring
    _ ≤ |(k : ℝ) * (Real.log 2 - logAtanhPartial 24 (1 / 3))| +
        |Real.log (u / 2 ^ k) -
          logAtanhPartial ratioOrder ((u - 2 ^ k) / (u + 2 ^ k))| :=
      abs_add_le _ _
    _ = (k : ℝ) * |Real.log 2 - logAtanhPartial 24 (1 / 3)| +
        |Real.log (u / 2 ^ k) -
          logAtanhPartial ratioOrder ((u - 2 ^ k) / (u + 2 ^ k))| := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
    _ ≤ (k : ℝ) *
          (2 * (|(1 / 3 : ℝ)| ^ (2 * 24 + 1) / (1 - (1 / 3 : ℝ) ^ 2))) +
        2 * (|(u - 2 ^ k) / (u + 2 ^ k)| ^ (2 * ratioOrder + 1) /
          (1 - ((u - 2 ^ k) / (u + 2 ^ k)) ^ 2)) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg k)) hratio

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

/-- A common norm bound controls the error after taking a natural power.  The slightly loose
`M ^ n` form is convenient for scaling-and-squaring certificates. -/
theorem norm_pow_sub_pow_le_of_norm_le
    {x y : ℂ} {M e : ℝ} (hM : 1 ≤ M) (he : 0 ≤ e)
    (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) (hxy : ‖x - y‖ ≤ e) (n : ℕ) :
    ‖x ^ n - y ^ n‖ ≤ (n : ℝ) * M ^ n * e := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hM0 : 0 ≤ M := zero_le_one.trans hM
      have hpow0 : 0 ≤ M ^ n := pow_nonneg hM0 n
      have hxpow : ‖x ^ n‖ ≤ M ^ n := by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg x) hx n
      have hpowStep : M ^ n ≤ M ^ (n + 1) := by
        rw [pow_succ]
        nlinarith
      calc
        ‖x ^ (n + 1) - y ^ (n + 1)‖ =
            ‖x ^ n * (x - y) + (x ^ n - y ^ n) * y‖ := by
          congr 1
          ring
        _ ≤ ‖x ^ n * (x - y)‖ + ‖(x ^ n - y ^ n) * y‖ :=
          norm_add_le _ _
        _ = ‖x ^ n‖ * ‖x - y‖ + ‖x ^ n - y ^ n‖ * ‖y‖ := by
          rw [norm_mul, norm_mul]
        _ ≤ M ^ n * e + ((n : ℝ) * M ^ n * e) * M := by
          gcongr
        _ ≤ M ^ (n + 1) * e + ((n : ℝ) * M ^ (n + 1) * e) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right hpowStep he
          · rw [pow_succ]
            ring_nf
            exact le_rfl
        _ = ((n + 1 : ℕ) : ℝ) * M ^ (n + 1) * e := by
          push_cast
          ring

/-- Scaling-and-squaring center for a complex exponential. -/
def scaledComplexExpTaylor (scale order : ℕ) (z : ℂ) : ℂ :=
  (complexExpTaylor order (z / scale)) ^ scale

/-- Taylor evaluation after scaling, followed by an exact natural power, encloses a complex
exponential without requiring a high Taylor order at the original height. -/
theorem norm_complex_exp_sub_scaledTaylor_le
    {z : ℂ} (hzRe : z.re ≤ 0) {B : ℝ} {scale order : ℕ}
    (hscale : 0 < scale) (hB : ‖z / scale‖ ≤ B)
    (hsmall : B / order.succ ≤ 1 / 2) :
    ‖Complex.exp z - scaledComplexExpTaylor scale order z‖ ≤
      (scale : ℝ) *
        (1 + B ^ order / order.factorial * 2) ^ scale *
          (B ^ order / order.factorial * 2) := by
  let r : ℂ := z / scale
  let e : ℝ := B ^ order / order.factorial * 2
  have hscaleR : (0 : ℝ) < scale := by exact_mod_cast hscale
  have hB0 : 0 ≤ B := (norm_nonneg r).trans (by simpa [r] using hB)
  have he : 0 ≤ e := by
    dsimp only [e]
    positivity
  have hrRe : r.re ≤ 0 := by
    have hre : r.re = z.re / scale := by
      simp [r, Complex.div_re, Complex.normSq]
      field_simp [hscaleR.ne']
    rw [hre]
    exact div_nonpos_of_nonpos_of_nonneg hzRe hscaleR.le
  have hexpNorm : ‖Complex.exp r‖ ≤ 1 := by
    rw [Complex.norm_exp]
    exact Real.exp_le_one_iff.mpr hrRe
  have htaylor : ‖Complex.exp r - complexExpTaylor order r‖ ≤ e := by
    simpa only [r, e] using norm_complex_exp_sub_taylor_le hB hsmall
  have htaylorNorm : ‖complexExpTaylor order r‖ ≤ 1 + e := by
    exact (norm_le_norm_add_norm_sub (Complex.exp r)
      (complexExpTaylor order r)).trans (add_le_add hexpNorm htaylor)
  have hpow := norm_pow_sub_pow_le_of_norm_le
    (M := 1 + e) (e := e) (by linarith) he
    (hexpNorm.trans (by linarith)) htaylorNorm htaylor scale
  have hzScale : ((scale : ℂ) * r) = z := by
    dsimp only [r]
    exact mul_div_cancel₀ z (Nat.cast_ne_zero.mpr hscale.ne')
  have hexpScale : Complex.exp z = Complex.exp r ^ scale := by
    rw [← hzScale, Complex.exp_nat_mul]
  rw [hexpScale]
  change ‖Complex.exp r ^ scale - complexExpTaylor order r ^ scale‖ ≤ _
  simpa only [e] using hpow

/-- Scaling-and-squaring remains valid when the exponent is itself enclosed by a certified ball. -/
theorem norm_complex_exp_sub_scaledTaylor_of_near
    {x q : ℂ} {delta B : ℝ}
    (hnear : ‖x - q‖ ≤ delta) (hdelta : delta ≤ 1)
    (hqRe : q.re ≤ 0) {scale order : ℕ}
    (hscale : 0 < scale) (hB : ‖q / scale‖ ≤ B)
    (hsmall : B / order.succ ≤ 1 / 2) :
    ‖Complex.exp x - scaledComplexExpTaylor scale order q‖ ≤
      2 * delta +
        (scale : ℝ) *
          (1 + B ^ order / order.factorial * 2) ^ scale *
            (B ^ order / order.factorial * 2) := by
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
  have hscaled := norm_complex_exp_sub_scaledTaylor_le
    hqRe hscale hB hsmall
  calc
    ‖Complex.exp x - scaledComplexExpTaylor scale order q‖ ≤
        ‖Complex.exp x - Complex.exp q‖ +
          ‖Complex.exp q - scaledComplexExpTaylor scale order q‖ := by
      simpa only [sub_add_sub_cancel] using
        norm_add_le (Complex.exp x - Complex.exp q)
          (Complex.exp q - scaledComplexExpTaylor scale order q)
    _ ≤ 2 * delta +
        (scale : ℝ) *
          (1 + B ^ order / order.factorial * 2) ^ scale *
            (B ^ order / order.factorial * 2) :=
      add_le_add hexpDiff hscaled

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

/-- The logarithm-ball `cpow` certificate with scaling-and-squaring in place of a long Taylor
polynomial at the original height. -/
theorem norm_ofReal_cpow_sub_scaledTaylor_of_log_near
    {u : ℝ} (hu : 0 < u) {s : ℂ} {L e S B : ℝ}
    (hlog : |Real.log u - L| ≤ e) (hs : ‖s‖ ≤ S)
    (hqRe : (((L : ℝ) : ℂ) * (-s)).re ≤ 0)
    (hdelta : e * S ≤ 1) {scale order : ℕ}
    (hscale : 0 < scale)
    (hB : ‖(((L : ℝ) : ℂ) * (-s)) / scale‖ ≤ B)
    (hsmall : B / order.succ ≤ 1 / 2) :
    ‖(u : ℂ) ^ (-s) -
        scaledComplexExpTaylor scale order (((L : ℝ) : ℂ) * (-s))‖ ≤
      2 * (e * S) +
        (scale : ℝ) *
          (1 + B ^ order / order.factorial * 2) ^ scale *
            (B ^ order / order.factorial * 2) := by
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
  have h := norm_complex_exp_sub_scaledTaylor_of_near
    (x := x) (q := q) hnear hdelta hqRe hscale hB hsmall
  have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  rw [Complex.cpow_def_of_ne_zero huC, ← Complex.ofReal_log hu.le]
  simpa only [x, q, mul_comm] using h

/-- A complete binary-range-reduced, scaling-and-squaring center for a positive-real complex
power. -/
def binaryScaledCpowCenter
    (k ratioOrder scale expOrder : ℕ) (u : ℝ) (s : ℂ) : ℂ :=
  scaledComplexExpTaylor scale expOrder
    (((binaryLogCenter k ratioOrder u : ℝ) : ℂ) * (-s))

/-- The corresponding explicit radius. -/
def binaryScaledCpowError
    (k ratioOrder scale expOrder : ℕ) (u S B : ℝ) : ℝ :=
  2 * (binaryLogError k ratioOrder u * S) +
    (scale : ℝ) *
      (1 + B ^ expOrder / expOrder.factorial * 2) ^ scale *
        (B ^ expOrder / expOrder.factorial * 2)

/-- Binary logarithm reduction and scaling-and-squaring combine into one reusable positive-real
complex-power enclosure. -/
theorem norm_ofReal_cpow_sub_binaryScaledCpowCenter_le
    {u : ℝ} (hu : 0 < u) {s : ℂ} (k ratioOrder : ℕ) {S B : ℝ}
    (hs : ‖s‖ ≤ S)
    (hqRe : (((binaryLogCenter k ratioOrder u : ℝ) : ℂ) * (-s)).re ≤ 0)
    (hdelta : binaryLogError k ratioOrder u * S ≤ 1)
    {scale expOrder : ℕ} (hscale : 0 < scale)
    (hB : ‖(((binaryLogCenter k ratioOrder u : ℝ) : ℂ) * (-s)) / scale‖ ≤ B)
    (hsmall : B / expOrder.succ ≤ 1 / 2) :
    ‖(u : ℂ) ^ (-s) -
        binaryScaledCpowCenter k ratioOrder scale expOrder u s‖ ≤
      binaryScaledCpowError k ratioOrder scale expOrder u S B := by
  exact norm_ofReal_cpow_sub_scaledTaylor_of_log_near hu
    (abs_log_sub_binaryLogCenter_le hu k ratioOrder) hs hqRe hdelta hscale hB hsmall

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

/-- The binary logarithm reduction already gives a short rational enclosure at the worst ratio
among the selected bases `1,...,30`. -/
theorem abs_log_23_sub_binaryLogCenter_le :
    |Real.log 23 - binaryLogCenter 5 12 23| ≤
      1 / 1000000000000000000 := by
  have h := abs_log_sub_binaryLogCenter_le (u := (23 : ℝ)) (by norm_num) 5 12
  exact h.trans (by norm_num [binaryLogError])

/-- Scaling-and-squaring reduces the height-ten exponential smoke certificate from order `80`
to order `16`. -/
theorem norm_exp_heightTenScale_sub_scaledTaylor_le :
    ‖Complex.exp (((-1 / 2 : ℝ) : ℂ) + (10 : ℂ) * I) -
        scaledComplexExpTaylor 32 16
          (((-1 / 2 : ℝ) : ℂ) + (10 : ℂ) * I)‖ ≤
      1 / 10000000000 := by
  let q : ℂ := (((-1 / 2 : ℝ) : ℂ) + (10 : ℂ) * I)
  have hq : ‖q‖ ≤ (11 : ℝ) := by
    calc
      ‖q‖ ≤ ‖(((-1 / 2 : ℝ) : ℂ))‖ + ‖(10 : ℂ) * I‖ := by
        simpa only [q] using
          norm_add_le (((-1 / 2 : ℝ) : ℂ)) ((10 : ℂ) * I)
      _ = 21 / 2 := by norm_num
      _ ≤ 11 := by norm_num
  have hscaled : ‖q / (32 : ℕ)‖ ≤ (1 : ℝ) := by
    rw [norm_div]
    norm_num
    linarith
  have h := norm_complex_exp_sub_scaledTaylor_le
    (z := q) (B := (1 : ℝ)) (scale := 32) (order := 16)
    (by norm_num [q]) (by norm_num) hscaled (by norm_num)
  change ‖Complex.exp q - scaledComplexExpTaylor 32 16 q‖ ≤ _
  exact h.trans (by norm_num)

/-- A closed certificate for the hardest binary range-reduction ratio in the finite sum, at the
reflected critical endpoint and height ten. -/
theorem norm_23_cpow_reflectedHeightTen_sub_binaryScaledCpowCenter_le :
    ‖(23 : ℂ) ^
          (-((((1 / 2 : ℝ) : ℂ) - (10 : ℂ) * I)))-
        binaryScaledCpowCenter 5 12 64 16 23
          ((((1 / 2 : ℝ) : ℂ) - (10 : ℂ) * I))‖ ≤
      1 / 10000000000 := by
  let s : ℂ := (((1 / 2 : ℝ) : ℂ) - (10 : ℂ) * I)
  let L : ℝ := binaryLogCenter 5 12 23
  have hs : ‖s‖ ≤ (11 : ℝ) := by
    calc
      ‖s‖ ≤ ‖(((1 / 2 : ℝ) : ℂ))‖ + ‖(10 : ℂ) * I‖ := by
        simpa only [s] using
          norm_sub_le (((1 / 2 : ℝ) : ℂ)) ((10 : ℂ) * I)
      _ = 21 / 2 := by norm_num
      _ ≤ 11 := by norm_num
  have hL0 : 0 ≤ L := by
    norm_num [L, binaryLogCenter, logAtanhPartial]
  have hL : |L| ≤ 7 / 2 := by
    rw [abs_of_nonneg hL0]
    norm_num [L, binaryLogCenter, logAtanhPartial]
  have hqRe : ((((L : ℝ) : ℂ) * (-s)).re ≤ 0) := by
    norm_num [s, Complex.mul_re]
    nlinarith
  have hdelta : binaryLogError 5 12 23 * (11 : ℝ) ≤ 1 := by
    norm_num [binaryLogError]
  have hB : ‖(((L : ℝ) : ℂ) * (-s)) / (64 : ℕ)‖ ≤ (1 : ℝ) := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_neg]
    norm_num
    calc
      |L| * ‖s‖ / 64 ≤ (7 / 2 : ℝ) * 11 / 64 := by
        gcongr
      _ ≤ 1 := by norm_num
  have h := norm_ofReal_cpow_sub_binaryScaledCpowCenter_le
    (u := (23 : ℝ)) (s := s) (S := (11 : ℝ)) (B := (1 : ℝ))
    (by norm_num) 5 12 hs (by simpa only [L] using hqRe) hdelta
    (scale := 64) (expOrder := 16) (by norm_num)
    (by simpa only [L] using hB) (by norm_num)
  change ‖(23 : ℂ) ^ (-s) - binaryScaledCpowCenter 5 12 64 16 23 s‖ ≤ _
  exact h.trans (by norm_num [binaryScaledCpowError, binaryLogError])

end

end LeanLab.Riemann
