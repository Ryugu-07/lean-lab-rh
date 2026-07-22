import LeanLab.Riemann.LiReverseCriterion

set_option linter.style.header false

/-!
# Farmer--Bettin--Gonek theta-infinity consumers

This module aligns the logarithmically tapered mollifier used by Farmer and by
Bettin--Gonek.  It proves the real-cutoff interpolation hidden in the passage from integer
mollifier lengths to an integral over real lengths, and isolates the final power-exponent
consumer in the proof that the theta-infinity conjecture implies RH.

The analytic moment-to-power bridge is not proved here.
-/

namespace LeanLab.Riemann

open Complex Filter MeasureTheory Real Set
open scoped BigOperators Interval

noncomputable section

/-- The source logarithmic taper `log(x/n) / log x`. -/
def farmerLogTaper (x : ℝ) (n : ℕ) : ℝ :=
  Real.log (x / (n : ℝ)) / Real.log x

/-- A logarithmically tapered Dirichlet polynomial with a fixed natural cutoff. -/
def farmerMollifierCore (a : ℕ → ℂ) (N : ℕ) (x : ℝ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-s) * farmerLogTaper x n

/-- The complex Mobius coefficient in Farmer's mollifier. -/
def farmerMobiusCoefficient (n : ℕ) : ℂ :=
  ((ArithmeticFunction.moebius n : ℤ) : ℂ)

/-- The source real-cutoff mollifier, extended by zero at and below `x = 1`. -/
def farmerMollifier (x : ℝ) (s : ℂ) : ℂ :=
  if 1 < x then farmerMollifierCore farmerMobiusCoefficient ⌊x⌋₊ x s else 0

/-- The point `1/2 + i t` on the critical line. -/
def farmerCriticalLinePoint (t : ℝ) : ℂ :=
  (1 / 2 : ℝ) + t * Complex.I

/-- Bettin--Gonek's mollified second moment `I_x(T1,T2)`. -/
def farmerMollifiedMoment (x T1 T2 : ℝ) : ℝ :=
  ∫ t in T1..T2,
    Complex.normSq
      (farmerMollifier x (farmerCriticalLinePoint t) *
        riemannZeta (farmerCriticalLinePoint t))

theorem farmerLogTaper_eq_one_sub {x : ℝ} (hx : 1 < x) {n : ℕ} (hn : 1 ≤ n) :
    farmerLogTaper x n = 1 - Real.log n / Real.log x := by
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hn)
  rw [farmerLogTaper, Real.log_div hx0 hn0]
  have hlogx : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  field_simp

/-- The interpolation coordinate for real cutoffs between `N` and `N+1`. -/
def farmerCutoffBlend (N : ℕ) (x : ℝ) : ℝ :=
  ((Real.log x)⁻¹ - (Real.log ((N : ℝ) + 1))⁻¹) /
    ((Real.log N)⁻¹ - (Real.log ((N : ℝ) + 1))⁻¹)

private theorem farmer_log_nat_pos {N : ℕ} (hN : 2 ≤ N) :
    0 < Real.log N := by
  exact Real.log_pos (by exact_mod_cast (show 1 < N by omega))

private theorem farmer_log_nat_succ_pos {N : ℕ} (hN : 2 ≤ N) :
    0 < Real.log ((N : ℝ) + 1) := by
  exact Real.log_pos (by exact_mod_cast (show 1 < N + 1 by omega))

theorem farmerCutoffBlend_mem_Icc {N : ℕ} (hN : 2 ≤ N) {x : ℝ}
    (hNx : (N : ℝ) ≤ x) (hxN : x ≤ N + 1) :
    farmerCutoffBlend N x ∈ Set.Icc (0 : ℝ) 1 := by
  have hlogN : 0 < Real.log N := farmer_log_nat_pos hN
  have hlogNp : 0 < Real.log ((N : ℝ) + 1) := farmer_log_nat_succ_pos hN
  have hxpos : 0 < x := lt_of_lt_of_le (by positivity : (0 : ℝ) < N) hNx
  have hlogx : 0 < Real.log x := Real.log_pos (by
    have : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    linarith)
  have hlogNx : Real.log N ≤ Real.log x :=
    Real.strictMonoOn_log.monotoneOn
      (by change (0 : ℝ) < N; positivity) (by change (0 : ℝ) < x; exact hxpos) hNx
  have hlogxNp : Real.log x ≤ Real.log ((N : ℝ) + 1) :=
    Real.strictMonoOn_log.monotoneOn (by change (0 : ℝ) < x; exact hxpos)
      (by change (0 : ℝ) < (N : ℝ) + 1; positivity) hxN
  have hinv_left : (Real.log ((N : ℝ) + 1))⁻¹ ≤ (Real.log x)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hlogx hlogxNp
  have hinv_right : (Real.log x)⁻¹ ≤ (Real.log N)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hlogN hlogNx
  have hlogNNp : Real.log N < Real.log ((N : ℝ) + 1) := by
    apply Real.strictMonoOn_log
    · change (0 : ℝ) < N
      positivity
    · change (0 : ℝ) < (N : ℝ) + 1
      positivity
    · exact_mod_cast (Nat.lt_succ_self N)
  have hden : 0 < (Real.log N)⁻¹ - (Real.log ((N : ℝ) + 1))⁻¹ := by
    have := one_div_lt_one_div_of_lt hlogN hlogNNp
    simpa only [one_div] using sub_pos.mpr this
  constructor
  · exact div_nonneg (sub_nonneg.mpr hinv_left) hden.le
  · rw [farmerCutoffBlend, div_le_one hden]
    linarith

theorem farmerLogTaper_interpolate {N : ℕ} (hN : 2 ≤ N) {x : ℝ}
    (hNx : (N : ℝ) ≤ x) (_hxN : x ≤ N + 1) {n : ℕ} (hn : 1 ≤ n) :
    farmerLogTaper x n =
      farmerCutoffBlend N x * farmerLogTaper N n +
        (1 - farmerCutoffBlend N x) * farmerLogTaper (N + 1) n := by
  have hxgt : 1 < x := by
    have : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    linarith
  have hNgt : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNpgt : (1 : ℝ) < N + 1 := by exact_mod_cast (show 1 < N + 1 by omega)
  rw [farmerLogTaper_eq_one_sub hxgt hn,
    farmerLogTaper_eq_one_sub hNgt hn,
    farmerLogTaper_eq_one_sub hNpgt hn]
  have hlogN : Real.log (N : ℝ) ≠ 0 := (Real.log_pos hNgt).ne'
  have hlogNp : Real.log (N + 1 : ℝ) ≠ 0 := (Real.log_pos hNpgt).ne'
  have hlogx : Real.log x ≠ 0 := (Real.log_pos hxgt).ne'
  have hden : (Real.log N)⁻¹ - (Real.log ((N : ℝ) + 1))⁻¹ ≠ 0 := by
    have hlt : Real.log N < Real.log ((N : ℝ) + 1) := by
      exact Real.strictMonoOn_log (by change (0 : ℝ) < N; positivity)
        (by change (0 : ℝ) < (N : ℝ) + 1; positivity)
        (by exact_mod_cast Nat.lt_succ_self N)
    have hinv := one_div_lt_one_div_of_lt (Real.log_pos hNgt) hlt
    simpa only [one_div, sub_ne_zero] using hinv.ne'
  have hlogdiff : Real.log ((N : ℝ) + 1) - Real.log N ≠ 0 := by
    apply sub_ne_zero.mpr
    exact (Real.strictMonoOn_log (by change (0 : ℝ) < N; positivity)
      (by change (0 : ℝ) < (N : ℝ) + 1; positivity)
      (by exact_mod_cast Nat.lt_succ_self N)).ne'
  have hblend : (Real.log x)⁻¹ =
      farmerCutoffBlend N x * (Real.log N)⁻¹ +
        (1 - farmerCutoffBlend N x) * (Real.log ((N : ℝ) + 1))⁻¹ := by
    rw [farmerCutoffBlend]
    field_simp [hlogN, hlogNp, hlogx, hden, hlogdiff]
    ring
  simp only [div_eq_mul_inv]
  rw [hblend]
  ring

theorem farmerMollifierCore_interpolate (a : ℕ → ℂ) {N : ℕ} (hN : 2 ≤ N)
    {x : ℝ} (hNx : (N : ℝ) ≤ x) (hxN : x ≤ N + 1) (s : ℂ) :
    farmerMollifierCore a N x s =
      farmerCutoffBlend N x * farmerMollifierCore a N N s +
        (1 - farmerCutoffBlend N x) * farmerMollifierCore a N (N + 1) s := by
  rw [farmerMollifierCore, farmerMollifierCore, farmerMollifierCore]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  rw [farmerLogTaper_interpolate hN hNx hxN hn1]
  push_cast
  ring

theorem farmerMollifierCore_succ_endpoint (a : ℕ → ℂ) {N : ℕ} (hN : 1 ≤ N)
    (s : ℂ) :
    farmerMollifierCore a (N + 1) (N + 1) s =
      farmerMollifierCore a N (N + 1) s := by
  rw [farmerMollifierCore, farmerMollifierCore]
  have hIcc : Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hIcc]
  rw [Finset.sum_insert (by simp)]
  simp [farmerLogTaper]

theorem farmerCutoffBlend_right_endpoint {N : ℕ} (hN : 2 ≤ N) :
    farmerCutoffBlend N (N + 1) = 0 := by
  have hlogN : 0 < Real.log N := farmer_log_nat_pos hN
  have hlogNp : 0 < Real.log ((N : ℝ) + 1) := farmer_log_nat_succ_pos hN
  have hden : (Real.log N)⁻¹ - (Real.log ((N : ℝ) + 1))⁻¹ ≠ 0 := by
    have hlt : Real.log N < Real.log ((N : ℝ) + 1) :=
      Real.strictMonoOn_log (by change (0 : ℝ) < N; positivity)
        (by change (0 : ℝ) < (N : ℝ) + 1; positivity)
        (by exact_mod_cast Nat.lt_succ_self N)
    have hinv := one_div_lt_one_div_of_lt hlogN hlt
    simpa only [one_div, sub_ne_zero] using hinv.ne'
  simp [farmerCutoffBlend]

theorem farmerMollifier_nat_eq_core {N : ℕ} (hN : 2 ≤ N) (s : ℂ) :
    farmerMollifier N s = farmerMollifierCore farmerMobiusCoefficient N N s := by
  have hNgt : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  simp [farmerMollifier, hNgt]

theorem farmerMollifier_interpolate {N : ℕ} (hN : 2 ≤ N) {x : ℝ}
    (hNx : (N : ℝ) ≤ x) (hxN : x ≤ N + 1) (s : ℂ) :
    farmerMollifier x s =
      farmerCutoffBlend N x * farmerMollifier N s +
        (1 - farmerCutoffBlend N x) * farmerMollifier (N + 1) s := by
  have hxgt : 1 < x := by
    have hNgt : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    linarith
  by_cases htop : x = N + 1
  · subst x
    rw [farmerCutoffBlend_right_endpoint hN]
    norm_num
  · have hxlt : x < (N : ℝ) + 1 := lt_of_le_of_ne hxN htop
    have hfloor : ⌊x⌋₊ = N := by
      apply (Nat.floor_eq_iff (le_of_lt (zero_lt_one.trans hxgt))).2
      exact ⟨hNx, hxlt⟩
    have hNpCore := farmerMollifier_nat_eq_core (N := N + 1)
      (show 2 ≤ N + 1 by omega) s
    norm_num [Nat.cast_add, Nat.cast_one] at hNpCore
    rw [farmerMollifier, if_pos hxgt, hfloor,
      farmerMollifier_nat_eq_core hN, hNpCore,
      farmerMollifierCore_interpolate farmerMobiusCoefficient hN hNx hxN,
      farmerMollifierCore_succ_endpoint farmerMobiusCoefficient (show 1 ≤ N by omega)]

theorem complex_normSq_convex {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (z w : ℂ) :
    Complex.normSq ((u : ℂ) * z + ((1 - u : ℝ) : ℂ) * w) ≤
      u * Complex.normSq z + (1 - u) * Complex.normSq w := by
  rw [Complex.normSq_apply, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  have huprod : 0 ≤ u * (1 - u) := mul_nonneg hu0 (sub_nonneg.mpr hu1)
  have hsquares : 0 ≤ (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hnonneg : 0 ≤ u * (1 - u) *
      ((z.re - w.re) ^ 2 + (z.im - w.im) ^ 2) := mul_nonneg huprod hsquares
  nlinarith

theorem farmerMollifierCore_mul_normSq_le (a : ℕ → ℂ) {N : ℕ} (hN : 2 ≤ N)
    {x : ℝ} (hNx : (N : ℝ) ≤ x) (hxN : x ≤ N + 1) (s z : ℂ) :
    Complex.normSq (farmerMollifierCore a N x s * z) ≤
      farmerCutoffBlend N x * Complex.normSq (farmerMollifierCore a N N s * z) +
        (1 - farmerCutoffBlend N x) *
          Complex.normSq (farmerMollifierCore a N (N + 1) s * z) := by
  rw [farmerMollifierCore_interpolate a hN hNx hxN]
  have hu := farmerCutoffBlend_mem_Icc hN hNx hxN
  have heq :
      (farmerCutoffBlend N x * farmerMollifierCore a N N s +
          (1 - farmerCutoffBlend N x) * farmerMollifierCore a N (N + 1) s) * z =
        (farmerCutoffBlend N x : ℂ) * (farmerMollifierCore a N N s * z) +
          ((1 - farmerCutoffBlend N x : ℝ) : ℂ) *
            (farmerMollifierCore a N (N + 1) s * z) := by
    push_cast
    ring
  rw [heq]
  exact complex_normSq_convex hu.1 hu.2 _ _

theorem farmerMollifier_mul_normSq_le {N : ℕ} (hN : 2 ≤ N)
    {x : ℝ} (hNx : (N : ℝ) ≤ x) (hxN : x ≤ N + 1) (s z : ℂ) :
    Complex.normSq (farmerMollifier x s * z) ≤
      farmerCutoffBlend N x * Complex.normSq (farmerMollifier N s * z) +
        (1 - farmerCutoffBlend N x) *
          Complex.normSq (farmerMollifier (N + 1) s * z) := by
  rw [farmerMollifier_interpolate hN hNx hxN]
  have hu := farmerCutoffBlend_mem_Icc hN hNx hxN
  have heq :
      (farmerCutoffBlend N x * farmerMollifier N s +
          (1 - farmerCutoffBlend N x) * farmerMollifier (N + 1) s) * z =
        (farmerCutoffBlend N x : ℂ) * (farmerMollifier N s * z) +
          ((1 - farmerCutoffBlend N x : ℝ) : ℂ) *
            (farmerMollifier (N + 1) s * z) := by
    push_cast
    ring
  rw [heq]
  exact complex_normSq_convex hu.1 hu.2 _ _

theorem continuous_farmerCriticalLinePoint : Continuous farmerCriticalLinePoint := by
  change Continuous (fun t : ℝ => (1 / 2 : ℝ) + t * Complex.I)
  fun_prop

theorem farmerCriticalLinePoint_ne_one (t : ℝ) : farmerCriticalLinePoint t ≠ 1 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num [farmerCriticalLinePoint] at hre

theorem continuous_farmerMollifier_criticalLine {x : ℝ} (hx : 1 < x) :
    Continuous (fun t : ℝ => farmerMollifier x (farmerCriticalLinePoint t)) := by
  simp only [farmerMollifier, if_pos hx, farmerMollifierCore]
  apply continuous_finsetSum
  intro n hn
  have hn0 : (n : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_zero_of_lt (Finset.mem_Icc.mp hn).1)
  have hpow : Continuous (fun t : ℝ => (n : ℂ) ^ (-farmerCriticalLinePoint t)) :=
    (continuous_iff_continuousAt.mpr fun _ => continuousAt_const_cpow hn0).comp
      continuous_farmerCriticalLinePoint.neg
  exact (continuous_const.mul hpow).mul continuous_const

theorem continuous_riemannZeta_criticalLine :
    Continuous (fun t : ℝ => riemannZeta (farmerCriticalLinePoint t)) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (differentiableAt_riemannZeta (farmerCriticalLinePoint_ne_one t)).continuousAt.comp
    continuous_farmerCriticalLinePoint.continuousAt

theorem continuous_farmerMollifiedIntegrand {x : ℝ} (hx : 1 < x) :
    Continuous (fun t : ℝ =>
      Complex.normSq
        (farmerMollifier x (farmerCriticalLinePoint t) *
          riemannZeta (farmerCriticalLinePoint t))) :=
  Complex.continuous_normSq.comp
    ((continuous_farmerMollifier_criticalLine hx).mul continuous_riemannZeta_criticalLine)

theorem intervalIntegrable_farmerMollifiedIntegrand {x : ℝ} (hx : 1 < x) (T1 T2 : ℝ) :
    IntervalIntegrable (fun t : ℝ =>
      Complex.normSq
        (farmerMollifier x (farmerCriticalLinePoint t) *
          riemannZeta (farmerCriticalLinePoint t))) volume T1 T2 :=
  (continuous_farmerMollifiedIntegrand hx).intervalIntegrable T1 T2

theorem farmerMollifiedMoment_interpolate {N : ℕ} (hN : 2 ≤ N)
    {x T1 T2 : ℝ} (hNx : (N : ℝ) ≤ x) (hxN : x ≤ N + 1) (hT : T1 ≤ T2) :
    farmerMollifiedMoment x T1 T2 ≤
      farmerCutoffBlend N x * farmerMollifiedMoment N T1 T2 +
        (1 - farmerCutoffBlend N x) * farmerMollifiedMoment (N + 1) T1 T2 := by
  let f := fun t : ℝ => Complex.normSq
    (farmerMollifier N (farmerCriticalLinePoint t) * riemannZeta (farmerCriticalLinePoint t))
  let g := fun t : ℝ => Complex.normSq
    (farmerMollifier (N + 1) (farmerCriticalLinePoint t) *
      riemannZeta (farmerCriticalLinePoint t))
  have hNgt : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNpgt : (1 : ℝ) < N + 1 := by exact_mod_cast (show 1 < N + 1 by omega)
  have hxgt : 1 < x := lt_of_lt_of_le hNgt hNx
  have hf : IntervalIntegrable f volume T1 T2 :=
    intervalIntegrable_farmerMollifiedIntegrand hNgt T1 T2
  have hg : IntervalIntegrable g volume T1 T2 :=
    intervalIntegrable_farmerMollifiedIntegrand hNpgt T1 T2
  have hlinear : IntervalIntegrable
      (fun t => farmerCutoffBlend N x * f t + (1 - farmerCutoffBlend N x) * g t)
      volume T1 T2 := (hf.const_mul _).add (hg.const_mul _)
  have hmono := intervalIntegral.integral_mono_on hT
    (intervalIntegrable_farmerMollifiedIntegrand hxgt T1 T2) hlinear (fun t _ =>
      farmerMollifier_mul_normSq_le hN hNx hxN (farmerCriticalLinePoint t)
        (riemannZeta (farmerCriticalLinePoint t)))
  rw [intervalIntegral.integral_add (hf.const_mul _) (hg.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hmono
  simpa only [farmerMollifiedMoment, f, g] using hmono

/-- The final power-growth obstruction in Bettin--Gonek Theorem 1. -/
def BettinGonekPowerObstruction (theta beta : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ T : ℝ in atTop,
        T ^ (2 * beta * theta) ≤ C * T ^ (1 + epsilon + theta)

/-- The source uniform mollified-moment hypothesis through length `T^theta`. -/
def FarmerLongMollifierBound (theta : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ C T0 : ℝ, 0 < C ∧ 2 ≤ T0 ∧
      ∀ T : ℝ, T0 ≤ T → ∀ N : ℕ, 2 ≤ N → (N : ℝ) ≤ T ^ theta →
        farmerMollifiedMoment N 0 T ≤ C * T ^ (1 + epsilon)

/-- Farmer's theta-infinity conjecture in the source uniform-bound form. -/
def FarmerThetaInfinityConjecture : Prop :=
  ∀ theta : ℝ, 0 < theta → FarmerLongMollifierBound theta

/-- The unformalized analytic content of Bettin--Gonek Theorem 1. -/
def BettinGonekMomentToPowerBridge (theta : ℝ) : Prop :=
  FarmerLongMollifierBound theta →
    ∀ rho : ℂ, IsNontrivialZero rho →
      BettinGonekPowerObstruction theta rho.re

theorem beta_le_of_bettinGonekPowerObstruction {theta beta : ℝ} (htheta : 0 < theta)
    (hpower : BettinGonekPowerObstruction theta beta) :
    beta ≤ 1 / 2 + 1 / (2 * theta) := by
  by_contra hbeta
  have hgap : 0 < 2 * beta * theta - (1 + theta) := by
    have htheta2 : 0 < 2 * theta := by positivity
    have := (not_le.mp hbeta)
    have hmul := mul_lt_mul_of_pos_right this htheta2
    have hcancel : (1 / (2 * theta)) * (2 * theta) = 1 := by
      field_simp [htheta.ne']
    have hhalf : (1 / 2 : ℝ) * (2 * theta) = theta := by ring
    nlinarith
  let epsilon := (2 * beta * theta - (1 + theta)) / 2
  have hepsilon : 0 < epsilon := by simp only [epsilon]; positivity
  obtain ⟨C, hC, hbound⟩ := hpower epsilon hepsilon
  have hexponent : 0 < 2 * beta * theta - (1 + epsilon + theta) := by
    simp only [epsilon]
    linarith
  have hgrow : ∀ᶠ T : ℝ in atTop,
      C < T ^ (2 * beta * theta - (1 + epsilon + theta)) :=
    (tendsto_rpow_atTop hexponent).eventually (eventually_gt_atTop C)
  have hpos : ∀ᶠ T : ℝ in atTop, 0 < T := eventually_gt_atTop 0
  obtain ⟨T, hTbound, hTgrow, hTpos⟩ := (hbound.and (hgrow.and hpos)).exists
  have hden : 0 < T ^ (1 + epsilon + theta) := Real.rpow_pos_of_pos hTpos _
  have hquot : T ^ (2 * beta * theta - (1 + epsilon + theta)) ≤ C := by
    rw [Real.rpow_sub hTpos]
    exact (div_le_iff₀ hden).2 (by simpa [mul_comm] using hTbound)
  linarith

theorem nontrivialZero_re_le_of_bettinGonekPowerObstruction {theta : ℝ}
    (htheta : 0 < theta)
    (hpower : ∀ rho : ℂ, IsNontrivialZero rho →
      BettinGonekPowerObstruction theta rho.re)
    {rho : ℂ} (hrho : IsNontrivialZero rho) :
    rho.re ≤ 1 / 2 + 1 / (2 * theta) :=
  beta_le_of_bettinGonekPowerObstruction htheta (hpower rho hrho)

theorem riemannZeta_ne_zero_of_bettinGonekPowerObstructions {theta : ℝ}
    (htheta : 0 < theta)
    (hpower : ∀ rho : ℂ, IsNontrivialZero rho →
      BettinGonekPowerObstruction theta rho.re)
    {s : ℂ} (hs : 1 / 2 + 1 / (2 * theta) < s.re) :
    riemannZeta s ≠ 0 := by
  intro hz
  have hboundary : 1 / 2 < 1 / 2 + 1 / (2 * theta) := by
    have : 0 < 1 / (2 * theta) := by positivity
    linarith
  have htrivial : ¬ IsTrivialZeroPoint s := by
    rintro ⟨n, rfl⟩
    have hneg := trivial_zero_re_lt_zero n
    linarith
  have hone : s ≠ 1 := by
    intro hsone
    subst s
    exact riemannZeta_ne_zero_of_one_le_re (s := (1 : ℂ)) (by norm_num) hz
  have hnontrivial : IsNontrivialZero s := ⟨hz, htrivial, hone⟩
  have hle := nontrivialZero_re_le_of_bettinGonekPowerObstruction
    htheta hpower hnontrivial
  linarith

theorem riemannZeta_ne_zero_of_farmerLongMollifierBound {theta : ℝ}
    (htheta : 0 < theta) (hmoment : FarmerLongMollifierBound theta)
    (hbridge : BettinGonekMomentToPowerBridge theta)
    {s : ℂ} (hs : 1 / 2 + 1 / (2 * theta) < s.re) :
    riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_bettinGonekPowerObstructions htheta
    (hbridge hmoment) hs

theorem riemannHypothesis_of_all_bettinGonekPowerObstructions
    (hpower : ∀ theta : ℝ, 0 < theta → ∀ rho : ℂ, IsNontrivialZero rho →
      BettinGonekPowerObstruction theta rho.re) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_nontrivial_zeros_on_line]
  intro rho hrho
  have upper_of_all : ∀ z : ℂ, IsNontrivialZero z → z.re ≤ 1 / 2 := by
    intro z hz
    by_contra hzupper
    have hdelta : 0 < z.re - 1 / 2 := sub_pos.mpr (not_le.mp hzupper)
    let theta := (z.re - 1 / 2)⁻¹
    have htheta : 0 < theta := inv_pos.mpr hdelta
    have hle := nontrivialZero_re_le_of_bettinGonekPowerObstruction htheta
      (hpower theta htheta) hz
    have hdelta_ne : z.re - 1 / 2 ≠ 0 := hdelta.ne'
    have hboundary : 1 / (2 * theta) = (z.re - 1 / 2) / 2 := by
      dsimp only [theta]
      field_simp [hdelta_ne]
    rw [hboundary] at hle
    have : (1 / 2 : ℝ) + (z.re - 1 / 2) / 2 < z.re := by linarith
    exact (not_lt_of_ge hle) this
  have hupper := upper_of_all rho hrho
  have hreflect := upper_of_all (1 - rho) (isNontrivialZero_one_sub hrho)
  rw [OnCriticalLine]
  simp only [Complex.sub_re, Complex.one_re] at hreflect
  linarith

theorem farmerThetaInfinityConjecture_implies_riemannHypothesis
    (hmoment : FarmerThetaInfinityConjecture)
    (hbridge : ∀ theta : ℝ, 0 < theta → BettinGonekMomentToPowerBridge theta) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_all_bettinGonekPowerObstructions
  intro theta htheta rho hrho
  exact hbridge theta htheta (hmoment theta htheta) rho hrho

/-- A fixed positive `theta` leaves a nonempty interval to the right of the critical line. -/
def bettinGonekFixedThetaWitness (theta : ℝ) : ℝ :=
  1 / 2 + 1 / (4 * theta)

theorem bettinGonekFixedThetaWitness_off_line {theta : ℝ} (htheta : 0 < theta) :
    1 / 2 < bettinGonekFixedThetaWitness theta := by
  rw [bettinGonekFixedThetaWitness]
  have : 0 < 1 / (4 * theta) := by positivity
  linarith

theorem bettinGonekFixedThetaWitness_below_boundary {theta : ℝ} (htheta : 0 < theta) :
    bettinGonekFixedThetaWitness theta < 1 / 2 + 1 / (2 * theta) := by
  rw [bettinGonekFixedThetaWitness]
  have hden : 0 < 4 * theta := by positivity
  have hden2 : 0 < 2 * theta := by positivity
  have hlt : 2 * theta < 4 * theta := by nlinarith
  have hinv := one_div_lt_one_div_of_lt hden2 hlt
  linarith

end

end LeanLab.Riemann
