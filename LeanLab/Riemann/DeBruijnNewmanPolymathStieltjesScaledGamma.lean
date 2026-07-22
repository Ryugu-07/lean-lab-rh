import LeanLab.Riemann.DeBruijnNewmanPolymathBoydBoundaryTraceNearZero
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Stieltjes representation and second-order bounds for the scaled Gamma function

This module reconstructs Stieltjes's periodic-kernel representation from the Gamma limit formula
and uses its zero-mean primitive to obtain the complex second-order Stirling bounds needed by the
Boyd boundary-dispersion limits.
-/

namespace LeanLab.Riemann

open Asymptotics Complex Filter MeasureTheory Real Set
open scoped Interval Real Topology

noncomputable section

/-- Stieltjes's periodic quadratic kernel `Q(t) = ({t} - {t}^2) / 2`. -/
def deBruijnNewmanPolymathStieltjesQ (t : ℝ) : ℝ :=
  (1 / 2) * (Int.fract t - Int.fract t ^ 2)

/-- The polynomial representative of Stieltjes's kernel on one unit interval. -/
def deBruijnNewmanPolymathStieltjesQUnit (u : ℝ) : ℝ :=
  (1 / 2) * (u - u ^ 2)

/-- A zero-endpoint primitive of `QUnit - 1/12`. -/
def deBruijnNewmanPolymathStieltjesCenteredPrimitive (u : ℝ) : ℝ :=
  (1 / 4) * u ^ 2 - (1 / 6) * u ^ 3 - (1 / 12) * u

theorem deBruijnNewmanPolymathStieltjesQ_eq_unit
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    deBruijnNewmanPolymathStieltjesQ u =
      deBruijnNewmanPolymathStieltjesQUnit u := by
  rcases hu with ⟨hu0, hu1⟩
  rcases hu1.eq_or_lt with rfl | hu1
  · simp [deBruijnNewmanPolymathStieltjesQ,
      deBruijnNewmanPolymathStieltjesQUnit]
  · rw [deBruijnNewmanPolymathStieltjesQ,
      Int.fract_eq_self.mpr ⟨hu0, hu1⟩]
    rfl

theorem deBruijnNewmanPolymathStieltjesQ_add_nat
    (t : ℝ) (n : ℕ) :
    deBruijnNewmanPolymathStieltjesQ (t + n) =
      deBruijnNewmanPolymathStieltjesQ t := by
  simp [deBruijnNewmanPolymathStieltjesQ, Int.fract_add_natCast]

theorem deBruijnNewmanPolymathStieltjesQ_nonneg (t : ℝ) :
    0 ≤ deBruijnNewmanPolymathStieltjesQ t := by
  have h0 := Int.fract_nonneg t
  have h1 := (Int.fract_lt_one t).le
  rw [deBruijnNewmanPolymathStieltjesQ]
  nlinarith [mul_nonneg h0 (sub_nonneg.mpr h1)]

theorem deBruijnNewmanPolymathStieltjesQ_le_one_eighth (t : ℝ) :
    deBruijnNewmanPolymathStieltjesQ t ≤ 1 / 8 := by
  have hsq : 0 ≤ (2 * Int.fract t - 1) ^ 2 := sq_nonneg _
  rw [deBruijnNewmanPolymathStieltjesQ]
  nlinarith

theorem deBruijnNewmanPolymathStieltjesCenteredPrimitive_zero :
    deBruijnNewmanPolymathStieltjesCenteredPrimitive 0 = 0 := by
  norm_num [deBruijnNewmanPolymathStieltjesCenteredPrimitive]

theorem deBruijnNewmanPolymathStieltjesCenteredPrimitive_one :
    deBruijnNewmanPolymathStieltjesCenteredPrimitive 1 = 0 := by
  norm_num [deBruijnNewmanPolymathStieltjesCenteredPrimitive]

theorem abs_deBruijnNewmanPolymathStieltjesCenteredPrimitive_le_half
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    |deBruijnNewmanPolymathStieltjesCenteredPrimitive u| ≤ 1 / 2 := by
  rcases hu with ⟨hu0, hu1⟩
  rw [abs_le]
  constructor <;>
    rw [deBruijnNewmanPolymathStieltjesCenteredPrimitive] <;>
    nlinarith [sq_nonneg u, mul_nonneg (sq_nonneg u) hu0,
      mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hu1)]

theorem integral_deBruijnNewmanPolymathStieltjesQUnit :
    (∫ u : ℝ in (0 : ℝ)..1,
      deBruijnNewmanPolymathStieltjesQUnit u) = 1 / 12 := by
  change (∫ u : ℝ in (0 : ℝ)..1, (1 / 2) * (u - u ^ 2)) = 1 / 12
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub]
  · norm_num
  · exact continuous_id.intervalIntegrable _ _
  · exact (continuous_id.pow 2).intervalIntegrable _ _

theorem integral_deBruijnNewmanPolymathStieltjesQ_unit :
    (∫ u : ℝ in (0 : ℝ)..1,
      deBruijnNewmanPolymathStieltjesQ u) = 1 / 12 := by
  rw [← integral_deBruijnNewmanPolymathStieltjesQUnit]
  apply intervalIntegral.integral_congr
  intro u hu
  apply deBruijnNewmanPolymathStieltjesQ_eq_unit
  simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hu

/-- The complex polynomial representative of `Q` on one unit interval. -/
def deBruijnNewmanPolymathStieltjesQUnitComplex (u : ℝ) : ℂ :=
  ((u : ℂ) - (u : ℂ) ^ 2) * (1 / 2)

/-- The affine denominator on the `n`-th Stieltjes unit block. -/
def deBruijnNewmanPolymathStieltjesBlockPoint
    (z : ℂ) (n : ℕ) (u : ℝ) : ℂ :=
  z + (n : ℂ) + (u : ℂ)

/-- An explicit antiderivative of the `n`-th Stieltjes unit-block integrand. -/
def deBruijnNewmanPolymathStieltjesBlockAntiderivative
    (z : ℂ) (n : ℕ) (u : ℝ) : ℂ :=
  -deBruijnNewmanPolymathStieltjesQUnitComplex u /
      deBruijnNewmanPolymathStieltjesBlockPoint z n u +
    (z + n + 1 / 2) *
      Complex.log (deBruijnNewmanPolymathStieltjesBlockPoint z n u) - u

theorem deBruijnNewmanPolymathStieltjesBlockPoint_re_pos
    {z : ℂ} (hz : 0 < z.re) (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    0 < (deBruijnNewmanPolymathStieltjesBlockPoint z n u).re := by
  rw [deBruijnNewmanPolymathStieltjesBlockPoint]
  simp only [add_re, natCast_re, ofReal_re]
  positivity

theorem hasDerivAt_deBruijnNewmanPolymathStieltjesBlockAntiderivative
    {z : ℂ} (hz : 0 < z.re) (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt (deBruijnNewmanPolymathStieltjesBlockAntiderivative z n)
      (deBruijnNewmanPolymathStieltjesQUnitComplex u /
        deBruijnNewmanPolymathStieltjesBlockPoint z n u ^ 2) u := by
  have huC : HasDerivAt (fun v : ℝ => (v : ℂ)) 1 u :=
    (hasDerivAt_id u).ofReal_comp
  have hpoint : HasDerivAt
      (deBruijnNewmanPolymathStieltjesBlockPoint z n) 1 u := by
    change HasDerivAt (fun v : ℝ => z + (n : ℂ) + (v : ℂ)) 1 u
    simpa only [add_assoc] using huC.const_add (z + n)
  have hpoint0 : deBruijnNewmanPolymathStieltjesBlockPoint z n u ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.zero_re] at hre
    linarith [deBruijnNewmanPolymathStieltjesBlockPoint_re_pos hz n hu]
  have hslit : deBruijnNewmanPolymathStieltjesBlockPoint z n u ∈
      Complex.slitPlane :=
    Or.inl (deBruijnNewmanPolymathStieltjesBlockPoint_re_pos hz n hu)
  have hq := (huC.sub (huC.pow 2)).mul_const (1 / 2 : ℂ)
  have hquot := hq.neg.div hpoint hpoint0
  have hlog := hpoint.clog_real hslit
  have hmain := hlog.const_mul (z + n + 1 / 2)
  have hraw := (hquot.add hmain).sub huC
  refine (hraw.congr_deriv ?_).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun v => ?_)
  · unfold deBruijnNewmanPolymathStieltjesQUnitComplex
      deBruijnNewmanPolymathStieltjesBlockPoint at hpoint0 ⊢
    field_simp [hpoint0]
    simp only [Pi.sub_apply, Pi.pow_apply, Pi.neg_apply]
    ring
  · simp [deBruijnNewmanPolymathStieltjesBlockAntiderivative,
      deBruijnNewmanPolymathStieltjesQUnitComplex,
      deBruijnNewmanPolymathStieltjesBlockPoint, div_eq_mul_inv]

/-- The `n`-th unit block in Stieltjes's logarithmic remainder. -/
def deBruijnNewmanPolymathStieltjesBlock (z : ℂ) (n : ℕ) : ℂ :=
  ∫ u : ℝ in (0 : ℝ)..1,
    deBruijnNewmanPolymathStieltjesQUnitComplex u /
      deBruijnNewmanPolymathStieltjesBlockPoint z n u ^ 2

theorem deBruijnNewmanPolymathStieltjesBlock_eq
    {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    deBruijnNewmanPolymathStieltjesBlock z n =
      (z + n + 1 / 2) * (Complex.log (z + n + 1) - Complex.log (z + n)) - 1 := by
  rw [deBruijnNewmanPolymathStieltjesBlock]
  have hint : IntervalIntegrable
      (fun u : ℝ => deBruijnNewmanPolymathStieltjesQUnitComplex u /
        deBruijnNewmanPolymathStieltjesBlockPoint z n u ^ 2)
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    intro u hu
    have hu' : u ∈ Icc (0 : ℝ) 1 := by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hu
    have hpoint0 : deBruijnNewmanPolymathStieltjesBlockPoint z n u ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp only [Complex.zero_re] at hre
      linarith [deBruijnNewmanPolymathStieltjesBlockPoint_re_pos hz n hu'.1]
    have hnum : ContinuousAt deBruijnNewmanPolymathStieltjesQUnitComplex u := by
      unfold deBruijnNewmanPolymathStieltjesQUnitComplex
      fun_prop
    have hden : ContinuousAt
        (fun v : ℝ => deBruijnNewmanPolymathStieltjesBlockPoint z n v ^ 2) u := by
      unfold deBruijnNewmanPolymathStieltjesBlockPoint
      fun_prop
    exact (hnum.div hden (pow_ne_zero 2 hpoint0)).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => hasDerivAt_deBruijnNewmanPolymathStieltjesBlockAntiderivative
      hz n (by
        rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
        exact hu.1)) hint]
  simp [deBruijnNewmanPolymathStieltjesBlockAntiderivative,
    deBruijnNewmanPolymathStieltjesQUnitComplex,
    deBruijnNewmanPolymathStieltjesBlockPoint]
  ring

/-- The first `N` unit blocks of the Stieltjes logarithmic remainder. -/
def deBruijnNewmanPolymathStieltjesPartial (z : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, deBruijnNewmanPolymathStieltjesBlock z n

theorem deBruijnNewmanPolymathStieltjesPartial_eq
    {z : ℂ} (hz : 0 < z.re) (N : ℕ) :
    deBruijnNewmanPolymathStieltjesPartial z N =
      (z + N - 1 / 2) * Complex.log (z + N) -
        (z - 1 / 2) * Complex.log z -
        (∑ n ∈ Finset.range N, Complex.log (z + n)) - N := by
  induction N with
  | zero => simp [deBruijnNewmanPolymathStieltjesPartial]
  | succ N ih =>
      rw [deBruijnNewmanPolymathStieltjesPartial] at ih ⊢
      rw [Finset.sum_range_succ, Finset.sum_range_succ,
        deBruijnNewmanPolymathStieltjesBlock_eq hz, ih]
      push_cast
      ring

/-- Stieltjes's logarithmic-remainder integrand on the positive real ray. -/
def deBruijnNewmanPolymathStieltjesIntegrand (z : ℂ) (t : ℝ) : ℂ :=
  (deBruijnNewmanPolymathStieltjesQ t : ℂ) /
    (z + (t : ℂ)) ^ 2

/-- The absolutely convergent Stieltjes logarithmic remainder on the right half-plane. -/
def deBruijnNewmanPolymathStieltjesLogRemainder (z : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi (0 : ℝ), deBruijnNewmanPolymathStieltjesIntegrand z t

theorem norm_deBruijnNewmanPolymathStieltjesIntegrand_le
    {z : ℂ} (hz : 0 < z.re) {t : ℝ} (ht : 0 ≤ t) :
    ‖deBruijnNewmanPolymathStieltjesIntegrand z t‖ ≤
      (1 / 8) * (t + z.re) ^ (-2 : ℝ) := by
  have hbase : 0 < t + z.re := by linarith
  have hpointRe : 0 < (z + (t : ℂ)).re := by
    simp only [add_re, ofReal_re]
    linarith
  have hpointNorm : t + z.re ≤ ‖z + (t : ℂ)‖ := by
    calc
      t + z.re = |(z + (t : ℂ)).re| := by
        rw [abs_of_pos hpointRe]
        simp only [add_re, ofReal_re]
        ring
      _ ≤ ‖z + (t : ℂ)‖ := Complex.abs_re_le_norm _
  have hsq : (t + z.re) ^ 2 ≤ ‖z + (t : ℂ)‖ ^ 2 := by
    exact pow_le_pow_left₀ hbase.le hpointNorm 2
  have hnormPos : 0 < ‖z + (t : ℂ)‖ := hbase.trans_le hpointNorm
  have hinv : (‖z + (t : ℂ)‖ ^ 2)⁻¹ ≤ ((t + z.re) ^ 2)⁻¹ := by
    exact (inv_le_inv₀ (sq_pos_of_pos hnormPos) (sq_pos_of_pos hbase)).2 hsq
  have hQ0 := deBruijnNewmanPolymathStieltjesQ_nonneg t
  have hQ8 := deBruijnNewmanPolymathStieltjesQ_le_one_eighth t
  rw [deBruijnNewmanPolymathStieltjesIntegrand, norm_div, norm_pow,
    norm_real, Real.norm_of_nonneg hQ0, div_eq_mul_inv]
  calc
    deBruijnNewmanPolymathStieltjesQ t * (‖z + (t : ℂ)‖ ^ 2)⁻¹ ≤
        (1 / 8) * (‖z + (t : ℂ)‖ ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_right hQ8 (inv_nonneg.mpr (sq_nonneg _))
    _ ≤ (1 / 8) * ((t + z.re) ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_left hinv (by norm_num)
    _ = (1 / 8) * (t + z.re) ^ (-2 : ℝ) := by
      congr 1
      rw [Real.rpow_neg hbase.le]
      norm_num [Real.rpow_natCast]

theorem deBruijnNewmanPolymathStieltjesIntegrand_integrableOn
    {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (deBruijnNewmanPolymathStieltjesIntegrand z) (Ioi (0 : ℝ)) := by
  have hmajor : IntegrableOn
      (fun t : ℝ => (1 / 8) * (t + z.re) ^ (-2 : ℝ)) (Ioi (0 : ℝ)) :=
    (integrableOn_add_rpow_Ioi_of_lt (a := (-2 : ℝ)) (c := 0) (m := z.re)
      (by norm_num) (neg_lt_zero.mpr hz)).const_mul (1 / 8)
  apply hmajor.mono'
  · apply Measurable.aestronglyMeasurable
    unfold deBruijnNewmanPolymathStieltjesIntegrand
      deBruijnNewmanPolymathStieltjesQ
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact norm_deBruijnNewmanPolymathStieltjesIntegrand_le hz ht.le

theorem integral_deBruijnNewmanPolymathStieltjesIntegrand_unitBlock
    (z : ℂ) (n : ℕ) :
    (∫ t : ℝ in (n : ℝ)..(n + 1 : ℕ),
        deBruijnNewmanPolymathStieltjesIntegrand z t) =
      deBruijnNewmanPolymathStieltjesBlock z n := by
  calc
    (∫ t : ℝ in (n : ℝ)..(n + 1 : ℕ),
        deBruijnNewmanPolymathStieltjesIntegrand z t) =
        ∫ u : ℝ in (0 : ℝ)..1,
          deBruijnNewmanPolymathStieltjesIntegrand z (u + n) := by
      symm
      simpa only [zero_add, Nat.cast_add, Nat.cast_one,
        add_comm (1 : ℝ) (n : ℝ)] using
        (intervalIntegral.integral_comp_add_right
          (f := deBruijnNewmanPolymathStieltjesIntegrand z)
          (a := (0 : ℝ)) (b := 1) (d := (n : ℝ)))
    _ = deBruijnNewmanPolymathStieltjesBlock z n := by
      rw [deBruijnNewmanPolymathStieltjesBlock]
      apply intervalIntegral.integral_congr
      intro u hu
      have hu' : u ∈ Icc (0 : ℝ) 1 := by
        simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hu
      change
        (deBruijnNewmanPolymathStieltjesQ (u + (n : ℝ)) : ℂ) /
            (z + ((u + (n : ℝ) : ℝ) : ℂ)) ^ 2 =
          deBruijnNewmanPolymathStieltjesQUnitComplex u /
            deBruijnNewmanPolymathStieltjesBlockPoint z n u ^ 2
      rw [deBruijnNewmanPolymathStieltjesQ_add_nat,
        deBruijnNewmanPolymathStieltjesQ_eq_unit hu']
      unfold deBruijnNewmanPolymathStieltjesQUnit
        deBruijnNewmanPolymathStieltjesQUnitComplex
        deBruijnNewmanPolymathStieltjesBlockPoint
      push_cast
      ring

theorem integral_deBruijnNewmanPolymathStieltjesIntegrand_zero_nat
    {z : ℂ} (hz : 0 < z.re) (N : ℕ) :
    (∫ t : ℝ in (0 : ℝ)..N,
        deBruijnNewmanPolymathStieltjesIntegrand z t) =
      deBruijnNewmanPolymathStieltjesPartial z N := by
  have hint : ∀ n < N, IntervalIntegrable
      (deBruijnNewmanPolymathStieltjesIntegrand z) volume
      (n : ℝ) (n + 1 : ℕ) := by
    intro n hn
    have hnn : (n : ℝ) ≤ (n + 1 : ℕ) := by
      exact_mod_cast Nat.le_succ n
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hnn]
    apply (deBruijnNewmanPolymathStieltjesIntegrand_integrableOn hz).mono_set
    intro t ht
    exact lt_of_le_of_lt (Nat.cast_nonneg n) ht.1
  calc
    (∫ t : ℝ in (0 : ℝ)..N,
        deBruijnNewmanPolymathStieltjesIntegrand z t) =
        ∑ n ∈ Finset.range N,
          ∫ t : ℝ in (n : ℝ)..(n + 1 : ℕ),
            deBruijnNewmanPolymathStieltjesIntegrand z t := by
      symm
      simpa only [Nat.cast_zero] using
        (intervalIntegral.sum_integral_adjacent_intervals
          (f := deBruijnNewmanPolymathStieltjesIntegrand z)
          (a := fun n : ℕ => (n : ℝ)) hint)
    _ = deBruijnNewmanPolymathStieltjesPartial z N := by
      rw [deBruijnNewmanPolymathStieltjesPartial]
      apply Finset.sum_congr rfl
      intro n hn
      exact integral_deBruijnNewmanPolymathStieltjesIntegrand_unitBlock z n

theorem tendsto_deBruijnNewmanPolymathStieltjesPartial
    {z : ℂ} (hz : 0 < z.re) :
    Tendsto (deBruijnNewmanPolymathStieltjesPartial z) atTop
      (𝓝 (deBruijnNewmanPolymathStieltjesLogRemainder z)) := by
  have h := intervalIntegral_tendsto_integral_Ioi (l := atTop)
    (f := deBruijnNewmanPolymathStieltjesIntegrand z) 0
    (deBruijnNewmanPolymathStieltjesIntegrand_integrableOn hz)
    tendsto_natCast_atTop_atTop
  simpa only [deBruijnNewmanPolymathStieltjesLogRemainder] using
    h.congr' (Filter.Eventually.of_forall fun N =>
      integral_deBruijnNewmanPolymathStieltjesIntegrand_zero_nat hz N)

/-- The factorial-only correction in the positive-real finite reconstruction. -/
def deBruijnNewmanPolymathStieltjesFactorialCorrection (N : ℕ) : ℝ :=
  (N + 1 / 2) * Real.log N - Real.log (Nat.factorial N) - N

/-- The shifted-log correction in the positive-real finite reconstruction. -/
def deBruijnNewmanPolymathStieltjesShiftCorrection (x : ℝ) (N : ℕ) : ℝ :=
  (x + N + 1 / 2) * Real.log (1 + x / N)

theorem deBruijnNewmanPolymathStieltjesPartial_ofReal_eq
    {x : ℝ} (hx : 0 < x) {N : ℕ} (hN : N ≠ 0) :
    deBruijnNewmanPolymathStieltjesPartial (x : ℂ) N =
      ((Real.BohrMollerup.logGammaSeq x N -
          (x - 1 / 2) * Real.log x +
          deBruijnNewmanPolymathStieltjesFactorialCorrection N +
          deBruijnNewmanPolymathStieltjesShiftCorrection x N : ℝ) : ℂ) := by
  rw [deBruijnNewmanPolymathStieltjesPartial_eq (by simpa using hx)]
  have hlogAdd (n : ℕ) :
      Complex.log ((x : ℂ) + n) = (Real.log (x + n) : ℂ) := by
    calc
      Complex.log ((x : ℂ) + n) =
          Complex.log ((x + (n : ℝ) : ℝ) : ℂ) := by
        congr 1
        push_cast
        rfl
      _ = (Real.log (x + n) : ℂ) :=
        (Complex.ofReal_log (by positivity : 0 ≤ x + (n : ℝ))).symm
  have hlogX : Complex.log (x : ℂ) = (Real.log x : ℂ) :=
    (Complex.ofReal_log hx.le).symm
  simp_rw [hlogAdd]
  rw [hlogX]
  push_cast
  norm_cast
  rw [deBruijnNewmanPolymathStieltjesFactorialCorrection,
    deBruijnNewmanPolymathStieltjesShiftCorrection,
    Real.BohrMollerup.logGammaSeq, Finset.sum_range_succ]
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hone : 0 < 1 + x / (N : ℝ) := by positivity
  have hsplit : Real.log (x + N) =
      Real.log N + Real.log (1 + x / N) := by
    rw [show x + (N : ℝ) = (N : ℝ) * (1 + x / N) by
      field_simp
      ring]
    exact Real.log_mul hNpos.ne' hone.ne'
  rw [hsplit]
  push_cast
  ring

theorem deBruijnNewmanPolymathStieltjesFactorialCorrection_eq
    {N : ℕ} (hN : N ≠ 0) :
    deBruijnNewmanPolymathStieltjesFactorialCorrection N =
      -Real.log (Stirling.stirlingSeq N) - (1 / 2) * Real.log 2 := by
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  rw [deBruijnNewmanPolymathStieltjesFactorialCorrection,
    Stirling.log_stirlingSeq_formula,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hNpos.ne',
    Real.log_div hNpos.ne' (Real.exp_ne_zero 1), Real.log_exp]
  ring

theorem tendsto_deBruijnNewmanPolymathStieltjesFactorialCorrection :
    Tendsto deBruijnNewmanPolymathStieltjesFactorialCorrection atTop
      (𝓝 (-(1 / 2) * Real.log (2 * Real.pi))) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (Stirling.stirlingSeq N)) atTop
      (𝓝 (Real.log (Real.sqrt Real.pi))) :=
    (Real.continuousAt_log (by positivity : Real.sqrt Real.pi ≠ 0)).tendsto.comp
      Stirling.tendsto_stirlingSeq_sqrt_pi
  have hraw : Tendsto
      (fun N : ℕ => -Real.log (Stirling.stirlingSeq N) - (1 / 2) * Real.log 2)
      atTop
      (𝓝 (-Real.log (Real.sqrt Real.pi) - (1 / 2) * Real.log 2)) :=
    hlog.neg.sub tendsto_const_nhds
  have hcorr : Tendsto deBruijnNewmanPolymathStieltjesFactorialCorrection atTop
      (𝓝 (-Real.log (Real.sqrt Real.pi) - (1 / 2) * Real.log 2)) :=
    hraw.congr' (by
      filter_upwards [eventually_ne_atTop 0] with N hN
      exact (deBruijnNewmanPolymathStieltjesFactorialCorrection_eq hN).symm)
  convert hcorr using 1
  rw [Real.log_sqrt Real.pi_pos.le,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero]
  ring

theorem tendsto_deBruijnNewmanPolymathStieltjesShiftCorrection (x : ℝ) :
    Tendsto (deBruijnNewmanPolymathStieltjesShiftCorrection x) atTop (𝓝 x) := by
  have hmain : Tendsto
      (fun N : ℕ => (N : ℝ) * Real.log (1 + x / N)) atTop (𝓝 x) :=
    (Real.tendsto_mul_log_one_add_div_atTop x).comp tendsto_natCast_atTop_atTop
  have hdiv : Tendsto (fun N : ℕ => x / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun N : ℕ => Real.log (1 + x / N)) atTop (𝓝 0) := by
    have hadd : Tendsto (fun N : ℕ => 1 + x / (N : ℝ)) atTop (𝓝 1) := by
      convert tendsto_const_nhds.add hdiv using 1 <;> norm_num
    simpa only [Function.comp_def, Real.log_one] using
      (Real.continuousAt_log one_ne_zero).tendsto.comp hadd
  have hsmall : Tendsto
      (fun N : ℕ => (x + 1 / 2) * Real.log (1 + x / N)) atTop (𝓝 0) := by
    convert tendsto_const_nhds.mul hlog using 1 <;> ring
  have hsum := hmain.add hsmall
  have hshift := hsum.congr' (Filter.Eventually.of_forall fun N => by
    show (N : ℝ) * Real.log (1 + x / N) +
        (x + 1 / 2) * Real.log (1 + x / N) =
      deBruijnNewmanPolymathStieltjesShiftCorrection x N
    rw [deBruijnNewmanPolymathStieltjesShiftCorrection]
    push_cast
    ring)
  simpa only [add_zero] using hshift

/-- The positive-real logarithm selected by the finite Gamma/Stirling reconstruction. -/
def deBruijnNewmanPolymathStieltjesPositiveLogValue (x : ℝ) : ℝ :=
  Real.log (Real.Gamma x) - (x - 1 / 2) * Real.log x + x -
    (1 / 2) * Real.log (2 * Real.pi)

theorem tendsto_deBruijnNewmanPolymathStieltjesPartial_ofReal
    {x : ℝ} (hx : 0 < x) :
    Tendsto (deBruijnNewmanPolymathStieltjesPartial (x : ℂ)) atTop
      (𝓝 ((deBruijnNewmanPolymathStieltjesPositiveLogValue x : ℝ) : ℂ)) := by
  have hreal : Tendsto
      (fun N : ℕ => Real.BohrMollerup.logGammaSeq x N -
        (x - 1 / 2) * Real.log x +
        deBruijnNewmanPolymathStieltjesFactorialCorrection N +
        deBruijnNewmanPolymathStieltjesShiftCorrection x N)
      atTop (𝓝 (deBruijnNewmanPolymathStieltjesPositiveLogValue x)) := by
    have hfixed : Tendsto
        (fun _ : ℕ => (x - 1 / 2) * Real.log x) atTop
        (𝓝 ((x - 1 / 2) * Real.log x)) := tendsto_const_nhds
    have h := (((Real.BohrMollerup.tendsto_log_gamma hx).sub hfixed).add
        tendsto_deBruijnNewmanPolymathStieltjesFactorialCorrection).add
        (tendsto_deBruijnNewmanPolymathStieltjesShiftCorrection x)
    unfold deBruijnNewmanPolymathStieltjesPositiveLogValue
    convert h using 1 <;> ring
  have hcomplex : Tendsto
      (fun N : ℕ => ((Real.BohrMollerup.logGammaSeq x N -
        (x - 1 / 2) * Real.log x +
        deBruijnNewmanPolymathStieltjesFactorialCorrection N +
        deBruijnNewmanPolymathStieltjesShiftCorrection x N : ℝ) : ℂ))
      atTop (𝓝 ((deBruijnNewmanPolymathStieltjesPositiveLogValue x : ℝ) : ℂ)) := by
    simpa only [Function.comp_def] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  apply hcomplex.congr'
  filter_upwards [eventually_ne_atTop 0] with N hN
  exact (deBruijnNewmanPolymathStieltjesPartial_ofReal_eq hx hN).symm

theorem deBruijnNewmanPolymathStieltjesLogRemainder_ofReal_eq
    {x : ℝ} (hx : 0 < x) :
    deBruijnNewmanPolymathStieltjesLogRemainder (x : ℂ) =
      ((deBruijnNewmanPolymathStieltjesPositiveLogValue x : ℝ) : ℂ) := by
  exact tendsto_nhds_unique
    (tendsto_deBruijnNewmanPolymathStieltjesPartial (by simpa using hx))
    (tendsto_deBruijnNewmanPolymathStieltjesPartial_ofReal hx)

theorem exp_deBruijnNewmanPolymathStieltjesPositiveLogValue
    {x : ℝ} (hx : 0 < x) :
    Real.exp (deBruijnNewmanPolymathStieltjesPositiveLogValue x) =
      Real.Gamma x /
        (Real.sqrt (2 * Real.pi) *
          Real.exp ((x - 1 / 2) * Real.log x - x)) := by
  have hGamma : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  have hsqrt : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hhalf : (1 / 2) * Real.log (2 * Real.pi) =
      Real.log (Real.sqrt (2 * Real.pi)) := by
    rw [Real.log_sqrt (by positivity : 0 ≤ 2 * Real.pi)]
    ring
  rw [deBruijnNewmanPolymathStieltjesPositiveLogValue, hhalf]
  rw [show Real.log (Real.Gamma x) - (x - 1 / 2) * Real.log x + x -
      Real.log (Real.sqrt (2 * Real.pi)) =
      Real.log (Real.Gamma x) -
        (Real.log (Real.sqrt (2 * Real.pi)) +
          ((x - 1 / 2) * Real.log x - x)) by ring]
  rw [Real.exp_sub, Real.exp_log hGamma, Real.exp_add, Real.exp_log hsqrt]

theorem exp_deBruijnNewmanPolymathStieltjesPositiveLogValue_complex
    {x : ℝ} (hx : 0 < x) :
    Complex.exp ((deBruijnNewmanPolymathStieltjesPositiveLogValue x : ℝ) : ℂ) =
      deBruijnNewmanPolymathScaledGamma (x : ℂ) := by
  rw [← Complex.ofReal_exp,
    exp_deBruijnNewmanPolymathStieltjesPositiveLogValue hx,
    deBruijnNewmanPolymathScaledGamma, Complex.Gamma_ofReal,
    deBruijnNewmanPolymathGammaStirlingMain_ofReal hx]
  push_cast
  rfl

theorem deBruijnNewmanPolymath_scaledGamma_ofReal_eq_exp_stieltjes
    {x : ℝ} (hx : 0 < x) :
    deBruijnNewmanPolymathScaledGamma (x : ℂ) =
      Complex.exp (deBruijnNewmanPolymathStieltjesLogRemainder (x : ℂ)) := by
  rw [deBruijnNewmanPolymathStieltjesLogRemainder_ofReal_eq hx]
  exact (exp_deBruijnNewmanPolymathStieltjesPositiveLogValue_complex hx).symm

/-- Parameter derivative of the Stieltjes logarithmic-remainder integrand. -/
def deBruijnNewmanPolymathStieltjesIntegrandDerivative (z : ℂ) (t : ℝ) : ℂ :=
  (-2 : ℂ) * (deBruijnNewmanPolymathStieltjesQ t : ℂ) /
    (z + (t : ℂ)) ^ 3

theorem hasDerivAt_deBruijnNewmanPolymathStieltjesIntegrand
    {z : ℂ} (hz : 0 < z.re) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun w : ℂ => deBruijnNewmanPolymathStieltjesIntegrand w t)
      (deBruijnNewmanPolymathStieltjesIntegrandDerivative z t) z := by
  have hden : z + (t : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hpoint := (hasDerivAt_id z).add_const (t : ℂ)
  have hraw := (hasDerivAt_const z
    (deBruijnNewmanPolymathStieltjesQ t : ℂ)).div (hpoint.pow 2)
      (pow_ne_zero 2 hden)
  unfold deBruijnNewmanPolymathStieltjesIntegrand
    deBruijnNewmanPolymathStieltjesIntegrandDerivative
  refine (hraw.congr_deriv ?_).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun w => ?_)
  · simp only [id_eq, Pi.pow_apply, Pi.add_apply, Pi.div_apply]
    field_simp [hden]
    ring
  · simp only [Pi.div_apply, Pi.pow_apply, id_eq]

private theorem deBruijnNewmanPolymathStieltjes_half_re_lt_re_of_mem_ball
    {z w : ℂ} (_hz : 0 < z.re) (hw : w ∈ Metric.ball z (z.re / 2)) :
    z.re / 2 < w.re := by
  have hdist : ‖w - z‖ < z.re / 2 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hw
  have hreAbs : |w.re - z.re| ≤ ‖w - z‖ := by
    simpa only [Complex.sub_re] using Complex.abs_re_le_norm (w - z)
  linarith [neg_abs_le (w.re - z.re)]

/-- Local integrable majorant for the parameter derivative of the Stieltjes kernel. -/
def deBruijnNewmanPolymathStieltjesDerivativeMajorant (z : ℂ) (t : ℝ) : ℝ :=
  (1 / 4) * (t + z.re / 2) ^ (-3 : ℝ)

theorem norm_deBruijnNewmanPolymathStieltjesIntegrandDerivative_le
    {z w : ℂ} (hz : 0 < z.re) (hw : w ∈ Metric.ball z (z.re / 2))
    {t : ℝ} (ht : 0 ≤ t) :
    ‖deBruijnNewmanPolymathStieltjesIntegrandDerivative w t‖ ≤
      deBruijnNewmanPolymathStieltjesDerivativeMajorant z t := by
  have hwre := deBruijnNewmanPolymathStieltjes_half_re_lt_re_of_mem_ball hz hw
  have hbase : 0 < t + z.re / 2 := by linarith
  have hpointRe : 0 < (w + (t : ℂ)).re := by
    simp only [add_re, ofReal_re]
    linarith
  have hpointNorm : t + z.re / 2 ≤ ‖w + (t : ℂ)‖ := by
    calc
      t + z.re / 2 ≤ t + w.re := by linarith
      _ = |(w + (t : ℂ)).re| := by
        rw [abs_of_pos hpointRe]
        simp only [add_re, ofReal_re]
        ring
      _ ≤ ‖w + (t : ℂ)‖ := Complex.abs_re_le_norm _
  have hpow : (t + z.re / 2) ^ 3 ≤ ‖w + (t : ℂ)‖ ^ 3 :=
    pow_le_pow_left₀ hbase.le hpointNorm 3
  have hnormPos : 0 < ‖w + (t : ℂ)‖ := hbase.trans_le hpointNorm
  have hinv : (‖w + (t : ℂ)‖ ^ 3)⁻¹ ≤ ((t + z.re / 2) ^ 3)⁻¹ :=
    (inv_le_inv₀ (pow_pos hnormPos 3) (pow_pos hbase 3)).2 hpow
  have hQ0 := deBruijnNewmanPolymathStieltjesQ_nonneg t
  have hQ8 := deBruijnNewmanPolymathStieltjesQ_le_one_eighth t
  rw [deBruijnNewmanPolymathStieltjesIntegrandDerivative,
    deBruijnNewmanPolymathStieltjesDerivativeMajorant,
    norm_div, norm_mul, norm_pow, norm_real, Real.norm_of_nonneg hQ0,
    div_eq_mul_inv]
  norm_num only [norm_neg, norm_ofNat]
  calc
    2 * deBruijnNewmanPolymathStieltjesQ t *
        (‖w + (t : ℂ)‖ ^ 3)⁻¹ ≤
        2 * (1 / 8) * (‖w + (t : ℂ)‖ ^ 3)⁻¹ := by
      gcongr
    _ ≤ 2 * (1 / 8) * ((t + z.re / 2) ^ 3)⁻¹ := by
      gcongr
    _ = (1 / 4) * (t + z.re / 2) ^ (-3 : ℝ) := by
      rw [Real.rpow_neg hbase.le]
      norm_num [Real.rpow_natCast]

theorem deBruijnNewmanPolymathStieltjesDerivativeMajorant_integrableOn
    {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (deBruijnNewmanPolymathStieltjesDerivativeMajorant z) (Ioi (0 : ℝ)) := by
  unfold deBruijnNewmanPolymathStieltjesDerivativeMajorant
  exact (integrableOn_add_rpow_Ioi_of_lt (a := (-3 : ℝ)) (c := 0)
    (m := z.re / 2) (by norm_num) (by linarith)).const_mul (1 / 4)

theorem deBruijnNewmanPolymathStieltjesLogRemainder_hasDerivAt
    {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt
      (fun w : ℂ => ∫ t : ℝ in Ioi 0,
        deBruijnNewmanPolymathStieltjesIntegrand w t)
      (∫ t : ℝ in Ioi 0,
        deBruijnNewmanPolymathStieltjesIntegrandDerivative z t) z := by
  let F : ℂ → ℝ → ℂ := deBruijnNewmanPolymathStieltjesIntegrand
  let F' : ℂ → ℝ → ℂ := deBruijnNewmanPolymathStieltjesIntegrandDerivative
  let bound : ℝ → ℝ := deBruijnNewmanPolymathStieltjesDerivativeMajorant z
  have hball : Metric.ball z (z.re / 2) ∈ 𝓝 z :=
    Metric.ball_mem_nhds z (by positivity)
  have hFmeas : ∀ᶠ w in 𝓝 z,
      AEStronglyMeasurable (F w) (volume.restrict (Ioi 0)) := by
    filter_upwards [hball] with w hw
    have hwre : 0 < w.re := lt_trans (by positivity)
      (deBruijnNewmanPolymathStieltjes_half_re_lt_re_of_mem_ball hz hw)
    exact (deBruijnNewmanPolymathStieltjesIntegrand_integrableOn hwre).aestronglyMeasurable
  have hFint : Integrable (F z) (volume.restrict (Ioi 0)) :=
    deBruijnNewmanPolymathStieltjesIntegrand_integrableOn hz
  have hF'meas : AEStronglyMeasurable (F' z) (volume.restrict (Ioi 0)) := by
    apply Measurable.aestronglyMeasurable
    unfold F' deBruijnNewmanPolymathStieltjesIntegrandDerivative
      deBruijnNewmanPolymathStieltjesQ
    fun_prop
  have hbound : ∀ᵐ t ∂volume.restrict (Ioi 0),
      ∀ w ∈ Metric.ball z (z.re / 2), ‖F' w t‖ ≤ bound t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht w hw
    exact norm_deBruijnNewmanPolymathStieltjesIntegrandDerivative_le hz hw ht.le
  have hdiff : ∀ᵐ t ∂volume.restrict (Ioi 0),
      ∀ w ∈ Metric.ball z (z.re / 2), HasDerivAt (F · t) (F' w t) w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht w hw
    have hwre : 0 < w.re := lt_trans (by positivity)
      (deBruijnNewmanPolymathStieltjes_half_re_lt_re_of_mem_ball hz hw)
    exact hasDerivAt_deBruijnNewmanPolymathStieltjesIntegrand hwre ht.le
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi 0)) (F := F) (F' := F') (bound := bound)
    (s := Metric.ball z (z.re / 2)) (x₀ := z) hball hFmeas hFint hF'meas hbound
    (deBruijnNewmanPolymathStieltjesDerivativeMajorant_integrableOn hz) hdiff
  simpa only [F, F'] using hmain.2

theorem deBruijnNewmanPolymathStieltjesLogRemainder_differentiableOn_rightHalfPlane :
    DifferentiableOn ℂ deBruijnNewmanPolymathStieltjesLogRemainder
      {z : ℂ | 0 < z.re} := by
  intro z hz
  exact (deBruijnNewmanPolymathStieltjesLogRemainder_hasDerivAt hz).differentiableAt
    |>.differentiableWithinAt

theorem deBruijnNewmanPolymath_exp_stieltjes_differentiableOn_rightHalfPlane :
    DifferentiableOn ℂ
      (fun z : ℂ => Complex.exp (deBruijnNewmanPolymathStieltjesLogRemainder z))
      {z : ℂ | 0 < z.re} := by
  intro z hz
  exact (deBruijnNewmanPolymathStieltjesLogRemainder_hasDerivAt hz).differentiableAt.cexp
    |>.differentiableWithinAt

theorem deBruijnNewmanPolymathScaledGamma_differentiableOn_rightHalfPlane :
    DifferentiableOn ℂ deBruijnNewmanPolymathScaledGamma {z : ℂ | 0 < z.re} := by
  intro z hz
  change 0 < z.re at hz
  apply DifferentiableAt.differentiableWithinAt
  have hnotpole : ∀ m : ℕ, z ≠ -m := by
    intro m hm
    have hre := congrArg Complex.re hm
    simp only [Complex.natCast_re, Complex.neg_re] at hre
    have hmNonneg : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith
  unfold deBruijnNewmanPolymathScaledGamma
  exact (Complex.differentiableAt_Gamma z hnotpole).div
    (deBruijnNewmanPolymathGammaStirlingMain_differentiableAt (Or.inl hz))
    (deBruijnNewmanPolymathGammaStirlingMain_ne_zero z)

/-- Stieltjes's representation for the project's actual scaled Gamma on the right half-plane. -/
theorem deBruijnNewmanPolymath_scaledGamma_eq_exp_stieltjes
    {z : ℂ} (hz : 0 < z.re) :
    deBruijnNewmanPolymathScaledGamma z =
      Complex.exp (deBruijnNewmanPolymathStieltjesLogRemainder z) := by
  let U : Set ℂ := {w : ℂ | 0 < w.re}
  have hopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hScaledAnalytic : AnalyticOnNhd ℂ deBruijnNewmanPolymathScaledGamma U :=
    (analyticOnNhd_iff_differentiableOn hopen).2
      deBruijnNewmanPolymathScaledGamma_differentiableOn_rightHalfPlane
  have hExpAnalytic : AnalyticOnNhd ℂ
      (fun w : ℂ => Complex.exp (deBruijnNewmanPolymathStieltjesLogRemainder w)) U :=
    (analyticOnNhd_iff_differentiableOn hopen).2
      deBruijnNewmanPolymath_exp_stieltjes_differentiableOn_rightHalfPlane
  have hpre : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have hone : (1 : ℂ) ∈ U := by simp [U]
  let x : ℕ → ℝ := fun n => 1 + 1 / ((n : ℝ) + 1)
  have hx : Tendsto x atTop (𝓝 1) := by
    dsimp only [x]
    simpa using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hxc : Tendsto (fun n => (x n : ℂ)) atTop (𝓝 (1 : ℂ)) := by
    change Tendsto (Complex.ofReal ∘ x) atTop (𝓝 (Complex.ofReal 1))
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp hx
  have hpunctured : ∀ᶠ n in atTop, (x n : ℂ) ∈ ({(1 : ℂ)} : Set ℂ)ᶜ :=
    Filter.Eventually.of_forall fun n => by
      have hxn : x n ≠ 1 := by
        dsimp only [x]
        have hpos : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
        linarith
      simp only [mem_compl_iff, mem_singleton_iff]
      intro h
      exact hxn (Complex.ofReal_inj.mp (by simpa only [ofReal_one] using h))
  have hxcWithin : Tendsto (fun n => (x n : ℂ)) atTop
      (𝓝[({(1 : ℂ)} : Set ℂ)ᶜ] (1 : ℂ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hxc, hpunctured⟩
  have heqFrequentlyAtTop : ∃ᶠ n in atTop,
      deBruijnNewmanPolymathScaledGamma (x n : ℂ) =
        Complex.exp (deBruijnNewmanPolymathStieltjesLogRemainder (x n : ℂ)) :=
    (Filter.Eventually.of_forall fun n =>
      deBruijnNewmanPolymath_scaledGamma_ofReal_eq_exp_stieltjes
        (by dsimp only [x]; positivity)).frequently
  have heqFrequently : ∃ᶠ w in 𝓝[({(1 : ℂ)} : Set ℂ)ᶜ] (1 : ℂ),
      deBruijnNewmanPolymathScaledGamma w =
        Complex.exp (deBruijnNewmanPolymathStieltjesLogRemainder w) :=
    hxcWithin.frequently heqFrequentlyAtTop
  exact (hScaledAnalytic.eqOn_of_preconnected_of_frequently_eq hExpAnalytic hpre hone
    heqFrequently) hz

theorem integral_add_rpow_neg_two_Ioi {r : ℝ} (hr : 0 < r) :
    (∫ t : ℝ in Ioi 0, (t + r) ^ (-2 : ℝ)) = 1 / r := by
  let F : ℝ → ℝ := fun t => -(t + r)⁻¹
  have hderiv : ∀ t ∈ Ici (0 : ℝ), HasDerivAt F ((t + r) ^ (-2 : ℝ)) t := by
    intro t ht
    have hpos : 0 < t + r := add_pos_of_nonneg_of_pos ht hr
    have hraw := (((hasDerivAt_id t).add_const r).inv hpos.ne').neg
    unfold F
    refine (hraw.congr_deriv ?_).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun u => ?_)
    · rw [Real.rpow_neg hpos.le]
      norm_num [Real.rpow_natCast]
      ring
    · simp only [Pi.neg_apply, Pi.inv_apply, id_eq]
  have hint : IntegrableOn (fun t : ℝ => (t + r) ^ (-2 : ℝ)) (Ioi 0) :=
    integrableOn_add_rpow_Ioi_of_lt (by norm_num) (by linarith)
  have hlim : Tendsto F atTop (𝓝 0) := by
    have hadd : Tendsto (fun t : ℝ => t + r) atTop atTop :=
      tendsto_atTop_add_const_right atTop r tendsto_id
    simpa only [F, Function.comp_def, neg_zero] using
      (tendsto_inv_atTop_zero.comp hadd).neg
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim]
  dsimp only [F]
  field_simp
  ring

/-- A radial majorant yielding a bound uniform up to the imaginary-axis boundary. -/
def deBruijnNewmanPolymathStieltjesRadialMajorant (z : ℂ) (t : ℝ) : ℝ :=
  (1 / 4) * (t + ‖z‖) ^ (-2 : ℝ)

theorem norm_deBruijnNewmanPolymathStieltjesIntegrand_le_radial
    {z : ℂ} (hz : 0 < z.re) {t : ℝ} (ht : 0 ≤ t) :
    ‖deBruijnNewmanPolymathStieltjesIntegrand z t‖ ≤
      deBruijnNewmanPolymathStieltjesRadialMajorant z t := by
  have hzNorm : 0 < ‖z‖ :=
    hz.trans_le ((le_abs_self z.re).trans (Complex.abs_re_le_norm z))
  have hpointNorm : 0 < ‖z + (t : ℂ)‖ := by
    have hpointRe : 0 < (z + (t : ℂ)).re := by
      simp only [add_re, ofReal_re]
      linarith
    exact hpointRe.trans_le
      ((le_abs_self (z + (t : ℂ)).re).trans (Complex.abs_re_le_norm (z + (t : ℂ))))
  have hgeom : (t + ‖z‖) ^ 2 ≤ 2 * ‖z + (t : ℂ)‖ ^ 2 := by
    have hzSq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    have hpointSq : ‖z + (t : ℂ)‖ ^ 2 =
        (z.re + t) ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [add_re, ofReal_re, add_im, ofReal_im, add_zero]
      ring
    nlinarith [sq_nonneg (t - ‖z‖), mul_nonneg ht hz.le]
  have hsumPos : 0 < t + ‖z‖ := by positivity
  have hhalf : (t + ‖z‖) ^ 2 / 2 ≤ ‖z + (t : ℂ)‖ ^ 2 := by linarith
  have hinv : (‖z + (t : ℂ)‖ ^ 2)⁻¹ ≤
      2 * ((t + ‖z‖) ^ 2)⁻¹ := by
    have h := (inv_le_inv₀ (sq_pos_of_pos hpointNorm)
      (div_pos (sq_pos_of_pos hsumPos) (by norm_num))).2 hhalf
    calc
      (‖z + (t : ℂ)‖ ^ 2)⁻¹ ≤ ((t + ‖z‖) ^ 2 / 2)⁻¹ := h
      _ = 2 * ((t + ‖z‖) ^ 2)⁻¹ := by field_simp
  have hQ0 := deBruijnNewmanPolymathStieltjesQ_nonneg t
  have hQ8 := deBruijnNewmanPolymathStieltjesQ_le_one_eighth t
  rw [deBruijnNewmanPolymathStieltjesIntegrand,
    deBruijnNewmanPolymathStieltjesRadialMajorant,
    norm_div, norm_pow, norm_real, Real.norm_of_nonneg hQ0, div_eq_mul_inv]
  calc
    deBruijnNewmanPolymathStieltjesQ t * (‖z + (t : ℂ)‖ ^ 2)⁻¹ ≤
        (1 / 8) * (‖z + (t : ℂ)‖ ^ 2)⁻¹ := by gcongr
    _ ≤ (1 / 8) * (2 * ((t + ‖z‖) ^ 2)⁻¹) := by gcongr
    _ = (1 / 4) * (t + ‖z‖) ^ (-2 : ℝ) := by
      rw [Real.rpow_neg hsumPos.le]
      norm_num [Real.rpow_natCast]
      ring

theorem deBruijnNewmanPolymathStieltjesRadialMajorant_integrableOn
    {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (deBruijnNewmanPolymathStieltjesRadialMajorant z) (Ioi (0 : ℝ)) := by
  unfold deBruijnNewmanPolymathStieltjesRadialMajorant
  exact (integrableOn_add_rpow_Ioi_of_lt (a := (-2 : ℝ)) (c := 0) (m := ‖z‖)
    (by norm_num) (by
      have hzNorm : 0 < ‖z‖ :=
        hz.trans_le ((le_abs_self z.re).trans (Complex.abs_re_le_norm z))
      linarith)).const_mul (1 / 4)

theorem norm_deBruijnNewmanPolymathStieltjesLogRemainder_le
    {z : ℂ} (hz : 0 < z.re) :
    ‖deBruijnNewmanPolymathStieltjesLogRemainder z‖ ≤ 1 / (4 * ‖z‖) := by
  have hnorm := norm_integral_le_of_norm_le
    (deBruijnNewmanPolymathStieltjesRadialMajorant_integrableOn hz) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact norm_deBruijnNewmanPolymathStieltjesIntegrand_le_radial hz ht.le)
  rw [deBruijnNewmanPolymathStieltjesLogRemainder]
  calc
    ‖∫ t : ℝ in Ioi 0, deBruijnNewmanPolymathStieltjesIntegrand z t‖ ≤
        ∫ t : ℝ in Ioi 0, deBruijnNewmanPolymathStieltjesRadialMajorant z t := hnorm
    _ = 1 / (4 * ‖z‖) := by
      change (∫ t : ℝ in Ioi 0, (1 / 4) * (t + ‖z‖) ^ (-2 : ℝ)) =
        1 / (4 * ‖z‖)
      rw [integral_const_mul, integral_add_rpow_neg_two_Ioi
        (hz.trans_le ((le_abs_self z.re).trans (Complex.abs_re_le_norm z)))]
      ring

/-- The centered primitive regarded as a complex-valued function of a real variable. -/
def deBruijnNewmanPolymathStieltjesCenteredPrimitiveComplex (u : ℝ) : ℂ :=
  (deBruijnNewmanPolymathStieltjesCenteredPrimitive u : ℂ)

theorem hasDerivAt_deBruijnNewmanPolymathStieltjesCenteredPrimitiveComplex (u : ℝ) :
    HasDerivAt deBruijnNewmanPolymathStieltjesCenteredPrimitiveComplex
      (deBruijnNewmanPolymathStieltjesQUnitComplex u - 1 / 12) u := by
  have huC : HasDerivAt (fun v : ℝ => (v : ℂ)) 1 u :=
    (hasDerivAt_id u).ofReal_comp
  have hraw := (((huC.pow 2).const_mul (1 / 4 : ℂ)).sub
    ((huC.pow 3).const_mul (1 / 6 : ℂ))).sub
    (huC.const_mul (1 / 12 : ℂ))
  unfold deBruijnNewmanPolymathStieltjesCenteredPrimitiveComplex
    deBruijnNewmanPolymathStieltjesCenteredPrimitive
    deBruijnNewmanPolymathStieltjesQUnitComplex
  refine (hraw.congr_deriv ?_).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun v => ?_)
  · push_cast
    ring
  · simp only [Pi.sub_apply, Pi.pow_apply]
    push_cast
    ring

theorem integral_one_div_deBruijnNewmanPolymathStieltjesBlockPoint_sq
    {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    (∫ u : ℝ in (0 : ℝ)..1,
        (1 : ℂ) / deBruijnNewmanPolymathStieltjesBlockPoint z n u ^ 2) =
      1 / (z + n) - 1 / (z + n + 1) := by
  let F : ℝ → ℂ := fun u => -(1 : ℂ) /
    deBruijnNewmanPolymathStieltjesBlockPoint z n u
  have hderiv : ∀ u ∈ [[(0 : ℝ), 1]], HasDerivAt F
      ((1 : ℂ) / deBruijnNewmanPolymathStieltjesBlockPoint z n u ^ 2) u := by
    intro u hu
    have hu' : u ∈ Icc (0 : ℝ) 1 := by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hu
    have hpoint0 : deBruijnNewmanPolymathStieltjesBlockPoint z n u ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp only [Complex.zero_re] at hre
      linarith [deBruijnNewmanPolymathStieltjesBlockPoint_re_pos hz n hu'.1]
    have huC : HasDerivAt (fun v : ℝ => (v : ℂ)) 1 u :=
      (hasDerivAt_id u).ofReal_comp
    have hpoint : HasDerivAt
        (deBruijnNewmanPolymathStieltjesBlockPoint z n) 1 u := by
      change HasDerivAt (fun v : ℝ => z + (n : ℂ) + (v : ℂ)) 1 u
      simpa only [add_assoc] using huC.const_add (z + n)
    have hraw := ((hasDerivAt_const u (-(1 : ℂ))).div hpoint hpoint0)
    unfold F
    refine (hraw.congr_deriv ?_).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun v => ?_)
    · field_simp [hpoint0]
      ring
    · rfl
  have hint : IntervalIntegrable
      (fun u : ℝ => (1 : ℂ) /
        deBruijnNewmanPolymathStieltjesBlockPoint z n u ^ 2)
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    intro u hu
    have hu' : u ∈ Icc (0 : ℝ) 1 := by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hu
    have hpoint0 : deBruijnNewmanPolymathStieltjesBlockPoint z n u ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp only [Complex.zero_re] at hre
      linarith [deBruijnNewmanPolymathStieltjesBlockPoint_re_pos hz n hu'.1]
    have hpointCont : ContinuousAt
        (deBruijnNewmanPolymathStieltjesBlockPoint z n) u := by
      unfold deBruijnNewmanPolymathStieltjesBlockPoint
      fun_prop
    exact (continuousAt_const.div (hpointCont.pow 2)
      (pow_ne_zero 2 hpoint0)).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp [F, deBruijnNewmanPolymathStieltjesBlockPoint]
  ring

theorem hasDerivAt_one_div_deBruijnNewmanPolymathStieltjesBlockPoint_sq
    {z : ℂ} (hz : 0 < z.re) (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt
      (fun v : ℝ => (1 : ℂ) /
        deBruijnNewmanPolymathStieltjesBlockPoint z n v ^ 2)
      ((-2 : ℂ) / deBruijnNewmanPolymathStieltjesBlockPoint z n u ^ 3) u := by
  have hpoint0 : deBruijnNewmanPolymathStieltjesBlockPoint z n u ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.zero_re] at hre
    linarith [deBruijnNewmanPolymathStieltjesBlockPoint_re_pos hz n hu]
  have huC : HasDerivAt (fun v : ℝ => (v : ℂ)) 1 u :=
    (hasDerivAt_id u).ofReal_comp
  have hpoint : HasDerivAt
      (deBruijnNewmanPolymathStieltjesBlockPoint z n) 1 u := by
    change HasDerivAt (fun v : ℝ => z + (n : ℂ) + (v : ℂ)) 1 u
    simpa only [add_assoc] using huC.const_add (z + n)
  have hraw := (hasDerivAt_const u (1 : ℂ)).div (hpoint.pow 2)
    (pow_ne_zero 2 hpoint0)
  refine (hraw.congr_deriv ?_).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun v => ?_)
  · simp only [Pi.pow_apply, Pi.div_apply]
    field_simp [hpoint0]
    ring
  · simp only [Pi.pow_apply, Pi.div_apply]

/-- The mean-subtracted contribution of one Stieltjes unit block. -/
def deBruijnNewmanPolymathStieltjesCenteredBlock (z : ℂ) (n : ℕ) : ℂ :=
  deBruijnNewmanPolymathStieltjesBlock z n -
    (1 / 12) * (1 / (z + n) - 1 / (z + n + 1))

theorem deBruijnNewmanPolymathStieltjesCenteredBlock_eq_integral
    {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    deBruijnNewmanPolymathStieltjesCenteredBlock z n =
      ∫ u : ℝ in (0 : ℝ)..1,
        (deBruijnNewmanPolymathStieltjesQUnitComplex u - 1 / 12) /
          deBruijnNewmanPolymathStieltjesBlockPoint z n u ^ 2 := by
  have hQ : IntervalIntegrable
      (fun u : ℝ => deBruijnNewmanPolymathStieltjesQUnitComplex u /
        deBruijnNewmanPolymathStieltjesBlockPoint z n u ^ 2)
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    intro u hu
    have hu' : u ∈ Icc (0 : ℝ) 1 := by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hu
    have hpoint0 : deBruijnNewmanPolymathStieltjesBlockPoint z n u ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp only [Complex.zero_re] at hre
      linarith [deBruijnNewmanPolymathStieltjesBlockPoint_re_pos hz n hu'.1]
    have hnum : ContinuousAt deBruijnNewmanPolymathStieltjesQUnitComplex u := by
      unfold deBruijnNewmanPolymathStieltjesQUnitComplex
      fun_prop
    have hpoint : ContinuousAt
        (deBruijnNewmanPolymathStieltjesBlockPoint z n) u := by
      unfold deBruijnNewmanPolymathStieltjesBlockPoint
      fun_prop
    exact (hnum.div (hpoint.pow 2) (pow_ne_zero 2 hpoint0)).continuousWithinAt
  have hOne : IntervalIntegrable
      (fun u : ℝ => (1 : ℂ) /
        deBruijnNewmanPolymathStieltjesBlockPoint z n u ^ 2)
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    intro u hu
    have hu' : u ∈ Icc (0 : ℝ) 1 := by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hu
    have hpoint0 : deBruijnNewmanPolymathStieltjesBlockPoint z n u ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp only [Complex.zero_re] at hre
      linarith [deBruijnNewmanPolymathStieltjesBlockPoint_re_pos hz n hu'.1]
    have hpoint : ContinuousAt
        (deBruijnNewmanPolymathStieltjesBlockPoint z n) u := by
      unfold deBruijnNewmanPolymathStieltjesBlockPoint
      fun_prop
    exact (continuousAt_const.div (hpoint.pow 2)
      (pow_ne_zero 2 hpoint0)).continuousWithinAt
  rw [deBruijnNewmanPolymathStieltjesCenteredBlock,
    deBruijnNewmanPolymathStieltjesBlock,
    ← integral_one_div_deBruijnNewmanPolymathStieltjesBlockPoint_sq hz n,
    ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub hQ (hOne.const_mul (1 / 12))]
  apply intervalIntegral.integral_congr
  intro u hu
  field_simp

theorem deBruijnNewmanPolymathStieltjesCenteredBlock_eq_primitive_integral
    {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    deBruijnNewmanPolymathStieltjesCenteredBlock z n =
      2 * ∫ u : ℝ in (0 : ℝ)..1,
        deBruijnNewmanPolymathStieltjesCenteredPrimitiveComplex u /
          deBruijnNewmanPolymathStieltjesBlockPoint z n u ^ 3 := by
  rw [deBruijnNewmanPolymathStieltjesCenteredBlock_eq_integral hz n]
  have hprimitive : ∀ u ∈ [[(0 : ℝ), 1]],
      HasDerivAt deBruijnNewmanPolymathStieltjesCenteredPrimitiveComplex
        (deBruijnNewmanPolymathStieltjesQUnitComplex u - 1 / 12) u :=
    fun u _ => hasDerivAt_deBruijnNewmanPolymathStieltjesCenteredPrimitiveComplex u
  have hreciprocal : ∀ u ∈ [[(0 : ℝ), 1]],
      HasDerivAt
        (fun v : ℝ => (1 : ℂ) /
          deBruijnNewmanPolymathStieltjesBlockPoint z n v ^ 2)
        ((-2 : ℂ) / deBruijnNewmanPolymathStieltjesBlockPoint z n u ^ 3) u := by
    intro u hu
    apply hasDerivAt_one_div_deBruijnNewmanPolymathStieltjesBlockPoint_sq hz n
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
    exact hu.1
  have hprimitiveDerivInt : IntervalIntegrable
      (fun u : ℝ => deBruijnNewmanPolymathStieltjesQUnitComplex u - 1 / 12)
      volume 0 1 := by
    apply Continuous.intervalIntegrable
    unfold deBruijnNewmanPolymathStieltjesQUnitComplex
    fun_prop
  have hreciprocalDerivInt : IntervalIntegrable
      (fun u : ℝ => (-2 : ℂ) /
        deBruijnNewmanPolymathStieltjesBlockPoint z n u ^ 3)
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    intro u hu
    have hu' : u ∈ Icc (0 : ℝ) 1 := by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hu
    have hpoint0 : deBruijnNewmanPolymathStieltjesBlockPoint z n u ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp only [Complex.zero_re] at hre
      linarith [deBruijnNewmanPolymathStieltjesBlockPoint_re_pos hz n hu'.1]
    have hpoint : ContinuousAt
        (deBruijnNewmanPolymathStieltjesBlockPoint z n) u := by
      unfold deBruijnNewmanPolymathStieltjesBlockPoint
      fun_prop
    exact (continuousAt_const.div (hpoint.pow 3)
      (pow_ne_zero 3 hpoint0)).continuousWithinAt
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hprimitive hreciprocal hprimitiveDerivInt hreciprocalDerivInt
  have hcentered :
      (∫ u : ℝ in (0 : ℝ)..1,
        (deBruijnNewmanPolymathStieltjesQUnitComplex u - 1 / 12) *
          ((1 : ℂ) /
            deBruijnNewmanPolymathStieltjesBlockPoint z n u ^ 2)) =
        -(∫ u : ℝ in (0 : ℝ)..1,
          deBruijnNewmanPolymathStieltjesCenteredPrimitiveComplex u *
            ((-2 : ℂ) /
              deBruijnNewmanPolymathStieltjesBlockPoint z n u ^ 3)) := by
    rw [hparts]
    simp [deBruijnNewmanPolymathStieltjesCenteredPrimitiveComplex,
      deBruijnNewmanPolymathStieltjesCenteredPrimitive_zero,
      deBruijnNewmanPolymathStieltjesCenteredPrimitive_one]
  calc
    (∫ u : ℝ in (0 : ℝ)..1,
        (deBruijnNewmanPolymathStieltjesQUnitComplex u - 1 / 12) /
          deBruijnNewmanPolymathStieltjesBlockPoint z n u ^ 2) =
        ∫ u : ℝ in (0 : ℝ)..1,
          (deBruijnNewmanPolymathStieltjesQUnitComplex u - 1 / 12) *
            ((1 : ℂ) /
              deBruijnNewmanPolymathStieltjesBlockPoint z n u ^ 2) := by
      apply intervalIntegral.integral_congr
      intro u hu
      ring
    _ = -(∫ u : ℝ in (0 : ℝ)..1,
          deBruijnNewmanPolymathStieltjesCenteredPrimitiveComplex u *
            ((-2 : ℂ) /
              deBruijnNewmanPolymathStieltjesBlockPoint z n u ^ 3)) := hcentered
    _ = 2 * ∫ u : ℝ in (0 : ℝ)..1,
        deBruijnNewmanPolymathStieltjesCenteredPrimitiveComplex u /
          deBruijnNewmanPolymathStieltjesBlockPoint z n u ^ 3 := by
      rw [← intervalIntegral.integral_neg]
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro u hu
      ring

/-- The first `N` mean-subtracted Stieltjes unit blocks. -/
def deBruijnNewmanPolymathStieltjesCenteredPartial (z : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, deBruijnNewmanPolymathStieltjesCenteredBlock z n

theorem deBruijnNewmanPolymathStieltjesCenteredPartial_eq
    (z : ℂ) (N : ℕ) :
    deBruijnNewmanPolymathStieltjesCenteredPartial z N =
      deBruijnNewmanPolymathStieltjesPartial z N -
        (1 / 12) * (1 / z - 1 / (z + N)) := by
  induction N with
  | zero =>
      simp [deBruijnNewmanPolymathStieltjesCenteredPartial,
        deBruijnNewmanPolymathStieltjesPartial]
  | succ N ih =>
      rw [deBruijnNewmanPolymathStieltjesCenteredPartial] at ih ⊢
      rw [deBruijnNewmanPolymathStieltjesPartial] at ih ⊢
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih,
        deBruijnNewmanPolymathStieltjesCenteredBlock]
      push_cast
      ring

theorem tendsto_one_div_deBruijnNewmanPolymathStieltjesBlockStart
    (z : ℂ) :
    Tendsto (fun N : ℕ => (1 : ℂ) / (z + N)) atTop (𝓝 0) := by
  have hcast : Tendsto (fun N : ℕ => (N : ℂ)) atTop
      (Bornology.cobounded ℂ) := tendsto_natCast_atTop_cobounded
  have hadd : Tendsto (fun N : ℕ => z + (N : ℂ)) atTop
      (Bornology.cobounded ℂ) := (tendsto_const_add_cobounded z).comp hcast
  simpa only [one_div, Function.comp_def] using tendsto_inv₀_cobounded.comp hadd

theorem tendsto_deBruijnNewmanPolymathStieltjesCenteredPartial
    {z : ℂ} (hz : 0 < z.re) :
    Tendsto (deBruijnNewmanPolymathStieltjesCenteredPartial z) atTop
      (𝓝 (deBruijnNewmanPolymathStieltjesLogRemainder z - 1 / (12 * z))) := by
  have htail := tendsto_one_div_deBruijnNewmanPolymathStieltjesBlockStart z
  have hcorrection : Tendsto
      (fun N : ℕ => (1 / 12 : ℂ) * (1 / z - 1 / (z + N))) atTop
      (𝓝 ((1 / 12 : ℂ) * (1 / z - 0))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.sub htail)
  have hraw := (tendsto_deBruijnNewmanPolymathStieltjesPartial hz).sub hcorrection
  have hrewritten : Tendsto
      (fun N : ℕ => deBruijnNewmanPolymathStieltjesCenteredPartial z N) atTop
      (𝓝 (deBruijnNewmanPolymathStieltjesLogRemainder z -
        (1 / 12 : ℂ) * (1 / z - 0))) :=
    hraw.congr' (Filter.Eventually.of_forall fun N =>
      (deBruijnNewmanPolymathStieltjesCenteredPartial_eq z N).symm)
  convert hrewritten using 1
  ring

theorem two_mul_add_norm_le_three_mul_norm_add_of_re_nonneg
    {z : ℂ} (hz : 0 ≤ z.re) {t : ℝ} (ht : 0 ≤ t) :
    2 * (t + ‖z‖) ≤ 3 * ‖z + (t : ℂ)‖ := by
  have hzSq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hpointSq : ‖z + (t : ℂ)‖ ^ 2 =
      (z.re + t) ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [add_re, ofReal_re, add_im, ofReal_im, add_zero]
    ring
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  calc
    (2 * (t + ‖z‖)) ^ 2 = 4 * (t + ‖z‖) ^ 2 := by ring
    _ ≤ 9 * ‖z + (t : ℂ)‖ ^ 2 := by
      nlinarith [hzSq, hpointSq, sq_nonneg (2 * ‖z‖ - 2 * t),
        mul_nonneg hz ht]
    _ = (3 * ‖z + (t : ℂ)‖) ^ 2 := by ring

theorem inv_norm_add_cube_le_stieltjes_radial
    {z : ℂ} (hz : 0 < z.re) {t : ℝ} (ht : 0 ≤ t) :
    (‖z + (t : ℂ)‖ ^ 3)⁻¹ ≤
      (27 / 8) * (t + ‖z‖) ^ (-3 : ℝ) := by
  have hzNorm : 0 < ‖z‖ :=
    hz.trans_le ((le_abs_self z.re).trans (Complex.abs_re_le_norm z))
  have hsum : 0 < t + ‖z‖ := by positivity
  have hpoint : 0 < ‖z + (t : ℂ)‖ := by
    have hre : 0 < (z + (t : ℂ)).re := by
      simp only [add_re, ofReal_re]
      linarith
    exact hre.trans_le
      ((le_abs_self (z + (t : ℂ)).re).trans
        (Complex.abs_re_le_norm (z + (t : ℂ))))
  have hscaled : (2 / 3 : ℝ) * (t + ‖z‖) ≤ ‖z + (t : ℂ)‖ := by
    have hgeom := two_mul_add_norm_le_three_mul_norm_add_of_re_nonneg hz.le ht
    linarith
  have hcubes : ((2 / 3 : ℝ) * (t + ‖z‖)) ^ 3 ≤
      ‖z + (t : ℂ)‖ ^ 3 :=
    pow_le_pow_left₀ (by positivity) hscaled 3
  have hinv : (‖z + (t : ℂ)‖ ^ 3)⁻¹ ≤
      (((2 / 3 : ℝ) * (t + ‖z‖)) ^ 3)⁻¹ :=
    (inv_le_inv₀ (pow_pos hpoint 3) (pow_pos (by positivity) 3)).2 hcubes
  calc
    (‖z + (t : ℂ)‖ ^ 3)⁻¹ ≤
        (((2 / 3 : ℝ) * (t + ‖z‖)) ^ 3)⁻¹ := hinv
    _ = (27 / 8) * (t + ‖z‖) ^ (-3 : ℝ) := by
      rw [Real.rpow_neg hsum.le]
      norm_num [Real.rpow_natCast]
      field_simp
      norm_num

/-- Radial integrable majorant for the mean-subtracted Stieltjes blocks. -/
def deBruijnNewmanPolymathStieltjesCenteredRadialMajorant
    (z : ℂ) (t : ℝ) : ℝ :=
  (27 / 8) * (t + ‖z‖) ^ (-3 : ℝ)

theorem norm_two_mul_stieltjesCenteredPrimitive_div_blockPoint_cube_le
    {z : ℂ} (hz : 0 < z.re) (n : ℕ) {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) :
    ‖(2 : ℂ) *
        deBruijnNewmanPolymathStieltjesCenteredPrimitiveComplex u /
          deBruijnNewmanPolymathStieltjesBlockPoint z n u ^ 3‖ ≤
      deBruijnNewmanPolymathStieltjesCenteredRadialMajorant z (n + u) := by
  have hprimitive :=
    abs_deBruijnNewmanPolymathStieltjesCenteredPrimitive_le_half hu
  have hprimitiveNorm :
      ‖deBruijnNewmanPolymathStieltjesCenteredPrimitiveComplex u‖ ≤ 1 / 2 := by
    simpa [deBruijnNewmanPolymathStieltjesCenteredPrimitiveComplex,
      Real.norm_eq_abs] using hprimitive
  have htu : 0 ≤ (n : ℝ) + u := add_nonneg (Nat.cast_nonneg n) hu.1
  have hradial := inv_norm_add_cube_le_stieltjes_radial hz htu
  have hpointEq : deBruijnNewmanPolymathStieltjesBlockPoint z n u =
      z + (((n : ℝ) + u : ℝ) : ℂ) := by
    unfold deBruijnNewmanPolymathStieltjesBlockPoint
    push_cast
    ring
  rw [norm_div, norm_mul, norm_ofNat, norm_pow, hpointEq, div_eq_mul_inv]
  calc
    2 * ‖deBruijnNewmanPolymathStieltjesCenteredPrimitiveComplex u‖ *
        (‖z + (((n : ℝ) + u : ℝ) : ℂ)‖ ^ 3)⁻¹ ≤
        1 * (‖z + (((n : ℝ) + u : ℝ) : ℂ)‖ ^ 3)⁻¹ := by
      gcongr
      nlinarith
    _ ≤ (27 / 8) * ((n : ℝ) + u + ‖z‖) ^ (-3 : ℝ) := by
      simpa only [one_mul] using hradial
    _ = deBruijnNewmanPolymathStieltjesCenteredRadialMajorant z (n + u) := by
      rfl

theorem norm_deBruijnNewmanPolymathStieltjesCenteredBlock_le
    {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ‖deBruijnNewmanPolymathStieltjesCenteredBlock z n‖ ≤
      ∫ u : ℝ in (0 : ℝ)..1,
        deBruijnNewmanPolymathStieltjesCenteredRadialMajorant z (n + u) := by
  rw [deBruijnNewmanPolymathStieltjesCenteredBlock_eq_primitive_integral hz n,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
  · filter_upwards with u hu
    simpa only [mul_div_assoc] using
      norm_two_mul_stieltjesCenteredPrimitive_div_blockPoint_cube_le hz n
        ⟨hu.1.le, hu.2⟩
  · apply ContinuousOn.intervalIntegrable
    intro u hu
    have hu' : u ∈ Icc (0 : ℝ) 1 := by
      simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hu
    have hbase : 0 < (n : ℝ) + u + ‖z‖ := by
      have hzNorm : 0 < ‖z‖ :=
        hz.trans_le ((le_abs_self z.re).trans (Complex.abs_re_le_norm z))
      exact add_pos_of_nonneg_of_pos
        (add_nonneg (Nat.cast_nonneg n) hu'.1) hzNorm
    unfold deBruijnNewmanPolymathStieltjesCenteredRadialMajorant
    exact (continuousAt_const.mul
      (((continuousAt_const.add continuousAt_id).add continuousAt_const).rpow_const
        (Or.inl hbase.ne'))).continuousWithinAt

theorem deBruijnNewmanPolymathStieltjesCenteredRadialMajorant_integrableOn
    {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (deBruijnNewmanPolymathStieltjesCenteredRadialMajorant z)
      (Ioi (0 : ℝ)) := by
  unfold deBruijnNewmanPolymathStieltjesCenteredRadialMajorant
  exact (integrableOn_add_rpow_Ioi_of_lt (a := (-3 : ℝ)) (c := 0) (m := ‖z‖)
    (by norm_num) (by
      have hzNorm : 0 < ‖z‖ :=
        hz.trans_le ((le_abs_self z.re).trans (Complex.abs_re_le_norm z))
      linarith)).const_mul (27 / 8)

theorem integral_add_rpow_neg_three_Ioi {r : ℝ} (hr : 0 < r) :
    (∫ t : ℝ in Ioi 0, (t + r) ^ (-3 : ℝ)) = 1 / (2 * r ^ 2) := by
  let F : ℝ → ℝ := fun t => -(1 / 2) * (t + r)⁻¹ ^ 2
  have hderiv : ∀ t ∈ Ici (0 : ℝ), HasDerivAt F ((t + r) ^ (-3 : ℝ)) t := by
    intro t ht
    have hpos : 0 < t + r := add_pos_of_nonneg_of_pos ht hr
    have hinv := ((hasDerivAt_id t).add_const r).inv hpos.ne'
    have hraw := (hinv.pow 2).const_mul (-(1 / 2 : ℝ))
    unfold F
    refine (hraw.congr_deriv ?_).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun u => ?_)
    · rw [Real.rpow_neg hpos.le]
      norm_num [Real.rpow_natCast]
      field_simp
    · simp only [Pi.mul_apply, Pi.neg_apply, Pi.pow_apply, Pi.inv_apply, id_eq]
  have hint : IntegrableOn (fun t : ℝ => (t + r) ^ (-3 : ℝ)) (Ioi 0) :=
    integrableOn_add_rpow_Ioi_of_lt (by norm_num) (by linarith)
  have hlim : Tendsto F atTop (𝓝 0) := by
    have hadd : Tendsto (fun t : ℝ => t + r) atTop atTop :=
      tendsto_atTop_add_const_right atTop r tendsto_id
    have hinv : Tendsto (fun t : ℝ => (t + r)⁻¹) atTop (𝓝 0) := by
      simpa only [Function.comp_def] using tendsto_inv_atTop_zero.comp hadd
    simpa only [F, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] using
      (hinv.pow 2).const_mul (-(1 / 2 : ℝ))
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim]
  dsimp only [F]
  field_simp
  ring

theorem integral_deBruijnNewmanPolymathStieltjesCenteredRadialMajorant
    {z : ℂ} (hz : 0 < z.re) :
    (∫ t : ℝ in Ioi 0,
      deBruijnNewmanPolymathStieltjesCenteredRadialMajorant z t) =
      27 / (16 * ‖z‖ ^ 2) := by
  have hzNorm : 0 < ‖z‖ :=
    hz.trans_le ((le_abs_self z.re).trans (Complex.abs_re_le_norm z))
  unfold deBruijnNewmanPolymathStieltjesCenteredRadialMajorant
  rw [integral_const_mul, integral_add_rpow_neg_three_Ioi hzNorm]
  field_simp
  ring

theorem integral_deBruijnNewmanPolymathStieltjesCenteredRadialMajorant_unitBlock
    (z : ℂ) (n : ℕ) :
    (∫ u : ℝ in (0 : ℝ)..1,
      deBruijnNewmanPolymathStieltjesCenteredRadialMajorant z (n + u)) =
      ∫ t : ℝ in (n : ℝ)..(n + 1 : ℕ),
        deBruijnNewmanPolymathStieltjesCenteredRadialMajorant z t := by
  simpa only [zero_add, add_zero, Nat.cast_add, Nat.cast_one] using
    (intervalIntegral.integral_comp_add_left
      (f := deBruijnNewmanPolymathStieltjesCenteredRadialMajorant z)
      (a := (0 : ℝ)) (b := 1) (d := (n : ℝ)))

theorem sum_integral_deBruijnNewmanPolymathStieltjesCenteredRadialMajorant
    {z : ℂ} (hz : 0 < z.re) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      ∫ u : ℝ in (0 : ℝ)..1,
        deBruijnNewmanPolymathStieltjesCenteredRadialMajorant z (n + u)) =
      ∫ t : ℝ in (0 : ℝ)..N,
        deBruijnNewmanPolymathStieltjesCenteredRadialMajorant z t := by
  have hint : ∀ n < N, IntervalIntegrable
      (deBruijnNewmanPolymathStieltjesCenteredRadialMajorant z) volume
      (n : ℝ) (n + 1 : ℕ) := by
    intro n hn
    have hnn : (n : ℝ) ≤ (n + 1 : ℕ) := by
      exact_mod_cast Nat.le_succ n
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hnn]
    exact (deBruijnNewmanPolymathStieltjesCenteredRadialMajorant_integrableOn hz).mono_set
      (fun t ht => lt_of_le_of_lt (Nat.cast_nonneg n) ht.1)
  calc
    (∑ n ∈ Finset.range N,
        ∫ u : ℝ in (0 : ℝ)..1,
          deBruijnNewmanPolymathStieltjesCenteredRadialMajorant z (n + u)) =
        ∑ n ∈ Finset.range N,
          ∫ t : ℝ in (n : ℝ)..(n + 1 : ℕ),
            deBruijnNewmanPolymathStieltjesCenteredRadialMajorant z t := by
      apply Finset.sum_congr rfl
      intro n hn
      exact integral_deBruijnNewmanPolymathStieltjesCenteredRadialMajorant_unitBlock z n
    _ = ∫ t : ℝ in (0 : ℝ)..N,
        deBruijnNewmanPolymathStieltjesCenteredRadialMajorant z t := by
      simpa only [Nat.cast_zero] using
        (intervalIntegral.sum_integral_adjacent_intervals
          (f := deBruijnNewmanPolymathStieltjesCenteredRadialMajorant z)
          (a := fun n : ℕ => (n : ℝ)) hint)

theorem norm_deBruijnNewmanPolymathStieltjesCenteredPartial_le
    {z : ℂ} (hz : 0 < z.re) (N : ℕ) :
    ‖deBruijnNewmanPolymathStieltjesCenteredPartial z N‖ ≤ 2 / ‖z‖ ^ 2 := by
  have hzNorm : 0 < ‖z‖ :=
    hz.trans_le ((le_abs_self z.re).trans (Complex.abs_re_le_norm z))
  have hfinite :
      (∫ t : ℝ in (0 : ℝ)..N,
        deBruijnNewmanPolymathStieltjesCenteredRadialMajorant z t) ≤
      ∫ t : ℝ in Ioi 0,
        deBruijnNewmanPolymathStieltjesCenteredRadialMajorant z t := by
    rw [intervalIntegral.integral_of_le (Nat.cast_nonneg N)]
    have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
        deBruijnNewmanPolymathStieltjesCenteredRadialMajorant z := by
      refine (ae_restrict_iff' measurableSet_Ioi).2 ?_
      exact Filter.Eventually.of_forall fun t ht => by
        unfold deBruijnNewmanPolymathStieltjesCenteredRadialMajorant
        exact mul_nonneg (by norm_num)
          (Real.rpow_nonneg (add_nonneg ht.le (norm_nonneg z)) _)
    exact setIntegral_mono_set
      (deBruijnNewmanPolymathStieltjesCenteredRadialMajorant_integrableOn hz)
      hnonneg (Filter.Eventually.of_forall fun t ht => ht.1)
  calc
    ‖deBruijnNewmanPolymathStieltjesCenteredPartial z N‖ =
        ‖∑ n ∈ Finset.range N,
          deBruijnNewmanPolymathStieltjesCenteredBlock z n‖ := rfl
    _ ≤ ∑ n ∈ Finset.range N,
        ‖deBruijnNewmanPolymathStieltjesCenteredBlock z n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N,
        ∫ u : ℝ in (0 : ℝ)..1,
          deBruijnNewmanPolymathStieltjesCenteredRadialMajorant z (n + u) := by
      gcongr with n hn
      exact norm_deBruijnNewmanPolymathStieltjesCenteredBlock_le hz n
    _ = ∫ t : ℝ in (0 : ℝ)..N,
        deBruijnNewmanPolymathStieltjesCenteredRadialMajorant z t :=
      sum_integral_deBruijnNewmanPolymathStieltjesCenteredRadialMajorant hz N
    _ ≤ ∫ t : ℝ in Ioi 0,
        deBruijnNewmanPolymathStieltjesCenteredRadialMajorant z t := hfinite
    _ = 27 / (16 * ‖z‖ ^ 2) :=
      integral_deBruijnNewmanPolymathStieltjesCenteredRadialMajorant hz
    _ ≤ 2 / ‖z‖ ^ 2 := by
      rw [show 27 / (16 * ‖z‖ ^ 2) = (27 / 16) / ‖z‖ ^ 2 by ring]
      exact (div_le_div_iff_of_pos_right (sq_pos_of_pos hzNorm)).2 (by norm_num)

theorem deBruijnNewmanPolymath_stieltjesLogRemainder_sub_first_norm_le
    {z : ℂ} (hz : 0 < z.re) :
    ‖deBruijnNewmanPolymathStieltjesLogRemainder z - 1 / (12 * z)‖ ≤
      2 / ‖z‖ ^ 2 := by
  apply le_of_tendsto'
    (tendsto_deBruijnNewmanPolymathStieltjesCenteredPartial hz).norm
  exact fun N => norm_deBruijnNewmanPolymathStieltjesCenteredPartial_le hz N

private theorem deBruijnNewmanPolymathStieltjesLogRemainder_norm_sq_le
    {z : ℂ} (hz : 0 < z.re) :
    ‖deBruijnNewmanPolymathStieltjesLogRemainder z‖ ^ 2 ≤
      1 / (16 * ‖z‖ ^ 2) := by
  have hL := norm_deBruijnNewmanPolymathStieltjesLogRemainder_le hz
  calc
    ‖deBruijnNewmanPolymathStieltjesLogRemainder z‖ ^ 2 ≤
        (1 / (4 * ‖z‖)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hL 2
    _ = 1 / (16 * ‖z‖ ^ 2) := by ring

private theorem deBruijnNewmanPolymathStieltjesLogRemainder_norm_le_one
    {z : ℂ} (hz : 0 < z.re) (hzNorm : 1 ≤ ‖z‖) :
    ‖deBruijnNewmanPolymathStieltjesLogRemainder z‖ ≤ 1 := by
  calc
    ‖deBruijnNewmanPolymathStieltjesLogRemainder z‖ ≤ 1 / (4 * ‖z‖) :=
      norm_deBruijnNewmanPolymathStieltjesLogRemainder_le hz
    _ ≤ 1 := by
      apply (div_le_iff₀ (by positivity : 0 < 4 * ‖z‖)).2
      nlinarith

theorem deBruijnNewmanPolymathGammaStirlingR2_norm_le_three
    {z : ℂ} (hz : 0 < z.re) (hzNorm : 1 ≤ ‖z‖) :
    ‖deBruijnNewmanPolymathGammaStirlingR2 z‖ ≤ 3 / ‖z‖ ^ 2 := by
  have hzNormPos : 0 < ‖z‖ := lt_of_lt_of_le (by norm_num) hzNorm
  have hExp := Complex.norm_exp_sub_one_sub_id_le
    (deBruijnNewmanPolymathStieltjesLogRemainder_norm_le_one hz hzNorm)
  have hCentered :=
    deBruijnNewmanPolymath_stieltjesLogRemainder_sub_first_norm_le hz
  change ‖deBruijnNewmanPolymathScaledGamma z - 1 - 1 / (12 * z)‖ ≤
    3 / ‖z‖ ^ 2
  rw [deBruijnNewmanPolymath_scaledGamma_eq_exp_stieltjes hz]
  calc
    ‖Complex.exp (deBruijnNewmanPolymathStieltjesLogRemainder z) - 1 -
        1 / (12 * z)‖ =
        ‖(Complex.exp (deBruijnNewmanPolymathStieltjesLogRemainder z) - 1 -
            deBruijnNewmanPolymathStieltjesLogRemainder z) +
          (deBruijnNewmanPolymathStieltjesLogRemainder z - 1 / (12 * z))‖ := by
      congr 1
      ring
    _ ≤ ‖Complex.exp (deBruijnNewmanPolymathStieltjesLogRemainder z) - 1 -
          deBruijnNewmanPolymathStieltjesLogRemainder z‖ +
        ‖deBruijnNewmanPolymathStieltjesLogRemainder z - 1 / (12 * z)‖ :=
      norm_add_le _ _
    _ ≤ ‖deBruijnNewmanPolymathStieltjesLogRemainder z‖ ^ 2 +
        2 / ‖z‖ ^ 2 := add_le_add hExp hCentered
    _ ≤ 1 / (16 * ‖z‖ ^ 2) + 2 / ‖z‖ ^ 2 :=
      add_le_add
        (deBruijnNewmanPolymathStieltjesLogRemainder_norm_sq_le hz) le_rfl
    _ ≤ 3 / ‖z‖ ^ 2 := by
      rw [show 1 / (16 * ‖z‖ ^ 2) + 2 / ‖z‖ ^ 2 =
        (33 / 16) / ‖z‖ ^ 2 by ring]
      exact (div_le_div_iff_of_pos_right (sq_pos_of_pos hzNormPos)).2 (by norm_num)

theorem deBruijnNewmanPolymathScaledGammaInverseR2_norm_le_three
    {z : ℂ} (hz : 0 < z.re) (hzNorm : 1 ≤ ‖z‖) :
    ‖deBruijnNewmanPolymathScaledGammaInverseR2 z‖ ≤ 3 / ‖z‖ ^ 2 := by
  have hzNormPos : 0 < ‖z‖ := lt_of_lt_of_le (by norm_num) hzNorm
  have hNegNorm :
      ‖-deBruijnNewmanPolymathStieltjesLogRemainder z‖ ≤ 1 := by
    simpa using
      deBruijnNewmanPolymathStieltjesLogRemainder_norm_le_one hz hzNorm
  have hExp := Complex.norm_exp_sub_one_sub_id_le hNegNorm
  have hCentered :=
    deBruijnNewmanPolymath_stieltjesLogRemainder_sub_first_norm_le hz
  rw [deBruijnNewmanPolymathScaledGammaInverseR2,
    deBruijnNewmanPolymath_scaledGamma_eq_exp_stieltjes hz]
  rw [one_div, ← Complex.exp_neg]
  calc
    ‖Complex.exp (-deBruijnNewmanPolymathStieltjesLogRemainder z) - 1 +
        1 / (12 * z)‖ =
        ‖(Complex.exp (-deBruijnNewmanPolymathStieltjesLogRemainder z) - 1 -
            (-deBruijnNewmanPolymathStieltjesLogRemainder z)) -
          (deBruijnNewmanPolymathStieltjesLogRemainder z - 1 / (12 * z))‖ := by
      congr 1
      ring
    _ ≤ ‖Complex.exp (-deBruijnNewmanPolymathStieltjesLogRemainder z) - 1 -
          (-deBruijnNewmanPolymathStieltjesLogRemainder z)‖ +
        ‖deBruijnNewmanPolymathStieltjesLogRemainder z - 1 / (12 * z)‖ :=
      norm_sub_le _ _
    _ ≤ ‖-deBruijnNewmanPolymathStieltjesLogRemainder z‖ ^ 2 +
        2 / ‖z‖ ^ 2 := add_le_add hExp hCentered
    _ = ‖deBruijnNewmanPolymathStieltjesLogRemainder z‖ ^ 2 +
        2 / ‖z‖ ^ 2 := by rw [norm_neg]
    _ ≤ 1 / (16 * ‖z‖ ^ 2) + 2 / ‖z‖ ^ 2 :=
      add_le_add
        (deBruijnNewmanPolymathStieltjesLogRemainder_norm_sq_le hz) le_rfl
    _ ≤ 3 / ‖z‖ ^ 2 := by
      rw [show 1 / (16 * ‖z‖ ^ 2) + 2 / ‖z‖ ^ 2 =
        (33 / 16) / ‖z‖ ^ 2 by ring]
      exact (div_le_div_iff_of_pos_right (sq_pos_of_pos hzNormPos)).2 (by norm_num)

theorem norm_deBruijnNewmanPolymathBoydR2CauchyWeight_div_sub_le_six
    {z w : ℂ} (hw : 0 < w.re) (hwNorm : 1 ≤ ‖w‖)
    (hfar : 2 * ‖z‖ ≤ ‖w‖) :
    ‖deBruijnNewmanPolymathBoydR2CauchyWeight w / (w - z)‖ ≤
      6 / ‖w‖ ^ 2 := by
  have hwNormPos : 0 < ‖w‖ := lt_of_lt_of_le (by norm_num) hwNorm
  have hden : ‖w‖ / 2 ≤ ‖w - z‖ := by
    calc
      ‖w‖ / 2 ≤ ‖w‖ - ‖z‖ := by linarith
      _ ≤ ‖w - z‖ := norm_sub_norm_le w z
  have hdenPos : 0 < ‖w - z‖ := lt_of_lt_of_le (half_pos hwNormPos) hden
  have hR2 := deBruijnNewmanPolymathGammaStirlingR2_norm_le_three hw hwNorm
  rw [deBruijnNewmanPolymathBoydR2CauchyWeight, norm_div, norm_mul]
  calc
    ‖w‖ * ‖deBruijnNewmanPolymathGammaStirlingR2 w‖ / ‖w - z‖ ≤
        (‖w‖ * (3 / ‖w‖ ^ 2)) / (‖w‖ / 2) := by
      gcongr
    _ = 6 / ‖w‖ ^ 2 := by
      field_simp [hwNormPos.ne']
      ring

theorem norm_deBruijnNewmanPolymathBoydInverseR2CauchyWeight_div_sub_le_six
    {z w : ℂ} (hw : w.re < 0) (hwNorm : 1 ≤ ‖w‖)
    (hfar : 2 * ‖z‖ ≤ ‖w‖) :
    ‖deBruijnNewmanPolymathBoydInverseR2CauchyWeight w / (w - z)‖ ≤
      6 / ‖w‖ ^ 2 := by
  have hwNormPos : 0 < ‖w‖ := lt_of_lt_of_le (by norm_num) hwNorm
  have hden : ‖w‖ / 2 ≤ ‖w - z‖ := by
    calc
      ‖w‖ / 2 ≤ ‖w‖ - ‖z‖ := by linarith
      _ ≤ ‖w - z‖ := norm_sub_norm_le w z
  have hdenPos : 0 < ‖w - z‖ := lt_of_lt_of_le (half_pos hwNormPos) hden
  have hInv : ‖deBruijnNewmanPolymathScaledGammaInverseR2 (-w)‖ ≤
      3 / ‖w‖ ^ 2 := by
    simpa only [norm_neg] using
      deBruijnNewmanPolymathScaledGammaInverseR2_norm_le_three
        (z := -w) (by simpa using neg_pos.mpr hw) (by simpa using hwNorm)
  rw [deBruijnNewmanPolymathBoydInverseR2CauchyWeight, norm_div, norm_mul]
  calc
    ‖w‖ * ‖deBruijnNewmanPolymathScaledGammaInverseR2 (-w)‖ / ‖w - z‖ ≤
        (‖w‖ * (3 / ‖w‖ ^ 2)) / (‖w‖ / 2) := by
      gcongr
    _ = 6 / ‖w‖ ^ 2 := by
      field_simp [hwNormPos.ne']
      ring

theorem norm_deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand_le
    {z : ℂ} {epsilon y : ℝ} (hepsilon : 0 < epsilon)
    (hyNorm : 1 ≤ |y|) (hyFar : 2 * ‖z‖ ≤ |y|) :
    ‖deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand z epsilon y‖ ≤
      12 / |y| ^ 2 := by
  let wplus : ℂ := (epsilon : ℂ) + (y : ℂ) * Complex.I
  let wminus : ℂ := -(epsilon : ℂ) + (y : ℂ) * Complex.I
  have hplusRe : 0 < wplus.re := by simpa [wplus] using hepsilon
  have hminusRe : wminus.re < 0 := by simpa [wminus] using neg_neg_of_pos hepsilon
  have hyPlus : |y| ≤ ‖wplus‖ := by
    calc
      |y| = |wplus.im| := by simp [wplus]
      _ ≤ ‖wplus‖ := Complex.abs_im_le_norm wplus
  have hyMinus : |y| ≤ ‖wminus‖ := by
    calc
      |y| = |wminus.im| := by simp [wminus]
      _ ≤ ‖wminus‖ := Complex.abs_im_le_norm wminus
  have hplus := norm_deBruijnNewmanPolymathBoydR2CauchyWeight_div_sub_le_six
    (z := z) hplusRe (hyNorm.trans hyPlus) (hyFar.trans hyPlus)
  have hminus :=
    norm_deBruijnNewmanPolymathBoydInverseR2CauchyWeight_div_sub_le_six
      (z := z) hminusRe (hyNorm.trans hyMinus) (hyFar.trans hyMinus)
  have hyPos : 0 < |y| := lt_of_lt_of_le (by norm_num) hyNorm
  have hplusTail : 6 / ‖wplus‖ ^ 2 ≤ 6 / |y| ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hyPos)
      (pow_le_pow_left₀ (abs_nonneg y) hyPlus 2)
  have hminusTail : 6 / ‖wminus‖ ^ 2 ≤ 6 / |y| ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hyPos)
      (pow_le_pow_left₀ (abs_nonneg y) hyMinus 2)
  rw [deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand,
    norm_mul, norm_I, one_mul]
  calc
    ‖deBruijnNewmanPolymathBoydR2CauchyWeight wplus / (wplus - z) -
        deBruijnNewmanPolymathBoydInverseR2CauchyWeight wminus / (wminus - z)‖ ≤
        ‖deBruijnNewmanPolymathBoydR2CauchyWeight wplus / (wplus - z)‖ +
          ‖deBruijnNewmanPolymathBoydInverseR2CauchyWeight wminus /
            (wminus - z)‖ := norm_sub_le _ _
    _ ≤ 6 / ‖wplus‖ ^ 2 + 6 / ‖wminus‖ ^ 2 := add_le_add hplus hminus
    _ ≤ 6 / |y| ^ 2 + 6 / |y| ^ 2 := add_le_add hplusTail hminusTail
    _ = 12 / |y| ^ 2 := by ring

theorem norm_deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand_le
    {z : ℂ} (hz : 0 < z.re) {y : ℝ}
    (hyNorm : 1 ≤ |y|) (hyFar : 2 * ‖z‖ ≤ |y|) :
    ‖deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand z y‖ ≤
      12 / |y| ^ 2 := by
  have hy0 : y ≠ 0 := by
    intro hy
    subst y
    norm_num at hyNorm
  have hlim : Filter.Tendsto
      (fun epsilon : ℝ =>
        deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand z epsilon y)
      (𝓝 0) (𝓝 (deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand z y)) := by
    simpa [deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand] using
      deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand_tendsto hz hy0
  have hlimRight : Filter.Tendsto
      (fun epsilon : ℝ =>
        deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand z epsilon y)
      (𝓝[>] (0 : ℝ))
      (𝓝 (deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand z y)) :=
    hlim.mono_left inf_le_left
  apply le_of_tendsto hlimRight.norm
  filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
  exact norm_deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand_le
    hepsilon hyNorm hyFar

theorem norm_deBruijnNewmanPolymathBoydBoundaryTraceErrorIntegrand_le
    {z : ℂ} (hz : 0 < z.re) {epsilon y : ℝ} (hepsilon : 0 < epsilon)
    (hyNorm : 1 ≤ |y|) (hyFar : 2 * ‖z‖ ≤ |y|) :
    ‖deBruijnNewmanPolymathBoydBoundaryTraceErrorIntegrand z epsilon y‖ ≤
      24 / |y| ^ 2 := by
  rw [deBruijnNewmanPolymathBoydBoundaryTraceErrorIntegrand]
  calc
    ‖deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand z epsilon y -
        deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand z y‖ ≤
        ‖deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand z epsilon y‖ +
          ‖deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand z y‖ := norm_sub_le _ _
    _ ≤ 12 / |y| ^ 2 + 12 / |y| ^ 2 := add_le_add
      (norm_deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand_le
        hepsilon hyNorm hyFar)
      (norm_deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand_le hz hyNorm hyFar)
    _ = 24 / |y| ^ 2 := by ring

theorem continuousAt_deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand
    {z : ℂ} (hz : 0 < z.re) {epsilon y : ℝ}
    (hepsilon : 0 ≤ epsilon) (hepsilonz : epsilon < z.re) (hy : y ≠ 0) :
    ContinuousAt
      (deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand z epsilon) y := by
  let wplus : ℂ := (epsilon : ℂ) + (y : ℂ) * Complex.I
  let wminus : ℂ := -(epsilon : ℂ) + (y : ℂ) * Complex.I
  have hplusIm : wplus.im ≠ 0 := by simpa [wplus] using hy
  have hminusIm : wminus.im ≠ 0 := by simpa [wminus] using hy
  have hplusPath : ContinuousAt
      (fun v : ℝ => (epsilon : ℂ) + (v : ℂ) * Complex.I) y := by
    fun_prop
  have hminusPath : ContinuousAt
      (fun v : ℝ => -(epsilon : ℂ) + (v : ℂ) * Complex.I) y := by
    fun_prop
  have hplusWeight : ContinuousAt
      (fun v : ℝ => deBruijnNewmanPolymathBoydR2CauchyWeight
        ((epsilon : ℂ) + (v : ℂ) * Complex.I)) y :=
    (deBruijnNewmanPolymathBoydR2CauchyWeight_continuousAt_of_im_ne_zero
      hplusIm).comp_of_eq hplusPath rfl
  have hminusWeight : ContinuousAt
      (fun v : ℝ => deBruijnNewmanPolymathBoydInverseR2CauchyWeight
        (-(epsilon : ℂ) + (v : ℂ) * Complex.I)) y :=
    (deBruijnNewmanPolymathBoydInverseR2CauchyWeight_continuousAt_of_im_ne_zero
      hminusIm).comp_of_eq hminusPath rfl
  have hplusDen : ContinuousAt
      (fun v : ℝ => (epsilon : ℂ) + (v : ℂ) * Complex.I - z) y := by
    fun_prop
  have hminusDen : ContinuousAt
      (fun v : ℝ => -(epsilon : ℂ) + (v : ℂ) * Complex.I - z) y := by
    fun_prop
  have hplusNe : wplus - z ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [wplus] at hre
    linarith
  have hminusNe : wminus - z ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [wminus] at hre
    linarith
  exact continuousAt_const.mul
    ((hplusWeight.div hplusDen hplusNe).sub
      (hminusWeight.div hminusDen hminusNe))

theorem continuousAt_deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand
    {z : ℂ} (hz : 0 < z.re) {y : ℝ} (hy : y ≠ 0) :
    ContinuousAt (deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand z) y := by
  have hshift := continuousAt_deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand
    hz (epsilon := 0) (by norm_num) hz hy
  apply hshift.congr
  filter_upwards [isOpen_compl_singleton.mem_nhds hy] with v hv
  exact deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand_zero z
    (Set.mem_compl_singleton_iff.mp hv)

theorem continuousAt_deBruijnNewmanPolymathBoydBoundaryTraceErrorIntegrand
    {z : ℂ} (hz : 0 < z.re) {epsilon y : ℝ}
    (hepsilon : 0 ≤ epsilon) (hepsilonz : epsilon < z.re) (hy : y ≠ 0) :
    ContinuousAt (deBruijnNewmanPolymathBoydBoundaryTraceErrorIntegrand z epsilon) y := by
  exact (continuousAt_deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand
    hz hepsilon hepsilonz hy).sub
      (continuousAt_deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand hz hy)

/-- A fixed cutoff beyond both the unit circle and twice the Cauchy pole radius. -/
def deBruijnNewmanPolymathStieltjesTailCutoff (z : ℂ) : ℝ :=
  max 1 (2 * ‖z‖)

theorem one_le_deBruijnNewmanPolymathStieltjesTailCutoff (z : ℂ) :
    1 ≤ deBruijnNewmanPolymathStieltjesTailCutoff z :=
  le_max_left _ _

theorem two_norm_le_deBruijnNewmanPolymathStieltjesTailCutoff (z : ℂ) :
    2 * ‖z‖ ≤ deBruijnNewmanPolymathStieltjesTailCutoff z :=
  le_max_right _ _

/-- The common integrable majorant for the positive and reflected negative trace tails. -/
def deBruijnNewmanPolymathStieltjesTailMajorant (y : ℝ) : ℝ :=
  24 / y ^ 2

theorem deBruijnNewmanPolymathStieltjesTailMajorant_integrableOn
    {B : ℝ} (hB : 0 < B) :
    IntegrableOn deBruijnNewmanPolymathStieltjesTailMajorant (Ioi B) := by
  unfold deBruijnNewmanPolymathStieltjesTailMajorant
  have hraw := (integrableOn_add_rpow_Ioi_of_lt
    (a := (-2 : ℝ)) (c := B) (m := 0)
    (by norm_num) (by linarith)).const_mul 24
  apply hraw.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hyPos : 0 < y := hB.trans hy
  rw [add_zero, Real.rpow_neg hyPos.le, Real.rpow_two, div_eq_mul_inv]

private theorem tendsto_intervalIntegral_of_dominated_on_Ioi
    {B : ℝ} {F : ℕ → ℝ → ℂ} {bound : ℝ → ℝ} {T : ℕ → ℝ}
    (hmeas : ∀ᶠ n in Filter.atTop,
      AEStronglyMeasurable (F n) (volume.restrict (Ioi B)))
    (hbound : ∀ᶠ n in Filter.atTop,
      ∀ᵐ y ∂volume.restrict (Ioi B), ‖F n y‖ ≤ bound y)
    (hboundNonneg : ∀ y ∈ Ioi B, 0 ≤ bound y)
    (hint : IntegrableOn bound (Ioi B))
    (hpointwise : ∀ᵐ y ∂volume.restrict (Ioi B),
      Filter.Tendsto (fun n : ℕ => F n y) Filter.atTop (𝓝 0))
    (hT : Filter.Tendsto T Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun n : ℕ => ∫ y : ℝ in B..T n, F n y)
      Filter.atTop (𝓝 0) := by
  let G : ℕ → ℝ → ℂ := fun n => (Ioc B (T n)).indicator (F n)
  have hGmeas : ∀ᶠ n in Filter.atTop,
      AEStronglyMeasurable (G n) (volume.restrict (Ioi B)) := by
    filter_upwards [hmeas] with n hn
    exact hn.indicator measurableSet_Ioc
  have hGbound : ∀ᶠ n in Filter.atTop,
      ∀ᵐ y ∂volume.restrict (Ioi B), ‖G n y‖ ≤ bound y := by
    filter_upwards [hbound] with n hn
    filter_upwards [hn, ae_restrict_mem measurableSet_Ioi] with y hy hyB
    by_cases hyIoc : y ∈ Ioc B (T n)
    · simpa [G, hyIoc] using hy
    · simp [G, hyIoc, hboundNonneg y hyB]
  have hGpointwise : ∀ᵐ y ∂volume.restrict (Ioi B),
      Filter.Tendsto (fun n : ℕ => G n y) Filter.atTop (𝓝 0) := by
    filter_upwards [hpointwise, ae_restrict_mem measurableSet_Ioi] with y hy hyB
    have hyT : ∀ᶠ n : ℕ in Filter.atTop, y ≤ T n :=
      (Filter.tendsto_atTop.1 hT y)
    have heq : (fun n : ℕ => F n y) =ᶠ[Filter.atTop]
        (fun n : ℕ => G n y) := by
      filter_upwards [hyT] with n hn
      rw [show G n y = (Ioc B (T n)).indicator (F n) y by rfl,
        Set.indicator_of_mem (show y ∈ Ioc B (T n) from ⟨hyB, hn⟩)]
    exact hy.congr' heq
  have hmain := tendsto_integral_filter_of_dominated_convergence bound hGmeas hGbound
    hint hGpointwise
  have hmain' : Filter.Tendsto
      (fun n : ℕ => ∫ y : ℝ, G n y ∂volume.restrict (Ioi B))
      Filter.atTop (𝓝 0) := by
    simpa only [integral_zero] using hmain
  have heq : (fun n : ℕ => ∫ y : ℝ, G n y ∂volume.restrict (Ioi B))
      =ᶠ[Filter.atTop] (fun n : ℕ => ∫ y : ℝ in B..T n, F n y) := by
    filter_upwards [Filter.tendsto_atTop.1 hT B] with n hBT
    have hsubset : Ioc B (T n) ⊆ Ioi B := fun _ hy => hy.1
    change (∫ y : ℝ, (Ioc B (T n)).indicator (F n) y ∂volume.restrict (Ioi B)) =
      ∫ y : ℝ in B..T n, F n y
    rw [integral_indicator measurableSet_Ioc,
      Measure.restrict_restrict_of_subset hsubset,
      intervalIntegral.integral_of_le hBT]
  exact hmain'.congr' heq

theorem tendsto_integral_deBruijnNewmanPolymathBoydBoundaryTraceErrorIntegrand_Ioi_cutoff
    {z : ℂ} (hz : 0 < z.re) :
    Filter.Tendsto
      (fun n : ℕ => ∫ y : ℝ in Ioi (deBruijnNewmanPolymathStieltjesTailCutoff z),
        deBruijnNewmanPolymathBoydBoundaryTraceErrorIntegrand z
          (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) y)
      Filter.atTop (𝓝 0) := by
  let B := deBruijnNewmanPolymathStieltjesTailCutoff z
  let F : ℕ → ℝ → ℂ := fun n y =>
    deBruijnNewmanPolymathBoydBoundaryTraceErrorIntegrand z
      (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) y
  let bound : ℝ → ℝ := deBruijnNewmanPolymathStieltjesTailMajorant
  have hB : 0 < B := lt_of_lt_of_le (by norm_num)
    (one_le_deBruijnNewmanPolymathStieltjesTailCutoff z)
  have hmeas : ∀ᶠ n in Filter.atTop,
      AEStronglyMeasurable (F n) (volume.restrict (Ioi B)) := by
    exact Filter.Eventually.of_forall fun n =>
      ContinuousOn.aestronglyMeasurable (fun y hy =>
        (continuousAt_deBruijnNewmanPolymathBoydBoundaryTraceErrorIntegrand hz
          (deBruijnNewmanPolymathBoydBoundaryEpsilon_pos hz n).le
          (deBruijnNewmanPolymathBoydBoundaryEpsilon_lt_re hz n)
          (ne_of_gt (hB.trans hy))).continuousWithinAt) measurableSet_Ioi
  have hbound : ∀ᶠ n in Filter.atTop,
      ∀ᵐ y ∂volume.restrict (Ioi B), ‖F n y‖ ≤ bound y := by
    refine Filter.Eventually.of_forall fun n => ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hyPos : 0 < y := hB.trans hy
    have hyNorm : 1 ≤ |y| := by
      rw [abs_of_pos hyPos]
      exact (one_le_deBruijnNewmanPolymathStieltjesTailCutoff z).trans hy.le
    have hyFar : 2 * ‖z‖ ≤ |y| := by
      rw [abs_of_pos hyPos]
      exact (two_norm_le_deBruijnNewmanPolymathStieltjesTailCutoff z).trans hy.le
    have hraw := norm_deBruijnNewmanPolymathBoydBoundaryTraceErrorIntegrand_le
      hz (deBruijnNewmanPolymathBoydBoundaryEpsilon_pos hz n) hyNorm hyFar
    change ‖deBruijnNewmanPolymathBoydBoundaryTraceErrorIntegrand z
      (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) y‖ ≤
        deBruijnNewmanPolymathStieltjesTailMajorant y
    calc
      _ ≤ 24 / |y| ^ 2 := hraw
      _ = deBruijnNewmanPolymathStieltjesTailMajorant y := by
        rw [deBruijnNewmanPolymathStieltjesTailMajorant, abs_of_pos hyPos]
  have hpointwise : ∀ᵐ y ∂volume.restrict (Ioi B),
      Filter.Tendsto (fun n : ℕ => F n y) Filter.atTop (𝓝 0) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : y ≠ 0 := ne_of_gt (hB.trans hy)
    have hshiftAt : Filter.Tendsto
        (fun epsilon : ℝ =>
          deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand z epsilon y)
        (𝓝 0) (𝓝 (deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand z y)) := by
      simpa [deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand] using
        deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand_tendsto hz hy0
    have hshift := hshiftAt.comp
      (deBruijnNewmanPolymathBoydBoundaryEpsilon_tendsto_zero z)
    have haxis : Filter.Tendsto
        (fun _ : ℕ => deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand z y)
        Filter.atTop
        (𝓝 (deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand z y)) :=
      tendsto_const_nhds
    simpa only [F, deBruijnNewmanPolymathBoydBoundaryTraceErrorIntegrand,
      sub_self, Function.comp_def] using hshift.sub haxis
  have hmain := tendsto_integral_filter_of_dominated_convergence bound hmeas hbound
    (deBruijnNewmanPolymathStieltjesTailMajorant_integrableOn hB) hpointwise
  simpa only [F, B, integral_zero] using hmain

theorem tendsto_intervalIntegral_deBruijnNewmanPolymathBoydBoundaryTraceErrorIntegrand_cutoff_height
    {z : ℂ} (hz : 0 < z.re) :
    Filter.Tendsto
      (fun n : ℕ => ∫ y : ℝ in deBruijnNewmanPolymathStieltjesTailCutoff z..
          deBruijnNewmanPolymathBoydBoundaryHeight z n,
        deBruijnNewmanPolymathBoydBoundaryTraceErrorIntegrand z
          (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) y)
      Filter.atTop (𝓝 0) := by
  let B := deBruijnNewmanPolymathStieltjesTailCutoff z
  let F : ℕ → ℝ → ℂ := fun n y =>
    deBruijnNewmanPolymathBoydBoundaryTraceErrorIntegrand z
      (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) y
  let bound : ℝ → ℝ := deBruijnNewmanPolymathStieltjesTailMajorant
  have hB : 0 < B := lt_of_lt_of_le (by norm_num)
    (one_le_deBruijnNewmanPolymathStieltjesTailCutoff z)
  have hmeas : ∀ᶠ n in Filter.atTop,
      AEStronglyMeasurable (F n) (volume.restrict (Ioi B)) := by
    exact Filter.Eventually.of_forall fun n =>
      ContinuousOn.aestronglyMeasurable (fun y hy =>
        (continuousAt_deBruijnNewmanPolymathBoydBoundaryTraceErrorIntegrand hz
          (deBruijnNewmanPolymathBoydBoundaryEpsilon_pos hz n).le
          (deBruijnNewmanPolymathBoydBoundaryEpsilon_lt_re hz n)
          (ne_of_gt (hB.trans hy))).continuousWithinAt) measurableSet_Ioi
  have hbound : ∀ᶠ n in Filter.atTop,
      ∀ᵐ y ∂volume.restrict (Ioi B), ‖F n y‖ ≤ bound y := by
    refine Filter.Eventually.of_forall fun n => ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hyPos : 0 < y := hB.trans hy
    have hyNorm : 1 ≤ |y| := by
      rw [abs_of_pos hyPos]
      exact (one_le_deBruijnNewmanPolymathStieltjesTailCutoff z).trans hy.le
    have hyFar : 2 * ‖z‖ ≤ |y| := by
      rw [abs_of_pos hyPos]
      exact (two_norm_le_deBruijnNewmanPolymathStieltjesTailCutoff z).trans hy.le
    have hraw := norm_deBruijnNewmanPolymathBoydBoundaryTraceErrorIntegrand_le
      hz (deBruijnNewmanPolymathBoydBoundaryEpsilon_pos hz n) hyNorm hyFar
    change ‖deBruijnNewmanPolymathBoydBoundaryTraceErrorIntegrand z
      (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) y‖ ≤
        deBruijnNewmanPolymathStieltjesTailMajorant y
    simpa [deBruijnNewmanPolymathStieltjesTailMajorant, abs_of_pos hyPos] using hraw
  have hboundNonneg : ∀ y ∈ Ioi B, 0 ≤ bound y := by
    intro y hy
    have hyPos : 0 < y := hB.trans hy
    change 0 ≤ 24 / y ^ 2
    positivity
  have hpointwise : ∀ᵐ y ∂volume.restrict (Ioi B),
      Filter.Tendsto (fun n : ℕ => F n y) Filter.atTop (𝓝 0) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : y ≠ 0 := ne_of_gt (hB.trans hy)
    have hshiftAt : Filter.Tendsto
        (fun epsilon : ℝ =>
          deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand z epsilon y)
        (𝓝 0) (𝓝 (deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand z y)) := by
      simpa [deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand] using
        deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand_tendsto hz hy0
    have hshift := hshiftAt.comp
      (deBruijnNewmanPolymathBoydBoundaryEpsilon_tendsto_zero z)
    have haxis : Filter.Tendsto
        (fun _ : ℕ => deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand z y)
        Filter.atTop
        (𝓝 (deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand z y)) :=
      tendsto_const_nhds
    simpa only [F, deBruijnNewmanPolymathBoydBoundaryTraceErrorIntegrand,
      sub_self, Function.comp_def] using hshift.sub haxis
  exact tendsto_intervalIntegral_of_dominated_on_Ioi hmeas hbound hboundNonneg
    (deBruijnNewmanPolymathStieltjesTailMajorant_integrableOn hB) hpointwise
    (deBruijnNewmanPolymathBoydBoundaryHeight_tendsto_atTop z)

theorem tendsto_intervalIntegral_deBruijnNewmanPolymathBoydBoundaryTraceErrorIntegrand_neg_height_cutoff
    {z : ℂ} (hz : 0 < z.re) :
    Filter.Tendsto
      (fun n : ℕ => ∫ y : ℝ in -deBruijnNewmanPolymathBoydBoundaryHeight z n..
          -deBruijnNewmanPolymathStieltjesTailCutoff z,
        deBruijnNewmanPolymathBoydBoundaryTraceErrorIntegrand z
          (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) y)
      Filter.atTop (𝓝 0) := by
  let B := deBruijnNewmanPolymathStieltjesTailCutoff z
  let F : ℕ → ℝ → ℂ := fun n y =>
    deBruijnNewmanPolymathBoydBoundaryTraceErrorIntegrand z
      (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) (-y)
  let bound : ℝ → ℝ := deBruijnNewmanPolymathStieltjesTailMajorant
  have hB : 0 < B := lt_of_lt_of_le (by norm_num)
    (one_le_deBruijnNewmanPolymathStieltjesTailCutoff z)
  have hmeas : ∀ᶠ n in Filter.atTop,
      AEStronglyMeasurable (F n) (volume.restrict (Ioi B)) := by
    exact Filter.Eventually.of_forall fun n =>
      ContinuousOn.aestronglyMeasurable (fun y hy => by
        have hy0 : -y ≠ 0 := neg_ne_zero.mpr (ne_of_gt (hB.trans hy))
        have hneg : ContinuousAt (fun v : ℝ => -v) y := by fun_prop
        have hcomp : ContinuousAt (fun v : ℝ =>
            deBruijnNewmanPolymathBoydBoundaryTraceErrorIntegrand z
              (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) (-v)) y :=
          (continuousAt_deBruijnNewmanPolymathBoydBoundaryTraceErrorIntegrand hz
          (deBruijnNewmanPolymathBoydBoundaryEpsilon_pos hz n).le
          (deBruijnNewmanPolymathBoydBoundaryEpsilon_lt_re hz n) hy0).comp hneg
        exact hcomp.continuousWithinAt) measurableSet_Ioi
  have hbound : ∀ᶠ n in Filter.atTop,
      ∀ᵐ y ∂volume.restrict (Ioi B), ‖F n y‖ ≤ bound y := by
    refine Filter.Eventually.of_forall fun n => ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hyPos : 0 < y := hB.trans hy
    have hyNorm : 1 ≤ |-y| := by
      rw [abs_neg, abs_of_pos hyPos]
      exact (one_le_deBruijnNewmanPolymathStieltjesTailCutoff z).trans hy.le
    have hyFar : 2 * ‖z‖ ≤ |-y| := by
      rw [abs_neg, abs_of_pos hyPos]
      exact (two_norm_le_deBruijnNewmanPolymathStieltjesTailCutoff z).trans hy.le
    have hraw := norm_deBruijnNewmanPolymathBoydBoundaryTraceErrorIntegrand_le
      hz (deBruijnNewmanPolymathBoydBoundaryEpsilon_pos hz n) hyNorm hyFar
    change ‖deBruijnNewmanPolymathBoydBoundaryTraceErrorIntegrand z
      (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) (-y)‖ ≤
        deBruijnNewmanPolymathStieltjesTailMajorant y
    simpa [deBruijnNewmanPolymathStieltjesTailMajorant, abs_neg,
      abs_of_pos hyPos] using hraw
  have hboundNonneg : ∀ y ∈ Ioi B, 0 ≤ bound y := by
    intro y hy
    have hyPos : 0 < y := hB.trans hy
    change 0 ≤ 24 / y ^ 2
    positivity
  have hpointwise : ∀ᵐ y ∂volume.restrict (Ioi B),
      Filter.Tendsto (fun n : ℕ => F n y) Filter.atTop (𝓝 0) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : -y ≠ 0 := neg_ne_zero.mpr (ne_of_gt (hB.trans hy))
    have hshiftAt : Filter.Tendsto
        (fun epsilon : ℝ =>
          deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand z epsilon (-y))
        (𝓝 0) (𝓝 (deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand z (-y))) := by
      simpa [deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand] using
        deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand_tendsto hz hy0
    have hshift := hshiftAt.comp
      (deBruijnNewmanPolymathBoydBoundaryEpsilon_tendsto_zero z)
    have haxis : Filter.Tendsto
        (fun _ : ℕ => deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand z (-y))
        Filter.atTop
        (𝓝 (deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand z (-y))) :=
      tendsto_const_nhds
    simpa only [F, deBruijnNewmanPolymathBoydBoundaryTraceErrorIntegrand,
      sub_self, Function.comp_def] using hshift.sub haxis
  have hpositive := tendsto_intervalIntegral_of_dominated_on_Ioi hmeas hbound
    hboundNonneg (deBruijnNewmanPolymathStieltjesTailMajorant_integrableOn hB)
    hpointwise (deBruijnNewmanPolymathBoydBoundaryHeight_tendsto_atTop z)
  have heq : (fun n : ℕ => ∫ y : ℝ in B..
        deBruijnNewmanPolymathBoydBoundaryHeight z n, F n y) =
      (fun n : ℕ => ∫ y : ℝ in -deBruijnNewmanPolymathBoydBoundaryHeight z n..-B,
        deBruijnNewmanPolymathBoydBoundaryTraceErrorIntegrand z
          (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) y) := by
    funext n
    simpa only [F] using (intervalIntegral.integral_comp_neg
      (f := deBruijnNewmanPolymathBoydBoundaryTraceErrorIntegrand z
        (deBruijnNewmanPolymathBoydBoundaryEpsilon z n))
      (a := B) (b := deBruijnNewmanPolymathBoydBoundaryHeight z n))
  rw [heq] at hpositive
  exact hpositive

theorem deBruijnNewmanPolymathBoydBoundaryTailResidual_tendsto_cutoff
    {z : ℂ} (hz : 0 < z.re) :
    Filter.Tendsto
      (fun n : ℕ => deBruijnNewmanPolymathBoydBoundaryTailResidual z
        (deBruijnNewmanPolymathBoydBoundaryEpsilon z n)
        (deBruijnNewmanPolymathStieltjesTailCutoff z)
        (deBruijnNewmanPolymathBoydBoundaryHeight z n))
      Filter.atTop (𝓝 0) := by
  have hneg :=
    tendsto_intervalIntegral_deBruijnNewmanPolymathBoydBoundaryTraceErrorIntegrand_neg_height_cutoff
      hz
  have hpos :=
    tendsto_intervalIntegral_deBruijnNewmanPolymathBoydBoundaryTraceErrorIntegrand_cutoff_height
      hz
  have hconst : Filter.Tendsto
      (fun _ : ℕ => -(1 / (2 * Real.pi * Complex.I * z))) Filter.atTop
      (𝓝 (-(1 / (2 * Real.pi * Complex.I * z)))) := tendsto_const_nhds
  simpa [deBruijnNewmanPolymathBoydBoundaryTailResidual,
    deBruijnNewmanPolymathBoydBoundarySegmentResidual] using
      (hconst.mul hneg).add (hconst.mul hpos)

theorem deBruijnNewmanPolymathBoydBoundaryTraceDiscrepancy_tendsto_zero
    {z : ℂ} (hz : 0 < z.re) :
    Filter.Tendsto (deBruijnNewmanPolymathBoydBoundaryTraceDiscrepancy z)
      Filter.atTop (𝓝 0) := by
  apply (deBruijnNewmanPolymathBoydBoundaryTrace_tendsto_iff_tail hz
    (lt_of_lt_of_le (by norm_num)
      (one_le_deBruijnNewmanPolymathStieltjesTailCutoff z))).mpr
  exact deBruijnNewmanPolymathBoydBoundaryTailResidual_tendsto_cutoff hz

theorem deBruijnNewmanPolymathBoydFiniteBoundaryProjection_tendsto_jump
    {z : ℂ} (hz : 0 < z.re) :
    Filter.Tendsto
      (fun n : ℕ => deBruijnNewmanPolymathBoydFiniteBoundaryProjection z
        (deBruijnNewmanPolymathBoydBoundaryEpsilon z n)
        (deBruijnNewmanPolymathBoydBoundaryHeight z n))
      Filter.atTop
      (𝓝 (deBruijnNewmanPolymathBoydBoundaryJumpProjection z)) := by
  exact (deBruijnNewmanPolymathBoydBoundaryTrace_tendsto_iff_discrepancy hz).mpr
    (deBruijnNewmanPolymathBoydBoundaryTraceDiscrepancy_tendsto_zero hz)

private theorem norm_deBruijnNewmanPolymathBoydR2RightEdgeResidual_canonical_le
    {z : ℂ} (hz : 0 < z.re) (n : ℕ)
    (hfar : 2 * ‖z‖ ≤ (n : ℝ) + 1) :
    ‖deBruijnNewmanPolymathBoydR2RightEdgeResidual z
        (deBruijnNewmanPolymathBoydBoundaryEpsilon z n)
        (deBruijnNewmanPolymathBoydBoundaryRadius z n)
        (deBruijnNewmanPolymathBoydBoundaryHeight z n)‖ ≤
      24 * (‖z‖ + ((n : ℝ) + 1)) / ((n : ℝ) + 1) ^ 2 := by
  let u : ℝ := (n : ℝ) + 1
  let epsilon := deBruijnNewmanPolymathBoydBoundaryEpsilon z n
  let R := deBruijnNewmanPolymathBoydBoundaryRadius z n
  let T := deBruijnNewmanPolymathBoydBoundaryHeight z n
  obtain ⟨hepsilon, _, _, _, _, hepsilonR⟩ :=
    deBruijnNewmanPolymathBoydBoundaryCanonical_geometry hz n
  have huOne : 1 ≤ u := by
    dsimp [u]
    exact le_add_of_nonneg_left (Nat.cast_nonneg n)
  have huPos : 0 < u := lt_of_lt_of_le (by norm_num) huOne
  have hreNorm : z.re ≤ ‖z‖ :=
    (le_abs_self z.re).trans (Complex.abs_re_le_norm z)
  have himNorm : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
  have huR : u ≤ R := by
    dsimp [u, R, deBruijnNewmanPolymathBoydBoundaryRadius]
    linarith
  have hRT : R ≤ ‖z‖ + u := by
    dsimp [u, R, deBruijnNewmanPolymathBoydBoundaryRadius]
    linarith
  have huT : u ≤ T := by
    dsimp [u, T, deBruijnNewmanPolymathBoydBoundaryHeight]
    linarith [abs_nonneg z.im]
  have hTupper : T ≤ ‖z‖ + u := by
    dsimp [u, T, deBruijnNewmanPolymathBoydBoundaryHeight]
    linarith
  have hRPos : 0 < R := huPos.trans_le huR
  have hTPos : 0 < T := huPos.trans_le huT
  have hepsilonR' : epsilon ≤ R := by simpa [epsilon, R] using hepsilonR.le
  have hlength : |R - epsilon| ≤ ‖z‖ + u := by
    rw [abs_of_nonneg (sub_nonneg.mpr hepsilonR')]
    linarith [hepsilon]
  have hhorizontal (S : ℝ) (hS : |S| = T) :
      ‖∫ x : ℝ in epsilon..R,
        deBruijnNewmanPolymathBoydR2CauchyWeight
            (x + S * Complex.I) /
          (x + S * Complex.I - z)‖ ≤
        (6 / u ^ 2) * |R - epsilon| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hx' := uIoc_subset_uIcc hx
    rw [uIcc_of_le hepsilonR'] at hx'
    let w : ℂ := x + S * Complex.I
    have hwRe : 0 < w.re := by
      simpa [w] using hepsilon.trans_le hx'.1
    have huNorm : u ≤ ‖w‖ := by
      calc
        u ≤ T := huT
        _ = |w.im| := by simpa [w] using hS.symm
        _ ≤ ‖w‖ := Complex.abs_im_le_norm w
    have hkernel := norm_deBruijnNewmanPolymathBoydR2CauchyWeight_div_sub_le_six
      (z := z) hwRe (huOne.trans huNorm) (hfar.trans huNorm)
    calc
      ‖deBruijnNewmanPolymathBoydR2CauchyWeight w / (w - z)‖ ≤
          6 / ‖w‖ ^ 2 := hkernel
      _ ≤ 6 / u ^ 2 := by
        exact div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos huPos)
          (pow_le_pow_left₀ huPos.le huNorm 2)
  have hhorizontalMajor : (6 / u ^ 2) * |R - epsilon| ≤
      6 * (‖z‖ + u) / u ^ 2 := by
    calc
      (6 / u ^ 2) * |R - epsilon| ≤
          (6 / u ^ 2) * (‖z‖ + u) :=
        mul_le_mul_of_nonneg_left hlength (by positivity)
      _ = 6 * (‖z‖ + u) / u ^ 2 := by ring
  have hbottom :
      ‖∫ x : ℝ in epsilon..R,
        deBruijnNewmanPolymathBoydR2CauchyWeight
            (x + (-T) * Complex.I) /
          (x + (-T) * Complex.I - z)‖ ≤
        6 * (‖z‖ + u) / u ^ 2 :=
    by
      simpa only [Complex.ofReal_neg] using
        (hhorizontal (-T) (by rw [abs_neg, abs_of_pos hTPos])).trans hhorizontalMajor
  have htop :
      ‖∫ x : ℝ in epsilon..R,
        deBruijnNewmanPolymathBoydR2CauchyWeight
            (x + T * Complex.I) /
          (x + T * Complex.I - z)‖ ≤
        6 * (‖z‖ + u) / u ^ 2 :=
    (hhorizontal T (abs_of_pos hTPos)).trans hhorizontalMajor
  have hverticalRaw :
      ‖∫ y : ℝ in -T..T,
        deBruijnNewmanPolymathBoydR2CauchyWeight
            (R + y * Complex.I) /
          (R + y * Complex.I - z)‖ ≤
        (6 / u ^ 2) * |T - (-T)| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro y _
    let w : ℂ := R + y * Complex.I
    have hwRe : 0 < w.re := by simpa [w] using hRPos
    have huNorm : u ≤ ‖w‖ := by
      calc
        u ≤ R := huR
        _ = |w.re| := by simp [w, abs_of_pos hRPos]
        _ ≤ ‖w‖ := Complex.abs_re_le_norm w
    have hkernel := norm_deBruijnNewmanPolymathBoydR2CauchyWeight_div_sub_le_six
      (z := z) hwRe (huOne.trans huNorm) (hfar.trans huNorm)
    calc
      ‖deBruijnNewmanPolymathBoydR2CauchyWeight w / (w - z)‖ ≤
          6 / ‖w‖ ^ 2 := hkernel
      _ ≤ 6 / u ^ 2 := by
        exact div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos huPos)
          (pow_le_pow_left₀ huPos.le huNorm 2)
  have hvertical :
      ‖Complex.I * (∫ y : ℝ in -T..T,
        deBruijnNewmanPolymathBoydR2CauchyWeight
            (R + y * Complex.I) /
          (R + y * Complex.I - z))‖ ≤
        12 * (‖z‖ + u) / u ^ 2 := by
    rw [norm_mul, norm_I, one_mul]
    calc
      _ ≤ (6 / u ^ 2) * |T - (-T)| := hverticalRaw
      _ = 12 * T / u ^ 2 := by rw [abs_of_pos (by linarith : 0 < T - -T)]; ring
      _ ≤ 12 * (‖z‖ + u) / u ^ 2 := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hTupper (by norm_num)) (sq_nonneg u)
  rw [deBruijnNewmanPolymathBoydR2RightEdgeResidual]
  change ‖(∫ x : ℝ in epsilon..R,
      deBruijnNewmanPolymathBoydR2CauchyWeight (x + -T * Complex.I) /
        (x + -T * Complex.I - z)) -
      (∫ x : ℝ in epsilon..R,
        deBruijnNewmanPolymathBoydR2CauchyWeight (x + T * Complex.I) /
          (x + T * Complex.I - z)) +
      Complex.I * (∫ y : ℝ in -T..T,
        deBruijnNewmanPolymathBoydR2CauchyWeight (R + y * Complex.I) /
          (R + y * Complex.I - z))‖ ≤ _
  calc
    _ ≤ ‖∫ x : ℝ in epsilon..R,
          deBruijnNewmanPolymathBoydR2CauchyWeight (x + -T * Complex.I) /
            (x + -T * Complex.I - z)‖ +
        ‖∫ x : ℝ in epsilon..R,
          deBruijnNewmanPolymathBoydR2CauchyWeight (x + T * Complex.I) /
            (x + T * Complex.I - z)‖ +
        ‖Complex.I * (∫ y : ℝ in -T..T,
          deBruijnNewmanPolymathBoydR2CauchyWeight (R + y * Complex.I) /
            (R + y * Complex.I - z))‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ 6 * (‖z‖ + u) / u ^ 2 + 6 * (‖z‖ + u) / u ^ 2 +
        12 * (‖z‖ + u) / u ^ 2 := add_le_add (add_le_add hbottom htop) hvertical
    _ = 24 * (‖z‖ + ((n : ℝ) + 1)) / ((n : ℝ) + 1) ^ 2 := by
      dsimp [u]
      ring

private theorem norm_deBruijnNewmanPolymathBoydInverseR2LeftEdgeResidual_canonical_le
    {z : ℂ} (hz : 0 < z.re) (n : ℕ)
    (hfar : 2 * ‖z‖ ≤ (n : ℝ) + 1) :
    ‖deBruijnNewmanPolymathBoydInverseR2LeftEdgeResidual z
        (deBruijnNewmanPolymathBoydBoundaryEpsilon z n)
        (deBruijnNewmanPolymathBoydBoundaryRadius z n)
        (deBruijnNewmanPolymathBoydBoundaryHeight z n)‖ ≤
      24 * (‖z‖ + ((n : ℝ) + 1)) / ((n : ℝ) + 1) ^ 2 := by
  let u : ℝ := (n : ℝ) + 1
  let epsilon := deBruijnNewmanPolymathBoydBoundaryEpsilon z n
  let R := deBruijnNewmanPolymathBoydBoundaryRadius z n
  let T := deBruijnNewmanPolymathBoydBoundaryHeight z n
  obtain ⟨hepsilon, _, _, _, _, hepsilonR⟩ :=
    deBruijnNewmanPolymathBoydBoundaryCanonical_geometry hz n
  have huOne : 1 ≤ u := by
    dsimp [u]
    exact le_add_of_nonneg_left (Nat.cast_nonneg n)
  have huPos : 0 < u := lt_of_lt_of_le (by norm_num) huOne
  have hreNorm : z.re ≤ ‖z‖ :=
    (le_abs_self z.re).trans (Complex.abs_re_le_norm z)
  have himNorm : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
  have huR : u ≤ R := by
    dsimp [u, R, deBruijnNewmanPolymathBoydBoundaryRadius]
    linarith
  have hRT : R ≤ ‖z‖ + u := by
    dsimp [u, R, deBruijnNewmanPolymathBoydBoundaryRadius]
    linarith
  have huT : u ≤ T := by
    dsimp [u, T, deBruijnNewmanPolymathBoydBoundaryHeight]
    linarith [abs_nonneg z.im]
  have hTupper : T ≤ ‖z‖ + u := by
    dsimp [u, T, deBruijnNewmanPolymathBoydBoundaryHeight]
    linarith
  have hRPos : 0 < R := huPos.trans_le huR
  have hTPos : 0 < T := huPos.trans_le huT
  have hepsilonR' : epsilon ≤ R := by simpa [epsilon, R] using hepsilonR.le
  have hlength : |(-epsilon) - (-R)| ≤ ‖z‖ + u := by
    have heq : (-epsilon) - (-R) = R - epsilon := by ring
    rw [heq, abs_of_nonneg (sub_nonneg.mpr hepsilonR')]
    linarith [hepsilon]
  have hhorizontal (S : ℝ) (hS : |S| = T) :
      ‖∫ x : ℝ in -R..-epsilon,
        deBruijnNewmanPolymathBoydInverseR2CauchyWeight
            (x + S * Complex.I) /
          (x + S * Complex.I - z)‖ ≤
        (6 / u ^ 2) * |(-epsilon) - (-R)| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hx' := uIoc_subset_uIcc hx
    rw [uIcc_of_le (neg_le_neg hepsilonR')] at hx'
    let w : ℂ := x + S * Complex.I
    have hwRe : w.re < 0 := by
      simpa [w] using hx'.2.trans_lt (neg_neg_of_pos hepsilon)
    have huNorm : u ≤ ‖w‖ := by
      calc
        u ≤ T := huT
        _ = |w.im| := by simpa [w] using hS.symm
        _ ≤ ‖w‖ := Complex.abs_im_le_norm w
    have hkernel :=
      norm_deBruijnNewmanPolymathBoydInverseR2CauchyWeight_div_sub_le_six
        (z := z) hwRe (huOne.trans huNorm) (hfar.trans huNorm)
    calc
      ‖deBruijnNewmanPolymathBoydInverseR2CauchyWeight w / (w - z)‖ ≤
          6 / ‖w‖ ^ 2 := hkernel
      _ ≤ 6 / u ^ 2 := by
        exact div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos huPos)
          (pow_le_pow_left₀ huPos.le huNorm 2)
  have hhorizontalMajor : (6 / u ^ 2) * |(-epsilon) - (-R)| ≤
      6 * (‖z‖ + u) / u ^ 2 := by
    calc
      (6 / u ^ 2) * |(-epsilon) - (-R)| ≤
          (6 / u ^ 2) * (‖z‖ + u) :=
        mul_le_mul_of_nonneg_left hlength (by positivity)
      _ = 6 * (‖z‖ + u) / u ^ 2 := by ring
  have hbottom :
      ‖∫ x : ℝ in -R..-epsilon,
        deBruijnNewmanPolymathBoydInverseR2CauchyWeight
            (x + (-T) * Complex.I) /
          (x + (-T) * Complex.I - z)‖ ≤
        6 * (‖z‖ + u) / u ^ 2 := by
    simpa only [Complex.ofReal_neg] using
      (hhorizontal (-T) (by rw [abs_neg, abs_of_pos hTPos])).trans hhorizontalMajor
  have htop :
      ‖∫ x : ℝ in -R..-epsilon,
        deBruijnNewmanPolymathBoydInverseR2CauchyWeight
            (x + T * Complex.I) /
          (x + T * Complex.I - z)‖ ≤
        6 * (‖z‖ + u) / u ^ 2 :=
    (hhorizontal T (abs_of_pos hTPos)).trans hhorizontalMajor
  have hverticalRaw :
      ‖∫ y : ℝ in -T..T,
        deBruijnNewmanPolymathBoydInverseR2CauchyWeight
            (-R + y * Complex.I) /
          (-R + y * Complex.I - z)‖ ≤
        (6 / u ^ 2) * |T - (-T)| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro y _
    let w : ℂ := -R + y * Complex.I
    have hwRe : w.re < 0 := by simpa [w] using neg_neg_of_pos hRPos
    have huNorm : u ≤ ‖w‖ := by
      calc
        u ≤ R := huR
        _ = |w.re| := by simp [w, abs_of_pos hRPos]
        _ ≤ ‖w‖ := Complex.abs_re_le_norm w
    have hkernel :=
      norm_deBruijnNewmanPolymathBoydInverseR2CauchyWeight_div_sub_le_six
        (z := z) hwRe (huOne.trans huNorm) (hfar.trans huNorm)
    calc
      ‖deBruijnNewmanPolymathBoydInverseR2CauchyWeight w / (w - z)‖ ≤
          6 / ‖w‖ ^ 2 := hkernel
      _ ≤ 6 / u ^ 2 := by
        exact div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos huPos)
          (pow_le_pow_left₀ huPos.le huNorm 2)
  have hvertical :
      ‖Complex.I * (∫ y : ℝ in -T..T,
        deBruijnNewmanPolymathBoydInverseR2CauchyWeight
            (-R + y * Complex.I) /
          (-R + y * Complex.I - z))‖ ≤
        12 * (‖z‖ + u) / u ^ 2 := by
    rw [norm_mul, norm_I, one_mul]
    calc
      _ ≤ (6 / u ^ 2) * |T - (-T)| := hverticalRaw
      _ = 12 * T / u ^ 2 := by rw [abs_of_pos (by linarith : 0 < T - -T)]; ring
      _ ≤ 12 * (‖z‖ + u) / u ^ 2 := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hTupper (by norm_num)) (sq_nonneg u)
  rw [deBruijnNewmanPolymathBoydInverseR2LeftEdgeResidual]
  change ‖-(∫ x : ℝ in -R..-epsilon,
      deBruijnNewmanPolymathBoydInverseR2CauchyWeight (x + -T * Complex.I) /
        (x + -T * Complex.I - z)) +
      (∫ x : ℝ in -R..-epsilon,
        deBruijnNewmanPolymathBoydInverseR2CauchyWeight (x + T * Complex.I) /
          (x + T * Complex.I - z)) +
      Complex.I * (∫ y : ℝ in -T..T,
        deBruijnNewmanPolymathBoydInverseR2CauchyWeight (-R + y * Complex.I) /
          (-R + y * Complex.I - z))‖ ≤ _
  calc
    _ ≤ ‖-(∫ x : ℝ in -R..-epsilon,
          deBruijnNewmanPolymathBoydInverseR2CauchyWeight (x + -T * Complex.I) /
            (x + -T * Complex.I - z))‖ +
        ‖∫ x : ℝ in -R..-epsilon,
          deBruijnNewmanPolymathBoydInverseR2CauchyWeight (x + T * Complex.I) /
            (x + T * Complex.I - z)‖ +
        ‖Complex.I * (∫ y : ℝ in -T..T,
          deBruijnNewmanPolymathBoydInverseR2CauchyWeight (-R + y * Complex.I) /
            (-R + y * Complex.I - z))‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 6 * (‖z‖ + u) / u ^ 2 + 6 * (‖z‖ + u) / u ^ 2 +
        12 * (‖z‖ + u) / u ^ 2 := by
      simpa only [norm_neg] using add_le_add (add_le_add hbottom htop) hvertical
    _ = 24 * (‖z‖ + ((n : ℝ) + 1)) / ((n : ℝ) + 1) ^ 2 := by
      dsimp [u]
      ring

private theorem deBruijnNewmanPolymathStieltjesEdgeMajorant_tendsto_zero
    (z : ℂ) :
    Filter.Tendsto
      (fun n : ℕ => 24 * (‖z‖ + ((n : ℝ) + 1)) / ((n : ℝ) + 1) ^ 2)
      Filter.atTop (𝓝 0) := by
  let u : ℕ → ℝ := fun n => (n : ℝ) + 1
  have hu : Filter.Tendsto u Filter.atTop Filter.atTop := by
    exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hinv : Filter.Tendsto (fun n : ℕ => (u n)⁻¹) Filter.atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hu
  have hraw : Filter.Tendsto
      (fun n : ℕ => 24 * (‖z‖ * ((u n)⁻¹) ^ 2 + (u n)⁻¹))
      Filter.atTop (𝓝 0) := by
    have hnorm : Filter.Tendsto (fun _ : ℕ => ‖z‖) Filter.atTop (𝓝 ‖z‖) :=
      tendsto_const_nhds
    have htwentyfour : Filter.Tendsto (fun _ : ℕ => (24 : ℝ))
        Filter.atTop (𝓝 24) := tendsto_const_nhds
    have hinside := (hnorm.mul (hinv.pow 2)).add hinv
    simpa using htwentyfour.mul hinside
  convert hraw using 1
  funext n
  have huPos : 0 < u n := by
    dsimp [u]
    positivity
  field_simp [u, huPos.ne']
  ring

theorem deBruijnNewmanPolymathBoydR2RightEdgeResidual_tendsto_zero
    {z : ℂ} (hz : 0 < z.re) :
    Filter.Tendsto
      (fun n : ℕ => deBruijnNewmanPolymathBoydR2RightEdgeResidual z
        (deBruijnNewmanPolymathBoydBoundaryEpsilon z n)
        (deBruijnNewmanPolymathBoydBoundaryRadius z n)
        (deBruijnNewmanPolymathBoydBoundaryHeight z n))
      Filter.atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hu : Filter.Tendsto (fun n : ℕ => (n : ℝ) + 1)
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hfar : ∀ᶠ n : ℕ in Filter.atTop, 2 * ‖z‖ ≤ (n : ℝ) + 1 :=
    Filter.tendsto_atTop.1 hu (2 * ‖z‖)
  have hbound : ∀ᶠ n : ℕ in Filter.atTop,
      ‖deBruijnNewmanPolymathBoydR2RightEdgeResidual z
        (deBruijnNewmanPolymathBoydBoundaryEpsilon z n)
        (deBruijnNewmanPolymathBoydBoundaryRadius z n)
        (deBruijnNewmanPolymathBoydBoundaryHeight z n)‖ ≤
          24 * (‖z‖ + ((n : ℝ) + 1)) / ((n : ℝ) + 1) ^ 2 := by
    filter_upwards [hfar] with n hn
    exact norm_deBruijnNewmanPolymathBoydR2RightEdgeResidual_canonical_le hz n hn
  exact squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _) hbound
    (deBruijnNewmanPolymathStieltjesEdgeMajorant_tendsto_zero z)

theorem deBruijnNewmanPolymathBoydInverseR2LeftEdgeResidual_tendsto_zero
    {z : ℂ} (hz : 0 < z.re) :
    Filter.Tendsto
      (fun n : ℕ => deBruijnNewmanPolymathBoydInverseR2LeftEdgeResidual z
        (deBruijnNewmanPolymathBoydBoundaryEpsilon z n)
        (deBruijnNewmanPolymathBoydBoundaryRadius z n)
        (deBruijnNewmanPolymathBoydBoundaryHeight z n))
      Filter.atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hu : Filter.Tendsto (fun n : ℕ => (n : ℝ) + 1)
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hfar : ∀ᶠ n : ℕ in Filter.atTop, 2 * ‖z‖ ≤ (n : ℝ) + 1 :=
    Filter.tendsto_atTop.1 hu (2 * ‖z‖)
  have hbound : ∀ᶠ n : ℕ in Filter.atTop,
      ‖deBruijnNewmanPolymathBoydInverseR2LeftEdgeResidual z
        (deBruijnNewmanPolymathBoydBoundaryEpsilon z n)
        (deBruijnNewmanPolymathBoydBoundaryRadius z n)
        (deBruijnNewmanPolymathBoydBoundaryHeight z n)‖ ≤
          24 * (‖z‖ + ((n : ℝ) + 1)) / ((n : ℝ) + 1) ^ 2 := by
    filter_upwards [hfar] with n hn
    exact norm_deBruijnNewmanPolymathBoydInverseR2LeftEdgeResidual_canonical_le hz n hn
  exact squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _) hbound
    (deBruijnNewmanPolymathStieltjesEdgeMajorant_tendsto_zero z)

theorem deBruijnNewmanPolymathBoydBoundaryTailResidual_tendsto_canonical
    {z : ℂ} (hz : 0 < z.re) {A : ℝ} (hA : 0 < A) :
    Filter.Tendsto
      (fun n : ℕ => deBruijnNewmanPolymathBoydBoundaryTailResidual z
        (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) A
        (deBruijnNewmanPolymathBoydBoundaryHeight z n))
      Filter.atTop (𝓝 0) := by
  exact (deBruijnNewmanPolymathBoydBoundaryTrace_tendsto_iff_tail hz hA).mp
    (deBruijnNewmanPolymathBoydBoundaryTraceDiscrepancy_tendsto_zero hz)

theorem deBruijnNewmanPolymathBoydBoundaryDispersionLimits :
    deBruijnNewmanPolymathBoydBoundaryDispersionLimitCertificate := by
  intro z hz
  exact ⟨deBruijnNewmanPolymathBoydR2RightEdgeResidual_tendsto_zero hz,
    deBruijnNewmanPolymathBoydInverseR2LeftEdgeResidual_tendsto_zero hz,
    deBruijnNewmanPolymathBoydFiniteBoundaryProjection_tendsto_jump hz⟩

theorem deBruijnNewmanPolymathGammaStirlingR2_eq_boyd
    {z : ℂ} (hz : 0 < z.re) :
    deBruijnNewmanPolymathGammaStirlingR2 z =
      deBruijnNewmanPolymathBoydR2Integral z :=
  deBruijnNewmanPolymathGammaStirlingR2_eq_boyd_of_boundaryDispersionLimits
    deBruijnNewmanPolymathBoydBoundaryDispersionLimits hz

/-- Auditable Loop 31 certificate: Stieltjes equation (13), explicit second-order bounds, all
three boundary-dispersion limits, and Boyd--Nemes equation (15). -/
def deBruijnNewmanPolymathStieltjesScaledGammaCertificateStatement : Prop :=
  (∀ z : ℂ, 0 < z.re →
    deBruijnNewmanPolymathScaledGamma z =
      Complex.exp (deBruijnNewmanPolymathStieltjesLogRemainder z)) ∧
  (∀ z : ℂ, 0 < z.re →
    ‖deBruijnNewmanPolymathStieltjesLogRemainder z - 1 / (12 * z)‖ ≤
      2 / ‖z‖ ^ 2) ∧
  (∀ z : ℂ, 0 < z.re → 1 ≤ ‖z‖ →
    ‖deBruijnNewmanPolymathGammaStirlingR2 z‖ ≤ 3 / ‖z‖ ^ 2) ∧
  (∀ z : ℂ, 0 < z.re → 1 ≤ ‖z‖ →
    ‖deBruijnNewmanPolymathScaledGammaInverseR2 z‖ ≤ 3 / ‖z‖ ^ 2) ∧
  (∀ z : ℂ, 0 < z.re → ∀ A : ℝ, 0 < A →
    Filter.Tendsto
      (fun n : ℕ => deBruijnNewmanPolymathBoydBoundaryTailResidual z
        (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) A
        (deBruijnNewmanPolymathBoydBoundaryHeight z n))
      Filter.atTop (𝓝 0)) ∧
  (∀ z : ℂ, 0 < z.re →
    Filter.Tendsto
      (fun n : ℕ => deBruijnNewmanPolymathBoydFiniteBoundaryProjection z
        (deBruijnNewmanPolymathBoydBoundaryEpsilon z n)
        (deBruijnNewmanPolymathBoydBoundaryHeight z n))
      Filter.atTop (𝓝 (deBruijnNewmanPolymathBoydBoundaryJumpProjection z))) ∧
  deBruijnNewmanPolymathBoydBoundaryDispersionLimitCertificate ∧
  (∀ z : ℂ, 0 < z.re →
    deBruijnNewmanPolymathGammaStirlingR2 z =
      deBruijnNewmanPolymathBoydR2Integral z)

theorem deBruijnNewmanPolymathStieltjesScaledGammaCertificate :
    deBruijnNewmanPolymathStieltjesScaledGammaCertificateStatement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_,
    deBruijnNewmanPolymathBoydBoundaryDispersionLimits, ?_⟩
  · exact fun _ hz => deBruijnNewmanPolymath_scaledGamma_eq_exp_stieltjes hz
  · exact fun _ hz =>
      deBruijnNewmanPolymath_stieltjesLogRemainder_sub_first_norm_le hz
  · exact fun _ hz hnorm =>
      deBruijnNewmanPolymathGammaStirlingR2_norm_le_three hz hnorm
  · exact fun _ hz hnorm =>
      deBruijnNewmanPolymathScaledGammaInverseR2_norm_le_three hz hnorm
  · exact fun _ hz _ hA =>
      deBruijnNewmanPolymathBoydBoundaryTailResidual_tendsto_canonical hz hA
  · exact fun _ hz =>
      deBruijnNewmanPolymathBoydFiniteBoundaryProjection_tendsto_jump hz
  · exact fun _ hz => deBruijnNewmanPolymathGammaStirlingR2_eq_boyd hz

end

end LeanLab.Riemann
