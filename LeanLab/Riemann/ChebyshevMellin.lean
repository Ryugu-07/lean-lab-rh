import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Chebyshev's psi function and ordered Dirichlet convergence

Mathlib's `LSeriesSummable` means absolute convergence. This file keeps naturally ordered
Dirichlet partial sums separate, so cancellation in the Chebyshev error is not erased.
-/

namespace LeanLab.Riemann

open Asymptotics Complex Finset Filter MeasureTheory Set
open scoped ArithmeticFunction LSeries.notation Topology

/-- The naturally ordered Dirichlet partial sum over `1, ..., N`. -/
noncomputable def orderedDirichletPartialSum
    (f : ℕ → ℂ) (s : ℂ) (N : ℕ) : ℂ :=
  ∑ k ∈ Icc 1 N, f k * (k : ℂ) ^ (-s)

/-- The naturally ordered Dirichlet series converges to the displayed value. -/
def OrderedDirichletHasSum (f : ℕ → ℂ) (s value : ℂ) : Prop :=
  Tendsto (orderedDirichletPartialSum f s) atTop (𝓝 value)

private theorem sum_Icc_zero_update_eq_sum_Icc_one
    (f : ℕ → ℂ) (n : ℕ) :
    (∑ k ∈ Icc 0 n, if k = 0 then 0 else f k) =
      ∑ k ∈ Icc 1 n, f k := by
  rw [Icc_eq_cons_Ioc n.zero_le, sum_cons, if_pos, zero_add,
    ← Icc_add_one_left_eq_Ioc]
  · exact sum_congr rfl fun k hk => by
      rw [if_neg (zero_lt_one.trans_le (mem_Icc.mp hk).1).ne']
  · simp

private theorem orderedDirichletPartialSum_eq_sum_Icc_zero_update
    (f : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    orderedDirichletPartialSum f s n =
      ∑ k ∈ Icc 0 n,
        (k : ℂ) ^ (-s) * (if k = 0 then 0 else f k) := by
  rw [orderedDirichletPartialSum, Icc_eq_cons_Ioc n.zero_le, sum_cons,
    if_pos, mul_zero, zero_add, ← Icc_add_one_left_eq_Ioc]
  · apply sum_congr rfl
    intro k hk
    rw [if_neg (zero_lt_one.trans_le (mem_Icc.mp hk).1).ne']
    ring
  · simp

/-- An `O(N^r)` bound for complex partial sums gives the exact Abel limit of the naturally
ordered Dirichlet series on `Re(s) > r`. This is conditional convergence, not Mathlib's
`LSeriesSummable`. -/
theorem orderedDirichletHasSum_mellin_of_sum_isBigO
    (f : ℕ → ℂ) {r : ℝ}
    (hO : (fun n => ∑ k ∈ Icc 1 n, f k) =O[atTop]
      fun n => (n : ℝ) ^ r)
    (hr : 0 ≤ r) {s : ℂ} (hs : r < s.re) :
    OrderedDirichletHasSum f s
      (s * ∫ t in Ioi (1 : ℝ),
        (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(s + 1))) := by
  let c : ℕ → ℂ := fun n => if n = 0 then 0 else f n
  let w : ℝ → ℂ := fun t => (t : ℂ) ^ (-s)
  have hs0 : s ≠ 0 := ne_zero_of_re_pos (hr.trans_lt hs)
  have hpowInt : -(s.re + 1) + r < -1 := by
    linarith
  have hwDiff :
      ∀ t ∈ Ici (1 : ℝ), DifferentiableAt ℝ w t := by
    intro t ht
    exact differentiableAt_id.ofReal_cpow_const
      (zero_lt_one.trans_le ht).ne' (neg_ne_zero.mpr hs0)
  have hwInt : LocallyIntegrableOn (deriv w) (Ici (1 : ℝ)) := by
    refine (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi
      (integrableOn_Ioi_deriv_ofReal_cpow zero_lt_one ?_)).locallyIntegrableOn
    simpa using hr.trans_lt hs
  have hO' :
      (fun n => ∑ k ∈ Icc 0 n, c k) =O[atTop]
        fun n => (n : ℝ) ^ r := by
    simpa only [c, sum_Icc_zero_update_eq_sum_Icc_one] using hO
  have hboundary :
      Tendsto
        (fun n : ℕ => w n * ∑ k ∈ Icc 0 n, c k)
        atTop (𝓝 0) := by
    have hlim :
        Tendsto (fun n : ℕ => (n : ℝ) ^ (-(s.re - r)))
          atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by rwa [sub_pos])).comp
        tendsto_natCast_atTop_atTop
    refine
      (IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow
        (-s.re) _ _ ?_ hO' ?_).trans_tendsto hlim
    · simpa only [w, neg_re] using
        (isBigO_norm_left.mp
          (norm_ofReal_cpow_eventually_eq_atTop (-s)).isBigO.natCast_atTop)
    · linarith
  have hderivO :
      (fun t =>
        deriv w t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k) =O[atTop]
        fun t => t ^ (-(s.re + 1) + r) := by
    refine .mul_atTop_rpow_of_isBigO_rpow (-(s.re + 1)) r _ ?_ ?_ ?_
    · have hp :
          (fun t : ℝ => t ^ ((-s).re - 1)) =
            fun t : ℝ => t ^ (-(s.re + 1)) := by
          funext t
          congr 1
          simp
          ring
      rw [← hp]
      simpa only [w] using isBigO_deriv_ofReal_cpow_const_atTop (-s)
    · exact (hO'.comp_tendsto tendsto_nat_floor_atTop).trans
        (isEquivalent_nat_floor.isBigO.rpow hr (eventually_ge_atTop 0))
    · rfl
  have hraw :
      Tendsto
        (fun n : ℕ =>
          ∑ k ∈ Icc 0 n, w k * c k)
        atTop
        (𝓝 (0 - ∫ t in Ioi (1 : ℝ),
          deriv w t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k)) :=
    tendsto_sum_mul_atTop_nhds_one_sub_integral₀
      (c := c) (f := w) (by simp [c]) hwDiff hwInt hboundary hderivO
      (integrableAtFilter_rpow_atTop_iff.mpr hpowInt)
  have hvalue :
      0 - ∫ t in Ioi (1 : ℝ),
          deriv w t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k =
        s * ∫ t in Ioi (1 : ℝ),
          (∑ k ∈ Icc 1 ⌊t⌋₊, f k) *
            (t : ℂ) ^ (-(s + 1)) := by
    rw [zero_sub, ← integral_neg, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : t ≠ 0 := (zero_lt_one.trans ht).ne'
    rw [show deriv w t = -s * (t : ℂ) ^ (-s - 1) by
      simpa only [w] using deriv_ofReal_cpow_const ht0 (neg_ne_zero.mpr hs0)]
    rw [sum_Icc_zero_update_eq_sum_Icc_one]
    have hexp : -s - 1 = -(s + 1) := by ring
    rw [hexp]
    ring
  rw [hvalue] at hraw
  change Tendsto (orderedDirichletPartialSum f s) atTop
    (𝓝 (s * ∫ t in Ioi (1 : ℝ),
      (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(s + 1))))
  convert hraw using 1
  funext n
  exact orderedDirichletPartialSum_eq_sum_Icc_zero_update f s n

private theorem sum_range_succ_lseriesTerm_eq_orderedDirichletPartialSum
    (f : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    (∑ k ∈ range (n + 1), LSeries.term f s k) =
      orderedDirichletPartialSum f s n := by
  rw [Nat.range_succ_eq_Icc_zero, Icc_eq_cons_Ioc n.zero_le, sum_cons,
    LSeries.term_zero, zero_add, ← Icc_add_one_left_eq_Ioc,
    orderedDirichletPartialSum]
  apply sum_congr rfl
  intro k hk
  have hk0 : k ≠ 0 :=
    (zero_lt_one.trans_le (mem_Icc.mp hk).1).ne'
  rw [LSeries.term_of_ne_zero hk0, cpow_neg]
  ring

/-- Absolute L-series convergence implies ordered convergence to the same value. The converse is
deliberately absent. -/
theorem orderedDirichletHasSum_of_LSeriesSummable
    {f : ℕ → ℂ} {s : ℂ} (hS : LSeriesSummable f s) :
    OrderedDirichletHasSum f s (LSeries f s) := by
  rw [OrderedDirichletHasSum]
  have h := (tendsto_add_atTop_iff_nat 1).mpr
    hS.hasSum.tendsto_sum_nat
  simpa only [LSeries] using h.congr'
    (Eventually.of_forall fun n =>
      sum_range_succ_lseriesTerm_eq_orderedDirichletPartialSum f s n)

/-- Mathlib's Chebyshev function is exactly the complex von Mangoldt partial sum. -/
theorem chebyshevPsi_eq_sum_vonMangoldt (x : ℝ) :
    (Chebyshev.psi x : ℂ) =
      ∑ k ∈ Icc 1 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt k : ℂ) := by
  rw [Chebyshev.psi, ← Icc_add_one_left_eq_Ioc]
  push_cast
  rfl

/-- The real Chebyshev partial sums have unconditional linear growth. -/
theorem chebyshevPsi_nat_isBigO :
    (fun n : ℕ => Chebyshev.psi n) =O[atTop]
      fun n => (n : ℝ) ^ (1 : ℝ) := by
  refine IsBigO.of_bound (Real.log 4 + 4) (Eventually.of_forall fun n => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Chebyshev.psi_nonneg n),
    Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.rpow_one]
  exact Chebyshev.psi_le_const_mul_self (by positivity)

/-- The complex von Mangoldt partial sums have the same unconditional linear growth. -/
theorem sum_vonMangoldt_nat_isBigO :
    (fun n : ℕ =>
      ∑ k ∈ Icc 1 n, (ArithmeticFunction.vonMangoldt k : ℂ)) =O[atTop]
      fun n => (n : ℝ) ^ (1 : ℝ) := by
  have hcast :
      (fun n : ℕ => (Chebyshev.psi n : ℂ)) =O[atTop]
        fun n => (n : ℝ) ^ (1 : ℝ) := by
    exact_mod_cast chebyshevPsi_nat_isBigO
  refine hcast.congr' ?_ EventuallyEq.rfl
  exact Eventually.of_forall fun n => by
    simpa using chebyshevPsi_eq_sum_vonMangoldt (n : ℝ)

open scoped LSeries.notation in
/-- The source Mellin representation of the von Mangoldt L-series on `Re(s)>1`. -/
theorem LSeries_vonMangoldt_eq_chebyshevPsi_mellin
    {s : ℂ} (hs : 1 < s.re) :
    L ↗ArithmeticFunction.vonMangoldt s =
      s * ∫ t in Ioi (1 : ℝ),
        (Chebyshev.psi t : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  have hsource :=
    LSeries_eq_mul_integral_of_nonneg
      (fun n => ArithmeticFunction.vonMangoldt n)
      (r := (1 : ℝ)) zero_le_one hs
      (chebyshevPsi_nat_isBigO.congr'
        (Eventually.of_forall fun n => by
          simp [Chebyshev.psi, ← Icc_add_one_left_eq_Ioc])
        EventuallyEq.rfl)
      (fun _ => ArithmeticFunction.vonMangoldt_nonneg)
  convert hsource using 1
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by
    change (Chebyshev.psi t : ℂ) * (t : ℂ) ^ (-(s + 1)) =
      (∑ k ∈ Icc 1 ⌊t⌋₊, (ArithmeticFunction.vonMangoldt k : ℂ)) *
        (t : ℂ) ^ (-(s + 1))
    rw [chebyshevPsi_eq_sum_vonMangoldt]

open scoped LSeries.notation in
/-- The Chebyshev Mellin integral is the negative zeta logarithmic derivative on `Re(s)>1`. -/
theorem neg_deriv_riemannZeta_div_eq_chebyshevPsi_mellin
    {s : ℂ} (hs : 1 < s.re) :
    -deriv riemannZeta s / riemannZeta s =
      s * ∫ t in Ioi (1 : ℝ),
        (Chebyshev.psi t : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
  exact LSeries_vonMangoldt_eq_chebyshevPsi_mellin hs

/-- The coefficient whose partial sum is the Chebyshev error at natural arguments. -/
noncomputable def chebyshevPsiErrorCoeff (n : ℕ) : ℂ :=
  (ArithmeticFunction.vonMangoldt n : ℂ) - 1

/-- The finite error-coefficient sum is exactly `psi(N)-N`. -/
theorem sum_chebyshevPsiErrorCoeff (N : ℕ) :
    (∑ k ∈ Icc 1 N, chebyshevPsiErrorCoeff k) =
      (Chebyshev.psi N : ℂ) - (N : ℂ) := by
  simp_rw [chebyshevPsiErrorCoeff]
  rw [sum_sub_distrib]
  have hvm :
      (∑ k ∈ Icc 1 N, (ArithmeticFunction.vonMangoldt k : ℂ)) =
        (Chebyshev.psi N : ℂ) := by
    simpa using (chebyshevPsi_eq_sum_vonMangoldt (N : ℝ)).symm
  rw [hvm]
  simp

/-- The real-variable partial sum in the Abel integral is the floor-valued Chebyshev error. -/
theorem sum_chebyshevPsiErrorCoeff_floor (x : ℝ) :
    (∑ k ∈ Icc 1 ⌊x⌋₊, chebyshevPsiErrorCoeff k) =
      (Chebyshev.psi x : ℂ) - (⌊x⌋₊ : ℂ) := by
  rw [sum_chebyshevPsiErrorCoeff,
    ← Chebyshev.psi_eq_psi_coe_floor x]

/-- The complex Chebyshev values inherit the unconditional linear bound. -/
theorem chebyshevPsi_complex_nat_isBigO :
    (fun n : ℕ => (Chebyshev.psi n : ℂ)) =O[atTop]
      fun n => (n : ℝ) ^ (1 : ℝ) := by
  exact_mod_cast chebyshevPsi_nat_isBigO

/-- Natural-number coercion has exact linear growth in the common real majorant. -/
theorem natCast_complex_isBigO_linear :
    (fun n : ℕ => (n : ℂ)) =O[atTop]
      fun n => (n : ℝ) ^ (1 : ℝ) := by
  refine IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
  simp [Real.rpow_one]

/-- The unconditional Chebyshev error has the coarse linear bound needed on `Re(s)>1`. -/
theorem chebyshevPsiError_nat_isBigO :
    (fun n : ℕ => (Chebyshev.psi n : ℂ) - (n : ℂ)) =O[atTop]
      fun n => (n : ℝ) ^ (1 : ℝ) :=
  chebyshevPsi_complex_nat_isBigO.sub natCast_complex_isBigO_linear

/-- The floor-error coefficient L-series is absolutely convergent on `Re(s)>1`. -/
theorem LSeriesSummable_chebyshevPsiErrorCoeff
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable chebyshevPsiErrorCoeff s := by
  have hv :
      LSeriesSummable
        (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have h1 : LSeriesSummable (1 : ℕ → ℂ) s :=
    LSeriesSummable_one_iff.mpr hs
  change LSeriesSummable
    ((fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) - 1) s
  exact hv.sub h1

open scoped LSeries.notation in
/-- On the common absolute-convergence region, the error series is the pole-canceling
combination `-zeta'/zeta-zeta`. -/
theorem LSeries_chebyshevPsiErrorCoeff_eq
    {s : ℂ} (hs : 1 < s.re) :
    L chebyshevPsiErrorCoeff s =
      -deriv riemannZeta s / riemannZeta s - riemannZeta s := by
  have hv :
      LSeriesSummable
        (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have h1 : LSeriesSummable (1 : ℕ → ℂ) s :=
    LSeriesSummable_one_iff.mpr hs
  calc
    L chebyshevPsiErrorCoeff s =
        L ((fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) - 1) s := by
          rfl
    _ = L (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s -
          L (1 : ℕ → ℂ) s :=
      LSeries_sub hv h1
    _ = -deriv riemannZeta s / riemannZeta s - riemannZeta s := by
      rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs,
        LSeries_one_eq_riemannZeta hs]

open scoped LSeries.notation in
/-- The exact floor-error Mellin representation on the absolute-convergence region. -/
theorem LSeries_chebyshevPsiErrorCoeff_eq_mellin
    {s : ℂ} (hs : 1 < s.re) :
    L chebyshevPsiErrorCoeff s =
      s * ∫ t in Ioi (1 : ℝ),
        ((Chebyshev.psi t : ℂ) - (⌊t⌋₊ : ℂ)) *
          (t : ℂ) ^ (-(s + 1)) := by
  have hsource :=
    LSeries_eq_mul_integral chebyshevPsiErrorCoeff
      (r := (1 : ℝ)) zero_le_one hs
      (LSeriesSummable_chebyshevPsiErrorCoeff hs)
      (chebyshevPsiError_nat_isBigO.congr'
        (Eventually.of_forall fun n =>
          (sum_chebyshevPsiErrorCoeff n).symm)
        EventuallyEq.rfl)
  convert hsource using 1
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by
    change
      ((Chebyshev.psi t : ℂ) - (⌊t⌋₊ : ℂ)) *
          (t : ℂ) ^ (-(s + 1)) =
        (∑ k ∈ Icc 1 ⌊t⌋₊, chebyshevPsiErrorCoeff k) *
          (t : ℂ) ^ (-(s + 1))
    rw [sum_chebyshevPsiErrorCoeff_floor]

/-- A von Koch-type exponent bound gives ordered convergence throughout the corresponding
half-plane, with the exact floor-error Mellin limit. -/
theorem orderedChebyshevPsiErrorHasSum_of_isBigO
    {r : ℝ}
    (hO : (fun n : ℕ =>
      (Chebyshev.psi n : ℂ) - (n : ℂ)) =O[atTop]
        fun n => (n : ℝ) ^ r)
    (hr : 0 ≤ r) {s : ℂ} (hs : r < s.re) :
    OrderedDirichletHasSum chebyshevPsiErrorCoeff s
      (s * ∫ t in Ioi (1 : ℝ),
        ((Chebyshev.psi t : ℂ) - (⌊t⌋₊ : ℂ)) *
          (t : ℂ) ^ (-(s + 1))) := by
  have hsource :=
    orderedDirichletHasSum_mellin_of_sum_isBigO
      chebyshevPsiErrorCoeff
      (hO.congr'
        (Eventually.of_forall fun n =>
          (sum_chebyshevPsiErrorCoeff n).symm)
        EventuallyEq.rfl)
      hr hs
  convert hsource using 1
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by
    change
      ((Chebyshev.psi t : ℂ) - (⌊t⌋₊ : ℂ)) *
          (t : ℂ) ^ (-(s + 1)) =
        (∑ k ∈ Icc 1 ⌊t⌋₊, chebyshevPsiErrorCoeff k) *
          (t : ℂ) ^ (-(s + 1))
    rw [sum_chebyshevPsiErrorCoeff_floor]

/-- The floor-valued error differs from the classical continuous error by the exact fractional
correction. -/
theorem chebyshevPsi_floorError_eq_continuousError_add (x : ℝ) :
    Chebyshev.psi x - (⌊x⌋₊ : ℝ) =
      (Chebyshev.psi x - x) + (x - (⌊x⌋₊ : ℝ)) := by
  ring

theorem chebyshevPsi_floorCorrection_nonneg
    {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ x - (⌊x⌋₊ : ℝ) :=
  Nat.zero_le_self_sub_floor hx

theorem chebyshevPsi_floorCorrection_lt_one (x : ℝ) :
    x - (⌊x⌋₊ : ℝ) < 1 :=
  Nat.self_sub_floor_lt_one x

/-- A concrete cancellation control: alternating coefficients have bounded ordered partial
sums. -/
noncomputable def alternatingDirichletCoeff (n : ℕ) : ℂ :=
  ((-1 : ℝ) ^ n : ℂ)

theorem alternatingDirichletCoeff_sum_isBigO :
    (fun n : ℕ => ∑ k ∈ Icc 1 n, alternatingDirichletCoeff k) =O[atTop]
      fun _ => (1 : ℝ) := by
  refine IsBigO.of_bound 2 (Eventually.of_forall fun n => ?_)
  let S : ℝ := ∑ k ∈ range (n + 1), (-1 : ℝ) ^ k
  have hsplit :
      (∑ k ∈ Icc 1 n, alternatingDirichletCoeff k) =
        (S : ℂ) - 1 := by
    rw [show S = ∑ k ∈ Icc 0 n, (-1 : ℝ) ^ k by
      simp only [S, Nat.range_succ_eq_Icc_zero]]
    rw [Icc_eq_cons_Ioc n.zero_le, sum_cons,
      ← Icc_add_one_left_eq_Ioc]
    simp only [alternatingDirichletCoeff, pow_zero]
    push_cast
    ring
  rw [hsplit]
  calc
    ‖(S : ℂ) - 1‖ ≤ ‖(S : ℂ)‖ + ‖(1 : ℂ)‖ :=
      norm_sub_le _ _
    _ = ‖S‖ + 1 := by simp
    _ ≤ 2 := by
      have hS : ‖S‖ ≤ 1 := by
        simpa only [S] using norm_sum_neg_one_pow_le (n + 1)
      linarith
    _ = 2 * ‖(1 : ℝ)‖ := by norm_num

/-- The alternating test series converges in the natural order throughout `Re(s)>0`. -/
theorem orderedAlternatingDirichletHasSum
    {s : ℂ} (hs : 0 < s.re) :
    OrderedDirichletHasSum alternatingDirichletCoeff s
      (s * ∫ t in Ioi (1 : ℝ),
        (∑ k ∈ Icc 1 ⌊t⌋₊, alternatingDirichletCoeff k) *
          (t : ℂ) ^ (-(s + 1))) := by
  apply orderedDirichletHasSum_mellin_of_sum_isBigO
    alternatingDirichletCoeff (r := (0 : ℝ))
  · simpa only [Real.rpow_zero] using
      alternatingDirichletCoeff_sum_isBigO
  · exact le_rfl
  · simpa using hs

/-- At `s=1/2` the same alternating series is not Mathlib-`LSeriesSummable`, because that
predicate requires absolute convergence. -/
theorem not_LSeriesSummable_alternatingDirichletCoeff_half :
    ¬LSeriesSummable alternatingDirichletCoeff (1 / 2 : ℂ) := by
  intro h
  have hnorm :
      Summable (fun n => ‖LSeries.term alternatingDirichletCoeff (1 / 2 : ℂ) n‖) :=
    summable_norm_iff.mpr h
  have hnormEq :
      (fun n => ‖LSeries.term alternatingDirichletCoeff (1 / 2 : ℂ) n‖) =
        fun n => ‖LSeries.term (1 : ℕ → ℂ) (1 / 2 : ℂ) n‖ := by
    funext n
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    by_cases hn : n = 0
    · simp [hn]
    · simp [hn, alternatingDirichletCoeff]
  have hOne : LSeriesSummable (1 : ℕ → ℂ) (1 / 2 : ℂ) := by
    rw [LSeriesSummable]
    apply summable_norm_iff.mp
    rw [← hnormEq]
    exact hnorm
  have hre := LSeriesSummable_one_iff.mp hOne
  norm_num at hre

/-- Aggregate endpoint for the classical Chebyshev--Mellin entrance and its ordered-convergence
boundary. -/
structure ChebyshevMellinCertificate : Prop where
  orderedAbel :
    ∀ (f : ℕ → ℂ) {r : ℝ},
      (fun n => ∑ k ∈ Icc 1 n, f k) =O[atTop]
          (fun n => (n : ℝ) ^ r) →
      0 ≤ r → ∀ {s : ℂ}, r < s.re →
      OrderedDirichletHasSum f s
        (s * ∫ t in Ioi (1 : ℝ),
          (∑ k ∈ Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(s + 1)))
  absoluteCompatible :
    ∀ {f : ℕ → ℂ} {s : ℂ}, LSeriesSummable f s →
      OrderedDirichletHasSum f s (LSeries f s)
  psiPartial :
    ∀ x : ℝ, (Chebyshev.psi x : ℂ) =
      ∑ k ∈ Icc 1 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt k : ℂ)
  psiMellin :
    ∀ {s : ℂ}, 1 < s.re →
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s =
        s * ∫ t in Ioi (1 : ℝ),
          (Chebyshev.psi t : ℂ) * (t : ℂ) ^ (-(s + 1))
  errorPartial :
    ∀ N : ℕ, (∑ k ∈ Icc 1 N, chebyshevPsiErrorCoeff k) =
      (Chebyshev.psi N : ℂ) - (N : ℂ)
  errorAbsoluteIdentity :
    ∀ {s : ℂ}, 1 < s.re →
      LSeries chebyshevPsiErrorCoeff s =
        -deriv riemannZeta s / riemannZeta s - riemannZeta s
  errorOrderedBridge :
    ∀ {r : ℝ},
      (fun n : ℕ => (Chebyshev.psi n : ℂ) - (n : ℂ)) =O[atTop]
          (fun n => (n : ℝ) ^ r) →
      0 ≤ r → ∀ {s : ℂ}, r < s.re →
      OrderedDirichletHasSum chebyshevPsiErrorCoeff s
        (s * ∫ t in Ioi (1 : ℝ),
          ((Chebyshev.psi t : ℂ) - (⌊t⌋₊ : ℂ)) *
            (t : ℂ) ^ (-(s + 1)))
  floorCorrection :
    ∀ x : ℝ, Chebyshev.psi x - (⌊x⌋₊ : ℝ) =
      (Chebyshev.psi x - x) + (x - (⌊x⌋₊ : ℝ))
  alternatingOrdered :
    ∀ {s : ℂ}, 0 < s.re →
      OrderedDirichletHasSum alternatingDirichletCoeff s
        (s * ∫ t in Ioi (1 : ℝ),
          (∑ k ∈ Icc 1 ⌊t⌋₊, alternatingDirichletCoeff k) *
            (t : ℂ) ^ (-(s + 1)))
  alternatingNotAbsolute :
    ¬LSeriesSummable alternatingDirichletCoeff (1 / 2 : ℂ)

theorem chebyshevMellin_endpoint :
    ChebyshevMellinCertificate where
  orderedAbel := orderedDirichletHasSum_mellin_of_sum_isBigO
  absoluteCompatible := orderedDirichletHasSum_of_LSeriesSummable
  psiPartial := chebyshevPsi_eq_sum_vonMangoldt
  psiMellin := LSeries_vonMangoldt_eq_chebyshevPsi_mellin
  errorPartial := sum_chebyshevPsiErrorCoeff
  errorAbsoluteIdentity := LSeries_chebyshevPsiErrorCoeff_eq
  errorOrderedBridge := orderedChebyshevPsiErrorHasSum_of_isBigO
  floorCorrection := chebyshevPsi_floorError_eq_continuousError_add
  alternatingOrdered := orderedAlternatingDirichletHasSum
  alternatingNotAbsolute :=
    not_LSeriesSummable_alternatingDirichletCoeff_half

end LeanLab.Riemann
