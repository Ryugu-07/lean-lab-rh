import LeanLab.Riemann.ZetaConvexity
import LeanLab.Riemann.LevinsonMontgomeryHeightTenCertificate
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Abel--Euler evaluator for the height-ten certificate

This module starts the Euler--Maclaurin attack on the finite datum isolated from the
Levinson--Montgomery argument.  It keeps the actual `riemannZeta` function in the statement and
uses the already compiled Abel continuation formula as the order-zero Euler summation identity.
The first derivative is obtained by dominated differentiation of the actual fractional-part
tail, avoiding the exponent loss from a Cauchy estimate.
-/

open Complex Filter Finset MeasureTheory Real Set Topology
open scoped BigOperators ComplexConjugate Topology

namespace LeanLab.Riemann

noncomputable section

/-- The actual fractional-part tail beginning at the integer cutoff `N`. -/
def abelZetaTailIntegral (s : ℂ) (N : ℕ) : ℂ :=
  ∫ u in Ioi (N : ℝ), zetaAbelFractKernel s u

/-- The parameter derivative of the fractional-part tail. -/
def abelZetaTailDerivIntegral (s : ℂ) (N : ℕ) : ℂ :=
  ∫ u in Ioi (N : ℝ), -((Real.log u : ℝ) : ℂ) * zetaAbelFractKernel s u

/-- The finite Abel approximation.  Since the partial sum contains `1,...,N`, its integral
main term is written with the sign convention inherited from `ZetaConvexity`. -/
def abelZetaApprox (s : ℂ) (N : ℕ) : ℂ :=
  zetaPartialSum s N - (N : ℂ) ^ (1 - s) / (1 - s)

/-- The derivative of the finite Abel approximation. -/
def abelZetaDerivApprox (s : ℂ) (N : ℕ) : ℂ :=
  deriv (fun w => abelZetaApprox w N) s

/-- The zero-endpoint quadratic primitive of the centered fractional part on one period. -/
def abelQuadraticPeriodic (u : ℝ) : ℝ :=
  (Int.fract u) ^ 2 / 2 - Int.fract u / 2

/-- The centered fractional-part kernel used for the first Euler--Maclaurin integration by
parts. -/
def abelCenteredFractKernel (s : ℂ) (u : ℝ) : ℂ :=
  (((Int.fract u - 1 / 2 : ℝ) : ℂ)) * (u : ℂ) ^ (-s - 1)

/-- The quadratic-periodic remainder kernel after one Euler--Maclaurin integration by parts. -/
def abelQuadraticTailKernel (s : ℂ) (u : ℝ) : ℂ :=
  (abelQuadraticPeriodic u : ℂ) * (u : ℂ) ^ (-s - 2)

/-- The parameter derivative of the quadratic-periodic remainder integral. -/
def abelQuadraticTailDerivIntegral (s : ℂ) (N : ℕ) : ℂ :=
  ∫ u in Ioi (N : ℝ),
    -((Real.log u : ℝ) : ℂ) * abelQuadraticTailKernel s u

/-- The quadratic periodic primitive has the sharp elementary bound `1/8`. -/
theorem abs_abelQuadraticPeriodic_le (u : ℝ) :
    |abelQuadraticPeriodic u| ≤ 1 / 8 := by
  have h0 : 0 ≤ Int.fract u := Int.fract_nonneg u
  have h1 : Int.fract u ≤ 1 := (Int.fract_lt_one u).le
  have hsquare : 0 ≤ (2 * Int.fract u - 1) ^ 2 := sq_nonneg _
  unfold abelQuadraticPeriodic
  rw [show Int.fract u ^ 2 / 2 - Int.fract u / 2 =
      -(Int.fract u * (1 - Int.fract u) / 2) by ring]
  rw [abs_neg, abs_of_nonneg (div_nonneg (mul_nonneg h0 (sub_nonneg.mpr h1)) (by norm_num))]
  nlinarith

private theorem fract_eq_sub_natCast_of_mem_Ico
    (k : ℕ) {u : ℝ} (hu : u ∈ Ico (k : ℝ) (k + 1 : ℝ)) :
    Int.fract u = u - k := by
  have hfloor : Int.floor u = (k : ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor
    · exact_mod_cast hu.1
    · exact_mod_cast hu.2
  simp only [Int.fract, hfloor, Int.cast_natCast]

private theorem integral_centered_shift_mul_cpow_eq_quadratic_shift
    (s : ℂ) (hs : 0 < s.re) (k : ℕ) (hk : 1 ≤ k) :
    (∫ u in (k : ℝ)..(k + 1 : ℝ),
        ((((u - k) - 1 / 2 : ℝ) : ℂ)) * (u : ℂ) ^ (-s - 1)) =
      (s + 1) *
        ∫ u in (k : ℝ)..(k + 1 : ℝ),
          ((((u - k) ^ 2 / 2 - (u - k) / 2 : ℝ) : ℂ)) *
            (u : ℂ) ^ (-s - 2) := by
  let q : ℝ → ℂ := fun u =>
    ((((u - k) ^ 2 / 2 - (u - k) / 2 : ℝ) : ℂ))
  let q' : ℝ → ℂ := fun u => ((((u - k) - 1 / 2 : ℝ) : ℂ))
  let f : ℝ → ℂ := fun u => (u : ℂ) ^ (-s - 1)
  let f' : ℝ → ℂ := fun u => -(s + 1) * (u : ℂ) ^ (-s - 2)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  have hq : ∀ u ∈ Set.uIcc (k : ℝ) (k + 1 : ℝ), HasDerivAt q (q' u) u := by
    intro u _hu
    have hbase := (hasDerivAt_id u).sub_const (k : ℝ)
    have hreal := ((hbase.pow 2).div_const 2).sub (hbase.div_const 2)
    have hreal' : HasDerivAt
        (fun x : ℝ => (x - k) ^ 2 / 2 - (x - k) / 2)
        ((u - k) - 1 / 2) u := by
      have hderivEq :
          (2 : ℝ) * (id u - k) ^ (2 - 1) * 1 / 2 - 1 / 2 =
            (u - k) - 1 / 2 := by
        simp only [id_eq]
        ring
      have hraw := hreal.congr_deriv hderivEq
      apply hraw.congr_of_eventuallyEq
      exact Eventually.of_forall fun _ => rfl
    simpa [q, q'] using hreal'.ofReal_comp
  have hf : ∀ u ∈ Set.uIcc (k : ℝ) (k + 1 : ℝ), HasDerivAt f (f' u) u := by
    intro u hu
    have huIcc : u ∈ Icc (k : ℝ) (k + 1 : ℝ) := by
      simpa [uIcc_of_le (by norm_num : (k : ℝ) ≤ k + 1)] using hu
    have hu0 : 0 < u := hkpos.trans_le huIcc.1
    have hexp : -s - 1 ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      norm_num at hre
      linarith
    have hraw := hasDerivAt_ofReal_cpow_const hu0.ne' hexp
    simpa [f, f'] using hraw.congr_deriv (by
      congr 1
      · ring
      · ring)
  have hqInt : IntervalIntegrable q' volume (k : ℝ) (k + 1 : ℝ) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hfInt : IntervalIntegrable f' volume (k : ℝ) (k + 1 : ℝ) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num : (k : ℝ) ≤ k + 1)]
    have hconst : ContinuousOn (fun _ : ℝ => (-(s + 1) : ℂ))
        (Icc (k : ℝ) (k + 1 : ℝ)) := continuousOn_const
    have hpow : ContinuousOn (fun u : ℝ => (u : ℂ) ^ (-s - 2))
        (Icc (k : ℝ) (k + 1 : ℝ)) :=
      Complex.continuousOn_ofReal_cpow (r := -s - 2) (a := (k : ℝ))
        (b := (k + 1 : ℝ)) hkpos
    have hcont := hconst.mul hpow
    apply hcont.congr
    intro u _hu
    rfl
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hq hf hqInt hfInt
  have hqLeft : q k = 0 := by simp [q]
  have hqRight : q (k + 1) = 0 := by simp [q]
  rw [hqLeft, hqRight, zero_mul, zero_mul, sub_zero, zero_sub] at hibp
  have hleft :
      (∫ u in (k : ℝ)..(k + 1 : ℝ), q u * f' u) =
        -(s + 1) * ∫ u in (k : ℝ)..(k + 1 : ℝ),
          q u * (u : ℂ) ^ (-s - 2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u _hu
    simp only [q, f']
    ring
  rw [hleft] at hibp
  have hright :
      (∫ u in (k : ℝ)..(k + 1 : ℝ), q' u * f u) =
        ∫ u in (k : ℝ)..(k + 1 : ℝ),
          ((((u - k) - 1 / 2 : ℝ) : ℂ)) * (u : ℂ) ^ (-s - 1) := by
    apply intervalIntegral.integral_congr
    intro u _hu
    rfl
  rw [hright] at hibp
  have hquad :
      (∫ u in (k : ℝ)..(k + 1 : ℝ),
          q u * (u : ℂ) ^ (-s - 2)) =
        ∫ u in (k : ℝ)..(k + 1 : ℝ),
          ((((u - k) ^ 2 / 2 - (u - k) / 2 : ℝ) : ℂ)) *
            (u : ℂ) ^ (-s - 2) := by
    apply intervalIntegral.integral_congr
    intro u _hu
    rfl
  rw [hquad] at hibp
  linear_combination hibp

private theorem integral_centeredFract_unit_eq_quadraticPeriodic
    (s : ℂ) (hs : 0 < s.re) (k : ℕ) (hk : 1 ≤ k) :
    (∫ u in (k : ℝ)..(k + 1 : ℝ), abelCenteredFractKernel s u) =
      (s + 1) *
        ∫ u in (k : ℝ)..(k + 1 : ℝ), abelQuadraticTailKernel s u := by
  have hraw := integral_centered_shift_mul_cpow_eq_quadratic_shift s hs k hk
  have hne : ∀ᵐ u : ℝ ∂volume, u ≠ (k + 1 : ℝ) := by
    simpa only [Set.mem_singleton_iff] using
      (Set.countable_singleton (k + 1 : ℝ)).ae_notMem (volume : Measure ℝ)
  have hcentered :
      (∫ u in (k : ℝ)..(k + 1 : ℝ), abelCenteredFractKernel s u) =
        ∫ u in (k : ℝ)..(k + 1 : ℝ),
          ((((u - k) - 1 / 2 : ℝ) : ℂ)) * (u : ℂ) ^ (-s - 1) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hne] with u hune hu
    rw [uIoc_of_le (by norm_num : (k : ℝ) ≤ k + 1)] at hu
    have hult : u < (k + 1 : ℝ) := lt_of_le_of_ne hu.2 hune
    rw [abelCenteredFractKernel,
      fract_eq_sub_natCast_of_mem_Ico k ⟨hu.1.le, hult⟩]
  have hquadratic :
      (∫ u in (k : ℝ)..(k + 1 : ℝ), abelQuadraticTailKernel s u) =
        ∫ u in (k : ℝ)..(k + 1 : ℝ),
          ((((u - k) ^ 2 / 2 - (u - k) / 2 : ℝ) : ℂ)) *
            (u : ℂ) ^ (-s - 2) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hne] with u hune hu
    rw [uIoc_of_le (by norm_num : (k : ℝ) ≤ k + 1)] at hu
    have hult : u < (k + 1 : ℝ) := lt_of_le_of_ne hu.2 hune
    rw [abelQuadraticTailKernel, abelQuadraticPeriodic,
      fract_eq_sub_natCast_of_mem_Ico k ⟨hu.1.le, hult⟩]
  rw [hcentered, hquadratic]
  exact hraw

private theorem integrableOn_abelCenteredFractKernel_Ioi
    {s : ℂ} (hs : 0 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    IntegrableOn (abelCenteredFractKernel s) (Ioi (N : ℝ)) := by
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hNreal
  have hmajor : IntegrableOn (fun u : ℝ => (1 / 2 : ℝ) * u ^ (-s.re - 1))
      (Ioi (N : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hNpos).const_mul (1 / 2)
  have hmeas : AEStronglyMeasurable (abelCenteredFractKernel s)
      (volume.restrict (Ioi (N : ℝ))) := by
    apply Measurable.aestronglyMeasurable
    exact (measurable_fract.sub measurable_const).complex_ofReal.mul
      (by simpa using Complex.measurable_ofReal.pow_const (-s - 1))
  refine hmajor.mono' hmeas ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ ?_)
  intro u hu
  have hu1 : 1 ≤ u := hNreal.trans hu.le
  have hu0 : 0 < u := zero_lt_one.trans_le hu1
  have hfract0 : 0 ≤ Int.fract u := Int.fract_nonneg u
  have hfract1 : Int.fract u ≤ 1 := (Int.fract_lt_one u).le
  have habs : |Int.fract u - 1 / 2| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith
  rw [abelCenteredFractKernel, norm_mul,
    Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos hu0]
  norm_num
  exact mul_le_mul_of_nonneg_right habs (Real.rpow_nonneg hu0.le _)

private theorem integrableOn_abelQuadraticTailKernel_Ioi
    {s : ℂ} (hs : 0 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    IntegrableOn (abelQuadraticTailKernel s) (Ioi (N : ℝ)) := by
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hNreal
  have hmajor : IntegrableOn (fun u : ℝ => (1 / 8 : ℝ) * u ^ (-s.re - 2))
      (Ioi (N : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hNpos).const_mul (1 / 8)
  have hmeas : AEStronglyMeasurable (abelQuadraticTailKernel s)
      (volume.restrict (Ioi (N : ℝ))) := by
    apply Measurable.aestronglyMeasurable
    exact (((measurable_fract.pow_const 2).div_const 2).sub
      (measurable_fract.div_const 2)).complex_ofReal.mul
      (by simpa using Complex.measurable_ofReal.pow_const (-s - 2))
  refine hmajor.mono' hmeas ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ ?_)
  intro u hu
  have hu1 : 1 ≤ u := hNreal.trans hu.le
  have hu0 : 0 < u := zero_lt_one.trans_le hu1
  rw [abelQuadraticTailKernel, norm_mul,
    Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos hu0]
  norm_num
  exact mul_le_mul_of_nonneg_right (abs_abelQuadraticPeriodic_le u)
    (Real.rpow_nonneg hu0.le _)

private theorem integral_centeredFract_natInterval_eq_quadraticPeriodic
    (s : ℂ) (hs : 0 < s.re) {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) :
    (∫ u in (N : ℝ)..(M : ℝ), abelCenteredFractKernel s u) =
      (s + 1) *
        ∫ u in (N : ℝ)..(M : ℝ), abelQuadraticTailKernel s u := by
  have hcentered := integrableOn_abelCenteredFractKernel_Ioi hs hN
  have hquadratic := integrableOn_abelQuadraticTailKernel_Ioi hs hN
  have hcenteredIci : IntegrableOn (abelCenteredFractKernel s) (Ici (N : ℝ)) :=
    (integrableOn_Ici_iff_integrableOn_Ioi
      (f := abelCenteredFractKernel s) (μ := volume)).mpr hcentered
  have hquadraticIci : IntegrableOn (abelQuadraticTailKernel s) (Ici (N : ℝ)) :=
    (integrableOn_Ici_iff_integrableOn_Ioi
      (f := abelQuadraticTailKernel s) (μ := volume)).mpr hquadratic
  induction M, hNM using Nat.le_induction with
  | base => simp
  | succ M hNM ih =>
      have hM : 1 ≤ M := hN.trans hNM
      have hunit := integral_centeredFract_unit_eq_quadraticPeriodic s hs M hM
      have hcenteredLeft : IntervalIntegrable (abelCenteredFractKernel s) volume
          (N : ℝ) (M : ℝ) := by
        apply IntegrableOn.intervalIntegrable
        exact hcenteredIci.mono_set (by
          intro u hu
          rw [Set.uIcc_of_le (by exact_mod_cast hNM)] at hu
          exact hu.1)
      have hcenteredRight : IntervalIntegrable (abelCenteredFractKernel s) volume
          (M : ℝ) (M + 1 : ℝ) := by
        apply IntegrableOn.intervalIntegrable
        exact hcenteredIci.mono_set (by
          intro u hu
          rw [Set.uIcc_of_le (by norm_num : (M : ℝ) ≤ M + 1)] at hu
          exact (show (N : ℝ) ≤ M by exact_mod_cast hNM).trans hu.1)
      have hquadraticLeft : IntervalIntegrable (abelQuadraticTailKernel s) volume
          (N : ℝ) (M : ℝ) := by
        apply IntegrableOn.intervalIntegrable
        exact hquadraticIci.mono_set (by
          intro u hu
          rw [Set.uIcc_of_le (by exact_mod_cast hNM)] at hu
          exact hu.1)
      have hquadraticRight : IntervalIntegrable (abelQuadraticTailKernel s) volume
          (M : ℝ) (M + 1 : ℝ) := by
        apply IntegrableOn.intervalIntegrable
        exact hquadraticIci.mono_set (by
          intro u hu
          rw [Set.uIcc_of_le (by norm_num : (M : ℝ) ≤ M + 1)] at hu
          exact (show (N : ℝ) ≤ M by exact_mod_cast hNM).trans hu.1)
      norm_num [Nat.cast_add, Nat.cast_one]
      rw [← intervalIntegral.integral_add_adjacent_intervals hcenteredLeft hcenteredRight,
        ← intervalIntegral.integral_add_adjacent_intervals hquadraticLeft hquadraticRight,
        ih, hunit]
      ring

/-- One Euler--Maclaurin integration by parts on the actual half-infinite periodic tail. -/
theorem integral_abelCenteredFractKernel_eq_quadraticTail
    {s : ℂ} (hs : 0 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    (∫ u in Ioi (N : ℝ), abelCenteredFractKernel s u) =
      (s + 1) * ∫ u in Ioi (N : ℝ), abelQuadraticTailKernel s u := by
  have hcentered := integrableOn_abelCenteredFractKernel_Ioi hs hN
  have hquadratic := integrableOn_abelQuadraticTailKernel_Ioi hs hN
  have hcenteredTendsto := intervalIntegral_tendsto_integral_Ioi
    (N : ℝ) hcentered tendsto_natCast_atTop_atTop
  have hquadraticTendsto := intervalIntegral_tendsto_integral_Ioi
    (N : ℝ) hquadratic tendsto_natCast_atTop_atTop
  have hfinite :
      (fun M : ℕ => ∫ u in (N : ℝ)..(M : ℝ), abelCenteredFractKernel s u) =ᶠ[atTop]
        fun M : ℕ => (s + 1) *
          ∫ u in (N : ℝ)..(M : ℝ), abelQuadraticTailKernel s u := by
    filter_upwards [eventually_ge_atTop N] with M hNM
    exact integral_centeredFract_natInterval_eq_quadraticPeriodic s hs hN hNM
  have hrightTendsto :
      Tendsto
        (fun M : ℕ => (s + 1) *
          ∫ u in (N : ℝ)..(M : ℝ), abelQuadraticTailKernel s u)
        atTop
        (nhds ((s + 1) * ∫ u in Ioi (N : ℝ), abelQuadraticTailKernel s u)) :=
    hquadraticTendsto.const_mul (s + 1)
  have hcenteredToRight := (tendsto_congr' hfinite).mpr hrightTendsto
  exact tendsto_nhds_unique hcenteredTendsto hcenteredToRight

/-- Exact decomposition of the Abel fractional-part tail after one Euler--Maclaurin step. -/
theorem abelZetaTailIntegral_eq_half_cpow_add_quadraticTail
    {s : ℂ} (hs : 0 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    abelZetaTailIntegral s N =
      (N : ℂ) ^ (-s) / (2 * s) +
        (s + 1) * ∫ u in Ioi (N : ℝ), abelQuadraticTailKernel s u := by
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hNreal
  have hsZero : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hcpow : IntegrableOn (fun u : ℝ => (u : ℂ) ^ (-s - 1)) (Ioi (N : ℝ)) :=
    integrableOn_Ioi_cpow_of_lt (by norm_num; linarith) hNpos
  have hhalf : IntegrableOn (fun u : ℝ => (1 / 2 : ℂ) * (u : ℂ) ^ (-s - 1))
      (Ioi (N : ℝ)) := hcpow.const_mul (1 / 2 : ℂ)
  have hcentered := integrableOn_abelCenteredFractKernel_Ioi hs hN
  have hsplit : abelZetaTailIntegral s N =
      (∫ u in Ioi (N : ℝ), (1 / 2 : ℂ) * (u : ℂ) ^ (-s - 1)) +
        ∫ u in Ioi (N : ℝ), abelCenteredFractKernel s u := by
    rw [abelZetaTailIntegral]
    rw [← integral_add hhalf hcentered]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _hu
    change ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1) =
      (1 / 2 : ℂ) * (u : ℂ) ^ (-s - 1) +
        (((Int.fract u - 1 / 2 : ℝ) : ℂ)) * (u : ℂ) ^ (-s - 1)
    norm_num only [ofReal_sub, ofReal_div, ofReal_one, ofReal_ofNat]
    ring
  have hcpowIntegral :
      (∫ u in Ioi (N : ℝ), (u : ℂ) ^ (-s - 1)) = (N : ℂ) ^ (-s) / s := by
    rw [integral_Ioi_cpow_of_lt (a := -s - 1) (by norm_num; linarith) hNpos]
    rw [show -s - 1 + 1 = -s by ring]
    rw [show (((N : ℝ) : ℂ)) = (N : ℂ) by norm_num]
    field_simp [hsZero]
  rw [hsplit, integral_const_mul, hcpowIntegral,
    integral_abelCenteredFractKernel_eq_quadraticTail hs hN]
  field_simp [hsZero]

/-- The first corrected Euler--Maclaurin approximation, for a partial sum through `N`. -/
def eulerMaclaurinOneZetaApprox (s : ℂ) (N : ℕ) : ℂ :=
  abelZetaApprox s N - (N : ℂ) ^ (-s) / 2

/-- The derivative of the first corrected Euler--Maclaurin approximation. -/
def eulerMaclaurinOneZetaDerivApprox (s : ℂ) (N : ℕ) : ℂ :=
  deriv (fun w => eulerMaclaurinOneZetaApprox w N) s

/-- The first corrected Euler--Maclaurin remainder. -/
def eulerMaclaurinOneZetaRemainder (s : ℂ) (N : ℕ) : ℂ :=
  -s * (s + 1) * ∫ u in Ioi (N : ℝ), abelQuadraticTailKernel s u

/-- Actual-zeta Euler--Maclaurin formula with one quadratic periodic remainder. -/
theorem riemannZeta_eq_eulerMaclaurinOneZetaApprox_add_remainder
    {s : ℂ} (hs : s ∈ zetaAbelContinuationDomain) {N : ℕ} (hN : 1 ≤ N) :
    riemannZeta s =
      eulerMaclaurinOneZetaApprox s N + eulerMaclaurinOneZetaRemainder s N := by
  have hsRe := zetaAbelContinuationDomain_re_pos hs
  rw [riemannZeta_eq_zetaPartialSum_sub_tail s hs N hN]
  change zetaPartialSum s N - (N : ℂ) ^ (1 - s) / (1 - s) -
      s * abelZetaTailIntegral s N =
    eulerMaclaurinOneZetaApprox s N + eulerMaclaurinOneZetaRemainder s N
  rw [abelZetaTailIntegral_eq_half_cpow_add_quadraticTail hsRe hN]
  unfold eulerMaclaurinOneZetaApprox eulerMaclaurinOneZetaRemainder
    abelZetaApprox
  have hsZero : s ≠ 0 := by
    intro h
    rw [h] at hsRe
    norm_num at hsRe
  field_simp [hsZero]
  ring

/-- Explicit value radius for the first corrected Euler--Maclaurin formula. -/
def eulerMaclaurinOneZetaError (s : ℂ) (N : ℕ) : ℝ :=
  ‖s * (s + 1)‖ * ((N : ℝ) ^ (-s.re - 1) / (8 * (s.re + 1)))

/-- Norm bound for the first quadratic periodic remainder integral. -/
theorem norm_integral_abelQuadraticTailKernel_le
    {s : ℂ} (hs : 0 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    ‖∫ u in Ioi (N : ℝ), abelQuadraticTailKernel s u‖ ≤
      (N : ℝ) ^ (-s.re - 1) / (8 * (s.re + 1)) := by
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hNreal
  have hmajor : IntegrableOn (fun u : ℝ => (1 / 8 : ℝ) * u ^ (-s.re - 2))
      (Ioi (N : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hNpos).const_mul (1 / 8)
  have hbound :
      ∀ᵐ u ∂(volume.restrict (Ioi (N : ℝ))),
        ‖abelQuadraticTailKernel s u‖ ≤ (1 / 8 : ℝ) * u ^ (-s.re - 2) := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ ?_)
    intro u hu
    have hu0 : 0 < u := hNpos.trans hu
    rw [abelQuadraticTailKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos hu0]
    norm_num
    exact mul_le_mul_of_nonneg_right (abs_abelQuadraticPeriodic_le u)
      (Real.rpow_nonneg hu0.le _)
  calc
    ‖∫ u in Ioi (N : ℝ), abelQuadraticTailKernel s u‖
        ≤ ∫ u in Ioi (N : ℝ), (1 / 8 : ℝ) * u ^ (-s.re - 2) :=
      MeasureTheory.norm_integral_le_of_norm_le hmajor hbound
    _ = (N : ℝ) ^ (-s.re - 1) / (8 * (s.re + 1)) := by
      rw [integral_const_mul,
        integral_Ioi_rpow_of_lt (a := -s.re - 2) (by linarith) hNpos]
      rw [show -s.re - 2 + 1 = -s.re - 1 by ring]
      rw [show -s.re - 1 = -(s.re + 1) by ring]
      field_simp [ne_of_gt (by linarith : 0 < s.re + 1)]

/-- The actual zeta value lies in the first corrected Euler--Maclaurin error ball. -/
theorem norm_riemannZeta_sub_eulerMaclaurinOneZetaApprox_le
    {s : ℂ} (hs : s ∈ zetaAbelContinuationDomain) {N : ℕ} (hN : 1 ≤ N) :
    ‖riemannZeta s - eulerMaclaurinOneZetaApprox s N‖ ≤
      eulerMaclaurinOneZetaError s N := by
  have hsRe := zetaAbelContinuationDomain_re_pos hs
  have htail := norm_integral_abelQuadraticTailKernel_le hsRe hN
  rw [riemannZeta_eq_eulerMaclaurinOneZetaApprox_add_remainder hs hN,
    add_sub_cancel_left]
  unfold eulerMaclaurinOneZetaRemainder eulerMaclaurinOneZetaError
  rw [norm_mul, norm_mul, norm_neg]
  calc
    ‖s‖ * ‖s + 1‖ * ‖∫ u in Ioi (N : ℝ), abelQuadraticTailKernel s u‖ =
        ‖s * (s + 1)‖ * ‖∫ u in Ioi (N : ℝ), abelQuadraticTailKernel s u‖ := by
      rw [norm_mul]
    _ ≤ ‖s * (s + 1)‖ * ((N : ℝ) ^ (-s.re - 1) / (8 * (s.re + 1))) :=
      mul_le_mul_of_nonneg_left htail (norm_nonneg (s * (s + 1)))

private theorem abelZetaTailIntegral_integrable
    {s : ℂ} (hs : 0 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    Integrable (fun u => zetaAbelFractKernel s u)
      (volume.restrict (Ioi (N : ℝ))) := by
  have hbase := ZetaAbelFractKernel.integrableOn_Ioi s hs
  exact hbase.mono_measure
    (Measure.restrict_mono
      (Set.Ioi_subset_Ioi (by exact_mod_cast hN : (1 : ℝ) ≤ (N : ℝ))) le_rfl)

private theorem abelZetaTailDerivIntegral_aestronglyMeasurable
    (s : ℂ) (N : ℕ) :
    AEStronglyMeasurable
      (fun u : ℝ => -((Real.log u : ℝ) : ℂ) * zetaAbelFractKernel s u)
      (volume.restrict (Ioi (N : ℝ))) := by
  by_cases hN : 1 ≤ N
  · exact (ZetaAbelFractKernel.aestronglyMeasurable_param_deriv s).mono_measure
      (Measure.restrict_mono
        (Set.Ioi_subset_Ioi (by exact_mod_cast hN : (1 : ℝ) ≤ (N : ℝ))) le_rfl)
  · have hmeas : Measurable (fun u : ℝ => zetaAbelFractKernel s u) :=
      (measurable_fract.complex_ofReal.mul <| by
        simpa using Complex.measurable_ofReal.pow_const (-s - 1))
    exact Measurable.aestronglyMeasurable (μ := volume.restrict (Ioi (N : ℝ)))
      (Real.measurable_log.complex_ofReal.neg.mul hmeas)

private theorem abelZetaTailIntegral_hasDerivAt
    {s : ℂ} (hs : 0 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    HasDerivAt (fun w => abelZetaTailIntegral w N)
      (abelZetaTailDerivIntegral s N) s := by
  let epsilon : ℝ := s.re / 2
  have hepsilon : 0 < epsilon := half_pos hs
  obtain ⟨delta, hdelta, hreal⟩ :=
    Complex.exists_pos_radius_forall_mem_ball_re_ge
      (z₀ := s) (a := epsilon) (half_lt_self hs)
  let F : ℂ → ℝ → ℂ := zetaAbelFractKernel
  let F' : ℂ → ℝ → ℂ := fun z u => -((Real.log u : ℝ) : ℂ) * F z u
  let bound : ℝ → ℝ := fun u => (2 / epsilon) * u ^ (-1 - epsilon / 2)
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hNreal
  have hboundInt : Integrable bound (volume.restrict (Ioi (N : ℝ))) := by
    simpa [bound, IntegrableOn] using
      (integrableOn_Ioi_rpow_of_lt (by linarith [half_pos hepsilon]) hNpos).const_mul
        (2 / epsilon)
  have hFmeas :
      ∀ᶠ z in nhds s,
        AEStronglyMeasurable (F z) (volume.restrict (Ioi (N : ℝ))) :=
    Eventually.of_forall fun z =>
      ZetaAbelFractKernel.aestronglyMeasurable z (Ioi (N : ℝ)) measurableSet_Ioi
  have hFint : Integrable (F s) (volume.restrict (Ioi (N : ℝ))) := by
    simpa [F] using abelZetaTailIntegral_integrable hs hN
  have hF'meas :
      AEStronglyMeasurable (F' s) (volume.restrict (Ioi (N : ℝ))) := by
    simpa [F, F'] using abelZetaTailDerivIntegral_aestronglyMeasurable s N
  have hbound :
      ∀ᵐ u ∂(volume.restrict (Ioi (N : ℝ))),
        ∀ z ∈ Metric.ball s delta, ‖F' z u‖ ≤ bound u := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ ?_)
    intro u hu z hz
    have hu1 : 1 < u := lt_of_le_of_lt hNreal hu
    have hzRe : epsilon ≤ z.re :=
      hreal s z (by simpa [dist_self] using hdelta) (Metric.mem_ball.mp hz)
    exact (ZetaAbelFractKernel.kernel_deriv_norm_bound_on_ball epsilon u hu1 z hzRe).trans
      (by simpa [bound] using Real.log_mul_rpow_neg_le_two_div_mul_rpow_neg hepsilon hu1)
  have hderiv :
      ∀ᵐ u ∂(volume.restrict (Ioi (N : ℝ))),
        ∀ z ∈ Metric.ball s delta, HasDerivAt (fun w => F w u) (F' z u) z := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ ?_)
    intro u hu z _hz
    have hu1 : 1 < u := lt_of_le_of_lt hNreal hu
    simpa [F, F'] using ZetaAbelFractKernel.hasDerivAt_in_param u hu1 z
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (N : ℝ))) (F := F) (F' := F') (x₀ := s)
    (s := Metric.ball s delta) (bound := bound) (Metric.ball_mem_nhds s hdelta)
    (hF_meas := hFmeas) (hF_int := hFint) (hF'_meas := hF'meas)
    (h_bound := hbound) (bound_integrable := hboundInt) (h_diff := hderiv)
  rcases h with ⟨_, hDeriv⟩
  simpa [abelZetaTailIntegral, abelZetaTailDerivIntegral, F, F'] using hDeriv

private theorem differentiableAt_abelZetaApprox
    (s : ℂ) (hs1 : s ≠ 1) {N : ℕ} (hN : 1 ≤ N) :
    DifferentiableAt ℂ (fun w => abelZetaApprox w N) s := by
  unfold abelZetaApprox zetaPartialSum
  have hsum : DifferentiableAt ℂ
      (fun w : ℂ => ∑ n ∈ range N, ((n : ℂ) + 1) ^ (-w)) s := by
    apply DifferentiableAt.fun_sum
    intro n _hn
    exact differentiableAt_id.neg.const_cpow (Or.inl (by
      intro h
      have hre := congrArg Complex.re h
      norm_num at hre
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith))
  have hNzero : (N : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_zero_of_lt hN)
  exact hsum.sub
    (((differentiableAt_const (c := (1 : ℂ))).sub differentiableAt_id).const_cpow
      (Or.inl hNzero) |>.div
      ((differentiableAt_const (c := (1 : ℂ))).sub differentiableAt_id)
      (sub_ne_zero.mpr hs1.symm))

/-- The order-zero Euler summation identity for the actual zeta function. -/
theorem riemannZeta_eq_abelZetaApprox_sub_tail
    {s : ℂ} (hs : s ∈ zetaAbelContinuationDomain) {N : ℕ} (hN : 1 ≤ N) :
    riemannZeta s = abelZetaApprox s N - s * abelZetaTailIntegral s N := by
  simpa [abelZetaApprox, abelZetaTailIntegral] using
    riemannZeta_eq_zetaPartialSum_sub_tail s hs N hN

/-- Differentiating the actual Abel tail gives a direct first-derivative evaluator. -/
theorem deriv_riemannZeta_sub_abelZetaDerivApprox
    {s : ℂ} (hs : s ∈ zetaAbelContinuationDomain) {N : ℕ} (hN : 1 ≤ N) :
    deriv riemannZeta s - abelZetaDerivApprox s N =
      -(abelZetaTailIntegral s N + s * abelZetaTailDerivIntegral s N) := by
  have hsRe : 0 < s.re := zetaAbelContinuationDomain_re_pos hs
  have hzeta : HasDerivAt riemannZeta (deriv riemannZeta s) s :=
    (differentiableAt_riemannZeta hs.1).hasDerivAt
  have happDiff := differentiableAt_abelZetaApprox s hs.1 hN
  have happ : HasDerivAt (fun w => abelZetaApprox w N)
      (abelZetaDerivApprox s N) s := by
    simpa [abelZetaDerivApprox] using happDiff.hasDerivAt
  have hleft := hzeta.sub happ
  have htail := abelZetaTailIntegral_hasDerivAt hsRe hN
  have hright : HasDerivAt
      (fun w => -(w * abelZetaTailIntegral w N))
      (-(abelZetaTailIntegral s N + s * abelZetaTailDerivIntegral s N)) s := by
    have h := ((hasDerivAt_id s).mul htail).neg
    change HasDerivAt
      (-((fun w : ℂ => w) * fun w => abelZetaTailIntegral w N))
      (-(abelZetaTailIntegral s N + s * abelZetaTailDerivIntegral s N)) s
    simpa only [Function.id_def, one_mul] using h
  have hdomain : ∀ᶠ w in nhds s, w ∈ zetaAbelContinuationDomain :=
    isOpen_zetaAbelContinuationDomain.mem_nhds hs
  have heq :
      (fun w => riemannZeta w - abelZetaApprox w N) =ᶠ[nhds s]
        fun w => -(w * abelZetaTailIntegral w N) := by
    filter_upwards [hdomain] with w hw
    rw [riemannZeta_eq_abelZetaApprox_sub_tail hw hN]
    ring
  exact (hright.unique (hleft.congr_of_eventuallyEq heq.symm)).symm

private theorem integrableOn_log_mul_rpow_neg_sub_one
    {a c : ℝ} (ha : 0 < a) (hc : 1 ≤ c) :
    IntegrableOn (fun u : ℝ => Real.log u * u ^ (-a - 1)) (Ioi c) := by
  let epsilon : ℝ := a / 2
  let p : ℝ := -a - 1 + epsilon
  have hepsilon : 0 < epsilon := half_pos ha
  have hp : p < -1 := by
    dsimp only [p, epsilon]
    linarith
  have hmajor : IntegrableOn (fun u : ℝ => epsilon⁻¹ * u ^ p) (Ioi c) :=
    (integrableOn_Ioi_rpow_of_lt hp (zero_lt_one.trans_le hc)).const_mul epsilon⁻¹
  refine hmajor.mono' (by fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu1 : 1 < u := lt_of_le_of_lt hc hu
  have hu0 : 0 < u := zero_lt_one.trans hu1
  have hlog : Real.log u ≤ u ^ epsilon / epsilon :=
    Real.log_le_rpow_div hu0.le hepsilon
  have hlog0 : 0 ≤ Real.log u := Real.log_nonneg hu1.le
  have htarget : 0 ≤ Real.log u * u ^ (-a - 1) :=
    mul_nonneg hlog0 (Real.rpow_nonneg hu0.le _)
  calc
    ‖Real.log u * u ^ (-a - 1)‖ = Real.log u * u ^ (-a - 1) := by
      rw [Real.norm_eq_abs, abs_of_nonneg htarget]
    _ ≤ (u ^ epsilon / epsilon) * u ^ (-a - 1) := by
      gcongr
    _ = epsilon⁻¹ * u ^ p := by
      rw [div_eq_mul_inv, mul_comm (u ^ epsilon), mul_assoc,
        ← Real.rpow_add hu0]
      congr 2
      dsimp only [p]
      ring

private theorem integral_Ioi_log_mul_rpow_neg_sub_one
    {a c : ℝ} (ha : 0 < a) (hc : 1 ≤ c) :
    (∫ u in Ioi c, Real.log u * u ^ (-a - 1)) =
      c ^ (-a) * (Real.log c / a + 1 / a ^ 2) := by
  let F : ℝ → ℝ := fun u =>
    -(u ^ (-a)) * (Real.log u / a + 1 / a ^ 2)
  have hderiv : ∀ u ∈ Ici c,
      HasDerivAt F (Real.log u * u ^ (-a - 1)) u := by
    intro u hu
    have hu0 : 0 < u := zero_lt_one.trans_le (hc.trans hu)
    have hpow := Real.hasDerivAt_rpow_const (p := -a) (Or.inl hu0.ne')
    have hlog := Real.hasDerivAt_log hu0.ne'
    have hF := hpow.neg.mul (hlog.div_const a |>.add_const (1 / a ^ 2))
    have hFat : HasDerivAt F
        (-(-a * u ^ (-a - 1)) * (Real.log u / a + 1 / a ^ 2) +
          (-u ^ (-a)) * (u⁻¹ / a)) u := by
      apply hF.congr_of_eventuallyEq
      exact Eventually.of_forall fun _ => rfl
    refine hFat.congr_deriv ?_
    rw [show -a - 1 = -a + (-1) by ring, Real.rpow_add hu0,
      Real.rpow_neg_one]
    field_simp [ne_of_gt ha, ne_of_gt hu0]
    ring
  have hint := integrableOn_log_mul_rpow_neg_sub_one ha hc
  have hpowZero : Tendsto (fun u : ℝ => u ^ (-a)) atTop (nhds 0) := by
    simpa only [neg_neg] using tendsto_rpow_neg_atTop ha
  have hlogPowZero :
      Tendsto (fun u : ℝ => Real.log u * u ^ (-a)) atTop (nhds 0) := by
    have h := (isLittleO_log_rpow_atTop ha).tendsto_div_nhds_zero
    apply Tendsto.congr' ?_ h
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    rw [Real.rpow_neg hu.le, div_eq_mul_inv]
  have hFZero : Tendsto F atTop (nhds 0) := by
    have hfirst := hlogPowZero.div_const a
    have hsecond := hpowZero.div_const (a ^ 2)
    have hsum : Tendsto
        (fun u : ℝ => -(Real.log u * u ^ (-a) / a + u ^ (-a) / a ^ 2))
        atTop (nhds 0) := by
      simpa only [zero_div, zero_add, neg_zero] using (hfirst.add hsecond).neg
    apply hsum.congr'
    exact Eventually.of_forall fun u => by
      dsimp only [F]
      ring
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hFZero]
  dsimp only [F]
  ring

private theorem abelQuadraticTailKernel_hasDerivAt_in_param
    (u : ℝ) (hu : 0 < u) (z : ℂ) :
    HasDerivAt (fun w => abelQuadraticTailKernel w u)
      (-((Real.log u : ℝ) : ℂ) * abelQuadraticTailKernel z u) z := by
  have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  have hexp : HasDerivAt (fun w : ℂ => -w - 2) (-1) z := by
    simpa using (hasDerivAt_id z).neg.sub_const (2 : ℂ)
  have hpow := HasDerivAt.const_cpow (c := (u : ℂ)) hexp (Or.inl huC)
  have h := hpow.const_mul (abelQuadraticPeriodic u : ℂ)
  simpa [abelQuadraticTailKernel, Complex.ofReal_log hu.le,
    mul_comm, mul_left_comm, mul_assoc] using h

private theorem abelQuadraticTailDerivIntegral_aestronglyMeasurable
    (s : ℂ) (N : ℕ) :
    AEStronglyMeasurable
      (fun u : ℝ =>
        -((Real.log u : ℝ) : ℂ) * abelQuadraticTailKernel s u)
      (volume.restrict (Ioi (N : ℝ))) := by
  have hkernel : Measurable (abelQuadraticTailKernel s) :=
    (((measurable_fract.pow_const 2).div_const 2).sub
      (measurable_fract.div_const 2)).complex_ofReal.mul
      (by simpa using Complex.measurable_ofReal.pow_const (-s - 2))
  exact (Real.measurable_log.complex_ofReal.neg.mul hkernel).aestronglyMeasurable

private theorem abelQuadraticTailIntegral_hasDerivAt
    {s : ℂ} (hs : 0 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    HasDerivAt
      (fun w => ∫ u in Ioi (N : ℝ), abelQuadraticTailKernel w u)
      (abelQuadraticTailDerivIntegral s N) s := by
  let epsilon : ℝ := s.re / 2
  have hepsilon : 0 < epsilon := half_pos hs
  obtain ⟨delta, hdelta, hreal⟩ :=
    Complex.exists_pos_radius_forall_mem_ball_re_ge
      (z₀ := s) (a := epsilon) (half_lt_self hs)
  let F : ℂ → ℝ → ℂ := abelQuadraticTailKernel
  let F' : ℂ → ℝ → ℂ := fun z u =>
    -((Real.log u : ℝ) : ℂ) * F z u
  let bound : ℝ → ℝ := fun u =>
    (1 / 8 : ℝ) * (Real.log u * u ^ (-epsilon - 2))
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hNreal
  have hboundInt : Integrable bound (volume.restrict (Ioi (N : ℝ))) := by
    have hraw :=
      (integrableOn_log_mul_rpow_neg_sub_one (a := epsilon + 1)
        (by linarith) hNreal).const_mul (1 / 8 : ℝ)
    apply hraw.congr
    filter_upwards with u
    simp only [bound]
    congr 3
    ring
  have hFmeas :
      ∀ᶠ z in nhds s,
        AEStronglyMeasurable (F z) (volume.restrict (Ioi (N : ℝ))) := by
    refine Eventually.of_forall fun z => Measurable.aestronglyMeasurable ?_
    exact (((measurable_fract.pow_const 2).div_const 2).sub
      (measurable_fract.div_const 2)).complex_ofReal.mul
      (by simpa [F] using Complex.measurable_ofReal.pow_const (-z - 2))
  have hFint : Integrable (F s) (volume.restrict (Ioi (N : ℝ))) := by
    simpa [F, IntegrableOn] using integrableOn_abelQuadraticTailKernel_Ioi hs hN
  have hF'meas :
      AEStronglyMeasurable (F' s) (volume.restrict (Ioi (N : ℝ))) := by
    simpa [F, F'] using abelQuadraticTailDerivIntegral_aestronglyMeasurable s N
  have hbound :
      ∀ᵐ u ∂(volume.restrict (Ioi (N : ℝ))),
        ∀ z ∈ Metric.ball s delta, ‖F' z u‖ ≤ bound u := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ ?_)
    intro u hu z hz
    have hu1 : 1 < u := lt_of_le_of_lt hNreal hu
    have hu0 : 0 < u := zero_lt_one.trans hu1
    have hzRe : epsilon ≤ z.re :=
      hreal s z (by simpa [dist_self] using hdelta) (Metric.mem_ball.mp hz)
    have hpow : u ^ (-z.re - 2) ≤ u ^ (-epsilon - 2) :=
      Real.rpow_le_rpow_of_exponent_le hu1.le (by linarith)
    have hkernel :
        ‖abelQuadraticTailKernel z u‖ ≤
          (1 / 8 : ℝ) * u ^ (-epsilon - 2) := by
      rw [abelQuadraticTailKernel, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
      norm_num
      exact (mul_le_mul_of_nonneg_right (abs_abelQuadraticPeriodic_le u)
        (Real.rpow_nonneg hu0.le _)).trans
          (mul_le_mul_of_nonneg_left hpow (by norm_num))
    have hlog : 0 ≤ Real.log u := Real.log_nonneg hu1.le
    calc
      ‖F' z u‖ = Real.log u * ‖abelQuadraticTailKernel z u‖ := by
        change ‖-((Real.log u : ℝ) : ℂ) * abelQuadraticTailKernel z u‖ = _
        rw [norm_mul, norm_neg, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg hlog]
      _ ≤ Real.log u * ((1 / 8 : ℝ) * u ^ (-epsilon - 2)) :=
        mul_le_mul_of_nonneg_left hkernel hlog
      _ = bound u := by simp only [bound]; ring
  have hderiv :
      ∀ᵐ u ∂(volume.restrict (Ioi (N : ℝ))),
        ∀ z ∈ Metric.ball s delta, HasDerivAt (fun w => F w u) (F' z u) z := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ ?_)
    intro u hu z _hz
    have hu0 : 0 < u := hNpos.trans hu
    simpa [F, F'] using abelQuadraticTailKernel_hasDerivAt_in_param u hu0 z
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (N : ℝ))) (F := F) (F' := F') (x₀ := s)
    (s := Metric.ball s delta) (bound := bound) (Metric.ball_mem_nhds s hdelta)
    (hF_meas := hFmeas) (hF_int := hFint) (hF'_meas := hF'meas)
    (h_bound := hbound) (bound_integrable := hboundInt) (h_diff := hderiv)
  rcases h with ⟨_, hDeriv⟩
  simpa [abelQuadraticTailDerivIntegral, F, F'] using hDeriv

private theorem differentiableAt_eulerMaclaurinOneZetaApprox
    (s : ℂ) (hs1 : s ≠ 1) {N : ℕ} (hN : 1 ≤ N) :
    DifferentiableAt ℂ (fun w => eulerMaclaurinOneZetaApprox w N) s := by
  have hbase := differentiableAt_abelZetaApprox s hs1 hN
  have hNzero : (N : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_zero_of_lt hN)
  have hpow : DifferentiableAt ℂ (fun w : ℂ => (N : ℂ) ^ (-w)) s :=
    differentiableAt_id.neg.const_cpow (Or.inl hNzero)
  have hraw := hbase.hasDerivAt.sub (hpow.div_const 2).hasDerivAt
  refine (hraw.congr_of_eventuallyEq (Eventually.of_forall fun w => ?_)).differentiableAt
  simp only [eulerMaclaurinOneZetaApprox, Pi.sub_apply]

/-- The actual zeta derivative differs from the first corrected finite derivative by the
derivative of the quadratic-periodic remainder. -/
theorem deriv_riemannZeta_sub_eulerMaclaurinOneZetaDerivApprox
    {s : ℂ} (hs : s ∈ zetaAbelContinuationDomain) {N : ℕ} (hN : 1 ≤ N) :
    deriv riemannZeta s - eulerMaclaurinOneZetaDerivApprox s N =
      -((2 * s + 1) *
          (∫ u in Ioi (N : ℝ), abelQuadraticTailKernel s u) +
        s * (s + 1) * abelQuadraticTailDerivIntegral s N) := by
  have hsRe : 0 < s.re := zetaAbelContinuationDomain_re_pos hs
  have hzeta : HasDerivAt riemannZeta (deriv riemannZeta s) s :=
    (differentiableAt_riemannZeta hs.1).hasDerivAt
  have happDiff := differentiableAt_eulerMaclaurinOneZetaApprox s hs.1 hN
  have happ : HasDerivAt (fun w => eulerMaclaurinOneZetaApprox w N)
      (eulerMaclaurinOneZetaDerivApprox s N) s := by
    simpa [eulerMaclaurinOneZetaDerivApprox] using happDiff.hasDerivAt
  have hleft := hzeta.sub happ
  have htail := abelQuadraticTailIntegral_hasDerivAt hsRe hN
  have hrightRaw :=
    (((hasDerivAt_id s).neg.mul ((hasDerivAt_id s).add_const (1 : ℂ))).mul htail)
  have hright : HasDerivAt
      (fun w => eulerMaclaurinOneZetaRemainder w N)
      (-((2 * s + 1) *
          (∫ u in Ioi (N : ℝ), abelQuadraticTailKernel s u) +
        s * (s + 1) * abelQuadraticTailDerivIntegral s N)) s := by
    refine (hrightRaw.congr_deriv (by
      simp only [Function.id_def, Pi.neg_apply, Pi.mul_apply]
      ring)).congr_of_eventuallyEq (Eventually.of_forall fun w => ?_)
    simp only [eulerMaclaurinOneZetaRemainder, Function.id_def,
      Pi.neg_apply, Pi.mul_apply]
  have hdomain : ∀ᶠ w in nhds s, w ∈ zetaAbelContinuationDomain :=
    isOpen_zetaAbelContinuationDomain.mem_nhds hs
  have heq :
      (fun w => riemannZeta w - eulerMaclaurinOneZetaApprox w N) =ᶠ[nhds s]
        fun w => eulerMaclaurinOneZetaRemainder w N := by
    filter_upwards [hdomain] with w hw
    rw [riemannZeta_eq_eulerMaclaurinOneZetaApprox_add_remainder hw hN]
    ring
  exact (hright.unique (hleft.congr_of_eventuallyEq heq.symm)).symm

/-- Explicit norm bound for the parameter derivative of the quadratic-periodic tail. -/
theorem norm_abelQuadraticTailDerivIntegral_le
    {s : ℂ} (hs : 0 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    ‖abelQuadraticTailDerivIntegral s N‖ ≤
      (1 / 8 : ℝ) * ((N : ℝ) ^ (-(s.re + 1)) *
        (Real.log (N : ℝ) / (s.re + 1) + 1 / (s.re + 1) ^ 2)) := by
  let a : ℝ := s.re + 1
  have ha : 0 < a := by simp only [a]; linarith
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hNreal
  have hmajor : IntegrableOn
      (fun u : ℝ => (1 / 8 : ℝ) * (Real.log u * u ^ (-a - 1)))
      (Ioi (N : ℝ)) :=
    (integrableOn_log_mul_rpow_neg_sub_one ha hNreal).const_mul (1 / 8)
  have hbound :
      ∀ᵐ u ∂(volume.restrict (Ioi (N : ℝ))),
        ‖-((Real.log u : ℝ) : ℂ) * abelQuadraticTailKernel s u‖ ≤
          (1 / 8 : ℝ) * (Real.log u * u ^ (-a - 1)) := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ ?_)
    intro u hu
    have hu1 : 1 ≤ u := hNreal.trans hu.le
    have hu0 : 0 < u := hNpos.trans hu
    have hlog : 0 ≤ Real.log u := Real.log_nonneg hu1
    have hkernel :
        ‖abelQuadraticTailKernel s u‖ ≤ (1 / 8 : ℝ) * u ^ (-a - 1) := by
      rw [abelQuadraticTailKernel, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
      norm_num
      rw [show -s.re - 2 = -a - 1 by simp only [a]; ring]
      exact mul_le_mul_of_nonneg_right (abs_abelQuadraticPeriodic_le u)
        (Real.rpow_nonneg hu0.le _)
    calc
      ‖-((Real.log u : ℝ) : ℂ) * abelQuadraticTailKernel s u‖ =
          Real.log u * ‖abelQuadraticTailKernel s u‖ := by
        rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hlog]
      _ ≤ Real.log u * ((1 / 8 : ℝ) * u ^ (-a - 1)) :=
        mul_le_mul_of_nonneg_left hkernel hlog
      _ = (1 / 8 : ℝ) * (Real.log u * u ^ (-a - 1)) := by ring
  calc
    ‖abelQuadraticTailDerivIntegral s N‖
        ≤ ∫ u in Ioi (N : ℝ),
            (1 / 8 : ℝ) * (Real.log u * u ^ (-a - 1)) := by
      exact MeasureTheory.norm_integral_le_of_norm_le hmajor hbound
    _ = (1 / 8 : ℝ) * ((N : ℝ) ^ (-(s.re + 1)) *
          (Real.log (N : ℝ) / (s.re + 1) + 1 / (s.re + 1) ^ 2)) := by
      rw [integral_const_mul, integral_Ioi_log_mul_rpow_neg_sub_one ha hNreal]

/-- Explicit norm bound for the undifferentiated Abel tail. -/
theorem norm_abelZetaTailIntegral_le
    {s : ℂ} (hs : 0 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    ‖abelZetaTailIntegral s N‖ ≤ (N : ℝ) ^ (-s.re) / s.re := by
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hNreal
  have hmajor : IntegrableOn (fun u : ℝ => u ^ (-s.re - 1)) (Ioi (N : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hNpos
  have hbound :
      ∀ᵐ u ∂(volume.restrict (Ioi (N : ℝ))),
        ‖zetaAbelFractKernel s u‖ ≤ u ^ (-s.re - 1) := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ ?_)
    intro u hu
    exact norm_zetaAbelFractKernel_le u (hNreal.trans hu.le) s
  calc
    ‖abelZetaTailIntegral s N‖
        ≤ ∫ u in Ioi (N : ℝ), u ^ (-s.re - 1) := by
      exact MeasureTheory.norm_integral_le_of_norm_le hmajor hbound
    _ = (N : ℝ) ^ (-s.re) / s.re := by
      rw [integral_Ioi_rpow_of_lt (a := -s.re - 1) (by linarith) hNpos]
      field_simp [ne_of_gt hs]
      ring

/-- Explicit norm bound for the parameter derivative of the Abel tail. -/
theorem norm_abelZetaTailDerivIntegral_le
    {s : ℂ} (hs : 0 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    ‖abelZetaTailDerivIntegral s N‖ ≤
      (N : ℝ) ^ (-s.re) *
        (Real.log (N : ℝ) / s.re + 1 / s.re ^ 2) := by
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hmajor := integrableOn_log_mul_rpow_neg_sub_one hs hNreal
  have hbound :
      ∀ᵐ u ∂(volume.restrict (Ioi (N : ℝ))),
        ‖-((Real.log u : ℝ) : ℂ) * zetaAbelFractKernel s u‖ ≤
          Real.log u * u ^ (-s.re - 1) := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ ?_)
    intro u hu
    have hu1 : 1 ≤ u := hNreal.trans hu.le
    have hlog : 0 ≤ Real.log u := Real.log_nonneg hu1
    calc
      ‖-((Real.log u : ℝ) : ℂ) * zetaAbelFractKernel s u‖ =
          Real.log u * ‖zetaAbelFractKernel s u‖ := by
        rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hlog]
      _ ≤ Real.log u * u ^ (-s.re - 1) := by
        gcongr
        exact norm_zetaAbelFractKernel_le u hu1 s
  calc
    ‖abelZetaTailDerivIntegral s N‖
        ≤ ∫ u in Ioi (N : ℝ), Real.log u * u ^ (-s.re - 1) := by
      exact MeasureTheory.norm_integral_le_of_norm_le hmajor hbound
    _ = (N : ℝ) ^ (-s.re) *
          (Real.log (N : ℝ) / s.re + 1 / s.re ^ 2) :=
      integral_Ioi_log_mul_rpow_neg_sub_one hs hNreal

/-- Explicit order-zero value radius. -/
def abelZetaError (s : ℂ) (N : ℕ) : ℝ :=
  ‖s‖ * (N : ℝ) ^ (-s.re) / s.re

/-- Explicit order-zero first-derivative radius. -/
def abelZetaDerivError (s : ℂ) (N : ℕ) : ℝ :=
  (N : ℝ) ^ (-s.re) / s.re +
    ‖s‖ * ((N : ℝ) ^ (-s.re) *
      (Real.log (N : ℝ) / s.re + 1 / s.re ^ 2))

/-- Explicit first-derivative radius for the first corrected Euler--Maclaurin formula. -/
def eulerMaclaurinOneZetaDerivError (s : ℂ) (N : ℕ) : ℝ :=
  ‖2 * s + 1‖ * ((N : ℝ) ^ (-s.re - 1) / (8 * (s.re + 1))) +
    ‖s * (s + 1)‖ * ((1 / 8 : ℝ) * ((N : ℝ) ^ (-(s.re + 1)) *
      (Real.log (N : ℝ) / (s.re + 1) + 1 / (s.re + 1) ^ 2)))

/-- The actual zeta value lies in the explicit Abel error ball. -/
theorem norm_riemannZeta_sub_abelZetaApprox_le
    {s : ℂ} (hs : s ∈ zetaAbelContinuationDomain) {N : ℕ} (hN : 1 ≤ N) :
    ‖riemannZeta s - abelZetaApprox s N‖ ≤ abelZetaError s N := by
  have hsRe : 0 < s.re := zetaAbelContinuationDomain_re_pos hs
  have hint := norm_abelZetaTailIntegral_le hsRe hN
  rw [riemannZeta_eq_abelZetaApprox_sub_tail hs hN]
  unfold abelZetaError
  rw [sub_sub_cancel_left, norm_neg, norm_mul]
  exact (mul_le_mul_of_nonneg_left hint (norm_nonneg s)).trans_eq (by ring)

/-- The actual zeta derivative lies in the direct differentiated-Abel error ball. -/
theorem norm_deriv_riemannZeta_sub_abelZetaDerivApprox_le
    {s : ℂ} (hs : s ∈ zetaAbelContinuationDomain) {N : ℕ} (hN : 1 ≤ N) :
    ‖deriv riemannZeta s - abelZetaDerivApprox s N‖ ≤
      abelZetaDerivError s N := by
  have hsRe : 0 < s.re := zetaAbelContinuationDomain_re_pos hs
  have hvalue := norm_abelZetaTailIntegral_le hsRe hN
  have hderiv := norm_abelZetaTailDerivIntegral_le hsRe hN
  rw [deriv_riemannZeta_sub_abelZetaDerivApprox hs hN, norm_neg]
  unfold abelZetaDerivError
  calc
    ‖abelZetaTailIntegral s N + s * abelZetaTailDerivIntegral s N‖
        ≤ ‖abelZetaTailIntegral s N‖ +
            ‖s * abelZetaTailDerivIntegral s N‖ := norm_add_le _ _
    _ = ‖abelZetaTailIntegral s N‖ +
          ‖s‖ * ‖abelZetaTailDerivIntegral s N‖ := by rw [norm_mul]
    _ ≤ (N : ℝ) ^ (-s.re) / s.re +
          ‖s‖ * ((N : ℝ) ^ (-s.re) *
            (Real.log (N : ℝ) / s.re + 1 / s.re ^ 2)) := by
      gcongr

/-- The actual zeta derivative lies in the first corrected Euler--Maclaurin error ball. -/
theorem norm_deriv_riemannZeta_sub_eulerMaclaurinOneZetaDerivApprox_le
    {s : ℂ} (hs : s ∈ zetaAbelContinuationDomain) {N : ℕ} (hN : 1 ≤ N) :
    ‖deriv riemannZeta s - eulerMaclaurinOneZetaDerivApprox s N‖ ≤
      eulerMaclaurinOneZetaDerivError s N := by
  have hsRe : 0 < s.re := zetaAbelContinuationDomain_re_pos hs
  have hvalue := norm_integral_abelQuadraticTailKernel_le hsRe hN
  have hderiv := norm_abelQuadraticTailDerivIntegral_le hsRe hN
  rw [deriv_riemannZeta_sub_eulerMaclaurinOneZetaDerivApprox hs hN, norm_neg]
  unfold eulerMaclaurinOneZetaDerivError
  calc
    ‖(2 * s + 1) * (∫ u in Ioi (N : ℝ), abelQuadraticTailKernel s u) +
        s * (s + 1) * abelQuadraticTailDerivIntegral s N‖ ≤
        ‖(2 * s + 1) *
          (∫ u in Ioi (N : ℝ), abelQuadraticTailKernel s u)‖ +
        ‖s * (s + 1) * abelQuadraticTailDerivIntegral s N‖ := norm_add_le _ _
    _ = ‖2 * s + 1‖ *
          ‖∫ u in Ioi (N : ℝ), abelQuadraticTailKernel s u‖ +
        ‖s * (s + 1)‖ * ‖abelQuadraticTailDerivIntegral s N‖ := by
      rw [norm_mul, norm_mul]
    _ ≤ ‖2 * s + 1‖ * ((N : ℝ) ^ (-s.re - 1) / (8 * (s.re + 1))) +
        ‖s * (s + 1)‖ * ((1 / 8 : ℝ) * ((N : ℝ) ^ (-(s.re + 1)) *
          (Real.log (N : ℝ) / (s.re + 1) + 1 / (s.re + 1) ^ 2))) := by
      gcongr

/-- First-corrected Euler--Maclaurin centers at the reflected right-half point, together with the
compiled digamma remainder, certify the pointwise Speiser sign condition on the height-ten
segment. -/
theorem speiserStrictNegativePoint_of_reflected_eulerMaclaurinOne_margins
    (s : ℂ) (hs0 : 0 < s.re) (hsHalf : s.re ≤ 1 / 2)
    {N : ℕ} (hN : 1 ≤ N)
    (hzMargin :
      eulerMaclaurinOneZetaError (1 - s) N <
        ‖eulerMaclaurinOneZetaApprox (1 - s) N‖)
    (hupper : levinsonMontgomeryReflectedArchimedeanUpper s < 0)
    (hcross :
      levinsonMontgomeryReflectedArchimedeanUpper s *
          (‖eulerMaclaurinOneZetaApprox (1 - s) N‖ -
            eulerMaclaurinOneZetaError (1 - s) N) ^ 2 <
        (eulerMaclaurinOneZetaDerivApprox (1 - s) N *
            conj (eulerMaclaurinOneZetaApprox (1 - s) N)).re -
          (eulerMaclaurinOneZetaDerivError (1 - s) N *
              (‖eulerMaclaurinOneZetaApprox (1 - s) N‖ +
                eulerMaclaurinOneZetaError (1 - s) N) +
            ‖eulerMaclaurinOneZetaDerivApprox (1 - s) N‖ *
              eulerMaclaurinOneZetaError (1 - s) N)) :
    riemannZeta s ≠ 0 ∧ deriv riemannZeta s ≠ 0 ∧
      (speiserZetaDerivRatio s).re < 0 := by
  have hs1 : s.re < 1 := by linarith
  have hwOne : 1 - s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have hwDomain : 1 - s ∈ zetaAbelContinuationDomain := by
    refine ⟨hwOne, ?_⟩
    unfold zetaAbelContinuationReLower
    norm_num
    linarith
  have hzBound :=
    norm_riemannZeta_sub_eulerMaclaurinOneZetaApprox_le hwDomain hN
  have hdBound :=
    norm_deriv_riemannZeta_sub_eulerMaclaurinOneZetaDerivApprox_le hwDomain hN
  have hratio := ratio_re_gt_of_approx hzBound hdBound hzMargin hupper hcross
  have hreflected : riemannZeta (1 - s) ≠ 0 := hratio.1
  have hzeta : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_sub_ne_zero hs0 hs1 hreflected
  have hsArchAbs :=
    abs_levinsonMontgomeryLogDerivArchimedeanTerm_sub_approx_le
      (s := s) (by linarith)
  have hwArchAbs :=
    abs_levinsonMontgomeryLogDerivArchimedeanTerm_sub_approx_le
      (s := 1 - s) (by norm_num; linarith)
  have harchUpper :
      levinsonMontgomeryLogDerivArchimedeanTerm s +
          levinsonMontgomeryLogDerivArchimedeanTerm (1 - s) ≤
        levinsonMontgomeryReflectedArchimedeanUpper s := by
    have hsUpper := (abs_le.mp hsArchAbs).2
    have hwUpper := (abs_le.mp hwArchAbs).2
    unfold levinsonMontgomeryReflectedArchimedeanUpper
    linarith
  have hreflection :=
    logDeriv_riemannZeta_re_reflection hs0 hs1 hzeta hreflected
  have hratioLog :
      levinsonMontgomeryReflectedArchimedeanUpper s <
        (logDeriv riemannZeta (1 - s)).re := by
    simpa only [logDeriv_apply] using hratio.2
  have hlogNegative : (logDeriv riemannZeta s).re < 0 := by
    rw [hreflection]
    linarith [hratioLog, harchUpper]
  have hderiv : deriv riemannZeta s ≠ 0 := by
    intro hzero
    rw [logDeriv_apply, hzero, zero_div, Complex.zero_re] at hlogNegative
    exact (lt_irrefl 0) hlogNegative
  refine ⟨hzeta, hderiv, ?_⟩
  simpa only [speiserZetaDerivRatio, logDeriv_apply] using hlogNegative

end

end LeanLab.Riemann
