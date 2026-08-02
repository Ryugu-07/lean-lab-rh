import LeanLab.Riemann.LevinsonMontgomeryEulerMaclaurin

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Second Euler--Maclaurin correction for the height-ten evaluator

This module extracts the Bernoulli `s * N^(-s-1) / 12` term from the existing quadratic-periodic
remainder. The remaining cubic-periodic integral gains one full power of the cutoff.
-/

open Complex Filter Finset MeasureTheory Real Set Topology
open scoped BigOperators ComplexConjugate Topology

namespace LeanLab.Riemann

noncomputable section

/-- The zero-endpoint cubic primitive of `abelQuadraticPeriodic + 1/12`. -/
def abelCubicPeriodic (u : ℝ) : ℝ :=
  (Int.fract u) ^ 3 / 6 - (Int.fract u) ^ 2 / 4 + Int.fract u / 12

/-- The cubic-periodic remainder kernel after extracting the first Bernoulli correction. -/
def abelCubicTailKernel (s : ℂ) (u : ℝ) : ℂ :=
  (abelCubicPeriodic u : ℂ) * (u : ℂ) ^ (-s - 3)

/-- The cubic periodic primitive has the elementary uniform bound `1/48`. -/
theorem abs_abelCubicPeriodic_le (u : ℝ) :
    |abelCubicPeriodic u| ≤ 1 / 48 := by
  let x := Int.fract u
  have hx0 : 0 ≤ x := Int.fract_nonneg u
  have hx1 : x ≤ 1 := (Int.fract_lt_one u).le
  have hcenter : |2 * x - 1| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hquad : x * (1 - x) ≤ 1 / 4 := by
    nlinarith [sq_nonneg (2 * x - 1)]
  have hfactor :
      abelCubicPeriodic u = x * (x - 1) * (2 * x - 1) / 12 := by
    simp only [abelCubicPeriodic, x]
    ring
  rw [hfactor, abs_div, abs_mul, abs_mul,
    abs_of_nonneg hx0, abs_of_nonpos (sub_nonpos.mpr hx1)]
  rw [show |(12 : ℝ)| = 12 by norm_num]
  rw [show -(x - 1) = 1 - x by ring]
  have hnonneg : 0 ≤ x * (1 - x) := mul_nonneg hx0 (sub_nonneg.mpr hx1)
  calc
    x * (1 - x) * |2 * x - 1| / 12 ≤ (1 / 4 : ℝ) * 1 / 12 := by
      gcongr
    _ = 1 / 48 := by norm_num

private theorem second_fract_eq_sub_natCast_of_mem_Ico
    (k : ℕ) {u : ℝ} (hu : u ∈ Ico (k : ℝ) (k + 1 : ℝ)) :
    Int.fract u = u - k := by
  have hfloor : Int.floor u = (k : ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor
    · exact_mod_cast hu.1
    · exact_mod_cast hu.2
  simp only [Int.fract, hfloor, Int.cast_natCast]

private theorem integral_quadratic_shift_eq_cubic_shift_sub
    (s : ℂ) (hs : 0 < s.re) (k : ℕ) (hk : 1 ≤ k) :
    (∫ u in (k : ℝ)..(k + 1 : ℝ),
        ((((u - k) ^ 2 / 2 - (u - k) / 2 : ℝ) : ℂ)) *
          (u : ℂ) ^ (-s - 2)) =
      (s + 2) *
          (∫ u in (k : ℝ)..(k + 1 : ℝ),
            ((((u - k) ^ 3 / 6 - (u - k) ^ 2 / 4 +
                (u - k) / 12 : ℝ) : ℂ)) * (u : ℂ) ^ (-s - 3)) -
        (1 / 12 : ℂ) *
          ∫ u in (k : ℝ)..(k + 1 : ℝ), (u : ℂ) ^ (-s - 2) := by
  let q : ℝ → ℂ := fun u =>
    ((((u - k) ^ 3 / 6 - (u - k) ^ 2 / 4 +
      (u - k) / 12 : ℝ) : ℂ))
  let q' : ℝ → ℂ := fun u =>
    ((((u - k) ^ 2 / 2 - (u - k) / 2 + 1 / 12 : ℝ) : ℂ))
  let f : ℝ → ℂ := fun u => (u : ℂ) ^ (-s - 2)
  let f' : ℝ → ℂ := fun u => -(s + 2) * (u : ℂ) ^ (-s - 3)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  have hq : ∀ u ∈ Set.uIcc (k : ℝ) (k + 1 : ℝ), HasDerivAt q (q' u) u := by
    intro u _hu
    have hbase := (hasDerivAt_id u).sub_const (k : ℝ)
    have hreal := (((hbase.pow 3).div_const 6).sub
      ((hbase.pow 2).div_const 4)).add (hbase.div_const 12)
    have hreal' : HasDerivAt
        (fun x : ℝ => (x - k) ^ 3 / 6 - (x - k) ^ 2 / 4 + (x - k) / 12)
        ((u - k) ^ 2 / 2 - (u - k) / 2 + 1 / 12) u := by
      apply hreal.congr_deriv
      simp only [id_eq]
      ring_nf
    simpa [q, q'] using hreal'.ofReal_comp
  have hf : ∀ u ∈ Set.uIcc (k : ℝ) (k + 1 : ℝ), HasDerivAt f (f' u) u := by
    intro u hu
    have huIcc : u ∈ Icc (k : ℝ) (k + 1 : ℝ) := by
      simpa [uIcc_of_le (by norm_num : (k : ℝ) ≤ k + 1)] using hu
    have hu0 : 0 < u := hkpos.trans_le huIcc.1
    have hexp : -s - 2 ≠ 0 := by
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
    have hconst : ContinuousOn (fun _ : ℝ => (-(s + 2) : ℂ))
        (Icc (k : ℝ) (k + 1 : ℝ)) := continuousOn_const
    have hpow : ContinuousOn (fun u : ℝ => (u : ℂ) ^ (-s - 3))
        (Icc (k : ℝ) (k + 1 : ℝ)) :=
      Complex.continuousOn_ofReal_cpow (r := -s - 3) (a := (k : ℝ))
        (b := (k + 1 : ℝ)) hkpos
    exact (hconst.mul hpow).congr (fun _ _ => rfl)
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hq hf hqInt hfInt
  have hqLeft : q k = 0 := by simp [q]
  have hqRight : q (k + 1) = 0 := by norm_num [q]
  rw [hqLeft, hqRight, zero_mul, zero_mul, sub_zero, zero_sub] at hibp
  have hleft :
      (∫ u in (k : ℝ)..(k + 1 : ℝ), q u * f' u) =
        -(s + 2) * ∫ u in (k : ℝ)..(k + 1 : ℝ),
          q u * (u : ℂ) ^ (-s - 3) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u _hu
    simp only [q, f']
    ring
  rw [hleft] at hibp
  have hfCont : ContinuousOn f (Set.uIcc (k : ℝ) (k + 1 : ℝ)) := by
    intro u hu
    exact (hf u hu).continuousAt.continuousWithinAt
  have hmainInt : IntervalIntegrable
      (fun u : ℝ =>
        ((((u - k) ^ 2 / 2 - (u - k) / 2 : ℝ) : ℂ)) *
          (u : ℂ) ^ (-s - 2)) volume (k : ℝ) (k + 1 : ℝ) := by
    apply ContinuousOn.intervalIntegrable
    have hpoly : Continuous
        (fun u : ℝ => ((((u - k) ^ 2 / 2 - (u - k) / 2 : ℝ) : ℂ))) := by
      fun_prop
    exact hpoly.continuousOn.mul (by simpa [f] using hfCont)
  have hconstInt : IntervalIntegrable
      (fun u : ℝ => (1 / 12 : ℂ) * (u : ℂ) ^ (-s - 2))
      volume (k : ℝ) (k + 1 : ℝ) := by
    have hfInterval : IntervalIntegrable f volume (k : ℝ) (k + 1 : ℝ) :=
      hfCont.intervalIntegrable
    simpa [f] using hfInterval.const_mul (1 / 12 : ℂ)
  have hright :
      (∫ u in (k : ℝ)..(k + 1 : ℝ), q' u * f u) =
        (∫ u in (k : ℝ)..(k + 1 : ℝ),
          ((((u - k) ^ 2 / 2 - (u - k) / 2 : ℝ) : ℂ)) *
            (u : ℂ) ^ (-s - 2)) +
          (1 / 12 : ℂ) *
            ∫ u in (k : ℝ)..(k + 1 : ℝ), (u : ℂ) ^ (-s - 2) := by
    calc
      (∫ u in (k : ℝ)..(k + 1 : ℝ), q' u * f u) =
          ∫ u in (k : ℝ)..(k + 1 : ℝ),
            (((((u - k) ^ 2 / 2 - (u - k) / 2 : ℝ) : ℂ)) *
                (u : ℂ) ^ (-s - 2) +
              (1 / 12 : ℂ) * (u : ℂ) ^ (-s - 2)) := by
        apply intervalIntegral.integral_congr
        intro u _hu
        simp only [q', f]
        norm_num only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_div,
          Complex.ofReal_one, Complex.ofReal_ofNat]
        ring
      _ = (∫ u in (k : ℝ)..(k + 1 : ℝ),
            ((((u - k) ^ 2 / 2 - (u - k) / 2 : ℝ) : ℂ)) *
              (u : ℂ) ^ (-s - 2)) +
            ∫ u in (k : ℝ)..(k + 1 : ℝ),
              (1 / 12 : ℂ) * (u : ℂ) ^ (-s - 2) :=
        intervalIntegral.integral_add hmainInt hconstInt
      _ = (∫ u in (k : ℝ)..(k + 1 : ℝ),
            ((((u - k) ^ 2 / 2 - (u - k) / 2 : ℝ) : ℂ)) *
              (u : ℂ) ^ (-s - 2)) +
            (1 / 12 : ℂ) *
              ∫ u in (k : ℝ)..(k + 1 : ℝ), (u : ℂ) ^ (-s - 2) := by
        rw [intervalIntegral.integral_const_mul]
  rw [hright] at hibp
  simp only [q] at hibp
  linear_combination hibp

private theorem integral_quadratic_unit_eq_cubic_sub
    (s : ℂ) (hs : 0 < s.re) (k : ℕ) (hk : 1 ≤ k) :
    (∫ u in (k : ℝ)..(k + 1 : ℝ), abelQuadraticTailKernel s u) =
      (s + 2) *
          (∫ u in (k : ℝ)..(k + 1 : ℝ), abelCubicTailKernel s u) -
        (1 / 12 : ℂ) *
          ∫ u in (k : ℝ)..(k + 1 : ℝ), (u : ℂ) ^ (-s - 2) := by
  have hraw := integral_quadratic_shift_eq_cubic_shift_sub s hs k hk
  have hne : ∀ᵐ u : ℝ ∂volume, u ≠ (k + 1 : ℝ) := by
    simpa only [Set.mem_singleton_iff] using
      (Set.countable_singleton (k + 1 : ℝ)).ae_notMem (volume : Measure ℝ)
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
      second_fract_eq_sub_natCast_of_mem_Ico k ⟨hu.1.le, hult⟩]
  have hcubic :
      (∫ u in (k : ℝ)..(k + 1 : ℝ), abelCubicTailKernel s u) =
        ∫ u in (k : ℝ)..(k + 1 : ℝ),
          ((((u - k) ^ 3 / 6 - (u - k) ^ 2 / 4 +
              (u - k) / 12 : ℝ) : ℂ)) * (u : ℂ) ^ (-s - 3) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hne] with u hune hu
    rw [uIoc_of_le (by norm_num : (k : ℝ) ≤ k + 1)] at hu
    have hult : u < (k + 1 : ℝ) := lt_of_le_of_ne hu.2 hune
    rw [abelCubicTailKernel, abelCubicPeriodic,
      second_fract_eq_sub_natCast_of_mem_Ico k ⟨hu.1.le, hult⟩]
  calc
    (∫ u in (k : ℝ)..(k + 1 : ℝ), abelQuadraticTailKernel s u) =
        ∫ u in (k : ℝ)..(k + 1 : ℝ),
          ((((u - k) ^ 2 / 2 - (u - k) / 2 : ℝ) : ℂ)) *
            (u : ℂ) ^ (-s - 2) := hquadratic
    _ = (s + 2) *
          (∫ u in (k : ℝ)..(k + 1 : ℝ),
            ((((u - k) ^ 3 / 6 - (u - k) ^ 2 / 4 +
                (u - k) / 12 : ℝ) : ℂ)) * (u : ℂ) ^ (-s - 3)) -
        (1 / 12 : ℂ) *
          ∫ u in (k : ℝ)..(k + 1 : ℝ), (u : ℂ) ^ (-s - 2) := hraw
    _ = (s + 2) *
          (∫ u in (k : ℝ)..(k + 1 : ℝ), abelCubicTailKernel s u) -
        (1 / 12 : ℂ) *
          ∫ u in (k : ℝ)..(k + 1 : ℝ), (u : ℂ) ^ (-s - 2) := by
      rw [← hcubic]

private theorem integrableOn_abelCubicTailKernel_Ioi
    {s : ℂ} (hs : 0 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    IntegrableOn (abelCubicTailKernel s) (Ioi (N : ℝ)) := by
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hNreal
  have hmajor : IntegrableOn (fun u : ℝ => (1 / 48 : ℝ) * u ^ (-s.re - 3))
      (Ioi (N : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hNpos).const_mul (1 / 48)
  have hmeas : AEStronglyMeasurable (abelCubicTailKernel s)
      (volume.restrict (Ioi (N : ℝ))) := by
    apply Measurable.aestronglyMeasurable
    exact ((((measurable_fract.pow_const 3).div_const 6).sub
      ((measurable_fract.pow_const 2).div_const 4)).add
      (measurable_fract.div_const 12)).complex_ofReal.mul
      (by simpa using Complex.measurable_ofReal.pow_const (-s - 3))
  refine hmajor.mono' hmeas ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ ?_)
  intro u hu
  have hu0 : 0 < u := hNpos.trans hu
  rw [abelCubicTailKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos hu0]
  norm_num
  exact mul_le_mul_of_nonneg_right (abs_abelCubicPeriodic_le u)
    (Real.rpow_nonneg hu0.le _)

private theorem second_integrableOn_abelQuadraticTailKernel_Ioi
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

private theorem integral_quadratic_natInterval_eq_cubic_sub
    (s : ℂ) (hs : 0 < s.re) {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) :
    (∫ u in (N : ℝ)..(M : ℝ), abelQuadraticTailKernel s u) =
      (s + 2) * (∫ u in (N : ℝ)..(M : ℝ), abelCubicTailKernel s u) -
        (1 / 12 : ℂ) * ∫ u in (N : ℝ)..(M : ℝ), (u : ℂ) ^ (-s - 2) := by
  have hquadratic := second_integrableOn_abelQuadraticTailKernel_Ioi hs hN
  have hcubic := integrableOn_abelCubicTailKernel_Ioi hs hN
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hNreal
  have hpure : IntegrableOn (fun u : ℝ => (u : ℂ) ^ (-s - 2)) (Ioi (N : ℝ)) :=
    integrableOn_Ioi_cpow_of_lt (by norm_num; linarith) hNpos
  have hquadraticIci : IntegrableOn (abelQuadraticTailKernel s) (Ici (N : ℝ)) :=
    (integrableOn_Ici_iff_integrableOn_Ioi
      (f := abelQuadraticTailKernel s) (μ := volume)).mpr hquadratic
  have hcubicIci : IntegrableOn (abelCubicTailKernel s) (Ici (N : ℝ)) :=
    (integrableOn_Ici_iff_integrableOn_Ioi
      (f := abelCubicTailKernel s) (μ := volume)).mpr hcubic
  have hpureIci : IntegrableOn (fun u : ℝ => (u : ℂ) ^ (-s - 2)) (Ici (N : ℝ)) :=
    (integrableOn_Ici_iff_integrableOn_Ioi
      (f := fun u : ℝ => (u : ℂ) ^ (-s - 2)) (μ := volume)).mpr hpure
  induction M, hNM using Nat.le_induction with
  | base => simp
  | succ M hNM ih =>
      have hM : 1 ≤ M := hN.trans hNM
      have hunit := integral_quadratic_unit_eq_cubic_sub s hs M hM
      have hqLeft : IntervalIntegrable (abelQuadraticTailKernel s) volume
          (N : ℝ) (M : ℝ) := by
        apply IntegrableOn.intervalIntegrable
        exact hquadraticIci.mono_set (by
          intro u hu
          rw [Set.uIcc_of_le (by exact_mod_cast hNM)] at hu
          exact hu.1)
      have hqRight : IntervalIntegrable (abelQuadraticTailKernel s) volume
          (M : ℝ) (M + 1 : ℝ) := by
        apply IntegrableOn.intervalIntegrable
        exact hquadraticIci.mono_set (by
          intro u hu
          rw [Set.uIcc_of_le (by norm_num : (M : ℝ) ≤ M + 1)] at hu
          exact (show (N : ℝ) ≤ M by exact_mod_cast hNM).trans hu.1)
      have hcLeft : IntervalIntegrable (abelCubicTailKernel s) volume
          (N : ℝ) (M : ℝ) := by
        apply IntegrableOn.intervalIntegrable
        exact hcubicIci.mono_set (by
          intro u hu
          rw [Set.uIcc_of_le (by exact_mod_cast hNM)] at hu
          exact hu.1)
      have hcRight : IntervalIntegrable (abelCubicTailKernel s) volume
          (M : ℝ) (M + 1 : ℝ) := by
        apply IntegrableOn.intervalIntegrable
        exact hcubicIci.mono_set (by
          intro u hu
          rw [Set.uIcc_of_le (by norm_num : (M : ℝ) ≤ M + 1)] at hu
          exact (show (N : ℝ) ≤ M by exact_mod_cast hNM).trans hu.1)
      have hpLeft : IntervalIntegrable (fun u : ℝ => (u : ℂ) ^ (-s - 2)) volume
          (N : ℝ) (M : ℝ) := by
        apply IntegrableOn.intervalIntegrable
        exact hpureIci.mono_set (by
          intro u hu
          rw [Set.uIcc_of_le (by exact_mod_cast hNM)] at hu
          exact hu.1)
      have hpRight : IntervalIntegrable (fun u : ℝ => (u : ℂ) ^ (-s - 2)) volume
          (M : ℝ) (M + 1 : ℝ) := by
        apply IntegrableOn.intervalIntegrable
        exact hpureIci.mono_set (by
          intro u hu
          rw [Set.uIcc_of_le (by norm_num : (M : ℝ) ≤ M + 1)] at hu
          exact (show (N : ℝ) ≤ M by exact_mod_cast hNM).trans hu.1)
      norm_num [Nat.cast_add, Nat.cast_one]
      rw [← intervalIntegral.integral_add_adjacent_intervals hqLeft hqRight,
        ← intervalIntegral.integral_add_adjacent_intervals hcLeft hcRight,
        ← intervalIntegral.integral_add_adjacent_intervals hpLeft hpRight,
        ih, hunit]
      ring

/-- Extract the first Bernoulli correction from the quadratic-periodic half-line tail. -/
theorem integral_abelQuadraticTailKernel_eq_cubicTail_sub
    {s : ℂ} (hs : 0 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    (∫ u in Ioi (N : ℝ), abelQuadraticTailKernel s u) =
      (s + 2) * (∫ u in Ioi (N : ℝ), abelCubicTailKernel s u) -
        (N : ℂ) ^ (-s - 1) / (12 * (s + 1)) := by
  have hquadratic := second_integrableOn_abelQuadraticTailKernel_Ioi hs hN
  have hcubic := integrableOn_abelCubicTailKernel_Ioi hs hN
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hNreal
  have hpure : IntegrableOn (fun u : ℝ => (u : ℂ) ^ (-s - 2)) (Ioi (N : ℝ)) :=
    integrableOn_Ioi_cpow_of_lt (by norm_num; linarith) hNpos
  have hquadraticTendsto := intervalIntegral_tendsto_integral_Ioi
    (N : ℝ) hquadratic tendsto_natCast_atTop_atTop
  have hcubicTendsto := intervalIntegral_tendsto_integral_Ioi
    (N : ℝ) hcubic tendsto_natCast_atTop_atTop
  have hpureTendsto := intervalIntegral_tendsto_integral_Ioi
    (N : ℝ) hpure tendsto_natCast_atTop_atTop
  have hfinite :
      (fun M : ℕ => ∫ u in (N : ℝ)..(M : ℝ), abelQuadraticTailKernel s u) =ᶠ[atTop]
        fun M : ℕ =>
          (s + 2) * (∫ u in (N : ℝ)..(M : ℝ), abelCubicTailKernel s u) -
            (1 / 12 : ℂ) * ∫ u in (N : ℝ)..(M : ℝ), (u : ℂ) ^ (-s - 2) := by
    filter_upwards [eventually_ge_atTop N] with M hNM
    exact integral_quadratic_natInterval_eq_cubic_sub s hs hN hNM
  have hrightTendsto :
      Tendsto
        (fun M : ℕ =>
          (s + 2) * (∫ u in (N : ℝ)..(M : ℝ), abelCubicTailKernel s u) -
            (1 / 12 : ℂ) * ∫ u in (N : ℝ)..(M : ℝ), (u : ℂ) ^ (-s - 2))
        atTop
        (nhds ((s + 2) * (∫ u in Ioi (N : ℝ), abelCubicTailKernel s u) -
          (1 / 12 : ℂ) * ∫ u in Ioi (N : ℝ), (u : ℂ) ^ (-s - 2))) :=
    by
      simpa using
        (hcubicTendsto.const_mul (s + 2)).sub
          (hpureTendsto.const_mul (1 / 12 : ℂ))
  have hlimit := tendsto_nhds_unique hquadraticTendsto
    ((tendsto_congr' hfinite).mpr hrightTendsto)
  have hpureValue :
      (∫ u in Ioi (N : ℝ), (u : ℂ) ^ (-s - 2)) =
        (N : ℂ) ^ (-s - 1) / (s + 1) := by
    rw [integral_Ioi_cpow_of_lt (a := -s - 2) (by norm_num; linarith) hNpos]
    rw [show -s - 2 + 1 = -s - 1 by ring]
    rw [show (((N : ℝ) : ℂ)) = (N : ℂ) by norm_num]
    have hsOne : s + 1 ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      norm_num at hre
      linarith
    have hneg : -s - 1 ≠ 0 := by
      intro h
      apply hsOne
      linear_combination -h
    field_simp [hsOne, hneg]
    ring
  rw [hlimit, hpureValue]
  have hsOne : s + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  field_simp [hsOne]

/-- The second corrected Euler--Maclaurin approximation. -/
def eulerMaclaurinTwoZetaApprox (s : ℂ) (N : ℕ) : ℂ :=
  eulerMaclaurinOneZetaApprox s N + s * (N : ℂ) ^ (-s - 1) / 12

/-- The cubic-periodic remainder after the second correction. -/
def eulerMaclaurinTwoZetaRemainder (s : ℂ) (N : ℕ) : ℂ :=
  -s * (s + 1) * (s + 2) *
    ∫ u in Ioi (N : ℝ), abelCubicTailKernel s u

/-- Actual zeta equals the second corrected center plus its cubic-periodic remainder. -/
theorem riemannZeta_eq_eulerMaclaurinTwoZetaApprox_add_remainder_of_re_pos
    {s : ℂ} (hsOne : s ≠ 1) (hsRe : 0 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    riemannZeta s =
      eulerMaclaurinTwoZetaApprox s N + eulerMaclaurinTwoZetaRemainder s N := by
  have hsOne' : s + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have hrem : eulerMaclaurinOneZetaRemainder s N =
      s * (N : ℂ) ^ (-s - 1) / 12 + eulerMaclaurinTwoZetaRemainder s N := by
    unfold eulerMaclaurinOneZetaRemainder eulerMaclaurinTwoZetaRemainder
    rw [integral_abelQuadraticTailKernel_eq_cubicTail_sub hsRe hN]
    generalize (∫ u in Ioi (N : ℝ), abelCubicTailKernel s u) = C
    generalize (N : ℂ) ^ (-s - 1) = P
    field_simp [hsOne']
    ring
  rw [riemannZeta_eq_eulerMaclaurinOneZetaApprox_add_remainder_of_re_pos
    hsOne hsRe hN, hrem]
  unfold eulerMaclaurinTwoZetaApprox
  ring

/-- Explicit value radius for the second corrected formula. -/
def eulerMaclaurinTwoZetaError (s : ℂ) (N : ℕ) : ℝ :=
  ‖s * (s + 1) * (s + 2)‖ *
    ((1 / 48 : ℝ) * ((N : ℝ) ^ (-s.re - 2) / (s.re + 2)))

/-- Norm bound for the cubic-periodic remainder integral. -/
theorem norm_integral_abelCubicTailKernel_le
    {s : ℂ} (hs : 0 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    ‖∫ u in Ioi (N : ℝ), abelCubicTailKernel s u‖ ≤
      (1 / 48 : ℝ) * ((N : ℝ) ^ (-s.re - 2) / (s.re + 2)) := by
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hNreal
  have hmajor : IntegrableOn (fun u : ℝ => (1 / 48 : ℝ) * u ^ (-s.re - 3))
      (Ioi (N : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hNpos).const_mul (1 / 48)
  have hbound :
      ∀ᵐ u ∂(volume.restrict (Ioi (N : ℝ))),
        ‖abelCubicTailKernel s u‖ ≤ (1 / 48 : ℝ) * u ^ (-s.re - 3) := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ ?_)
    intro u hu
    have hu0 : 0 < u := hNpos.trans hu
    rw [abelCubicTailKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos hu0]
    norm_num
    exact mul_le_mul_of_nonneg_right (abs_abelCubicPeriodic_le u)
      (Real.rpow_nonneg hu0.le _)
  calc
    ‖∫ u in Ioi (N : ℝ), abelCubicTailKernel s u‖ ≤
        ∫ u in Ioi (N : ℝ), (1 / 48 : ℝ) * u ^ (-s.re - 3) :=
      MeasureTheory.norm_integral_le_of_norm_le hmajor hbound
    _ = (1 / 48 : ℝ) * ((N : ℝ) ^ (-s.re - 2) / (s.re + 2)) := by
      rw [integral_const_mul,
        integral_Ioi_rpow_of_lt (a := -s.re - 3) (by linarith) hNpos]
      rw [show -s.re - 3 + 1 = -(s.re + 2) by ring]
      field_simp [ne_of_gt (by linarith : 0 < s.re + 2)]
      ring

/-- The actual zeta value lies in the second corrected error ball. -/
theorem norm_riemannZeta_sub_eulerMaclaurinTwoZetaApprox_le_of_re_pos
    {s : ℂ} (hsOne : s ≠ 1) (hsRe : 0 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    ‖riemannZeta s - eulerMaclaurinTwoZetaApprox s N‖ ≤
      eulerMaclaurinTwoZetaError s N := by
  have htail := norm_integral_abelCubicTailKernel_le hsRe hN
  rw [riemannZeta_eq_eulerMaclaurinTwoZetaApprox_add_remainder_of_re_pos
    hsOne hsRe hN, add_sub_cancel_left]
  unfold eulerMaclaurinTwoZetaRemainder eulerMaclaurinTwoZetaError
  rw [norm_mul, norm_mul, norm_mul, norm_neg]
  calc
    ‖s‖ * ‖s + 1‖ * ‖s + 2‖ *
        ‖∫ u in Ioi (N : ℝ), abelCubicTailKernel s u‖ =
      ‖s * (s + 1) * (s + 2)‖ *
        ‖∫ u in Ioi (N : ℝ), abelCubicTailKernel s u‖ := by
      rw [norm_mul, norm_mul]
    _ ≤ ‖s * (s + 1) * (s + 2)‖ *
        ((1 / 48 : ℝ) * ((N : ℝ) ^ (-s.re - 2) / (s.re + 2))) :=
      mul_le_mul_of_nonneg_left htail (norm_nonneg _)

/-- Parameter derivative of the cubic-periodic tail integral. -/
def abelCubicTailDerivIntegral (s : ℂ) (N : ℕ) : ℂ :=
  ∫ u in Ioi (N : ℝ),
    -((Real.log u : ℝ) : ℂ) * abelCubicTailKernel s u

private theorem abelCubicTailKernel_hasDerivAt_in_param
    (u : ℝ) (hu : 0 < u) (z : ℂ) :
    HasDerivAt (fun w => abelCubicTailKernel w u)
      (-((Real.log u : ℝ) : ℂ) * abelCubicTailKernel z u) z := by
  have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  have hexp : HasDerivAt (fun w : ℂ => -w - 3) (-1) z := by
    simpa using (hasDerivAt_id z).neg.sub_const (3 : ℂ)
  have hpow := HasDerivAt.const_cpow (c := (u : ℂ)) hexp (Or.inl huC)
  have h := hpow.const_mul (abelCubicPeriodic u : ℂ)
  simpa [abelCubicTailKernel, Complex.ofReal_log hu.le,
    mul_comm, mul_left_comm, mul_assoc] using h

private theorem abelCubicTailDerivIntegral_aestronglyMeasurable
    (s : ℂ) (N : ℕ) :
    AEStronglyMeasurable
      (fun u : ℝ =>
        -((Real.log u : ℝ) : ℂ) * abelCubicTailKernel s u)
      (volume.restrict (Ioi (N : ℝ))) := by
  have hkernel : Measurable (abelCubicTailKernel s) :=
    ((((measurable_fract.pow_const 3).div_const 6).sub
      ((measurable_fract.pow_const 2).div_const 4)).add
      (measurable_fract.div_const 12)).complex_ofReal.mul
      (by simpa using Complex.measurable_ofReal.pow_const (-s - 3))
  exact (Real.measurable_log.complex_ofReal.neg.mul hkernel).aestronglyMeasurable

private theorem second_integrableOn_log_mul_rpow_neg_sub_one
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

private theorem second_integral_Ioi_log_mul_rpow_neg_sub_one
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
  have hint := second_integrableOn_log_mul_rpow_neg_sub_one ha hc
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

private theorem abelCubicTailIntegral_hasDerivAt
    {s : ℂ} (hs : 0 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    HasDerivAt
      (fun w => ∫ u in Ioi (N : ℝ), abelCubicTailKernel w u)
      (abelCubicTailDerivIntegral s N) s := by
  let epsilon : ℝ := s.re / 2
  have hepsilon : 0 < epsilon := half_pos hs
  obtain ⟨delta, hdelta, hreal⟩ :=
    Complex.exists_pos_radius_forall_mem_ball_re_ge
      (z₀ := s) (a := epsilon) (half_lt_self hs)
  let F : ℂ → ℝ → ℂ := abelCubicTailKernel
  let F' : ℂ → ℝ → ℂ := fun z u =>
    -((Real.log u : ℝ) : ℂ) * F z u
  let bound : ℝ → ℝ := fun u =>
    (1 / 48 : ℝ) * (Real.log u * u ^ (-epsilon - 3))
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hNreal
  have hboundInt : Integrable bound (volume.restrict (Ioi (N : ℝ))) := by
    have hraw :=
      (second_integrableOn_log_mul_rpow_neg_sub_one (a := epsilon + 2)
        (by linarith) hNreal).const_mul (1 / 48 : ℝ)
    apply hraw.congr
    filter_upwards with u
    simp only [bound]
    congr 3
    ring
  have hFmeas :
      ∀ᶠ z in nhds s,
        AEStronglyMeasurable (F z) (volume.restrict (Ioi (N : ℝ))) := by
    refine Eventually.of_forall fun z => Measurable.aestronglyMeasurable ?_
    exact ((((measurable_fract.pow_const 3).div_const 6).sub
      ((measurable_fract.pow_const 2).div_const 4)).add
      (measurable_fract.div_const 12)).complex_ofReal.mul
      (by simpa [F] using Complex.measurable_ofReal.pow_const (-z - 3))
  have hFint : Integrable (F s) (volume.restrict (Ioi (N : ℝ))) := by
    simpa [F, IntegrableOn] using integrableOn_abelCubicTailKernel_Ioi hs hN
  have hF'meas :
      AEStronglyMeasurable (F' s) (volume.restrict (Ioi (N : ℝ))) := by
    simpa [F, F'] using abelCubicTailDerivIntegral_aestronglyMeasurable s N
  have hbound :
      ∀ᵐ u ∂(volume.restrict (Ioi (N : ℝ))),
        ∀ z ∈ Metric.ball s delta, ‖F' z u‖ ≤ bound u := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ ?_)
    intro u hu z hz
    have hu1 : 1 < u := lt_of_le_of_lt hNreal hu
    have hu0 : 0 < u := zero_lt_one.trans hu1
    have hzRe : epsilon ≤ z.re :=
      hreal s z (by simpa [dist_self] using hdelta) (Metric.mem_ball.mp hz)
    have hpow : u ^ (-z.re - 3) ≤ u ^ (-epsilon - 3) :=
      Real.rpow_le_rpow_of_exponent_le hu1.le (by linarith)
    have hkernel :
        ‖abelCubicTailKernel z u‖ ≤
          (1 / 48 : ℝ) * u ^ (-epsilon - 3) := by
      rw [abelCubicTailKernel, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
      norm_num
      exact (mul_le_mul_of_nonneg_right (abs_abelCubicPeriodic_le u)
        (Real.rpow_nonneg hu0.le _)).trans
          (mul_le_mul_of_nonneg_left hpow (by norm_num))
    have hlog : 0 ≤ Real.log u := Real.log_nonneg hu1.le
    calc
      ‖F' z u‖ = Real.log u * ‖abelCubicTailKernel z u‖ := by
        change ‖-((Real.log u : ℝ) : ℂ) * abelCubicTailKernel z u‖ = _
        rw [norm_mul, norm_neg, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg hlog]
      _ ≤ Real.log u * ((1 / 48 : ℝ) * u ^ (-epsilon - 3)) :=
        mul_le_mul_of_nonneg_left hkernel hlog
      _ = bound u := by simp only [bound]; ring
  have hderiv :
      ∀ᵐ u ∂(volume.restrict (Ioi (N : ℝ))),
        ∀ z ∈ Metric.ball s delta, HasDerivAt (fun w => F w u) (F' z u) z := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ ?_)
    intro u hu z _hz
    have hu0 : 0 < u := hNpos.trans hu
    simpa [F, F'] using abelCubicTailKernel_hasDerivAt_in_param u hu0 z
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (N : ℝ))) (F := F) (F' := F') (x₀ := s)
    (s := Metric.ball s delta) (bound := bound) (Metric.ball_mem_nhds s hdelta)
    (hF_meas := hFmeas) (hF_int := hFint) (hF'_meas := hF'meas)
    (h_bound := hbound) (bound_integrable := hboundInt) (h_diff := hderiv)
  rcases h with ⟨_, hDeriv⟩
  simpa [abelCubicTailDerivIntegral, F, F'] using hDeriv

/-- Explicit norm bound for the parameter derivative of the cubic-periodic tail. -/
theorem norm_abelCubicTailDerivIntegral_le
    {s : ℂ} (hs : 0 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    ‖abelCubicTailDerivIntegral s N‖ ≤
      (1 / 48 : ℝ) * ((N : ℝ) ^ (-(s.re + 2)) *
        (Real.log (N : ℝ) / (s.re + 2) + 1 / (s.re + 2) ^ 2)) := by
  let a : ℝ := s.re + 2
  have ha : 0 < a := by simp only [a]; linarith
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hNreal
  have hmajor : IntegrableOn
      (fun u : ℝ => (1 / 48 : ℝ) * (Real.log u * u ^ (-a - 1)))
      (Ioi (N : ℝ)) :=
    (second_integrableOn_log_mul_rpow_neg_sub_one ha hNreal).const_mul (1 / 48)
  have hbound :
      ∀ᵐ u ∂(volume.restrict (Ioi (N : ℝ))),
        ‖-((Real.log u : ℝ) : ℂ) * abelCubicTailKernel s u‖ ≤
          (1 / 48 : ℝ) * (Real.log u * u ^ (-a - 1)) := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ ?_)
    intro u hu
    have hu1 : 1 ≤ u := hNreal.trans hu.le
    have hu0 : 0 < u := hNpos.trans hu
    have hlog : 0 ≤ Real.log u := Real.log_nonneg hu1
    have hkernel :
        ‖abelCubicTailKernel s u‖ ≤ (1 / 48 : ℝ) * u ^ (-a - 1) := by
      rw [abelCubicTailKernel, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
      norm_num
      rw [show -s.re - 3 = -a - 1 by simp only [a]; ring]
      exact mul_le_mul_of_nonneg_right (abs_abelCubicPeriodic_le u)
        (Real.rpow_nonneg hu0.le _)
    calc
      ‖-((Real.log u : ℝ) : ℂ) * abelCubicTailKernel s u‖ =
          Real.log u * ‖abelCubicTailKernel s u‖ := by
        rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hlog]
      _ ≤ Real.log u * ((1 / 48 : ℝ) * u ^ (-a - 1)) :=
        mul_le_mul_of_nonneg_left hkernel hlog
      _ = (1 / 48 : ℝ) * (Real.log u * u ^ (-a - 1)) := by ring
  calc
    ‖abelCubicTailDerivIntegral s N‖
        ≤ ∫ u in Ioi (N : ℝ),
            (1 / 48 : ℝ) * (Real.log u * u ^ (-a - 1)) := by
      exact MeasureTheory.norm_integral_le_of_norm_le hmajor hbound
    _ = (1 / 48 : ℝ) * ((N : ℝ) ^ (-(s.re + 2)) *
          (Real.log (N : ℝ) / (s.re + 2) + 1 / (s.re + 2) ^ 2)) := by
      rw [integral_const_mul,
        second_integral_Ioi_log_mul_rpow_neg_sub_one ha hNreal]

/-- The derivative center attached to the second corrected approximation. -/
def eulerMaclaurinTwoZetaDerivApprox (s : ℂ) (N : ℕ) : ℂ :=
  deriv (fun w => eulerMaclaurinTwoZetaApprox w N) s

/-- Explicit derivative of the second Bernoulli correction. -/
def eulerMaclaurinTwoCorrectionDerivFiniteFormula (s : ℂ) (N : ℕ) : ℂ :=
  ((N : ℂ) ^ (-s - 1) -
    s * (N : ℂ) ^ (-s - 1) * ((Real.log (N : ℝ) : ℝ) : ℂ)) / 12

/-- Explicit finite formula for the second corrected derivative center. -/
def eulerMaclaurinTwoZetaDerivFiniteFormula (s : ℂ) (N : ℕ) : ℂ :=
  eulerMaclaurinOneZetaDerivFiniteFormula s N +
    eulerMaclaurinTwoCorrectionDerivFiniteFormula s N

private theorem eulerMaclaurinTwoCorrection_hasDerivAt
    (s : ℂ) {N : ℕ} (hN : 1 ≤ N) :
    HasDerivAt
      (fun w => w * (N : ℂ) ^ (-w - 1) / 12)
      (eulerMaclaurinTwoCorrectionDerivFiniteFormula s N) s := by
  have hNzero : (N : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_zero_of_lt hN)
  have hNreal : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hNlog : Complex.log (N : ℂ) = ((Real.log (N : ℝ) : ℝ) : ℂ) := by
    rw [show (N : ℂ) = ((N : ℝ) : ℂ) by norm_num, ← Complex.ofReal_log hNreal]
  have hexp : HasDerivAt (fun w : ℂ => -w - 1) (-1) s := by
    simpa using (hasDerivAt_id s).neg.sub_const (1 : ℂ)
  have hpow := HasDerivAt.const_cpow (c := (N : ℂ)) hexp (Or.inl hNzero)
  have hraw := ((hasDerivAt_id s).mul hpow).div_const (12 : ℂ)
  refine (hraw.congr_deriv ?_).congr_of_eventuallyEq
    (Eventually.of_forall fun w => ?_)
  · rw [hNlog]
    unfold eulerMaclaurinTwoCorrectionDerivFiniteFormula
    simp only [id_eq]
    ring
  · simp only [Function.id_def, Pi.mul_apply]

/-- Explicit derivative of the cubic-periodic remainder. -/
def eulerMaclaurinTwoZetaRemainderDeriv (s : ℂ) (N : ℕ) : ℂ :=
  -((3 * s ^ 2 + 6 * s + 2) *
      (∫ u in Ioi (N : ℝ), abelCubicTailKernel s u) +
    s * (s + 1) * (s + 2) * abelCubicTailDerivIntegral s N)

private theorem eulerMaclaurinTwoZetaRemainder_hasDerivAt
    {s : ℂ} (hs : 0 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    HasDerivAt
      (fun w => eulerMaclaurinTwoZetaRemainder w N)
      (eulerMaclaurinTwoZetaRemainderDeriv s N) s := by
  have htail := abelCubicTailIntegral_hasDerivAt hs hN
  have hraw :=
    ((((hasDerivAt_id s).neg.mul
      ((hasDerivAt_id s).add_const (1 : ℂ))).mul
      ((hasDerivAt_id s).add_const (2 : ℂ))).mul htail)
  refine (hraw.congr_deriv ?_).congr_of_eventuallyEq
    (Eventually.of_forall fun w => ?_)
  · simp only [Function.id_def, Pi.neg_apply, Pi.mul_apply,
      eulerMaclaurinTwoZetaRemainderDeriv]
    ring
  · simp only [eulerMaclaurinTwoZetaRemainder, Function.id_def,
      Pi.neg_apply, Pi.mul_apply]

private theorem eulerMaclaurinTwoZetaApprox_hasDerivAt_of_re_pos
    {s : ℂ} (hsOne : s ≠ 1) (hsRe : 0 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    HasDerivAt
      (fun w => eulerMaclaurinTwoZetaApprox w N)
      (deriv riemannZeta s - eulerMaclaurinTwoZetaRemainderDeriv s N) s := by
  have hzeta : HasDerivAt riemannZeta (deriv riemannZeta s) s :=
    (differentiableAt_riemannZeta hsOne).hasDerivAt
  have hrem := eulerMaclaurinTwoZetaRemainder_hasDerivAt hsRe hN
  have hdiff := hzeta.sub hrem
  have hmem : s ∈ zetaAbelPositiveDomain := ⟨hsOne, hsRe⟩
  have hdomain : ∀ᶠ w in nhds s, w ∈ zetaAbelPositiveDomain :=
    isOpen_zetaAbelPositiveDomain.mem_nhds hmem
  have heq :
      (fun w => riemannZeta w - eulerMaclaurinTwoZetaRemainder w N) =ᶠ[nhds s]
        fun w => eulerMaclaurinTwoZetaApprox w N := by
    filter_upwards [hdomain] with w hw
    rw [riemannZeta_eq_eulerMaclaurinTwoZetaApprox_add_remainder_of_re_pos
      hw.1 hw.2 hN]
    ring
  exact hdiff.congr_of_eventuallyEq heq.symm

/-- The actual zeta derivative differs from the second corrected derivative center by the
derivative of the cubic-periodic remainder. -/
theorem deriv_riemannZeta_sub_eulerMaclaurinTwoZetaDerivApprox_of_re_pos
    {s : ℂ} (hsOne : s ≠ 1) (hsRe : 0 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    deriv riemannZeta s - eulerMaclaurinTwoZetaDerivApprox s N =
      eulerMaclaurinTwoZetaRemainderDeriv s N := by
  have happ := eulerMaclaurinTwoZetaApprox_hasDerivAt_of_re_pos hsOne hsRe hN
  have hderiv : eulerMaclaurinTwoZetaDerivApprox s N =
      deriv riemannZeta s - eulerMaclaurinTwoZetaRemainderDeriv s N := by
    unfold eulerMaclaurinTwoZetaDerivApprox
    exact happ.deriv
  rw [hderiv]
  ring

/-- The opaque derivative center equals the explicit finite second-correction formula. -/
theorem eulerMaclaurinTwoZetaDerivApprox_eq_finiteFormula
    (s : ℂ) (hsOne : s ≠ 1) (hsRe : 0 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    eulerMaclaurinTwoZetaDerivApprox s N =
      eulerMaclaurinTwoZetaDerivFiniteFormula s N := by
  have htwo := eulerMaclaurinTwoZetaApprox_hasDerivAt_of_re_pos hsOne hsRe hN
  have hcorr := eulerMaclaurinTwoCorrection_hasDerivAt s hN
  have honeRaw := htwo.sub hcorr
  have honeDiff : DifferentiableAt ℂ
      (fun w => eulerMaclaurinOneZetaApprox w N) s := by
    refine (honeRaw.congr_of_eventuallyEq (Eventually.of_forall fun w => ?_)).differentiableAt
    change eulerMaclaurinOneZetaApprox w N =
      eulerMaclaurinTwoZetaApprox w N - w * (N : ℂ) ^ (-w - 1) / 12
    unfold eulerMaclaurinTwoZetaApprox
    ring
  have hone : HasDerivAt (fun w => eulerMaclaurinOneZetaApprox w N)
      (eulerMaclaurinOneZetaDerivApprox s N) s := by
    simpa [eulerMaclaurinOneZetaDerivApprox] using honeDiff.hasDerivAt
  have htotal := hone.add hcorr
  have htotal' : HasDerivAt (fun w => eulerMaclaurinTwoZetaApprox w N)
      (eulerMaclaurinOneZetaDerivApprox s N +
        eulerMaclaurinTwoCorrectionDerivFiniteFormula s N) s := by
    exact htotal.congr_of_eventuallyEq (Eventually.of_forall fun w => by
      unfold eulerMaclaurinTwoZetaApprox
      rfl)
  unfold eulerMaclaurinTwoZetaDerivApprox
  rw [htotal'.deriv,
    eulerMaclaurinOneZetaDerivApprox_eq_finiteFormula s hsOne hN]
  rfl

/-- Explicit first-derivative radius for the second corrected Euler--Maclaurin formula. -/
def eulerMaclaurinTwoZetaDerivError (s : ℂ) (N : ℕ) : ℝ :=
  ‖3 * s ^ 2 + 6 * s + 2‖ *
      ((1 / 48 : ℝ) * ((N : ℝ) ^ (-s.re - 2) / (s.re + 2))) +
    ‖s * (s + 1) * (s + 2)‖ *
      ((1 / 48 : ℝ) * ((N : ℝ) ^ (-(s.re + 2)) *
        (Real.log (N : ℝ) / (s.re + 2) + 1 / (s.re + 2) ^ 2)))

/-- The actual zeta derivative lies in the second corrected error ball on `re(s) > 0`. -/
theorem norm_deriv_riemannZeta_sub_eulerMaclaurinTwoZetaDerivApprox_le_of_re_pos
    {s : ℂ} (hsOne : s ≠ 1) (hsRe : 0 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    ‖deriv riemannZeta s - eulerMaclaurinTwoZetaDerivApprox s N‖ ≤
      eulerMaclaurinTwoZetaDerivError s N := by
  have hvalue := norm_integral_abelCubicTailKernel_le hsRe hN
  have hderiv := norm_abelCubicTailDerivIntegral_le hsRe hN
  rw [deriv_riemannZeta_sub_eulerMaclaurinTwoZetaDerivApprox_of_re_pos
    hsOne hsRe hN]
  unfold eulerMaclaurinTwoZetaRemainderDeriv
    eulerMaclaurinTwoZetaDerivError
  rw [norm_neg]
  calc
    ‖(3 * s ^ 2 + 6 * s + 2) *
          (∫ u in Ioi (N : ℝ), abelCubicTailKernel s u) +
        s * (s + 1) * (s + 2) * abelCubicTailDerivIntegral s N‖ ≤
        ‖(3 * s ^ 2 + 6 * s + 2) *
          (∫ u in Ioi (N : ℝ), abelCubicTailKernel s u)‖ +
        ‖s * (s + 1) * (s + 2) * abelCubicTailDerivIntegral s N‖ :=
      norm_add_le _ _
    _ = ‖3 * s ^ 2 + 6 * s + 2‖ *
          ‖∫ u in Ioi (N : ℝ), abelCubicTailKernel s u‖ +
        ‖s * (s + 1) * (s + 2)‖ *
          ‖abelCubicTailDerivIntegral s N‖ := by
      rw [norm_mul, norm_mul]
    _ ≤ ‖3 * s ^ 2 + 6 * s + 2‖ *
          ((1 / 48 : ℝ) * ((N : ℝ) ^ (-s.re - 2) / (s.re + 2))) +
        ‖s * (s + 1) * (s + 2)‖ *
          ((1 / 48 : ℝ) * ((N : ℝ) ^ (-(s.re + 2)) *
            (Real.log (N : ℝ) / (s.re + 2) + 1 / (s.re + 2) ^ 2))) := by
      gcongr

end

end LeanLab.Riemann
