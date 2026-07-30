import LeanLab.Riemann.MaynardPrattTypeIILocalZeroCount

set_option linter.style.header false

/-!
# Maynard--Pratt Type-II global fourth-moment charging

This file contains only the geometric and measure-theoretic charging layer. It rewrites each
translated local fourth moment as an integral over an absolute ordinate window, proves that
windows around sufficiently separated zero copies are disjoint, and charges their sum to one
global fourth moment. No twisted fourth-moment estimate is assumed or proved here.
-/

namespace LeanLab.Riemann

open Complex Filter MeasureTheory Set
open scoped BigOperators Interval Topology

noncomputable section

/-- The nonnegative fourth-power integrand used in the Type-II rarity argument. -/
def maynardPrattTypeIIFourthIntegrand (M : ℕ) (t : ℝ) : ℝ :=
  ‖maynardPrattTypeIITwistedValue M t‖ ^ (4 : ℝ)

/-- The literal global mollifier--zeta fourth moment on a closed ordinate interval. -/
def maynardPrattTypeIIGlobalFourthMoment
    (M : ℕ) (a b : ℝ) : ℝ :=
  ∫ t : ℝ in Set.Icc a b, maynardPrattTypeIIFourthIntegrand M t

/-- The common coefficient obtained by replacing a Type-II zero's real part by the threshold
`sigma` in the source local-charge inequality. -/
def maynardPrattTypeIISourceChargeScale (T sigma : ℝ) : ℝ :=
  ‖(((1 / (2 * Real.pi) : ℝ) : ℂ))‖ *
    classicalDetectorSourceY T ^ (1 / 2 - sigma) *
    (2 * Real.log T) *
    (2 * Real.log T ^ (2 : ℕ)) ^ (3 / 4 : ℝ)

/-- The half-open absolute ordinate window used to make separated windows disjoint. -/
def maynardPrattTypeIIOrdinateWindow
    (T sigma R : ℝ) (i : MaynardPrattTypeIIZeroIndex T sigma) : Set ℝ :=
  Set.Ioc
    ((maynardPrattTypeIIZeroValue T sigma i).im - R)
    ((maynardPrattTypeIIZeroValue T sigma i).im + R)

theorem continuous_maynardPrattTypeIIFourthIntegrand (M : ℕ) :
    Continuous (maynardPrattTypeIIFourthIntegrand M) := by
  unfold maynardPrattTypeIIFourthIntegrand
  exact (continuous_maynardPrattTypeIITwistedValue M).norm.rpow_const
    (fun _ => Or.inr (by norm_num))

theorem maynardPrattTypeIIFourthIntegrand_nonneg
    (M : ℕ) (t : ℝ) :
    0 ≤ maynardPrattTypeIIFourthIntegrand M t :=
  Real.rpow_nonneg (norm_nonneg _) _

theorem maynardPrattTypeIILocalFourthMoment_nonneg
    (M : ℕ) (rho : ℂ) (R : ℝ) :
    0 ≤ maynardPrattTypeIILocalFourthMoment M rho R := by
  rw [maynardPrattTypeIILocalFourthMoment]
  apply MeasureTheory.integral_nonneg
  exact fun _u : ℝ =>
    Real.rpow_nonneg
      (norm_nonneg
        (maynardPrattTypeIITwistedValue M (rho.im + _u))) (4 : ℝ)

theorem integrableOn_maynardPrattTypeIIFourthIntegrand_Icc
    (M : ℕ) (a b : ℝ) :
    IntegrableOn (maynardPrattTypeIIFourthIntegrand M) (Set.Icc a b) :=
  (continuous_maynardPrattTypeIIFourthIntegrand M).continuousOn.integrableOn_compact
    isCompact_Icc

/-- Translation from the source's centered local coordinate to an absolute ordinate window. -/
theorem maynardPrattTypeIILocalFourthMoment_eq_integral_ordinateWindow
    (M : ℕ) (rho : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    maynardPrattTypeIILocalFourthMoment M rho R =
      ∫ t : ℝ in Set.Ioc (rho.im - R) (rho.im + R),
        maynardPrattTypeIIFourthIntegrand M t := by
  rw [maynardPrattTypeIILocalFourthMoment, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -R ≤ R)]
  have hfun :
      (fun x : ℝ =>
        ‖maynardPrattTypeIITwistedValue M (rho.im + x)‖ ^ (4 : ℝ)) =
        (fun x : ℝ => maynardPrattTypeIIFourthIntegrand M (x + rho.im)) := by
    funext x
    simp only [maynardPrattTypeIIFourthIntegrand, add_comm]
  rw [hfun]
  rw [intervalIntegral.integral_comp_add_right]
  rw [intervalIntegral.integral_of_le (by linarith : -R + rho.im ≤ R + rho.im)]
  simp only [sub_eq_add_neg, add_comm]

/-- Separation by at least `H` makes radius-`R` half-open windows disjoint whenever
`2 * R ≤ H`. -/
theorem pairwise_disjoint_maynardPrattTypeIIOrdinateWindow
    {T sigma H R : ℝ}
    {S : Finset (MaynardPrattTypeIIZeroIndex T sigma)}
    (hsep :
      IsOrdinateSeparated S
        (fun i => (maynardPrattTypeIIZeroValue T sigma i).im) H)
    (hRH : 2 * R ≤ H) :
    Set.Pairwise (S : Set (MaynardPrattTypeIIZeroIndex T sigma))
      (fun i j =>
        Disjoint
          (maynardPrattTypeIIOrdinateWindow T sigma R i)
          (maynardPrattTypeIIOrdinateWindow T sigma R j)) := by
  intro i hi j hj hij
  have hfar :
      H ≤
        |(maynardPrattTypeIIZeroValue T sigma i).im -
          (maynardPrattTypeIIZeroValue T sigma j).im| := by
    simpa only using hsep hi hj hij
  by_cases hijOrder :
      (maynardPrattTypeIIZeroValue T sigma i).im ≤
        (maynardPrattTypeIIZeroValue T sigma j).im
  · apply Set.Ioc_disjoint_Ioc_of_le
    rw [abs_of_nonpos (sub_nonpos.mpr hijOrder)] at hfar
    linarith
  · have hjiOrder :
        (maynardPrattTypeIIZeroValue T sigma j).im ≤
          (maynardPrattTypeIIZeroValue T sigma i).im :=
      le_of_not_ge hijOrder
    apply Disjoint.symm
    apply Set.Ioc_disjoint_Ioc_of_le
    rw [abs_of_nonneg (sub_nonneg.mpr hjiOrder)] at hfar
    linarith

/-- Disjoint local fourth moments charge to one enclosing global fourth moment. This is the
precise structural interface consumed by a future analytic twisted-moment estimate. -/
theorem sum_maynardPrattTypeIILocalFourthMoment_le_global
    {T sigma H R A B : ℝ}
    {S : Finset (MaynardPrattTypeIIZeroIndex T sigma)}
    (hR : 0 ≤ R)
    (hsep :
      IsOrdinateSeparated S
        (fun i => (maynardPrattTypeIIZeroValue T sigma i).im) H)
    (hRH : 2 * R ≤ H)
    (hwindow :
      ∀ i ∈ S,
        maynardPrattTypeIIOrdinateWindow T sigma R i ⊆ Set.Icc A B) :
    (∑ i ∈ S,
        maynardPrattTypeIILocalFourthMoment
          (classicalDetectorSourceM T)
          (maynardPrattTypeIIZeroValue T sigma i) R) ≤
      maynardPrattTypeIIGlobalFourthMoment
        (classicalDetectorSourceM T) A B := by
  let f : ℝ → ℝ :=
    maynardPrattTypeIIFourthIntegrand (classicalDetectorSourceM T)
  have hpair :
      Set.Pairwise (S : Set (MaynardPrattTypeIIZeroIndex T sigma))
        (fun i j =>
          Disjoint
            (maynardPrattTypeIIOrdinateWindow T sigma R i)
            (maynardPrattTypeIIOrdinateWindow T sigma R j)) :=
    pairwise_disjoint_maynardPrattTypeIIOrdinateWindow hsep hRH
  have hlocalIntegrable :
      ∀ i ∈ S,
        IntegrableOn f (maynardPrattTypeIIOrdinateWindow T sigma R i) := by
    intro i _hi
    exact
      (integrableOn_maynardPrattTypeIIFourthIntegrand_Icc
        (classicalDetectorSourceM T)
        ((maynardPrattTypeIIZeroValue T sigma i).im - R)
        ((maynardPrattTypeIIZeroValue T sigma i).im + R)).mono_set
        Set.Ioc_subset_Icc_self
  have hsubset :
      (⋃ i ∈ S, maynardPrattTypeIIOrdinateWindow T sigma R i) ⊆
        Set.Icc A B := by
    refine Set.iUnion_subset fun i => ?_
    refine Set.iUnion_subset fun hi => ?_
    exact hwindow i hi
  calc
    (∑ i ∈ S,
        maynardPrattTypeIILocalFourthMoment
          (classicalDetectorSourceM T)
          (maynardPrattTypeIIZeroValue T sigma i) R) =
        ∑ i ∈ S,
          ∫ t : ℝ in maynardPrattTypeIIOrdinateWindow T sigma R i,
            f t := by
      apply Finset.sum_congr rfl
      intro i hi
      simpa only [f, maynardPrattTypeIIOrdinateWindow] using
        maynardPrattTypeIILocalFourthMoment_eq_integral_ordinateWindow
          (classicalDetectorSourceM T)
          (maynardPrattTypeIIZeroValue T sigma i) hR
    _ =
        ∫ t : ℝ in
          ⋃ i ∈ S, maynardPrattTypeIIOrdinateWindow T sigma R i,
          f t := by
      symm
      exact MeasureTheory.integral_biUnion_finset S
        (fun _ _ => measurableSet_Ioc) hpair hlocalIntegrable
    _ ≤ ∫ t : ℝ in Set.Icc A B, f t := by
      apply MeasureTheory.setIntegral_mono_set
        (integrableOn_maynardPrattTypeIIFourthIntegrand_Icc
          (classicalDetectorSourceM T) A B)
      · exact Filter.Eventually.of_forall fun t =>
          maynardPrattTypeIIFourthIntegrand_nonneg
            (classicalDetectorSourceM T) t
      · exact Filter.Eventually.of_forall hsubset
    _ =
        maynardPrattTypeIIGlobalFourthMoment
          (classicalDetectorSourceM T) A B := rfl

/-- Every radius-`R` window around a source-range Type-II ordinate lies in `[T / 2, 3T]`
once `R ≤ T / 2`. -/
theorem maynardPrattTypeIIOrdinateWindow_subset_sourceGlobal
    {T sigma R : ℝ} (_hT : 0 ≤ T) (hRT : R ≤ T / 2)
    (i : MaynardPrattTypeIIZeroIndex T sigma) :
    maynardPrattTypeIIOrdinateWindow T sigma R i ⊆
      Set.Icc (T / 2) (3 * T) := by
  have hmem := mem_maynardPrattTypeIIZeroFinset.mp i.1.2
  have himLower :
      T ≤ (maynardPrattTypeIIZeroValue T sigma i).im := by
    simpa only [maynardPrattTypeIIZeroValue] using hmem.2.2.1
  have himUpper :
      (maynardPrattTypeIIZeroValue T sigma i).im ≤ 2 * T := by
    simpa only [maynardPrattTypeIIZeroValue] using hmem.2.2.2.1
  intro t ht
  change
    (maynardPrattTypeIIZeroValue T sigma i).im - R < t ∧
      t ≤ (maynardPrattTypeIIZeroValue T sigma i).im + R at ht
  constructor <;> linarith

/-- At the literal source scales, every separated Type-II family charges to the single
global mollifier--zeta fourth moment on `[T / 2, 3T]`. -/
theorem eventually_sum_maynardPrattTypeIILocalFourthMoment_source_le_global :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ (sigma : ℝ)
        (S : Finset (MaynardPrattTypeIIZeroIndex T sigma)),
        IsOrdinateSeparated S
            (fun i => (maynardPrattTypeIIZeroValue T sigma i).im)
            (Real.log T ^ (3 : ℕ)) →
        (∑ i ∈ S,
            maynardPrattTypeIILocalFourthMoment
              (classicalDetectorSourceM T)
              (maynardPrattTypeIIZeroValue T sigma i)
              (Real.log T ^ (2 : ℕ))) ≤
          maynardPrattTypeIIGlobalFourthMoment
            (classicalDetectorSourceM T) (T / 2) (3 * T) := by
  have hratio :
      Tendsto
        (fun T : ℝ => Real.log T ^ (2 : ℕ) / T)
        Filter.atTop (𝓝 0) := by
    simpa only [Real.rpow_two, Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
        (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
  have hratioSmall :
      ∀ᶠ T : ℝ in Filter.atTop,
        Real.log T ^ (2 : ℕ) / T < 1 / 2 :=
    (tendsto_order.1 hratio).2 (1 / 2) (by norm_num)
  filter_upwards
    [hratioSmall, eventually_ge_atTop (Real.exp 2)] with
      T hratioT hTexp
  intro sigma S hsep
  have hTpos : 0 < T := (Real.exp_pos 2).trans_le hTexp
  have hlogTwo : 2 ≤ Real.log T := by
    calc
      (2 : ℝ) = Real.log (Real.exp 2) := by rw [Real.log_exp]
      _ ≤ Real.log T := Real.log_le_log (Real.exp_pos 2) hTexp
  have hRT : Real.log T ^ (2 : ℕ) ≤ T / 2 := by
    have hmul :=
      (div_lt_iff₀ hTpos).mp hratioT
    linarith
  have hRH :
      2 * Real.log T ^ (2 : ℕ) ≤ Real.log T ^ (3 : ℕ) := by
    calc
      2 * Real.log T ^ (2 : ℕ) ≤
          Real.log T * Real.log T ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_right hlogTwo
          (sq_nonneg (Real.log T))
      _ = Real.log T ^ (3 : ℕ) := by ring
  exact
    sum_maynardPrattTypeIILocalFourthMoment_le_global
      (sq_nonneg (Real.log T)) hsep hRH
      (fun i _ =>
        maynardPrattTypeIIOrdinateWindow_subset_sourceGlobal
          hTpos.le hRT i)

/-- The local source charge with a coefficient uniform over all Type-II zeros to the right of
`sigma`. -/
theorem eventually_one_sixth_le_sourceChargeScale_mul_localFourthRoot :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ (sigma : ℝ) (i : MaynardPrattTypeIIZeroIndex T sigma),
        1 / 2 + 1 / Real.log T ≤ sigma →
        (1 / 6 : ℝ) ≤
          maynardPrattTypeIISourceChargeScale T sigma *
            (maynardPrattTypeIILocalFourthMoment
              (classicalDetectorSourceM T)
              (maynardPrattTypeIIZeroValue T sigma i)
              (Real.log T ^ (2 : ℕ))) ^ (1 / 4 : ℝ) := by
  filter_upwards
    [eventually_one_sixth_le_source_typeIILocalFourthMoment,
      eventually_ge_atTop (1 : ℝ)] with T hsource hT
  intro sigma i hsigma
  have hmem := mem_maynardPrattTypeIIZeroFinset.mp i.1.2
  have hraw :=
    hsource sigma hsigma hmem.1 hmem.2.2.1 hmem.2.2.2.1
      hmem.2.2.2.2.1 hmem.2.2.2.2.2
  have hYone :
      1 ≤ classicalDetectorSourceY T := by
    rw [classicalDetectorSourceY]
    simpa only [Real.one_le_sqrt] using hT
  have hYpow :
      classicalDetectorSourceY T ^
          (1 / 2 - (maynardPrattTypeIIZeroValue T sigma i).re) ≤
        classicalDetectorSourceY T ^ (1 / 2 - sigma) := by
    apply Real.rpow_le_rpow_of_exponent_le hYone
    have hre :
        sigma ≤ (maynardPrattTypeIIZeroValue T sigma i).re := by
      simpa only [maynardPrattTypeIIZeroValue] using hmem.2.2.2.2.1
    linarith
  have hlogNonneg : 0 ≤ 2 * Real.log T := by
    have hTpos : 0 < T := zero_lt_one.trans_le hT
    exact mul_nonneg (by norm_num) (Real.log_nonneg hT)
  have hwindowNonneg :
      0 ≤ (2 * Real.log T ^ (2 : ℕ)) ^ (3 / 4 : ℝ) :=
    Real.rpow_nonneg (by positivity) _
  have hmomentRootNonneg :
      0 ≤
        (maynardPrattTypeIILocalFourthMoment
          (classicalDetectorSourceM T)
          (maynardPrattTypeIIZeroValue T sigma i)
          (Real.log T ^ (2 : ℕ))) ^ (1 / 4 : ℝ) :=
    Real.rpow_nonneg
      (maynardPrattTypeIILocalFourthMoment_nonneg _ _ _) _
  calc
    (1 / 6 : ℝ) ≤
        ‖(((1 / (2 * Real.pi) : ℝ) : ℂ))‖ *
          (classicalDetectorSourceY T ^
              (1 / 2 - (maynardPrattTypeIIZeroValue T sigma i).re) *
            (2 * Real.log T) *
            ((2 * Real.log T ^ (2 : ℕ)) ^ (3 / 4 : ℝ) *
              (maynardPrattTypeIILocalFourthMoment
                (classicalDetectorSourceM T)
                (maynardPrattTypeIIZeroValue T sigma i)
                (Real.log T ^ (2 : ℕ))) ^ (1 / 4 : ℝ))) := hraw
    _ ≤
        ‖(((1 / (2 * Real.pi) : ℝ) : ℂ))‖ *
          (classicalDetectorSourceY T ^ (1 / 2 - sigma) *
            (2 * Real.log T) *
            ((2 * Real.log T ^ (2 : ℕ)) ^ (3 / 4 : ℝ) *
              (maynardPrattTypeIILocalFourthMoment
                (classicalDetectorSourceM T)
                (maynardPrattTypeIIZeroValue T sigma i)
                (Real.log T ^ (2 : ℕ))) ^ (1 / 4 : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      calc
        classicalDetectorSourceY T ^
              (1 / 2 - (maynardPrattTypeIIZeroValue T sigma i).re) *
              (2 * Real.log T) *
              ((2 * Real.log T ^ (2 : ℕ)) ^ (3 / 4 : ℝ) *
                (maynardPrattTypeIILocalFourthMoment
                  (classicalDetectorSourceM T)
                  (maynardPrattTypeIIZeroValue T sigma i)
                  (Real.log T ^ (2 : ℕ))) ^ (1 / 4 : ℝ)) =
            classicalDetectorSourceY T ^
              (1 / 2 - (maynardPrattTypeIIZeroValue T sigma i).re) *
              ((2 * Real.log T) *
                ((2 * Real.log T ^ (2 : ℕ)) ^ (3 / 4 : ℝ) *
                  (maynardPrattTypeIILocalFourthMoment
                    (classicalDetectorSourceM T)
                    (maynardPrattTypeIIZeroValue T sigma i)
                    (Real.log T ^ (2 : ℕ))) ^ (1 / 4 : ℝ))) := by ring
        _ ≤ classicalDetectorSourceY T ^ (1 / 2 - sigma) *
              ((2 * Real.log T) *
                ((2 * Real.log T ^ (2 : ℕ)) ^ (3 / 4 : ℝ) *
                  (maynardPrattTypeIILocalFourthMoment
                    (classicalDetectorSourceM T)
                    (maynardPrattTypeIIZeroValue T sigma i)
                    (Real.log T ^ (2 : ℕ))) ^ (1 / 4 : ℝ))) := by
          apply mul_le_mul_of_nonneg_right hYpow
          exact mul_nonneg hlogNonneg
            (mul_nonneg hwindowNonneg hmomentRootNonneg)
        _ = classicalDetectorSourceY T ^ (1 / 2 - sigma) *
              (2 * Real.log T) *
              ((2 * Real.log T ^ (2 : ℕ)) ^ (3 / 4 : ℝ) *
                (maynardPrattTypeIILocalFourthMoment
                  (classicalDetectorSourceM T)
                  (maynardPrattTypeIIZeroValue T sigma i)
                  (Real.log T ^ (2 : ℕ))) ^ (1 / 4 : ℝ)) := by ring
    _ =
        maynardPrattTypeIISourceChargeScale T sigma *
          (maynardPrattTypeIILocalFourthMoment
            (classicalDetectorSourceM T)
            (maynardPrattTypeIIZeroValue T sigma i)
            (Real.log T ^ (2 : ℕ))) ^ (1 / 4 : ℝ) := by
      rw [maynardPrattTypeIISourceChargeScale]
      ring

/-- Raising a nonnegative local fourth-root charge to the fourth power removes the root
without any hidden positivity assumption. -/
theorem fourthMoment_lower_bound_of_charge
    {C m : ℝ} (hm : 0 ≤ m)
    (hcharge : (1 / 6 : ℝ) ≤ C * m ^ (1 / 4 : ℝ)) :
    (1 / 6 : ℝ) ^ (4 : ℕ) ≤ C ^ (4 : ℕ) * m := by
  have hpow :=
    pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 6) hcharge 4
  calc
    (1 / 6 : ℝ) ^ (4 : ℕ) ≤
        (C * m ^ (1 / 4 : ℝ)) ^ (4 : ℕ) := hpow
    _ = C ^ (4 : ℕ) * (m ^ (1 / 4 : ℝ)) ^ (4 : ℕ) := by
      rw [mul_pow]
    _ = C ^ (4 : ℕ) * m := by
      congr 1
      convert
        Real.rpow_inv_natCast_pow hm (by norm_num : (4 : ℕ) ≠ 0)
          using 1
      norm_num

/-- Summing the uniform local charges over a separated source family and then applying the
global charging theorem. -/
theorem eventually_card_mul_charge_le_sourceChargeScale_pow_mul_globalFourthMoment :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ (sigma : ℝ)
        (S : Finset (MaynardPrattTypeIIZeroIndex T sigma)),
        1 / 2 + 1 / Real.log T ≤ sigma →
        IsOrdinateSeparated S
            (fun i => (maynardPrattTypeIIZeroValue T sigma i).im)
            (Real.log T ^ (3 : ℕ)) →
        (S.card : ℝ) * (1 / 6 : ℝ) ^ (4 : ℕ) ≤
          maynardPrattTypeIISourceChargeScale T sigma ^ (4 : ℕ) *
            maynardPrattTypeIIGlobalFourthMoment
              (classicalDetectorSourceM T) (T / 2) (3 * T) := by
  filter_upwards
    [eventually_one_sixth_le_sourceChargeScale_mul_localFourthRoot,
      eventually_sum_maynardPrattTypeIILocalFourthMoment_source_le_global]
      with T hlocalCharge hglobalCharge
  intro sigma S hsigma hsep
  have hpoint :
      ∀ i ∈ S,
        (1 / 6 : ℝ) ^ (4 : ℕ) ≤
          maynardPrattTypeIISourceChargeScale T sigma ^ (4 : ℕ) *
            maynardPrattTypeIILocalFourthMoment
              (classicalDetectorSourceM T)
              (maynardPrattTypeIIZeroValue T sigma i)
              (Real.log T ^ (2 : ℕ)) := by
    intro i _hi
    exact fourthMoment_lower_bound_of_charge
      (maynardPrattTypeIILocalFourthMoment_nonneg _ _ _)
      (hlocalCharge sigma i hsigma)
  calc
    (S.card : ℝ) * (1 / 6 : ℝ) ^ (4 : ℕ) =
        ∑ i ∈ S, (1 / 6 : ℝ) ^ (4 : ℕ) := by simp
    _ ≤ ∑ i ∈ S,
          maynardPrattTypeIISourceChargeScale T sigma ^ (4 : ℕ) *
            maynardPrattTypeIILocalFourthMoment
              (classicalDetectorSourceM T)
              (maynardPrattTypeIIZeroValue T sigma i)
              (Real.log T ^ (2 : ℕ)) :=
      Finset.sum_le_sum hpoint
    _ =
        maynardPrattTypeIISourceChargeScale T sigma ^ (4 : ℕ) *
          (∑ i ∈ S,
            maynardPrattTypeIILocalFourthMoment
              (classicalDetectorSourceM T)
              (maynardPrattTypeIIZeroValue T sigma i)
              (Real.log T ^ (2 : ℕ))) := by
      rw [Finset.mul_sum]
    _ ≤
        maynardPrattTypeIISourceChargeScale T sigma ^ (4 : ℕ) *
          maynardPrattTypeIIGlobalFourthMoment
            (classicalDetectorSourceM T) (T / 2) (3 * T) := by
      apply mul_le_mul_of_nonneg_left (hglobalCharge sigma S hsep)
      positivity

/-- The exact remaining analytic producer: a polylogarithmic global fourth moment for the
literal source mollifier length `floor (2 * T^(1/100))`. -/
def MaynardPrattTypeIISourceTwistedFourthMomentEstimate (A : ℕ) : Prop :=
  ∀ᶠ T : ℝ in Filter.atTop,
    maynardPrattTypeIIGlobalFourthMoment
        (classicalDetectorSourceM T) (T / 2) (3 * T) ≤
      T * Real.log T ^ A

/-- Conditional separated-family rarity with no premise beyond the named global twisted
fourth-moment estimate. -/
theorem eventually_card_mul_charge_le_of_sourceTwistedFourthMomentEstimate
    {A : ℕ}
    (hmoment : MaynardPrattTypeIISourceTwistedFourthMomentEstimate A) :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ (sigma : ℝ)
        (S : Finset (MaynardPrattTypeIIZeroIndex T sigma)),
        1 / 2 + 1 / Real.log T ≤ sigma →
        IsOrdinateSeparated S
            (fun i => (maynardPrattTypeIIZeroValue T sigma i).im)
            (Real.log T ^ (3 : ℕ)) →
        (S.card : ℝ) * (1 / 6 : ℝ) ^ (4 : ℕ) ≤
          maynardPrattTypeIISourceChargeScale T sigma ^ (4 : ℕ) *
            (T * Real.log T ^ A) := by
  filter_upwards
    [eventually_card_mul_charge_le_sourceChargeScale_pow_mul_globalFourthMoment,
      hmoment] with T hcharge hmomentT
  intro sigma S hsigma hsep
  exact (hcharge sigma S hsigma hsep).trans
    (mul_le_mul_of_nonneg_left hmomentT (by positivity))

/-- The local zero-count packing producer composed with the conditional fourth-moment
estimate. This is the complete structural Type-II reduction before simplifying exponents. -/
theorem eventually_exists_typeIISeparated_fullCount_charge_le_of_sourceMomentEstimate
    {A : ℕ}
    (hmoment : MaynardPrattTypeIISourceTwistedFourthMomentEstimate A) :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ sigma : ℝ,
        1 / 2 + 1 / Real.log T ≤ sigma →
        ∃ S : Finset (MaynardPrattTypeIIZeroIndex T sigma),
          IsOrdinateSeparated S
              (fun i => (maynardPrattTypeIIZeroValue T sigma i).im)
              (Real.log T ^ (3 : ℕ)) ∧
          IsOrdinateCover S Finset.univ
              (fun i => (maynardPrattTypeIIZeroValue T sigma i).im)
              (Real.log T ^ (3 : ℕ)) ∧
          maynardPrattTypeIIZeroCount T sigma ≤
            Nat.ceil (30 * Real.log T ^ (7 : ℕ)) * S.card ∧
          (maynardPrattTypeIIZeroCount T sigma : ℝ) *
              (1 / 6 : ℝ) ^ (4 : ℕ) ≤
            (Nat.ceil (30 * Real.log T ^ (7 : ℕ)) : ℝ) *
              (maynardPrattTypeIISourceChargeScale T sigma ^ (4 : ℕ) *
                (T * Real.log T ^ A)) := by
  filter_upwards
    [eventually_exists_maynardPrattTypeIISeparated_source_card_control,
      eventually_card_mul_charge_le_of_sourceTwistedFourthMomentEstimate hmoment]
      with T hpacking hcharge
  intro sigma hsigma
  obtain ⟨S, hsep, hcover, hcount⟩ := hpacking sigma
  refine ⟨S, hsep, hcover, hcount, ?_⟩
  have hcountReal :
      (maynardPrattTypeIIZeroCount T sigma : ℝ) ≤
        (Nat.ceil (30 * Real.log T ^ (7 : ℕ)) : ℝ) *
          (S.card : ℝ) := by
    exact_mod_cast hcount
  have hselected := hcharge sigma S hsigma hsep
  calc
    (maynardPrattTypeIIZeroCount T sigma : ℝ) *
          (1 / 6 : ℝ) ^ (4 : ℕ) ≤
        ((Nat.ceil (30 * Real.log T ^ (7 : ℕ)) : ℝ) *
          (S.card : ℝ)) * (1 / 6 : ℝ) ^ (4 : ℕ) :=
      mul_le_mul_of_nonneg_right hcountReal (by positivity)
    _ =
        (Nat.ceil (30 * Real.log T ^ (7 : ℕ)) : ℝ) *
          ((S.card : ℝ) * (1 / 6 : ℝ) ^ (4 : ℕ)) := by ring
    _ ≤
        (Nat.ceil (30 * Real.log T ^ (7 : ℕ)) : ℝ) *
          (maynardPrattTypeIISourceChargeScale T sigma ^ (4 : ℕ) *
            (T * Real.log T ^ A)) := by
      exact mul_le_mul_of_nonneg_left hselected (Nat.cast_nonneg _)

end

end LeanLab.Riemann
