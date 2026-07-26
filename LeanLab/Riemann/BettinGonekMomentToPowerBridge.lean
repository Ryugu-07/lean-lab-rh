import LeanLab.Riemann.BettinGonekInverseMellinConvolution
import LeanLab.Riemann.SpeiserCountingEquivalence
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.MeasureTheory.Integral.Prod

set_option linter.style.header false

/-!
# Bettin--Gonek moment-to-power bridge

This module completes the analytic implication from Farmer's long-mollifier moment bound to the
power obstruction used in Bettin and Gonek's Theorem 1.
-/

namespace LeanLab.Riemann

open Complex Filter MeasureTheory Set Topology
open scoped Interval Topology

noncomputable section

/-- Zeta does not vanish at the real point `1/2`. -/
theorem riemannZeta_half_ne_zero :
    riemannZeta (1 / 2 : ℂ) ≠ 0 := by
  intro hzero
  have hnontrivial : IsNontrivialZero (1 / 2 : ℂ) := by
    refine ⟨hzero, ?_, by norm_num⟩
    rintro ⟨n, hn⟩
    have hre := congrArg Complex.re hn
    norm_num at hre
    have hn0 : (0 : ℝ) ≤ n := by positivity
    linarith
  exact criticalStripRealAxisZeroFree (1 / 2 : ℂ) hnontrivial (by norm_num)

/-- The fixed low-height zeta mass used in the source argument. -/
def bettinGonekFixedZetaMass : ℝ :=
  ∫ t : ℝ in 0..1,
    Complex.normSq (riemannZeta (farmerCriticalLinePoint t))

theorem bettinGonekFixedZetaMass_pos :
    0 < bettinGonekFixedZetaMass := by
  unfold bettinGonekFixedZetaMass
  apply intervalIntegral.integral_pos (by norm_num)
    (Complex.continuous_normSq.comp continuous_riemannZeta_criticalLine).continuousOn
  · intro t _
    exact Complex.normSq_nonneg _
  · refine ⟨0, by norm_num, ?_⟩
    change 0 <
      Complex.normSq (riemannZeta (farmerCriticalLinePoint 0))
    rw [Complex.normSq_pos]
    simpa [farmerCriticalLinePoint] using riemannZeta_half_ne_zero

/-- A positive lower bound for the residue scale, uniform on the fixed interval `[0,1]`. -/
def bettinGonekResidueScaleLower (rho : ℂ) : ℝ :=
  ‖rho - 1‖ /
    ((‖rho + 3 / 2‖ + 1) ^ 2 * ‖rho + 3 / 2‖ ^ 4)

theorem bettinGonekResidueScaleLower_pos
    {rho : ℂ} (hrho : IsNontrivialZero rho) :
    0 < bettinGonekResidueScaleLower rho := by
  rw [bettinGonekResidueScaleLower]
  apply div_pos
  · exact norm_pos_iff.mpr (sub_ne_zero.mpr hrho.2.2)
  · have hrhoAdd : rho + 3 / 2 ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      norm_num at hre
      linarith [nontrivial_zero_re_pos hrho]
    exact mul_pos (pow_pos (by positivity) 2)
      (pow_pos (norm_pos_iff.mpr hrhoAdd) 4)

theorem bettinGonekResidueScaleLower_le
    {rho : ℂ} (hrho : IsNontrivialZero rho) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    bettinGonekResidueScaleLower rho ≤
      bettinGonekResidueScale rho t := by
  have hrhoAdd : rho + 3 / 2 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith [nontrivial_zero_re_pos hrho]
  have hrhoAddSub : rho + 3 / 2 - t * Complex.I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [Complex.sub_re, Complex.mul_re] at hre
    linarith [nontrivial_zero_re_pos hrho]
  have hnorm :
      ‖rho + 3 / 2 - t * Complex.I‖ ≤ ‖rho + 3 / 2‖ + 1 := by
    calc
      ‖rho + 3 / 2 - t * Complex.I‖
          ≤ ‖rho + 3 / 2‖ + ‖(t : ℂ) * Complex.I‖ := norm_sub_le _ _
      _ = ‖rho + 3 / 2‖ + |t| := by simp
      _ ≤ ‖rho + 3 / 2‖ + 1 := by
        rw [abs_of_nonneg ht.1]
        have ht1 : t ≤ 1 := ht.2
        linarith
  have hden :
      ‖rho + 3 / 2 - t * Complex.I‖ ^ 2 * ‖rho + 3 / 2‖ ^ 4 ≤
        (‖rho + 3 / 2‖ + 1) ^ 2 * ‖rho + 3 / 2‖ ^ 4 := by
    gcongr
  rw [bettinGonekResidueScaleLower, bettinGonekResidueScale]
  exact div_le_div_of_nonneg_left (norm_nonneg _)
    (mul_pos (pow_pos (norm_pos_iff.mpr hrhoAddSub) 2)
      (pow_pos (norm_pos_iff.mpr hrhoAdd) 4)) hden

/-- The inverse-Mellin majorant is independent of the height translation. -/
theorem bettinGonekInverseMellinBound_eq_zero
    (rho : ℂ) (t : ℝ) :
    bettinGonekInverseMellinBound rho t =
      bettinGonekInverseMellinBound rho 0 := by
  unfold bettinGonekInverseMellinBound
  congr 1
  simpa only [add_zero] using
    (MeasureTheory.integral_add_right_eq_self
      (fun y : ℝ => bettinGonekAuxiliaryDecayConstant rho *
        ((1 + |y|)⁻¹ ^ (3 : ℕ))) t)

theorem farmerMollifier_eq_one_of_one_lt_le_two
    {x : ℝ} (hx : 1 < x) (hxTwo : x ≤ 2) (s : ℂ) :
    farmerMollifier x s = 1 := by
  by_cases htop : x = 2
  · subst x
    rw [farmerMollifier, if_pos (by norm_num),
      show ⌊(2 : ℝ)⌋₊ = 2 by norm_num, farmerMollifierCore,
      show Finset.Icc 1 2 = {1, 2} by decide]
    norm_num [farmerMobiusCoefficient, farmerLogTaper]
    exact_mod_cast (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  · have hxlt : x < 2 := lt_of_le_of_ne hxTwo htop
    have hfloor : ⌊x⌋₊ = 1 := by
      apply (Nat.floor_eq_iff (by positivity : (0 : ℝ) ≤ x)).2
      constructor
      · norm_num
        exact hx.le
      · norm_num
        exact hxlt
    rw [farmerMollifier, if_pos hx, hfloor]
    rw [farmerMollifierCore, show Finset.Icc 1 1 = {1} by decide]
    norm_num [farmerMobiusCoefficient, farmerLogTaper,
      (Real.log_pos hx).ne']

theorem norm_farmerMollifier_le_sum_endpoints
    {N : ℕ} (hN : 2 ≤ N) {x : ℝ}
    (hNx : (N : ℝ) ≤ x) (hxN : x ≤ N + 1) (s : ℂ) :
    ‖farmerMollifier x s‖ ≤
      ‖farmerMollifier N s‖ + ‖farmerMollifier (N + 1) s‖ := by
  rw [farmerMollifier_interpolate hN hNx hxN]
  let u := farmerCutoffBlend N x
  have hu : u ∈ Set.Icc (0 : ℝ) 1 :=
    farmerCutoffBlend_mem_Icc hN hNx hxN
  change
    ‖(u : ℂ) * farmerMollifier N s +
        (1 - (u : ℂ)) * farmerMollifier (N + 1) s‖ ≤ _
  calc
    ‖(u : ℂ) * farmerMollifier N s +
        (1 - (u : ℂ)) * farmerMollifier (N + 1) s‖
        ≤ ‖(u : ℂ) * farmerMollifier N s‖ +
          ‖(1 - (u : ℂ)) * farmerMollifier (N + 1) s‖ :=
      norm_add_le _ _
    _ = u * ‖farmerMollifier N s‖ +
        (1 - u) * ‖farmerMollifier (N + 1) s‖ := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hu.1]
      have hsub :
          (1 : ℂ) - (u : ℂ) = ((1 - u : ℝ) : ℂ) := by push_cast; rfl
      rw [hsub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hu.2)]
    _ ≤ ‖farmerMollifier N s‖ + ‖farmerMollifier (N + 1) s‖ := by
      exact add_le_add
        (mul_le_of_le_one_left (norm_nonneg _) hu.2)
        (mul_le_of_le_one_left (norm_nonneg _) (by linarith [hu.1]))

theorem norm_bettinGonekLogMollifier_le_endpoints_mul_log
    {N : ℕ} (hN : 2 ≤ N) {x X : ℝ}
    (hNx : (N : ℝ) ≤ x) (hxN : x ≤ N + 1)
    (hNX : (N : ℝ) + 1 ≤ X) (s : ℂ) :
    ‖bettinGonekLogMollifier x s‖ ≤
      Real.log X *
        (‖farmerMollifier N s‖ + ‖farmerMollifier (N + 1) s‖) := by
  have hxOne : 1 ≤ x := by
    have hNreal : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hXpos : 0 < X := by
    have hNreal : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hxOne
  have hxX : x ≤ X := hxN.trans hNX
  have hlog :
      Real.log x ≤ Real.log X :=
    Real.strictMonoOn_log.monotoneOn (lt_of_lt_of_le zero_lt_one hxOne)
      hXpos hxX
  have hM := norm_farmerMollifier_le_sum_endpoints hN hNx hxN s
  rw [bettinGonekLogMollifier, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hlogx]
  calc
    ‖farmerMollifier x s‖ * Real.log x ≤
        (‖farmerMollifier N s‖ + ‖farmerMollifier (N + 1) s‖) *
          Real.log X := by
      exact mul_le_mul hM hlog hlogx
        (add_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = Real.log X *
        (‖farmerMollifier N s‖ + ‖farmerMollifier (N + 1) s‖) := by
      ring

theorem integral_norm_bettinGonekLogMollifier_unit_le
    {N : ℕ} (hN : 2 ≤ N) {X : ℝ}
    (hNX : (N : ℝ) + 1 ≤ X) (t : ℝ) :
    (∫ x : ℝ in (N : ℝ)..N + 1,
        ‖bettinGonekLogMollifier x (farmerCriticalLinePoint t)‖) ≤
      Real.log X *
        (‖farmerMollifier N (farmerCriticalLinePoint t)‖ +
          ‖farmerMollifier (N + 1) (farmerCriticalLinePoint t)‖) := by
  let f : ℝ → ℝ := fun x =>
    ‖bettinGonekLogMollifier x (farmerCriticalLinePoint t)‖
  have hNOne : (1 : ℝ) < N := by
    exact_mod_cast (show 1 < N by omega)
  have hfi : IntervalIntegrable f volume (N : ℝ) (N + 1) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    have hbig :=
      integrableOn_norm_bettinGonekLogMollifier_Icc t ((N : ℝ) + 1)
    rw [integrableOn_Icc_iff_integrableOn_Ioc] at hbig
    exact hbig.mono_set (fun x hx =>
      ⟨lt_of_lt_of_le hNOne hx.1.le, hx.2⟩)
  have hconst : IntervalIntegrable
      (fun _x : ℝ =>
        Real.log X *
          (‖farmerMollifier N (farmerCriticalLinePoint t)‖ +
            ‖farmerMollifier (N + 1) (farmerCriticalLinePoint t)‖))
      volume (N : ℝ) (N + 1) :=
    intervalIntegrable_const
  calc
    (∫ x : ℝ in (N : ℝ)..N + 1, f x) ≤
        ∫ _x : ℝ in (N : ℝ)..N + 1,
          Real.log X *
            (‖farmerMollifier N (farmerCriticalLinePoint t)‖ +
              ‖farmerMollifier (N + 1) (farmerCriticalLinePoint t)‖) := by
      apply intervalIntegral.integral_mono_on (by norm_num) hfi hconst
      intro x hx
      exact norm_bettinGonekLogMollifier_le_endpoints_mul_log
        hN hx.1 hx.2 hNX _
    _ = Real.log X *
        (‖farmerMollifier N (farmerCriticalLinePoint t)‖ +
          ‖farmerMollifier (N + 1) (farmerCriticalLinePoint t)‖) := by
      norm_num

theorem norm_bettinGonekLogMollifier_one_two_le_log
    {X : ℕ} (hX : 2 ≤ X) {x : ℝ}
    (hx : x ∈ Set.Icc (1 : ℝ) 2) (s : ℂ) :
    ‖bettinGonekLogMollifier x s‖ ≤ Real.log X := by
  have hXpos : (0 : ℝ) < X := by positivity
  by_cases hxOne : x = 1
  · subst x
    rw [bettinGonekLogMollifier, farmerMollifier,
      if_neg (by norm_num), zero_mul, norm_zero]
    exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  · have hxgt : 1 < x := lt_of_le_of_ne hx.1 (Ne.symm hxOne)
    have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx.1
    have hxX : x ≤ (X : ℝ) := by
      have hTwoX : (2 : ℝ) ≤ X := by exact_mod_cast hX
      exact hx.2.trans hTwoX
    have hlog :
        Real.log x ≤ Real.log X :=
      Real.strictMonoOn_log.monotoneOn (lt_of_lt_of_le zero_lt_one hx.1)
        hXpos hxX
    rw [bettinGonekLogMollifier,
      farmerMollifier_eq_one_of_one_lt_le_two hxgt hx.2,
      one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hlogx]
    exact hlog

theorem integral_norm_bettinGonekLogMollifier_one_two_le_log
    {X : ℕ} (hX : 2 ≤ X) (t : ℝ) :
    (∫ x : ℝ in (1 : ℝ)..2,
        ‖bettinGonekLogMollifier x (farmerCriticalLinePoint t)‖) ≤
      Real.log X := by
  let f : ℝ → ℝ := fun x =>
    ‖bettinGonekLogMollifier x (farmerCriticalLinePoint t)‖
  have hfi : IntervalIntegrable f volume (1 : ℝ) 2 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    have hbig := integrableOn_norm_bettinGonekLogMollifier_Icc t 2
    rw [integrableOn_Icc_iff_integrableOn_Ioc] at hbig
    exact hbig
  calc
    (∫ x : ℝ in (1 : ℝ)..2, f x) ≤
        ∫ _x : ℝ in (1 : ℝ)..2, Real.log X := by
      apply intervalIntegral.integral_mono_on (by norm_num) hfi
        intervalIntegrable_const
      intro x hx
      exact norm_bettinGonekLogMollifier_one_two_le_log hX hx _
    _ = Real.log X := by norm_num

/-- The finite endpoint norm sum produced by partitioning the real mollifier cutoff. -/
def bettinGonekCutoffNormSum (X : ℕ) (t : ℝ) : ℝ :=
  ∑ N ∈ Finset.Ico 2 X,
    (‖farmerMollifier N (farmerCriticalLinePoint t)‖ +
      ‖farmerMollifier (N + 1) (farmerCriticalLinePoint t)‖)

theorem bettinGonekCutoffNormSum_nonneg (X : ℕ) (t : ℝ) :
    0 ≤ bettinGonekCutoffNormSum X t := by
  unfold bettinGonekCutoffNormSum
  positivity

theorem integral_norm_bettinGonekLogMollifier_le_cutoffNormSum
    {X : ℕ} (hX : 2 ≤ X) (t : ℝ) :
    (∫ x : ℝ in Set.Icc (1 : ℝ) X,
        ‖bettinGonekLogMollifier x (farmerCriticalLinePoint t)‖) ≤
      Real.log X * (1 + bettinGonekCutoffNormSum X t) := by
  let f : ℝ → ℝ := fun x =>
    ‖bettinGonekLogMollifier x (farmerCriticalLinePoint t)‖
  have htotal : IntervalIntegrable f volume (1 : ℝ) X := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by exact_mod_cast (show 1 ≤ X by omega))]
    have hbig :=
      integrableOn_norm_bettinGonekLogMollifier_Icc t (X : ℝ)
    rw [integrableOn_Icc_iff_integrableOn_Ioc] at hbig
    exact hbig
  have hOneX : (1 : ℝ) ≤ (X : ℝ) := by
    exact_mod_cast (show 1 ≤ X by omega)
  have hTwoX : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hfirst : IntervalIntegrable f volume (1 : ℝ) 2 :=
    htotal.mono_set (by
      rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2),
        uIcc_of_le hOneX]
      intro x hx
      exact ⟨hx.1, hx.2.trans hTwoX⟩)
  have htail : IntervalIntegrable f volume (2 : ℝ) X :=
    htotal.mono_set (by
      rw [uIcc_of_le hTwoX, uIcc_of_le hOneX]
      intro x hx
      exact ⟨le_trans (by norm_num) hx.1, hx.2⟩)
  have hunits :
      ∀ N ∈ Set.Ico 2 X,
        IntervalIntegrable f volume (N : ℝ) ((N + 1 : ℕ) : ℝ) := by
    intro N hN
    have hNN : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by norm_num
    exact htotal.mono_set (by
      rw [uIcc_of_le hNN, uIcc_of_le hOneX]
      intro x hx
      constructor
      · have hNtwo : 2 ≤ N := hN.1
        have : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
        exact this.trans hx.1
      · have hsucc : N + 1 ≤ X := Nat.succ_le_iff.mpr hN.2
        exact hx.2.trans (by exact_mod_cast hsucc))
  have hpartition :
      (∑ N ∈ Finset.Ico 2 X,
          ∫ x : ℝ in (N : ℝ)..N + 1, f x) =
        ∫ x : ℝ in (2 : ℝ)..X, f x := by
    simpa using
      (intervalIntegral.sum_integral_adjacent_intervals_Ico
        (a := fun N : ℕ => (N : ℝ)) hX hunits)
  have htailBound :
      (∫ x : ℝ in (2 : ℝ)..X, f x) ≤
        Real.log X * bettinGonekCutoffNormSum X t := by
    rw [← hpartition, bettinGonekCutoffNormSum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro N hN
    have hNIco : N ∈ Set.Ico 2 X := by simpa using hN
    have hsucc : N + 1 ≤ X := Nat.succ_le_iff.mpr hNIco.2
    exact integral_norm_bettinGonekLogMollifier_unit_le
      hNIco.1 (by exact_mod_cast hsucc) t
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le
      (by exact_mod_cast (show 1 ≤ X by omega))]
  rw [← intervalIntegral.integral_add_adjacent_intervals hfirst htail]
  have hfirstBound :=
    integral_norm_bettinGonekLogMollifier_one_two_le_log hX t
  change (∫ x : ℝ in (1 : ℝ)..2, f x) +
      (∫ x : ℝ in (2 : ℝ)..X, f x) ≤ _
  calc
    (∫ x : ℝ in (1 : ℝ)..2, f x) +
        (∫ x : ℝ in (2 : ℝ)..X, f x) ≤
      Real.log X + Real.log X * bettinGonekCutoffNormSum X t :=
        add_le_add hfirstBound htailBound
    _ = Real.log X * (1 + bettinGonekCutoffNormSum X t) := by ring

theorem bettinGonekResidue_lower_rpow_le_cutoffNormSum
    {rho : ℂ} (hrho : IsNontrivialZero rho)
    {X : ℕ} (hX : 2 ≤ X) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    bettinGonekResidueScaleLower rho *
        (X : ℝ) ^ (rho.re + 1 / 2) ≤
      bettinGonekInverseMellinBound rho 0 * Real.log X *
          (1 + bettinGonekCutoffNormSum X t) + 2 := by
  have hXpos : (0 : ℝ) < X := by positivity
  have hscale :=
    bettinGonekResidueScaleLower_le hrho ht
  have hresidue :=
    bettinGonekResidueScale_mul_rpow_le_JLineIntegral_three_add_two
      hrho t hXpos
  have hJ :=
    norm_bettinGonekJLineIntegral_three_le_inverseMellinBound
      hrho t (x := (X : ℝ)) (by exact_mod_cast hX)
  have hcutoff :=
    integral_norm_bettinGonekLogMollifier_le_cutoffNormSum hX t
  have hboundNonneg :
      0 ≤ bettinGonekInverseMellinBound rho 0 :=
    bettinGonekInverseMellinBound_nonneg rho 0
  calc
    bettinGonekResidueScaleLower rho *
        (X : ℝ) ^ (rho.re + 1 / 2) ≤
      bettinGonekResidueScale rho t *
        (X : ℝ) ^ (rho.re + 1 / 2) :=
        mul_le_mul_of_nonneg_right hscale (Real.rpow_nonneg hXpos.le _)
    _ ≤ ‖bettinGonekJLineIntegral rho t X 3‖ + 2 := hresidue
    _ ≤ bettinGonekInverseMellinBound rho t *
          (∫ x : ℝ in Set.Icc (1 : ℝ) X,
            ‖bettinGonekLogMollifier x (farmerCriticalLinePoint t)‖) + 2 :=
        by linarith
    _ = bettinGonekInverseMellinBound rho 0 *
          (∫ x : ℝ in Set.Icc (1 : ℝ) X,
            ‖bettinGonekLogMollifier x (farmerCriticalLinePoint t)‖) + 2 := by
        rw [bettinGonekInverseMellinBound_eq_zero]
    _ ≤ bettinGonekInverseMellinBound rho 0 *
          (Real.log X * (1 + bettinGonekCutoffNormSum X t)) + 2 := by
        gcongr
    _ = bettinGonekInverseMellinBound rho 0 * Real.log X *
          (1 + bettinGonekCutoffNormSum X t) + 2 := by ring

theorem bettinGonekResidue_lower_rpow_sq_le_cutoffNormSum_sq
    {rho : ℂ} (hrho : IsNontrivialZero rho)
    {X : ℕ} (hX : 2 ≤ X) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (bettinGonekResidueScaleLower rho *
        (X : ℝ) ^ (rho.re + 1 / 2)) ^ 2 ≤
      2 * bettinGonekInverseMellinBound rho 0 ^ 2 *
          Real.log X ^ 2 *
          (1 + bettinGonekCutoffNormSum X t) ^ 2 + 8 := by
  let p :=
    bettinGonekResidueScaleLower rho *
      (X : ℝ) ^ (rho.re + 1 / 2)
  let q :=
    bettinGonekInverseMellinBound rho 0 * Real.log X *
      (1 + bettinGonekCutoffNormSum X t)
  have hpq : p ≤ q + 2 :=
    bettinGonekResidue_lower_rpow_le_cutoffNormSum hrho hX ht
  have hp : 0 ≤ p := mul_nonneg
    (bettinGonekResidueScaleLower_pos hrho).le (Real.rpow_nonneg (by positivity) _)
  have hq : 0 ≤ q := by
    dsimp only [q]
    apply mul_nonneg
    · exact mul_nonneg (bettinGonekInverseMellinBound_nonneg rho 0)
        (Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega)))
    · exact add_nonneg zero_le_one
        (bettinGonekCutoffNormSum_nonneg X t)
  have hsquare : p ^ 2 ≤ (q + 2) ^ 2 :=
    (sq_le_sq₀ hp (by linarith)).2 hpq
  have hloose : (q + 2) ^ 2 ≤ 2 * q ^ 2 + 8 := by
    nlinarith [sq_nonneg (q - 2)]
  dsimp only [p, q] at hsquare hloose ⊢
  calc
    (bettinGonekResidueScaleLower rho *
        (X : ℝ) ^ (rho.re + 1 / 2)) ^ 2 ≤
      (bettinGonekInverseMellinBound rho 0 * Real.log X *
        (1 + bettinGonekCutoffNormSum X t) + 2) ^ 2 := hsquare
    _ ≤ 2 * (bettinGonekInverseMellinBound rho 0 * Real.log X *
        (1 + bettinGonekCutoffNormSum X t)) ^ 2 + 8 := hloose
    _ = 2 * bettinGonekInverseMellinBound rho 0 ^ 2 *
          Real.log X ^ 2 *
          (1 + bettinGonekCutoffNormSum X t) ^ 2 + 8 := by ring

/-- The endpoint square sum paired with `bettinGonekCutoffNormSum`. -/
def bettinGonekCutoffNormSqSum (X : ℕ) (t : ℝ) : ℝ :=
  ∑ N ∈ Finset.Ico 2 X,
    (Complex.normSq (farmerMollifier N (farmerCriticalLinePoint t)) +
      Complex.normSq
        (farmerMollifier (N + 1) (farmerCriticalLinePoint t)))

theorem bettinGonekCutoffNormSqSum_nonneg (X : ℕ) (t : ℝ) :
    0 ≤ bettinGonekCutoffNormSqSum X t := by
  unfold bettinGonekCutoffNormSqSum
  apply Finset.sum_nonneg
  intro N _
  exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

theorem continuous_bettinGonekCutoffNormSqSum (X : ℕ) :
    Continuous (fun t : ℝ => bettinGonekCutoffNormSqSum X t) := by
  unfold bettinGonekCutoffNormSqSum
  apply continuous_finsetSum
  intro N hN
  have hNtwo : 2 ≤ N := (Finset.mem_Ico.mp hN).1
  have hNgt : (1 : ℝ) < N := by
    exact_mod_cast (show 1 < N by omega)
  have hNpgt : (1 : ℝ) < N + 1 := by
    exact_mod_cast (show 1 < N + 1 by omega)
  exact (Complex.continuous_normSq.comp
      (continuous_farmerMollifier_criticalLine hNgt)).add
    (Complex.continuous_normSq.comp
      (continuous_farmerMollifier_criticalLine hNpgt))

theorem bettinGonekCutoffNormSum_sq_le
    (X : ℕ) (t : ℝ) :
    bettinGonekCutoffNormSum X t ^ 2 ≤
      2 * X * bettinGonekCutoffNormSqSum X t := by
  let b : ℕ → ℝ := fun N =>
    ‖farmerMollifier N (farmerCriticalLinePoint t)‖ +
      ‖farmerMollifier (N + 1) (farmerCriticalLinePoint t)‖
  have hCauchy :
      (∑ N ∈ Finset.Ico 2 X, b N) ^ 2 ≤
        ((Finset.Ico 2 X).card : ℝ) *
          ∑ N ∈ Finset.Ico 2 X, b N ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hpoint (N : ℕ) :
      b N ^ 2 ≤
        2 * (Complex.normSq
            (farmerMollifier N (farmerCriticalLinePoint t)) +
          Complex.normSq
            (farmerMollifier (N + 1) (farmerCriticalLinePoint t))) := by
    dsimp only [b]
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    nlinarith [sq_nonneg
      (‖farmerMollifier N (farmerCriticalLinePoint t)‖ -
        ‖farmerMollifier (N + 1) (farmerCriticalLinePoint t)‖)]
  have hsum :
      (∑ N ∈ Finset.Ico 2 X, b N ^ 2) ≤
        2 * bettinGonekCutoffNormSqSum X t := by
    rw [bettinGonekCutoffNormSqSum, Finset.mul_sum]
    exact Finset.sum_le_sum fun N _ => hpoint N
  have hcardNat : (Finset.Ico 2 X).card ≤ X := by
    rw [Nat.card_Ico]
    omega
  have hcard : ((Finset.Ico 2 X).card : ℝ) ≤ X := by
    exact_mod_cast hcardNat
  have hsumNonneg :
      0 ≤ ∑ N ∈ Finset.Ico 2 X, b N ^ 2 := by positivity
  have hXnonneg : (0 : ℝ) ≤ X := by positivity
  rw [bettinGonekCutoffNormSum]
  change (∑ N ∈ Finset.Ico 2 X, b N) ^ 2 ≤ _
  calc
    (∑ N ∈ Finset.Ico 2 X, b N) ^ 2 ≤
        ((Finset.Ico 2 X).card : ℝ) *
          ∑ N ∈ Finset.Ico 2 X, b N ^ 2 := hCauchy
    _ ≤ (X : ℝ) * ∑ N ∈ Finset.Ico 2 X, b N ^ 2 :=
      mul_le_mul_of_nonneg_right hcard hsumNonneg
    _ ≤ (X : ℝ) * (2 * bettinGonekCutoffNormSqSum X t) :=
      mul_le_mul_of_nonneg_left hsum hXnonneg
    _ = 2 * X * bettinGonekCutoffNormSqSum X t := by ring

theorem one_add_bettinGonekCutoffNormSum_sq_le
    (X : ℕ) (t : ℝ) :
    (1 + bettinGonekCutoffNormSum X t) ^ 2 ≤
      2 * (1 + 2 * X * bettinGonekCutoffNormSqSum X t) := by
  have hsum := bettinGonekCutoffNormSum_sq_le X t
  have hnonneg := bettinGonekCutoffNormSum_nonneg X t
  calc
    (1 + bettinGonekCutoffNormSum X t) ^ 2 ≤
        2 * (1 + bettinGonekCutoffNormSum X t ^ 2) := by
      nlinarith [sq_nonneg (1 - bettinGonekCutoffNormSum X t)]
    _ ≤ 2 * (1 + 2 * X * bettinGonekCutoffNormSqSum X t) := by
      gcongr

theorem bettinGonekResidue_lower_rpow_sq_le_cutoffNormSqSum
    {rho : ℂ} (hrho : IsNontrivialZero rho)
    {X : ℕ} (hX : 2 ≤ X) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (bettinGonekResidueScaleLower rho *
        (X : ℝ) ^ (rho.re + 1 / 2)) ^ 2 ≤
      4 * bettinGonekInverseMellinBound rho 0 ^ 2 *
          Real.log X ^ 2 *
          (1 + 2 * X * bettinGonekCutoffNormSqSum X t) + 8 := by
  have hsource :=
    bettinGonekResidue_lower_rpow_sq_le_cutoffNormSum_sq hrho hX ht
  have hfinite := one_add_bettinGonekCutoffNormSum_sq_le X t
  have hcoefficient :
      0 ≤ 2 * bettinGonekInverseMellinBound rho 0 ^ 2 *
        Real.log X ^ 2 := by positivity
  calc
    (bettinGonekResidueScaleLower rho *
        (X : ℝ) ^ (rho.re + 1 / 2)) ^ 2 ≤
      2 * bettinGonekInverseMellinBound rho 0 ^ 2 *
          Real.log X ^ 2 *
          (1 + bettinGonekCutoffNormSum X t) ^ 2 + 8 := hsource
    _ ≤ 2 * bettinGonekInverseMellinBound rho 0 ^ 2 *
          Real.log X ^ 2 *
          (2 * (1 + 2 * X * bettinGonekCutoffNormSqSum X t)) + 8 := by
      gcongr
    _ = 4 * bettinGonekInverseMellinBound rho 0 ^ 2 *
          Real.log X ^ 2 *
          (1 + 2 * X * bettinGonekCutoffNormSqSum X t) + 8 := by ring

/-- The finite endpoint moment sum obtained after integrating in height. -/
def bettinGonekCutoffMomentSum (X : ℕ) (T1 T2 : ℝ) : ℝ :=
  ∑ N ∈ Finset.Ico 2 X,
    (farmerMollifiedMoment N T1 T2 +
      farmerMollifiedMoment (N + 1) T1 T2)

theorem integral_zetaNormSq_mul_bettinGonekCutoffNormSqSum
    (X : ℕ) (T1 T2 : ℝ) :
    (∫ t : ℝ in T1..T2,
        Complex.normSq (riemannZeta (farmerCriticalLinePoint t)) *
          bettinGonekCutoffNormSqSum X t) =
      bettinGonekCutoffMomentSum X T1 T2 := by
  let z : ℝ → ℝ := fun t =>
    Complex.normSq (riemannZeta (farmerCriticalLinePoint t))
  have hpoint :
      (fun t : ℝ => z t * bettinGonekCutoffNormSqSum X t) =
        fun t : ℝ =>
          ∑ N ∈ Finset.Ico 2 X,
            (Complex.normSq
                (farmerMollifier N (farmerCriticalLinePoint t) *
                  riemannZeta (farmerCriticalLinePoint t)) +
              Complex.normSq
                (farmerMollifier (N + 1) (farmerCriticalLinePoint t) *
                  riemannZeta (farmerCriticalLinePoint t))) := by
    funext t
    rw [bettinGonekCutoffNormSqSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro N _
    rw [mul_add, Complex.normSq_mul, Complex.normSq_mul]
    dsimp only [z]
    ring
  rw [show (fun t : ℝ =>
      Complex.normSq (riemannZeta (farmerCriticalLinePoint t)) *
        bettinGonekCutoffNormSqSum X t) =
      (fun t : ℝ => z t * bettinGonekCutoffNormSqSum X t) by rfl,
    hpoint]
  have hint :
      ∀ N ∈ Finset.Ico 2 X,
        IntervalIntegrable
          (fun t : ℝ =>
            Complex.normSq
                (farmerMollifier N (farmerCriticalLinePoint t) *
                  riemannZeta (farmerCriticalLinePoint t)) +
              Complex.normSq
                (farmerMollifier (N + 1) (farmerCriticalLinePoint t) *
                  riemannZeta (farmerCriticalLinePoint t)))
          volume T1 T2 := by
    intro N hN
    have hNtwo : 2 ≤ N := (Finset.mem_Ico.mp hN).1
    have hNgt : (1 : ℝ) < N := by
      exact_mod_cast (show 1 < N by omega)
    have hNpgt : (1 : ℝ) < N + 1 := by
      exact_mod_cast (show 1 < N + 1 by omega)
    exact (intervalIntegrable_farmerMollifiedIntegrand hNgt T1 T2).add
      (intervalIntegrable_farmerMollifiedIntegrand hNpgt T1 T2)
  rw [intervalIntegral.integral_finsetSum hint]
  unfold bettinGonekCutoffMomentSum
  apply Finset.sum_congr rfl
  intro N hN
  have hNtwo : 2 ≤ N := (Finset.mem_Ico.mp hN).1
  have hNgt : (1 : ℝ) < N := by
    exact_mod_cast (show 1 < N by omega)
  have hNpgt : (1 : ℝ) < N + 1 := by
    exact_mod_cast (show 1 < N + 1 by omega)
  rw [intervalIntegral.integral_add
    (intervalIntegrable_farmerMollifiedIntegrand hNgt T1 T2)
    (intervalIntegrable_farmerMollifiedIntegrand hNpgt T1 T2)]
  rfl

theorem farmerMollifiedMoment_zero_one_le
    {N : ℕ} (hN : 2 ≤ N) {T : ℝ} (hT : 1 ≤ T) :
    farmerMollifiedMoment N 0 1 ≤
      farmerMollifiedMoment N 0 T := by
  have hNgt : (1 : ℝ) < N := by
    exact_mod_cast (show 1 < N by omega)
  exact intervalIntegral.integral_mono_interval le_rfl zero_le_one hT
    (Eventually.of_forall fun _ => Complex.normSq_nonneg _)
    (intervalIntegrable_farmerMollifiedIntegrand hNgt 0 T)

theorem bettinGonekCutoffMomentSum_zero_one_le
    (X : ℕ) {T : ℝ} (hT : 1 ≤ T) :
    bettinGonekCutoffMomentSum X 0 1 ≤
      bettinGonekCutoffMomentSum X 0 T := by
  unfold bettinGonekCutoffMomentSum
  apply Finset.sum_le_sum
  intro N hN
  have hNtwo : 2 ≤ N := (Finset.mem_Ico.mp hN).1
  have hleft :=
    farmerMollifiedMoment_zero_one_le (N := N) hNtwo (T := T) hT
  have hright :=
    farmerMollifiedMoment_zero_one_le (N := N + 1) (by omega) (T := T) hT
  norm_num [Nat.cast_add, Nat.cast_one] at hright
  exact add_le_add hleft hright

theorem bettinGonekCutoffMomentSum_le
    {X : ℕ} {T M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ N : ℕ, 2 ≤ N → N ≤ X →
      farmerMollifiedMoment N 0 T ≤ M) :
    bettinGonekCutoffMomentSum X 0 T ≤ 2 * X * M := by
  have hterm :
      ∀ N ∈ Finset.Ico 2 X,
        farmerMollifiedMoment N 0 T +
            farmerMollifiedMoment (N + 1) 0 T ≤
          2 * M := by
    intro N hN
    have hNIco := Finset.mem_Ico.mp hN
    have hsucc : N + 1 ≤ X := Nat.succ_le_iff.mpr hNIco.2
    have hleft := hbound N hNIco.1 hNIco.2.le
    have hright := hbound (N + 1) (by omega) hsucc
    norm_num [Nat.cast_add, Nat.cast_one] at hright
    linarith
  have hsum :
      bettinGonekCutoffMomentSum X 0 T ≤
        ((Finset.Ico 2 X).card : ℝ) * (2 * M) := by
    rw [bettinGonekCutoffMomentSum]
    calc
      (∑ N ∈ Finset.Ico 2 X,
          (farmerMollifiedMoment N 0 T +
            farmerMollifiedMoment (N + 1) 0 T)) ≤
          ∑ _N ∈ Finset.Ico 2 X, 2 * M :=
        Finset.sum_le_sum hterm
      _ = ((Finset.Ico 2 X).card : ℝ) * (2 * M) := by simp
  have hcardNat : (Finset.Ico 2 X).card ≤ X := by
    rw [Nat.card_Ico]
    omega
  have hcard : ((Finset.Ico 2 X).card : ℝ) ≤ X := by
    exact_mod_cast hcardNat
  calc
    bettinGonekCutoffMomentSum X 0 T ≤
        ((Finset.Ico 2 X).card : ℝ) * (2 * M) := hsum
    _ ≤ (X : ℝ) * (2 * M) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 2 * X * M := by ring

theorem bettinGonek_fixed_mass_rpow_sq_le
    {rho : ℂ} (hrho : IsNontrivialZero rho)
    {X : ℕ} (hX : 2 ≤ X) :
    (bettinGonekResidueScaleLower rho *
        (X : ℝ) ^ (rho.re + 1 / 2)) ^ 2 *
        bettinGonekFixedZetaMass ≤
      4 * bettinGonekInverseMellinBound rho 0 ^ 2 *
          Real.log X ^ 2 *
          (bettinGonekFixedZetaMass +
            2 * X * bettinGonekCutoffMomentSum X 0 1) +
        8 * bettinGonekFixedZetaMass := by
  let z : ℝ → ℝ := fun t =>
    Complex.normSq (riemannZeta (farmerCriticalLinePoint t))
  let S : ℝ → ℝ := fun t => bettinGonekCutoffNormSqSum X t
  let L : ℝ :=
    (bettinGonekResidueScaleLower rho *
      (X : ℝ) ^ (rho.re + 1 / 2)) ^ 2
  let K : ℝ :=
    4 * bettinGonekInverseMellinBound rho 0 ^ 2 * Real.log X ^ 2
  have hz : Continuous z :=
    Complex.continuous_normSq.comp continuous_riemannZeta_criticalLine
  have hS : Continuous S := continuous_bettinGonekCutoffNormSqSum X
  have hzInt : IntervalIntegrable z volume (0 : ℝ) 1 :=
    hz.intervalIntegrable 0 1
  have hzSInt : IntervalIntegrable (fun t => z t * S t) volume (0 : ℝ) 1 :=
    (hz.mul hS).intervalIntegrable 0 1
  have hrightInt : IntervalIntegrable
      (fun t => (K * (1 + 2 * X * S t) + 8) * z t)
      volume (0 : ℝ) 1 :=
    (((continuous_const.mul
        (continuous_const.add (continuous_const.mul hS))).add
      continuous_const).mul hz).intervalIntegrable 0 1
  have hleftInt : IntervalIntegrable (fun t => L * z t)
      volume (0 : ℝ) 1 :=
    hzInt.const_mul L
  have hintegral :
      (∫ t : ℝ in (0 : ℝ)..1, L * z t) ≤
        ∫ t : ℝ in (0 : ℝ)..1,
          (K * (1 + 2 * X * S t) + 8) * z t := by
    apply intervalIntegral.integral_mono_on zero_le_one hleftInt hrightInt
    intro t ht
    have hpoint :=
      bettinGonekResidue_lower_rpow_sq_le_cutoffNormSqSum hrho hX ht
    exact mul_le_mul_of_nonneg_right hpoint (Complex.normSq_nonneg _)
  have hrightPoint :
      (fun t : ℝ => (K * (1 + 2 * X * S t) + 8) * z t) =
        fun t : ℝ =>
          K * z t + (K * 2 * X) * (z t * S t) + 8 * z t := by
    funext t
    ring
  rw [hrightPoint,
    intervalIntegral.integral_add
      ((hzInt.const_mul K).add (hzSInt.const_mul (K * 2 * X)))
      (hzInt.const_mul 8),
    intervalIntegral.integral_add (hzInt.const_mul K)
      (hzSInt.const_mul (K * 2 * X)),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hintegral
  change L * bettinGonekFixedZetaMass ≤ _ at hintegral
  rw [show (∫ t : ℝ in (0 : ℝ)..1, z t * S t) =
      bettinGonekCutoffMomentSum X 0 1 by
        exact integral_zetaNormSq_mul_bettinGonekCutoffNormSqSum X 0 1] at hintegral
  rw [show (∫ t : ℝ in (0 : ℝ)..1, z t) =
      bettinGonekFixedZetaMass by rfl] at hintegral
  dsimp only [L, K] at hintegral ⊢
  calc
    (bettinGonekResidueScaleLower rho *
        (X : ℝ) ^ (rho.re + 1 / 2)) ^ 2 *
        bettinGonekFixedZetaMass ≤
      (4 * bettinGonekInverseMellinBound rho 0 ^ 2 * Real.log X ^ 2 *
          bettinGonekFixedZetaMass) +
        4 * bettinGonekInverseMellinBound rho 0 ^ 2 * Real.log X ^ 2 *
          2 * X * bettinGonekCutoffMomentSum X 0 1 +
        8 * bettinGonekFixedZetaMass := hintegral
    _ = 4 * bettinGonekInverseMellinBound rho 0 ^ 2 *
          Real.log X ^ 2 *
          (bettinGonekFixedZetaMass +
            2 * X * bettinGonekCutoffMomentSum X 0 1) +
        8 * bettinGonekFixedZetaMass := by ring

theorem rpow_add_half_sq
    {x beta : ℝ} (hx : 0 < x) :
    (x ^ (beta + 1 / 2)) ^ 2 = x ^ (2 * beta + 1) := by
  calc
    (x ^ (beta + 1 / 2)) ^ 2 =
        (x ^ (beta + 1 / 2)) ^ (2 : ℝ) := by
      exact (Real.rpow_natCast (x ^ (beta + 1 / 2)) 2).symm
    _ = x ^ ((beta + 1 / 2) * 2) :=
      (Real.rpow_mul hx.le (beta + 1 / 2) 2).symm
    _ = x ^ (2 * beta + 1) := by ring_nf

theorem rpow_sq
    {x exponent : ℝ} (hx : 0 ≤ x) :
    (x ^ exponent) ^ 2 = x ^ (2 * exponent) := by
  calc
    (x ^ exponent) ^ 2 = (x ^ exponent) ^ (2 : ℝ) :=
      (Real.rpow_natCast (x ^ exponent) 2).symm
    _ = x ^ (exponent * 2) :=
      (Real.rpow_mul hx exponent 2).symm
    _ = x ^ (2 * exponent) := by ring_nf

/-- The explicit constant in the integer-cutoff power estimate. -/
def bettinGonekIntegerPowerConstant (rho : ℂ) (C : ℝ) : ℝ :=
  (4 * bettinGonekInverseMellinBound rho 0 ^ 2 *
      (bettinGonekFixedZetaMass + 4 * C) +
      8 * bettinGonekFixedZetaMass) /
    (bettinGonekResidueScaleLower rho ^ 2 *
      bettinGonekFixedZetaMass)

theorem bettinGonekIntegerPowerConstant_pos
    {rho : ℂ} (hrho : IsNontrivialZero rho)
    {C : ℝ} (hC : 0 < C) :
    0 < bettinGonekIntegerPowerConstant rho C := by
  unfold bettinGonekIntegerPowerConstant
  apply div_pos
  · have hmass := bettinGonekFixedZetaMass_pos
    positivity
  · exact mul_pos (sq_pos_of_pos (bettinGonekResidueScaleLower_pos hrho))
      bettinGonekFixedZetaMass_pos

theorem bettinGonek_integer_power_le
    {rho : ℂ} (hrho : IsNontrivialZero rho)
    {X : ℕ} (hX : 2 ≤ X)
    {T delta C : ℝ} (hT : 1 ≤ T) (hdelta : 0 ≤ delta) (hC : 0 < C)
    (hbound : ∀ N : ℕ, 2 ≤ N → N ≤ X →
      farmerMollifiedMoment N 0 T ≤ C * T ^ (1 + delta)) :
    (X : ℝ) ^ (2 * rho.re) ≤
      bettinGonekIntegerPowerConstant rho C *
        (1 + Real.log X ^ 2 * X * T ^ (1 + delta)) := by
  let A := bettinGonekResidueScaleLower rho
  let B := bettinGonekInverseMellinBound rho 0
  let Z := bettinGonekFixedZetaMass
  let R := T ^ (1 + delta)
  let L := Real.log X ^ 2
  let U := L * X * R
  let K := 4 * B ^ 2 * (Z + 4 * C) + 8 * Z
  have hA : 0 < A := bettinGonekResidueScaleLower_pos hrho
  have hZ : 0 < Z := bettinGonekFixedZetaMass_pos
  have hXreal : (1 : ℝ) ≤ X := by
    exact_mod_cast (show 1 ≤ X by omega)
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le zero_lt_one hXreal
  have hexponent : 0 ≤ 1 + delta := by linarith
  have hR : 1 ≤ R := by
    dsimp only [R]
    exact Real.one_le_rpow hT hexponent
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  have hLU : L ≤ U := by
    dsimp only [U]
    have hXR : 1 ≤ (X : ℝ) * R :=
      one_le_mul_of_one_le_of_one_le hXreal hR
    nlinarith
  have hmomentNonneg : 0 ≤ C * R := mul_nonneg hC.le (by positivity)
  have hcutoffT :
      bettinGonekCutoffMomentSum X 0 T ≤ 2 * X * (C * R) :=
    bettinGonekCutoffMomentSum_le hmomentNonneg (by
      intro N hN hNX
      simpa only [R] using hbound N hN hNX)
  have hcutoff :
      bettinGonekCutoffMomentSum X 0 1 ≤ 2 * X * (C * R) :=
    (bettinGonekCutoffMomentSum_zero_one_le X hT).trans hcutoffT
  have hfixed := bettinGonek_fixed_mass_rpow_sq_le hrho hX
  have hfixed' :
      (A * (X : ℝ) ^ (rho.re + 1 / 2)) ^ 2 * Z ≤
        4 * B ^ 2 * L * (Z + 4 * X ^ 2 * C * R) + 8 * Z := by
    dsimp only [A, B, Z, L]
    calc
      (bettinGonekResidueScaleLower rho *
          (X : ℝ) ^ (rho.re + 1 / 2)) ^ 2 *
          bettinGonekFixedZetaMass ≤
        4 * bettinGonekInverseMellinBound rho 0 ^ 2 *
            Real.log X ^ 2 *
            (bettinGonekFixedZetaMass +
              2 * X * bettinGonekCutoffMomentSum X 0 1) +
          8 * bettinGonekFixedZetaMass := hfixed
      _ ≤ 4 * bettinGonekInverseMellinBound rho 0 ^ 2 *
            Real.log X ^ 2 *
            (bettinGonekFixedZetaMass +
              2 * X * (2 * X * (C * R))) +
          8 * bettinGonekFixedZetaMass := by
        gcongr
      _ = 4 * bettinGonekInverseMellinBound rho 0 ^ 2 *
            Real.log X ^ 2 *
            (bettinGonekFixedZetaMass + 4 * X ^ 2 * C * R) +
          8 * bettinGonekFixedZetaMass := by ring_nf
  have hZterm : L * Z ≤ (X : ℝ) * Z * (1 + U) := by
    calc
      L * Z ≤ U * Z := mul_le_mul_of_nonneg_right hLU hZ.le
      _ ≤ (X : ℝ) * Z * (1 + U) := by
        have hXU : U ≤ (X : ℝ) * (1 + U) := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hXreal) hU]
        nlinarith
  have hCterm :
      L * (4 * (X : ℝ) ^ 2 * C * R) ≤
        (X : ℝ) * (4 * C) * (1 + U) := by
    have heq :
        L * (4 * (X : ℝ) ^ 2 * C * R) =
          (X : ℝ) * (4 * C) * U := by
      dsimp only [U]
      ring_nf
    rw [heq]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hlogBlock :
      L * (Z + 4 * (X : ℝ) ^ 2 * C * R) ≤
        (X : ℝ) * (Z + 4 * C) * (1 + U) := by
    calc
      L * (Z + 4 * (X : ℝ) ^ 2 * C * R) =
          L * Z + L * (4 * (X : ℝ) ^ 2 * C * R) := by ring_nf
      _ ≤ (X : ℝ) * Z * (1 + U) +
          (X : ℝ) * (4 * C) * (1 + U) :=
        add_le_add hZterm hCterm
      _ = (X : ℝ) * (Z + 4 * C) * (1 + U) := by ring_nf
  have hRhs :
      4 * B ^ 2 * L * (Z + 4 * (X : ℝ) ^ 2 * C * R) + 8 * Z ≤
        K * X * (1 + U) := by
    have hmain := mul_le_mul_of_nonneg_left hlogBlock
      (by positivity : 0 ≤ 4 * B ^ 2)
    have height : 8 * Z ≤ 8 * Z * X * (1 + U) := by
      have : 1 ≤ (X : ℝ) * (1 + U) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hXreal) hU]
      nlinarith
    dsimp only [K]
    calc
      4 * B ^ 2 * L * (Z + 4 * (X : ℝ) ^ 2 * C * R) + 8 * Z ≤
          4 * B ^ 2 * ((X : ℝ) * (Z + 4 * C) * (1 + U)) +
            8 * Z * X * (1 + U) := add_le_add (by nlinarith) height
      _ = (4 * B ^ 2 * (Z + 4 * C) + 8 * Z) *
          X * (1 + U) := by ring_nf
  have hleft :
      (A ^ 2 * Z) * X * (X : ℝ) ^ (2 * rho.re) ≤
        K * X * (1 + U) := by
    calc
      (A ^ 2 * Z) * X * (X : ℝ) ^ (2 * rho.re) =
          (A * (X : ℝ) ^ (rho.re + 1 / 2)) ^ 2 * Z := by
        rw [mul_pow, rpow_add_half_sq hXpos,
          Real.rpow_add hXpos (2 * rho.re) 1, Real.rpow_one]
        ring_nf
      _ ≤ 4 * B ^ 2 * L * (Z + 4 * X ^ 2 * C * R) + 8 * Z := hfixed'
      _ ≤ K * X * (1 + U) := hRhs
  have hcancel :
      (A ^ 2 * Z) * (X : ℝ) ^ (2 * rho.re) ≤
        K * (1 + U) := by
    have hrearrange :
        ((A ^ 2 * Z) * (X : ℝ) ^ (2 * rho.re)) * X ≤
          (K * (1 + U)) * X := by
      calc
        ((A ^ 2 * Z) * (X : ℝ) ^ (2 * rho.re)) * X =
            (A ^ 2 * Z) * X * (X : ℝ) ^ (2 * rho.re) := by ring_nf
        _ ≤ K * X * (1 + U) := hleft
        _ = (K * (1 + U)) * X := by ring_nf
    exact (mul_le_mul_iff_of_pos_right hXpos).mp hrearrange
  have hden : 0 < A ^ 2 * Z := mul_pos (sq_pos_of_pos hA) hZ
  have hcancel' :
      (X : ℝ) ^ (2 * rho.re) * (A ^ 2 * Z) ≤
        K * (1 + U) := by
    simpa only [mul_comm] using hcancel
  calc
    (X : ℝ) ^ (2 * rho.re) ≤
        (K * (1 + U)) / (A ^ 2 * Z) :=
      (le_div_iff₀ hden).2 hcancel'
    _ = bettinGonekIntegerPowerConstant rho C * (1 + U) := by
      dsimp only [K, A, B, Z]
      rw [bettinGonekIntegerPowerConstant]
      exact (div_mul_eq_mul_div _ _ _).symm
    _ = bettinGonekIntegerPowerConstant rho C *
        (1 + Real.log X ^ 2 * X * T ^ (1 + delta)) := by rfl

/-- Bettin--Gonek's source argument: Farmer's long-mollifier moment bound forces every
nontrivial zero to satisfy the required power obstruction. -/
theorem bettinGonekMomentToPowerBridge_of_pos
    {theta : ℝ} (htheta : 0 < theta) :
    BettinGonekMomentToPowerBridge theta := by
  intro hmoment rho hrho epsilon hepsilon
  let delta := epsilon / 4
  have hdelta : 0 < delta := div_pos hepsilon (by norm_num)
  rcases hmoment delta hdelta with
    ⟨C₀, T₀, hC₀, hT₀, hmomentBound⟩
  let a := epsilon / (8 * theta)
  have ha : 0 < a := div_pos hepsilon (by positivity)
  let D := bettinGonekIntegerPowerConstant rho C₀
  have hD : 0 < D :=
    bettinGonekIntegerPowerConstant_pos hrho hC₀
  let C := (2 : ℝ) ^ (2 * rho.re) * D * (1 + (a ^ 2)⁻¹)
  have hbeta : 0 < rho.re := nontrivial_zero_re_pos hrho
  have hC : 0 < C := by
    dsimp only [C]
    exact mul_pos
      (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hD)
      (by positivity)
  refine ⟨C, hC, ?_⟩
  let threshold := max T₀ (max 1 ((2 : ℝ) ^ (1 / theta)))
  filter_upwards [eventually_ge_atTop threshold] with T hT
  have hTT₀ : T₀ ≤ T := le_trans (le_max_left _ _) hT
  have hTOne : 1 ≤ T :=
    le_trans (le_trans (le_max_left _ _)
      (le_max_right T₀ (max 1 ((2 : ℝ) ^ (1 / theta))))) hT
  have hTPowThreshold : (2 : ℝ) ^ (1 / theta) ≤ T :=
    le_trans (le_trans (le_max_right _ _)
      (le_max_right T₀ (max 1 ((2 : ℝ) ^ (1 / theta))))) hT
  have hTpos : 0 < T := zero_lt_one.trans_le hTOne
  have hthetaNonneg : 0 ≤ theta := htheta.le
  have hTthetaLower :
      (2 : ℝ) ≤ T ^ theta := by
    have hmono := Real.rpow_le_rpow
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
      hTPowThreshold hthetaNonneg
    have hpow :
        ((2 : ℝ) ^ (1 / theta)) ^ theta = 2 := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      rw [div_mul_cancel₀ 1 htheta.ne', Real.rpow_one]
    rwa [hpow] at hmono
  let X : ℕ := ⌊T ^ theta⌋₊
  have hX : 2 ≤ X := by
    dsimp only [X]
    exact Nat.le_floor hTthetaLower
  have hXOne : (1 : ℝ) ≤ X := by
    exact_mod_cast (show 1 ≤ X by omega)
  have hXpos : (0 : ℝ) < X := zero_lt_one.trans_le hXOne
  have hXT : (X : ℝ) ≤ T ^ theta := by
    dsimp only [X]
    exact Nat.floor_le (Real.rpow_nonneg hTpos.le _)
  have hinteger :
      (X : ℝ) ^ (2 * rho.re) ≤
        D * (1 + Real.log X ^ 2 * X * T ^ (1 + delta)) := by
    dsimp only [D]
    apply bettinGonek_integer_power_le hrho hX hTOne hdelta.le hC₀
    intro N hN hNX
    apply hmomentBound T hTT₀ N hN
    exact (by exact_mod_cast hNX : (N : ℝ) ≤ X).trans hXT
  have hfloorUpper :
      T ^ theta ≤ 2 * (X : ℝ) := by
    have hlt : T ^ theta < (X : ℝ) + 1 := by
      dsimp only [X]
      exact Nat.lt_floor_add_one _
    have hplus : (X : ℝ) + 1 ≤ 2 * X := by
      nlinarith
    exact hlt.le.trans hplus
  have hfloorPower :
      T ^ (2 * rho.re * theta) ≤
        (2 : ℝ) ^ (2 * rho.re) * (X : ℝ) ^ (2 * rho.re) := by
    calc
      T ^ (2 * rho.re * theta) =
          (T ^ theta) ^ (2 * rho.re) := by
        rw [← Real.rpow_mul hTpos.le]
        congr 1
        ring_nf
      _ ≤ (2 * (X : ℝ)) ^ (2 * rho.re) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hTpos.le _)
          hfloorUpper (by positivity)
      _ = (2 : ℝ) ^ (2 * rho.re) *
          (X : ℝ) ^ (2 * rho.re) :=
        Real.mul_rpow (by norm_num) hXpos.le
  have hlogNonneg : 0 ≤ Real.log X := Real.log_nonneg hXOne
  have hlogRaw :
      Real.log X ≤ (X : ℝ) ^ a / a :=
    Real.log_le_rpow_div hXpos.le ha
  have hXa :
      (X : ℝ) ^ a ≤ (T ^ theta) ^ a :=
    Real.rpow_le_rpow hXpos.le hXT ha.le
  have hTthetaA :
      (T ^ theta) ^ a = T ^ (theta * a) := by
    rw [← Real.rpow_mul hTpos.le]
  have hlog :
      Real.log X ≤ T ^ (theta * a) / a :=
    hlogRaw.trans (div_le_div_of_nonneg_right
      (hXa.trans_eq hTthetaA) ha.le)
  have hlogSq :
      Real.log X ^ 2 ≤ (T ^ (theta * a) / a) ^ 2 :=
    (sq_le_sq₀ hlogNonneg (div_nonneg (Real.rpow_nonneg hTpos.le _) ha.le)).2 hlog
  have hexponent : 2 * (theta * a) = epsilon / 4 := by
    dsimp only [a]
    calc
      2 * (theta * (epsilon / (8 * theta))) =
          2 * (theta * ((epsilon / 8) / theta)) := by
        rw [div_div]
      _ = 2 * (((epsilon / 8) / theta) * theta) := by ring_nf
      _ = 2 * (epsilon / 8) := by
        rw [div_mul_cancel₀ _ htheta.ne']
      _ = epsilon / 4 := by ring_nf
  have hlogSq' :
      Real.log X ^ 2 ≤ (a ^ 2)⁻¹ * T ^ (epsilon / 4) := by
    calc
      Real.log X ^ 2 ≤ (T ^ (theta * a) / a) ^ 2 := hlogSq
      _ = (a ^ 2)⁻¹ * T ^ (epsilon / 4) := by
        rw [div_pow, rpow_sq hTpos.le, hexponent]
        rw [div_eq_mul_inv]
        ring_nf
  have hdeltaEq : delta = epsilon / 4 := rfl
  have hU :
      Real.log X ^ 2 * X * T ^ (1 + delta) ≤
        (a ^ 2)⁻¹ * T ^ (1 + theta + epsilon / 2) := by
    calc
      Real.log X ^ 2 * X * T ^ (1 + delta) ≤
          ((a ^ 2)⁻¹ * T ^ (epsilon / 4)) *
            (T ^ theta) * T ^ (1 + delta) := by
        gcongr
      _ = (a ^ 2)⁻¹ * T ^ (1 + theta + epsilon / 2) := by
        rw [hdeltaEq]
        calc
          (a ^ 2)⁻¹ * T ^ (epsilon / 4) * T ^ theta *
              T ^ (1 + epsilon / 4) =
            (a ^ 2)⁻¹ * (T ^ (epsilon / 4) * T ^ theta) *
              T ^ (1 + epsilon / 4) := by ring_nf
          _ = (a ^ 2)⁻¹ * T ^ (epsilon / 4 + theta) *
              T ^ (1 + epsilon / 4) := by
            rw [← Real.rpow_add hTpos]
          _ = (a ^ 2)⁻¹ *
              (T ^ (epsilon / 4 + theta) * T ^ (1 + epsilon / 4)) := by
            ring_nf
          _ = (a ^ 2)⁻¹ *
              T ^ ((epsilon / 4 + theta) + (1 + epsilon / 4)) := by
            rw [← Real.rpow_add hTpos]
          _ = (a ^ 2)⁻¹ * T ^ (1 + theta + epsilon / 2) := by
            congr 1
            ring_nf
  have htargetExponentNonneg : 0 ≤ 1 + epsilon + theta := by
    linarith
  have htargetOne : 1 ≤ T ^ (1 + epsilon + theta) :=
    Real.one_le_rpow hTOne htargetExponentNonneg
  have hexponentMono :
      T ^ (1 + theta + epsilon / 2) ≤
        T ^ (1 + epsilon + theta) :=
    Real.rpow_le_rpow_of_exponent_le hTOne (by linarith)
  have honeU :
      1 + Real.log X ^ 2 * X * T ^ (1 + delta) ≤
        (1 + (a ^ 2)⁻¹) * T ^ (1 + epsilon + theta) := by
    calc
      1 + Real.log X ^ 2 * X * T ^ (1 + delta) ≤
          1 + (a ^ 2)⁻¹ * T ^ (1 + theta + epsilon / 2) :=
        add_le_add le_rfl hU
      _ ≤ T ^ (1 + epsilon + theta) +
          (a ^ 2)⁻¹ * T ^ (1 + epsilon + theta) := by
        gcongr
      _ = (1 + (a ^ 2)⁻¹) * T ^ (1 + epsilon + theta) := by ring_nf
  calc
    T ^ (2 * rho.re * theta) ≤
        (2 : ℝ) ^ (2 * rho.re) * (X : ℝ) ^ (2 * rho.re) :=
      hfloorPower
    _ ≤ (2 : ℝ) ^ (2 * rho.re) *
        (D * (1 + Real.log X ^ 2 * X * T ^ (1 + delta))) := by
      gcongr
    _ ≤ (2 : ℝ) ^ (2 * rho.re) *
        (D * ((1 + (a ^ 2)⁻¹) * T ^ (1 + epsilon + theta))) := by
      gcongr
    _ = C * T ^ (1 + epsilon + theta) := by
      dsimp only [C]
      ring_nf

theorem farmerThetaInfinityConjecture_implies_riemannHypothesis_bettinGonek
    (hmoment : FarmerThetaInfinityConjecture) :
    RiemannHypothesis := by
  exact farmerThetaInfinityConjecture_implies_riemannHypothesis hmoment
    (fun _theta htheta =>
      bettinGonekMomentToPowerBridge_of_pos htheta)

end

end LeanLab.Riemann
