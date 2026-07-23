import LeanLab.Riemann.BurnolY
import LeanLab.Riemann.ThetaInfinityMollifier
import LeanLab.Riemann.TruncatedPerron

set_option linter.style.header false

/-!
# Bettin--Gonek's mollifier Mellin identity

This module proves the first analytic identity in Bettin--Gonek's off-line-zero obstruction from
the actual real-cutoff Mobius mollifier. The inverse Mellin transform, contour shift, and residue
lower bound are not part of this module.
-/

namespace LeanLab.Riemann

open Complex Filter MeasureTheory Real Set
open scoped ArithmeticFunction.Moebius BigOperators Topology

noncomputable section

/-- The source mollifier after cancelling its logarithmic taper denominator. -/
def bettinGonekLogMollifier (x : ℝ) (s : ℂ) : ℂ :=
  farmerMollifier x s * Real.log x

/-- The `n`th Mobius source term, activated at the real cutoff `x >= n`. -/
def bettinGonekMollifierSeriesTerm (s : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  (Ici (n : ℝ)).indicator
    (fun y : ℝ =>
      LSeries.term (fun m : ℕ => (ArithmeticFunction.moebius m : ℂ)) s n *
        (Real.log (y / n) : ℂ)) x

/-- The `n`th source term after multiplication by the Mellin weight `x^(-w)`. -/
def bettinGonekMellinSeriesTerm (s w : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (-w) * bettinGonekMollifierSeriesTerm s n x

/-- The complete source integrand on the critical line. -/
def bettinGonekWeightedMollifier (t : ℝ) (w : ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (-w) * bettinGonekLogMollifier x (farmerCriticalLinePoint t)

/-- Bettin--Gonek's `H_t(w)` in the literal lower-cutoff normalization. -/
def bettinGonekH (t : ℝ) (w : ℂ) : ℂ :=
  ∫ x : ℝ in Ioi 1, bettinGonekWeightedMollifier t w x

/-- The scaled logarithmic kernel underlying one mollifier term. -/
def bettinGonekLogKernel (n : ℕ) (w : ℂ) (x : ℝ) : ℂ :=
  (Real.log (x / n) : ℂ) * (x : ℂ) ^ (-w)

theorem bettinGonekLogMollifier_eq_finset {x : ℝ} (hx : 1 < x) (s : ℂ) :
    bettinGonekLogMollifier x s =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        LSeries.term (fun m : ℕ => (ArithmeticFunction.moebius m : ℂ)) s n *
          (Real.log (x / n) : ℂ) := by
  rw [bettinGonekLogMollifier, farmerMollifier, if_pos hx, farmerMollifierCore]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := Nat.ne_zero_of_lt (Finset.mem_Icc.mp hn).1
  have hlogx : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  rw [LSeries.term_of_ne_zero hn0, farmerMobiusCoefficient, farmerLogTaper,
    Complex.cpow_neg]
  push_cast
  field_simp [hlogx]

theorem tsum_bettinGonekMollifierSeriesTerm (x : ℝ) (s : ℂ) :
    ∑' n : ℕ, bettinGonekMollifierSeriesTerm s n x =
      bettinGonekLogMollifier x s := by
  by_cases hx : 1 < x
  · rw [bettinGonekLogMollifier_eq_finset hx]
    rw [tsum_eq_sum (s := Finset.Icc 1 ⌊x⌋₊)]
    · apply Finset.sum_congr rfl
      intro n hn
      have hx0 : 0 ≤ x := (zero_lt_one.trans hx).le
      have hnfloor : n ≤ ⌊x⌋₊ := (Finset.mem_Icc.mp hn).2
      have hnfloorR : (n : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hnfloor
      have hfloorle : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
      have hnle : (n : ℝ) ≤ x := by
        exact hnfloorR.trans hfloorle
      simp [bettinGonekMollifierSeriesTerm, hnle]
    · intro n hn
      rcases eq_or_ne n 0 with rfl | hn0
      · simp [bettinGonekMollifierSeriesTerm, LSeries.term]
      · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
        have htop : ⌊x⌋₊ < n := by
          have := hn
          simp only [Finset.mem_Icc, not_and_or, not_le] at this
          omega
        have hfloor : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
        have hcast : (⌊x⌋₊ : ℝ) + 1 ≤ n := by exact_mod_cast htop
        have hxn : ¬(n : ℝ) ≤ x := not_le.mpr (hfloor.trans_le hcast)
        simp [bettinGonekMollifierSeriesTerm, hxn]
  · have hxle : x ≤ 1 := not_lt.mp hx
    have hleft : bettinGonekLogMollifier x s = 0 := by
      simp [bettinGonekLogMollifier, farmerMollifier, hx]
    rw [hleft]
    have hzero : (fun n : ℕ => bettinGonekMollifierSeriesTerm s n x) = 0 := by
      funext n
      rcases eq_or_ne n 0 with rfl | hn0
      · simp [bettinGonekMollifierSeriesTerm, LSeries.term]
      · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
        by_cases hnx : (n : ℝ) ≤ x
        · have hnle : n ≤ 1 := by exact_mod_cast hnx.trans hxle
          have hnEq : n = 1 := Nat.le_antisymm hnle hn1
          subst n
          have hxone : (1 : ℝ) ≤ x := by simpa using hnx
          have hxEq : x = 1 := le_antisymm hxle hxone
          subst x
          simp [bettinGonekMollifierSeriesTerm]
        · simp [bettinGonekMollifierSeriesTerm, hnx]
    rw [hzero]
    exact tsum_zero

theorem bettinGonekLogMollifier_eq_zero {x : ℝ} (hx : x ≤ 1) (s : ℂ) :
    bettinGonekLogMollifier x s = 0 := by
  simp [bettinGonekLogMollifier, farmerMollifier, not_lt.mpr hx]

theorem integrableOn_bettinGonekLogKernel_Ioi {n : ℕ} (hn : 0 < n)
    {w : ℂ} (hw : 1 < w.re) :
    IntegrableOn (bettinGonekLogKernel n w) (Ioi (n : ℝ)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hbase : IntegrableOn
      (fun u : ℝ => (Real.log u : ℂ) * (u : ℂ) ^ (-w)) (Ioi (1 : ℝ)) := by
    simpa only [show -(w - 1) - 1 = -w by ring, pow_one] using
      (integrableOn_log_pow_mul_cpow_neg_sub_one_Ioi 1
        (a := w - 1) (by simpa using hw))
  have hscaled : IntegrableOn
      (fun u : ℝ => bettinGonekLogKernel n w (n * u)) (Ioi (1 : ℝ)) := by
    change Integrable
      (fun u : ℝ => bettinGonekLogKernel n w (n * u))
      (volume.restrict (Ioi (1 : ℝ)))
    refine (hbase.const_mul ((n : ℂ) ^ (-w))).congr ?_
    apply (ae_restrict_iff' measurableSet_Ioi).mpr
    filter_upwards with u hu
    have hu0 : 0 ≤ u := (zero_lt_one.trans hu).le
    change (n : ℂ) ^ (-w) * ((Real.log u : ℂ) * (u : ℂ) ^ (-w)) =
      (Real.log (((n : ℝ) * u) / n) : ℂ) *
        (((n : ℝ) * u : ℝ) : ℂ) ^ (-w)
    have hdiv : (n : ℝ) * u / n = u := by field_simp
    rw [hdiv, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hnR.le hu0]
    push_cast
    ring
  have h := (integrableOn_Ioi_comp_mul_left_iff
    (bettinGonekLogKernel n w) 1 hnR).mp hscaled
  simpa using h

theorem integral_bettinGonekLogKernel_Ioi {n : ℕ} (hn : 0 < n)
    {w : ℂ} (hw : 1 < w.re) :
    (∫ x : ℝ in Ioi (n : ℝ), bettinGonekLogKernel n w x) =
      (n : ℂ) ^ (1 - w) / (w - 1) ^ 2 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hbase :
      (∫ u : ℝ in Ioi 1, (Real.log u : ℂ) * (u : ℂ) ^ (-w)) =
        1 / (w - 1) ^ 2 := by
    simpa only [show -(w - 1) - 1 = -w by ring, pow_one, Nat.factorial_one,
      Nat.cast_one, one_div, one_add_one_eq_two] using
      (integral_Ioi_log_pow_mul_cpow_neg_sub_one 1
        (a := w - 1) (by simpa using hw))
  have hscaled :
      (∫ u : ℝ in Ioi 1, bettinGonekLogKernel n w (n * u)) =
        (n : ℂ) ^ (-w) * (1 / (w - 1) ^ 2) := by
    calc
      _ = ∫ u : ℝ in Ioi 1,
          (n : ℂ) ^ (-w) * ((Real.log u : ℂ) * (u : ℂ) ^ (-w)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro u hu
        have hu0 : 0 ≤ u := (zero_lt_one.trans hu).le
        change (Real.log (((n : ℝ) * u) / n) : ℂ) *
            (((n : ℝ) * u : ℝ) : ℂ) ^ (-w) =
          (n : ℂ) ^ (-w) * ((Real.log u : ℂ) * (u : ℂ) ^ (-w))
        have hdiv : (n : ℝ) * u / n = u := by field_simp
        rw [hdiv, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hnR.le hu0]
        push_cast
        ring
      _ = (n : ℂ) ^ (-w) *
          (∫ u : ℝ in Ioi 1, (Real.log u : ℂ) * (u : ℂ) ^ (-w)) := by
        rw [integral_const_mul]
      _ = _ := by rw [hbase]
  have hsub := integral_comp_mul_left_Ioi (bettinGonekLogKernel n w) 1 hnR
  norm_num only [mul_one] at hsub
  rw [hscaled] at hsub
  have hrecover :
      (∫ x : ℝ in Ioi (n : ℝ), bettinGonekLogKernel n w x) =
        (n : ℂ) * ((n : ℂ) ^ (-w) * (1 / (w - 1) ^ 2)) := by
    let I : ℂ := ∫ x : ℝ in Ioi (n : ℝ), bettinGonekLogKernel n w x
    have hmul : (n : ℂ)⁻¹ * I =
        (n : ℂ) ^ (-w) * (1 / (w - 1) ^ 2) := by
      change (n : ℂ)⁻¹ *
          (∫ x : ℝ in Ioi (n : ℝ), bettinGonekLogKernel n w x) = _
      simpa only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast] using hsub.symm
    change I = _
    calc
      I = (n : ℂ) * ((n : ℂ)⁻¹ * I) := by field_simp
      _ = _ := by rw [hmul]
  have hpow : (n : ℂ) * (n : ℂ) ^ (-w) = (n : ℂ) ^ (1 - w) := by
    calc
      (n : ℂ) * (n : ℂ) ^ (-w) =
          (n : ℂ) ^ (1 : ℂ) * (n : ℂ) ^ (-w) := by rw [Complex.cpow_one]
      _ = (n : ℂ) ^ ((1 : ℂ) + (-w)) := (Complex.cpow_add _ _ hnC).symm
      _ = (n : ℂ) ^ (1 - w) := by rfl
  rw [hrecover, ← mul_assoc, hpow]
  simp only [div_eq_mul_inv, one_mul]

theorem bettinGonekMellinSeriesTerm_eq_indicator_kernel
    (s w : ℂ) (n : ℕ) :
    bettinGonekMellinSeriesTerm s w n =
      (Ici (n : ℝ)).indicator
        (fun x : ℝ =>
          LSeries.term (fun m : ℕ => (ArithmeticFunction.moebius m : ℂ)) s n *
            bettinGonekLogKernel n w x) := by
  funext x
  by_cases hx : x ∈ Ici (n : ℝ)
  · rw [Set.indicator_of_mem hx, bettinGonekMellinSeriesTerm,
      bettinGonekMollifierSeriesTerm, Set.indicator_of_mem hx, bettinGonekLogKernel]
    ring
  · simp [bettinGonekMellinSeriesTerm, bettinGonekMollifierSeriesTerm, hx]

theorem integrable_bettinGonekMellinSeriesTerm (s : ℂ) {w : ℂ}
    (hw : 1 < w.re) (n : ℕ) :
    Integrable (bettinGonekMellinSeriesTerm s w n) := by
  rcases eq_or_ne n 0 with rfl | hn0
  · have hzero : bettinGonekMellinSeriesTerm s w 0 = fun _x : ℝ => 0 := by
      funext x
      simp [bettinGonekMellinSeriesTerm, bettinGonekMollifierSeriesTerm, LSeries.term]
    rw [hzero]
    exact integrable_zero ℝ ℂ volume
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    have hkIci : IntegrableOn (bettinGonekLogKernel n w) (Ici (n : ℝ)) :=
      Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi
        (integrableOn_bettinGonekLogKernel_Ioi hn hw)
    rw [bettinGonekMellinSeriesTerm_eq_indicator_kernel]
    exact (integrable_indicator_iff measurableSet_Ici).mpr
      (hkIci.const_mul
        (LSeries.term (fun m : ℕ => (ArithmeticFunction.moebius m : ℂ)) s n))

theorem LSeries_term_mul_nat_cpow_one_sub
    (s w : ℂ) {n : ℕ} (hn : n ≠ 0) :
    LSeries.term (fun m : ℕ => (ArithmeticFunction.moebius m : ℂ)) s n *
        (n : ℂ) ^ (1 - w) =
      LSeries.term (fun m : ℕ => (ArithmeticFunction.moebius m : ℂ)) (w + s - 1) n := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
  simp only [div_eq_mul_inv, ← Complex.cpow_neg]
  rw [mul_assoc, ← Complex.cpow_add _ _ hnC]
  ring_nf

theorem integral_bettinGonekMellinSeriesTerm
    (s : ℂ) {w : ℂ} (hw : 1 < w.re) (n : ℕ) :
    (∫ x : ℝ, bettinGonekMellinSeriesTerm s w n x) =
      LSeries.term (fun m : ℕ => (ArithmeticFunction.moebius m : ℂ)) (w + s - 1) n /
        (w - 1) ^ 2 := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp [bettinGonekMellinSeriesTerm, bettinGonekMollifierSeriesTerm, LSeries.term]
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    rw [bettinGonekMellinSeriesTerm_eq_indicator_kernel,
      integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
      integral_const_mul, integral_bettinGonekLogKernel_Ioi hn hw]
    rw [div_eq_mul_inv, ← mul_assoc, LSeries_term_mul_nat_cpow_one_sub s w hn0]
    rfl

theorem norm_bettinGonekLogKernel {n : ℕ} (hn : 0 < n) (w : ℂ)
    {x : ℝ} (hx : (n : ℝ) < x) :
    ‖bettinGonekLogKernel n w x‖ =
      Real.log (x / n) * x ^ (-w.re) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hx0 : 0 < x := hnR.trans hx
  have hdiv : 1 ≤ x / (n : ℝ) := one_le_div hnR |>.mpr hx.le
  rw [bettinGonekLogKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_nonneg hdiv), Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  simp only [Complex.neg_re]

theorem re_bettinGonekLogKernel_real {n : ℕ} (hn : 0 < n) (a : ℝ)
    {x : ℝ} (hx : (n : ℝ) < x) :
    (bettinGonekLogKernel n (a : ℂ) x).re =
      Real.log (x / n) * x ^ (-a) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hx0 : 0 < x := hnR.trans hx
  have hpow : (x : ℂ) ^ (-(a : ℂ)) = ((x ^ (-a) : ℝ) : ℂ) := by
    have hexp : -(a : ℂ) = ((-a : ℝ) : ℂ) := by push_cast; rfl
    rw [hexp]
    exact (Complex.ofReal_cpow hx0.le (-a)).symm
  rw [bettinGonekLogKernel, hpow]
  norm_num

theorem integral_norm_bettinGonekLogKernel_Ioi {n : ℕ} (hn : 0 < n)
    {w : ℂ} (hw : 1 < w.re) :
    (∫ x : ℝ in Ioi (n : ℝ), ‖bettinGonekLogKernel n w x‖) =
      (n : ℝ) ^ (1 - w.re) / (w.re - 1) ^ 2 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hpureInt : IntegrableOn
      (bettinGonekLogKernel n (w.re : ℂ)) (Ioi (n : ℝ)) :=
    integrableOn_bettinGonekLogKernel_Ioi hn (by simpa using hw)
  calc
    (∫ x : ℝ in Ioi (n : ℝ), ‖bettinGonekLogKernel n w x‖) =
        ∫ x : ℝ in Ioi (n : ℝ),
          (bettinGonekLogKernel n (w.re : ℂ) x).re := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      change ‖bettinGonekLogKernel n w x‖ =
        (bettinGonekLogKernel n (w.re : ℂ) x).re
      rw [norm_bettinGonekLogKernel hn w hx,
        re_bettinGonekLogKernel_real hn w.re hx]
    _ = (∫ x : ℝ in Ioi (n : ℝ),
        bettinGonekLogKernel n (w.re : ℂ) x).re := integral_re hpureInt
    _ = ((n : ℂ) ^ (1 - (w.re : ℂ)) /
        ((w.re : ℂ) - 1) ^ 2).re := by
      rw [integral_bettinGonekLogKernel_Ioi hn (by simpa using hw)]
    _ = (n : ℝ) ^ (1 - w.re) / (w.re - 1) ^ 2 := by
      have hpow : (n : ℂ) ^ (1 - (w.re : ℂ)) =
          (((n : ℝ) ^ (1 - w.re) : ℝ) : ℂ) := by
        have hexp : 1 - (w.re : ℂ) = ((1 - w.re : ℝ) : ℂ) := by
          push_cast
          ring
        rw [hexp]
        exact (Complex.ofReal_cpow hnR.le (1 - w.re)).symm
      rw [hpow]
      change
        ((((n : ℝ) ^ (1 - w.re) : ℝ) : ℂ) /
            ((w.re : ℂ) - 1) ^ 2).re =
          (n : ℝ) ^ (1 - w.re) / (w.re - 1) ^ 2
      have hquot :
          (((n : ℝ) ^ (1 - w.re) : ℝ) : ℂ) /
              ((w.re : ℂ) - 1) ^ 2 =
            ((((n : ℝ) ^ (1 - w.re) / (w.re - 1) ^ 2 : ℝ)) : ℂ) := by
        push_cast
        rfl
      simpa only [Complex.ofReal_re] using congrArg Complex.re hquot

theorem integral_norm_bettinGonekMellinSeriesTerm
    (s : ℂ) {w : ℂ} (hw : 1 < w.re) {n : ℕ} (hn : 0 < n) :
    (∫ x : ℝ, ‖bettinGonekMellinSeriesTerm s w n x‖) =
      ‖LSeries.term (fun m : ℕ => (ArithmeticFunction.moebius m : ℂ)) s n‖ *
        ((n : ℝ) ^ (1 - w.re) / (w.re - 1) ^ 2) := by
  rw [bettinGonekMellinSeriesTerm_eq_indicator_kernel]
  simp_rw [norm_indicator_eq_indicator_norm, norm_mul]
  rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
    integral_const_mul, integral_norm_bettinGonekLogKernel_Ioi hn hw]

theorem norm_mobius_LSeries_term_criticalLine_le (t : ℝ) (n : ℕ) :
    ‖LSeries.term (fun m : ℕ => (ArithmeticFunction.moebius m : ℂ))
        (farmerCriticalLinePoint t) n‖ ≤
      (n : ℝ) ^ (-1 / 2 : ℝ) := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp [LSeries.term]
  · rw [LSeries.term_of_ne_zero hn0, div_eq_mul_inv, ← Complex.cpow_neg]
    apply norm_mobius_mul_nat_cpow_neg_le
    simp [farmerCriticalLinePoint]

/-- The summable majorant for the integrated norms on `Re(w)>3/2`. -/
def bettinGonekMellinIntegratedNormBound (w : ℂ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (1 / 2 - w.re) / (w.re - 1) ^ 2

theorem integral_norm_bettinGonekMellinSeriesTerm_le
    (t : ℝ) {w : ℂ} (hw : 3 / 2 < w.re) (n : ℕ) :
    (∫ x : ℝ, ‖bettinGonekMellinSeriesTerm (farmerCriticalLinePoint t) w n x‖) ≤
      bettinGonekMellinIntegratedNormBound w n := by
  rcases eq_or_ne n 0 with rfl | hn0
  · have hzero : bettinGonekMellinSeriesTerm (farmerCriticalLinePoint t) w 0 =
        fun _x : ℝ => 0 := by
      funext x
      simp [bettinGonekMellinSeriesTerm, bettinGonekMollifierSeriesTerm, LSeries.term]
    rw [hzero]
    simp only [norm_zero, integral_zero]
    exact div_nonneg (Real.rpow_nonneg (by norm_num) _) (sq_nonneg _)
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    rw [integral_norm_bettinGonekMellinSeriesTerm
      (farmerCriticalLinePoint t) (by linarith : 1 < w.re) hn]
    rw [bettinGonekMellinIntegratedNormBound]
    have hkernel : 0 ≤ (n : ℝ) ^ (1 - w.re) / (w.re - 1) ^ 2 :=
      div_nonneg (Real.rpow_nonneg hnR.le _) (sq_nonneg _)
    calc
      _ ≤ (n : ℝ) ^ (-1 / 2 : ℝ) *
          ((n : ℝ) ^ (1 - w.re) / (w.re - 1) ^ 2) :=
        mul_le_mul_of_nonneg_right (norm_mobius_LSeries_term_criticalLine_le t n) hkernel
      _ = (n : ℝ) ^ (1 / 2 - w.re) / (w.re - 1) ^ 2 := by
        rw [← mul_div_assoc, ← Real.rpow_add hnR]
        congr 2
        ring

theorem summable_bettinGonekMellinIntegratedNormBound
    {w : ℂ} (hw : 3 / 2 < w.re) :
    Summable (bettinGonekMellinIntegratedNormBound w) := by
  unfold bettinGonekMellinIntegratedNormBound
  exact (Real.summable_nat_rpow.mpr (by linarith : 1 / 2 - w.re < -1)).div_const _

theorem summable_integral_norm_bettinGonekMellinSeriesTerm
    (t : ℝ) {w : ℂ} (hw : 3 / 2 < w.re) :
    Summable
      (fun n : ℕ =>
        ∫ x : ℝ, ‖bettinGonekMellinSeriesTerm (farmerCriticalLinePoint t) w n x‖) := by
  exact (summable_bettinGonekMellinIntegratedNormBound hw).of_nonneg_of_le
    (fun _n => integral_nonneg fun _x => norm_nonneg _)
    (integral_norm_bettinGonekMellinSeriesTerm_le t hw)

private theorem integrable_tsum_of_summable_integral_norm
    {F : ℕ → ℝ → ℂ} (hF : ∀ n, Integrable (F n))
    (hSum : Summable fun n => ∫ x : ℝ, ‖F n x‖) :
    Integrable (fun x : ℝ => ∑' n : ℕ, F n x) := by
  have hmeas : ∀ n, AEStronglyMeasurable (F n) := fun n => (hF n).1
  refine ⟨AEStronglyMeasurable.tsum hmeas, ?_⟩
  rw [HasFiniteIntegral]
  have henorm (n : ℕ) :
      (∫⁻ x : ℝ, ‖F n x‖ₑ) = ‖∫ x : ℝ, ‖F n x‖‖ₑ := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hF n).norm, ENNReal.coe_nnreal_eq, coe_nnnorm,
      Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg (F n x))]
    simp only [coe_nnnorm]
  have hseries : (∑' n : ℕ, ∫⁻ x : ℝ, ‖F n x‖ₑ) ≠ ⊤ := by
    rw [funext henorm]
    exact ENNReal.tsum_coe_ne_top_iff_summable.mpr
      (NNReal.summable_coe.mp hSum.abs)
  have hmajor : (∫⁻ x : ℝ, ∑' n : ℕ, ‖F n x‖ₑ) < ⊤ := by
    rw [lintegral_tsum fun n => (hmeas n).enorm]
    exact lt_top_iff_ne_top.mpr hseries
  refine (lintegral_mono fun x => enorm_tsum_le_tsum_enorm).trans_lt hmajor

theorem integrable_tsum_bettinGonekMellinSeriesTerm
    (t : ℝ) {w : ℂ} (hw : 3 / 2 < w.re) :
    Integrable
      (fun x : ℝ =>
        ∑' n : ℕ, bettinGonekMellinSeriesTerm (farmerCriticalLinePoint t) w n x) := by
  exact integrable_tsum_of_summable_integral_norm
    (fun n => integrable_bettinGonekMellinSeriesTerm
      (farmerCriticalLinePoint t) (by linarith : 1 < w.re) n)
    (summable_integral_norm_bettinGonekMellinSeriesTerm t hw)

theorem tsum_bettinGonekMellinSeriesTerm
    (t : ℝ) (w : ℂ) (x : ℝ) :
    ∑' n : ℕ, bettinGonekMellinSeriesTerm (farmerCriticalLinePoint t) w n x =
      bettinGonekWeightedMollifier t w x := by
  simp only [bettinGonekMellinSeriesTerm, bettinGonekWeightedMollifier]
  rw [tsum_mul_left, tsum_bettinGonekMollifierSeriesTerm]

theorem integrable_bettinGonekWeightedMollifier
    (t : ℝ) {w : ℂ} (hw : 3 / 2 < w.re) :
    Integrable (bettinGonekWeightedMollifier t w) := by
  refine (integrable_tsum_bettinGonekMellinSeriesTerm t hw).congr ?_
  filter_upwards with x
  exact tsum_bettinGonekMellinSeriesTerm t w x

theorem integral_bettinGonekWeightedMollifier_eq_setIntegral_Ioi
    (t : ℝ) (w : ℂ) {c : ℝ} (hc : c ≤ 1) :
    (∫ x : ℝ, bettinGonekWeightedMollifier t w x) =
      ∫ x : ℝ in Ioi c, bettinGonekWeightedMollifier t w x := by
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : c < x
  · rw [Set.indicator_of_mem (show x ∈ Ioi c from hx)]
  · have hx1 : x ≤ 1 := (not_lt.mp hx).trans hc
    rw [Set.indicator_of_notMem (show x ∉ Ioi c from hx)]
    simp [bettinGonekWeightedMollifier, bettinGonekLogMollifier_eq_zero hx1]

theorem hasSum_integral_bettinGonekMellinSeriesTerm
    (t : ℝ) {w : ℂ} (hw : 3 / 2 < w.re) :
    HasSum
      (fun n : ℕ =>
        ∫ x : ℝ, bettinGonekMellinSeriesTerm (farmerCriticalLinePoint t) w n x)
      (∫ x : ℝ, bettinGonekWeightedMollifier t w x) := by
  have h := MeasureTheory.hasSum_integral_of_summable_integral_norm
    (fun n => integrable_bettinGonekMellinSeriesTerm
      (farmerCriticalLinePoint t) (by linarith : 1 < w.re) n)
    (summable_integral_norm_bettinGonekMellinSeriesTerm t hw)
  have heq :
      (∫ x : ℝ,
        ∑' n : ℕ, bettinGonekMellinSeriesTerm (farmerCriticalLinePoint t) w n x) =
        ∫ x : ℝ, bettinGonekWeightedMollifier t w x := by
    apply integral_congr_ae
    filter_upwards with x
    exact tsum_bettinGonekMellinSeriesTerm t w x
  rw [← heq]
  exact h

theorem integral_bettinGonekWeightedMollifier
    (t : ℝ) {w : ℂ} (hw : 3 / 2 < w.re) :
    (∫ x : ℝ, bettinGonekWeightedMollifier t w x) =
      (riemannZeta (w - 1 / 2 + t * Complex.I))⁻¹ / (w - 1) ^ 2 := by
  let s := farmerCriticalLinePoint t
  let q := w + s - 1
  have hq : 1 < q.re := by
    dsimp only [q, s, farmerCriticalLinePoint]
    norm_num [Complex.add_re, Complex.mul_re]
    linarith
  have hsource := hasSum_integral_bettinGonekMellinSeriesTerm t hw
  have hsource' : HasSum
      (fun n : ℕ =>
        LSeries.term (fun m : ℕ => (ArithmeticFunction.moebius m : ℂ)) q n /
          (w - 1) ^ 2)
      (∫ x : ℝ, bettinGonekWeightedMollifier t w x) := by
    simpa only [q, s, integral_bettinGonekMellinSeriesTerm
      (farmerCriticalLinePoint t) (by linarith : 1 < w.re)] using hsource
  have hL : HasSum
      (fun n : ℕ =>
        LSeries.term (fun m : ℕ => (ArithmeticFunction.moebius m : ℂ)) q n /
          (w - 1) ^ 2)
      ((riemannZeta q)⁻¹ / (w - 1) ^ 2) := by
    have hbase := (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hq).LSeriesHasSum
    rw [LSeries_moebius_eq_reciprocal_riemannZeta hq] at hbase
    exact hbase.div_const ((w - 1) ^ 2)
  have hvalue := hsource'.unique hL
  have hqeq : q = w - 1 / 2 + t * Complex.I := by
    dsimp only [q, s, farmerCriticalLinePoint]
    push_cast
    ring
  simpa only [hqeq] using hvalue

theorem mellinConvergent_bettinGonekLogMollifier
    (t : ℝ) {w : ℂ} (hw : 3 / 2 < w.re) :
    MellinConvergent
      (fun x : ℝ => bettinGonekLogMollifier x (farmerCriticalLinePoint t)) (1 - w) := by
  rw [MellinConvergent]
  have hweighted : IntegrableOn (bettinGonekWeightedMollifier t w) (Ioi (0 : ℝ)) :=
    (integrable_bettinGonekWeightedMollifier t hw).integrableOn
  refine hweighted.congr ?_
  apply (ae_restrict_iff' measurableSet_Ioi).mpr
  filter_upwards with x hx
  change bettinGonekWeightedMollifier t w x =
    (x : ℂ) ^ (1 - w - 1) *
      bettinGonekLogMollifier x (farmerCriticalLinePoint t)
  rw [bettinGonekWeightedMollifier]
  ring_nf

theorem mellin_bettinGonekLogMollifier_eq_integral
    (t : ℝ) (w : ℂ) :
    mellin (fun x : ℝ => bettinGonekLogMollifier x (farmerCriticalLinePoint t)) (1 - w) =
      ∫ x : ℝ, bettinGonekWeightedMollifier t w x := by
  rw [mellin, integral_bettinGonekWeightedMollifier_eq_setIntegral_Ioi
    t w (show (0 : ℝ) ≤ 1 by norm_num)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  simp only [bettinGonekWeightedMollifier, smul_eq_mul]
  ring_nf

theorem hasMellin_bettinGonekLogMollifier
    (t : ℝ) {w : ℂ} (hw : 3 / 2 < w.re) :
    HasMellin
      (fun x : ℝ => bettinGonekLogMollifier x (farmerCriticalLinePoint t)) (1 - w)
      ((riemannZeta (w - 1 / 2 + t * Complex.I))⁻¹ / (w - 1) ^ 2) := by
  refine ⟨mellinConvergent_bettinGonekLogMollifier t hw, ?_⟩
  rw [mellin_bettinGonekLogMollifier_eq_integral]
  exact integral_bettinGonekWeightedMollifier t hw

theorem bettinGonekH_eq
    (t : ℝ) {w : ℂ} (hw : 3 / 2 < w.re) :
    bettinGonekH t w =
      1 / ((w - 1) ^ 2 * riemannZeta (w - 1 / 2 + t * Complex.I)) := by
  rw [bettinGonekH, ← integral_bettinGonekWeightedMollifier_eq_setIntegral_Ioi
    t w (show (1 : ℝ) ≤ 1 by rfl), integral_bettinGonekWeightedMollifier t hw]
  have hw1 : w - 1 ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at hre
    linarith
  have hq : 1 < (w - 1 / 2 + t * Complex.I).re := by
    norm_num [Complex.add_re, Complex.mul_re]
    linarith
  have hzeta := riemannZeta_ne_zero_of_one_lt_re hq
  field_simp

theorem bettinGonekMellinIdentity_endpoint
    (t : ℝ) {w : ℂ} (hw : 3 / 2 < w.re) :
    (∀ x : ℝ,
      ∑' n : ℕ, bettinGonekMollifierSeriesTerm (farmerCriticalLinePoint t) n x =
        bettinGonekLogMollifier x (farmerCriticalLinePoint t)) ∧
      HasMellin
        (fun x : ℝ => bettinGonekLogMollifier x (farmerCriticalLinePoint t)) (1 - w)
        ((riemannZeta (w - 1 / 2 + t * Complex.I))⁻¹ / (w - 1) ^ 2) ∧
      bettinGonekH t w =
        1 / ((w - 1) ^ 2 * riemannZeta (w - 1 / 2 + t * Complex.I)) := by
  exact ⟨fun x => tsum_bettinGonekMollifierSeriesTerm x (farmerCriticalLinePoint t),
    hasMellin_bettinGonekLogMollifier t hw, bettinGonekH_eq t hw⟩

end

end LeanLab.Riemann
