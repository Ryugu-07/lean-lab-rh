import LeanLab.Riemann.BurnolLowerBound
import LeanLab.Riemann.BaezDuarteMellin
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Prod

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Burnol's explicit Hardy-space function

This file formalizes the explicit function `A` used in Burnol's unitary model for the
Nyman--Beurling approximation distance.
-/

namespace LeanLab.Riemann

open MeasureTheory Set
open scoped ENNReal NNReal Topology

/-- Burnol's explicit source function
`floor(1/t) * log t + log(floor(1/t)!) + floor(1/t)` on the positive half-line. -/
noncomputable def burnolA (t : ℝ) : ℝ :=
  if 0 < t then
    let n := ⌊t⁻¹⌋₊
    (n : ℝ) * Real.log t + Real.log (n.factorial : ℝ) + (n : ℝ)
  else 0

theorem burnolA_of_pos {t : ℝ} (ht : 0 < t) :
    burnolA t =
      (⌊t⁻¹⌋₊ : ℝ) * Real.log t +
        Real.log (⌊t⁻¹⌋₊.factorial : ℝ) + (⌊t⁻¹⌋₊ : ℝ) := by
  simp [burnolA, ht]

theorem burnolA_eq_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    burnolA t = 0 := by
  simp [burnolA, not_lt.mpr ht]

theorem burnolA_eq_zero_of_one_lt {t : ℝ} (ht : 1 < t) :
    burnolA t = 0 := by
  rw [burnolA_of_pos (zero_lt_one.trans ht)]
  have hinv : t⁻¹ < 1 := (inv_lt_one₀ (zero_lt_one.trans ht)).2 ht
  have hfloor : ⌊t⁻¹⌋₊ = 0 := Nat.floor_eq_zero.mpr hinv
  simp [hfloor]

theorem measurable_burnolA : Measurable burnolA := by
  have hn : Measurable (fun t : ℝ => ⌊t⁻¹⌋₊) := measurable_inv.nat_floor
  have hncast : Measurable (fun t : ℝ => (⌊t⁻¹⌋₊ : ℝ)) :=
    (measurable_of_countable _).comp hn
  have hfactorialNat : Measurable (fun n : ℕ => (n.factorial : ℝ)) :=
    measurable_of_countable _
  have hfactorial : Measurable (fun t : ℝ => (⌊t⁻¹⌋₊.factorial : ℝ)) :=
    hfactorialNat.comp hn
  change Measurable (fun t : ℝ => if 0 < t then
    (⌊t⁻¹⌋₊ : ℝ) * Real.log t +
      Real.log (⌊t⁻¹⌋₊.factorial : ℝ) + (⌊t⁻¹⌋₊ : ℝ) else 0)
  exact Measurable.ite measurableSet_Ioi
    ((hncast.mul Real.measurable_log).add hfactorial.log |>.add hncast)
    measurable_const

/-- The reciprocal-variable integrand used to identify Burnol's floor formula. -/
noncomputable def burnolFractDiv (x : ℝ) : ℝ :=
  if x = 0 then 0 else Int.fract x / x

theorem burnolFractDiv_eq_on_nat_interval (n : ℕ) :
    Set.EqOn burnolFractDiv (fun x : ℝ => 1 - (n : ℝ) / x)
      (Ioo (n : ℝ) (n + 1 : ℝ)) := by
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt (Nat.cast_nonneg n |>.trans_lt hx.1)
  have hfloor : ⌊x⌋ = (n : ℤ) :=
    Int.floor_eq_on_Ico (n : ℤ) x ⟨hx.1.le, by exact_mod_cast hx.2⟩
  rw [burnolFractDiv, if_neg hx0]
  simp only [Int.fract, hfloor, Int.cast_natCast]
  field_simp

theorem intervalIntegral_burnolFractDiv_zero_one :
    (∫ x : ℝ in (0 : ℝ)..1, burnolFractDiv x) = 1 := by
  have hEq : Set.EqOn burnolFractDiv (fun _ : ℝ => 1) (Ioo (0 : ℝ) 1) := by
    simpa using burnolFractDiv_eq_on_nat_interval 0
  rw [intervalIntegral.integral_congr_Ioo_of_le zero_le_one hEq]
  simp

theorem intervalIntegral_burnolFractDiv_nat_succ (n : ℕ) (hn : 0 < n) :
    (∫ x : ℝ in (n : ℝ)..(n + 1 : ℝ), burnolFractDiv x) =
      1 - (n : ℝ) * Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) := by
  rw [intervalIntegral.integral_congr_Ioo_of_le (by exact_mod_cast Nat.le_succ n)
    (burnolFractDiv_eq_on_nat_interval n)]
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [intervalIntegral.integral_sub]
  · have hdiv : (fun x : ℝ => (n : ℝ) / x) =
        fun x : ℝ => (n : ℝ) * (1 / x) := by
      funext x
      ring
    rw [hdiv, intervalIntegral.integral_const_mul]
    rw [integral_one_div_of_pos hnR (by positivity)]
    norm_num
  · exact intervalIntegrable_const
  · exact (intervalIntegrable_inv_iff.2
      (Or.inr (notMem_uIcc_of_lt hnR (by positivity)))).const_mul _

theorem intervalIntegrable_burnolFractDiv_nat (n : ℕ) :
    IntervalIntegrable burnolFractDiv volume (n : ℝ) (n + 1 : ℝ) := by
  have hle : (n : ℝ) ≤ (n + 1 : ℝ) := by exact_mod_cast Nat.le_succ n
  by_cases hn : n = 0
  · subst n
    have hEq : Set.EqOn (fun _ : ℝ => (1 : ℝ)) burnolFractDiv (Ioo (0 : ℝ) 1) := by
      simpa using (burnolFractDiv_eq_on_nat_interval 0).symm
    have hconst : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 1 :=
      intervalIntegrable_const (c := (1 : ℝ))
    simpa [Nat.cast_add] using
      hconst.congr_uIoo (by simpa [uIoo_of_le hle] using hEq)
  · have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hinv : IntervalIntegrable (fun x : ℝ => x⁻¹) volume (n : ℝ) (n + 1 : ℝ) :=
      intervalIntegrable_inv_iff.2
        (Or.inr (notMem_uIcc_of_lt hnR (by positivity)))
    have hsimple : IntervalIntegrable (fun x : ℝ => 1 - (n : ℝ) / x)
        volume (n : ℝ) (n + 1 : ℝ) := by
      have hconst : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume
          (n : ℝ) (n + 1 : ℝ) := intervalIntegrable_const (c := (1 : ℝ))
      simpa only [div_eq_mul_inv] using
        hconst.sub (hinv.const_mul (n : ℝ))
    exact hsimple.congr_uIoo (by
      simpa [uIoo_of_le hle] using (burnolFractDiv_eq_on_nat_interval n).symm)

theorem intervalIntegrable_burnolFractDiv_zero_nat : ∀ n : ℕ,
    IntervalIntegrable burnolFractDiv volume 0 (n : ℝ)
  | 0 => by simp
  | n + 1 => by
      simpa [Nat.cast_add] using
        (intervalIntegrable_burnolFractDiv_zero_nat n).trans
          (intervalIntegrable_burnolFractDiv_nat n)

theorem intervalIntegral_burnolFractDiv_nat_to
    (n : ℕ) (hn : 0 < n) {x : ℝ}
    (hnx : (n : ℝ) ≤ x) (hxn : x ≤ (n + 1 : ℝ)) :
    (∫ u : ℝ in (n : ℝ)..x, burnolFractDiv u) =
      x - n - (n : ℝ) * Real.log (x / n) := by
  have hEq : Set.EqOn burnolFractDiv (fun u : ℝ => 1 - (n : ℝ) / u)
      (Ioo (n : ℝ) x) := by
    intro u hu
    exact burnolFractDiv_eq_on_nat_interval n ⟨hu.1, hu.2.trans_le hxn⟩
  rw [intervalIntegral.integral_congr_Ioo_of_le hnx hEq]
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hxR : 0 < x := hnR.trans_le hnx
  rw [intervalIntegral.integral_sub]
  · have hdiv : (fun u : ℝ => (n : ℝ) / u) =
        fun u : ℝ => (n : ℝ) * (1 / u) := by
      funext u
      ring
    rw [hdiv, intervalIntegral.integral_const_mul]
    rw [integral_one_div_of_pos hnR hxR]
    norm_num
  · exact intervalIntegrable_const
  · exact (intervalIntegrable_inv_iff.2
      (Or.inr (notMem_uIcc_of_lt hnR hxR))).const_mul _

theorem intervalIntegral_burnolFractDiv_zero_nat : ∀ n : ℕ,
    (∫ x : ℝ in (0 : ℝ)..(n : ℝ), burnolFractDiv x) =
      (n : ℝ) + Real.log (n.factorial : ℝ) - (n : ℝ) * Real.log (n : ℝ)
  | 0 => by simp
  | n + 1 => by
      have hadd := intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_burnolFractDiv_zero_nat n)
        (intervalIntegrable_burnolFractDiv_nat n)
      simp only [Nat.cast_add, Nat.cast_one]
      rw [← hadd, intervalIntegral_burnolFractDiv_zero_nat n]
      by_cases hn : n = 0
      · subst n
        simpa using intervalIntegral_burnolFractDiv_zero_one
      · rw [intervalIntegral_burnolFractDiv_nat_succ n (Nat.pos_of_ne_zero hn)]
        have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
        have hsuccR : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
        rw [Real.log_div hsuccR.ne' hnR.ne']
        rw [Nat.factorial_succ, Nat.cast_mul]
        rw [Real.log_mul hsuccR.ne' (by positivity : ((n.factorial : ℕ) : ℝ) ≠ 0)]
        push_cast
        ring

theorem intervalIntegral_burnolFractDiv_zero_to {x : ℝ} (hx : 0 < x) :
    (∫ u : ℝ in (0 : ℝ)..x, burnolFractDiv u) =
      x + Real.log (⌊x⌋₊.factorial : ℝ) - (⌊x⌋₊ : ℝ) * Real.log x := by
  let n := ⌊x⌋₊
  have hnx : (n : ℝ) ≤ x := Nat.floor_le hx.le
  have hxn : x ≤ (n + 1 : ℝ) := (Nat.lt_floor_add_one x).le
  by_cases hn : n = 0
  · have hx1 : x ≤ 1 := by simpa [n, hn] using hxn
    have hEq : Set.EqOn burnolFractDiv (fun _ : ℝ => 1) (Ioo (0 : ℝ) x) := by
      intro u hu
      have hu0 : (((0 : ℕ) : ℝ)) < u := by simpa using hu.1
      have hu1 : u < (((0 : ℕ) : ℝ) + 1) := by
        simpa using hu.2.trans_le hx1
      simpa using burnolFractDiv_eq_on_nat_interval 0 ⟨hu0, hu1⟩
    rw [intervalIntegral.integral_congr_Ioo_of_le hx.le hEq]
    simp [n, hn]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hIntTail : IntervalIntegrable burnolFractDiv volume (n : ℝ) x := by
      apply (intervalIntegrable_burnolFractDiv_nat n).mono_set
      rw [uIcc_of_le hnx]
      rw [uIcc_of_le (by exact_mod_cast Nat.le_succ n : (n : ℝ) ≤ (n + 1 : ℝ))]
      exact Icc_subset_Icc_right hxn
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_burnolFractDiv_zero_nat n) hIntTail
    rw [← hadd, intervalIntegral_burnolFractDiv_zero_nat n,
      intervalIntegral_burnolFractDiv_nat_to n hnpos hnx hxn]
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
    rw [Real.log_div hx.ne' hnR.ne']
    dsimp only [n]
    ring

theorem burnolA_eq_reciprocal_fract_integral_sub_fractionalPart
    {t : ℝ} (ht : 0 < t) :
    burnolA t =
      (∫ x : ℝ in (0 : ℝ)..t⁻¹, burnolFractDiv x) - fractionalPartKernel 1 t := by
  have hinv : 0 < t⁻¹ := inv_pos.mpr ht
  let n := ⌊t⁻¹⌋₊
  have hfloorInt : ⌊t⁻¹⌋ = (n : ℤ) := by
    apply Int.floor_eq_iff.mpr
    exact ⟨Nat.floor_le hinv.le, by simpa [n] using Nat.lt_floor_add_one t⁻¹⟩
  rw [burnolA_of_pos ht, intervalIntegral_burnolFractDiv_zero_to hinv]
  rw [fractionalPartKernel, one_div]
  simp only [Int.fract, hfloorInt, Int.cast_natCast]
  rw [Real.log_inv]
  dsimp only [n]
  ring

/-- The positive-half-line kernel divided by the Hardy measure factor. -/
noncomputable def burnolFractionalPartDiv (u : ℝ) : ℝ :=
  fractionalPartKernel 1 u / u

theorem measurable_burnolFractionalPartDiv : Measurable burnolFractionalPartDiv := by
  exact (measurable_fractionalPartKernel 1).div measurable_id

theorem burnolFractionalPartDiv_eq_inv_sq {u : ℝ} (hu : 1 < u) :
    burnolFractionalPartDiv u = u ^ (-2 : ℝ) := by
  have hu0 : 0 < u := zero_lt_one.trans hu
  have hinv : 0 < u⁻¹ := inv_pos.mpr hu0
  have hinv1 : u⁻¹ < 1 := (inv_lt_one₀ hu0).2 hu
  rw [burnolFractionalPartDiv, fractionalPartKernel, one_div]
  rw [Int.fract_eq_self.mpr ⟨hinv.le, hinv1⟩]
  rw [div_eq_mul_inv, Real.rpow_neg (le_of_lt hu0), Real.rpow_two]
  field_simp

theorem integrableOn_burnolFractionalPartDiv_Ioi {t : ℝ} (ht : 0 < t) :
    IntegrableOn burnolFractionalPartDiv (Ioi t) := by
  by_cases ht1 : t ≤ 1
  · have hbounded : IntegrableOn burnolFractionalPartDiv (Ioc t 1) := by
      apply IntegrableOn.of_bound measure_Ioc_lt_top
      · exact measurable_burnolFractionalPartDiv.aestronglyMeasurable.restrict
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
        rw [Real.norm_eq_abs, abs_of_nonneg]
        · calc
            burnolFractionalPartDiv u ≤ 1 / u := by
              rw [burnolFractionalPartDiv, div_le_div_iff_of_pos_right (ht.trans_le hu.1.le)]
              exact (fractionalPartKernel_lt_one 1 u).le
            _ ≤ 1 / t := one_div_le_one_div_of_le ht hu.1.le
        · exact div_nonneg (fractionalPartKernel_nonneg 1 u) (ht.trans_le hu.1.le).le
    have htail : IntegrableOn burnolFractionalPartDiv (Ioi 1) := by
      refine (integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num)
        (c := (1 : ℝ)) zero_lt_one).congr_fun ?_ measurableSet_Ioi
      intro u hu
      exact (burnolFractionalPartDiv_eq_inv_sq hu).symm
    rw [show Ioi t = Ioc t 1 ∪ Ioi 1 by exact (Ioc_union_Ioi_eq_Ioi ht1).symm]
    exact hbounded.union htail
  · have ht1' : 1 < t := lt_of_not_ge ht1
    refine (integrableOn_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num)
      (c := t) ht).congr_fun ?_ measurableSet_Ioi
    intro u hu
    exact (burnolFractionalPartDiv_eq_inv_sq (ht1'.trans hu)).symm

theorem integral_burnolFractionalPartDiv_Ioi_eq_reciprocal_fract_integral
    {t : ℝ} (ht : 0 < t) :
    (∫ u : ℝ in Ioi t, burnolFractionalPartDiv u) =
      ∫ x : ℝ in (0 : ℝ)..t⁻¹, burnolFractDiv x := by
  have himage : (fun u : ℝ => u⁻¹) '' Ioi t = Ioo 0 t⁻¹ := by
    simpa only [image_inv_eq_inv] using inv_Ioi₀ ht
  have hchange := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun u hu => (hasDerivAt_inv (ne_of_gt (ht.trans hu))).hasDerivWithinAt)
    inv_injective.injOn burnolFractDiv
  rw [himage] at hchange
  rw [intervalIntegral.integral_of_le (inv_nonneg.mpr ht.le), integral_Ioc_eq_integral_Ioo]
  rw [hchange]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  have hu0 : 0 < u := ht.trans hu
  have hu_ne : u ≠ 0 := hu0.ne'
  simp only [burnolFractDiv, if_neg (inv_ne_zero hu_ne)]
  rw [burnolFractionalPartDiv, fractionalPartKernel, one_div]
  simp only [abs_neg, abs_inv, abs_pow, abs_of_pos hu0, smul_eq_mul]
  field_simp

theorem burnolA_eq_tailIntegral_sub_fractionalPart {t : ℝ} (ht : 0 < t) :
    burnolA t =
      (∫ u : ℝ in Ioi t, burnolFractionalPartDiv u) - fractionalPartKernel 1 t := by
  rw [integral_burnolFractionalPartDiv_Ioi_eq_reciprocal_fract_integral ht]
  exact burnolA_eq_reciprocal_fract_integral_sub_fractionalPart ht

theorem integral_burnolFractionalPartDiv_Ioi_one :
    (∫ u : ℝ in Ioi (1 : ℝ), burnolFractionalPartDiv u) = 1 := by
  calc
    (∫ u : ℝ in Ioi (1 : ℝ), burnolFractionalPartDiv u) =
        ∫ u : ℝ in Ioi (1 : ℝ), u ^ (-2 : ℝ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      exact burnolFractionalPartDiv_eq_inv_sq hu
    _ = 1 := by
      rw [integral_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num)
        (c := (1 : ℝ)) zero_lt_one]
      norm_num

theorem integral_burnolFractionalPartDiv_Ioi_nonneg {t : ℝ} (ht : 0 < t) :
    0 ≤ ∫ u : ℝ in Ioi t, burnolFractionalPartDiv u := by
  apply setIntegral_nonneg measurableSet_Ioi
  intro u hu
  exact div_nonneg (fractionalPartKernel_nonneg 1 u) (ht.trans hu).le

theorem integral_burnolFractionalPartDiv_Ioi_le_one_sub_log
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (∫ u : ℝ in Ioi t, burnolFractionalPartDiv u) ≤ 1 - Real.log t := by
  have hbounded : IntegrableOn burnolFractionalPartDiv (Ioc t 1) := by
    exact (integrableOn_burnolFractionalPartDiv_Ioi ht).mono_set
      (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi le_rfl))
  have htail : IntegrableOn burnolFractionalPartDiv (Ioi 1) :=
    integrableOn_burnolFractionalPartDiv_Ioi zero_lt_one
  have hsplit := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hbounded htail
  have hunion : Ioc t 1 ∪ Ioi 1 = Ioi t := Ioc_union_Ioi_eq_Ioi ht1
  rw [hunion] at hsplit
  have hinvInt : IntervalIntegrable (fun u : ℝ => 1 / u) volume t 1 := by
    simpa only [one_div] using intervalIntegrable_inv_iff.2
      (Or.inr (notMem_uIcc_of_lt ht zero_lt_one))
  have hbounded_le :
      (∫ u : ℝ in Ioc t 1, burnolFractionalPartDiv u) ≤ -Real.log t := by
    have hmono := setIntegral_mono_on hbounded hinvInt.1 measurableSet_Ioc (fun u hu => by
      rw [burnolFractionalPartDiv, div_le_div_iff_of_pos_right (ht.trans hu.1)]
      exact (fractionalPartKernel_lt_one 1 u).le)
    calc
      (∫ u : ℝ in Ioc t 1, burnolFractionalPartDiv u) ≤
          ∫ u : ℝ in Ioc t 1, 1 / u := hmono
      _ = ∫ u : ℝ in t..1, 1 / u := by
        rw [intervalIntegral.integral_of_le ht1]
      _ = -Real.log t := by
        rw [integral_one_div_of_pos ht zero_lt_one, one_div, Real.log_inv]
  rw [hsplit, integral_burnolFractionalPartDiv_Ioi_one]
  linarith

theorem abs_burnolA_le_two_add_abs_log {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    |burnolA t| ≤ 2 + |Real.log t| := by
  rw [burnolA_eq_tailIntegral_sub_fractionalPart ht]
  have htail0 := integral_burnolFractionalPartDiv_Ioi_nonneg ht
  have htail1 := integral_burnolFractionalPartDiv_Ioi_le_one_sub_log ht ht1
  have hfract0 := fractionalPartKernel_nonneg 1 t
  have hfract1 := (fractionalPartKernel_lt_one 1 t).le
  have hlog : Real.log t ≤ 0 := Real.log_nonpos ht.le ht1
  rw [abs_sub_comm]
  calc
    |fractionalPartKernel 1 t - ∫ u : ℝ in Ioi t, burnolFractionalPartDiv u| ≤
        |fractionalPartKernel 1 t| +
          |∫ u : ℝ in Ioi t, burnolFractionalPartDiv u| := abs_sub _ _
    _ = fractionalPartKernel 1 t +
          ∫ u : ℝ in Ioi t, burnolFractionalPartDiv u := by
      rw [abs_of_nonneg hfract0, abs_of_nonneg htail0]
    _ ≤ 2 + |Real.log t| := by
      rw [abs_of_nonpos hlog]
      linarith

/-- Burnol's explicit source function belongs to `L²(0, infinity)`. -/
theorem burnolA_memLp_two_positiveHalfLine :
    MemLp burnolA (2 : ℝ≥0∞)
      (volume.restrict (Ioi (0 : ℝ))) := by
  rw [memLp_two_iff_integrable_sq measurable_burnolA.aestronglyMeasurable]
  change IntegrableOn (fun t : ℝ => burnolA t ^ 2) (Ioi (0 : ℝ)) volume
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  apply IntegrableOn.union
  · have hbase : IntegrableOn (fun t : ℝ => t ^ (-1 / 2 : ℝ)) (Ioc 0 1) volume := by
      rw [integrableOn_Ioc_iff_integrableOn_Ioo]
      exact (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 (by norm_num)
    refine Integrable.mono' (hbase.const_mul (36 : ℝ)) ?_ ?_
    · exact (measurable_burnolA.pow_const 2).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : 0 < t := ht.1
      have ht1 : t ≤ 1 := ht.2
      have hquarter : 0 < t ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos ht0 _
      have hlogMul :=
        Real.abs_log_mul_self_rpow_lt t (1 / 4 : ℝ) ht0 ht1 (by norm_num)
      rw [abs_mul, abs_of_pos hquarter] at hlogMul
      have hlog : |Real.log t| < 4 * t ^ (-1 / 4 : ℝ) := by
        calc
          |Real.log t| < 4 / t ^ (1 / 4 : ℝ) := by
            apply (lt_div_iff₀ hquarter).2
            simpa using hlogMul
          _ = 4 * t ^ (-1 / 4 : ℝ) := by
            rw [show (-1 / 4 : ℝ) = -(1 / 4 : ℝ) by norm_num,
              Real.rpow_neg ht0.le, div_eq_mul_inv]
      have hpower : 1 ≤ t ^ (-1 / 4 : ℝ) :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht0 ht1 (by norm_num)
      have hA := abs_burnolA_le_two_add_abs_log ht0 ht1
      have hAbound : |burnolA t| ≤ 6 * t ^ (-1 / 4 : ℝ) := by
        nlinarith
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
      calc
        |burnolA t| ^ 2 ≤ (6 * t ^ (-1 / 4 : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hAbound 2
        _ = 36 * t ^ (-1 / 2 : ℝ) := by
          rw [mul_pow, show (6 : ℝ) ^ 2 = 36 by norm_num,
            ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
          norm_num
  · refine integrableOn_zero.congr_fun ?_ measurableSet_Ioi
    intro t ht
    simp [burnolA_eq_zero_of_one_lt ht]

/-- Burnol's explicit source function as a real `L²(0, infinity)` element. -/
noncomputable def burnolAL2 : positiveHalfLineL2 :=
  burnolA_memLp_two_positiveHalfLine.toLp burnolA

theorem burnolAL2_coeFn :
    burnolAL2 =ᵐ[volume.restrict (Ioi (0 : ℝ))] burnolA := by
  exact MemLp.coeFn_toLp burnolA_memLp_two_positiveHalfLine

/-- Burnol's explicit source function as a complex `L²(0, infinity)` element. -/
noncomputable def burnolComplexAL2 : positiveHalfLineComplexL2 :=
  baezDuarteOfRealLp burnolAL2

theorem burnolComplexAL2_coeFn :
    burnolComplexAL2 =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun t => (burnolA t : ℂ) := by
  change baezDuarteOfRealLp burnolAL2 =ᵐ[volume.restrict (Ioi (0 : ℝ))]
    fun t => (burnolA t : ℂ)
  filter_upwards [baezDuarteOfRealLp_coeFn burnolAL2, burnolAL2_coeFn]
    with t hcomplex hreal
  exact hcomplex.trans (congrArg Complex.ofReal hreal)

/-- The complex Hardy tail appearing in Burnol's Mellin calculation. -/
noncomputable def burnolComplexFractionalPartTail (t : ℝ) : ℂ :=
  ∫ u : ℝ in Ioi t, (burnolFractionalPartDiv u : ℂ)

theorem burnolComplexFractionalPartTail_eq_ofReal (t : ℝ) :
    burnolComplexFractionalPartTail t =
      (∫ u : ℝ in Ioi t, burnolFractionalPartDiv u : ℝ) := by
  exact integral_complex_ofReal

/-- The open triangle on which the Fubini kernel for the Hardy tail is supported. -/
def burnolMellinTriangle : Set (ℝ × ℝ) :=
  {p | 0 < p.1 ∧ p.1 < p.2}

theorem measurableSet_burnolMellinTriangle : MeasurableSet burnolMellinTriangle := by
  exact (measurableSet_lt measurable_const measurable_fst).inter
    (measurableSet_lt measurable_fst measurable_snd)

/-- The two-variable kernel used to interchange the Mellin and Hardy-tail integrals. -/
noncomputable def burnolMellinTriangleKernel (s : ℂ) (p : ℝ × ℝ) : ℂ :=
  burnolMellinTriangle.indicator
    (fun q => (q.1 : ℂ) ^ (s - 1) * (burnolFractionalPartDiv q.2 : ℂ)) p

theorem measurable_burnolMellinTriangleKernel (s : ℂ) :
    Measurable (burnolMellinTriangleKernel s) := by
  have hpow : Measurable (fun t : ℝ => (t : ℂ) ^ (s - 1)) :=
    measurable_of_continuousOn_compl_singleton (0 : ℝ)
      (continuousOn_of_forall_continuousAt fun t ht =>
        Complex.continuousAt_ofReal_cpow_const t (s - 1) (Or.inr ht))
  exact ((hpow.comp measurable_fst).mul
    (Complex.measurable_ofReal.comp
      (measurable_burnolFractionalPartDiv.comp measurable_snd))).indicator
        measurableSet_burnolMellinTriangle

theorem integrable_burnolMellinTriangleKernel_slice
    (s : ℂ) (hs0 : 0 < s.re) (u : ℝ) :
    Integrable (fun t : ℝ => burnolMellinTriangleKernel s (t, u)) := by
  by_cases hu : 0 < u
  · have hpow : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1)) (Ioo 0 u) := by
      rw [← integrableOn_Ioc_iff_integrableOn_Ioo]
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hu.le]
      exact intervalIntegral.intervalIntegrable_cpow' (by
        simp only [Complex.sub_re, Complex.one_re]
        linarith)
    have hlocal : IntegrableOn
        (fun t : ℝ => (t : ℂ) ^ (s - 1) * (burnolFractionalPartDiv u : ℂ))
        (Ioo 0 u) := hpow.mul_const _
    have hindicator := hlocal.integrable_indicator measurableSet_Ioo
    refine hindicator.congr (ae_of_all _ fun t => ?_)
    by_cases ht : t ∈ Ioo (0 : ℝ) u
    · have htri : (t, u) ∈ burnolMellinTriangle := by
        exact ht
      simp [burnolMellinTriangleKernel, htri, ht]
    · have htri : (t, u) ∉ burnolMellinTriangle := by
        simpa [burnolMellinTriangle, Set.mem_Ioo] using ht
      simp [burnolMellinTriangleKernel, htri, ht]
  · have hzero : Integrable (fun _ : ℝ => (0 : ℂ)) := integrable_zero _ _ volume
    refine hzero.congr (ae_of_all _ fun t => ?_)
    have hnot : (t, u) ∉ burnolMellinTriangle := by
      intro ht
      exact hu (ht.1.trans ht.2)
    simp [burnolMellinTriangleKernel, hnot]

theorem integral_norm_burnolMellinTriangleKernel
    (s : ℂ) (hs0 : 0 < s.re) (u : ℝ) :
    (∫ t : ℝ, ‖burnolMellinTriangleKernel s (t, u)‖) =
      if 0 < u then
        (1 / s.re) * u ^ (s.re - 1) * fractionalPartKernel 1 u
      else 0 := by
  split_ifs with hu
  · calc
      (∫ t : ℝ, ‖burnolMellinTriangleKernel s (t, u)‖) =
          ∫ t : ℝ in Ioo 0 u,
            ‖(t : ℂ) ^ (s - 1) * (burnolFractionalPartDiv u : ℂ)‖ := by
        rw [← integral_indicator measurableSet_Ioo]
        apply integral_congr_ae
        exact ae_of_all _ fun t => by
          by_cases ht : t ∈ Ioo (0 : ℝ) u
          · simp [burnolMellinTriangleKernel, burnolMellinTriangle, ht, ht.1, ht.2]
          · have hnot : (t, u) ∉ burnolMellinTriangle := by
              simpa [burnolMellinTriangle, Set.mem_Ioo] using ht
            simp [burnolMellinTriangleKernel, hnot, ht]
      _ = ∫ t : ℝ in Ioo 0 u,
            t ^ (s.re - 1) * burnolFractionalPartDiv u := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro t ht
        have hdiv : 0 ≤ burnolFractionalPartDiv u :=
          div_nonneg (fractionalPartKernel_nonneg 1 u) hu.le
        change ‖(t : ℂ) ^ (s - 1) * (burnolFractionalPartDiv u : ℂ)‖ =
          t ^ (s.re - 1) * burnolFractionalPartDiv u
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht.1]
        simp [abs_of_nonneg hdiv]
      _ = (∫ t : ℝ in Ioo 0 u, t ^ (s.re - 1)) *
            burnolFractionalPartDiv u := by
        rw [integral_mul_const]
      _ = (u ^ s.re / s.re) * burnolFractionalPartDiv u := by
        congr 1
        rw [← integral_Ioc_eq_integral_Ioo,
          ← intervalIntegral.integral_of_le hu.le,
          integral_rpow (Or.inl (by linarith))]
        rw [show s.re - 1 + 1 = s.re by ring, Real.zero_rpow hs0.ne']
        simp
      _ = (1 / s.re) * u ^ (s.re - 1) * fractionalPartKernel 1 u := by
        rw [burnolFractionalPartDiv, Real.rpow_sub_one hu.ne']
        field_simp [hs0.ne', hu.ne']
  · have hzero : ∀ t : ℝ, burnolMellinTriangleKernel s (t, u) = 0 := by
      intro t
      have hnot : (t, u) ∉ burnolMellinTriangle := by
        intro ht
        exact hu (ht.1.trans ht.2)
      simp [burnolMellinTriangleKernel, hnot]
    simp [hzero]

theorem integrable_burnolMellinTriangleKernel
    (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    Integrable (burnolMellinTriangleKernel s) (volume.prod volume) := by
  have hMellin := hasMellin_fractionalPartKernel_one s hs0 hs1
  have hkernelMeas : AEStronglyMeasurable
      (fun u : ℝ => (fractionalPartKernel 1 u : ℂ))
      (volume.restrict (Ioi (0 : ℝ))) :=
    (Complex.measurable_ofReal.comp
      (measurable_fractionalPartKernel 1)).aestronglyMeasurable
  have hweightNorm : IntegrableOn
      (fun u : ℝ => u ^ (s.re - 1) * ‖(fractionalPartKernel 1 u : ℂ)‖)
      (Ioi (0 : ℝ)) :=
    (mellin_convergent_iff_norm (T := Ioi (0 : ℝ))
      Subset.rfl measurableSet_Ioi hkernelMeas).mp hMellin.1
  have hweight : IntegrableOn
      (fun u : ℝ => u ^ (s.re - 1) * fractionalPartKernel 1 u)
      (Ioi (0 : ℝ)) := by
    refine hweightNorm.congr_fun ?_ measurableSet_Ioi
    intro u _hu
    simp [abs_of_nonneg (fractionalPartKernel_nonneg 1 u)]
  have hscaledWeight : IntegrableOn
      (fun u : ℝ => (1 / s.re) *
        (u ^ (s.re - 1) * fractionalPartKernel 1 u))
      (Ioi (0 : ℝ)) := by
    change Integrable
      (fun u : ℝ => (1 / s.re) *
        (u ^ (s.re - 1) * fractionalPartKernel 1 u))
      (volume.restrict (Ioi (0 : ℝ)))
    exact hweight.const_mul (1 / s.re)
  have houterIndicator : Integrable
      ((Ioi (0 : ℝ)).indicator
        (fun u : ℝ => (1 / s.re) *
          (u ^ (s.re - 1) * fractionalPartKernel 1 u))) :=
    hscaledWeight.integrable_indicator measurableSet_Ioi
  have houter : Integrable
      (fun u : ℝ => ∫ t : ℝ, ‖burnolMellinTriangleKernel s (t, u)‖) := by
    refine houterIndicator.congr (ae_of_all _ fun u => ?_)
    change (Ioi (0 : ℝ)).indicator
      (fun u : ℝ => (1 / s.re) *
        (u ^ (s.re - 1) * fractionalPartKernel 1 u)) u =
        ∫ t : ℝ, ‖burnolMellinTriangleKernel s (t, u)‖
    rw [integral_norm_burnolMellinTriangleKernel s hs0 u]
    by_cases hu : 0 < u
    · simp [hu, mul_assoc]
    · simp [hu]
  refine (integrable_prod_iff'
    (measurable_burnolMellinTriangleKernel s).aestronglyMeasurable).2 ?_
  exact ⟨ae_of_all _ (integrable_burnolMellinTriangleKernel_slice s hs0), houter⟩

theorem integral_burnolMellinTriangleKernel_slice
    (s : ℂ) (hs0 : 0 < s.re) (u : ℝ) :
    (∫ t : ℝ, burnolMellinTriangleKernel s (t, u)) =
      if 0 < u then
        (1 / s) * (u : ℂ) ^ (s - 1) * (fractionalPartKernel 1 u : ℂ)
      else 0 := by
  have hsne : s ≠ 0 := by
    intro hs
    rw [hs, Complex.zero_re] at hs0
    exact lt_irrefl 0 hs0
  split_ifs with hu
  · calc
      (∫ t : ℝ, burnolMellinTriangleKernel s (t, u)) =
          ∫ t : ℝ in Ioo 0 u,
            (t : ℂ) ^ (s - 1) * (burnolFractionalPartDiv u : ℂ) := by
        rw [← integral_indicator measurableSet_Ioo]
        apply integral_congr_ae
        exact ae_of_all _ fun t => by
          by_cases ht : t ∈ Ioo (0 : ℝ) u
          · have htri : (t, u) ∈ burnolMellinTriangle := by exact ht
            simp [burnolMellinTriangleKernel, htri, ht]
          · have htri : (t, u) ∉ burnolMellinTriangle := by
              simpa [burnolMellinTriangle, Set.mem_Ioo] using ht
            simp [burnolMellinTriangleKernel, htri, ht]
      _ = (∫ t : ℝ in Ioo 0 u, (t : ℂ) ^ (s - 1)) *
            (burnolFractionalPartDiv u : ℂ) := by
        rw [integral_mul_const]
      _ = ((u : ℂ) ^ s / s) * (burnolFractionalPartDiv u : ℂ) := by
        congr 1
        rw [← integral_Ioc_eq_integral_Ioo,
          ← intervalIntegral.integral_of_le hu.le,
          integral_cpow (Or.inl (by
            simp only [Complex.sub_re, Complex.one_re]
            linarith))]
        rw [show s - 1 + 1 = s by ring]
        simp [Complex.zero_cpow hsne]
      _ = (1 / s) * (u : ℂ) ^ (s - 1) * (fractionalPartKernel 1 u : ℂ) := by
        rw [burnolFractionalPartDiv,
          Complex.cpow_sub s 1 (Complex.ofReal_ne_zero.mpr hu.ne'), Complex.cpow_one]
        push_cast
        field_simp [hsne, hu.ne']
  · have hzero : ∀ t : ℝ, burnolMellinTriangleKernel s (t, u) = 0 := by
      intro t
      have hnot : (t, u) ∉ burnolMellinTriangle := by
        intro ht
        exact hu (ht.1.trans ht.2)
      simp [burnolMellinTriangleKernel, hnot]
    simp [hzero]

theorem integral_burnolMellinTriangleKernel_tail
    (s : ℂ) (t : ℝ) :
    (∫ u : ℝ, burnolMellinTriangleKernel s (t, u)) =
      if 0 < t then
        (t : ℂ) ^ (s - 1) * burnolComplexFractionalPartTail t
      else 0 := by
  split_ifs with ht
  · calc
      (∫ u : ℝ, burnolMellinTriangleKernel s (t, u)) =
          ∫ u : ℝ in Ioi t,
            (t : ℂ) ^ (s - 1) * (burnolFractionalPartDiv u : ℂ) := by
        rw [← integral_indicator measurableSet_Ioi]
        apply integral_congr_ae
        exact ae_of_all _ fun u => by
          by_cases hu : u ∈ Ioi t
          · have htri : (t, u) ∈ burnolMellinTriangle := ⟨ht, hu⟩
            simp [burnolMellinTriangleKernel, htri, hu]
          · have htri : (t, u) ∉ burnolMellinTriangle := by
              intro h
              exact hu h.2
            simp [burnolMellinTriangleKernel, htri, hu]
      _ = (t : ℂ) ^ (s - 1) *
            (∫ u : ℝ in Ioi t, (burnolFractionalPartDiv u : ℂ)) := by
        rw [integral_const_mul]
      _ = (t : ℂ) ^ (s - 1) * burnolComplexFractionalPartTail t := rfl
  · have hzero : ∀ u : ℝ, burnolMellinTriangleKernel s (t, u) = 0 := by
      intro u
      have hnot : (t, u) ∉ burnolMellinTriangle := by
        intro h
        exact ht h.1
      simp [burnolMellinTriangleKernel, hnot]
    simp [hzero]

theorem mellinConvergent_burnolComplexFractionalPartTail
    (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    MellinConvergent burnolComplexFractionalPartTail s := by
  have hleft :=
    (integrable_burnolMellinTriangleKernel s hs0 hs1).integral_prod_left
  have hindicator : Integrable
      ((Ioi (0 : ℝ)).indicator
        (fun t : ℝ => (t : ℂ) ^ (s - 1) * burnolComplexFractionalPartTail t)) := by
    refine hleft.congr (ae_of_all _ fun t => ?_)
    change (∫ u : ℝ, burnolMellinTriangleKernel s (t, u)) =
      (Ioi (0 : ℝ)).indicator
        (fun t : ℝ => (t : ℂ) ^ (s - 1) * burnolComplexFractionalPartTail t) t
    rw [integral_burnolMellinTriangleKernel_tail s t]
    by_cases ht : 0 < t
    · simp [ht]
    · simp [ht]
  rw [MellinConvergent]
  simpa only [smul_eq_mul] using
    (integrable_indicator_iff measurableSet_Ioi).mp hindicator

theorem mellin_burnolComplexFractionalPartTail_eq
    (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    mellin burnolComplexFractionalPartTail s =
      (1 / s) * mellin (fun u : ℝ => (fractionalPartKernel 1 u : ℂ)) s := by
  have hprod := integrable_burnolMellinTriangleKernel s hs0 hs1
  have hprodCurried : Integrable
      (Function.uncurry (fun t u : ℝ => burnolMellinTriangleKernel s (t, u)))
      (volume.prod volume) := by
    refine hprod.congr (ae_of_all _ fun p => ?_)
    rcases p with ⟨t, u⟩
    rfl
  have hswap := integral_integral_swap (μ := volume) (ν := volume) hprodCurried
  have hleft :
      (∫ t : ℝ, ∫ u : ℝ, burnolMellinTriangleKernel s (t, u)) =
        mellin burnolComplexFractionalPartTail s := by
    rw [mellin, ← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    exact ae_of_all _ fun t => by
      change (∫ u : ℝ, burnolMellinTriangleKernel s (t, u)) =
        (Ioi (0 : ℝ)).indicator
          (fun t : ℝ =>
            (t : ℂ) ^ (s - 1) * burnolComplexFractionalPartTail t) t
      rw [integral_burnolMellinTriangleKernel_tail s t]
      by_cases ht : 0 < t
      · simp [ht]
      · simp [ht]
  have hright :
      (∫ u : ℝ, ∫ t : ℝ, burnolMellinTriangleKernel s (t, u)) =
        (1 / s) * mellin (fun u : ℝ => (fractionalPartKernel 1 u : ℂ)) s := by
    calc
      (∫ u : ℝ, ∫ t : ℝ, burnolMellinTriangleKernel s (t, u)) =
          ∫ u : ℝ in Ioi (0 : ℝ),
            (1 / s) * (u : ℂ) ^ (s - 1) * (fractionalPartKernel 1 u : ℂ) := by
        rw [← integral_indicator measurableSet_Ioi]
        apply integral_congr_ae
        exact ae_of_all _ fun u => by
          change (∫ t : ℝ, burnolMellinTriangleKernel s (t, u)) =
            (Ioi (0 : ℝ)).indicator
              (fun u : ℝ =>
                (1 / s) * (u : ℂ) ^ (s - 1) * (fractionalPartKernel 1 u : ℂ)) u
          rw [integral_burnolMellinTriangleKernel_slice s hs0 u]
          by_cases hu : 0 < u
          · simp [hu]
          · simp [hu]
      _ = (1 / s) *
          (∫ u : ℝ in Ioi (0 : ℝ),
            (u : ℂ) ^ (s - 1) * (fractionalPartKernel 1 u : ℂ)) := by
        simp_rw [mul_assoc]
        rw [integral_const_mul]
      _ = (1 / s) * mellin
          (fun u : ℝ => (fractionalPartKernel 1 u : ℂ)) s := by
        rfl
  calc
    mellin burnolComplexFractionalPartTail s =
        ∫ t : ℝ, ∫ u : ℝ, burnolMellinTriangleKernel s (t, u) := hleft.symm
    _ = ∫ u : ℝ, ∫ t : ℝ, burnolMellinTriangleKernel s (t, u) := hswap
    _ = (1 / s) * mellin
        (fun u : ℝ => (fractionalPartKernel 1 u : ℂ)) s := hright

theorem hasMellin_burnolComplexFractionalPartTail
    (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    HasMellin burnolComplexFractionalPartTail s
      ((1 / s) * (-riemannZeta s / s)) := by
  refine ⟨mellinConvergent_burnolComplexFractionalPartTail s hs0 hs1, ?_⟩
  rw [mellin_burnolComplexFractionalPartTail_eq s hs0 hs1,
    (hasMellin_fractionalPartKernel_one s hs0 hs1).2]

theorem burnolA_complex_eq_tail_sub_fractionalPart
    {t : ℝ} (ht : 0 < t) :
    (burnolA t : ℂ) = burnolComplexFractionalPartTail t -
      (fractionalPartKernel 1 t : ℂ) := by
  have hreal := burnolA_eq_tailIntegral_sub_fractionalPart ht
  have hcomplex := congrArg Complex.ofReal hreal
  simpa [burnolComplexFractionalPartTail_eq_ofReal] using hcomplex

/-- Burnol's explicit source function has Mellin transform
`Z(s) = (s - 1) * zeta(s) / s^2` on the critical strip. -/
theorem hasMellin_burnolA
    (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    HasMellin (fun t : ℝ => (burnolA t : ℂ)) s
      ((s - 1) * riemannZeta s / s ^ 2) := by
  have hsne : s ≠ 0 := by
    intro hs
    rw [hs, Complex.zero_re] at hs0
    exact lt_irrefl 0 hs0
  have htail := hasMellin_burnolComplexFractionalPartTail s hs0 hs1
  have hkernel := hasMellin_fractionalPartKernel_one s hs0 hs1
  have hsub := hasMellin_sub htail.1 hkernel.1
  have hsubValue : HasMellin
      (fun t : ℝ => burnolComplexFractionalPartTail t -
        (fractionalPartKernel 1 t : ℂ)) s
      ((1 / s) * (-riemannZeta s / s) - (-riemannZeta s / s)) := by
    refine ⟨hsub.1, ?_⟩
    rw [hsub.2, htail.2, hkernel.2]
  constructor
  · rw [MellinConvergent]
    refine hsubValue.1.congr_fun ?_ measurableSet_Ioi
    intro t ht
    simp only [smul_eq_mul]
    rw [burnolA_complex_eq_tail_sub_fractionalPart ht]
  · rw [mellin]
    calc
      (∫ t : ℝ in Ioi (0 : ℝ),
          (t : ℂ) ^ (s - 1) * (burnolA t : ℂ)) =
          ∫ t : ℝ in Ioi (0 : ℝ),
            (t : ℂ) ^ (s - 1) *
              (burnolComplexFractionalPartTail t -
                (fractionalPartKernel 1 t : ℂ)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        change (t : ℂ) ^ (s - 1) * (burnolA t : ℂ) =
          (t : ℂ) ^ (s - 1) *
            (burnolComplexFractionalPartTail t - (fractionalPartKernel 1 t : ℂ))
        rw [burnolA_complex_eq_tail_sub_fractionalPart ht]
      _ = mellin
          (fun t : ℝ => burnolComplexFractionalPartTail t -
            (fractionalPartKernel 1 t : ℂ)) s := by
        rfl
      _ = (1 / s) * (-riemannZeta s / s) - (-riemannZeta s / s) :=
        hsubValue.2
      _ = (s - 1) * riemannZeta s / s ^ 2 := by
        field_simp [hsne]
        ring

end LeanLab.Riemann
