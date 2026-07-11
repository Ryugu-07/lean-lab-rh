import LeanLab.Riemann.BaezDuarteMellin
import LeanLab.Riemann.LiScaffold
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

set_option linter.style.header false

/-!
# Reverse implication of the strong Baez-Duarte criterion

This file formalizes the Mellin zero obstruction for the M0-aligned positive-natural closure
criterion in `L²(0, infinity)`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LeanLab.Riemann

/-- A finite real linear combination of the positive-natural kernels, viewed as complex-valued. -/
def baezDuarteFiniteKernelSum
    (c : baezDuartePositiveNatIndex →₀ ℝ) (x : ℝ) : ℂ :=
  c.sum fun n r => (r : ℂ) * fractionalPartKernel (((n : ℕ) : ℝ)⁻¹) x

theorem baezDuarteFiniteKernelSum_ofReal
    (c : baezDuartePositiveNatIndex →₀ ℝ) (x : ℝ) :
    baezDuarteFiniteKernelSum c x =
      (c.sum fun n r => r * fractionalPartKernel (((n : ℕ) : ℝ)⁻¹) x : ℝ) := by
  classical
  simp [baezDuarteFiniteKernelSum, Finsupp.sum]

/-- At a zeta zero in the critical strip, every finite natural-kernel combination has zero
Mellin transform. -/
theorem hasMellin_baezDuarteFiniteKernelSum_zero
    (c : baezDuartePositiveNatIndex →₀ ℝ) (s : ℂ)
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (hz : riemannZeta s = 0) :
    HasMellin (baezDuarteFiniteKernelSum c) s 0 := by
  classical
  have hterm : ∀ n : baezDuartePositiveNatIndex,
      HasMellin
        (fun x : ℝ => (c n : ℂ) *
          (fractionalPartKernel (((n : ℕ) : ℝ)⁻¹) x : ℂ)) s 0 := by
    intro n
    have hk := hasMellin_baezDuarteKernel n s hs0 hs1
    have hsmul := hasMellin_const_smul hk.1 (c n : ℂ)
    rw [hk.2, hz] at hsmul
    simpa [smul_eq_mul] using hsmul
  have hsum : HasMellin
      (fun x : ℝ => ∑ n ∈ c.support,
        (c n : ℂ) * (fractionalPartKernel (((n : ℕ) : ℝ)⁻¹) x : ℂ)) s 0 := by
    induction c.support using Finset.induction_on with
    | empty =>
        simp [HasMellin, MellinConvergent, mellin]
    | @insert n u hn ih =>
        have hnM := hterm n
        have hadd := hasMellin_add hnM.1 ih.1
        simpa [hn, hnM.2, ih.2] using hadd
  convert hsum using 1
  funext x
  simp [baezDuarteFiniteKernelSum, Finsupp.sum]

/-- The local Mellin weight belongs to `L²(0,1)` precisely in the range needed by the reverse
criterion. -/
theorem mellinWeight_memLp_two_unitInterval
    (s : ℂ) (hs : 1 / 2 < s.re) :
    MemLp (fun x : ℝ => (x : ℂ) ^ (s - 1)) (2 : ℝ≥0∞)
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
  rw [memLp_two_iff_integrable_sq_norm]
  · have hpow : IntegrableOn (fun x : ℝ => x ^ (2 * (s.re - 1))) (Ioo (0 : ℝ) 1) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 (by linarith)
    exact hpow.congr_fun (fun x hx => by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx.1, Complex.sub_re, Complex.one_re,
        ← Real.rpow_mul_natCast hx.1.le]
      ring_nf) measurableSet_Ioo
  · exact ContinuousOn.aestronglyMeasurable
      (fun x hx => (Complex.continuousAt_ofReal_cpow_const x (s - 1)
        (Or.inr hx.1.ne')).continuousWithinAt) measurableSet_Ioo

/-- The local complex-valued approximation error on `(0,1)`. -/
def baezDuarteLocalMellinError
    (c : baezDuartePositiveNatIndex →₀ ℝ) (x : ℝ) : ℂ :=
  1 - baezDuarteFiniteKernelSum c x

theorem baezDuarteLocalMellinError_memLp_two
    (c : baezDuartePositiveNatIndex →₀ ℝ) :
    MemLp (baezDuarteLocalMellinError c) (2 : ℝ≥0∞)
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
  classical
  have hone : MemLp (fun _ : ℝ => (1 : ℂ)) (2 : ℝ≥0∞)
      (volume.restrict (Ioo (0 : ℝ) 1)) :=
    unitIntervalOne_memLp_two_unitInterval.ofReal
  have hsum : MemLp (baezDuarteFiniteKernelSum c) (2 : ℝ≥0∞)
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
    change MemLp
      (fun x : ℝ => ∑ n ∈ c.support,
        (c n : ℂ) * fractionalPartKernel (((n : ℕ) : ℝ)⁻¹) x)
      (2 : ℝ≥0∞) (volume.restrict (Ioo (0 : ℝ) 1))
    apply memLp_finsetSum
    intro n _hn
    have hreal :=
      (fractionalPartKernel_memLp_two_unitInterval (((n : ℕ) : ℝ)⁻¹)).const_smul (c n)
    have hcplx : MemLp
        (fun x : ℝ => ((c n * fractionalPartKernel (((n : ℕ) : ℝ)⁻¹) x : ℝ) : ℂ))
        (2 : ℝ≥0∞) (volume.restrict (Ioo (0 : ℝ) 1)) := hreal.ofReal
    simpa using hcplx
  exact hone.sub hsum

theorem baezDuarteLocalMellinError_eq_ofReal
    (c : baezDuartePositiveNatIndex →₀ ℝ) (x : ℝ) :
    baezDuarteLocalMellinError c x =
      ((1 - c.sum fun n r =>
        r * fractionalPartKernel (((n : ℕ) : ℝ)⁻¹) x : ℝ) : ℂ) := by
  rw [baezDuarteLocalMellinError, baezDuarteFiniteKernelSum_ofReal]
  push_cast
  rfl

theorem integral_norm_baezDuarteLocalMellinError_sq
    (c : baezDuartePositiveNatIndex →₀ ℝ) :
    (∫ x : ℝ, ‖baezDuarteLocalMellinError c x‖ ^ 2 ∂
        (volume.restrict (Ioo (0 : ℝ) 1))) =
      baezDuarteUnitIntervalError c := by
  rw [baezDuarteUnitIntervalError]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  change ‖baezDuarteLocalMellinError c x‖ ^ 2 =
    (1 - c.sum fun n r => r * fractionalPartKernel (((n : ℕ) : ℝ)⁻¹) x) *
      (1 - c.sum fun n r => r * fractionalPartKernel (((n : ℕ) : ℝ)⁻¹) x)
  rw [baezDuarteLocalMellinError_eq_ofReal, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [pow_two]

/-- Cauchy-Schwarz bounds the local Mellin error by the square root of the source's unit-interval
quadratic error. -/
theorem norm_integral_baezDuarteLocalMellinError_le
    (c : baezDuartePositiveNatIndex →₀ ℝ) (s : ℂ) (hs : 1 / 2 < s.re) :
    ‖∫ x : ℝ,
        (x : ℂ) ^ (s - 1) * baezDuarteLocalMellinError c x ∂
          (volume.restrict (Ioo (0 : ℝ) 1))‖ ≤
      (∫ x : ℝ, ‖(x : ℂ) ^ (s - 1)‖ ^ (2 : ℝ) ∂
          (volume.restrict (Ioo (0 : ℝ) 1))) ^ (1 / (2 : ℝ)) *
        (baezDuarteUnitIntervalError c) ^ (1 / (2 : ℝ)) := by
  let μ := volume.restrict (Ioo (0 : ℝ) 1)
  have hw := mellinWeight_memLp_two_unitInterval s hs
  have he := baezDuarteLocalMellinError_memLp_two c
  have hw' : MemLp (fun x : ℝ => (x : ℂ) ^ (s - 1))
      (ENNReal.ofReal (2 : ℝ)) μ := by simpa [μ] using hw
  have he' : MemLp (baezDuarteLocalMellinError c)
      (ENNReal.ofReal (2 : ℝ)) μ := by simpa [μ] using he
  have hint : Integrable
      (fun x : ℝ => (x : ℂ) ^ (s - 1) * baezDuarteLocalMellinError c x) μ :=
    hw.integrable_mul he
  calc
    ‖∫ x : ℝ, (x : ℂ) ^ (s - 1) * baezDuarteLocalMellinError c x ∂μ‖ ≤
        ∫ x : ℝ, ‖(x : ℂ) ^ (s - 1) * baezDuarteLocalMellinError c x‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ = ∫ x : ℝ,
        ‖(x : ℂ) ^ (s - 1)‖ * ‖baezDuarteLocalMellinError c x‖ ∂μ := by
      congr 1
      funext x
      rw [norm_mul]
    _ ≤ (∫ x : ℝ, ‖(x : ℂ) ^ (s - 1)‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
        (∫ x : ℝ, ‖baezDuarteLocalMellinError c x‖ ^ (2 : ℝ) ∂μ) ^
          (1 / (2 : ℝ)) := by
      exact integral_mul_norm_le_Lp_mul_Lq (Real.HolderConjugate.two_two) hw' he'
    _ = (∫ x : ℝ, ‖(x : ℂ) ^ (s - 1)‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
        (baezDuarteUnitIntervalError c) ^ (1 / (2 : ℝ)) := by
      have herr : (∫ x : ℝ, ‖baezDuarteLocalMellinError c x‖ ^ (2 : ℝ) ∂μ) =
          baezDuarteUnitIntervalError c := by
        simpa only [Real.rpow_two] using integral_norm_baezDuarteLocalMellinError_sq c
      rw [herr]

theorem integral_Ioo_cpow_sub_one
    (s : ℂ) (hs0 : 0 < s.re) :
    (∫ x : ℝ in Ioo (0 : ℝ) 1, (x : ℂ) ^ (s - 1)) = s⁻¹ := by
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one]
  rw [integral_cpow (Or.inl (by
    simp only [Complex.sub_re, Complex.one_re]
    linarith))]
  have hs_ne : s ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hs0
    exact lt_irrefl 0 hs0
  rw [Complex.ofReal_one, Complex.ofReal_zero,
    show (s - 1) + 1 = s by ring, Complex.one_cpow, Complex.zero_cpow hs_ne,
    sub_zero]
  rw [div_eq_mul_inv, one_mul]

theorem integral_Ioi_baezDuarteFiniteKernelSum
    (c : baezDuartePositiveNatIndex →₀ ℝ) (s : ℂ) (hs1 : s.re < 1) :
    (∫ x : ℝ in Ioi (1 : ℝ),
        (x : ℂ) ^ (s - 1) * baezDuarteFiniteKernelSum c x) =
      (baezDuarteReciprocalMoment c : ℂ) / (1 - s) := by
  let m : ℝ := baezDuarteReciprocalMoment c
  have hpow : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 2)) (Ioi (1 : ℝ)) :=
    integrableOn_Ioi_cpow_of_lt (by
      change s.re - 2 < -1
      linarith) zero_lt_one
  calc
    (∫ x : ℝ in Ioi (1 : ℝ),
        (x : ℂ) ^ (s - 1) * baezDuarteFiniteKernelSum c x) =
        ∫ x : ℝ in Ioi (1 : ℝ), (m : ℂ) * (x : ℂ) ^ (s - 2) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
      rw [baezDuarteFiniteKernelSum_ofReal,
        baezDuarte_finsupp_sum_eq_reciprocalMoment_div_of_one_lt c hx]
      dsimp only [m]
      push_cast
      rw [div_eq_mul_inv, ← Complex.cpow_neg_one]
      have hxne : (x : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_trans zero_lt_one hx))
      calc
        (x : ℂ) ^ (s - 1) * ((baezDuarteReciprocalMoment c : ℂ) *
            (x : ℂ) ^ (-1 : ℂ)) =
            (baezDuarteReciprocalMoment c : ℂ) *
              ((x : ℂ) ^ (s - 1) * (x : ℂ) ^ (-1 : ℂ)) := by ring
        _ = (baezDuarteReciprocalMoment c : ℂ) *
              (x : ℂ) ^ ((s - 1) + (-1 : ℂ)) := by rw [← Complex.cpow_add _ _ hxne]
        _ = (baezDuarteReciprocalMoment c : ℂ) * (x : ℂ) ^ (s - 2) := by
          congr 2
          ring
    _ = (m : ℂ) * ∫ x : ℝ in Ioi (1 : ℝ), (x : ℂ) ^ (s - 2) := by
      rw [integral_const_mul]
    _ = (m : ℂ) * (-((1 : ℂ) ^ ((s - 2) + 1)) / ((s - 2) + 1)) := by
      rw [integral_Ioi_cpow_of_lt (by
        change s.re - 2 < -1
        linarith) zero_lt_one]
      norm_num
    _ = (baezDuarteReciprocalMoment c : ℂ) / (1 - s) := by
      dsimp only [m]
      rw [show (s - 2) + 1 = s - 1 by ring, Complex.one_cpow]
      have hrel : 1 - s = -(s - 1) := by ring
      rw [hrel]
      simp only [div_eq_mul_inv, inv_neg]
      ring

theorem integral_baezDuarteLocalMellinError_eq
    (c : baezDuartePositiveNatIndex →₀ ℝ) (s : ℂ)
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (hz : riemannZeta s = 0) :
    (∫ x : ℝ,
        (x : ℂ) ^ (s - 1) * baezDuarteLocalMellinError c x ∂
          (volume.restrict (Ioo (0 : ℝ) 1))) =
      s⁻¹ + (baezDuarteReciprocalMoment c : ℂ) / (1 - s) := by
  let g : ℝ → ℂ := fun x =>
    (x : ℂ) ^ (s - 1) * baezDuarteFiniteKernelSum c x
  have hM := hasMellin_baezDuarteFiniteKernelSum_zero c s hs0 hs1 hz
  have htotal : IntegrableOn g (Ioi (0 : ℝ)) := by
    simpa only [MellinConvergent, g, smul_eq_mul] using hM.1
  have htail : IntegrableOn g (Ioi (1 : ℝ)) :=
    htotal.mono_set (Ioi_subset_Ioi zero_le_one)
  have hzero : (∫ x : ℝ in Ioi (0 : ℝ), g x) = 0 := by
    simpa only [mellin, g, smul_eq_mul] using hM.2
  have hsplit :
      (∫ x : ℝ in (0 : ℝ)..1, g x) + (∫ x : ℝ in Ioi (1 : ℝ), g x) = 0 := by
    have h := hzero
    rw [← intervalIntegral.integral_interval_add_Ioi htotal htail] at h
    exact h
  have hlocal_sum :
      (∫ x : ℝ in Ioo (0 : ℝ) 1, g x) =
        -(baezDuarteReciprocalMoment c : ℂ) / (1 - s) := by
    have htail_value := integral_Ioi_baezDuarteFiniteKernelSum c s hs1
    have hinterval :
        (∫ x : ℝ in (0 : ℝ)..1, g x) = ∫ x : ℝ in Ioo (0 : ℝ) 1, g x := by
      rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    rw [hinterval, htail_value] at hsplit
    linear_combination hsplit
  have hweight : Integrable
      (fun x : ℝ => (x : ℂ) ^ (s - 1))
      (volume.restrict (Ioo (0 : ℝ) 1)) :=
    (intervalIntegral.integrableOn_Ioo_cpow_iff zero_lt_one).2 (by
      simp only [Complex.sub_re, Complex.one_re]
      linarith)
  have hsum_local : Integrable g (volume.restrict (Ioo (0 : ℝ) 1)) :=
    htotal.mono_set Ioo_subset_Ioi_self
  calc
    (∫ x : ℝ,
        (x : ℂ) ^ (s - 1) * baezDuarteLocalMellinError c x ∂
          (volume.restrict (Ioo (0 : ℝ) 1))) =
        (∫ x : ℝ in Ioo (0 : ℝ) 1, (x : ℂ) ^ (s - 1)) -
          ∫ x : ℝ in Ioo (0 : ℝ) 1, g x := by
      rw [← integral_sub hweight hsum_local]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      dsimp only [g]
      rw [baezDuarteLocalMellinError]
      ring
    _ = s⁻¹ - (-(baezDuarteReciprocalMoment c : ℂ) / (1 - s)) := by
      rw [integral_Ioo_cpow_sub_one s hs0, hlocal_sum]
    _ = s⁻¹ + (baezDuarteReciprocalMoment c : ℂ) / (1 - s) := by ring

/-- Membership in the aligned natural-kernel closure excludes every zeta zero strictly to the
right of the critical line. -/
theorem riemannZeta_ne_zero_of_baezDuarteComplexTarget_mem_closure
    (hclosure : baezDuarteComplexTargetL2 ∈ baezDuarteComplexKernelClosure)
    {s : ℂ} (hs_half : 1 / 2 < s.re) (hs_one : s.re < 1) :
    riemannZeta s ≠ 0 := by
  intro hz
  have hs0 : 0 < s.re := by linarith
  have hs_ne : s ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hs_half
    norm_num at hs_half
  let A : ℝ :=
    (∫ x : ℝ, ‖(x : ℂ) ^ (s - 1)‖ ^ (2 : ℝ) ∂
      (volume.restrict (Ioo (0 : ℝ) 1))) ^ (1 / (2 : ℝ))
  let B : ℝ := ‖(1 - s)⁻¹‖
  let Q : ℝ := ‖s⁻¹‖
  let D : ℝ := A + B + 1
  let ε : ℝ := Q / (2 * D)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hQ : 0 < Q := by
    dsimp only [Q]
    exact norm_pos_iff.mpr (inv_ne_zero hs_ne)
  have hD : 0 < D := by dsimp only [D]; linarith
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have happrox :=
    (baezDuarteComplexTarget_mem_closure_iff_fullLineConcreteApprox.mp hclosure)
  obtain ⟨c, hc⟩ := happrox (ε ^ 2) (sq_pos_of_pos hε)
  rw [baezDuarteSplitFullLineError_eq_unitInterval_add_moment_sq] at hc
  have hu0 : 0 ≤ baezDuarteUnitIntervalError c := by
    rw [← integral_norm_baezDuarteLocalMellinError_sq]
    exact integral_nonneg fun x => sq_nonneg ‖baezDuarteLocalMellinError c x‖
  have hu_lt : baezDuarteUnitIntervalError c < ε ^ 2 := by
    nlinarith [sq_nonneg (baezDuarteReciprocalMoment c)]
  have hm_sq_lt : baezDuarteReciprocalMoment c ^ 2 < ε ^ 2 := by
    nlinarith
  have hu_root_le :
      (baezDuarteUnitIntervalError c) ^ (1 / (2 : ℝ)) ≤ ε := by
    rw [← Real.sqrt_eq_rpow]
    exact (Real.sqrt_lt' hε).2 hu_lt |>.le
  have hm_abs_le : |baezDuarteReciprocalMoment c| ≤ ε := by
    exact ((sq_lt_sq₀ (abs_nonneg _) hε.le).mp (by simpa only [sq_abs] using hm_sq_lt)).le
  let I : ℂ := ∫ x : ℝ,
    (x : ℂ) ^ (s - 1) * baezDuarteLocalMellinError c x ∂
      (volume.restrict (Ioo (0 : ℝ) 1))
  have hI : ‖I‖ ≤ A * (baezDuarteUnitIntervalError c) ^ (1 / (2 : ℝ)) := by
    simpa only [I, A] using norm_integral_baezDuarteLocalMellinError_le c s hs_half
  have hidentity : s⁻¹ = I - (baezDuarteReciprocalMoment c : ℂ) / (1 - s) := by
    have h := integral_baezDuarteLocalMellinError_eq c s hs0 hs_one hz
    change I = s⁻¹ + (baezDuarteReciprocalMoment c : ℂ) / (1 - s) at h
    rw [h]
    ring
  have htail_norm :
      ‖(baezDuarteReciprocalMoment c : ℂ) / (1 - s)‖ =
        |baezDuarteReciprocalMoment c| * B := by
    dsimp only [B]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, norm_inv]
    ring
  have hQ_bound : Q ≤
      A * (baezDuarteUnitIntervalError c) ^ (1 / (2 : ℝ)) +
        B * |baezDuarteReciprocalMoment c| := by
    dsimp only [Q]
    rw [hidentity]
    calc
      ‖I - (baezDuarteReciprocalMoment c : ℂ) / (1 - s)‖ ≤
          ‖I‖ + ‖(baezDuarteReciprocalMoment c : ℂ) / (1 - s)‖ := norm_sub_le _ _
      _ ≤ A * (baezDuarteUnitIntervalError c) ^ (1 / (2 : ℝ)) +
          B * |baezDuarteReciprocalMoment c| := by
        rw [htail_norm, mul_comm |baezDuarteReciprocalMoment c| B]
        gcongr
  have hsmall :
      A * (baezDuarteUnitIntervalError c) ^ (1 / (2 : ℝ)) +
          B * |baezDuarteReciprocalMoment c| ≤ (A + B) * ε := by
    calc
      A * (baezDuarteUnitIntervalError c) ^ (1 / (2 : ℝ)) +
          B * |baezDuarteReciprocalMoment c| ≤ A * ε + B * ε := by gcongr
      _ = (A + B) * ε := by ring
  have hstrict : (A + B) * ε < Q := by
    dsimp only [ε]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (mul_pos (by norm_num) hD)).2
    dsimp only [D] at hD ⊢
    have hpos : 0 < Q * (A + B + 2) := mul_pos hQ (by linarith)
    nlinarith
  exact (not_lt_of_ge (hQ_bound.trans hsmall)) hstrict

theorem riemannZeta_one_sub_eq_zero_of_isNontrivialZero
    {s : ℂ} (hs : IsNontrivialZero s) :
    riemannZeta (1 - s) = 0 := by
  have hs0 : s ≠ 0 := ne_zero_of_isNontrivialZero hs
  have hcompleted : completedRiemannZeta s = 0 :=
    completedRiemannZeta_eq_zero_of_isZetaZero_of_Gammaℝ_ne_zero hs0
      (Gammaℝ_ne_zero_of_isNontrivialZero hs) hs.1
  have hreflected : completedRiemannZeta (1 - s) = 0 := by
    rw [completedRiemannZeta_one_sub]
    exact hcompleted
  have href_ne : 1 - s ≠ 0 := by
    intro h
    have : (1 : ℂ) = s := sub_eq_zero.mp h
    exact hs.2.2 this.symm
  rw [riemannZeta_def_of_ne_zero href_ne, hreflected]
  simp

/-- The reverse implication of Baez-Duarte's strong positive-natural criterion, connected to the
exact Mathlib statement of RH. -/
theorem baezDuarteComplexTarget_mem_closure_imp_riemannHypothesis
    (hclosure : baezDuarteComplexTargetL2 ∈ baezDuarteComplexKernelClosure) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_nontrivial_zeros_on_line]
  intro s hs
  rw [OnCriticalLine]
  rcases lt_trichotomy s.re (1 / 2) with hleft | hline | hright
  · have hreflect_zero := riemannZeta_one_sub_eq_zero_of_isNontrivialZero hs
    have hreflect_half : 1 / 2 < (1 - s).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    by_cases hreflect_one : (1 - s).re < 1
    · exact False.elim
        (riemannZeta_ne_zero_of_baezDuarteComplexTarget_mem_closure
          hclosure hreflect_half hreflect_one hreflect_zero)
    · exact False.elim
        (riemannZeta_ne_zero_of_one_le_re (le_of_not_gt hreflect_one) hreflect_zero)
  · exact hline
  · exact False.elim
      (riemannZeta_ne_zero_of_baezDuarteComplexTarget_mem_closure
        hclosure hright (nontrivial_zero_re_lt_one hs) hs.1)

end LeanLab.Riemann
