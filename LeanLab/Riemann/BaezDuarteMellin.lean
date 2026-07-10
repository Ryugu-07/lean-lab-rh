import LeanLab.Riemann.NymanBeurling
import Mathlib.Analysis.MellinTransform
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaAbelContinuation

set_option linter.style.header false

/-!
# Mellin transform of the Baez-Duarte fractional-part kernel

This file formalizes the classical identity

`M[rho(1/x)](s) = -zeta(s) / s`, for `0 < re(s) < 1`.

The Abel-continuation input is an audited source snapshot from
`PrimeNumberTheoremAnd`; the final theorem also proves convergence of the Mellin integral.
-/

noncomputable section

open MeasureTheory Set Filter Topology Complex ZetaAbelFractKernel
open scoped Topology

namespace LeanLab.Riemann

/-- The connected positive-real-part domain of the Abel formula, with its pole removed. -/
def zetaAbelPositiveDomain : Set ℂ :=
  {s | s ≠ (1 : ℂ) ∧ 0 < s.re}

theorem isOpen_zetaAbelPositiveDomain : IsOpen zetaAbelPositiveDomain := by
  change IsOpen ({s : ℂ | s ≠ 1} ∩ {s : ℂ | 0 < s.re})
  exact isOpen_compl_singleton.inter (isOpen_lt continuous_const Complex.continuous_re)

theorem isPreconnected_zetaAbelPositiveDomain : IsPreconnected zetaAbelPositiveDomain := by
  convert (Complex.isPathConnected_halfSpace_re_gt_diff_singleton
      (a := 0) (p := (1 : ℂ)) (by norm_num)).isConnected.isPreconnected using 1
  ext z
  simp [zetaAbelPositiveDomain, and_comm]

theorem two_mem_zetaAbelPositiveDomain : (2 : ℂ) ∈ zetaAbelPositiveDomain := by
  simp [zetaAbelPositiveDomain]

/-- The Abel integral formula is analytic wherever `re(s) > 0`, away from the pole at one. -/
theorem analyticOn_zetaAbelContinuationFormula_positive :
    AnalyticOn ℂ zetaAbelContinuationFormula zetaAbelPositiveDomain := by
  simp only [AnalyticOn, zetaAbelPositiveDomain, Set.mem_setOf_eq]
  intro s ⟨hs_ne, hs_re⟩
  apply AnalyticAt.analyticWithinAt
  refine analyticAt_const.add (analyticAt_const.div (analyticAt_id.sub analyticAt_const) ?_) |>.sub
    (analyticAt_id.mul (integral_analytic s hs_re))
  exact sub_ne_zero.mpr hs_ne

/-- The source Abel formula for zeta is valid on the full half-plane `re(s) > 0`, away from one. -/
theorem riemannZeta_eq_zetaAbelContinuationFormula_of_re_pos
    (s : ℂ) (hs_ne : s ≠ 1) (hs_re : 0 < s.re) :
    riemannZeta s = zetaAbelContinuationFormula s := by
  have hUo := isOpen_zetaAbelPositiveDomain
  have hζ : AnalyticOnNhd ℂ riemannZeta zetaAbelPositiveDomain := by
    rw [← hUo.analyticOn_iff_analyticOnNhd]
    have h : AnalyticOn ℂ riemannZeta ({1} : Set ℂ)ᶜ :=
      isOpen_compl_singleton.analyticOn_iff_analyticOnNhd.mpr analyticOn_riemannZeta
    exact AnalyticOn.mono h fun _ hz => hz.1
  have hF : AnalyticOnNhd ℂ zetaAbelContinuationFormula zetaAbelPositiveDomain := by
    rw [← hUo.analyticOn_iff_analyticOnNhd]
    exact analyticOn_zetaAbelContinuationFormula_positive
  have hEq : riemannZeta =ᶠ[𝓝 (2 : ℂ)] zetaAbelContinuationFormula := by
    have hopen : IsOpen {w : ℂ | 1 < w.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with w hw
      using riemannZeta_abel_integral w hw
  exact (AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    hζ hF isPreconnected_zetaAbelPositiveDomain two_mem_zetaAbelPositiveDomain hEq)
      ⟨hs_ne, hs_re⟩

/-- The real fractional-part function, regarded as complex-valued. -/
def complexFractionalPart (x : ℝ) : ℂ :=
  (Int.fract x : ℝ)

private theorem cpow_neg_sub_one_mul_complexFractionalPart
    (s : ℂ) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    (u : ℂ) ^ (-s - 1) * complexFractionalPart u = (u : ℂ) ^ (-s) := by
  rw [complexFractionalPart, Int.fract_eq_self.2 ⟨hu0.le, hu1⟩]
  calc
    (u : ℂ) ^ (-s - 1) * (u : ℂ) =
        (u : ℂ) ^ (-s - 1) * (u : ℂ) ^ (1 : ℂ) := by rw [Complex.cpow_one]
    _ = (u : ℂ) ^ ((-s - 1) + 1) :=
      (Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hu0.ne')).symm
    _ = (u : ℂ) ^ (-s) := by
      congr 1
      ring

/-- The Mellin integral of the fractional-part function converges at `-s` on the critical strip. -/
theorem mellinConvergent_complexFractionalPart_neg
    (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    MellinConvergent complexFractionalPart (-s) := by
  rw [MellinConvergent, ← Ioc_union_Ioi_eq_Ioi zero_le_one, integrableOn_union]
  constructor
  · rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    have hpow : IntegrableOn (fun u : ℝ => (u : ℂ) ^ (-s)) (Ioc 0 1) := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
      exact intervalIntegral.intervalIntegrable_cpow' (by
        simp only [neg_re]
        linarith)
    refine (hpow.mono_set Ioo_subset_Ioc_self).congr_fun ?_ measurableSet_Ioo
    intro u hu
    simpa only [smul_eq_mul] using
      (cpow_neg_sub_one_mul_complexFractionalPart s hu.1 hu.2).symm
  · simpa [IntegrableOn, complexFractionalPart, zetaAbelFractKernel, smul_eq_mul, mul_comm] using
      ZetaAbelFractKernel.integrableOn_Ioi s hs0

private theorem integral_zero_one_complexFractionalPart_neg
    (s : ℂ) (hs1 : s.re < 1) :
    (∫ u : ℝ in (0 : ℝ)..1,
      (u : ℂ) ^ (-s - 1) * complexFractionalPart u) = 1 / (1 - s) := by
  calc
    (∫ u : ℝ in (0 : ℝ)..1,
        (u : ℂ) ^ (-s - 1) * complexFractionalPart u) =
        ∫ u : ℝ in Ioc (0 : ℝ) 1,
          (u : ℂ) ^ (-s - 1) * complexFractionalPart u := by
            rw [intervalIntegral.integral_of_le zero_le_one]
    _ = ∫ u : ℝ in Ioo (0 : ℝ) 1,
          (u : ℂ) ^ (-s - 1) * complexFractionalPart u :=
      integral_Ioc_eq_integral_Ioo
    _ = ∫ u : ℝ in Ioo (0 : ℝ) 1, (u : ℂ) ^ (-s) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro u hu
      exact cpow_neg_sub_one_mul_complexFractionalPart s hu.1 hu.2
    _ = ∫ u : ℝ in Ioc (0 : ℝ) 1, (u : ℂ) ^ (-s) :=
      integral_Ioc_eq_integral_Ioo.symm
    _ = ∫ u : ℝ in (0 : ℝ)..1, (u : ℂ) ^ (-s) := by
      rw [intervalIntegral.integral_of_le zero_le_one]
    _ = 1 / (1 - s) := by
      rw [integral_cpow (Or.inl (by simp only [neg_re]; linarith))]
      have hne : -s + 1 ≠ 0 := by
        intro h
        apply_fun Complex.re at h
        simp only [add_re, neg_re, one_re, zero_re] at h
        linarith
      rw [ofReal_one, ofReal_zero, one_cpow, zero_cpow hne, sub_zero]
      congr 1
      ring

/-- Abel continuation gives the Mellin transform of the fractional-part function at `-s`. -/
theorem mellin_complexFractionalPart_neg_eq
    (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    mellin complexFractionalPart (-s) = -riemannZeta s / s := by
  have hs_ne_zero : s ≠ 0 := by
    intro hs
    rw [hs, zero_re] at hs0
    exact lt_irrefl 0 hs0
  have hs_ne_one : s ≠ 1 := by
    intro hs
    rw [hs, one_re] at hs1
    exact lt_irrefl 1 hs1
  let g : ℝ → ℂ := fun u => (u : ℂ) ^ (-s - 1) * complexFractionalPart u
  have htotal : IntegrableOn g (Ioi (0 : ℝ)) := by
    have hconv := mellinConvergent_complexFractionalPart_neg s hs0 hs1
    simpa [MellinConvergent, g, smul_eq_mul] using hconv
  have htail : IntegrableOn g (Ioi (1 : ℝ)) :=
    htotal.mono_set (Ioi_subset_Ioi zero_le_one)
  have htail_eq :
      (∫ u : ℝ in Ioi (1 : ℝ), g u) =
        ∫ u : ℝ in Ioi (1 : ℝ), zetaAbelFractKernel s u := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _hu
    simp [g, complexFractionalPart, zetaAbelFractKernel, mul_comm]
  have hzeta := riemannZeta_eq_zetaAbelContinuationFormula_of_re_pos
    s hs_ne_one hs0
  rw [mellin]
  change (∫ u : ℝ in Ioi (0 : ℝ), g u) = -riemannZeta s / s
  rw [← intervalIntegral.integral_interval_add_Ioi htotal htail,
    integral_zero_one_complexFractionalPart_neg s hs1, htail_eq, hzeta,
    zetaAbelContinuationFormula]
  have hs_sub_one : s - 1 ≠ 0 := sub_ne_zero.mpr hs_ne_one
  have one_sub_s : 1 - s ≠ 0 := sub_ne_zero.mpr hs_ne_one.symm
  field_simp [hs_ne_zero, hs_sub_one, one_sub_s]
  ring

/-- The classical Mellin identity at the root of the Nyman-Beurling formulation. -/
theorem hasMellin_fractionalPartKernel_one
    (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    HasMellin (fun x : ℝ => (fractionalPartKernel 1 x : ℂ)) s
      (-riemannZeta s / s) := by
  have hfun :
      (fun x : ℝ => (fractionalPartKernel 1 x : ℂ)) =
        fun x : ℝ => complexFractionalPart (x ^ (-1 : ℝ)) := by
    funext x
    simp [fractionalPartKernel, complexFractionalPart, Real.rpow_neg_one, one_div]
  have hdiv : s / ((-1 : ℝ) : ℂ) = -s := by
    simp [div_eq_mul_inv]
  rw [hfun]
  constructor
  · rw [MellinConvergent.comp_rpow (f := complexFractionalPart)
      (s := s) (a := (-1 : ℝ)) (by norm_num)]
    rw [hdiv]
    exact mellinConvergent_complexFractionalPart_neg s hs0 hs1
  · rw [mellin_comp_rpow]
    simp only [abs_neg, abs_one, inv_one, one_smul]
    rw [hdiv]
    exact mellin_complexFractionalPart_neg_eq s hs0 hs1

/-- Mellin transform of every positive-natural Baez-Duarte kernel `rho(1 / (n*x))`. -/
theorem hasMellin_baezDuarteKernel
    (n : baezDuartePositiveNatIndex) (s : ℂ)
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    HasMellin
      (fun x : ℝ =>
        (fractionalPartKernel (((n : ℕ) : ℝ)⁻¹) x : ℂ)) s
      (((n : ℕ) : ℂ) ^ (-s) * (-riemannZeta s / s)) := by
  have hnpos : 0 < ((n : ℕ) : ℝ) := Nat.cast_pos.mpr n.property
  have hfun :
      (fun x : ℝ =>
        (fractionalPartKernel (((n : ℕ) : ℝ)⁻¹) x : ℂ)) =
        fun x : ℝ => (fractionalPartKernel 1 (((n : ℕ) : ℝ) * x) : ℂ) := by
    funext x
    simp [fractionalPartKernel, div_eq_mul_inv, mul_inv_rev, mul_comm]
  rw [hfun]
  constructor
  · rw [MellinConvergent.comp_mul_left
      (f := fun y : ℝ => (fractionalPartKernel 1 y : ℂ))
      (s := s) (a := ((n : ℕ) : ℝ)) hnpos]
    exact (hasMellin_fractionalPartKernel_one s hs0 hs1).1
  · rw [mellin_comp_mul_left
        (fun y : ℝ => (fractionalPartKernel 1 y : ℂ)) s hnpos,
      (hasMellin_fractionalPartKernel_one s hs0 hs1).2]
    rfl

end LeanLab.Riemann
