import LeanLab.Riemann.WeilFiniteDictionarySourceCalculus
import LeanLab.Riemann.WeilCompactLaplaceZeroCutoff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Admissibility of the finite Guinand--Weil dictionary

This module studies the piecewise-smooth Fourier weight produced by the finite Volterra source
calculus. It proves its literal boundary regularity and aligns the induced entire Fourier test
with the project's compact-Laplace coordinates before addressing horizontal-strip decay and the
actual xi-divisor sum.
-/

open Complex Filter Function MeasureTheory Set Topology
open scoped BigOperators ContDiff Interval Topology

namespace LeanLab.Riemann

noncomputable section

@[simp]
theorem weilFiniteVolterraKernel_zero (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) :
    weilFiniteVolterraKernel N u 0 = 0 := by
  simp [weilFiniteVolterraKernel]

@[fun_prop]
theorem continuous_weilFiniteVolterraPair (N : ℕ)
    (i j : Fin (2 * N + 1)) :
    Continuous (weilFiniteVolterraPair N i j) := by
  by_cases hij : i = j
  · subst j
    have heq : weilFiniteVolterraPair N i i =
        fun (w : ℝ) => ((2 : ℝ) : ℂ) * (w : ℂ) *
          weilFiniteTrigMonomial N i w := by
      apply funext
      intro w
      simpa only [ofReal_ofNat, ofReal_mul] using
        weilFiniteVolterraPair_same N i w
    rw [heq]
    unfold weilFiniteTrigMonomial
    fun_prop
  · have heq : weilFiniteVolterraPair N i j =
      fun (w : ℝ) =>
        (weilFiniteTrigMonomial N i w - weilFiniteTrigMonomial N j w) /
          (((Real.pi *
            ((weilFiniteCenteredFrequency N i : ℝ) -
              (weilFiniteCenteredFrequency N j : ℝ)) : ℝ) : ℂ) * Complex.I) := by
      apply funext
      intro w
      exact weilFiniteVolterraPair_ne hij w
    rw [heq]
    unfold weilFiniteTrigMonomial
    fun_prop

@[fun_prop]
theorem continuous_weilFiniteVolterraKernel (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) :
    Continuous (weilFiniteVolterraKernel N u) := by
  rw [show weilFiniteVolterraKernel N u =
      fun (w : ℝ) => ∑ i, ∑ j,
        (((u i * u j : ℝ) : ℂ) * weilFiniteVolterraPair N i j w) by
    funext w
    exact weilFiniteVolterraKernel_eq_sum_pairs N u w]
  fun_prop

@[fun_prop]
theorem contDiff_weilFiniteTrigMonomial (N : ℕ)
    (i : Fin (2 * N + 1)) :
    ContDiff ℝ ∞ (weilFiniteTrigMonomial N i) := by
  unfold weilFiniteTrigMonomial
  have hreal : ContDiff ℝ ∞
      (fun w : ℝ =>
        (2 * Real.pi * (weilFiniteCenteredFrequency N i : ℝ)) * w) :=
    contDiff_const.mul contDiff_id
  exact ((Complex.ofRealCLM.contDiff.comp hreal).mul contDiff_const).cexp

@[fun_prop]
theorem contDiff_weilFiniteVolterraPair (N : ℕ)
    (i j : Fin (2 * N + 1)) :
    ContDiff ℝ ∞ (weilFiniteVolterraPair N i j) := by
  by_cases hij : i = j
  · subst j
    have heq : weilFiniteVolterraPair N i i =
        fun (w : ℝ) => ((2 : ℝ) : ℂ) * (w : ℂ) *
          weilFiniteTrigMonomial N i w := by
      apply funext
      intro w
      simpa only [ofReal_ofNat, ofReal_mul] using
        weilFiniteVolterraPair_same N i w
    rw [heq]
    exact ((contDiff_const.mul Complex.ofRealCLM.contDiff).mul
      (contDiff_weilFiniteTrigMonomial N i))
  · have heq : weilFiniteVolterraPair N i j =
      fun (w : ℝ) =>
        (weilFiniteTrigMonomial N i w - weilFiniteTrigMonomial N j w) /
          (((Real.pi *
            ((weilFiniteCenteredFrequency N i : ℝ) -
              (weilFiniteCenteredFrequency N j : ℝ)) : ℝ) : ℂ) * Complex.I) := by
      apply funext
      intro w
      exact weilFiniteVolterraPair_ne hij w
    rw [heq]
    exact ((contDiff_weilFiniteTrigMonomial N i).sub
      (contDiff_weilFiniteTrigMonomial N j)).div_const _

@[fun_prop]
theorem contDiff_weilFiniteVolterraKernel (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) :
    ContDiff ℝ ∞ (weilFiniteVolterraKernel N u) := by
  rw [show weilFiniteVolterraKernel N u =
      fun (w : ℝ) => ∑ i, ∑ j,
        (((u i * u j : ℝ) : ℂ) * weilFiniteVolterraPair N i j w) by
    funext w
    exact weilFiniteVolterraKernel_eq_sum_pairs N u w]
  fun_prop

/-- Two integrations by parts on one smooth interval, with every boundary term retained. -/
theorem sq_mul_intervalIntegral_mul_cexp_eq
    {h : ℝ → ℂ} (hh : ContDiff ℝ 2 h)
    (a b : ℝ) (s : ℂ) :
    s ^ 2 * (∫ x : ℝ in a..b,
        h x * Complex.exp (s * (x : ℂ))) =
      s * (h b * Complex.exp (s * (b : ℂ)) -
        h a * Complex.exp (s * (a : ℂ))) -
      (deriv h b * Complex.exp (s * (b : ℂ)) -
        deriv h a * Complex.exp (s * (a : ℂ))) +
      ∫ x : ℝ in a..b,
        deriv (deriv h) x * Complex.exp (s * (x : ℂ)) := by
  let e : ℝ → ℂ := fun x => Complex.exp (s * (x : ℂ))
  have he (x : ℝ) :
      HasDerivAt e (s * e x) x := by
    dsimp only [e]
    convert ((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul s).cexp using 1
    · ext y
      simp
    · simp
      ring
  have hh1 : ContDiff ℝ 1 h := hh.of_le (by norm_num)
  have hdh : ContDiff ℝ 1 (deriv h) := by
    simpa using hh.deriv'
  have hdiff : Differentiable ℝ h := hh1.differentiable one_ne_zero
  have hddiff : Differentiable ℝ (deriv h) :=
    hdh.differentiable one_ne_zero
  have hderivInt : IntervalIntegrable (deriv h) volume a b :=
    hh1.continuous_deriv_one.intervalIntegrable (μ := volume) a b
  have hderiv2Int : IntervalIntegrable (deriv (deriv h)) volume a b :=
    hdh.continuous_deriv_one.intervalIntegrable (μ := volume) a b
  have hseInt : IntervalIntegrable (fun x : ℝ => s * e x) volume a b := by
    apply Continuous.intervalIntegrable
    dsimp only [e]
    fun_prop
  have heInt : IntervalIntegrable e volume a b := by
    apply Continuous.intervalIntegrable
    dsimp only [e]
    fun_prop
  have hibp0 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := h) (u' := deriv h) (v := e) (v' := fun x => s * e x)
    (fun x _ => (hdiff x).hasDerivAt) (fun x _ => he x)
    hderivInt hseInt
  have hibp1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := deriv h) (u' := deriv (deriv h)) (v := e)
    (v' := fun x => s * e x)
    (fun x _ => (hddiff x).hasDerivAt) (fun x _ => he x)
    hderiv2Int hseInt
  have hscale0 :
      (∫ x : ℝ in a..b, h x * (s * e x)) =
        s * ∫ x : ℝ in a..b, h x * e x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  have hscale1 :
      (∫ x : ℝ in a..b, deriv h x * (s * e x)) =
        s * ∫ x : ℝ in a..b, deriv h x * e x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [hscale0] at hibp0
  rw [hscale1] at hibp1
  dsimp only [e] at hibp0 hibp1
  calc
    s ^ 2 * (∫ x : ℝ in a..b,
        h x * Complex.exp (s * (x : ℂ))) =
        s * (s * ∫ x : ℝ in a..b,
          h x * Complex.exp (s * (x : ℂ))) := by ring
    _ = s * ((h b * Complex.exp (s * (b : ℂ)) -
          h a * Complex.exp (s * (a : ℂ))) -
        ∫ x : ℝ in a..b,
          deriv h x * Complex.exp (s * (x : ℂ))) := by rw [hibp0]
    _ = s * (h b * Complex.exp (s * (b : ℂ)) -
          h a * Complex.exp (s * (a : ℂ))) -
        (deriv h b * Complex.exp (s * (b : ℂ)) -
          deriv h a * Complex.exp (s * (a : ℂ))) +
        ∫ x : ℝ in a..b,
          deriv (deriv h) x * Complex.exp (s * (x : ℂ)) := by
      calc
        s * ((h b * Complex.exp (s * (b : ℂ)) -
              h a * Complex.exp (s * (a : ℂ))) -
            ∫ x : ℝ in a..b,
              deriv h x * Complex.exp (s * (x : ℂ))) =
            s * (h b * Complex.exp (s * (b : ℂ)) -
              h a * Complex.exp (s * (a : ℂ))) -
              s * ∫ x : ℝ in a..b,
                deriv h x * Complex.exp (s * (x : ℂ)) := by ring
        _ = s * (h b * Complex.exp (s * (b : ℂ)) -
              h a * Complex.exp (s * (a : ℂ))) -
            ((deriv h b * Complex.exp (s * (b : ℂ)) -
                deriv h a * Complex.exp (s * (a : ℂ))) -
              ∫ x : ℝ in a..b,
                deriv (deriv h) x * Complex.exp (s * (x : ℂ))) := by
          rw [hibp1]
        _ = _ := by ring

/-- The source chord parameter, clamped to zero beyond the Fourier band. -/
def weilFiniteDictionaryClampedChord (C : ℕ) (ξ : ℝ) : ℝ :=
  max 0 (1 - |ξ| / weilFiniteDictionaryBandwidth C)

theorem continuous_weilFiniteDictionaryClampedChord (C : ℕ) :
    Continuous (weilFiniteDictionaryClampedChord C) := by
  unfold weilFiniteDictionaryClampedChord
  fun_prop

theorem weilFiniteDictionaryFourierWeight_eq_clamped
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) (ξ : ℝ) :
    weilFiniteDictionaryFourierWeight C N u ξ =
      Real.pi * (weilFiniteVolterraKernel N u
        (weilFiniteDictionaryClampedChord C ξ)).re := by
  have hDelta := weilFiniteDictionaryBandwidth_pos hC
  by_cases hξ : |ξ| ≤ weilFiniteDictionaryBandwidth C
  · have hchord : 0 ≤ 1 - |ξ| / weilFiniteDictionaryBandwidth C := by
      rw [sub_nonneg, div_le_one hDelta]
      exact hξ
    rw [weilFiniteDictionaryFourierWeight, if_pos hξ]
    simp [weilFiniteDictionaryClampedChord, max_eq_right hchord]
  · have hξ' : weilFiniteDictionaryBandwidth C < |ξ| := lt_of_not_ge hξ
    have hchord : 1 - |ξ| / weilFiniteDictionaryBandwidth C < 0 := by
      rw [sub_neg, one_lt_div hDelta]
      exact hξ'
    rw [weilFiniteDictionaryFourierWeight, if_neg hξ]
    simp [weilFiniteDictionaryClampedChord, max_eq_left hchord.le]

theorem continuous_weilFiniteDictionaryFourierWeight
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) :
    Continuous (weilFiniteDictionaryFourierWeight C N u) := by
  rw [show weilFiniteDictionaryFourierWeight C N u =
      fun ξ => Real.pi * (weilFiniteVolterraKernel N u
        (weilFiniteDictionaryClampedChord C ξ)).re by
    funext ξ
    exact weilFiniteDictionaryFourierWeight_eq_clamped hC N u ξ]
  exact continuous_const.mul
    (Complex.continuous_re.comp
      ((continuous_weilFiniteVolterraKernel N u).comp
        (continuous_weilFiniteDictionaryClampedChord C)))

theorem hasCompactSupport_weilFiniteDictionaryFourierWeight
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) :
    HasCompactSupport (weilFiniteDictionaryFourierWeight C N u) := by
  let Δ := weilFiniteDictionaryBandwidth C
  refine HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (-Δ) Δ)) ?_
  intro ξ hξ
  have houtside : Δ < |ξ| := by
    have hnot : ¬(-Δ ≤ ξ ∧ ξ ≤ Δ) := by
      simpa only [mem_Icc] using hξ
    rcases not_and_or.mp hnot with hleft | hright
    · rw [not_le] at hleft
      rw [abs_of_neg (lt_of_lt_of_le hleft (neg_nonpos.mpr
        (weilFiniteDictionaryBandwidth_pos hC).le))]
      linarith
    · rw [not_le] at hright
      rw [abs_of_pos (lt_trans (weilFiniteDictionaryBandwidth_pos hC) hright)]
      exact hright
  exact weilFiniteDictionaryFourierWeight_eq_zero_of_bandwidth_lt houtside

theorem integrable_weilFiniteDictionaryFourierWeight
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) :
    Integrable (weilFiniteDictionaryFourierWeight C N u) :=
  (continuous_weilFiniteDictionaryFourierWeight hC N u).integrable_of_hasCompactSupport
    (hasCompactSupport_weilFiniteDictionaryFourierWeight hC N u)

/-- The source Fourier weight in the project's logarithmic coordinate `x=2*pi*xi`. -/
def weilFiniteDictionaryLogWeight (C N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) (x : ℝ) : ℝ :=
  weilFiniteDictionaryFourierWeight C N u (x / (2 * Real.pi))

theorem continuous_weilFiniteDictionaryLogWeight
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) :
    Continuous (weilFiniteDictionaryLogWeight C N u) := by
  unfold weilFiniteDictionaryLogWeight
  exact (continuous_weilFiniteDictionaryFourierWeight hC N u).comp
    (continuous_id.div_const (2 * Real.pi))

theorem hasCompactSupport_weilFiniteDictionaryLogWeight
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) :
    HasCompactSupport (weilFiniteDictionaryLogWeight C N u) := by
  have hscale : (2 * Real.pi : ℝ)⁻¹ ≠ 0 :=
    inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  have hsupp :=
    (hasCompactSupport_weilFiniteDictionaryFourierWeight hC N u).comp_homeomorph
      (Homeomorph.mulRight₀ ((2 * Real.pi : ℝ)⁻¹) hscale)
  have heq : weilFiniteDictionaryLogWeight C N u =
      weilFiniteDictionaryFourierWeight C N u ∘
        (Homeomorph.mulRight₀ ((2 * Real.pi : ℝ)⁻¹) hscale) := by
    funext x
    simp only [weilFiniteDictionaryLogWeight, Function.comp_apply,
      Homeomorph.coe_mulRight₀, div_eq_mul_inv]
  rw [heq]
  exact hsupp

/-- The compact logarithmic density whose bilateral Laplace transform is the source test. -/
def weilFiniteDictionaryPhysicalDensity (C N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) (x : ℝ) : ℂ :=
  (((2 * Real.pi : ℝ)⁻¹ : ℝ) : ℂ) *
    Complex.exp ((-(x / 2) : ℝ) : ℂ) *
      (weilFiniteDictionaryLogWeight C N u x : ℂ)

theorem continuous_weilFiniteDictionaryPhysicalDensity
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) :
    Continuous (weilFiniteDictionaryPhysicalDensity C N u) := by
  unfold weilFiniteDictionaryPhysicalDensity
  exact (continuous_const.mul
    (Complex.continuous_exp.comp
      (Complex.continuous_ofReal.comp
        (continuous_id.div_const 2).neg))).mul
          (Complex.continuous_ofReal.comp
            (continuous_weilFiniteDictionaryLogWeight hC N u))

theorem hasCompactSupport_weilFiniteDictionaryPhysicalDensity
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) :
    HasCompactSupport (weilFiniteDictionaryPhysicalDensity C N u) := by
  unfold weilFiniteDictionaryPhysicalDensity
  exact ((hasCompactSupport_weilFiniteDictionaryLogWeight hC N u).comp_left
    Complex.ofReal_zero).mul_left

theorem integrable_weilFiniteDictionaryPhysicalDensity
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) :
    Integrable (weilFiniteDictionaryPhysicalDensity C N u) :=
  (continuous_weilFiniteDictionaryPhysicalDensity hC N u).integrable_of_hasCompactSupport
    (hasCompactSupport_weilFiniteDictionaryPhysicalDensity hC N u)

/-- The literal Fourier integral of the finite-dictionary test. -/
def weilFiniteDictionaryTest (C N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) (z : ℂ) : ℂ :=
  ∫ ξ : ℝ in -weilFiniteDictionaryBandwidth C..weilFiniteDictionaryBandwidth C,
    (weilFiniteDictionaryFourierWeight C N u ξ : ℂ) *
      Complex.exp
        ((((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) * z)

theorem intervalIntegrable_weilFiniteDictionaryTest
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) (z : ℂ) :
    IntervalIntegrable
      (fun ξ : ℝ =>
        (weilFiniteDictionaryFourierWeight C N u ξ : ℂ) *
          Complex.exp ((((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) * z))
      volume (-weilFiniteDictionaryBandwidth C) (weilFiniteDictionaryBandwidth C) := by
  apply Continuous.intervalIntegrable
  exact (Complex.continuous_ofReal.comp
    (continuous_weilFiniteDictionaryFourierWeight hC N u)).mul
      (Complex.continuous_exp.comp (by fun_prop))

theorem integral_eq_intervalIntegral_of_eq_zero_off_Icc
    {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hzero : ∀ x : ℝ, x ∉ Icc a b → f x = 0) :
    (∫ x : ℝ, f x) = ∫ x : ℝ in a..b, f x := by
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  rw [← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ Icc a b
  · simp [hx]
  · simp [hx, hzero x hx]

/-- The logarithmic Fourier kernel after the source substitution `x=2*pi*xi`. -/
def weilFiniteDictionaryScaledKernel (C N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) (z : ℂ) (x : ℝ) : ℂ :=
  (((2 * Real.pi : ℝ)⁻¹ : ℝ) : ℂ) *
    (weilFiniteDictionaryLogWeight C N u x : ℂ) *
      Complex.exp ((Complex.I * z) * (x : ℂ))

theorem weilFiniteDictionaryPhysicalLaplaceKernel
    (C N : ℕ) (u : Fin (2 * N + 1) → ℝ) (z : ℂ) (x : ℝ) :
    Complex.exp (((1 / 2 : ℂ) + Complex.I * z) * (x : ℂ)) *
        weilFiniteDictionaryPhysicalDensity C N u x =
      weilFiniteDictionaryScaledKernel C N u z x := by
  have harg :
      (((1 / 2 : ℂ) + Complex.I * z) * (x : ℂ)) +
          ((-(x / 2) : ℝ) : ℂ) =
        (Complex.I * z) * (x : ℂ) := by
    push_cast
    ring
  rw [weilFiniteDictionaryPhysicalDensity, weilFiniteDictionaryScaledKernel]
  calc
    Complex.exp (((1 / 2 : ℂ) + Complex.I * z) * (x : ℂ)) *
          ((((2 * Real.pi : ℝ)⁻¹ : ℝ) : ℂ) *
            Complex.exp ((-(x / 2) : ℝ) : ℂ) *
              (weilFiniteDictionaryLogWeight C N u x : ℂ)) =
        (((2 * Real.pi : ℝ)⁻¹ : ℝ) : ℂ) *
          (weilFiniteDictionaryLogWeight C N u x : ℂ) *
            (Complex.exp (((1 / 2 : ℂ) + Complex.I * z) * (x : ℂ)) *
              Complex.exp ((-(x / 2) : ℝ) : ℂ)) := by ring
    _ = (((2 * Real.pi : ℝ)⁻¹ : ℝ) : ℂ) *
          (weilFiniteDictionaryLogWeight C N u x : ℂ) *
            Complex.exp
              ((((1 / 2 : ℂ) + Complex.I * z) * (x : ℂ)) +
                ((-(x / 2) : ℝ) : ℂ)) := by
      rw [Complex.exp_add]
    _ = _ := by rw [harg]

theorem weilFiniteDictionaryScaledKernel_zero_off
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) (z : ℂ) {x : ℝ}
    (hx : x ∉ Icc
      ((2 * Real.pi) * (-weilFiniteDictionaryBandwidth C))
      ((2 * Real.pi) * weilFiniteDictionaryBandwidth C)) :
    weilFiniteDictionaryScaledKernel C N u z x = 0 := by
  have hc : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hDelta := weilFiniteDictionaryBandwidth_pos hC
  have habs : (2 * Real.pi) * weilFiniteDictionaryBandwidth C < |x| := by
    have hnot : ¬
        ((2 * Real.pi) * (-weilFiniteDictionaryBandwidth C) ≤ x ∧
          x ≤ (2 * Real.pi) * weilFiniteDictionaryBandwidth C) := by
      simpa only [mem_Icc] using hx
    rcases not_and_or.mp hnot with hleft | hright
    · rw [not_le] at hleft
      have hxneg : x < 0 := by
        calc
          x < (2 * Real.pi) * (-weilFiniteDictionaryBandwidth C) := hleft
          _ < 0 := mul_neg_of_pos_of_neg hc (neg_neg_of_pos hDelta)
      rw [abs_of_neg hxneg]
      nlinarith
    · rw [not_le] at hright
      have hxpos : 0 < x :=
        lt_trans (mul_pos hc hDelta) hright
      rw [abs_of_pos hxpos]
      exact hright
  have hcoord :
      weilFiniteDictionaryBandwidth C < |x / (2 * Real.pi)| := by
    rw [abs_div, abs_of_pos hc]
    rw [lt_div_iff₀ hc]
    simpa only [mul_comm] using habs
  have hweight :
      weilFiniteDictionaryLogWeight C N u x = 0 := by
    exact weilFiniteDictionaryFourierWeight_eq_zero_of_bandwidth_lt hcoord
  simp [weilFiniteDictionaryScaledKernel, hweight]

theorem compactLaplaceTransform_weilFiniteDictionaryPhysicalDensity
    (C N : ℕ) (u : Fin (2 * N + 1) → ℝ) (z : ℂ) :
    compactLaplaceTransform (weilFiniteDictionaryPhysicalDensity C N u)
        ((1 / 2 : ℂ) + Complex.I * z) =
      ∫ x : ℝ, weilFiniteDictionaryScaledKernel C N u z x := by
  unfold compactLaplaceTransform
  apply integral_congr_ae
  filter_upwards [] with x
  exact weilFiniteDictionaryPhysicalLaplaceKernel C N u z x

theorem integral_weilFiniteDictionaryScaledKernel_eq_interval
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) (z : ℂ) :
    (∫ x : ℝ, weilFiniteDictionaryScaledKernel C N u z x) =
      ∫ x : ℝ in
        (2 * Real.pi) * (-weilFiniteDictionaryBandwidth C)..
          (2 * Real.pi) * weilFiniteDictionaryBandwidth C,
        weilFiniteDictionaryScaledKernel C N u z x := by
  apply integral_eq_intervalIntegral_of_eq_zero_off_Icc
  · have hc : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
    have hDelta := weilFiniteDictionaryBandwidth_pos hC
    nlinarith
  · intro x hx
    exact weilFiniteDictionaryScaledKernel_zero_off hC N u z hx

theorem weilFiniteDictionaryScaledKernel_changeOfVariables
    (C N : ℕ) (u : Fin (2 * N + 1) → ℝ) (z : ℂ) (ξ : ℝ) :
    ((2 * Real.pi : ℝ) : ℂ) *
        weilFiniteDictionaryScaledKernel C N u z ((2 * Real.pi) * ξ) =
      (weilFiniteDictionaryFourierWeight C N u ξ : ℂ) *
        Complex.exp
          ((((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) * z) := by
  have hc : (2 * Real.pi : ℝ) ≠ 0 :=
    mul_ne_zero (by norm_num) Real.pi_ne_zero
  rw [weilFiniteDictionaryScaledKernel, weilFiniteDictionaryLogWeight]
  have hcoord : (2 * Real.pi * ξ) / (2 * Real.pi) = ξ := by
    field_simp [hc]
  rw [hcoord]
  have harg :
      (Complex.I * z) * (((2 * Real.pi) * ξ : ℝ) : ℂ) =
        ((((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) * z) := by
    ring
  rw [harg]
  push_cast
  field_simp [hc]

theorem interval_weilFiniteDictionaryScaledKernel_eq_test
    (C N : ℕ) (u : Fin (2 * N + 1) → ℝ) (z : ℂ) :
    (∫ x : ℝ in
        (2 * Real.pi) * (-weilFiniteDictionaryBandwidth C)..
          (2 * Real.pi) * weilFiniteDictionaryBandwidth C,
        weilFiniteDictionaryScaledKernel C N u z x) =
      weilFiniteDictionaryTest C N u z := by
  let c : ℝ := 2 * Real.pi
  let Δ : ℝ := weilFiniteDictionaryBandwidth C
  have hsub := intervalIntegral.smul_integral_comp_mul_left
    (fun x : ℝ => weilFiniteDictionaryScaledKernel C N u z x)
    (a := -Δ) (b := Δ) c
  calc
    (∫ x : ℝ in c * (-Δ)..c * Δ,
        weilFiniteDictionaryScaledKernel C N u z x) =
        c • ∫ ξ : ℝ in -Δ..Δ,
          weilFiniteDictionaryScaledKernel C N u z (c * ξ) := hsub.symm
    _ = ∫ ξ : ℝ in -Δ..Δ,
        ((c : ℂ) * weilFiniteDictionaryScaledKernel C N u z (c * ξ)) := by
      rw [intervalIntegral.integral_const_mul]
      rfl
    _ = ∫ ξ : ℝ in -Δ..Δ,
        (weilFiniteDictionaryFourierWeight C N u ξ : ℂ) *
          Complex.exp ((((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) * z) := by
      apply intervalIntegral.integral_congr
      intro ξ _
      exact weilFiniteDictionaryScaledKernel_changeOfVariables C N u z ξ
    _ = weilFiniteDictionaryTest C N u z := by
      rfl

theorem weilFiniteDictionaryTest_eq_compactLaplaceTransform
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) (z : ℂ) :
    weilFiniteDictionaryTest C N u z =
      compactLaplaceTransform (weilFiniteDictionaryPhysicalDensity C N u)
        ((1 / 2 : ℂ) + Complex.I * z) := by
  rw [compactLaplaceTransform_weilFiniteDictionaryPhysicalDensity,
    integral_weilFiniteDictionaryScaledKernel_eq_interval hC]
  exact (interval_weilFiniteDictionaryScaledKernel_eq_test C N u z).symm

theorem differentiable_weilFiniteDictionaryTest
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) :
    Differentiable ℂ (weilFiniteDictionaryTest C N u) := by
  have hLaplace :
      Differentiable ℂ
        (compactLaplaceTransform (weilFiniteDictionaryPhysicalDensity C N u)) :=
    differentiable_compactLaplaceTransform
      (continuous_weilFiniteDictionaryPhysicalDensity hC N u)
      (hasCompactSupport_weilFiniteDictionaryPhysicalDensity hC N u)
  intro z
  rw [show weilFiniteDictionaryTest C N u =
      fun w : ℂ =>
        compactLaplaceTransform (weilFiniteDictionaryPhysicalDensity C N u)
          ((1 / 2 : ℂ) + Complex.I * w) by
    funext w
    exact weilFiniteDictionaryTest_eq_compactLaplaceTransform hC N u w]
  exact (hLaplace _).comp z (by fun_prop)

theorem weilFiniteDictionaryTest_neg
    (C N : ℕ) (u : Fin (2 * N + 1) → ℝ) (z : ℂ) :
    weilFiniteDictionaryTest C N u (-z) =
      weilFiniteDictionaryTest C N u z := by
  let Δ := weilFiniteDictionaryBandwidth C
  let f : ℝ → ℂ := fun ξ =>
    (weilFiniteDictionaryFourierWeight C N u ξ : ℂ) *
      Complex.exp ((((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) * z)
  have hsub := intervalIntegral.integral_comp_neg
    (f := f) (a := -Δ) (b := Δ)
  have hpoint : ∀ ξ : ℝ,
      (weilFiniteDictionaryFourierWeight C N u ξ : ℂ) *
          Complex.exp
            ((((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) * (-z)) =
        f (-ξ) := by
    intro ξ
    dsimp only [f]
    rw [weilFiniteDictionaryFourierWeight_neg C N u ξ]
    congr 2
    push_cast
    ring
  rw [weilFiniteDictionaryTest, weilFiniteDictionaryTest]
  calc
    (∫ ξ : ℝ in -Δ..Δ,
        (weilFiniteDictionaryFourierWeight C N u ξ : ℂ) *
          Complex.exp ((((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) * (-z))) =
        ∫ ξ : ℝ in -Δ..Δ, f (-ξ) := by
      apply intervalIntegral.integral_congr
      intro ξ _
      exact hpoint ξ
    _ = ∫ ξ : ℝ in -Δ..Δ, f ξ := by
      simpa only [neg_neg] using hsub
    _ = ∫ ξ : ℝ in -Δ..Δ,
        (weilFiniteDictionaryFourierWeight C N u ξ : ℂ) *
          Complex.exp ((((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) * z) := by
      rfl

theorem weilFiniteDictionaryTest_zeroCoordinate
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) (s : ℂ) :
    weilFiniteDictionaryTest C N u ((s - 1 / 2) / Complex.I) =
      compactLaplaceTransform (weilFiniteDictionaryPhysicalDensity C N u) s := by
  rw [weilFiniteDictionaryTest_eq_compactLaplaceTransform hC]
  have harg :
      (1 / 2 : ℂ) + Complex.I * ((s - 1 / 2) / Complex.I) = s := by
    field_simp [Complex.I_ne_zero]
    ring
  rw [harg]

theorem compactLaplaceTransform_weilFiniteDictionaryPhysicalDensity_one_sub
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) (s : ℂ) :
    compactLaplaceTransform (weilFiniteDictionaryPhysicalDensity C N u) (1 - s) =
      compactLaplaceTransform (weilFiniteDictionaryPhysicalDensity C N u) s := by
  let z : ℂ := (s - 1 / 2) / Complex.I
  have hcoord :
      ((1 - s) - 1 / 2) / Complex.I = -z := by
    dsimp only [z]
    field_simp [Complex.I_ne_zero]
    ring
  calc
    compactLaplaceTransform (weilFiniteDictionaryPhysicalDensity C N u) (1 - s) =
        weilFiniteDictionaryTest C N u
          (((1 - s) - 1 / 2) / Complex.I) :=
      (weilFiniteDictionaryTest_zeroCoordinate hC N u (1 - s)).symm
    _ = weilFiniteDictionaryTest C N u (-z) := by rw [hcoord]
    _ = weilFiniteDictionaryTest C N u z :=
      weilFiniteDictionaryTest_neg C N u z
    _ = compactLaplaceTransform (weilFiniteDictionaryPhysicalDensity C N u) s := by
      exact weilFiniteDictionaryTest_zeroCoordinate hC N u s

theorem symmetrizedCompactLaplaceWeight_weilFiniteDictionaryPhysicalDensity
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) (s : ℂ) :
    symmetrizedCompactLaplaceWeight
        (weilFiniteDictionaryPhysicalDensity C N u) s =
      compactLaplaceTransform (weilFiniteDictionaryPhysicalDensity C N u) s := by
  rw [symmetrizedCompactLaplaceWeight,
    compactLaplaceTransform_weilFiniteDictionaryPhysicalDensity_one_sub hC]
  ring

theorem weilFiniteDictionaryTest_xiDivisorZero
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) (p : RiemannXiDivisorZeroIndex) :
    weilFiniteDictionaryTest C N u
        ((riemannXiDivisorZeroValue p - 1 / 2) / Complex.I) =
      symmetrizedCompactLaplaceWeight
        (weilFiniteDictionaryPhysicalDensity C N u)
          (riemannXiDivisorZeroValue p) := by
  rw [symmetrizedCompactLaplaceWeight_weilFiniteDictionaryPhysicalDensity hC]
  exact weilFiniteDictionaryTest_zeroCoordinate hC N u _

/-- The `L^1` mass of the source Fourier weight on its exact band. -/
def weilFiniteDictionaryFourierMass (C N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) : ℝ :=
  ∫ ξ : ℝ in
    -weilFiniteDictionaryBandwidth C..weilFiniteDictionaryBandwidth C,
      |weilFiniteDictionaryFourierWeight C N u ξ|

theorem weilFiniteDictionaryFourierMass_nonneg
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) :
    0 ≤ weilFiniteDictionaryFourierMass C N u := by
  unfold weilFiniteDictionaryFourierMass
  apply intervalIntegral.integral_nonneg
  · linarith [weilFiniteDictionaryBandwidth_pos hC]
  · intro ξ _
    exact abs_nonneg _

theorem norm_weilFiniteDictionaryTest_le_exp_band_mul_mass
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) (z : ℂ) :
    ‖weilFiniteDictionaryTest C N u z‖ ≤
      Real.exp
          ((2 * Real.pi * weilFiniteDictionaryBandwidth C) * ‖z‖) *
        weilFiniteDictionaryFourierMass C N u := by
  let Δ : ℝ := weilFiniteDictionaryBandwidth C
  let E : ℝ := Real.exp ((2 * Real.pi * Δ) * ‖z‖)
  have hΔ : 0 < Δ := weilFiniteDictionaryBandwidth_pos hC
  have hc : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hab : -Δ ≤ Δ := by linarith
  have hmajorInt : IntervalIntegrable
      (fun ξ : ℝ => E * |weilFiniteDictionaryFourierWeight C N u ξ|)
      volume (-Δ) Δ := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul
      (continuous_abs.comp
        (continuous_weilFiniteDictionaryFourierWeight hC N u))
  have hpoint : ∀ ξ ∈ Ioc (-Δ) Δ,
      ‖(weilFiniteDictionaryFourierWeight C N u ξ : ℂ) *
          Complex.exp ((((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) * z)‖ ≤
        E * |weilFiniteDictionaryFourierWeight C N u ξ| := by
    intro ξ hξ
    have hξIcc : ξ ∈ Icc (-Δ) Δ := by
      exact ⟨hξ.1.le, hξ.2⟩
    have hξabs : |ξ| ≤ Δ := (abs_le).2 hξIcc
    have hre :
        (((((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) * z).re) =
          -(2 * Real.pi * ξ) * z.im := by
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero,
        mul_one]
      ring
    have hexp :
        Real.exp
            (((((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) * z).re) ≤ E := by
      rw [hre]
      apply Real.exp_le_exp.mpr
      calc
        -(2 * Real.pi * ξ) * z.im ≤
            |2 * Real.pi * ξ| * |z.im| := by
          calc
            -(2 * Real.pi * ξ) * z.im ≤
                |-(2 * Real.pi * ξ) * z.im| := le_abs_self _
            _ = |2 * Real.pi * ξ| * |z.im| := by
              rw [abs_mul, abs_neg]
        _ ≤ (2 * Real.pi * Δ) * ‖z‖ := by
          rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
            abs_of_pos Real.pi_pos]
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left hξabs hc.le)
            (abs_im_le_norm z) (abs_nonneg _) (mul_nonneg hc.le hΔ.le)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    calc
      |weilFiniteDictionaryFourierWeight C N u ξ| *
          Real.exp
            (((((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) * z).re) ≤
          |weilFiniteDictionaryFourierWeight C N u ξ| * E :=
        mul_le_mul_of_nonneg_left hexp (abs_nonneg _)
      _ = E * |weilFiniteDictionaryFourierWeight C N u ξ| := by ring
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le hab
    (by filter_upwards with ξ hξ; exact hpoint ξ hξ) hmajorInt
  rw [weilFiniteDictionaryTest]
  calc
    ‖∫ ξ : ℝ in -Δ..Δ,
        (weilFiniteDictionaryFourierWeight C N u ξ : ℂ) *
          Complex.exp ((((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) * z)‖ ≤
        ∫ ξ : ℝ in -Δ..Δ,
          E * |weilFiniteDictionaryFourierWeight C N u ξ| := hnorm
    _ = E * weilFiniteDictionaryFourierMass C N u := by
      rw [intervalIntegral.integral_const_mul]
      rfl
    _ = Real.exp
          ((2 * Real.pi * weilFiniteDictionaryBandwidth C) * ‖z‖) *
        weilFiniteDictionaryFourierMass C N u := by
      rfl

theorem norm_weilFiniteDictionaryTest_le_exp_log_mul_mass
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) (z : ℂ) :
    ‖weilFiniteDictionaryTest C N u z‖ ≤
      Real.exp (Real.log C * ‖z‖) *
        weilFiniteDictionaryFourierMass C N u := by
  have hwidth :
      2 * Real.pi * weilFiniteDictionaryBandwidth C = Real.log C := by
    rw [weilFiniteDictionaryBandwidth]
    field_simp [Real.pi_ne_zero]
  simpa only [hwidth] using
    norm_weilFiniteDictionaryTest_le_exp_band_mul_mass hC N u z

/-- The smooth positive-half branch before extension by zero at the Fourier boundary. -/
def weilFiniteDictionaryRightBranch (C N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) (ξ : ℝ) : ℂ :=
  (Real.pi *
    (weilFiniteVolterraKernel N u
      (1 - ξ / weilFiniteDictionaryBandwidth C)).re : ℝ)

/-- The reflected smooth negative-half branch. -/
def weilFiniteDictionaryLeftBranch (C N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) (ξ : ℝ) : ℂ :=
  weilFiniteDictionaryRightBranch C N u (-ξ)

theorem contDiff_weilFiniteDictionaryRightBranch
    (C N : ℕ) (u : Fin (2 * N + 1) → ℝ) :
    ContDiff ℝ ∞ (weilFiniteDictionaryRightBranch C N u) := by
  let chord : ℝ → ℝ :=
    fun ξ => 1 - ξ / weilFiniteDictionaryBandwidth C
  have hchord : ContDiff ℝ ∞ chord := by
    dsimp only [chord]
    exact contDiff_const.sub (contDiff_id.div_const _)
  have hkernel : ContDiff ℝ ∞
      (fun ξ => weilFiniteVolterraKernel N u (chord ξ)) :=
    (contDiff_weilFiniteVolterraKernel N u).comp hchord
  have hre : ContDiff ℝ ∞
      (fun ξ => (weilFiniteVolterraKernel N u (chord ξ)).re) :=
    Complex.reCLM.contDiff.comp hkernel
  unfold weilFiniteDictionaryRightBranch
  exact Complex.ofRealCLM.contDiff.comp (contDiff_const.mul hre)

theorem contDiff_weilFiniteDictionaryLeftBranch
    (C N : ℕ) (u : Fin (2 * N + 1) → ℝ) :
    ContDiff ℝ ∞ (weilFiniteDictionaryLeftBranch C N u) := by
  unfold weilFiniteDictionaryLeftBranch
  exact (contDiff_weilFiniteDictionaryRightBranch C N u).comp contDiff_id.neg

theorem weilFiniteDictionaryFourierWeight_eq_rightBranch
    {C : ℕ} (_hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) {ξ : ℝ}
    (hξ0 : 0 ≤ ξ) (hξΔ : ξ ≤ weilFiniteDictionaryBandwidth C) :
    (weilFiniteDictionaryFourierWeight C N u ξ : ℂ) =
      weilFiniteDictionaryRightBranch C N u ξ := by
  have hband : |ξ| ≤ weilFiniteDictionaryBandwidth C := by
    rw [abs_of_nonneg hξ0]
    exact hξΔ
  rw [weilFiniteDictionaryFourierWeight, if_pos hband]
  simp only [abs_of_nonneg hξ0, weilFiniteDictionaryRightBranch, ofReal_mul]

theorem weilFiniteDictionaryFourierWeight_eq_leftBranch
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) {ξ : ℝ}
    (hξΔ : -weilFiniteDictionaryBandwidth C ≤ ξ) (hξ0 : ξ ≤ 0) :
    (weilFiniteDictionaryFourierWeight C N u ξ : ℂ) =
      weilFiniteDictionaryLeftBranch C N u ξ := by
  have hneg0 : 0 ≤ -ξ := neg_nonneg.mpr hξ0
  have hnegΔ : -ξ ≤ weilFiniteDictionaryBandwidth C := by linarith
  calc
    (weilFiniteDictionaryFourierWeight C N u ξ : ℂ) =
        (weilFiniteDictionaryFourierWeight C N u (-ξ) : ℂ) := by
      rw [weilFiniteDictionaryFourierWeight_neg C N u ξ]
    _ = weilFiniteDictionaryRightBranch C N u (-ξ) :=
      weilFiniteDictionaryFourierWeight_eq_rightBranch hC N u hneg0 hnegΔ
    _ = weilFiniteDictionaryLeftBranch C N u ξ := rfl

@[simp]
theorem weilFiniteDictionaryRightBranch_bandwidth
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) :
    weilFiniteDictionaryRightBranch C N u
      (weilFiniteDictionaryBandwidth C) = 0 := by
  have hΔne : weilFiniteDictionaryBandwidth C ≠ 0 :=
    (weilFiniteDictionaryBandwidth_pos hC).ne'
  rw [weilFiniteDictionaryRightBranch]
  have hchord :
      1 - weilFiniteDictionaryBandwidth C /
        weilFiniteDictionaryBandwidth C = 0 := by
    field_simp [hΔne]
    ring
  rw [hchord, weilFiniteVolterraKernel_zero]
  simp

@[simp]
theorem weilFiniteDictionaryLeftBranch_neg_bandwidth
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) :
    weilFiniteDictionaryLeftBranch C N u
      (-weilFiniteDictionaryBandwidth C) = 0 := by
  rw [weilFiniteDictionaryLeftBranch, neg_neg]
  exact weilFiniteDictionaryRightBranch_bandwidth hC N u

@[simp]
theorem weilFiniteDictionaryLeftBranch_zero
    (C N : ℕ) (u : Fin (2 * N + 1) → ℝ) :
    weilFiniteDictionaryLeftBranch C N u 0 =
      weilFiniteDictionaryRightBranch C N u 0 := by
  simp [weilFiniteDictionaryLeftBranch]

/-- The complex frequency parameter in the source Fourier integral. -/
def weilFiniteDictionaryFrequencyParameter (z : ℂ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ) * Complex.I) * z

theorem weilFiniteDictionaryTest_eq_branch_integrals
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) (z : ℂ) :
    weilFiniteDictionaryTest C N u z =
      (∫ ξ : ℝ in -weilFiniteDictionaryBandwidth C..0,
        weilFiniteDictionaryLeftBranch C N u ξ *
          Complex.exp
            (weilFiniteDictionaryFrequencyParameter z * (ξ : ℂ))) +
      ∫ ξ : ℝ in 0..weilFiniteDictionaryBandwidth C,
        weilFiniteDictionaryRightBranch C N u ξ *
          Complex.exp
            (weilFiniteDictionaryFrequencyParameter z * (ξ : ℂ)) := by
  let Δ : ℝ := weilFiniteDictionaryBandwidth C
  let q : ℝ → ℂ := fun ξ =>
    (weilFiniteDictionaryFourierWeight C N u ξ : ℂ) *
      Complex.exp ((((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) * z)
  have hqcont : Continuous q := by
    dsimp only [q]
    exact (Complex.continuous_ofReal.comp
      (continuous_weilFiniteDictionaryFourierWeight hC N u)).mul
        (Complex.continuous_exp.comp (by fun_prop))
  have hleftInt : IntervalIntegrable q volume (-Δ) 0 :=
    hqcont.intervalIntegrable (μ := volume) (-Δ) 0
  have hrightInt : IntervalIntegrable q volume 0 Δ :=
    hqcont.intervalIntegrable (μ := volume) 0 Δ
  have hsplit :=
    intervalIntegral.integral_add_adjacent_intervals hleftInt hrightInt
  have hexp (ξ : ℝ) :
      ((((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) * z) =
        weilFiniteDictionaryFrequencyParameter z * (ξ : ℂ) := by
    rw [weilFiniteDictionaryFrequencyParameter]
    push_cast
    ring
  rw [weilFiniteDictionaryTest]
  calc
    (∫ ξ : ℝ in -Δ..Δ, q ξ) =
        (∫ ξ : ℝ in -Δ..0, q ξ) +
          ∫ ξ : ℝ in 0..Δ, q ξ := hsplit.symm
    _ = (∫ ξ : ℝ in -Δ..0,
          weilFiniteDictionaryLeftBranch C N u ξ *
            Complex.exp
              (weilFiniteDictionaryFrequencyParameter z * (ξ : ℂ))) +
        ∫ ξ : ℝ in 0..Δ,
          weilFiniteDictionaryRightBranch C N u ξ *
            Complex.exp
              (weilFiniteDictionaryFrequencyParameter z * (ξ : ℂ)) := by
      congr 1
      · apply intervalIntegral.integral_congr
        intro ξ hξ
        rw [uIcc_of_le (by linarith [weilFiniteDictionaryBandwidth_pos hC])] at hξ
        dsimp only [q]
        rw [weilFiniteDictionaryFourierWeight_eq_leftBranch hC N u hξ.1 hξ.2,
          hexp]
      · apply intervalIntegral.integral_congr
        intro ξ hξ
        rw [uIcc_of_le (weilFiniteDictionaryBandwidth_pos hC).le] at hξ
        dsimp only [q]
        rw [weilFiniteDictionaryFourierWeight_eq_rightBranch hC N u hξ.1 hξ.2,
          hexp]

/-- The derivative-jump boundary contribution after two half-band integrations by parts. -/
def weilFiniteDictionaryDerivativeBoundary (C N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) (z : ℂ) : ℂ :=
  (deriv (weilFiniteDictionaryLeftBranch C N u) 0 -
      deriv (weilFiniteDictionaryLeftBranch C N u)
        (-weilFiniteDictionaryBandwidth C) *
        Complex.exp
          (weilFiniteDictionaryFrequencyParameter z *
            ((-weilFiniteDictionaryBandwidth C : ℝ) : ℂ))) +
    (deriv (weilFiniteDictionaryRightBranch C N u)
        (weilFiniteDictionaryBandwidth C) *
        Complex.exp
          (weilFiniteDictionaryFrequencyParameter z *
            (weilFiniteDictionaryBandwidth C : ℂ)) -
      deriv (weilFiniteDictionaryRightBranch C N u) 0)

/-- The two smooth second-derivative integrals left after the boundary jumps. -/
def weilFiniteDictionarySecondDerivativeIntegral (C N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) (z : ℂ) : ℂ :=
  (∫ ξ : ℝ in -weilFiniteDictionaryBandwidth C..0,
      deriv (deriv (weilFiniteDictionaryLeftBranch C N u)) ξ *
        Complex.exp
          (weilFiniteDictionaryFrequencyParameter z * (ξ : ℂ))) +
    ∫ ξ : ℝ in 0..weilFiniteDictionaryBandwidth C,
      deriv (deriv (weilFiniteDictionaryRightBranch C N u)) ξ *
        Complex.exp
          (weilFiniteDictionaryFrequencyParameter z * (ξ : ℂ))

theorem frequencyParameter_sq_mul_weilFiniteDictionaryTest
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) (z : ℂ) :
    weilFiniteDictionaryFrequencyParameter z ^ 2 *
        weilFiniteDictionaryTest C N u z =
      -weilFiniteDictionaryDerivativeBoundary C N u z +
        weilFiniteDictionarySecondDerivativeIntegral C N u z := by
  let Δ : ℝ := weilFiniteDictionaryBandwidth C
  let s : ℂ := weilFiniteDictionaryFrequencyParameter z
  let hl : ℝ → ℂ := weilFiniteDictionaryLeftBranch C N u
  let hr : ℝ → ℂ := weilFiniteDictionaryRightBranch C N u
  have hleftSmooth : ContDiff ℝ 2 hl :=
    (contDiff_weilFiniteDictionaryLeftBranch C N u).of_le
      (WithTop.coe_le_coe.mpr (OrderTop.le_top (2 : ℕ∞)))
  have hrightSmooth : ContDiff ℝ 2 hr :=
    (contDiff_weilFiniteDictionaryRightBranch C N u).of_le
      (WithTop.coe_le_coe.mpr (OrderTop.le_top (2 : ℕ∞)))
  have hleft := sq_mul_intervalIntegral_mul_cexp_eq
    hleftSmooth (-Δ) 0 s
  have hright := sq_mul_intervalIntegral_mul_cexp_eq
    hrightSmooth 0 Δ s
  have hlband : hl (-Δ) = 0 := by
    dsimp only [hl, Δ]
    exact weilFiniteDictionaryLeftBranch_neg_bandwidth hC N u
  have hrband : hr Δ = 0 := by
    dsimp only [hr, Δ]
    exact weilFiniteDictionaryRightBranch_bandwidth hC N u
  have hlzero : hl 0 = hr 0 := by
    dsimp only [hl, hr]
    exact weilFiniteDictionaryLeftBranch_zero C N u
  rw [hlband, hlzero] at hleft
  rw [hrband] at hright
  simp only [ofReal_zero, mul_zero, Complex.exp_zero, mul_one, zero_mul,
    sub_zero] at hleft hright
  rw [weilFiniteDictionaryTest_eq_branch_integrals hC]
  change s ^ 2 *
      ((∫ ξ : ℝ in -Δ..0, hl ξ * Complex.exp (s * (ξ : ℂ))) +
        ∫ ξ : ℝ in 0..Δ, hr ξ * Complex.exp (s * (ξ : ℂ))) = _
  calc
    s ^ 2 *
        ((∫ ξ : ℝ in -Δ..0, hl ξ * Complex.exp (s * (ξ : ℂ))) +
          ∫ ξ : ℝ in 0..Δ, hr ξ * Complex.exp (s * (ξ : ℂ))) =
        s ^ 2 * (∫ ξ : ℝ in -Δ..0,
          hl ξ * Complex.exp (s * (ξ : ℂ))) +
        s ^ 2 * (∫ ξ : ℝ in 0..Δ,
          hr ξ * Complex.exp (s * (ξ : ℂ))) := by ring
    _ = (s * hr 0 -
          (deriv hl 0 -
            deriv hl (-Δ) * Complex.exp (s * ((-Δ : ℝ) : ℂ))) +
          ∫ ξ : ℝ in -Δ..0,
            deriv (deriv hl) ξ * Complex.exp (s * (ξ : ℂ))) +
        (-s * hr 0 -
          (deriv hr Δ * Complex.exp (s * (Δ : ℂ)) -
            deriv hr 0) +
          ∫ ξ : ℝ in 0..Δ,
            deriv (deriv hr) ξ * Complex.exp (s * (ξ : ℂ))) := by
      rw [hleft, hright]
      ring
    _ = -weilFiniteDictionaryDerivativeBoundary C N u z +
        weilFiniteDictionarySecondDerivativeIntegral C N u z := by
      dsimp only [weilFiniteDictionaryDerivativeBoundary,
        weilFiniteDictionarySecondDerivativeIntegral, hl, hr, Δ, s]
      ring

/-- Uniform exponential envelope on a horizontal strip. -/
def weilFiniteDictionaryStripEnvelope (C : ℕ) (A : ℝ) : ℝ :=
  Real.exp
    ((2 * Real.pi * weilFiniteDictionaryBandwidth C) * A)

theorem one_le_weilFiniteDictionaryStripEnvelope
    {C : ℕ} (hC : 2 ≤ C) {A : ℝ} (hA : 0 ≤ A) :
    1 ≤ weilFiniteDictionaryStripEnvelope C A := by
  rw [weilFiniteDictionaryStripEnvelope, ← Real.exp_zero]
  apply Real.exp_le_exp.mpr
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
      (weilFiniteDictionaryBandwidth_pos hC).le) hA

theorem norm_cexp_frequencyParameter_mul_le_stripEnvelope
    {C : ℕ} (hC : 2 ≤ C) {A x : ℝ} {z : ℂ}
    (_hA : 0 ≤ A) (hx : |x| ≤ weilFiniteDictionaryBandwidth C)
    (hz : |z.im| ≤ A) :
    ‖Complex.exp
        (weilFiniteDictionaryFrequencyParameter z * (x : ℂ))‖ ≤
      weilFiniteDictionaryStripEnvelope C A := by
  have hc : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hΔ := weilFiniteDictionaryBandwidth_pos hC
  have hre :
      (weilFiniteDictionaryFrequencyParameter z * (x : ℂ)).re =
        -(2 * Real.pi * x) * z.im := by
    rw [weilFiniteDictionaryFrequencyParameter]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero,
      mul_one]
    ring
  rw [Complex.norm_exp, weilFiniteDictionaryStripEnvelope, hre]
  apply Real.exp_le_exp.mpr
  calc
    -(2 * Real.pi * x) * z.im ≤ |2 * Real.pi * x| * |z.im| := by
      calc
        -(2 * Real.pi * x) * z.im ≤
            |-(2 * Real.pi * x) * z.im| := le_abs_self _
        _ = |2 * Real.pi * x| * |z.im| := by
          rw [abs_mul, abs_neg]
    _ ≤ (2 * Real.pi * weilFiniteDictionaryBandwidth C) * A := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_pos Real.pi_pos]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hx hc.le) hz (abs_nonneg _)
        (mul_nonneg hc.le hΔ.le)

/-- Endpoint derivative size in the half-band integration-by-parts identity. -/
def weilFiniteDictionaryDerivativeSize (C N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) : ℝ :=
  ‖deriv (weilFiniteDictionaryLeftBranch C N u) 0‖ +
    ‖deriv (weilFiniteDictionaryLeftBranch C N u)
      (-weilFiniteDictionaryBandwidth C)‖ +
    ‖deriv (weilFiniteDictionaryRightBranch C N u)
      (weilFiniteDictionaryBandwidth C)‖ +
    ‖deriv (weilFiniteDictionaryRightBranch C N u) 0‖

theorem weilFiniteDictionaryDerivativeSize_nonneg
    (C N : ℕ) (u : Fin (2 * N + 1) → ℝ) :
    0 ≤ weilFiniteDictionaryDerivativeSize C N u := by
  unfold weilFiniteDictionaryDerivativeSize
  positivity

/-- Integral mass of the two smooth second derivatives. -/
def weilFiniteDictionarySecondDerivativeMass (C N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) : ℝ :=
  (∫ ξ : ℝ in -weilFiniteDictionaryBandwidth C..0,
      ‖deriv (deriv (weilFiniteDictionaryLeftBranch C N u)) ξ‖) +
    ∫ ξ : ℝ in 0..weilFiniteDictionaryBandwidth C,
      ‖deriv (deriv (weilFiniteDictionaryRightBranch C N u)) ξ‖

theorem weilFiniteDictionarySecondDerivativeMass_nonneg
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) :
    0 ≤ weilFiniteDictionarySecondDerivativeMass C N u := by
  unfold weilFiniteDictionarySecondDerivativeMass
  apply add_nonneg
  · apply intervalIntegral.integral_nonneg
    · linarith [weilFiniteDictionaryBandwidth_pos hC]
    · intro ξ _
      exact norm_nonneg _
  · apply intervalIntegral.integral_nonneg
    · exact (weilFiniteDictionaryBandwidth_pos hC).le
    · intro ξ _
      exact norm_nonneg _

/-- The full smooth/jump numerator controlling inverse-square decay. -/
def weilFiniteDictionaryDecayNumerator (C N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) : ℝ :=
  weilFiniteDictionaryDerivativeSize C N u +
    weilFiniteDictionarySecondDerivativeMass C N u

theorem weilFiniteDictionaryDecayNumerator_nonneg
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) :
    0 ≤ weilFiniteDictionaryDecayNumerator C N u :=
  add_nonneg (weilFiniteDictionaryDerivativeSize_nonneg C N u)
    (weilFiniteDictionarySecondDerivativeMass_nonneg hC N u)

theorem norm_weilFiniteDictionaryDerivativeBoundary_le
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) {A : ℝ} (hA : 0 ≤ A)
    {z : ℂ} (hz : |z.im| ≤ A) :
    ‖weilFiniteDictionaryDerivativeBoundary C N u z‖ ≤
      weilFiniteDictionaryStripEnvelope C A *
        weilFiniteDictionaryDerivativeSize C N u := by
  let Δ : ℝ := weilFiniteDictionaryBandwidth C
  let E : ℝ := weilFiniteDictionaryStripEnvelope C A
  let dl0 : ℂ := deriv (weilFiniteDictionaryLeftBranch C N u) 0
  let dlb : ℂ :=
    deriv (weilFiniteDictionaryLeftBranch C N u) (-Δ)
  let drb : ℂ :=
    deriv (weilFiniteDictionaryRightBranch C N u) Δ
  let dr0 : ℂ := deriv (weilFiniteDictionaryRightBranch C N u) 0
  let el : ℂ :=
    Complex.exp
      (weilFiniteDictionaryFrequencyParameter z * ((-Δ : ℝ) : ℂ))
  let er : ℂ :=
    Complex.exp
      (weilFiniteDictionaryFrequencyParameter z * (Δ : ℂ))
  have hE : 1 ≤ E :=
    one_le_weilFiniteDictionaryStripEnvelope hC hA
  have hel : ‖el‖ ≤ E := by
    dsimp only [el, Δ, E]
    apply norm_cexp_frequencyParameter_mul_le_stripEnvelope hC hA
    · rw [abs_neg, abs_of_pos (weilFiniteDictionaryBandwidth_pos hC)]
    · exact hz
  have her : ‖er‖ ≤ E := by
    dsimp only [er, Δ, E]
    apply norm_cexp_frequencyParameter_mul_le_stripEnvelope hC hA
    · rw [abs_of_pos (weilFiniteDictionaryBandwidth_pos hC)]
    · exact hz
  have hdlb : ‖dlb * el‖ ≤ ‖dlb‖ * E := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hel (norm_nonneg _)
  have hdrb : ‖drb * er‖ ≤ ‖drb‖ * E := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left her (norm_nonneg _)
  have hraw :
      ‖(dl0 - dlb * el) + (drb * er - dr0)‖ ≤
        (‖dl0‖ + ‖dlb * el‖) + (‖drb * er‖ + ‖dr0‖) := by
    exact (norm_add_le _ _).trans
      (add_le_add (norm_sub_le _ _) (norm_sub_le _ _))
  rw [weilFiniteDictionaryDerivativeBoundary]
  change ‖(dl0 - dlb * el) + (drb * er - dr0)‖ ≤ _
  calc
    ‖(dl0 - dlb * el) + (drb * er - dr0)‖ ≤
        (‖dl0‖ + ‖dlb * el‖) + (‖drb * er‖ + ‖dr0‖) := hraw
    _ ≤ (E * ‖dl0‖ + E * ‖dlb‖) +
        (E * ‖drb‖ + E * ‖dr0‖) := by
      apply add_le_add
      · apply add_le_add
        · simpa only [one_mul] using
            mul_le_mul_of_nonneg_right hE (norm_nonneg dl0)
        · simpa only [mul_comm] using hdlb
      · apply add_le_add
        · simpa only [mul_comm] using hdrb
        · simpa only [one_mul] using
            mul_le_mul_of_nonneg_right hE (norm_nonneg dr0)
    _ = E * weilFiniteDictionaryDerivativeSize C N u := by
      dsimp only [weilFiniteDictionaryDerivativeSize, dl0, dlb, drb, dr0, Δ, E]
      ring

theorem continuous_secondDeriv_weilFiniteDictionaryLeftBranch
    (C N : ℕ) (u : Fin (2 * N + 1) → ℝ) :
    Continuous
      (deriv (deriv (weilFiniteDictionaryLeftBranch C N u))) := by
  have h2 : ContDiff ℝ 2 (weilFiniteDictionaryLeftBranch C N u) :=
    (contDiff_weilFiniteDictionaryLeftBranch C N u).of_le
      (WithTop.coe_le_coe.mpr (OrderTop.le_top (2 : ℕ∞)))
  have h1 : ContDiff ℝ 1
      (deriv (weilFiniteDictionaryLeftBranch C N u)) := by
    simpa using h2.deriv'
  exact h1.continuous_deriv_one

theorem continuous_secondDeriv_weilFiniteDictionaryRightBranch
    (C N : ℕ) (u : Fin (2 * N + 1) → ℝ) :
    Continuous
      (deriv (deriv (weilFiniteDictionaryRightBranch C N u))) := by
  have h2 : ContDiff ℝ 2 (weilFiniteDictionaryRightBranch C N u) :=
    (contDiff_weilFiniteDictionaryRightBranch C N u).of_le
      (WithTop.coe_le_coe.mpr (OrderTop.le_top (2 : ℕ∞)))
  have h1 : ContDiff ℝ 1
      (deriv (weilFiniteDictionaryRightBranch C N u)) := by
    simpa using h2.deriv'
  exact h1.continuous_deriv_one

theorem norm_weilFiniteDictionarySecondDerivativeIntegral_le
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) {A : ℝ} (hA : 0 ≤ A)
    {z : ℂ} (hz : |z.im| ≤ A) :
    ‖weilFiniteDictionarySecondDerivativeIntegral C N u z‖ ≤
      weilFiniteDictionaryStripEnvelope C A *
        weilFiniteDictionarySecondDerivativeMass C N u := by
  let Δ : ℝ := weilFiniteDictionaryBandwidth C
  let E : ℝ := weilFiniteDictionaryStripEnvelope C A
  let ddl : ℝ → ℂ :=
    deriv (deriv (weilFiniteDictionaryLeftBranch C N u))
  let ddr : ℝ → ℂ :=
    deriv (deriv (weilFiniteDictionaryRightBranch C N u))
  have hΔ : 0 < Δ := weilFiniteDictionaryBandwidth_pos hC
  have hddlCont : Continuous ddl := by
    dsimp only [ddl]
    exact continuous_secondDeriv_weilFiniteDictionaryLeftBranch C N u
  have hddrCont : Continuous ddr := by
    dsimp only [ddr]
    exact continuous_secondDeriv_weilFiniteDictionaryRightBranch C N u
  have hleftMajorInt : IntervalIntegrable
      (fun ξ : ℝ => E * ‖ddl ξ‖) volume (-Δ) 0 := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul hddlCont.norm
  have hrightMajorInt : IntervalIntegrable
      (fun ξ : ℝ => E * ‖ddr ξ‖) volume 0 Δ := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul hddrCont.norm
  have hleftPoint : ∀ ξ ∈ Ioc (-Δ) 0,
      ‖ddl ξ *
          Complex.exp
            (weilFiniteDictionaryFrequencyParameter z * (ξ : ℂ))‖ ≤
        E * ‖ddl ξ‖ := by
    intro ξ hξ
    have hξabs : |ξ| ≤ Δ :=
      (abs_le).2 ⟨hξ.1.le, hξ.2.trans hΔ.le⟩
    have hexp : ‖Complex.exp
        (weilFiniteDictionaryFrequencyParameter z * (ξ : ℂ))‖ ≤ E := by
      dsimp only [E, Δ]
      exact norm_cexp_frequencyParameter_mul_le_stripEnvelope hC hA hξabs hz
    rw [norm_mul]
    calc
      ‖ddl ξ‖ *
          ‖Complex.exp
            (weilFiniteDictionaryFrequencyParameter z * (ξ : ℂ))‖ ≤
          ‖ddl ξ‖ * E :=
        mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
      _ = E * ‖ddl ξ‖ := by ring
  have hrightPoint : ∀ ξ ∈ Ioc 0 Δ,
      ‖ddr ξ *
          Complex.exp
            (weilFiniteDictionaryFrequencyParameter z * (ξ : ℂ))‖ ≤
        E * ‖ddr ξ‖ := by
    intro ξ hξ
    have hξabs : |ξ| ≤ Δ :=
      (abs_le).2
        ⟨(neg_nonpos.mpr hΔ.le).trans hξ.1.le, hξ.2⟩
    have hexp : ‖Complex.exp
        (weilFiniteDictionaryFrequencyParameter z * (ξ : ℂ))‖ ≤ E := by
      dsimp only [E, Δ]
      exact norm_cexp_frequencyParameter_mul_le_stripEnvelope hC hA hξabs hz
    rw [norm_mul]
    calc
      ‖ddr ξ‖ *
          ‖Complex.exp
            (weilFiniteDictionaryFrequencyParameter z * (ξ : ℂ))‖ ≤
          ‖ddr ξ‖ * E :=
        mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
      _ = E * ‖ddr ξ‖ := by ring
  have hleft := intervalIntegral.norm_integral_le_of_norm_le
    (show -Δ ≤ 0 by linarith)
    (by filter_upwards with ξ hξ; exact hleftPoint ξ hξ)
    hleftMajorInt
  have hright := intervalIntegral.norm_integral_le_of_norm_le hΔ.le
    (by filter_upwards with ξ hξ; exact hrightPoint ξ hξ)
    hrightMajorInt
  rw [weilFiniteDictionarySecondDerivativeIntegral]
  change ‖(∫ ξ : ℝ in -Δ..0,
      ddl ξ * Complex.exp (weilFiniteDictionaryFrequencyParameter z * (ξ : ℂ))) +
    ∫ ξ : ℝ in 0..Δ,
      ddr ξ * Complex.exp
        (weilFiniteDictionaryFrequencyParameter z * (ξ : ℂ))‖ ≤ _
  calc
    ‖(∫ ξ : ℝ in -Δ..0,
        ddl ξ * Complex.exp
          (weilFiniteDictionaryFrequencyParameter z * (ξ : ℂ))) +
      ∫ ξ : ℝ in 0..Δ,
        ddr ξ * Complex.exp
          (weilFiniteDictionaryFrequencyParameter z * (ξ : ℂ))‖ ≤
        ‖∫ ξ : ℝ in -Δ..0,
          ddl ξ * Complex.exp
            (weilFiniteDictionaryFrequencyParameter z * (ξ : ℂ))‖ +
        ‖∫ ξ : ℝ in 0..Δ,
          ddr ξ * Complex.exp
            (weilFiniteDictionaryFrequencyParameter z * (ξ : ℂ))‖ :=
      norm_add_le _ _
    _ ≤ (∫ ξ : ℝ in -Δ..0, E * ‖ddl ξ‖) +
        ∫ ξ : ℝ in 0..Δ, E * ‖ddr ξ‖ :=
      add_le_add hleft hright
    _ = E * weilFiniteDictionarySecondDerivativeMass C N u := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
      dsimp only [weilFiniteDictionarySecondDerivativeMass, ddl, ddr, Δ, E]
      ring

theorem norm_weilFiniteDictionaryDecayRhs_le
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) {A : ℝ} (hA : 0 ≤ A)
    {z : ℂ} (hz : |z.im| ≤ A) :
    ‖-weilFiniteDictionaryDerivativeBoundary C N u z +
        weilFiniteDictionarySecondDerivativeIntegral C N u z‖ ≤
      weilFiniteDictionaryStripEnvelope C A *
        weilFiniteDictionaryDecayNumerator C N u := by
  have hboundary :=
    norm_weilFiniteDictionaryDerivativeBoundary_le hC N u hA hz
  have hintegral :=
    norm_weilFiniteDictionarySecondDerivativeIntegral_le hC N u hA hz
  calc
    ‖-weilFiniteDictionaryDerivativeBoundary C N u z +
        weilFiniteDictionarySecondDerivativeIntegral C N u z‖ ≤
      ‖weilFiniteDictionaryDerivativeBoundary C N u z‖ +
        ‖weilFiniteDictionarySecondDerivativeIntegral C N u z‖ := by
      simpa only [norm_neg] using
        norm_add_le
          (-weilFiniteDictionaryDerivativeBoundary C N u z)
          (weilFiniteDictionarySecondDerivativeIntegral C N u z)
    _ ≤ weilFiniteDictionaryStripEnvelope C A *
          weilFiniteDictionaryDerivativeSize C N u +
        weilFiniteDictionaryStripEnvelope C A *
          weilFiniteDictionarySecondDerivativeMass C N u :=
      add_le_add hboundary hintegral
    _ = weilFiniteDictionaryStripEnvelope C A *
        weilFiniteDictionaryDecayNumerator C N u := by
      rw [weilFiniteDictionaryDecayNumerator]
      ring

theorem norm_weilFiniteDictionaryFrequencyParameter
    (z : ℂ) :
    ‖weilFiniteDictionaryFrequencyParameter z‖ =
      (2 * Real.pi) * ‖z‖ := by
  rw [weilFiniteDictionaryFrequencyParameter, norm_mul, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos
      (mul_pos (by norm_num) Real.pi_pos), Complex.norm_I]
  ring

theorem norm_weilFiniteDictionaryTest_le_inv_sq
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) {A : ℝ} (hA : 0 ≤ A)
    {z : ℂ} (hz : |z.im| ≤ A) (hz0 : z ≠ 0) :
    ‖weilFiniteDictionaryTest C N u z‖ ≤
      (weilFiniteDictionaryStripEnvelope C A *
        weilFiniteDictionaryDecayNumerator C N u) /
          ((2 * Real.pi * ‖z‖) ^ (2 : ℕ)) := by
  let s : ℂ := weilFiniteDictionaryFrequencyParameter z
  have hs0 : s ≠ 0 := by
    unfold s weilFiniteDictionaryFrequencyParameter
    exact mul_ne_zero
      (mul_ne_zero
        (Complex.ofReal_ne_zero.mpr
          (mul_ne_zero (by norm_num) Real.pi_ne_zero))
        Complex.I_ne_zero) hz0
  have hden :
      ‖s ^ (2 : ℕ)‖ = (2 * Real.pi * ‖z‖) ^ (2 : ℕ) := by
    rw [norm_pow, norm_weilFiniteDictionaryFrequencyParameter]
  have hdenPos : 0 < (2 * Real.pi * ‖z‖) ^ (2 : ℕ) := by
    apply pow_pos
    exact mul_pos (mul_pos (by norm_num) Real.pi_pos)
      (norm_pos_iff.mpr hz0)
  have hident :=
    frequencyParameter_sq_mul_weilFiniteDictionaryTest hC N u z
  have hrhs :=
    norm_weilFiniteDictionaryDecayRhs_le hC N u hA hz
  have hmul :
      (2 * Real.pi * ‖z‖) ^ (2 : ℕ) *
          ‖weilFiniteDictionaryTest C N u z‖ ≤
        weilFiniteDictionaryStripEnvelope C A *
          weilFiniteDictionaryDecayNumerator C N u := by
    rw [← hden, ← norm_mul, hident]
    exact hrhs
  apply (le_div_iff₀ hdenPos).2
  simpa only [mul_comm] using hmul

theorem norm_weilFiniteDictionaryTest_le_stripMass
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) {A : ℝ} (hA : 0 ≤ A)
    {z : ℂ} (hz : |z.im| ≤ A) :
    ‖weilFiniteDictionaryTest C N u z‖ ≤
      weilFiniteDictionaryStripEnvelope C A *
        weilFiniteDictionaryFourierMass C N u := by
  let Δ : ℝ := weilFiniteDictionaryBandwidth C
  let E : ℝ := weilFiniteDictionaryStripEnvelope C A
  have hΔ : 0 < Δ := weilFiniteDictionaryBandwidth_pos hC
  have hmajorInt : IntervalIntegrable
      (fun ξ : ℝ =>
        E * |weilFiniteDictionaryFourierWeight C N u ξ|)
      volume (-Δ) Δ := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul
      (continuous_abs.comp
        (continuous_weilFiniteDictionaryFourierWeight hC N u))
  have hpoint : ∀ ξ ∈ Ioc (-Δ) Δ,
      ‖(weilFiniteDictionaryFourierWeight C N u ξ : ℂ) *
          Complex.exp
            (weilFiniteDictionaryFrequencyParameter z * (ξ : ℂ))‖ ≤
        E * |weilFiniteDictionaryFourierWeight C N u ξ| := by
    intro ξ hξ
    have hξabs : |ξ| ≤ Δ := (abs_le).2 ⟨hξ.1.le, hξ.2⟩
    have hexp :
        ‖Complex.exp
          (weilFiniteDictionaryFrequencyParameter z * (ξ : ℂ))‖ ≤ E := by
      dsimp only [E, Δ]
      exact norm_cexp_frequencyParameter_mul_le_stripEnvelope hC hA hξabs hz
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      |weilFiniteDictionaryFourierWeight C N u ξ| *
          ‖Complex.exp
            (weilFiniteDictionaryFrequencyParameter z * (ξ : ℂ))‖ ≤
        |weilFiniteDictionaryFourierWeight C N u ξ| * E :=
          mul_le_mul_of_nonneg_left hexp (abs_nonneg _)
      _ = E * |weilFiniteDictionaryFourierWeight C N u ξ| := by ring
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le
    (show -Δ ≤ Δ by linarith)
    (by filter_upwards with ξ hξ; exact hpoint ξ hξ) hmajorInt
  rw [weilFiniteDictionaryTest]
  have hexp (ξ : ℝ) :
      ((((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) * z) =
        weilFiniteDictionaryFrequencyParameter z * (ξ : ℂ) := by
    rw [weilFiniteDictionaryFrequencyParameter]
    push_cast
    ring
  simp_rw [hexp]
  calc
    ‖∫ ξ : ℝ in -Δ..Δ,
        (weilFiniteDictionaryFourierWeight C N u ξ : ℂ) *
          Complex.exp
            (weilFiniteDictionaryFrequencyParameter z * (ξ : ℂ))‖ ≤
      ∫ ξ : ℝ in -Δ..Δ,
        E * |weilFiniteDictionaryFourierWeight C N u ξ| := hnorm
    _ = E * weilFiniteDictionaryFourierMass C N u := by
      rw [intervalIntegral.integral_const_mul]
      rfl

/-- A source-faithful constant for uniform inverse-square decay on one horizontal strip. -/
def weilFiniteDictionaryStripDecayConstant (C N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) (A : ℝ) : ℝ :=
  4 * max
    (weilFiniteDictionaryStripEnvelope C A *
      weilFiniteDictionaryFourierMass C N u)
    ((weilFiniteDictionaryStripEnvelope C A *
      weilFiniteDictionaryDecayNumerator C N u) /
        ((2 * Real.pi) ^ (2 : ℕ)))

theorem weilFiniteDictionaryStripDecayConstant_nonneg
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) {A : ℝ} (_hA : 0 ≤ A) :
    0 ≤ weilFiniteDictionaryStripDecayConstant C N u A := by
  have hE : 0 ≤ weilFiniteDictionaryStripEnvelope C A := by
    unfold weilFiniteDictionaryStripEnvelope
    positivity
  have hmass := weilFiniteDictionaryFourierMass_nonneg hC N u
  have hnum := weilFiniteDictionaryDecayNumerator_nonneg hC N u
  unfold weilFiniteDictionaryStripDecayConstant
  positivity

theorem norm_weilFiniteDictionaryTest_le_stripDecay_div
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) {A : ℝ} (hA : 0 ≤ A)
    {z : ℂ} (hz : |z.im| ≤ A) :
    ‖weilFiniteDictionaryTest C N u z‖ ≤
      weilFiniteDictionaryStripDecayConstant C N u A /
        (1 + |z.re|) ^ (2 : ℕ) := by
  let E : ℝ := weilFiniteDictionaryStripEnvelope C A
  let B : ℝ := E * weilFiniteDictionaryFourierMass C N u
  let K : ℝ := E * weilFiniteDictionaryDecayNumerator C N u
  let c : ℝ := 2 * Real.pi
  let D : ℝ := K / (c ^ (2 : ℕ))
  let M : ℝ := 4 * max B D
  let r : ℝ := |z.re|
  let t : ℝ := 1 + r
  have hc : 0 < c := mul_pos (by norm_num) Real.pi_pos
  have hE : 0 ≤ E := by
    dsimp only [E, weilFiniteDictionaryStripEnvelope]
    positivity
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg hE (weilFiniteDictionaryFourierMass_nonneg hC N u)
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg hE (weilFiniteDictionaryDecayNumerator_nonneg hC N u)
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  have hr : 0 ≤ r := by
    dsimp only [r]
    positivity
  have ht : 0 < t := by
    dsimp only [t]
    linarith
  have hM_B : 4 * B ≤ M := by
    dsimp only [M]
    exact mul_le_mul_of_nonneg_left (le_max_left B D) (by norm_num)
  have hM_D : 4 * D ≤ M := by
    dsimp only [M]
    exact mul_le_mul_of_nonneg_left (le_max_right B D) (by norm_num)
  change ‖weilFiniteDictionaryTest C N u z‖ ≤ M / t ^ (2 : ℕ)
  by_cases hr1 : r ≤ 1
  · have huniform :
        ‖weilFiniteDictionaryTest C N u z‖ ≤ B := by
      dsimp only [B, E]
      exact norm_weilFiniteDictionaryTest_le_stripMass hC N u hA hz
    have ht2 : t ^ (2 : ℕ) ≤ 4 := by
      have ht_le : t ≤ 2 := by
        dsimp only [t]
        linarith
      nlinarith
    have hBt : B * t ^ (2 : ℕ) ≤ M := by
      calc
        B * t ^ (2 : ℕ) ≤ B * 4 :=
          mul_le_mul_of_nonneg_left ht2 hB
        _ = 4 * B := by ring
        _ ≤ M := hM_B
    exact huniform.trans ((le_div_iff₀ (pow_pos ht 2)).2 hBt)
  · have hrpos : 0 < r := lt_trans zero_lt_one (lt_of_not_ge hr1)
    have hz0 : z ≠ 0 := by
      intro hz0
      subst z
      simp [r] at hrpos
    have hinv :
        ‖weilFiniteDictionaryTest C N u z‖ ≤
          K / ((c * ‖z‖) ^ (2 : ℕ)) := by
      dsimp only [K, c, E]
      exact norm_weilFiniteDictionaryTest_le_inv_sq hC N u hA hz hz0
    have hreNorm : r ≤ ‖z‖ := by
      dsimp only [r]
      exact abs_re_le_norm z
    have hcrPos : 0 < c * r := mul_pos hc hrpos
    have hczPos : 0 < c * ‖z‖ :=
      mul_pos hc (norm_pos_iff.mpr hz0)
    have hden :
        (c * r) ^ (2 : ℕ) ≤ (c * ‖z‖) ^ (2 : ℕ) := by
      gcongr
    have hfirst :
        K / ((c * ‖z‖) ^ (2 : ℕ)) ≤
          K / ((c * r) ^ (2 : ℕ)) :=
      div_le_div_of_nonneg_left hK (pow_pos hcrPos 2) hden
    have hKD :
        K / ((c * r) ^ (2 : ℕ)) = D / (r ^ (2 : ℕ)) := by
      dsimp only [D]
      field_simp [hc.ne', hrpos.ne']
    have ht_le : t ≤ 2 * r := by
      dsimp only [t]
      linarith [lt_of_not_ge hr1]
    have ht_sq : t ^ (2 : ℕ) ≤ 4 * r ^ (2 : ℕ) := by
      nlinarith
    have hsecond :
        D / (r ^ (2 : ℕ)) ≤
          (4 * D) / (t ^ (2 : ℕ)) := by
      calc
        D / (r ^ (2 : ℕ)) =
            (4 * D) / (4 * r ^ (2 : ℕ)) := by
          field_simp [hrpos.ne']
        _ ≤ (4 * D) / (t ^ (2 : ℕ)) :=
          div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hD)
            (pow_pos ht 2) ht_sq
    have hthird :
        (4 * D) / (t ^ (2 : ℕ)) ≤ M / (t ^ (2 : ℕ)) :=
      div_le_div_of_nonneg_right hM_D (pow_nonneg ht.le 2)
    exact hinv.trans (hfirst.trans (by rw [hKD]; exact hsecond.trans hthird))

theorem norm_weilFiniteDictionaryTest_le_stripDecay
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) {A : ℝ} (hA : 0 ≤ A)
    {z : ℂ} (hz : |z.im| ≤ A) :
    ‖weilFiniteDictionaryTest C N u z‖ ≤
      weilFiniteDictionaryStripDecayConstant C N u A *
        ((1 + |z.re|)⁻¹ ^ (2 : ℕ)) := by
  have h :=
    norm_weilFiniteDictionaryTest_le_stripDecay_div hC N u hA hz
  simpa only [div_eq_mul_inv, inv_pow] using h

@[simp]
theorem weilFiniteDictionaryZeroCoordinate_re (s : ℂ) :
    (((s - 1 / 2) / Complex.I : ℂ).re) = s.im := by
  rw [Complex.div_re]
  norm_num [Complex.normSq]

@[simp]
theorem weilFiniteDictionaryZeroCoordinate_im (s : ℂ) :
    (((s - 1 / 2) / Complex.I : ℂ).im) = 1 / 2 - s.re := by
  rw [Complex.div_im]
  norm_num [Complex.normSq]

theorem abs_weilFiniteDictionaryZeroCoordinate_im_le_half
    (p : RiemannXiDivisorZeroIndex) :
    |(((riemannXiDivisorZeroValue p - 1 / 2) / Complex.I : ℂ).im)| ≤
      1 / 2 := by
  have hp := riemannXiDivisorZeroIndex_val_isNontrivialZero p
  have hpReflect : IsNontrivialZero (1 - riemannXiDivisorZeroValue p) := by
    rw [isNontrivialZero_iff_riemannXi_eq_zero, riemannXi_one_sub]
    exact (isNontrivialZero_iff_riemannXi_eq_zero _).mp hp
  have hrePos : 0 < (riemannXiDivisorZeroValue p).re := by
    have hreflectRe := nontrivial_zero_re_lt_one hpReflect
    simp only [Complex.sub_re, Complex.one_re] at hreflectRe
    linarith
  rw [weilFiniteDictionaryZeroCoordinate_im]
  rw [abs_le]
  constructor
  · linarith [nontrivial_zero_re_lt_one hp]
  · linarith

theorem one_add_abs_im_inv_sq_le_norm_inv_sq
    (p : RiemannXiDivisorZeroIndex) :
    ((1 + |(riemannXiDivisorZeroValue p).im|)⁻¹ ^ (2 : ℕ)) ≤
      (‖riemannXiDivisorZeroValue p‖⁻¹ ^ (2 : ℕ)) := by
  let ρ : ℂ := riemannXiDivisorZeroValue p
  have hp := riemannXiDivisorZeroIndex_val_isNontrivialZero p
  have hpReflect : IsNontrivialZero (1 - ρ) := by
    rw [isNontrivialZero_iff_riemannXi_eq_zero, riemannXi_one_sub]
    exact (isNontrivialZero_iff_riemannXi_eq_zero _).mp hp
  have hrePos : 0 < ρ.re := by
    have hreflectRe := nontrivial_zero_re_lt_one hpReflect
    simp only [Complex.sub_re, Complex.one_re] at hreflectRe
    linarith
  have habsRe : |ρ.re| ≤ 1 := by
    rw [abs_of_nonneg hrePos.le]
    exact (nontrivial_zero_re_lt_one hp).le
  have hnorm :
      ‖ρ‖ ≤ 1 + |ρ.im| := by
    calc
      ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
      _ ≤ 1 + |ρ.im| := by
        simpa only [add_comm] using add_le_add_right habsRe |ρ.im|
  have hnormPos : 0 < ‖ρ‖ :=
    norm_pos_iff.mpr (Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p)
  have honePos : 0 < 1 + |ρ.im| := by positivity
  have hinv : (1 + |ρ.im|)⁻¹ ≤ ‖ρ‖⁻¹ :=
    (inv_le_inv₀ honePos hnormPos).2 hnorm
  exact pow_le_pow_left₀ (inv_nonneg.mpr (by positivity)) hinv 2

theorem norm_weilFiniteDictionaryTest_xiDivisorZero_le
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) (p : RiemannXiDivisorZeroIndex) :
    ‖weilFiniteDictionaryTest C N u
        ((riemannXiDivisorZeroValue p - 1 / 2) / Complex.I)‖ ≤
      weilFiniteDictionaryStripDecayConstant C N u (1 / 2) *
        (‖riemannXiDivisorZeroValue p‖⁻¹ ^ (2 : ℕ)) := by
  have hstrip :=
    norm_weilFiniteDictionaryTest_le_stripDecay hC N u
      (A := 1 / 2) (by norm_num)
      (abs_weilFiniteDictionaryZeroCoordinate_im_le_half p)
  have hdecay :
      ((1 +
          |(((riemannXiDivisorZeroValue p - 1 / 2) /
            Complex.I : ℂ).re)|)⁻¹ ^ (2 : ℕ)) ≤
        (‖riemannXiDivisorZeroValue p‖⁻¹ ^ (2 : ℕ)) := by
    simpa only [weilFiniteDictionaryZeroCoordinate_re] using
      one_add_abs_im_inv_sq_le_norm_inv_sq p
  exact hstrip.trans
    (mul_le_mul_of_nonneg_left hdecay
      (weilFiniteDictionaryStripDecayConstant_nonneg
        hC N u (A := 1 / 2) (by norm_num)))

theorem summable_norm_weilFiniteDictionaryTest_xiDivisorZero
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      ‖weilFiniteDictionaryTest C N u
        ((riemannXiDivisorZeroValue p - 1 / 2) / Complex.I)‖) := by
  exact
    (summable_riemannXiDivisorZeroIndex_norm_inv_sq.mul_left
      (weilFiniteDictionaryStripDecayConstant C N u (1 / 2))).of_nonneg_of_le
        (fun p => norm_nonneg _)
        (norm_weilFiniteDictionaryTest_xiDivisorZero_le hC N u)

theorem summable_weilFiniteDictionaryTest_xiDivisorZero
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      weilFiniteDictionaryTest C N u
        ((riemannXiDivisorZeroValue p - 1 / 2) / Complex.I)) :=
  (summable_norm_weilFiniteDictionaryTest_xiDivisorZero hC N u).of_norm

theorem summable_norm_symmetrizedCompactLaplaceWeight_weilFiniteDictionary
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      ‖symmetrizedCompactLaplaceWeight
        (weilFiniteDictionaryPhysicalDensity C N u)
          (riemannXiDivisorZeroValue p)‖) := by
  refine (summable_norm_weilFiniteDictionaryTest_xiDivisorZero hC N u).congr ?_
  intro p
  rw [weilFiniteDictionaryTest_xiDivisorZero hC]

theorem summable_symmetrizedCompactLaplaceWeight_weilFiniteDictionary
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      symmetrizedCompactLaplaceWeight
        (weilFiniteDictionaryPhysicalDensity C N u)
          (riemannXiDivisorZeroValue p)) :=
  (summable_norm_symmetrizedCompactLaplaceWeight_weilFiniteDictionary
    hC N u).of_norm

/-- The source-level admissibility package for one finite even-sector vector. -/
structure WeilFiniteDictionaryAdmissibilityCertificate
    (C N : ℕ) (u : Fin (2 * N + 1) → ℝ) : Prop where
  kernel_zero :
    weilFiniteVolterraKernel N u 0 = 0
  fourier_continuous :
    Continuous (weilFiniteDictionaryFourierWeight C N u)
  fourier_compactSupport :
    HasCompactSupport (weilFiniteDictionaryFourierWeight C N u)
  fourier_integrable :
    Integrable (weilFiniteDictionaryFourierWeight C N u)
  physicalDensity_continuous :
    Continuous (weilFiniteDictionaryPhysicalDensity C N u)
  physicalDensity_compactSupport :
    HasCompactSupport (weilFiniteDictionaryPhysicalDensity C N u)
  physicalDensity_integrable :
    Integrable (weilFiniteDictionaryPhysicalDensity C N u)
  test_even :
    ∀ z : ℂ,
      weilFiniteDictionaryTest C N u (-z) =
        weilFiniteDictionaryTest C N u z
  test_entire :
    Differentiable ℂ (weilFiniteDictionaryTest C N u)
  exponentialType_logC :
    ∀ z : ℂ,
      ‖weilFiniteDictionaryTest C N u z‖ ≤
        Real.exp (Real.log C * ‖z‖) *
          weilFiniteDictionaryFourierMass C N u
  exact_zeroCoordinate :
    ∀ s : ℂ,
      weilFiniteDictionaryTest C N u ((s - 1 / 2) / Complex.I) =
        compactLaplaceTransform (weilFiniteDictionaryPhysicalDensity C N u) s
  exact_projectZeroWeight :
    ∀ p : RiemannXiDivisorZeroIndex,
      weilFiniteDictionaryTest C N u
          ((riemannXiDivisorZeroValue p - 1 / 2) / Complex.I) =
        symmetrizedCompactLaplaceWeight
          (weilFiniteDictionaryPhysicalDensity C N u)
            (riemannXiDivisorZeroValue p)
  horizontalStripDecay :
    ∀ A : ℝ, 0 ≤ A →
      ∃ M : ℝ, 0 ≤ M ∧
        ∀ z : ℂ, |z.im| ≤ A →
          ‖weilFiniteDictionaryTest C N u z‖ ≤
            M * ((1 + |z.re|)⁻¹ ^ (2 : ℕ))
  zeroNormSummable :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      ‖weilFiniteDictionaryTest C N u
        ((riemannXiDivisorZeroValue p - 1 / 2) / Complex.I)‖)
  zeroSummable :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      weilFiniteDictionaryTest C N u
        ((riemannXiDivisorZeroValue p - 1 / 2) / Complex.I))
  projectZeroWeightNormSummable :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      ‖symmetrizedCompactLaplaceWeight
        (weilFiniteDictionaryPhysicalDensity C N u)
          (riemannXiDivisorZeroValue p)‖)
  projectZeroWeightSummable :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      symmetrizedCompactLaplaceWeight
        (weilFiniteDictionaryPhysicalDensity C N u)
          (riemannXiDivisorZeroValue p))

/-- Every finite even-sector vector in the literal source dictionary is admissible, with an
absolutely convergent sum over the actual multiplicity-bearing xi divisor. -/
theorem weilFiniteDictionaryAdmissibility_endpoint
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) :
    WeilFiniteDictionaryAdmissibilityCertificate C N u := by
  refine {
    kernel_zero := weilFiniteVolterraKernel_zero N u
    fourier_continuous :=
      continuous_weilFiniteDictionaryFourierWeight hC N u
    fourier_compactSupport :=
      hasCompactSupport_weilFiniteDictionaryFourierWeight hC N u
    fourier_integrable :=
      integrable_weilFiniteDictionaryFourierWeight hC N u
    physicalDensity_continuous :=
      continuous_weilFiniteDictionaryPhysicalDensity hC N u
    physicalDensity_compactSupport :=
      hasCompactSupport_weilFiniteDictionaryPhysicalDensity hC N u
    physicalDensity_integrable :=
      integrable_weilFiniteDictionaryPhysicalDensity hC N u
    test_even := weilFiniteDictionaryTest_neg C N u
    test_entire := differentiable_weilFiniteDictionaryTest hC N u
    exponentialType_logC :=
      norm_weilFiniteDictionaryTest_le_exp_log_mul_mass hC N u
    exact_zeroCoordinate :=
      weilFiniteDictionaryTest_zeroCoordinate hC N u
    exact_projectZeroWeight :=
      weilFiniteDictionaryTest_xiDivisorZero hC N u
    horizontalStripDecay := ?_
    zeroNormSummable :=
      summable_norm_weilFiniteDictionaryTest_xiDivisorZero hC N u
    zeroSummable :=
      summable_weilFiniteDictionaryTest_xiDivisorZero hC N u
    projectZeroWeightNormSummable :=
      summable_norm_symmetrizedCompactLaplaceWeight_weilFiniteDictionary
        hC N u
    projectZeroWeightSummable :=
      summable_symmetrizedCompactLaplaceWeight_weilFiniteDictionary
        hC N u }
  intro A hA
  refine
    ⟨weilFiniteDictionaryStripDecayConstant C N u A,
      weilFiniteDictionaryStripDecayConstant_nonneg hC N u hA, ?_⟩
  intro z hz
  exact norm_weilFiniteDictionaryTest_le_stripDecay hC N u hA hz

end

end LeanLab.Riemann
