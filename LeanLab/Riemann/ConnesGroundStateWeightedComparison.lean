import LeanLab.Riemann.WeilGroundStateFourierTopology
import LeanLab.Riemann.WeilGroundStateRayleighGap
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Support-sensitive comparison for the Connes ground-state route

This module converts projective ground-line control into the exponentially weighted `L¹`
topology required by `WeilGroundStateFourierTopology`.  On support `[-R, R]`, the exact
positive-strip cost is

`sqrt ((exp (2 * A * R) - 1) / A)`,

while the endpoint `A = 0` costs `sqrt (2 * R)`.  For the source radius `R = log lambda`,
the positive-strip rate is therefore controlled by `lambda ^ (2 * A)` times the projective
defect.

The final theorem is a quantitative consumer.  It does not prove that Connes' actual prolate
packet has the required Rayleigh-excess-to-gap rate.
-/

noncomputable section

open Complex Filter Function MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace LeanLab.Riemann

/-- Exact squared exponential weight mass on a symmetric support interval. -/
theorem integral_exp_sqWeight_Icc
    (A R : ℝ) (hA : 0 < A) (hR : 0 ≤ R) :
    ∫ x : ℝ in Icc (-R) R, Real.exp (2 * A * |x|) =
      (Real.exp (2 * A * R) - 1) / A := by
  have hnegR : -R ≤ R := by linarith
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le hnegR]
  have hintLeft :
      IntervalIntegrable (fun x : ℝ => Real.exp (2 * A * |x|)) volume (-R) 0 :=
    (Real.continuous_exp.comp
      (continuous_const.mul continuous_abs)).intervalIntegrable _ _
  have hintRight :
      IntervalIntegrable (fun x : ℝ => Real.exp (2 * A * |x|)) volume 0 R :=
    (Real.continuous_exp.comp
      (continuous_const.mul continuous_abs)).intervalIntegrable _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals hintLeft hintRight]
  have hleft :
      (∫ x : ℝ in -R..0, Real.exp (2 * A * |x|)) =
        ∫ x : ℝ in 0..R, Real.exp (2 * A * x) := by
    calc
      (∫ x : ℝ in -R..0, Real.exp (2 * A * |x|)) =
          ∫ x : ℝ in -R..0, Real.exp (2 * A * (-x)) := by
            apply intervalIntegral.integral_congr
            intro x hx
            rw [uIcc_of_le (by linarith : -R ≤ 0)] at hx
            change Real.exp (2 * A * |x|) = Real.exp (2 * A * (-x))
            rw [abs_of_nonpos hx.2]
      _ = ∫ x : ℝ in 0..R, Real.exp (2 * A * x) := by
            simpa using
              (intervalIntegral.integral_comp_neg
                (f := fun x : ℝ => Real.exp (2 * A * x))
                (a := -R) (b := 0))
  have hright :
      (∫ x : ℝ in 0..R, Real.exp (2 * A * |x|)) =
        ∫ x : ℝ in 0..R, Real.exp (2 * A * x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hR] at hx
    change Real.exp (2 * A * |x|) = Real.exp (2 * A * x)
    rw [abs_of_nonneg hx.1]
  rw [hleft, hright]
  have htwoA : 2 * A ≠ 0 := by positivity
  have hscaled :=
    intervalIntegral.integral_comp_mul_left
      (f := Real.exp) (a := 0) (b := R) htwoA
  simp only [integral_exp] at hscaled
  have hpos :
      (∫ x : ℝ in 0..R, Real.exp (2 * A * x)) =
        (Real.exp (2 * A * R) - 1) / (2 * A) := by
    simpa [div_eq_inv_mul, mul_assoc] using hscaled
  rw [hpos]
  field_simp [hA.ne']
  ring_nf

/-- Squared `L²` distance between two centered source-coordinate functions. -/
def connesGroundStateL2Error (f g : ℝ → ℂ) : ℝ :=
  ∫ x : ℝ, ‖f x - g x‖ ^ 2

/-- Squared `L²` norm in the centered source coordinate. -/
def connesGroundStateL2NormSq (f : ℝ → ℂ) : ℝ :=
  ∫ x : ℝ, ‖f x‖ ^ 2

/-- Real part of the source-coordinate `L²` inner product. -/
def connesGroundStateRealInner (f g : ℝ → ℂ) : ℝ :=
  ∫ x : ℝ, (f x * (starRingEnd ℂ) (g x)).re

/-- Squared projective defect for normalized source-coordinate functions. -/
def connesGroundStateProjectiveDefect (f g : ℝ → ℂ) : ℝ :=
  1 - connesGroundStateRealInner f g ^ 2

/-- Exact positive-strip squared-weight mass for support radius `R`. -/
def connesGroundStateWeightMass (A R : ℝ) : ℝ :=
  (Real.exp (2 * A * R) - 1) / A

/-- The exact weighted Hölder estimate on a common symmetric support interval. -/
theorem connesGroundStateFourierStripError_le
    (A R : ℝ) (hA : 0 < A) (hR : 0 ≤ R)
    (f g : ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g)
    (hfcompact : HasCompactSupport f) (hgcompact : HasCompactSupport g)
    (hfsupp : Function.support f ⊆ Icc (-R) R)
    (hgsupp : Function.support g ⊆ Icc (-R) R) :
    weilGroundStateFourierStripError A f g ≤
      Real.sqrt (connesGroundStateWeightMass A R) *
        Real.sqrt (connesGroundStateL2Error f g) := by
  let s : Set ℝ := Icc (-R) R
  let w : ℝ → ℝ := fun x => Real.exp (A * |x|)
  let d : ℝ → ℝ := fun x => ‖f x - g x‖
  have hsd : MeasurableSet s := measurableSet_Icc
  have hwmeas : AEStronglyMeasurable w (volume.restrict s) := by
    exact
      (Real.continuous_exp.comp
        (continuous_const.mul continuous_abs)).aestronglyMeasurable
  have hwbound : ∀ᵐ x ∂volume.restrict s, ‖w x‖ ≤ Real.exp (A * R) := by
    filter_upwards [ae_restrict_mem hsd] with x hx
    have habs : |x| ≤ R :=
      abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
    simp only [w, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left habs hA.le)
  have hwLp : MemLp w (ENNReal.ofReal 2) (volume.restrict s) :=
    MemLp.of_bound hwmeas (Real.exp (A * R)) hwbound
  have hdLpGlobal : MemLp d (ENNReal.ofReal 2) volume := by
    exact
      ((hf.sub hg).memLp_of_hasCompactSupport
        (hfcompact.sub hgcompact)).norm
  have hdLp : MemLp d (ENNReal.ofReal 2) (volume.restrict s) :=
    hdLpGlobal.mono_measure Measure.restrict_le_self
  have hholder :=
    integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := volume.restrict s) Real.HolderConjugate.two_two
      (Eventually.of_forall fun x => (Real.exp_pos _).le)
      (Eventually.of_forall fun x => norm_nonneg _)
      hwLp hdLp
  have hw2 :
      (∫ x : ℝ in s, w x ^ (2 : ℝ)) =
        connesGroundStateWeightMass A R := by
    change
      (∫ x : ℝ in Icc (-R) R,
        Real.exp (A * |x|) ^ (2 : ℝ)) =
          connesGroundStateWeightMass A R
    simp_rw [Real.rpow_two]
    unfold connesGroundStateWeightMass
    convert integral_exp_sqWeight_Icc A R hA hR using 1
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    simp only [pow_two, ← Real.exp_add]
    congr 1
    ring_nf
  have hd2 :
      (∫ x : ℝ in s, d x ^ (2 : ℝ)) =
        connesGroundStateL2Error f g := by
    have hzero : ∀ x ∉ s, d x ^ (2 : ℝ) = 0 := by
      intro x hx
      have hfx : f x = 0 := by
        by_contra hne
        exact hx (hfsupp hne)
      have hgx : g x = 0 := by
        by_contra hne
        exact hx (hgsupp hne)
      simp [d, hfx, hgx]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
    simp [connesGroundStateL2Error, d]
  have hmain :
      (∫ x : ℝ in s, w x * d x) ≤
        Real.sqrt (connesGroundStateWeightMass A R) *
          Real.sqrt (connesGroundStateL2Error f g) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← hw2, ← hd2]
    exact hholder
  have hrestrict :
      (∫ x : ℝ in s, w x * d x) =
        weilGroundStateFourierStripError A f g := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · rfl
    · intro x hx
      have hfx : f x = 0 := by
        by_contra hne
        exact hx (hfsupp hne)
      have hgx : g x = 0 := by
        by_contra hne
        exact hx (hgsupp hne)
      simp [w, d, hfx, hgx]
  rw [← hrestrict]
  exact hmain

/-- At `A = 0`, the exact support cost is the square root of the interval length. -/
theorem connesGroundStateFourierStripError_zero_le
    (R : ℝ) (hR : 0 ≤ R)
    (f g : ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g)
    (hfcompact : HasCompactSupport f) (hgcompact : HasCompactSupport g)
    (hfsupp : Function.support f ⊆ Icc (-R) R)
    (hgsupp : Function.support g ⊆ Icc (-R) R) :
    weilGroundStateFourierStripError 0 f g ≤
      Real.sqrt (2 * R) * Real.sqrt (connesGroundStateL2Error f g) := by
  let s : Set ℝ := Icc (-R) R
  let d : ℝ → ℝ := fun x => ‖f x - g x‖
  have honeLp :
      MemLp (fun _x : ℝ => (1 : ℝ)) (ENNReal.ofReal 2) (volume.restrict s) := by
    exact
      MemLp.of_bound continuous_const.aestronglyMeasurable 1
        (Eventually.of_forall fun _x => by simp)
  have hdLpGlobal : MemLp d (ENNReal.ofReal 2) volume := by
    exact
      ((hf.sub hg).memLp_of_hasCompactSupport
        (hfcompact.sub hgcompact)).norm
  have hdLp : MemLp d (ENNReal.ofReal 2) (volume.restrict s) :=
    hdLpGlobal.mono_measure Measure.restrict_le_self
  have hholder :=
    integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := volume.restrict s) Real.HolderConjugate.two_two
      (Eventually.of_forall fun _x => zero_le_one)
      (Eventually.of_forall fun x => norm_nonneg _)
      honeLp hdLp
  have hone2 :
      (∫ _x : ℝ in s, (1 : ℝ) ^ (2 : ℝ)) = 2 * R := by
    simp [s, hR]
    ring_nf
  have hd2 :
      (∫ x : ℝ in s, d x ^ (2 : ℝ)) =
        connesGroundStateL2Error f g := by
    have hzero : ∀ x ∉ s, d x ^ (2 : ℝ) = 0 := by
      intro x hx
      have hfx : f x = 0 := by
        by_contra hne
        exact hx (hfsupp hne)
      have hgx : g x = 0 := by
        by_contra hne
        exact hx (hgsupp hne)
      simp [d, hfx, hgx]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
    simp [connesGroundStateL2Error, d]
  have hmain :
      (∫ x : ℝ in s, (1 : ℝ) * d x) ≤
        Real.sqrt (2 * R) *
          Real.sqrt (connesGroundStateL2Error f g) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← hone2, ← hd2]
    exact hholder
  have hrestrict :
      (∫ x : ℝ in s, (1 : ℝ) * d x) =
        weilGroundStateFourierStripError 0 f g := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · simp [weilGroundStateFourierStripError, d]
    · intro x hx
      have hfx : f x = 0 := by
        by_contra hne
        exact hx (hfsupp hne)
      have hgx : g x = 0 := by
        by_contra hne
        exact hx (hgsupp hne)
      simp [d, hfx, hgx]
  rw [← hrestrict]
  exact hmain

/-- Polarization identity for the centered source-coordinate `L²` error. -/
theorem connesGroundStateL2Error_eq
    (f g : ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g)
    (hfcompact : HasCompactSupport f) (hgcompact : HasCompactSupport g) :
    connesGroundStateL2Error f g =
      connesGroundStateL2NormSq f + connesGroundStateL2NormSq g -
        2 * connesGroundStateRealInner f g := by
  have hfnorm :
      Integrable (fun x : ℝ => ‖f x‖ ^ 2) := by
    have hc :
        HasCompactSupport
          ((fun x : ℝ => ‖f x‖) * (fun x : ℝ => ‖f x‖)) :=
      hfcompact.norm.mul_right
    have hi :
        Integrable (fun x : ℝ => ‖f x‖ * ‖f x‖) :=
      (hf.norm.mul hf.norm).integrable_of_hasCompactSupport
        (by simpa only [Pi.mul_apply] using hc)
    simpa only [pow_two] using hi
  have hgnorm :
      Integrable (fun x : ℝ => ‖g x‖ ^ 2) := by
    have hc :
        HasCompactSupport
          ((fun x : ℝ => ‖g x‖) * (fun x : ℝ => ‖g x‖)) :=
      hgcompact.norm.mul_right
    have hi :
        Integrable (fun x : ℝ => ‖g x‖ * ‖g x‖) :=
      (hg.norm.mul hg.norm).integrable_of_hasCompactSupport
        (by simpa only [Pi.mul_apply] using hc)
    simpa only [pow_two] using hi
  have hinner :
      Integrable
        (fun x : ℝ => (f x * (starRingEnd ℂ) (g x)).re) := by
    have hcont :
        Continuous
          (fun x : ℝ => (f x * (starRingEnd ℂ) (g x)).re) := by
      fun_prop
    have hcomp :
        HasCompactSupport
          (fun x : ℝ => (f x * (starRingEnd ℂ) (g x)).re) := by
      have hp :
          HasCompactSupport
            (fun x : ℝ => f x * (starRingEnd ℂ) (g x)) := by
        change HasCompactSupport (f * fun x : ℝ => (starRingEnd ℂ) (g x))
        exact hfcompact.mul_right
      exact hp.comp_left (g := fun z : ℂ => z.re) (by simp)
    exact hcont.integrable_of_hasCompactSupport hcomp
  unfold connesGroundStateL2Error connesGroundStateL2NormSq
    connesGroundStateRealInner
  calc
    (∫ x : ℝ, ‖f x - g x‖ ^ 2) =
        ∫ x : ℝ,
          (‖f x‖ ^ 2 + ‖g x‖ ^ 2) -
            2 * (f x * (starRingEnd ℂ) (g x)).re := by
      apply integral_congr_ae
      filter_upwards with x
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
      simp only [Complex.normSq_eq_norm_sq]
    _ = (∫ x : ℝ, ‖f x‖ ^ 2 + ‖g x‖ ^ 2) -
          ∫ x : ℝ, 2 * (f x * (starRingEnd ℂ) (g x)).re := by
      rw [integral_sub]
      · exact hfnorm.add hgnorm
      · exact hinner.const_mul 2
    _ = ((∫ x : ℝ, ‖f x‖ ^ 2) + ∫ x : ℝ, ‖g x‖ ^ 2) -
          2 * ∫ x : ℝ, (f x * (starRingEnd ℂ) (g x)).re := by
      rw [integral_add hfnorm hgnorm, MeasureTheory.integral_const_mul]

/-- Coherent orientation turns normalized projective defect into actual `L²` error. -/
theorem connesGroundStateL2Error_le_two_projectiveDefect
    (f g : ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g)
    (hfcompact : HasCompactSupport f) (hgcompact : HasCompactSupport g)
    (hfnorm : connesGroundStateL2NormSq f = 1)
    (hgnorm : connesGroundStateL2NormSq g = 1)
    (horient : 0 ≤ connesGroundStateRealInner f g) :
    connesGroundStateL2Error f g ≤
      2 * connesGroundStateProjectiveDefect f g := by
  have herr :=
    connesGroundStateL2Error_eq f g hf hg hfcompact hgcompact
  have herrorNonneg : 0 ≤ connesGroundStateL2Error f g := by
    apply integral_nonneg
    intro x
    positivity
  have hinnerLe : connesGroundStateRealInner f g ≤ 1 := by
    rw [hfnorm, hgnorm] at herr
    nlinarith
  unfold connesGroundStateProjectiveDefect
  rw [herr, hfnorm, hgnorm]
  nlinarith

/-- A projective-defect ratio bounds the coherently oriented `L²` error. -/
theorem connesGroundStateL2Error_le_two_ratio
    (f g : ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g)
    (hfcompact : HasCompactSupport f) (hgcompact : HasCompactSupport g)
    (hfnorm : connesGroundStateL2NormSq f = 1)
    (hgnorm : connesGroundStateL2NormSq g = 1)
    (horient : 0 ≤ connesGroundStateRealInner f g)
    {ratio : ℝ}
    (hdefect : connesGroundStateProjectiveDefect f g ≤ ratio) :
    connesGroundStateL2Error f g ≤ 2 * ratio := by
  exact
    (connesGroundStateL2Error_le_two_projectiveDefect
      f g hf hg hfcompact hgcompact hfnorm hgnorm horient).trans
      (mul_le_mul_of_nonneg_left hdefect (by positivity))

theorem connesGroundStateWeightMass_log
    (A lambda : ℝ) (hlambda : 0 < lambda) :
    connesGroundStateWeightMass A (Real.log lambda) =
      (lambda ^ (2 * A) - 1) / A := by
  unfold connesGroundStateWeightMass
  rw [Real.rpow_def_of_pos hlambda]
  congr 1
  ring_nf

/-- The source `lambda^(2A)` rate implies the exact positive-strip weight-mass rate. -/
theorem tendsto_connesGroundStateWeightMass_mul_of_rpow_rate
    {A : ℝ} (hA : 0 < A)
    {lambda ratio : ℕ → ℝ}
    (hlambda : ∀ n, 1 ≤ lambda n)
    (hratio : ∀ n, 0 ≤ ratio n)
    (hrate :
      Tendsto (fun n => lambda n ^ (2 * A) * ratio n)
        atTop (nhds 0)) :
    Tendsto
      (fun n =>
        connesGroundStateWeightMass A (Real.log (lambda n)) * ratio n)
      atTop (nhds 0) := by
  have hratioLe :
      ∀ n, ratio n ≤ lambda n ^ (2 * A) * ratio n := by
    intro n
    have hpow : 1 ≤ lambda n ^ (2 * A) :=
      Real.one_le_rpow (hlambda n) (by positivity)
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hpow (hratio n)
  have hratioZero :
      Tendsto ratio atTop (nhds 0) :=
    squeeze_zero hratio hratioLe hrate
  have hquotient :
      Tendsto
        (fun n =>
          (lambda n ^ (2 * A) * ratio n - ratio n) / A)
        atTop (nhds 0) := by
    simpa using (hrate.sub hratioZero).div_const A
  apply hquotient.congr'
  filter_upwards with n
  rw [connesGroundStateWeightMass_log A (lambda n)
    (lt_of_lt_of_le zero_lt_one (hlambda n))]
  ring_nf

/-- Any positive source power rate also pays the logarithmic `A = 0` support cost. -/
theorem tendsto_log_mul_of_rpow_rate
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {lambda ratio : ℕ → ℝ}
    (hlambda : ∀ n, 1 ≤ lambda n)
    (hratio : ∀ n, 0 ≤ ratio n)
    (hrate :
      Tendsto (fun n => lambda n ^ epsilon * ratio n)
        atTop (nhds 0)) :
    Tendsto (fun n => Real.log (lambda n) * ratio n)
      atTop (nhds 0) := by
  have hlower :
      ∀ n, 0 ≤ Real.log (lambda n) * ratio n := by
    intro n
    exact mul_nonneg (Real.log_nonneg (hlambda n)) (hratio n)
  have hupper :
      ∀ n,
        Real.log (lambda n) * ratio n ≤
          (lambda n ^ epsilon * ratio n) / epsilon := by
    intro n
    calc
      Real.log (lambda n) * ratio n ≤
          (lambda n ^ epsilon / epsilon) * ratio n := by
        exact mul_le_mul_of_nonneg_right
          (Real.log_le_rpow_div
            (show 0 ≤ lambda n by linarith [hlambda n]) hepsilon)
          (hratio n)
      _ = (lambda n ^ epsilon * ratio n) / epsilon := by ring_nf
  have hbound :
      Tendsto
        (fun n => (lambda n ^ epsilon * ratio n) / epsilon)
        atTop (nhds 0) := by
    simpa [hepsilon.ne'] using hrate.div_const epsilon
  exact squeeze_zero hlower hupper hbound

/-- Exact positive-strip rate consumer before substituting `R = log lambda`. -/
theorem tendsto_connesGroundStateFourierStripError_of_weightMass_rate
    {A : ℝ} (hA : 0 < A)
    {R ratio : ℕ → ℝ} {f g : ℕ → ℝ → ℂ}
    (hR : ∀ n, 0 ≤ R n)
    (hf : ∀ n, Continuous (f n)) (hg : ∀ n, Continuous (g n))
    (hfcompact : ∀ n, HasCompactSupport (f n))
    (hgcompact : ∀ n, HasCompactSupport (g n))
    (hfsupp : ∀ n, Function.support (f n) ⊆ Icc (-(R n)) (R n))
    (hgsupp : ∀ n, Function.support (g n) ⊆ Icc (-(R n)) (R n))
    (hfnorm : ∀ n, connesGroundStateL2NormSq (f n) = 1)
    (hgnorm : ∀ n, connesGroundStateL2NormSq (g n) = 1)
    (horient : ∀ n, 0 ≤ connesGroundStateRealInner (f n) (g n))
    (hdefect :
      ∀ n, connesGroundStateProjectiveDefect (f n) (g n) ≤ ratio n)
    (hrate :
      Tendsto
        (fun n => connesGroundStateWeightMass A (R n) * ratio n)
        atTop (nhds 0)) :
    Tendsto
      (fun n => weilGroundStateFourierStripError A (f n) (g n))
      atTop (nhds 0) := by
  have hmass : ∀ n, 0 ≤ connesGroundStateWeightMass A (R n) := by
    intro n
    rw [connesGroundStateWeightMass,
      ← integral_exp_sqWeight_Icc A (R n) hA (hR n)]
    apply integral_nonneg
    intro x
    positivity
  have hupper :
      ∀ n,
        weilGroundStateFourierStripError A (f n) (g n) ≤
          Real.sqrt
            (2 * (connesGroundStateWeightMass A (R n) * ratio n)) := by
    intro n
    have hweighted :=
      connesGroundStateFourierStripError_le
        A (R n) hA (hR n) (f n) (g n)
        (hf n) (hg n) (hfcompact n) (hgcompact n)
        (hfsupp n) (hgsupp n)
    have herror :=
      connesGroundStateL2Error_le_two_ratio
        (f n) (g n) (hf n) (hg n) (hfcompact n) (hgcompact n)
        (hfnorm n) (hgnorm n) (horient n) (hdefect n)
    calc
      weilGroundStateFourierStripError A (f n) (g n) ≤
          Real.sqrt (connesGroundStateWeightMass A (R n)) *
            Real.sqrt (connesGroundStateL2Error (f n) (g n)) :=
        hweighted
      _ ≤ Real.sqrt (connesGroundStateWeightMass A (R n)) *
            Real.sqrt (2 * ratio n) := by
        exact mul_le_mul_of_nonneg_left
          (Real.sqrt_le_sqrt herror) (Real.sqrt_nonneg _)
      _ = Real.sqrt
          (2 * (connesGroundStateWeightMass A (R n) * ratio n)) := by
        rw [← Real.sqrt_mul (hmass n)]
        congr 1
        ring_nf
  have hscaled :
      Tendsto
        (fun n => 2 * (connesGroundStateWeightMass A (R n) * ratio n))
        atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hrate
  have hsqrt :
      Tendsto
        (fun n =>
          Real.sqrt
            (2 * (connesGroundStateWeightMass A (R n) * ratio n)))
        atTop (nhds 0) := by
    simpa using hscaled.sqrt
  exact squeeze_zero'
    (Eventually.of_forall fun n =>
      weilGroundStateFourierStripError_nonneg A (f n) (g n))
    (Eventually.of_forall hupper)
    hsqrt

/-- Endpoint rate consumer: `R * ratio -> 0` pays the unweighted support length. -/
theorem tendsto_connesGroundStateFourierStripError_zero_of_log_rate
    {R ratio : ℕ → ℝ} {f g : ℕ → ℝ → ℂ}
    (hR : ∀ n, 0 ≤ R n)
    (hf : ∀ n, Continuous (f n)) (hg : ∀ n, Continuous (g n))
    (hfcompact : ∀ n, HasCompactSupport (f n))
    (hgcompact : ∀ n, HasCompactSupport (g n))
    (hfsupp : ∀ n, Function.support (f n) ⊆ Icc (-(R n)) (R n))
    (hgsupp : ∀ n, Function.support (g n) ⊆ Icc (-(R n)) (R n))
    (hfnorm : ∀ n, connesGroundStateL2NormSq (f n) = 1)
    (hgnorm : ∀ n, connesGroundStateL2NormSq (g n) = 1)
    (horient : ∀ n, 0 ≤ connesGroundStateRealInner (f n) (g n))
    (hdefect :
      ∀ n, connesGroundStateProjectiveDefect (f n) (g n) ≤ ratio n)
    (hrate : Tendsto (fun n => R n * ratio n) atTop (nhds 0)) :
    Tendsto
      (fun n => weilGroundStateFourierStripError 0 (f n) (g n))
      atTop (nhds 0) := by
  have hupper :
      ∀ n,
        weilGroundStateFourierStripError 0 (f n) (g n) ≤
          Real.sqrt (4 * (R n * ratio n)) := by
    intro n
    have hweighted :=
      connesGroundStateFourierStripError_zero_le
        (R n) (hR n) (f n) (g n)
        (hf n) (hg n) (hfcompact n) (hgcompact n)
        (hfsupp n) (hgsupp n)
    have herror :=
      connesGroundStateL2Error_le_two_ratio
        (f n) (g n) (hf n) (hg n) (hfcompact n) (hgcompact n)
        (hfnorm n) (hgnorm n) (horient n) (hdefect n)
    calc
      weilGroundStateFourierStripError 0 (f n) (g n) ≤
          Real.sqrt (2 * R n) *
            Real.sqrt (connesGroundStateL2Error (f n) (g n)) :=
        hweighted
      _ ≤ Real.sqrt (2 * R n) * Real.sqrt (2 * ratio n) := by
        exact mul_le_mul_of_nonneg_left
          (Real.sqrt_le_sqrt herror) (Real.sqrt_nonneg _)
      _ = Real.sqrt (4 * (R n * ratio n)) := by
        rw [← Real.sqrt_mul (mul_nonneg (by norm_num) (hR n))]
        congr 1
        ring_nf
  have hscaled :
      Tendsto (fun n => 4 * (R n * ratio n)) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hrate
  have hsqrt :
      Tendsto (fun n => Real.sqrt (4 * (R n * ratio n)))
        atTop (nhds 0) := by
    simpa using hscaled.sqrt
  exact squeeze_zero'
    (Eventually.of_forall fun n =>
      weilGroundStateFourierStripError_nonneg 0 (f n) (g n))
    (Eventually.of_forall hupper)
    hsqrt

/-- Source-scale Rayleigh-gap rate required by the support-sensitive comparison. -/
def ConnesGroundStateRayleighGapRate
    (lambda ratio : ℕ → ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → A < 1 / 2 →
    Tendsto (fun n => lambda n ^ (2 * A) * ratio n)
      atTop (nhds 0)

/-- Weighted comparison topology on every closed substrip of the critical half-strip. -/
def ConnesGroundStateWeightedComparison
    (f g : ℕ → ℝ → ℂ) : Prop :=
  ∀ A : ℝ, 0 ≤ A → A < 1 / 2 →
    Tendsto
      (fun n => weilGroundStateFourierStripError A (f n) (g n))
      atTop (nhds 0)

/--
The source-scale rate, common support, normalization, orientation, and projective control imply
the weighted comparison topology.  The `A = 0` case follows from the positive-power rate.
-/
theorem connesGroundStateWeightedComparison_of_rayleighGapRate
    {lambda ratio : ℕ → ℝ} {f g : ℕ → ℝ → ℂ}
    (hlambda : ∀ n, 1 ≤ lambda n)
    (hf : ∀ n, Continuous (f n)) (hg : ∀ n, Continuous (g n))
    (hfcompact : ∀ n, HasCompactSupport (f n))
    (hgcompact : ∀ n, HasCompactSupport (g n))
    (hfsupp :
      ∀ n,
        Function.support (f n) ⊆
          Icc (-Real.log (lambda n)) (Real.log (lambda n)))
    (hgsupp :
      ∀ n,
        Function.support (g n) ⊆
          Icc (-Real.log (lambda n)) (Real.log (lambda n)))
    (hfnorm : ∀ n, connesGroundStateL2NormSq (f n) = 1)
    (hgnorm : ∀ n, connesGroundStateL2NormSq (g n) = 1)
    (horient : ∀ n, 0 ≤ connesGroundStateRealInner (f n) (g n))
    (hratio : ∀ n, 0 ≤ ratio n)
    (hdefect :
      ∀ n, connesGroundStateProjectiveDefect (f n) (g n) ≤ ratio n)
    (hrate : ConnesGroundStateRayleighGapRate lambda ratio) :
    ConnesGroundStateWeightedComparison f g := by
  intro A hAnonneg hAhalf
  rcases hAnonneg.eq_or_lt with hAzero | hApos
  · subst A
    have hquarterRate :=
      hrate (1 / 4) (by norm_num) (by norm_num)
    have hhalfRate :
        Tendsto (fun n => lambda n ^ (1 / 2 : ℝ) * ratio n)
          atTop (nhds 0) := by
      simpa only [show (2 : ℝ) * (1 / 4) = 1 / 2 by norm_num] using
        hquarterRate
    have hlogRate :=
      tendsto_log_mul_of_rpow_rate
        (epsilon := (1 / 2 : ℝ)) (by norm_num)
        hlambda hratio hhalfRate
    exact
      tendsto_connesGroundStateFourierStripError_zero_of_log_rate
        (fun n => Real.log_nonneg (hlambda n))
        hf hg hfcompact hgcompact hfsupp hgsupp
        hfnorm hgnorm horient hdefect hlogRate
  · have hmassRate :=
      tendsto_connesGroundStateWeightMass_mul_of_rpow_rate
        hApos hlambda hratio (hrate A hApos hAhalf)
    exact
      tendsto_connesGroundStateFourierStripError_of_weightMass_rate
        hApos (fun n => Real.log_nonneg (hlambda n))
        hf hg hfcompact hgcompact hfsupp hgsupp
        hfnorm hgnorm horient hdefect hmassRate

/--
Compose the quantitative comparison with an independently proved packet-transform limit.
The packet limit remains an explicit premise until Connes' source theorem is reconstructed.
-/
theorem connesGroundStateFourier_uniform_transfer_of_rayleighGapRate
    {A : ℝ} (hA : 0 ≤ A) (hAhalf : A < 1 / 2)
    {lambda ratio : ℕ → ℝ} {f g : ℕ → ℝ → ℂ}
    {target : ℂ → ℂ}
    (hlambda : ∀ n, 1 ≤ lambda n)
    (hf : ∀ n, Continuous (f n)) (hg : ∀ n, Continuous (g n))
    (hfcompact : ∀ n, HasCompactSupport (f n))
    (hgcompact : ∀ n, HasCompactSupport (g n))
    (hfsupp :
      ∀ n,
        Function.support (f n) ⊆
          Icc (-Real.log (lambda n)) (Real.log (lambda n)))
    (hgsupp :
      ∀ n,
        Function.support (g n) ⊆
          Icc (-Real.log (lambda n)) (Real.log (lambda n)))
    (hfnorm : ∀ n, connesGroundStateL2NormSq (f n) = 1)
    (hgnorm : ∀ n, connesGroundStateL2NormSq (g n) = 1)
    (horient : ∀ n, 0 ≤ connesGroundStateRealInner (f n) (g n))
    (hratio : ∀ n, 0 ≤ ratio n)
    (hdefect :
      ∀ n, connesGroundStateProjectiveDefect (f n) (g n) ≤ ratio n)
    (hrate : ConnesGroundStateRayleighGapRate lambda ratio)
    (hgTarget :
      WeilGroundStateUniformOnClosedStrip A
        (fun n => weilGroundStateFourierTransform (g n)) target) :
    WeilGroundStateUniformOnClosedStrip A
      (fun n => weilGroundStateFourierTransform (f n)) target := by
  apply weilGroundStateFourier_uniform_transfer
    hA hf hg hfcompact hgcompact hgTarget
  exact
    connesGroundStateWeightedComparison_of_rayleighGapRate
      hlambda hf hg hfcompact hgcompact hfsupp hgsupp
      hfnorm hgnorm horient hratio hdefect hrate
      A hA hAhalf

/-- Expanding source radius used in the collapsing-gap negative control. -/
def connesCollapsingGapLambda (n : ℕ) : ℝ :=
  Real.exp n

/-- Exponentially collapsing spectral gap used in the negative control. -/
def connesCollapsingGapScale (n : ℕ) : ℝ :=
  Real.exp (-(n : ℝ))

/--
Even an absolute Rayleigh excess that beats every source weight below the critical half-strip
need not align eigenvectors when the spectral gap collapses at the same rate.
-/
theorem connesCollapsingGap_absoluteExcessRate :
    ConnesGroundStateRayleighGapRate
      connesCollapsingGapLambda connesCollapsingGapScale := by
  intro A hA hAhalf
  have hcoef : 0 < 1 - 2 * A := by linarith
  have hn :
      Tendsto (fun n : ℕ => (1 - 2 * A) * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hcoef
  have hexp :
      Tendsto
        (fun n : ℕ => Real.exp (-((1 - 2 * A) * (n : ℝ))))
        atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hn
  convert hexp using 1
  funext n
  unfold connesCollapsingGapLambda connesCollapsingGapScale
  rw [← Real.exp_mul, ← Real.exp_add]
  congr 1
  ring_nf

theorem connesCollapsingGap_ratio_eq_one (n : ℕ) :
    weilRayleighExcess
        (weilCollapsingGapMatrix (connesCollapsingGapScale n)) 0
        weilCollapsingGapTest /
      connesCollapsingGapScale n = 1 := by
  rw [weilCollapsingGap_rayleighExcess]
  exact div_self (ne_of_gt (Real.exp_pos _))

/-- Audit bundle for the collapsing-gap negative control. -/
structure ConnesGroundStateAbsoluteExcessFalsificationCertificate : Prop where
  absoluteRate :
    ConnesGroundStateRayleighGapRate
      connesCollapsingGapLambda connesCollapsingGapScale
  gapRatio :
    ∀ n : ℕ,
      weilRayleighExcess
          (weilCollapsingGapMatrix (connesCollapsingGapScale n)) 0
          weilCollapsingGapTest /
        connesCollapsingGapScale n = 1
  projectiveDefect :
    weilProjectiveDefect weilCollapsingGapGround weilCollapsingGapTest = 1

theorem connesGroundStateAbsoluteExcessFalsification_endpoint :
    ConnesGroundStateAbsoluteExcessFalsificationCertificate where
  absoluteRate := connesCollapsingGap_absoluteExcessRate
  gapRatio := connesCollapsingGap_ratio_eq_one
  projectiveDefect := weilCollapsingGap_projectiveDefect

end LeanLab.Riemann
