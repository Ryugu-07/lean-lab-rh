import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

open Complex Filter MeasureTheory Real Set Topology

namespace LeanLab.Riemann

noncomputable section

/-!
# A complex-rate Laplace--Gamma integral

This file extends Mathlib's positive-real-rate Gamma integral to every complex decay rate in the
open right half-plane.  The proof differentiates along vertical lines, closes the resulting ODE by
integration by parts, and evaluates the constant at the positive real axis.
-/

def deBruijnNewmanComplexLaplaceIntegrand (s k : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (s - 1) * Complex.exp (-k * t)

/-- A positive real scaling introduces no principal-log branch jump in complex powers. -/
theorem deBruijnNewman_cpow_ofReal_mul {r : ℝ} (hr : 0 < r)
    {z a : ℂ} (hz : z ≠ 0) :
    (((r : ℂ) * z) ^ a) = (r : ℂ) ^ a * z ^ a := by
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hrz0 : (r : ℂ) * z ≠ 0 := mul_ne_zero hr0 hz
  rw [Complex.cpow_def_of_ne_zero hrz0, Complex.cpow_def_of_ne_zero hr0,
    Complex.cpow_def_of_ne_zero hz, Complex.log_ofReal_mul hr hz, add_mul,
    Complex.exp_add]
  rw [Complex.ofReal_log hr.le]

theorem integrableOn_deBruijnNewmanComplexLaplaceIntegrand {s k : ℂ} (hs : 0 < s.re) (hk : 0 < k.re) :
    IntegrableOn (deBruijnNewmanComplexLaplaceIntegrand s k) (Ioi 0) := by
  have hgamma := Complex.GammaIntegral_convergent hs
  have hscaled : IntegrableOn
      (fun t : ℝ => ((-(k.re * t)).exp : ℂ) * ((k.re * t : ℝ) : ℂ) ^ (s - 1))
      (Ioi 0) := by
    have hgamma' : IntegrableOn
        (fun x : ℝ => ((-x).exp : ℂ) * (x : ℂ) ^ (s - 1))
        (Ioi (k.re * 0)) := by simpa using hgamma
    have h := (integrableOn_Ioi_comp_mul_left_iff
      (fun x : ℝ => ((-x).exp : ℂ) * (x : ℂ) ^ (s - 1)) 0 hk).mpr hgamma'
    simpa only [mul_zero] using h
  have hkpow : ((k.re : ℂ) ^ (s - 1)) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]
    exact Or.inl (Complex.ofReal_ne_zero.mpr hk.ne')
  have hreal : IntegrableOn
      (fun t : ℝ => ((-k.re * t).exp : ℂ) * (t : ℂ) ^ (s - 1))
      (Ioi 0) := by
    change Integrable
      (fun t : ℝ => ((-k.re * t).exp : ℂ) * (t : ℂ) ^ (s - 1))
      (volume.restrict (Ioi 0))
    rw [← integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hkpow)]
    refine hscaled.congr_fun (fun t ht => ?_) measurableSet_Ioi
    have ht0 : 0 ≤ t := le_of_lt ht
    change ((-(k.re * t)).exp : ℂ) * ((k.re * t : ℝ) : ℂ) ^ (s - 1) = _
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hk.le ht0]
    push_cast
    ring_nf
  have hmeas : AEStronglyMeasurable (deBruijnNewmanComplexLaplaceIntegrand s k)
      (volume.restrict (Ioi 0)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    apply (continuousOn_of_forall_continuousAt fun t ht =>
      (continuousAt_ofReal_cpow_const _ _ (Or.inr ht.ne'))).mul
    fun_prop
  rw [IntegrableOn, ← integrable_norm_iff hmeas]
  have hrealNorm := hreal.norm
  apply hrealNorm.congr
  apply (ae_restrict_iff' measurableSet_Ioi).mpr
  filter_upwards with t ht
  simp only [deBruijnNewmanComplexLaplaceIntegrand, norm_mul]
  rw [Complex.norm_of_nonneg (Real.exp_pos _).le,
    Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp]
  have hre : (-k * (t : ℂ)).re = -k.re * t := by simp
  rw [hre]
  ring

theorem tendsto_deBruijnNewmanComplexLaplaceKernel_zero {s k : ℂ} (hs : 0 < s.re) :
    Tendsto (fun t : ℝ => (t : ℂ) ^ s * Complex.exp (-k * t))
      (𝓝[>] 0) (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hrpow : Tendsto (fun t : ℝ => t ^ s.re) (𝓝[>] 0) (𝓝 0) := by
    have h : ContinuousWithinAt (fun t : ℝ => t ^ s.re) (Ioi 0) 0 :=
      (Real.continuousAt_rpow_const 0 s.re (Or.inr hs.le)).continuousWithinAt
    change Tendsto (fun t : ℝ => t ^ s.re) (𝓝[>] 0) (𝓝 ((0 : ℝ) ^ s.re)) at h
    simpa [Real.zero_rpow hs.ne'] using h
  have hexp : Tendsto (fun t : ℝ => Real.exp (-k.re * t)) (𝓝[>] 0) (𝓝 1) := by
    have hcont : ContinuousAt (fun t : ℝ => Real.exp (-k.re * t)) 0 := by fun_prop
    have h : ContinuousWithinAt (fun t : ℝ => Real.exp (-k.re * t)) (Ioi 0) 0 :=
      hcont.continuousWithinAt
    change Tendsto (fun t : ℝ => Real.exp (-k.re * t)) (𝓝[>] 0)
      (𝓝 (Real.exp (-k.re * 0))) at h
    simpa using h
  have hprod : Tendsto (fun t : ℝ => t ^ s.re * Real.exp (-k.re * t))
      (𝓝[>] 0) (𝓝 0) := by simpa using hrpow.mul hexp
  apply hprod.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : 0 < t := ht
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_exp]
  have hre : (-k * (t : ℂ)).re = -k.re * t := by simp
  rw [hre]

theorem tendsto_deBruijnNewmanComplexLaplaceKernel_infty {s k : ℂ} (hk : 0 < k.re) :
    Tendsto (fun t : ℝ => (t : ℂ) ^ s * Complex.exp (-k * t))
      atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have heq :
      (fun t : ℝ => ‖(t : ℂ) ^ s * Complex.exp (-k * t)‖) =ᶠ[atTop]
        (fun t : ℝ => t ^ s.re * Real.exp (-k.re * t)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp]
    have hre : (-k * (t : ℂ)).re = -k.re * t := by simp
    rw [hre]
  exact (tendsto_congr' heq).mpr
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s.re k.re hk)

theorem deBruijnNewmanComplexLaplace_add_one {s k : ℂ} (hs : 0 < s.re) (hk : 0 < k.re) :
    (∫ t : ℝ in Ioi 0, deBruijnNewmanComplexLaplaceIntegrand (s + 1) k t) =
      s / k * ∫ t : ℝ in Ioi 0, deBruijnNewmanComplexLaplaceIntegrand s k t := by
  letI : NormedSpace ℝ ℂ := NormedSpace.complexToReal
  let u : ℝ → ℂ := fun t => (t : ℂ) ^ s
  let u' : ℝ → ℂ := fun t => s * (t : ℂ) ^ (s - 1)
  let v : ℝ → ℂ := fun t => Complex.exp (-k * t)
  let v' : ℝ → ℂ := fun t => -k * Complex.exp (-k * t)
  have hu : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt u (u' t) t := by
    intro t ht
    have hs0 : s ≠ 0 := by intro h; simpa [h] using hs
    have hcpow : HasDerivAt (fun x : ℝ => (x : ℂ) ^ s)
        (s * (t : ℂ) ^ (s - 1)) t :=
      hasDerivAt_ofReal_cpow_const ht.ne' hs0
    simpa only [u, u', mul_one] using hcpow
  have hv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt v (v' t) t := by
    intro t _
    have hlinear : HasDerivAt (fun x : ℝ => -k * (x : ℂ)) (-k) t := by
      simpa only [id_eq, Complex.ofReal_one, mul_one] using
        (hasDerivAt_id t).ofReal_comp.const_mul (-k)
    simpa only [v, v', mul_comm] using hlinear.cexp
  have hbase := integrableOn_deBruijnNewmanComplexLaplaceIntegrand hs hk
  have hnext := integrableOn_deBruijnNewmanComplexLaplaceIntegrand (s := s + 1) (k := k) (by simp; linarith) hk
  have hleft : IntegrableOn (u' * v) (Ioi 0) := by
    apply (hbase.const_mul s).congr
    filter_upwards with t
    simp only [u', v, Pi.mul_apply, deBruijnNewmanComplexLaplaceIntegrand]
    ring
  have hright : IntegrableOn (u * v') (Ioi 0) := by
    apply (hnext.const_mul (-k)).congr
    filter_upwards with t
    simp only [u, v', Pi.mul_apply, deBruijnNewmanComplexLaplaceIntegrand, add_sub_cancel_right]
    ring
  have huv : IntegrableOn (u' * v + u * v') (Ioi 0) := hleft.add hright
  have hparts := MeasureTheory.integral_Ioi_deriv_mul_eq_sub hu hv huv
    (tendsto_deBruijnNewmanComplexLaplaceKernel_zero hs) (tendsto_deBruijnNewmanComplexLaplaceKernel_infty hk)
  change (∫ x : ℝ in Ioi 0, (u' * v) x + (u * v') x) = 0 - 0 at hparts
  rw [MeasureTheory.integral_add hleft hright] at hparts
  have hleftInt : (∫ t : ℝ in Ioi 0, (u' * v) t) =
      s * ∫ t : ℝ in Ioi 0, deBruijnNewmanComplexLaplaceIntegrand s k t := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t _
    simp only [u', v, Pi.mul_apply, deBruijnNewmanComplexLaplaceIntegrand]
    ring
  have hrightInt : (∫ t : ℝ in Ioi 0, (u * v') t) =
      -k * ∫ t : ℝ in Ioi 0, deBruijnNewmanComplexLaplaceIntegrand (s + 1) k t := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t _
    simp only [u, v', Pi.mul_apply, deBruijnNewmanComplexLaplaceIntegrand, add_sub_cancel_right]
    ring
  rw [hleftInt, hrightInt] at hparts
  simp only [sub_self] at hparts
  have hk0 : k ≠ 0 := by intro h; simpa [h] using hk
  calc
    (∫ t : ℝ in Ioi 0, deBruijnNewmanComplexLaplaceIntegrand (s + 1) k t) =
        (s * ∫ t : ℝ in Ioi 0, deBruijnNewmanComplexLaplaceIntegrand s k t) / k := by
      apply (eq_div_iff hk0).2
      linear_combination -hparts
    _ = s / k * ∫ t : ℝ in Ioi 0, deBruijnNewmanComplexLaplaceIntegrand s k t := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring

def deBruijnNewmanComplexLaplaceVerticalRate (a y : ℝ) : ℂ :=
  a + Complex.I * y

def deBruijnNewmanComplexLaplaceVerticalDerivative (s : ℂ) (a y t : ℝ) : ℂ :=
  -Complex.I * (t : ℂ) * deBruijnNewmanComplexLaplaceIntegrand s (deBruijnNewmanComplexLaplaceVerticalRate a y) t

def deBruijnNewmanComplexLaplaceVerticalIntegral (s : ℂ) (a y : ℝ) : ℂ :=
  ∫ t : ℝ in Ioi 0, deBruijnNewmanComplexLaplaceIntegrand s (deBruijnNewmanComplexLaplaceVerticalRate a y) t

@[simp] theorem deBruijnNewmanComplexLaplaceVerticalRate_re (a y : ℝ) :
    (deBruijnNewmanComplexLaplaceVerticalRate a y).re = a := by
  simp [deBruijnNewmanComplexLaplaceVerticalRate]

theorem deBruijnNewmanComplexLaplaceVerticalDerivative_integrable {s : ℂ} {a y : ℝ}
    (hs : 0 < s.re) (ha : 0 < a) :
    IntegrableOn (deBruijnNewmanComplexLaplaceVerticalDerivative s a y) (Ioi 0) := by
  have hnext := integrableOn_deBruijnNewmanComplexLaplaceIntegrand (s := s + 1)
    (k := deBruijnNewmanComplexLaplaceVerticalRate a y) (by simp; linarith) (by simp [ha])
  apply (hnext.const_mul (-Complex.I)).congr
  apply (ae_restrict_iff' measurableSet_Ioi).mpr
  filter_upwards with t ht
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hpow : (t : ℂ) ^ s = (t : ℂ) * (t : ℂ) ^ (s - 1) := by
    calc
      (t : ℂ) ^ s = (t : ℂ) ^ ((1 : ℂ) + (s - 1)) := by congr 1 <;> ring
      _ = (t : ℂ) ^ (1 : ℂ) * (t : ℂ) ^ (s - 1) :=
        Complex.cpow_add _ _ ht0
      _ = (t : ℂ) * (t : ℂ) ^ (s - 1) := by simp
  unfold deBruijnNewmanComplexLaplaceVerticalDerivative deBruijnNewmanComplexLaplaceIntegrand
  rw [add_sub_cancel_right, hpow]
  ring

theorem deBruijnNewmanComplexLaplaceVerticalDerivative_norm (s : ℂ) (a y₁ y₂ : ℝ) {t : ℝ}
    (ht : 0 < t) :
    ‖deBruijnNewmanComplexLaplaceVerticalDerivative s a y₁ t‖ =
      ‖deBruijnNewmanComplexLaplaceVerticalDerivative s a y₂ t‖ := by
  unfold deBruijnNewmanComplexLaplaceVerticalDerivative deBruijnNewmanComplexLaplaceIntegrand deBruijnNewmanComplexLaplaceVerticalRate
  simp only [norm_mul, norm_neg, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht,
    Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp]
  congr 2
  simp [Complex.mul_re]

theorem hasDerivAt_deBruijnNewmanComplexLaplaceVerticalIntegral {s : ℂ} {a y : ℝ}
    (hs : 0 < s.re) (ha : 0 < a) :
    HasDerivAt (deBruijnNewmanComplexLaplaceVerticalIntegral s a)
      (∫ t : ℝ in Ioi 0, deBruijnNewmanComplexLaplaceVerticalDerivative s a y t) y := by
  let F : ℝ → ℝ → ℂ := fun y t =>
    deBruijnNewmanComplexLaplaceIntegrand s (deBruijnNewmanComplexLaplaceVerticalRate a y) t
  let F' : ℝ → ℝ → ℂ := fun y t => deBruijnNewmanComplexLaplaceVerticalDerivative s a y t
  let bound : ℝ → ℝ := fun t => ‖F' y t‖
  have hFint : ∀ y : ℝ, IntegrableOn (F y) (Ioi 0) := fun y =>
    integrableOn_deBruijnNewmanComplexLaplaceIntegrand hs (by simpa [F] using ha)
  have hF'int : ∀ y : ℝ, IntegrableOn (F' y) (Ioi 0) := fun y =>
    deBruijnNewmanComplexLaplaceVerticalDerivative_integrable hs ha
  have hdiff : ∀ (t y : ℝ), HasDerivAt (F · t) (F' y t) y := by
    intro t y
    have hIy : HasDerivAt (fun x : ℝ => Complex.I * (x : ℂ)) Complex.I y := by
      simpa only [id_eq, Complex.ofReal_one, mul_one] using
        (hasDerivAt_id y).ofReal_comp.const_mul Complex.I
    have hrate : HasDerivAt (deBruijnNewmanComplexLaplaceVerticalRate a) Complex.I y := by
      simpa only [deBruijnNewmanComplexLaplaceVerticalRate, Pi.add_apply, zero_add] using!
        (hasDerivAt_const y (a : ℂ)).add hIy
    have hlinear : HasDerivAt
        (fun x : ℝ => -(deBruijnNewmanComplexLaplaceVerticalRate a x) * (t : ℂ))
        (-Complex.I * t) y := by
      exact hrate.neg.mul_const (t : ℂ)
    have hexp := hlinear.cexp
    unfold F F' deBruijnNewmanComplexLaplaceVerticalDerivative deBruijnNewmanComplexLaplaceIntegrand
    have hmul := (hasDerivAt_const y ((t : ℂ) ^ (s - 1))).mul hexp
    have hmul' : HasDerivAt
        (fun x => (t : ℂ) ^ (s - 1) *
          Complex.exp (-(deBruijnNewmanComplexLaplaceVerticalRate a x) * (t : ℂ)))
        ((t : ℂ) ^ (s - 1) *
          (Complex.exp (-(deBruijnNewmanComplexLaplaceVerticalRate a y) * (t : ℂ)) * (-Complex.I * t))) y := by
      simpa only [zero_mul, zero_add] using! hmul
    convert hmul' using 1 <;> ring
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi 0)) (F := F) (F' := F') (bound := bound)
    (s := Set.univ) (x₀ := y) univ_mem
    (Filter.Eventually.of_forall fun x => (hFint x).aestronglyMeasurable)
    (hFint y)
    (hF'int y).aestronglyMeasurable
    (by
      apply (ae_restrict_iff' measurableSet_Ioi).mpr
      filter_upwards with t ht
      intro x _
      exact le_of_eq (deBruijnNewmanComplexLaplaceVerticalDerivative_norm s a x y ht))
    (hF'int y).norm
    (Filter.Eventually.of_forall fun t x _ => hdiff t x)
  change HasDerivAt
    (fun n => ∫ t : ℝ in Ioi 0, deBruijnNewmanComplexLaplaceIntegrand s (deBruijnNewmanComplexLaplaceVerticalRate a n) t)
    (∫ t : ℝ in Ioi 0, deBruijnNewmanComplexLaplaceVerticalDerivative s a y t) y
  exact hmain.2

theorem deBruijnNewmanComplexLaplaceVerticalDerivative_integral {s : ℂ} {a y : ℝ}
    (hs : 0 < s.re) (ha : 0 < a) :
    (∫ t : ℝ in Ioi 0, deBruijnNewmanComplexLaplaceVerticalDerivative s a y t) =
      -Complex.I * deBruijnNewmanComplexLaplaceVerticalIntegral (s + 1) a y := by
  rw [deBruijnNewmanComplexLaplaceVerticalIntegral, ← MeasureTheory.integral_const_mul]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hpow : (t : ℂ) ^ s = (t : ℂ) * (t : ℂ) ^ (s - 1) := by
    calc
      (t : ℂ) ^ s = (t : ℂ) ^ ((1 : ℂ) + (s - 1)) := by congr 1 <;> ring
      _ = (t : ℂ) ^ (1 : ℂ) * (t : ℂ) ^ (s - 1) :=
        Complex.cpow_add _ _ ht0
      _ = (t : ℂ) * (t : ℂ) ^ (s - 1) := by simp
  unfold deBruijnNewmanComplexLaplaceVerticalDerivative deBruijnNewmanComplexLaplaceIntegrand
  change -Complex.I * (t : ℂ) *
      ((t : ℂ) ^ (s - 1) * Complex.exp (-deBruijnNewmanComplexLaplaceVerticalRate a y * t)) =
    -Complex.I *
      ((t : ℂ) ^ (s + 1 - 1) * Complex.exp (-deBruijnNewmanComplexLaplaceVerticalRate a y * t))
  rw [add_sub_cancel_right, hpow]
  ring

theorem hasDerivAt_deBruijnNewmanComplexLaplaceVerticalIntegral_closed {s : ℂ} {a y : ℝ}
    (hs : 0 < s.re) (ha : 0 < a) :
    HasDerivAt (deBruijnNewmanComplexLaplaceVerticalIntegral s a)
      (-Complex.I * (s / deBruijnNewmanComplexLaplaceVerticalRate a y) *
        deBruijnNewmanComplexLaplaceVerticalIntegral s a y) y := by
  have hraw := hasDerivAt_deBruijnNewmanComplexLaplaceVerticalIntegral (y := y) hs ha
  apply hraw.congr_deriv
  rw [deBruijnNewmanComplexLaplaceVerticalDerivative_integral hs ha]
  simp only [deBruijnNewmanComplexLaplaceVerticalIntegral]
  rw [deBruijnNewmanComplexLaplace_add_one hs (by simpa using ha)]
  ring

def deBruijnNewmanComplexLaplaceVerticalNormalized (s : ℂ) (a y : ℝ) : ℂ :=
  deBruijnNewmanComplexLaplaceVerticalRate a y ^ s * deBruijnNewmanComplexLaplaceVerticalIntegral s a y

theorem hasDerivAt_deBruijnNewmanComplexLaplaceVerticalNormalized_zero {s : ℂ} {a y : ℝ}
    (hs : 0 < s.re) (ha : 0 < a) :
    HasDerivAt (deBruijnNewmanComplexLaplaceVerticalNormalized s a) 0 y := by
  have hIy : HasDerivAt (fun x : ℝ => Complex.I * (x : ℂ)) Complex.I y := by
    simpa only [id_eq, Complex.ofReal_one, mul_one] using
      (hasDerivAt_id y).ofReal_comp.const_mul Complex.I
  have hrate : HasDerivAt (deBruijnNewmanComplexLaplaceVerticalRate a) Complex.I y := by
    simpa only [deBruijnNewmanComplexLaplaceVerticalRate, Pi.add_apply, zero_add] using!
      (hasDerivAt_const y (a : ℂ)).add hIy
  have hpow : HasDerivAt
      (fun x : ℝ => deBruijnNewmanComplexLaplaceVerticalRate a x ^ s)
      (s * deBruijnNewmanComplexLaplaceVerticalRate a y ^ (s - 1) * Complex.I) y := by
    have hslit : deBruijnNewmanComplexLaplaceVerticalRate a y ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using ha))
    exact (Complex.hasStrictDerivAt_cpow_const (c := s) hslit).hasDerivAt.comp y hrate
  have hint := hasDerivAt_deBruijnNewmanComplexLaplaceVerticalIntegral_closed (y := y) hs ha
  unfold deBruijnNewmanComplexLaplaceVerticalNormalized
  apply (hpow.mul hint).congr_deriv
  have hk0 : deBruijnNewmanComplexLaplaceVerticalRate a y ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    have ha0 : a = 0 := by simpa using hre
    exact ha.ne' ha0
  have hfactor : deBruijnNewmanComplexLaplaceVerticalRate a y ^ s =
      deBruijnNewmanComplexLaplaceVerticalRate a y ^ (s - 1) * deBruijnNewmanComplexLaplaceVerticalRate a y := by
    calc
      deBruijnNewmanComplexLaplaceVerticalRate a y ^ s =
          deBruijnNewmanComplexLaplaceVerticalRate a y ^ ((s - 1) + 1) := by congr 1 <;> ring
      _ = deBruijnNewmanComplexLaplaceVerticalRate a y ^ (s - 1) *
          deBruijnNewmanComplexLaplaceVerticalRate a y ^ (1 : ℂ) := Complex.cpow_add _ _ hk0
      _ = deBruijnNewmanComplexLaplaceVerticalRate a y ^ (s - 1) *
          deBruijnNewmanComplexLaplaceVerticalRate a y := by simp
  rw [hfactor]
  field_simp [hk0]
  ring

theorem deBruijnNewmanComplexLaplaceVerticalNormalized_eq (s : ℂ) {a : ℝ} (ha : 0 < a)
    (y₁ y₂ : ℝ) (hs : 0 < s.re) :
    deBruijnNewmanComplexLaplaceVerticalNormalized s a y₁ =
      deBruijnNewmanComplexLaplaceVerticalNormalized s a y₂ := by
  apply is_const_of_deriv_eq_zero
    (fun y => (hasDerivAt_deBruijnNewmanComplexLaplaceVerticalNormalized_zero hs ha).differentiableAt)
    (fun y => (hasDerivAt_deBruijnNewmanComplexLaplaceVerticalNormalized_zero hs ha).deriv)

theorem deBruijnNewmanComplexLaplaceVerticalNormalized_zero (s : ℂ) {a : ℝ}
    (hs : 0 < s.re) (ha : 0 < a) :
    deBruijnNewmanComplexLaplaceVerticalNormalized s a 0 = Complex.Gamma s := by
  have hgamma := Complex.integral_cpow_mul_exp_neg_mul_Ioi hs ha
  have hintegral : deBruijnNewmanComplexLaplaceVerticalIntegral s a 0 =
      ((1 / a : ℝ) : ℂ) ^ s * Complex.Gamma s := by
    simpa [deBruijnNewmanComplexLaplaceVerticalIntegral, deBruijnNewmanComplexLaplaceIntegrand,
      deBruijnNewmanComplexLaplaceVerticalRate] using hgamma
  rw [deBruijnNewmanComplexLaplaceVerticalNormalized, hintegral]
  have hprod : (a : ℂ) ^ s * (((1 / a : ℝ) : ℂ) ^ s) = 1 := by
    rw [← Complex.mul_cpow_ofReal_nonneg ha.le (one_div_nonneg.mpr ha.le)]
    norm_num [ha.ne']
  simp only [deBruijnNewmanComplexLaplaceVerticalRate, Complex.ofReal_zero, mul_zero, add_zero]
  rw [← mul_assoc, hprod, one_mul]

theorem deBruijnNewmanComplexLaplace_eq {s k : ℂ} (hs : 0 < s.re) (hk : 0 < k.re) :
    (∫ t : ℝ in Ioi 0, deBruijnNewmanComplexLaplaceIntegrand s k t) =
      k ^ (-s) * Complex.Gamma s := by
  have hrate : deBruijnNewmanComplexLaplaceVerticalRate k.re k.im = k := by
    apply Complex.ext <;> simp [deBruijnNewmanComplexLaplaceVerticalRate]
  have hconst := deBruijnNewmanComplexLaplaceVerticalNormalized_eq s hk k.im 0 hs
  rw [deBruijnNewmanComplexLaplaceVerticalNormalized_zero s hs hk] at hconst
  simp only [deBruijnNewmanComplexLaplaceVerticalNormalized, deBruijnNewmanComplexLaplaceVerticalIntegral, hrate] at hconst
  have hk0 : k ≠ 0 := by intro h; simpa [h] using hk
  calc
    (∫ t : ℝ in Ioi 0, deBruijnNewmanComplexLaplaceIntegrand s k t) =
        1 * (∫ t : ℝ in Ioi 0, deBruijnNewmanComplexLaplaceIntegrand s k t) := by rw [one_mul]
    _ = (k ^ (-s) * k ^ s) *
        (∫ t : ℝ in Ioi 0, deBruijnNewmanComplexLaplaceIntegrand s k t) := by
      rw [← Complex.cpow_add _ _ hk0]
      simp
    _ = k ^ (-s) * Complex.Gamma s := by rw [mul_assoc, hconst]

end

end LeanLab.Riemann
