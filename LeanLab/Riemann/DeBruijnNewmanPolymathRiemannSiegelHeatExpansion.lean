import LeanLab.Riemann.DeBruijnNewmanPolymathHeatKernel
import LeanLab.Riemann.DeBruijnNewmanPolymathRiemannSiegelSum
import LeanLab.Riemann.DeBruijnNewmanPolymathRiemannSiegelXioContinuation
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Heat-evolved finite Riemann--Siegel expansion

This module proves the exact two-sum, two-remainder expansion in equation `(39)` of the
Polymath de Bruijn--Newman paper, in the project's variance-two Gaussian normalization.
-/

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace LeanLab.Riemann

noncomputable section

def deBruijnNewmanRiemannSiegelHeatShift (t y : ℝ) : ℂ :=
  ((Real.sqrt t / 2 * y : ℝ) : ℂ)

def deBruijnNewmanRiemannSiegelHeatEvolve (t : ℝ) (F : ℂ → ℂ) (s : ℂ) : ℂ :=
  ∫ y : ℝ, F (s + deBruijnNewmanRiemannSiegelHeatShift t y) ∂gaussianReal 0 2

def deBruijnNewmanRiemannSiegelHeatTerm (t : ℝ) (n : ℕ) : ℂ → ℂ :=
  deBruijnNewmanRiemannSiegelHeatEvolve t (deBruijnNewmanRiemannSiegelR0Term n)

def deBruijnNewmanRiemannSiegelHeatRemainder (t : ℝ) (N : ℕ) : ℂ → ℂ :=
  deBruijnNewmanRiemannSiegelHeatEvolve t (deBruijnNewmanRiemannSiegelR0N N)

theorem deBruijnNewmanRiemannSiegel_isNoninteger_of_im_ne_zero
    {s : ℂ} (hs : s.im ≠ 0) (x : ℝ) :
    deBruijnNewmanRiemannSiegelIsNoninteger (s + (x : ℂ)) := by
  intro n hn
  have him := congrArg Complex.im hn
  simp only [Complex.add_im, Complex.ofReal_im, add_zero, Complex.intCast_im] at him
  exact hs him

theorem deBruijnNewmanRiemannSiegel_base_im_ne_zero {z : ℂ} (hz : z.re ≠ 0) :
    ((1 + Complex.I * z) / 2).im ≠ 0 := by
  have hcalc : ((1 + Complex.I * z) / 2).im = z.re / 2 := by
    norm_num [Complex.div_im, Complex.mul_im]
  rw [hcalc]
  exact div_ne_zero hz (by norm_num)

theorem deBruijnNewmanRiemannSiegel_xio_finite (N : ℕ) {s : ℂ}
    (hs : deBruijnNewmanRiemannSiegelIsNoninteger s) :
    (1 / 8) * riemannXi s =
      ((∑ k ∈ Finset.range N,
          deBruijnNewmanRiemannSiegelR0Term (k + 1) s) +
        deBruijnNewmanRiemannSiegelR0N N s) +
      ((∑ k ∈ Finset.range N,
          deBruijnNewmanRiemannSiegelReflect
            (deBruijnNewmanRiemannSiegelR0Term (k + 1)) (1 - s)) +
        deBruijnNewmanRiemannSiegelReflect
          (deBruijnNewmanRiemannSiegelR0N N) (1 - s)) := by
  rw [deBruijnNewmanRiemannSiegel_xio hs,
    deBruijnNewmanRiemannSiegelR0N_finite_decomposition N s]
  have hreflect := deBruijnNewmanRiemannSiegelR0N_finite_decomposition N
    ((starRingEnd ℂ) (1 - s))
  unfold deBruijnNewmanRiemannSiegelReflect
  rw [hreflect, map_add, map_sum]

theorem deBruijnNewmanRiemannSiegel_integrable_exp_sq_add_abs_gaussian
    {c : ℝ} (hc : c < 1 / 4) (d : ℝ) :
    Integrable (fun y : ℝ => Real.exp (c * y ^ 2 + d * |y|))
      (gaussianReal 0 2) := by
  rw [ProbabilityTheory.gaussianReal_of_var_ne_zero (μ := 0) (v := 2) (by norm_num)]
  rw [integrable_withDensity_iff_integrable_smul'
    (ProbabilityTheory.measurable_gaussianPDF 0 2)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ProbabilityTheory.gaussianPDF, ENNReal.toReal_ofReal,
    ProbabilityTheory.gaussianPDFReal_nonneg, smul_eq_mul]
  let a : ℝ := 1 / 4 - c
  have ha : 0 < a := by dsimp [a]; linarith
  have hgauss : Integrable (fun y : ℝ => Real.exp (-(a / 2) * y ^ 2)) :=
    integrable_exp_neg_mul_sq (by positivity)
  let C : ℝ := (Real.sqrt (2 * Real.pi * 2))⁻¹ *
    Real.exp (d ^ 2 / (2 * a))
  refine Integrable.mono' (hgauss.const_mul C) (by fun_prop) ?_
  apply ae_of_all
  intro y
  have hsq : 0 ≤ (a * |y| - |d|) ^ 2 := sq_nonneg _
  have hlinear : d * |y| ≤ a / 2 * y ^ 2 + d ^ 2 / (2 * a) := by
    have had : 0 < 2 * a := by positivity
    have hrewrite :
        a / 2 * y ^ 2 + d ^ 2 / (2 * a) =
          (a ^ 2 * y ^ 2 + d ^ 2) / (2 * a) := by
      field_simp
    rw [hrewrite, le_div_iff₀ had]
    have hd : d * |y| ≤ |d| * |y| :=
      mul_le_mul_of_nonneg_right (le_abs_self d) (abs_nonneg y)
    nlinarith [hsq, sq_abs y, sq_abs d]
  have hexp :
      c * y ^ 2 + d * |y| - y ^ 2 / 4 ≤
        -(a / 2) * y ^ 2 + d ^ 2 / (2 * a) := by
    dsimp [a] at hlinear ⊢
    linarith
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (ProbabilityTheory.gaussianPDFReal_nonneg 0 2 y),
    abs_of_nonneg (Real.exp_nonneg _)]
  simp only [ProbabilityTheory.gaussianPDFReal, sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  norm_num only [NNReal.coe_ofNat]
  have hexponent :
      -y ^ 2 / 4 + (c * y ^ 2 + d * |y|) =
        c * y ^ 2 + d * |y| - y ^ 2 / 4 := by ring
  rw [hexponent]
  dsimp [C]
  calc
    (Real.sqrt (2 * Real.pi * 2))⁻¹ *
          Real.exp (c * y ^ 2 + d * |y| - y ^ 2 / 4) ≤
        (Real.sqrt (2 * Real.pi * 2))⁻¹ *
          Real.exp (-(a / 2) * y ^ 2 + d ^ 2 / (2 * a)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)
    _ = (Real.sqrt (2 * Real.pi * 2))⁻¹ *
          Real.exp (d ^ 2 / (2 * a)) * Real.exp (-(a / 2) * y ^ 2) := by
      rw [Real.exp_add]
      ring

theorem deBruijnNewmanRiemannSiegel_log_one_add_abs_le
    {delta : ℝ} (hdelta : 0 < delta) (v : ℝ) :
    Real.log (1 + |v|) ≤
      delta * |v| + delta + |Real.log delta| := by
  have hdelta0 : delta ≠ 0 := ne_of_gt hdelta
  have hone : 1 + |v| ≠ 0 := by positivity
  have hnonneg : 0 ≤ delta * (1 + |v|) := by positivity
  have hlog := Real.log_le_self hnonneg
  rw [Real.log_mul hdelta0 hone] at hlog
  have hneg : -Real.log delta ≤ |Real.log delta| := neg_le_abs _
  linarith

def deBruijnNewmanRiemannSiegelLineLogConstant (N : ℕ) (delta : ℝ) : ℝ :=
  N + 1 / 2 + 6 + delta + |Real.log delta|

theorem deBruijnNewmanRiemannSiegel_abs_log_norm_line_le
    (N : ℕ) {delta : ℝ} (hdelta : 0 < delta) (v : ℝ) :
    |Real.log ‖deBruijnNewmanRiemannSiegelLine N v‖| ≤
      deBruijnNewmanRiemannSiegelLineLogConstant N delta + delta * |v| := by
  let w := deBruijnNewmanRiemannSiegelLine N v
  let A : ℝ := N + 1 / 2
  have hA : 0 < A := by dsimp [A]; positivity
  have hwLower : (1 / 4 : ℝ) ≤ ‖w‖ :=
    one_div_four_le_norm_deBruijnNewmanRiemannSiegelLine N v
  have hwPos : 0 < ‖w‖ := lt_of_lt_of_le (by norm_num) hwLower
  have hwUpper : ‖w‖ ≤ A + |v| := by
    simpa [w, A] using norm_deBruijnNewmanRiemannSiegelLine_le N v
  have hAuPos : 0 < A + |v| := add_pos_of_pos_of_nonneg hA (abs_nonneg v)
  have hfactor : A + |v| ≤ (A + 1) * (1 + |v|) := by
    nlinarith [abs_nonneg v, hA]
  have hAone : 0 < A + 1 := by positivity
  have huone : 0 < 1 + |v| := by positivity
  have hlogUpper : Real.log ‖w‖ ≤
      A + 1 + (delta * |v| + delta + |Real.log delta|) := by
    calc
      Real.log ‖w‖ ≤ Real.log (A + |v|) :=
        Real.log_le_log hwPos hwUpper
      _ ≤ Real.log ((A + 1) * (1 + |v|)) :=
        Real.log_le_log hAuPos hfactor
      _ = Real.log (A + 1) + Real.log (1 + |v|) := by
        rw [Real.log_mul (ne_of_gt hAone) (ne_of_gt huone)]
      _ ≤ (A + 1) + Real.log (1 + |v|) := by
        gcongr
        exact Real.log_le_self hAone.le
      _ ≤ A + 1 + (delta * |v| + delta + |Real.log delta|) := by
        linarith [deBruijnNewmanRiemannSiegel_log_one_add_abs_le hdelta v]
  have hlogLower : -Real.log ‖w‖ ≤ 4 := by
    have h := Real.neg_inv_le_log hwPos.le
    have hinv : ‖w‖⁻¹ ≤ 4 := by
      rw [inv_le_iff_one_le_mul₀' hwPos]
      nlinarith
    linarith
  rw [abs_le]
  constructor
  · dsimp [deBruijnNewmanRiemannSiegelLineLogConstant, A]
    have hnonneg : 0 ≤ delta * |v| := mul_nonneg hdelta.le (abs_nonneg v)
    linarith [abs_nonneg (Real.log delta)]
  · dsimp [deBruijnNewmanRiemannSiegelLineLogConstant, A]
    dsimp [A, w] at hlogUpper
    linarith

theorem deBruijnNewmanRiemannSiegel_norm_cpow_neg_line_le
    (N : ℕ) {delta : ℝ} (hdelta : 0 < delta) (s : ℂ) (v : ℝ) :
    ‖deBruijnNewmanRiemannSiegelLine N v ^ (-s)‖ ≤
      Real.exp
        (|s.re| * (deBruijnNewmanRiemannSiegelLineLogConstant N delta + delta * |v|) +
          |s.im| * Real.pi) := by
  let w := deBruijnNewmanRiemannSiegelLine N v
  have hw : w ≠ 0 := Complex.slitPlane_ne_zero
    (deBruijnNewmanRiemannSiegelLine_mem_slitPlane N v)
  rw [Complex.cpow_def_of_ne_zero hw, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hlog := deBruijnNewmanRiemannSiegel_abs_log_norm_line_le N hdelta v
  have harg := Complex.abs_arg_le_pi w
  rw [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.log_re, Complex.log_im]
  calc
    Real.log ‖w‖ * -s.re - w.arg * -s.im =
        (-s.re) * Real.log ‖w‖ + s.im * w.arg := by ring
    _ ≤ |(-s.re) * Real.log ‖w‖| + |s.im * w.arg| :=
      add_le_add (le_abs_self _) (le_abs_self _)
    _ = |s.re| * |Real.log ‖w‖| + |s.im| * |w.arg| := by
      rw [abs_mul, abs_mul, abs_neg]
    _ ≤ |s.re| * (deBruijnNewmanRiemannSiegelLineLogConstant N delta + delta * |v|) +
          |s.im| * Real.pi :=
      add_le_add (mul_le_mul_of_nonneg_left hlog (abs_nonneg _))
        (mul_le_mul_of_nonneg_left harg (abs_nonneg _))

def deBruijnNewmanRiemannSiegelLineRate (N : ℕ) (delta : ℝ) (s : ℂ) : ℝ :=
  delta * |s.re| + Real.sqrt 2 * Real.pi * (N + 1 / 2)

def deBruijnNewmanRiemannSiegelLineMajorantConstant (N : ℕ) (delta : ℝ) (s : ℂ) : ℝ :=
  |s.re| * deBruijnNewmanRiemannSiegelLineLogConstant N delta + |s.im| * Real.pi +
    deBruijnNewmanRiemannSiegelLineRate N delta s ^ 2 / (2 * Real.pi)

def deBruijnNewmanRiemannSiegelLineMajorant (N : ℕ) (delta : ℝ) (s : ℂ) (v : ℝ) : ℝ :=
  (1 / 2) * Real.exp (deBruijnNewmanRiemannSiegelLineMajorantConstant N delta s) *
    Real.exp (-(Real.pi / 2) * v ^ 2)

theorem deBruijnNewmanRiemannSiegel_nonneg_lineRate
    (N : ℕ) {delta : ℝ} (hdelta : 0 < delta) (s : ℂ) :
    0 ≤ deBruijnNewmanRiemannSiegelLineRate N delta s := by
  unfold deBruijnNewmanRiemannSiegelLineRate
  positivity

theorem deBruijnNewmanRiemannSiegel_lineRate_mul_abs_le
    (N : ℕ) {delta : ℝ} (hdelta : 0 < delta) (s : ℂ) (v : ℝ) :
    deBruijnNewmanRiemannSiegelLineRate N delta s * |v| ≤
      Real.pi / 2 * v ^ 2 +
        deBruijnNewmanRiemannSiegelLineRate N delta s ^ 2 / (2 * Real.pi) := by
  let C := deBruijnNewmanRiemannSiegelLineRate N delta s
  have hpi : 0 < 2 * Real.pi := by positivity
  have hsq : 0 ≤ (Real.pi * |v| - C) ^ 2 := sq_nonneg _
  have hrewrite :
      Real.pi / 2 * v ^ 2 + C ^ 2 / (2 * Real.pi) =
        (Real.pi ^ 2 * v ^ 2 + C ^ 2) / (2 * Real.pi) := by
    field_simp
  rw [hrewrite, le_div_iff₀ hpi]
  have hC := deBruijnNewmanRiemannSiegel_nonneg_lineRate N hdelta s
  dsimp [C] at hC hsq ⊢
  nlinarith [sq_abs v]

theorem deBruijnNewmanRiemannSiegel_norm_lineIntegrand_le_majorant
    (N : ℕ) {delta : ℝ} (hdelta : 0 < delta) (s : ℂ) (v : ℝ) :
    ‖deBruijnNewmanRiemannSiegelLineIntegrand N s v‖ ≤
      deBruijnNewmanRiemannSiegelLineMajorant N delta s v := by
  let w := deBruijnNewmanRiemannSiegelLine N v
  have hpow := deBruijnNewmanRiemannSiegel_norm_cpow_neg_line_le N hdelta s v
  have hden := two_le_norm_deBruijnNewmanRiemannSiegelDenominator N v
  have hdenPos : 0 < ‖deBruijnNewmanRiemannSiegelDenominator w‖ :=
    lt_of_lt_of_le (by norm_num) hden
  have hpre :
      ‖deBruijnNewmanRiemannSiegelLineIntegrand N s v‖ ≤
        (1 / 2) * Real.exp
          (|s.re| * (deBruijnNewmanRiemannSiegelLineLogConstant N delta + delta * |v|) +
            |s.im| * Real.pi +
            (-Real.pi * v ^ 2 +
              Real.sqrt 2 * Real.pi * (N + 1 / 2) * v)) := by
    rw [deBruijnNewmanRiemannSiegelLineIntegrand,
      deBruijnNewmanRiemannSiegelKernel,
      deBruijnNewmanRiemannSiegelNumerator,
      norm_mul, norm_deBruijnNewmanRiemannSiegelDirection, mul_one, norm_div, norm_mul,
      norm_exp_deBruijnNewmanRiemannSiegel_gaussian]
    calc
      ‖w ^ (-s)‖ *
            Real.exp (-Real.pi * v ^ 2 +
              Real.sqrt 2 * Real.pi * (N + 1 / 2) * v) /
          ‖deBruijnNewmanRiemannSiegelDenominator w‖ ≤
          (Real.exp
              (|s.re| * (deBruijnNewmanRiemannSiegelLineLogConstant N delta + delta * |v|) +
                |s.im| * Real.pi) *
            Real.exp (-Real.pi * v ^ 2 +
              Real.sqrt 2 * Real.pi * (N + 1 / 2) * v)) /
              ‖deBruijnNewmanRiemannSiegelDenominator w‖ := by
        apply div_le_div_of_nonneg_right
        · exact mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _)
        · exact hdenPos.le
      _ ≤ (Real.exp
              (|s.re| * (deBruijnNewmanRiemannSiegelLineLogConstant N delta + delta * |v|) +
                |s.im| * Real.pi) *
            Real.exp (-Real.pi * v ^ 2 +
              Real.sqrt 2 * Real.pi * (N + 1 / 2) * v)) / 2 := by
        exact div_le_div_of_nonneg_left
          (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)) (by norm_num) hden
      _ = (1 / 2) * Real.exp
          (|s.re| * (deBruijnNewmanRiemannSiegelLineLogConstant N delta + delta * |v|) +
            |s.im| * Real.pi +
            (-Real.pi * v ^ 2 +
              Real.sqrt 2 * Real.pi * (N + 1 / 2) * v)) := by
        conv_rhs => rw [Real.exp_add]
        ring_nf
  apply hpre.trans
  rw [deBruijnNewmanRiemannSiegelLineMajorant]
  conv_rhs => rw [mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
  have hv : v ≤ |v| := le_abs_self v
  have hB : 0 ≤ Real.sqrt 2 * Real.pi * (N + 1 / 2) := by positivity
  have hshift :
      Real.sqrt 2 * Real.pi * (N + 1 / 2) * v ≤
        Real.sqrt 2 * Real.pi * (N + 1 / 2) * |v| :=
    mul_le_mul_of_nonneg_left hv hB
  have hcomplete := deBruijnNewmanRiemannSiegel_lineRate_mul_abs_le N hdelta s v
  simp only [deBruijnNewmanRiemannSiegelLineMajorantConstant, deBruijnNewmanRiemannSiegelLineRate] at hcomplete ⊢
  nlinarith

theorem deBruijnNewmanRiemannSiegel_integrable_lineMajorant
    (N : ℕ) (delta : ℝ) (s : ℂ) :
    Integrable (deBruijnNewmanRiemannSiegelLineMajorant N delta s) := by
  have hgauss : Integrable (fun v : ℝ => Real.exp (-(Real.pi / 2) * v ^ 2)) :=
    integrable_exp_neg_mul_sq (by positivity)
  change Integrable (fun v : ℝ =>
    ((1 / 2) * Real.exp (deBruijnNewmanRiemannSiegelLineMajorantConstant N delta s)) *
      Real.exp (-(Real.pi / 2) * v ^ 2))
  exact hgauss.const_mul
    ((1 / 2) * Real.exp (deBruijnNewmanRiemannSiegelLineMajorantConstant N delta s))

theorem deBruijnNewmanRiemannSiegel_norm_rawIntegral_le
    (N : ℕ) {delta : ℝ} (hdelta : 0 < delta) (s : ℂ) :
    ‖deBruijnNewmanRiemannSiegelRawIntegral N s‖ ≤
      ∫ v : ℝ, deBruijnNewmanRiemannSiegelLineMajorant N delta s v := by
  unfold deBruijnNewmanRiemannSiegelRawIntegral
  apply MeasureTheory.norm_integral_le_of_norm_le
    (deBruijnNewmanRiemannSiegel_integrable_lineMajorant N delta s)
  exact ae_of_all _ fun v => deBruijnNewmanRiemannSiegel_norm_lineIntegrand_le_majorant N hdelta s v

def deBruijnNewmanRiemannSiegelContourGaussianMass : ℝ :=
  ∫ v : ℝ, Real.exp (-(Real.pi / 2) * v ^ 2)

theorem deBruijnNewmanRiemannSiegelContourGaussianMass_nonneg : 0 ≤ deBruijnNewmanRiemannSiegelContourGaussianMass := by
  unfold deBruijnNewmanRiemannSiegelContourGaussianMass
  exact integral_nonneg fun _ => Real.exp_nonneg _

theorem deBruijnNewmanRiemannSiegel_integral_lineMajorant
    (N : ℕ) (delta : ℝ) (s : ℂ) :
    (∫ v : ℝ, deBruijnNewmanRiemannSiegelLineMajorant N delta s v) =
      ((1 / 2) * Real.exp (deBruijnNewmanRiemannSiegelLineMajorantConstant N delta s)) *
        deBruijnNewmanRiemannSiegelContourGaussianMass := by
  unfold deBruijnNewmanRiemannSiegelLineMajorant deBruijnNewmanRiemannSiegelContourGaussianMass
  rw [MeasureTheory.integral_const_mul]

def deBruijnNewmanRiemannSiegelRawDelta (a : ℝ) : ℝ :=
  1 / (8 * (|a| + 1))

theorem deBruijnNewmanRiemannSiegelRawDelta_pos (a : ℝ) : 0 < deBruijnNewmanRiemannSiegelRawDelta a := by
  unfold deBruijnNewmanRiemannSiegelRawDelta
  positivity

theorem deBruijnNewmanRiemannSiegelRawDelta_mul_abs_le (a : ℝ) :
    deBruijnNewmanRiemannSiegelRawDelta a * |a| ≤ 1 / 8 := by
  let A := |a|
  have hA : 0 ≤ A := abs_nonneg a
  have hden : 0 < 8 * (A + 1) := by positivity
  unfold deBruijnNewmanRiemannSiegelRawDelta
  change 1 / (8 * (A + 1)) * A ≤ 1 / 8
  rw [div_mul_eq_mul_div, div_le_iff₀ hden]
  nlinarith

theorem deBruijnNewmanRiemannSiegelRawDelta_sq_mul_abs_sq_div_pi_le (a : ℝ) :
    deBruijnNewmanRiemannSiegelRawDelta a ^ 2 * |a| ^ 2 / Real.pi ≤ 1 / 64 := by
  have hmul := deBruijnNewmanRiemannSiegelRawDelta_mul_abs_le a
  have hmulNonneg : 0 ≤ deBruijnNewmanRiemannSiegelRawDelta a * |a| :=
    mul_nonneg (deBruijnNewmanRiemannSiegelRawDelta_pos a).le (abs_nonneg a)
  have hsq : (deBruijnNewmanRiemannSiegelRawDelta a * |a|) ^ 2 ≤ (1 / 8 : ℝ) ^ 2 :=
    (sq_le_sq₀ hmulNonneg (by norm_num)).mpr hmul
  have hpi : 1 ≤ Real.pi := by linarith [Real.one_le_pi_div_two]
  have hnum : 0 ≤ deBruijnNewmanRiemannSiegelRawDelta a ^ 2 * |a| ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  calc
    deBruijnNewmanRiemannSiegelRawDelta a ^ 2 * |a| ^ 2 / Real.pi ≤
        deBruijnNewmanRiemannSiegelRawDelta a ^ 2 * |a| ^ 2 :=
      div_le_self hnum hpi
    _ = (deBruijnNewmanRiemannSiegelRawDelta a * |a|) ^ 2 := by ring
    _ ≤ (1 / 8 : ℝ) ^ 2 := hsq
    _ = 1 / 64 := by norm_num

theorem deBruijnNewmanRiemannSiegel_norm_rawIntegral_horizontal_le
    (N : ℕ) (a : ℝ) (s : ℂ) :
    ∃ C d : ℝ, 0 ≤ C ∧
      ∀ y : ℝ,
        ‖deBruijnNewmanRiemannSiegelRawIntegral N (s + (a * y : ℝ))‖ ≤
          C * Real.exp ((1 / 64 : ℝ) * y ^ 2 + d * |y|) := by
  let delta := deBruijnNewmanRiemannSiegelRawDelta a
  let A := |a|
  let S := |s.re|
  let L := deBruijnNewmanRiemannSiegelLineLogConstant N delta
  let B := Real.sqrt 2 * Real.pi * (N + 1 / 2)
  let D := delta * S + B
  let C0 := S * L + |s.im| * Real.pi + D ^ 2 / Real.pi
  let C := (1 / 2) * deBruijnNewmanRiemannSiegelContourGaussianMass * Real.exp C0
  let d := A * L
  refine ⟨C, d, ?_, ?_⟩
  · dsimp [C]
    exact mul_nonneg
      (mul_nonneg (by norm_num) deBruijnNewmanRiemannSiegelContourGaussianMass_nonneg)
      (Real.exp_nonneg _)
  intro y
  have hdelta : 0 < delta := deBruijnNewmanRiemannSiegelRawDelta_pos a
  have hA : 0 ≤ A := abs_nonneg a
  have hS : 0 ≤ S := abs_nonneg s.re
  have hL : 0 ≤ L := by
    dsimp [L, deBruijnNewmanRiemannSiegelLineLogConstant]
    positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hre : |(s + (a * y : ℝ)).re| ≤ S + A * |y| := by
    simp only [Complex.add_re, Complex.ofReal_re]
    calc
      |s.re + a * y| ≤ |s.re| + |a * y| := abs_add_le _ _
      _ = S + A * |y| := by simp [S, A, abs_mul]
  have him : |(s + (a * y : ℝ)).im| = |s.im| := by simp
  have hrate :
      deBruijnNewmanRiemannSiegelLineRate N delta (s + (a * y : ℝ)) ≤
        D + delta * A * |y| := by
    have hmul := mul_le_mul_of_nonneg_left hre hdelta.le
    calc
      deBruijnNewmanRiemannSiegelLineRate N delta (s + (a * y : ℝ)) =
          delta * |(s + (a * y : ℝ)).re| + B := by rfl
      _ ≤ delta * (S + A * |y|) + B := by
        simpa [add_comm] using add_le_add_right hmul B
      _ = D + delta * A * |y| := by dsimp [D]; ring
  have hrateNonneg :
      0 ≤ deBruijnNewmanRiemannSiegelLineRate N delta (s + (a * y : ℝ)) :=
    deBruijnNewmanRiemannSiegel_nonneg_lineRate N hdelta _
  have hrightNonneg : 0 ≤ D + delta * A * |y| := by
    exact add_nonneg hD (mul_nonneg (mul_nonneg hdelta.le hA) (abs_nonneg y))
  have hrateSq :
      deBruijnNewmanRiemannSiegelLineRate N delta (s + (a * y : ℝ)) ^ 2 ≤
        (D + delta * A * |y|) ^ 2 :=
    (sq_le_sq₀ hrateNonneg hrightNonneg).mpr hrate
  have hsplitSq :
      (D + delta * A * |y|) ^ 2 ≤
        2 * D ^ 2 + 2 * (delta * A) ^ 2 * y ^ 2 := by
    nlinarith [sq_nonneg (D - delta * A * |y|), sq_abs y]
  have hrateDiv :
      deBruijnNewmanRiemannSiegelLineRate N delta (s + (a * y : ℝ)) ^ 2 /
          (2 * Real.pi) ≤
        D ^ 2 / Real.pi +
          (delta ^ 2 * A ^ 2 / Real.pi) * y ^ 2 := by
    have hpi : 0 < 2 * Real.pi := by positivity
    rw [div_le_iff₀ hpi]
    field_simp
    nlinarith [hrateSq, hsplitSq]
  have hdeltaSq : delta ^ 2 * A ^ 2 / Real.pi ≤ 1 / 64 := by
    simpa [delta, A] using deBruijnNewmanRiemannSiegelRawDelta_sq_mul_abs_sq_div_pi_le a
  have hquad :
      (delta ^ 2 * A ^ 2 / Real.pi) * y ^ 2 ≤
        (1 / 64 : ℝ) * y ^ 2 :=
    mul_le_mul_of_nonneg_right hdeltaSq (sq_nonneg y)
  have hconstant :
      deBruijnNewmanRiemannSiegelLineMajorantConstant N delta (s + (a * y : ℝ)) ≤
        C0 + (1 / 64 : ℝ) * y ^ 2 + d * |y| := by
    unfold deBruijnNewmanRiemannSiegelLineMajorantConstant
    dsimp [C0, d]
    have hlinear := mul_le_mul_of_nonneg_right hre hL
    simp only [add_zero]
    dsimp [L, S, A] at hlinear
    nlinarith
  calc
    ‖deBruijnNewmanRiemannSiegelRawIntegral N (s + (a * y : ℝ))‖ ≤
        ∫ v : ℝ, deBruijnNewmanRiemannSiegelLineMajorant N delta (s + (a * y : ℝ)) v :=
      deBruijnNewmanRiemannSiegel_norm_rawIntegral_le N hdelta _
    _ = ((1 / 2) *
          Real.exp (deBruijnNewmanRiemannSiegelLineMajorantConstant N delta (s + (a * y : ℝ)))) *
        deBruijnNewmanRiemannSiegelContourGaussianMass :=
      deBruijnNewmanRiemannSiegel_integral_lineMajorant N delta _
    _ ≤ ((1 / 2) *
          Real.exp (C0 + (1 / 64 : ℝ) * y ^ 2 + d * |y|)) *
        deBruijnNewmanRiemannSiegelContourGaussianMass := by
      apply mul_le_mul_of_nonneg_right _ deBruijnNewmanRiemannSiegelContourGaussianMass_nonneg
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr hconstant) (by norm_num)
    _ = C * Real.exp ((1 / 64 : ℝ) * y ^ 2 + d * |y|) := by
      dsimp [C]
      rw [show C0 + (1 / 64 : ℝ) * y ^ 2 + d * |y| =
          C0 + ((1 / 64 : ℝ) * y ^ 2 + d * |y|) by ring,
        Real.exp_add]
      ring

theorem deBruijnNewmanRiemannSiegel_integrable_rawIntegral_horizontal
    (N : ℕ) (a : ℝ) (s : ℂ) :
    Integrable
      (fun y : ℝ =>
        deBruijnNewmanRiemannSiegelRawIntegral N (s + (a * y : ℝ)))
      (gaussianReal 0 2) := by
  obtain ⟨C, d, hC, hbound⟩ := deBruijnNewmanRiemannSiegel_norm_rawIntegral_horizontal_le N a s
  have hmajor :=
    (deBruijnNewmanRiemannSiegel_integrable_exp_sq_add_abs_gaussian (by norm_num : (1 / 64 : ℝ) < 1 / 4) d).const_mul C
  refine Integrable.mono' hmajor ?_ (ae_of_all _ hbound)
  exact (differentiable_deBruijnNewmanRiemannSiegelRawIntegral N).continuous.comp
    (by fun_prop) |>.aestronglyMeasurable

theorem deBruijnNewmanRiemannSiegel_norm_Gamma_le_realGamma {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz, Real.Gamma_eq_integral hz]
  calc
    ‖∫ x : ℝ in Set.Ioi 0, ((-x).exp : ℂ) * (x : ℂ) ^ (z - 1)‖ ≤
        ∫ x : ℝ in Set.Ioi 0,
          ‖((-x).exp : ℂ) * (x : ℂ) ^ (z - 1)‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ x : ℝ in Set.Ioi 0, Real.exp (-x) * x ^ (z.re - 1) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      rw [norm_mul, Complex.norm_of_nonneg (Real.exp_nonneg _),
        Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp

theorem deBruijnNewmanRiemannSiegel_realGamma_le_one {x : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ 2) :
    Real.Gamma x ≤ 1 := by
  have hconv := Real.convexOn_Gamma.2
    (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (show (2 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (show 0 ≤ 2 - x by linarith)
    (show 0 ≤ x - 1 by linarith)
    (show (2 - x) + (x - 1) = (1 : ℝ) by ring)
  calc
    Real.Gamma x =
        Real.Gamma ((2 - x) • (1 : ℝ) + (x - 1) • (2 : ℝ)) := by
      congr 1
      simp only [smul_eq_mul]
      ring
    _ ≤ (2 - x) • Real.Gamma 1 + (x - 1) • Real.Gamma 2 := hconv
    _ = 1 := by
      simp [smul_eq_mul]
      ring

theorem deBruijnNewmanRiemannSiegel_Gamma_add_nat (z : ℂ) (hz : z.im ≠ 0) :
    ∀ n : ℕ,
      Complex.Gamma (z + n) =
        (∏ k ∈ Finset.range n, (z + k)) * Complex.Gamma z := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hne : z + (n : ℂ) ≠ 0 := by
        intro h
        have him := congrArg Complex.im h
        simp only [Complex.add_im, Complex.natCast_im, add_zero, Complex.zero_im] at him
        exact hz him
      rw [Nat.cast_succ, ← add_assoc, Complex.Gamma_add_one _ hne, ih,
        Finset.prod_range_succ]
      ring

def deBruijnNewmanRiemannSiegelGammaLogConstant (delta : ℝ) : ℝ :=
  delta + |Real.log delta|

theorem deBruijnNewmanRiemannSiegel_realGamma_le_subquadratic
    {delta : ℝ} (hdelta : 0 < delta) {u : ℝ} (hu : 1 ≤ u) :
    Real.Gamma u ≤
      Real.exp
        (delta * (u + 1) ^ 2 + deBruijnNewmanRiemannSiegelGammaLogConstant delta * (u + 1)) := by
  by_cases hu2 : u ≤ 2
  · have hGamma := deBruijnNewmanRiemannSiegel_realGamma_le_one hu hu2
    have hexponent :
        0 ≤ delta * (u + 1) ^ 2 + deBruijnNewmanRiemannSiegelGammaLogConstant delta * (u + 1) := by
      unfold deBruijnNewmanRiemannSiegelGammaLogConstant
      positivity
    exact hGamma.trans (Real.one_le_exp hexponent)
  · have hu2' : 2 ≤ u := (lt_of_not_ge hu2).le
    let n := ⌈u⌉₊
    have hnLower : u ≤ (n : ℝ) := by
      exact Nat.le_ceil u
    have hnUpper : (n : ℝ) < u + 1 := by
      exact Nat.ceil_lt_add_one (by linarith)
    have hnPos : 0 < (n : ℝ) := lt_of_lt_of_le (by norm_num) (hu2'.trans hnLower)
    have hGamma : Real.Gamma u ≤ Real.Gamma ((n : ℝ) + 1) := by
      apply Real.Gamma_strictMonoOn_Ici.monotoneOn
      · exact hu2'
      · exact Set.mem_Ici.mpr (by linarith)
      · linarith
    have hfactorial : Real.Gamma ((n : ℝ) + 1) ≤ (n : ℝ) ^ n := by
      have hGammaNat : Real.Gamma ((n : ℝ) + 1) = (n.factorial : ℝ) := by
        simpa only [Nat.cast_add, Nat.cast_one] using Real.Gamma_nat_eq_factorial n
      rw [hGammaNat]
      exact_mod_cast Nat.factorial_le_pow n
    have hlog :
        Real.log (n : ℝ) ≤
          delta * (n : ℝ) + deBruijnNewmanRiemannSiegelGammaLogConstant delta := by
      have hlogMono :
          Real.log (n : ℝ) ≤ Real.log (1 + |(n : ℝ)|) := by
        apply Real.log_le_log hnPos
        simp only [abs_of_nonneg hnPos.le]
        linarith
      exact hlogMono.trans (by
        simpa [deBruijnNewmanRiemannSiegelGammaLogConstant, abs_of_nonneg hnPos.le, add_assoc] using
          deBruijnNewmanRiemannSiegel_log_one_add_abs_le hdelta (n : ℝ))
    have hK : 0 ≤ deBruijnNewmanRiemannSiegelGammaLogConstant delta := by
      unfold deBruijnNewmanRiemannSiegelGammaLogConstant
      positivity
    have hexponent :
        (n : ℝ) * Real.log (n : ℝ) ≤
          delta * (u + 1) ^ 2 + deBruijnNewmanRiemannSiegelGammaLogConstant delta * (u + 1) := by
      have hmul := mul_le_mul_of_nonneg_left hlog hnPos.le
      have hnLe : (n : ℝ) ≤ u + 1 := hnUpper.le
      have hsquare : (n : ℝ) ^ 2 ≤ (u + 1) ^ 2 :=
        (sq_le_sq₀ hnPos.le (by linarith)).mpr hnLe
      have hquad := mul_le_mul_of_nonneg_left hsquare hdelta.le
      have hlinear := mul_le_mul_of_nonneg_left hnLe hK
      nlinarith
    calc
      Real.Gamma u ≤ Real.Gamma ((n : ℝ) + 1) := hGamma
      _ ≤ (n : ℝ) ^ n := hfactorial
      _ = Real.exp ((n : ℝ) * Real.log (n : ℝ)) := by
        rw [Real.exp_nat_mul, Real.exp_log hnPos]
      _ ≤ Real.exp
          (delta * (u + 1) ^ 2 + deBruijnNewmanRiemannSiegelGammaLogConstant delta * (u + 1)) :=
        Real.exp_le_exp.mpr hexponent

theorem deBruijnNewmanRiemannSiegel_norm_Gamma_le_exp_linear_of_re_lt_one
    {z : ℂ} (him : z.im ≠ 0) (hre : z.re < 1) :
    ‖Complex.Gamma z‖ ≤
      Real.exp
        (max 1 |z.im|⁻¹ * (2 + |z.re|)) := by
  let n := ⌈1 - z.re⌉₊
  let q := max 1 |z.im|⁻¹
  have hargNonneg : 0 ≤ 1 - z.re := by linarith
  have hnLower : 1 - z.re ≤ (n : ℝ) := Nat.le_ceil _
  have hnUpper : (n : ℝ) < (1 - z.re) + 1 :=
    Nat.ceil_lt_add_one hargNonneg
  have hshiftReLower : 1 ≤ (z + (n : ℂ)).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    linarith
  have hshiftReUpper : (z + (n : ℂ)).re ≤ 2 := by
    simp only [Complex.add_re, Complex.natCast_re]
    linarith
  have hshiftGamma : ‖Complex.Gamma (z + (n : ℂ))‖ ≤ 1 := by
    exact (deBruijnNewmanRiemannSiegel_norm_Gamma_le_realGamma (lt_of_lt_of_le (by norm_num) hshiftReLower)).trans
      (deBruijnNewmanRiemannSiegel_realGamma_le_one hshiftReLower hshiftReUpper)
  have hfactor (k : ℕ) : |z.im| ≤ ‖z + (k : ℂ)‖ := by
    calc
      |z.im| = |(z + (k : ℂ)).im| := by simp
      _ ≤ ‖z + (k : ℂ)‖ := Complex.abs_im_le_norm _
  have hprod :
      |z.im| ^ n ≤ ‖∏ k ∈ Finset.range n, (z + (k : ℂ))‖ := by
    rw [norm_prod]
    calc
      |z.im| ^ n = ∏ _k ∈ Finset.range n, |z.im| := by simp
      _ ≤ ∏ k ∈ Finset.range n, ‖z + (k : ℂ)‖ := by
        exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun k _ => hfactor k)
  have himPos : 0 < |z.im| := abs_pos.mpr him
  have hrec := deBruijnNewmanRiemannSiegel_Gamma_add_nat z him n
  have hmul : |z.im| ^ n * ‖Complex.Gamma z‖ ≤ 1 := by
    calc
      |z.im| ^ n * ‖Complex.Gamma z‖ ≤
          ‖∏ k ∈ Finset.range n, (z + (k : ℂ))‖ * ‖Complex.Gamma z‖ :=
        mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
      _ = ‖(∏ k ∈ Finset.range n, (z + (k : ℂ))) * Complex.Gamma z‖ := by
        rw [norm_mul]
      _ = ‖Complex.Gamma (z + (n : ℂ))‖ := by rw [← hrec]
      _ ≤ 1 := hshiftGamma
  have hdiv : ‖Complex.Gamma z‖ ≤ |z.im|⁻¹ ^ n := by
    calc
      ‖Complex.Gamma z‖ ≤ 1 / |z.im| ^ n := by
        rw [le_div_iff₀ (pow_pos himPos n)]
        simpa [mul_comm] using hmul
      _ = |z.im|⁻¹ ^ n := by simp [one_div]
  have hqNonneg : 0 ≤ q := by dsimp [q]; positivity
  have hqOne : 1 ≤ q := le_max_left _ _
  have hqPow : |z.im|⁻¹ ^ n ≤ q ^ n := by
    exact pow_le_pow_left₀ (inv_nonneg.mpr (abs_nonneg _)) (le_max_right _ _) n
  have hqExp : q ≤ Real.exp q := by
    linarith [Real.add_one_le_exp q]
  have hpowExp : q ^ n ≤ Real.exp ((n : ℝ) * q) := by
    calc
      q ^ n ≤ Real.exp q ^ n := pow_le_pow_left₀ hqNonneg hqExp n
      _ = Real.exp ((n : ℝ) * q) := by rw [Real.exp_nat_mul]
  have hnAbs : (n : ℝ) ≤ 2 + |z.re| := by
    have hreAbs : -z.re ≤ |z.re| := neg_le_abs _
    linarith
  have hexpMono :
      Real.exp ((n : ℝ) * q) ≤ Real.exp (q * (2 + |z.re|)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  exact hdiv.trans (hqPow.trans (hpowExp.trans (by simpa [mul_comm] using hexpMono)))

def deBruijnNewmanRiemannSiegelGammaDelta (a : ℝ) : ℝ :=
  1 / (256 * (|a| + 1) ^ 2)

theorem deBruijnNewmanRiemannSiegelGammaDelta_pos (a : ℝ) : 0 < deBruijnNewmanRiemannSiegelGammaDelta a := by
  unfold deBruijnNewmanRiemannSiegelGammaDelta
  positivity

theorem deBruijnNewmanRiemannSiegelGammaDelta_quad (a : ℝ) :
    2 * deBruijnNewmanRiemannSiegelGammaDelta a * |a| ^ 2 ≤ 1 / 128 := by
  let A := |a|
  have hA : 0 ≤ A := abs_nonneg a
  have hden : 0 < 256 * (A + 1) ^ 2 := by positivity
  unfold deBruijnNewmanRiemannSiegelGammaDelta
  dsimp [A] at hA hden ⊢
  rw [show 2 * (1 / (256 * (|a| + 1) ^ 2)) * |a| ^ 2 =
      (2 * |a| ^ 2) / (256 * (|a| + 1) ^ 2) by ring,
    div_le_iff₀ hden]
  nlinarith [sq_nonneg |a|]

theorem deBruijnNewmanRiemannSiegel_norm_Gamma_horizontal_le
    (a : ℝ) {s : ℂ} (him : s.im ≠ 0) :
    ∃ C d : ℝ, 0 ≤ C ∧ 0 ≤ d ∧
      ∀ y : ℝ,
        ‖Complex.Gamma (s + (a * y : ℝ))‖ ≤
          C * Real.exp ((1 / 128 : ℝ) * y ^ 2 + d * |y|) := by
  let delta := deBruijnNewmanRiemannSiegelGammaDelta a
  let A := |a|
  let S := |s.re + 1|
  let K := deBruijnNewmanRiemannSiegelGammaLogConstant delta
  let q := max 1 |s.im|⁻¹
  let Cpos := 2 * delta * S ^ 2 + K * S
  let dpos := K * A
  let Cneg := q * (2 + |s.re|)
  let dneg := q * A
  let C0 := max Cpos Cneg
  let d := max dpos dneg
  let C := Real.exp C0
  refine ⟨C, d, Real.exp_nonneg _, ?_, ?_⟩
  · dsimp [d, dpos, dneg, K, q, A]
    positivity
  intro y
  have hdelta : 0 < delta := deBruijnNewmanRiemannSiegelGammaDelta_pos a
  have hA : 0 ≤ A := abs_nonneg a
  have hS : 0 ≤ S := abs_nonneg (s.re + 1)
  have hK : 0 ≤ K := by dsimp [K, deBruijnNewmanRiemannSiegelGammaLogConstant]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hCpos : 0 ≤ Cpos := by dsimp [Cpos]; positivity
  have hCneg : 0 ≤ Cneg := by dsimp [Cneg]; positivity
  have hCposMax : Cpos ≤ C0 := by dsimp [C0]; exact le_max_left _ _
  have hCnegMax : Cneg ≤ C0 := by dsimp [C0]; exact le_max_right _ _
  have hdpos : dpos ≤ d := by dsimp [d]; exact le_max_left _ _
  have hdneg : dneg ≤ d := by dsimp [d]; exact le_max_right _ _
  let z : ℂ := s + (a * y : ℝ)
  have himz : z.im ≠ 0 := by simpa [z] using him
  by_cases hzre : 1 ≤ z.re
  · have hGamma := (deBruijnNewmanRiemannSiegel_norm_Gamma_le_realGamma
        (lt_of_lt_of_le (by norm_num) hzre)).trans
        (deBruijnNewmanRiemannSiegel_realGamma_le_subquadratic hdelta hzre)
    have hzreFormula : z.re + 1 = (s.re + 1) + a * y := by
      simp [z]
      ring
    have hsquare : (z.re + 1) ^ 2 ≤ 2 * S ^ 2 + 2 * A ^ 2 * y ^ 2 := by
      rw [hzreFormula]
      have hab : (a * y) ^ 2 = A ^ 2 * y ^ 2 := by
        dsimp [A]
        rw [mul_pow, sq_abs]
      have hSsq : S ^ 2 = (s.re + 1) ^ 2 := by
        dsimp [S]
        rw [sq_abs]
      nlinarith [sq_nonneg ((s.re + 1) - a * y)]
    have hlinear : K * (z.re + 1) ≤ K * (S + A * |y|) := by
      apply mul_le_mul_of_nonneg_left _ hK
      rw [hzreFormula]
      calc
        (s.re + 1) + a * y ≤ |(s.re + 1) + a * y| := le_abs_self _
        _ ≤ |s.re + 1| + |a * y| := abs_add_le _ _
        _ = S + A * |y| := by simp [S, A, abs_mul]
    have hquad : 2 * delta * A ^ 2 * y ^ 2 ≤ (1 / 128 : ℝ) * y ^ 2 := by
      exact mul_le_mul_of_nonneg_right
        (by simpa [delta, A] using deBruijnNewmanRiemannSiegelGammaDelta_quad a) (sq_nonneg y)
    have hexponent :
        delta * (z.re + 1) ^ 2 + K * (z.re + 1) ≤
          C0 + (1 / 128 : ℝ) * y ^ 2 + d * |y| := by
      have hsquareMul := mul_le_mul_of_nonneg_left hsquare hdelta.le
      have hdMul := mul_le_mul_of_nonneg_right hdpos (abs_nonneg y)
      dsimp [Cpos, dpos] at hCposMax hdpos ⊢
      nlinarith
    calc
      ‖Complex.Gamma z‖ ≤
          Real.exp (delta * (z.re + 1) ^ 2 + K * (z.re + 1)) := hGamma
      _ ≤ Real.exp (C0 + ((1 / 128 : ℝ) * y ^ 2 + d * |y|)) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      _ = C * Real.exp ((1 / 128 : ℝ) * y ^ 2 + d * |y|) := by
        dsimp [C]
        rw [Real.exp_add]
  · have hzre' : z.re < 1 := lt_of_not_ge hzre
    have hGamma := deBruijnNewmanRiemannSiegel_norm_Gamma_le_exp_linear_of_re_lt_one himz hzre'
    have habs : |z.re| ≤ |s.re| + A * |y| := by
      dsimp [z]
      calc
        |s.re + a * y| ≤ |s.re| + |a * y| := abs_add_le _ _
        _ = |s.re| + A * |y| := by simp [A, abs_mul]
    have hlinear : q * (2 + |z.re|) ≤ Cneg + dneg * |y| := by
      have hmul := mul_le_mul_of_nonneg_left habs hq
      dsimp [Cneg, dneg]
      dsimp [q, A] at hmul ⊢
      nlinarith
    have htarget :
        q * (2 + |z.re|) ≤
          C0 + (1 / 128 : ℝ) * y ^ 2 + d * |y| := by
      have hdMul := mul_le_mul_of_nonneg_right hdneg (abs_nonneg y)
      nlinarith [sq_nonneg y]
    calc
      ‖Complex.Gamma z‖ ≤ Real.exp (q * (2 + |z.re|)) := by
        simpa [q, z] using hGamma
      _ ≤ Real.exp (C0 + ((1 / 128 : ℝ) * y ^ 2 + d * |y|)) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      _ = C * Real.exp ((1 / 128 : ℝ) * y ^ 2 + d * |y|) := by
        dsimp [C]
        rw [Real.exp_add]

theorem deBruijnNewmanRiemannSiegel_norm_prefactor_horizontal_le
    (a : ℝ) {s : ℂ} (him : s.im ≠ 0) :
    ∃ C d : ℝ, 0 ≤ C ∧ 0 ≤ d ∧
      ∀ y : ℝ,
        ‖deBruijnNewmanRiemannSiegelPrefactor (s + (a * y : ℝ))‖ ≤
          C * Real.exp ((1 / 128 : ℝ) * y ^ 2 + d * |y|) := by
  obtain ⟨Cg, dg, hCg, hdg, hGamma⟩ :=
    deBruijnNewmanRiemannSiegel_norm_Gamma_horizontal_le (a / 2) (s := s / 2) (by
      have hIm : (s / 2).im = s.im / 2 := by
        norm_num [Complex.div_im]
      rw [hIm]
      exact div_ne_zero him (by norm_num))
  let A := |a|
  let B := ‖s‖ + A + 1
  let P := |Real.log Real.pi| / 2
  let C := (1 / 8) * B ^ 2 * Real.exp (P * |s.re|) * Cg
  let d := 2 + P * A + dg
  refine ⟨C, d, ?_, ?_, ?_⟩
  · dsimp [C, B, P, A]
    positivity
  · dsimp [d, P, A]
    positivity
  intro y
  let z : ℂ := s + (a * y : ℝ)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B, A]; positivity
  have hBone : 1 ≤ B := by
    dsimp [B]
    nlinarith [norm_nonneg s]
  have hzNorm : ‖z‖ ≤ B * (1 + |y|) := by
    calc
      ‖z‖ ≤ ‖s‖ + ‖((a * y : ℝ) : ℂ)‖ := by
        dsimp [z]
        exact norm_add_le _ _
      _ = ‖s‖ + A * |y| := by simp [A]
      _ ≤ B * (1 + |y|) := by
        dsimp [B]
        nlinarith [abs_nonneg y, norm_nonneg s]
  have hzSubNorm : ‖z - 1‖ ≤ 2 * B * (1 + |y|) := by
    calc
      ‖z - 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ B * (1 + |y|) + 1 := by
        norm_num only [norm_one]
        exact add_le_add hzNorm le_rfl
      _ ≤ 2 * B * (1 + |y|) := by
        nlinarith [abs_nonneg y]
  have honeExp : 1 + |y| ≤ Real.exp |y| := by
    simpa [add_comm] using Real.add_one_le_exp |y|
  have hpoly : ‖z * (z - 1) / 2‖ ≤ B ^ 2 * Real.exp (2 * |y|) := by
    rw [norm_div, norm_mul]
    norm_num only [Complex.norm_ofNat]
    calc
      ‖z‖ * ‖z - 1‖ / 2 ≤
          (B * (1 + |y|)) * (2 * B * (1 + |y|)) / 2 := by
        gcongr
      _ = B ^ 2 * (1 + |y|) ^ 2 := by ring
      _ ≤ B ^ 2 * (Real.exp |y|) ^ 2 := by
        gcongr
      _ = B ^ 2 * Real.exp (2 * |y|) := by
        rw [show (2 : ℝ) * |y| = (2 : ℕ) * |y| by norm_num,
          Real.exp_nat_mul]
  have hzReAbs : |z.re| ≤ |s.re| + A * |y| := by
    dsimp [z]
    calc
      |s.re + a * y| ≤ |s.re| + |a * y| := abs_add_le _ _
      _ = |s.re| + A * |y| := by simp [A, abs_mul]
  have hpi :
      ‖(Real.pi : ℂ) ^ (-z / 2)‖ ≤
        Real.exp (P * |s.re| + P * A * |y|) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
      Real.rpow_def_of_pos Real.pi_pos]
    apply Real.exp_le_exp.mpr
    have hP : 0 ≤ P := by dsimp [P]; positivity
    have hbase : Real.log Real.pi * (-z.re / 2) ≤ P * |z.re| := by
      have habsMul :
          Real.log Real.pi * (-z.re) ≤
            |Real.log Real.pi| * |z.re| := by
        calc
          Real.log Real.pi * (-z.re) ≤
              |Real.log Real.pi * (-z.re)| := le_abs_self _
          _ = |Real.log Real.pi| * |z.re| := by rw [abs_mul, abs_neg]
      dsimp [P]
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hzReAbs hP
    have hre : (-z / 2).re = -z.re / 2 := by
      norm_num [Complex.div_re]
    rw [hre]
    exact hbase.trans (by
      calc
        P * |z.re| ≤ P * (|s.re| + A * |y|) := hmul
        _ = P * |s.re| + P * A * |y| := by ring)
  have hGamma' := hGamma y
  have hGammaAt :
      ‖Complex.Gamma (z / 2)‖ ≤
        Cg * Real.exp ((1 / 128 : ℝ) * y ^ 2 + dg * |y|) := by
    convert hGamma' using 1
    dsimp [z]
    congr 2
    push_cast
    ring
  unfold deBruijnNewmanRiemannSiegelPrefactor
  change ‖(1 / 8 : ℂ) * (z * (z - 1) / 2) *
      (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2)‖ ≤ _
  rw [norm_mul, norm_mul, norm_mul]
  have hconst : ‖(1 / 8 : ℂ)‖ = (1 / 8 : ℝ) := by norm_num
  rw [hconst]
  calc
    (1 / 8 : ℝ) * ‖z * (z - 1) / 2‖ *
          ‖(Real.pi : ℂ) ^ (-z / 2)‖ * ‖Complex.Gamma (z / 2)‖ ≤
        (1 / 8) * (B ^ 2 * Real.exp (2 * |y|)) *
          Real.exp (P * |s.re| + P * A * |y|) *
          (Cg * Real.exp ((1 / 128 : ℝ) * y ^ 2 + dg * |y|)) := by
      gcongr
    _ = C * Real.exp ((1 / 128 : ℝ) * y ^ 2 + d * |y|) := by
      dsimp [C, d]
      have hexp :
          Real.exp (2 * |y|) * Real.exp (P * |s.re| + P * A * |y|) *
              Real.exp ((1 / 128 : ℝ) * y ^ 2 + dg * |y|) =
            Real.exp (P * |s.re|) *
              Real.exp ((1 / 128 : ℝ) * y ^ 2 + (2 + P * A + dg) * |y|) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      calc
        (1 / 8) * (B ^ 2 * Real.exp (2 * |y|)) *
              Real.exp (P * |s.re| + P * A * |y|) *
              (Cg * Real.exp ((1 / 128 : ℝ) * y ^ 2 + dg * |y|)) =
            ((1 / 8) * B ^ 2 * Cg) *
              (Real.exp (2 * |y|) *
                Real.exp (P * |s.re| + P * A * |y|) *
                Real.exp ((1 / 128 : ℝ) * y ^ 2 + dg * |y|)) := by ring
        _ = ((1 / 8) * B ^ 2 * Cg) *
              (Real.exp (P * |s.re|) *
                Real.exp ((1 / 128 : ℝ) * y ^ 2 + (2 + P * A + dg) * |y|)) := by
            rw [hexp]
        _ = (1 / 8) * B ^ 2 * Real.exp (P * |s.re|) * Cg *
              Real.exp ((1 / 128 : ℝ) * y ^ 2 + (2 + P * A + dg) * |y|) := by ring

theorem deBruijnNewmanRiemannSiegel_integrable_prefactor_horizontal
    (a : ℝ) {s : ℂ} (him : s.im ≠ 0) :
    Integrable
      (fun y : ℝ => deBruijnNewmanRiemannSiegelPrefactor (s + (a * y : ℝ)))
      (gaussianReal 0 2) := by
  obtain ⟨C, d, _hC, _hd, hbound⟩ := deBruijnNewmanRiemannSiegel_norm_prefactor_horizontal_le a him
  have hmajor :=
    (deBruijnNewmanRiemannSiegel_integrable_exp_sq_add_abs_gaussian
      (by norm_num : (1 / 128 : ℝ) < 1 / 4) d).const_mul C
  refine Integrable.mono' hmajor ?_ (ae_of_all _ hbound)
  exact (continuous_iff_continuousAt.mpr fun y => by
    have hg : ContinuousAt (fun x : ℝ => s + ((a * x : ℝ) : ℂ)) y := by fun_prop
    exact ContinuousAt.comp'
      (f := fun x : ℝ => s + ((a * x : ℝ) : ℂ))
      (g := deBruijnNewmanRiemannSiegelPrefactor)
      (differentiableAt_deBruijnNewmanRiemannSiegelPrefactor_of_isNoninteger
        (deBruijnNewmanRiemannSiegel_isNoninteger_of_im_ne_zero him (a * y))).continuousAt hg
    ).aestronglyMeasurable

theorem deBruijnNewmanRiemannSiegel_integrable_R0N_horizontal
    (N : ℕ) (a : ℝ) {s : ℂ} (him : s.im ≠ 0) :
    Integrable
      (fun y : ℝ => deBruijnNewmanRiemannSiegelR0N N (s + (a * y : ℝ)))
      (gaussianReal 0 2) := by
  obtain ⟨Cp, dp, _hCp, _hdp, hp⟩ := deBruijnNewmanRiemannSiegel_norm_prefactor_horizontal_le a him
  obtain ⟨Cr, dr, _hCr, hr⟩ := deBruijnNewmanRiemannSiegel_norm_rawIntegral_horizontal_le N a s
  have hmajor :=
    (deBruijnNewmanRiemannSiegel_integrable_exp_sq_add_abs_gaussian
      (by norm_num : (3 / 128 : ℝ) < 1 / 4) (dp + dr)).const_mul (Cp * Cr)
  refine Integrable.mono' hmajor ?_ ?_
  · exact (continuous_iff_continuousAt.mpr fun y => by
      let z : ℂ := s + (a * y : ℝ)
      have hzmem : z ∈ deBruijnNewmanRiemannSiegelNonintegerDomain := by
        rw [mem_deBruijnNewmanRiemannSiegelNonintegerDomain_iff]
        exact deBruijnNewmanRiemannSiegel_isNoninteger_of_im_ne_zero him (a * y)
      have hdiff :=
        (differentiableOn_deBruijnNewmanRiemannSiegelR0N_nonintegerDomain N z hzmem).differentiableAt
          (isOpen_deBruijnNewmanRiemannSiegelNonintegerDomain.mem_nhds hzmem)
      have hg : ContinuousAt (fun x : ℝ => s + ((a * x : ℝ) : ℂ)) y := by fun_prop
      exact ContinuousAt.comp'
        (f := fun x : ℝ => s + ((a * x : ℝ) : ℂ))
        (g := deBruijnNewmanRiemannSiegelR0N N)
        hdiff.continuousAt hg
      ).aestronglyMeasurable
  · apply ae_of_all
    intro y
    unfold deBruijnNewmanRiemannSiegelR0N
    rw [norm_mul]
    calc
      ‖deBruijnNewmanRiemannSiegelPrefactor (s + (a * y : ℝ))‖ *
          ‖deBruijnNewmanRiemannSiegelRawIntegral N (s + (a * y : ℝ))‖ ≤
        (Cp * Real.exp ((1 / 128 : ℝ) * y ^ 2 + dp * |y|)) *
          (Cr * Real.exp ((1 / 64 : ℝ) * y ^ 2 + dr * |y|)) := by
        exact mul_le_mul (hp y) (hr y) (norm_nonneg _) (by positivity)
      _ = (Cp * Cr) *
          Real.exp ((3 / 128 : ℝ) * y ^ 2 + (dp + dr) * |y|) := by
        rw [show Cp * Real.exp ((1 / 128 : ℝ) * y ^ 2 + dp * |y|) *
              (Cr * Real.exp ((1 / 64 : ℝ) * y ^ 2 + dr * |y|)) =
            (Cp * Cr) *
              (Real.exp ((1 / 128 : ℝ) * y ^ 2 + dp * |y|) *
                Real.exp ((1 / 64 : ℝ) * y ^ 2 + dr * |y|)) by ring,
          ← Real.exp_add]
        ring_nf

theorem deBruijnNewmanRiemannSiegel_R0N_adjacent_decomposition (N : ℕ) (s : ℂ) :
    deBruijnNewmanRiemannSiegelR0N N s =
      deBruijnNewmanRiemannSiegelR0Term (N + 1) s +
        deBruijnNewmanRiemannSiegelR0N (N + 1) s := by
  unfold deBruijnNewmanRiemannSiegelR0N deBruijnNewmanRiemannSiegelR0Term
  rw [deBruijnNewmanRiemannSiegelRawIntegral_adjacent_shift]
  ring

theorem deBruijnNewmanRiemannSiegel_integrable_R0Term_horizontal
    (N : ℕ) (a : ℝ) {s : ℂ} (him : s.im ≠ 0) :
    Integrable
      (fun y : ℝ =>
        deBruijnNewmanRiemannSiegelR0Term (N + 1) (s + (a * y : ℝ)))
      (gaussianReal 0 2) := by
  have hN := deBruijnNewmanRiemannSiegel_integrable_R0N_horizontal N a him
  have hN1 := deBruijnNewmanRiemannSiegel_integrable_R0N_horizontal (N + 1) a him
  refine (hN.sub hN1).congr (ae_of_all _ fun y => ?_)
  change deBruijnNewmanRiemannSiegelR0N N (s + (a * y : ℝ)) -
      deBruijnNewmanRiemannSiegelR0N (N + 1) (s + (a * y : ℝ)) =
        deBruijnNewmanRiemannSiegelR0Term (N + 1) (s + (a * y : ℝ))
  rw [deBruijnNewmanRiemannSiegel_R0N_adjacent_decomposition N]
  ring

theorem deBruijnNewmanRiemannSiegel_integral_neg_gaussian (f : ℝ → ℂ) :
    (∫ y : ℝ, f (-y) ∂gaussianReal 0 2) =
      ∫ y : ℝ, f y ∂gaussianReal 0 2 := by
  let hneg : MeasurePreserving (fun y : ℝ => -y)
      (gaussianReal 0 2) (gaussianReal 0 2) :=
    ⟨by fun_prop, by
      simpa using (gaussianReal_map_neg (μ := 0) (v := 2))⟩
  exact hneg.integral_comp measurableEmbedding_neg f

theorem deBruijnNewmanRiemannSiegelHeatEvolve_reflect (t : ℝ) (F : ℂ → ℂ) (s : ℂ) :
    deBruijnNewmanRiemannSiegelHeatEvolve t (deBruijnNewmanRiemannSiegelReflect F) s =
      deBruijnNewmanRiemannSiegelReflect (deBruijnNewmanRiemannSiegelHeatEvolve t F) s := by
  unfold deBruijnNewmanRiemannSiegelHeatEvolve deBruijnNewmanRiemannSiegelReflect
  rw [← integral_conj]
  apply integral_congr_ae
  apply ae_of_all
  intro y
  unfold deBruijnNewmanRiemannSiegelHeatShift
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat, map_add, map_mul,
    map_div₀, Complex.conj_ofReal]
  rw [map_ofNat]

theorem deBruijnNewmanRiemannSiegel_integral_reflect_neg_shift
    (t : ℝ) (F : ℂ → ℂ) (s : ℂ) :
    (∫ y : ℝ,
        deBruijnNewmanRiemannSiegelReflect F (s - deBruijnNewmanRiemannSiegelHeatShift t y)
        ∂gaussianReal 0 2) =
      deBruijnNewmanRiemannSiegelReflect (deBruijnNewmanRiemannSiegelHeatEvolve t F) s := by
  calc
    (∫ y : ℝ,
        deBruijnNewmanRiemannSiegelReflect F (s - deBruijnNewmanRiemannSiegelHeatShift t y)
        ∂gaussianReal 0 2) =
      ∫ y : ℝ,
        deBruijnNewmanRiemannSiegelReflect F (s + deBruijnNewmanRiemannSiegelHeatShift t y)
        ∂gaussianReal 0 2 := by
      simpa [deBruijnNewmanRiemannSiegelHeatShift, sub_eq_add_neg] using
        deBruijnNewmanRiemannSiegel_integral_neg_gaussian
          (fun y : ℝ =>
            deBruijnNewmanRiemannSiegelReflect F (s + deBruijnNewmanRiemannSiegelHeatShift t y))
    _ = deBruijnNewmanRiemannSiegelReflect (deBruijnNewmanRiemannSiegelHeatEvolve t F) s :=
      deBruijnNewmanRiemannSiegelHeatEvolve_reflect t F s

theorem deBruijnNewmanRiemannSiegel_integrable_reflect_horizontal_of_integrable
    (F : ℂ → ℂ) (a : ℝ) (s : ℂ)
    (hF : Integrable (fun y : ℝ => F ((starRingEnd ℂ) s + (a * y : ℝ)))
      (gaussianReal 0 2)) :
    Integrable
      (fun y : ℝ => deBruijnNewmanRiemannSiegelReflect F (s + (a * y : ℝ)))
      (gaussianReal 0 2) := by
  refine Integrable.mono' hF.norm ?_ ?_
  · simpa [deBruijnNewmanRiemannSiegelReflect] using
      Complex.continuous_conj.comp_aestronglyMeasurable hF.aestronglyMeasurable
  · apply ae_of_all
    intro y
    simp [deBruijnNewmanRiemannSiegelReflect]

theorem deBruijnNewmanRiemannSiegel_integrable_reflect_R0Term_horizontal
    (N : ℕ) (a : ℝ) {s : ℂ} (him : s.im ≠ 0) :
    Integrable
      (fun y : ℝ => deBruijnNewmanRiemannSiegelReflect
        (deBruijnNewmanRiemannSiegelR0Term (N + 1)) (s + (a * y : ℝ)))
      (gaussianReal 0 2) := by
  apply deBruijnNewmanRiemannSiegel_integrable_reflect_horizontal_of_integrable
  apply deBruijnNewmanRiemannSiegel_integrable_R0Term_horizontal N a
  simpa using him

theorem deBruijnNewmanRiemannSiegel_integrable_reflect_R0N_horizontal
    (N : ℕ) (a : ℝ) {s : ℂ} (him : s.im ≠ 0) :
    Integrable
      (fun y : ℝ => deBruijnNewmanRiemannSiegelReflect
        (deBruijnNewmanRiemannSiegelR0N N) (s + (a * y : ℝ)))
      (gaussianReal 0 2) := by
  apply deBruijnNewmanRiemannSiegel_integrable_reflect_horizontal_of_integrable
  apply deBruijnNewmanRiemannSiegel_integrable_R0N_horizontal N a
  simpa using him

theorem deBruijnNewmanRiemannSiegel_reflected_base_im_ne_zero {z : ℂ} (hz : z.re ≠ 0) :
    ((1 - Complex.I * z) / 2).im ≠ 0 := by
  have hcalc : ((1 - Complex.I * z) / 2).im = -z.re / 2 := by
    norm_num [Complex.div_im, Complex.mul_im]
  rw [hcalc]
  exact div_ne_zero (neg_ne_zero.mpr hz) (by norm_num)

theorem deBruijnNewmanH_riemannSiegel_finite_expansion
    {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : z.re ≠ 0) (N : ℕ) :
    deBruijnNewmanH t z =
      (∑ k ∈ Finset.range N,
        deBruijnNewmanRiemannSiegelHeatTerm t (k + 1) ((1 + Complex.I * z) / 2)) +
      (∑ k ∈ Finset.range N,
        deBruijnNewmanRiemannSiegelReflect (deBruijnNewmanRiemannSiegelHeatTerm t (k + 1))
          ((1 - Complex.I * z) / 2)) +
      deBruijnNewmanRiemannSiegelHeatRemainder t N ((1 + Complex.I * z) / 2) +
      deBruijnNewmanRiemannSiegelReflect (deBruijnNewmanRiemannSiegelHeatRemainder t N)
        ((1 - Complex.I * z) / 2) := by
  let a := Real.sqrt t / 2
  let p := (1 + Complex.I * z) / 2
  let q := (1 - Complex.I * z) / 2
  have hpim : p.im ≠ 0 := by
    exact deBruijnNewmanRiemannSiegel_base_im_ne_zero hz
  have hqim : q.im ≠ 0 := by
    exact deBruijnNewmanRiemannSiegel_reflected_base_im_ne_zero hz
  have hterm (k : ℕ) : Integrable
      (fun y : ℝ => deBruijnNewmanRiemannSiegelR0Term (k + 1) (p + (a * y : ℝ)))
      (gaussianReal 0 2) :=
    deBruijnNewmanRiemannSiegel_integrable_R0Term_horizontal k a hpim
  have hsum : Integrable
      (fun y : ℝ => ∑ k ∈ Finset.range N,
        deBruijnNewmanRiemannSiegelR0Term (k + 1) (p + (a * y : ℝ)))
      (gaussianReal 0 2) :=
    integrable_finsetSum (Finset.range N) (fun k _ => hterm k)
  have hrem : Integrable
      (fun y : ℝ => deBruijnNewmanRiemannSiegelR0N N (p + (a * y : ℝ)))
      (gaussianReal 0 2) :=
    deBruijnNewmanRiemannSiegel_integrable_R0N_horizontal N a hpim
  have hrefTerm (k : ℕ) : Integrable
      (fun y : ℝ => deBruijnNewmanRiemannSiegelReflect
        (deBruijnNewmanRiemannSiegelR0Term (k + 1)) (q - (a * y : ℝ)))
      (gaussianReal 0 2) := by
    simpa [sub_eq_add_neg] using
      (deBruijnNewmanRiemannSiegel_integrable_reflect_R0Term_horizontal k (-a) (s := q) hqim)
  have hrefSum : Integrable
      (fun y : ℝ => ∑ k ∈ Finset.range N,
        deBruijnNewmanRiemannSiegelReflect
          (deBruijnNewmanRiemannSiegelR0Term (k + 1)) (q - (a * y : ℝ)))
      (gaussianReal 0 2) :=
    integrable_finsetSum (Finset.range N) (fun k _ => hrefTerm k)
  have hrefRem : Integrable
      (fun y : ℝ => deBruijnNewmanRiemannSiegelReflect
        (deBruijnNewmanRiemannSiegelR0N N) (q - (a * y : ℝ)))
      (gaussianReal 0 2) := by
    simpa [sub_eq_add_neg] using
      (deBruijnNewmanRiemannSiegel_integrable_reflect_R0N_horizontal N (-a) (s := q) hqim)
  rw [deBruijnNewmanH_eq_gaussian_riemannXi ht.le z]
  calc
    (∫ y : ℝ, (1 / 8 : ℂ) * riemannXi
        ((1 + Complex.I * z) / 2 + ((Real.sqrt t / 2 * y : ℝ) : ℂ))
        ∂gaussianReal 0 2) =
      ∫ y : ℝ,
        (((∑ k ∈ Finset.range N,
            deBruijnNewmanRiemannSiegelR0Term (k + 1) (p + (a * y : ℝ))) +
          deBruijnNewmanRiemannSiegelR0N N (p + (a * y : ℝ))) +
        ((∑ k ∈ Finset.range N,
            deBruijnNewmanRiemannSiegelReflect
              (deBruijnNewmanRiemannSiegelR0Term (k + 1)) (q - (a * y : ℝ))) +
          deBruijnNewmanRiemannSiegelReflect
            (deBruijnNewmanRiemannSiegelR0N N) (q - (a * y : ℝ))))
        ∂gaussianReal 0 2 := by
      apply integral_congr_ae
      apply ae_of_all
      intro y
      have hxy := deBruijnNewmanRiemannSiegel_xio_finite N
        (deBruijnNewmanRiemannSiegel_isNoninteger_of_im_ne_zero hpim (a * y))
      have hleft :
          (1 + Complex.I * z) / 2 + ((Real.sqrt t / 2 * y : ℝ) : ℂ) =
            p + (a * y : ℝ) := by
        dsimp [p, a]
      have hreflected : 1 - (p + (a * y : ℝ)) = q - (a * y : ℝ) := by
        dsimp [p, q]
        ring
      dsimp only
      rw [hleft]
      rw [hreflected] at hxy
      exact hxy
    _ =
      ((∑ k ∈ Finset.range N,
          ∫ y : ℝ, deBruijnNewmanRiemannSiegelR0Term (k + 1)
            (p + (a * y : ℝ)) ∂gaussianReal 0 2) +
        (∫ y : ℝ, deBruijnNewmanRiemannSiegelR0N N
          (p + (a * y : ℝ)) ∂gaussianReal 0 2)) +
      ((∑ k ∈ Finset.range N,
          ∫ y : ℝ, deBruijnNewmanRiemannSiegelReflect
            (deBruijnNewmanRiemannSiegelR0Term (k + 1))
              (q - (a * y : ℝ)) ∂gaussianReal 0 2) +
        (∫ y : ℝ, deBruijnNewmanRiemannSiegelReflect
          (deBruijnNewmanRiemannSiegelR0N N)
            (q - (a * y : ℝ)) ∂gaussianReal 0 2)) := by
      calc
        (∫ y : ℝ,
            (((∑ k ∈ Finset.range N,
                deBruijnNewmanRiemannSiegelR0Term (k + 1) (p + (a * y : ℝ))) +
              deBruijnNewmanRiemannSiegelR0N N (p + (a * y : ℝ))) +
            ((∑ k ∈ Finset.range N,
                deBruijnNewmanRiemannSiegelReflect
                  (deBruijnNewmanRiemannSiegelR0Term (k + 1)) (q - (a * y : ℝ))) +
              deBruijnNewmanRiemannSiegelReflect
                (deBruijnNewmanRiemannSiegelR0N N) (q - (a * y : ℝ))))
            ∂gaussianReal 0 2) =
          (∫ y : ℝ,
              ((∑ k ∈ Finset.range N,
                deBruijnNewmanRiemannSiegelR0Term (k + 1) (p + (a * y : ℝ))) +
                deBruijnNewmanRiemannSiegelR0N N (p + (a * y : ℝ)))
              ∂gaussianReal 0 2) +
            (∫ y : ℝ,
              ((∑ k ∈ Finset.range N,
                deBruijnNewmanRiemannSiegelReflect
                  (deBruijnNewmanRiemannSiegelR0Term (k + 1)) (q - (a * y : ℝ))) +
                deBruijnNewmanRiemannSiegelReflect
                  (deBruijnNewmanRiemannSiegelR0N N) (q - (a * y : ℝ)))
              ∂gaussianReal 0 2) := by
            simpa only [Pi.add_apply] using
              integral_add (hsum.add hrem) (hrefSum.add hrefRem)
        _ =
          ((∫ y : ℝ, ∑ k ∈ Finset.range N,
              deBruijnNewmanRiemannSiegelR0Term (k + 1) (p + (a * y : ℝ))
              ∂gaussianReal 0 2) +
            (∫ y : ℝ, deBruijnNewmanRiemannSiegelR0N N
              (p + (a * y : ℝ)) ∂gaussianReal 0 2)) +
          ((∫ y : ℝ, ∑ k ∈ Finset.range N,
              deBruijnNewmanRiemannSiegelReflect
                (deBruijnNewmanRiemannSiegelR0Term (k + 1)) (q - (a * y : ℝ))
              ∂gaussianReal 0 2) +
            (∫ y : ℝ, deBruijnNewmanRiemannSiegelReflect
              (deBruijnNewmanRiemannSiegelR0N N) (q - (a * y : ℝ))
              ∂gaussianReal 0 2)) := by
            rw [integral_add hsum hrem, integral_add hrefSum hrefRem]
        _ = _ := by
          rw [integral_finsetSum (Finset.range N) (fun k _ => hterm k),
            integral_finsetSum (Finset.range N) (fun k _ => hrefTerm k)]
    _ =
      (∑ k ∈ Finset.range N, deBruijnNewmanRiemannSiegelHeatTerm t (k + 1) p) +
      (∑ k ∈ Finset.range N,
        deBruijnNewmanRiemannSiegelReflect (deBruijnNewmanRiemannSiegelHeatTerm t (k + 1)) q) +
      deBruijnNewmanRiemannSiegelHeatRemainder t N p +
      deBruijnNewmanRiemannSiegelReflect (deBruijnNewmanRiemannSiegelHeatRemainder t N) q := by
      have hrefTermIntegral (k : ℕ) :
          (∫ y : ℝ, deBruijnNewmanRiemannSiegelReflect
            (deBruijnNewmanRiemannSiegelR0Term (k + 1))
              (q - (a * y : ℝ)) ∂gaussianReal 0 2) =
            deBruijnNewmanRiemannSiegelReflect (deBruijnNewmanRiemannSiegelHeatTerm t (k + 1)) q := by
        simpa [deBruijnNewmanRiemannSiegelHeatTerm, a, deBruijnNewmanRiemannSiegelHeatShift] using
          deBruijnNewmanRiemannSiegel_integral_reflect_neg_shift t
            (deBruijnNewmanRiemannSiegelR0Term (k + 1)) q
      have hrefRemIntegral :
          (∫ y : ℝ, deBruijnNewmanRiemannSiegelReflect
            (deBruijnNewmanRiemannSiegelR0N N)
              (q - (a * y : ℝ)) ∂gaussianReal 0 2) =
            deBruijnNewmanRiemannSiegelReflect (deBruijnNewmanRiemannSiegelHeatRemainder t N) q := by
        simpa [deBruijnNewmanRiemannSiegelHeatRemainder, a, deBruijnNewmanRiemannSiegelHeatShift] using
          deBruijnNewmanRiemannSiegel_integral_reflect_neg_shift t
            (deBruijnNewmanRiemannSiegelR0N N) q
      rw [Finset.sum_congr rfl (fun k _ => hrefTermIntegral k), hrefRemIntegral]
      unfold deBruijnNewmanRiemannSiegelHeatTerm deBruijnNewmanRiemannSiegelHeatRemainder deBruijnNewmanRiemannSiegelHeatEvolve
      dsimp [a, deBruijnNewmanRiemannSiegelHeatShift]
      ring
    _ =
      (∑ k ∈ Finset.range N,
        deBruijnNewmanRiemannSiegelHeatTerm t (k + 1) ((1 + Complex.I * z) / 2)) +
      (∑ k ∈ Finset.range N,
        deBruijnNewmanRiemannSiegelReflect (deBruijnNewmanRiemannSiegelHeatTerm t (k + 1))
          ((1 - Complex.I * z) / 2)) +
      deBruijnNewmanRiemannSiegelHeatRemainder t N ((1 + Complex.I * z) / 2) +
      deBruijnNewmanRiemannSiegelReflect (deBruijnNewmanRiemannSiegelHeatRemainder t N)
        ((1 - Complex.I * z) / 2) := by
      rfl
end

end LeanLab.Riemann
