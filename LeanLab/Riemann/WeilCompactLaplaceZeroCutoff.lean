import LeanLab.Riemann.WeilCompactLaplaceSeparator
import LeanLab.Riemann.WeilSymmetricGaussianFamily
import LeanLab.Riemann.LiSymmetricZeroFormula
import Mathlib.Analysis.Calculus.ParametricIntegral

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The compact-smooth zero side of Weil's explicit formula

This module proves the selected-height xi zero-cutoff passage for the reflection symmetrization of
the bilateral Laplace transform of every compactly supported function with six continuous
derivatives on the logarithmic line. Six integrations by parts provide enough decay to absorb the
project's coarse fourth-power bound for the xi logarithmic derivative on the selected horizontal
edges.
-/

open Complex Filter Function MeasureTheory Set Topology
open scoped BigOperators ContDiff Interval Topology

namespace LeanLab.Riemann

noncomputable section

/-- Reflection symmetrization of a compactly supported bilateral Laplace transform. -/
def symmetrizedCompactLaplaceWeight (f : ℝ → ℂ) (s : ℂ) : ℂ :=
  (compactLaplaceTransform f s + compactLaplaceTransform f (1 - s)) / 2

/-- A continuous compactly supported function has an entire bilateral Laplace transform. -/
theorem differentiable_compactLaplaceTransform {f : ℝ → ℂ}
    (hf : Continuous f) (hfsupp : HasCompactSupport f) :
    Differentiable ℂ (compactLaplaceTransform f) := by
  intro s0
  let F : ℂ → ℝ → ℂ := fun s x => Complex.exp (s * (x : ℂ)) * f x
  let F' : ℂ → ℝ → ℂ := fun s x =>
    (x : ℂ) * Complex.exp (s * (x : ℂ)) * f x
  let bound : ℝ → ℝ := fun x =>
    |x| * Real.exp ((‖s0‖ + 1) * |x|) * ‖f x‖
  have hFmeas : ∀ᶠ s in 𝓝 s0, AEStronglyMeasurable (F s) := by
    filter_upwards [] with s
    exact (by fun_prop : Continuous (F s)).aestronglyMeasurable
  have hFint : Integrable (F s0) := by
    simpa only [F] using integrable_compactLaplaceKernel hf hfsupp s0
  have hF'meas : AEStronglyMeasurable (F' s0) :=
    (by fun_prop : Continuous (F' s0)).aestronglyMeasurable
  have hboundInt : Integrable bound := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (by fun_prop : Continuous bound)
    · exact hfsupp.norm.mul_left
  have hbound : ∀ᵐ x : ℝ, ∀ s ∈ Metric.ball s0 1, ‖F' s x‖ ≤ bound x := by
    filter_upwards [] with x
    intro s hs
    have hsNorm : ‖s‖ ≤ ‖s0‖ + 1 := by
      have hdist : ‖s - s0‖ < 1 := by simpa [dist_eq] using hs
      calc
        ‖s‖ = ‖(s - s0) + s0‖ := by ring_nf
        _ ≤ ‖s - s0‖ + ‖s0‖ := norm_add_le _ _
        _ ≤ ‖s0‖ + 1 := by linarith
    have hreNorm : |s.re| ≤ ‖s‖ := abs_re_le_norm s
    have hmul : (s * (x : ℂ)).re ≤ (‖s0‖ + 1) * |x| := by
      simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
      calc
        s.re * x ≤ |s.re * x| := le_abs_self _
        _ = |s.re| * |x| := abs_mul _ _
        _ ≤ (‖s0‖ + 1) * |x| := by gcongr; linarith
    dsimp only [F', bound]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    gcongr
  have hdiff : ∀ᵐ x : ℝ, ∀ s ∈ Metric.ball s0 1,
      HasDerivAt (fun z : ℂ => F z x) (F' s x) s := by
    filter_upwards [] with x
    intro s _hs
    dsimp only [F, F']
    simpa only [id_eq, one_mul, mul_one, mul_assoc, mul_left_comm, mul_comm] using
      (((hasDerivAt_id s).mul_const (x : ℂ)).cexp.mul_const (f x))
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds s0 (by norm_num : (0 : ℝ) < 1))
    hFmeas hFint hF'meas hbound hboundInt hdiff
  exact hmain.2.differentiableAt

theorem differentiable_symmetrizedCompactLaplaceWeight {f : ℝ → ℂ}
    (hf : Continuous f) (hfsupp : HasCompactSupport f) :
    Differentiable ℂ (symmetrizedCompactLaplaceWeight f) := by
  have hL := differentiable_compactLaplaceTransform hf hfsupp
  intro s
  unfold symmetrizedCompactLaplaceWeight
  exact ((hL s).add ((hL (1 - s)).comp s (by fun_prop))).div_const 2

@[simp] theorem symmetrizedCompactLaplaceWeight_one_sub (f : ℝ → ℂ) (s : ℂ) :
    symmetrizedCompactLaplaceWeight f (1 - s) =
      symmetrizedCompactLaplaceWeight f s := by
  unfold symmetrizedCompactLaplaceWeight
  have harg : (1 : ℂ) - (1 - s) = s := by ring
  rw [harg]
  congr 1
  ring

/-- Reflection of the xi divisor transports compact-Laplace summability without dropping
analytic multiplicity. -/
theorem summable_compactLaplaceTransform_one_sub_xiDivisorZero
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfsupp : HasCompactSupport f) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      compactLaplaceTransform f (1 - riemannXiDivisorZeroValue p)) := by
  have hsum := (summable_norm_compactLaplaceTransform_xiDivisorZero hf hfsupp).of_norm
  have hreflect : Summable (fun p : RiemannXiDivisorZeroIndex =>
      compactLaplaceTransform f
        (riemannXiDivisorZeroValue (riemannXiDivisorZeroReflectEquiv p))) :=
    hsum.comp_injective riemannXiDivisorZeroReflectEquiv.injective
  simpa only [Function.comp_apply, riemannXiDivisorZeroReflectEquiv_apply,
    riemannXiDivisorZeroValue_reflect] using hreflect

theorem summable_symmetrizedCompactLaplaceWeight_xiDivisorZero
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfsupp : HasCompactSupport f) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      symmetrizedCompactLaplaceWeight f (riemannXiDivisorZeroValue p)) := by
  apply Summable.div_const
  exact (summable_norm_compactLaplaceTransform_xiDivisorZero hf hfsupp).of_norm.add
    (summable_compactLaplaceTransform_one_sub_xiDivisorZero hf hfsupp)

theorem hasCompactSupport_iterate_deriv {f : ℝ → ℂ}
    (hfsupp : HasCompactSupport f) :
    ∀ n : ℕ, HasCompactSupport (deriv^[n] f)
  | 0 => by simpa
  | n + 1 => by
      rw [Function.iterate_succ_apply']
      exact (hasCompactSupport_iterate_deriv hfsupp n).deriv

/-- Repeated integration by parts for a smooth compactly supported bilateral Laplace transform. -/
theorem compactLaplaceTransform_iterate_deriv {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (hfsupp : HasCompactSupport f) (s : ℂ) :
    ∀ n : ℕ,
      compactLaplaceTransform (deriv^[n] f) s =
        (-s) ^ n * compactLaplaceTransform f s
  | 0 => by simp
  | n + 1 => by
      rw [Function.iterate_succ_apply',
        compactLaplaceTransform_deriv
          ((hf.iterate_deriv n).of_le (by simp))
          (hasCompactSupport_iterate_deriv hfsupp n) s,
        compactLaplaceTransform_iterate_deriv hf hfsupp s n]
      rw [pow_succ']
      ring

/-- Repeated integration by parts through the sixth derivative needs only six continuous
derivatives, rather than a Schwartz-smooth physical function. -/
theorem compactLaplaceTransform_iterate_deriv_of_le_six {f : ℝ → ℂ}
    (hf : ContDiff ℝ 6 f) (hfsupp : HasCompactSupport f) (s : ℂ) :
    ∀ n : ℕ, n ≤ 6 →
      compactLaplaceTransform (deriv^[n] f) s =
        (-s) ^ n * compactLaplaceTransform f s
  | 0, _ => by simp
  | n + 1, hn => by
      have hn6 : n ≤ 6 := Nat.le_trans (Nat.le_succ n) hn
      have hnreg : ContDiff ℝ 1 (deriv^[n] f) := by
        apply ContDiff.iterate_deriv' 1 n
        apply hf.of_le
        exact_mod_cast (show 1 + n ≤ 6 by simpa [Nat.add_comm] using hn)
      rw [Function.iterate_succ_apply',
        compactLaplaceTransform_deriv hnreg
          (hasCompactSupport_iterate_deriv hfsupp n) s,
        compactLaplaceTransform_iterate_deriv_of_le_six hf hfsupp s n hn6]
      rw [pow_succ']
      ring

/-- A fixed-strip mass for the sixth derivative of a compactly supported function. -/
def compactLaplaceSixthDerivativeMass (c : ℝ) (f : ℝ → ℂ) : ℝ :=
  ∫ x : ℝ, Real.exp (c * |x|) * ‖deriv^[6] f x‖

theorem integrable_compactLaplaceSixthDerivativeMajorant
    {f : ℝ → ℂ} (hf : ContDiff ℝ 6 f) (hfsupp : HasCompactSupport f) (c : ℝ) :
    Integrable (fun x : ℝ => Real.exp (c * |x|) * ‖deriv^[6] f x‖) := by
  have hderiv : ContDiff ℝ 0 (deriv^[6] f) := by
    simpa using ContDiff.iterate_deriv' 0 6 hf
  apply Continuous.integrable_of_hasCompactSupport
  · exact (Real.continuous_exp.comp
      (continuous_const.mul continuous_abs)).mul hderiv.continuous.norm
  · exact (hasCompactSupport_iterate_deriv hfsupp 6).norm.mul_left

theorem compactLaplaceSixthDerivativeMass_nonneg (c : ℝ) (f : ℝ → ℂ) :
    0 ≤ compactLaplaceSixthDerivativeMass c f := by
  apply integral_nonneg
  intro x
  positivity

theorem norm_compactLaplaceKernel_le_exp_mul_abs
    {g : ℝ → ℂ} {s : ℂ} {c : ℝ} (hre : |s.re| ≤ c) (x : ℝ) :
    ‖Complex.exp (s * (x : ℂ)) * g x‖ ≤
      Real.exp (c * |x|) * ‖g x‖ := by
  rw [norm_mul, Complex.norm_exp]
  gcongr
  simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  calc
    s.re * x ≤ |s.re * x| := le_abs_self _
    _ = |s.re| * |x| := abs_mul _ _
    _ ≤ c * |x| := by gcongr

theorem norm_compactLaplaceTransform_sixthDeriv_le_mass
    {f : ℝ → ℂ} (hf : ContDiff ℝ 6 f) (hfsupp : HasCompactSupport f)
    {c : ℝ} {s : ℂ} (hre : |s.re| ≤ c) :
    ‖compactLaplaceTransform (deriv^[6] f) s‖ ≤
      compactLaplaceSixthDerivativeMass c f := by
  apply norm_integral_le_of_norm_le
    (integrable_compactLaplaceSixthDerivativeMajorant hf hfsupp c)
  filter_upwards with x
  exact norm_compactLaplaceKernel_le_exp_mul_abs hre x

/-- Six integrations by parts give inverse-sixth-power decay on every fixed real strip. -/
theorem norm_compactLaplaceTransform_le_mass_mul_inv_pow_six
    {f : ℝ → ℂ} (hf : ContDiff ℝ 6 f) (hfsupp : HasCompactSupport f)
    {c : ℝ} {s : ℂ} (hs0 : s ≠ 0) (hre : |s.re| ≤ c) :
    ‖compactLaplaceTransform f s‖ ≤
      compactLaplaceSixthDerivativeMass c f * (‖s‖⁻¹ ^ (6 : ℕ)) := by
  have hbound := norm_compactLaplaceTransform_sixthDeriv_le_mass hf hfsupp hre
  have hnorm : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have hident := compactLaplaceTransform_iterate_deriv_of_le_six hf hfsupp s 6 le_rfl
  calc
    ‖compactLaplaceTransform f s‖ =
        ‖compactLaplaceTransform (deriv^[6] f) s‖ * (‖s‖⁻¹ ^ (6 : ℕ)) := by
      rw [hident, norm_mul, norm_pow, norm_neg]
      field_simp [hnorm.ne']
    _ ≤ compactLaplaceSixthDerivativeMass c f * (‖s‖⁻¹ ^ (6 : ℕ)) := by
      gcongr

/-- On a selected top edge, reflection-symmetrized compact Laplace weights have uniform
inverse-sixth-power decay in the height scale. -/
theorem norm_symmetrizedCompactLaplaceWeight_selectedTopEdge_le
    {f : ℝ → ℂ} (hf : ContDiff ℝ 6 f) (hfsupp : HasCompactSupport f)
    {c : ℝ} (hc : 1 < c) (n : ℕ) {x : ℝ} (hx : x ∈ [[1 - c, c]]) :
    ‖symmetrizedCompactLaplaceWeight f
        ((x : ℂ) + gaussianXiSelectedHeight c n * I)‖ ≤
      compactLaplaceSixthDerivativeMass c f *
        (gaussianXiHeightScale c n)⁻¹ ^ (6 : ℕ) := by
  let R : ℝ := gaussianXiHeightScale c n
  let T : ℝ := gaussianXiSelectedHeight c n
  let z : ℂ := (x : ℂ) + T * I
  have hRpos : 0 < R := gaussianXiHeightScale_pos hc n
  have hTpos : 0 < T := lt_trans hRpos (gaussianXiSelectedHeight_spec c n).1.1
  have hlr : 1 - c ≤ c := by linarith
  rw [uIcc_of_le hlr] at hx
  have hzre : |z.re| ≤ c := by
    simp only [z, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
      zero_mul, sub_zero, add_zero]
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2]
  have hreflectre : |((1 : ℂ) - z).re| ≤ c := by
    simp only [z, sub_re, one_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero]
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2]
  have hzNorm : R ≤ ‖z‖ := by
    have him : z.im = T := by simp [z]
    calc
      R ≤ T := (gaussianXiSelectedHeight_spec c n).1.1.le
      _ = |z.im| := by rw [him, abs_of_pos hTpos]
      _ ≤ ‖z‖ := Complex.abs_im_le_norm z
  have hreflectNorm : R ≤ ‖(1 : ℂ) - z‖ := by
    have him : ((1 : ℂ) - z).im = -T := by simp [z]
    calc
      R ≤ T := (gaussianXiSelectedHeight_spec c n).1.1.le
      _ = |((1 : ℂ) - z).im| := by rw [him, abs_neg, abs_of_pos hTpos]
      _ ≤ ‖(1 : ℂ) - z‖ := Complex.abs_im_le_norm _
  have hz0 : z ≠ 0 := by
    exact norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le hRpos hzNorm))
  have hreflect0 : (1 : ℂ) - z ≠ 0 := by
    exact norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le hRpos hreflectNorm))
  have hzInv : ‖z‖⁻¹ ≤ R⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hRpos hzNorm
  have hreflectInv : ‖(1 : ℂ) - z‖⁻¹ ≤ R⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hRpos hreflectNorm
  have hmass : 0 ≤ compactLaplaceSixthDerivativeMass c f :=
    compactLaplaceSixthDerivativeMass_nonneg c f
  have hL : ‖compactLaplaceTransform f z‖ ≤
      compactLaplaceSixthDerivativeMass c f * R⁻¹ ^ (6 : ℕ) := by
    calc
      ‖compactLaplaceTransform f z‖ ≤
          compactLaplaceSixthDerivativeMass c f * (‖z‖⁻¹ ^ (6 : ℕ)) :=
        norm_compactLaplaceTransform_le_mass_mul_inv_pow_six hf hfsupp hz0 hzre
      _ ≤ compactLaplaceSixthDerivativeMass c f * R⁻¹ ^ (6 : ℕ) := by gcongr
  have hLreflect : ‖compactLaplaceTransform f (1 - z)‖ ≤
      compactLaplaceSixthDerivativeMass c f * R⁻¹ ^ (6 : ℕ) := by
    calc
      ‖compactLaplaceTransform f (1 - z)‖ ≤
          compactLaplaceSixthDerivativeMass c f *
            (‖(1 : ℂ) - z‖⁻¹ ^ (6 : ℕ)) :=
        norm_compactLaplaceTransform_le_mass_mul_inv_pow_six hf hfsupp
          hreflect0 hreflectre
      _ ≤ compactLaplaceSixthDerivativeMass c f * R⁻¹ ^ (6 : ℕ) := by gcongr
  change ‖symmetrizedCompactLaplaceWeight f z‖ ≤ _
  unfold symmetrizedCompactLaplaceWeight
  calc
    ‖(compactLaplaceTransform f z + compactLaplaceTransform f (1 - z)) / 2‖ ≤
        (‖compactLaplaceTransform f z‖ + ‖compactLaplaceTransform f (1 - z)‖) / 2 := by
      rw [norm_div]
      norm_num
      gcongr
      exact norm_add_le _ _
    _ ≤ (compactLaplaceSixthDerivativeMass c f * R⁻¹ ^ (6 : ℕ) +
          compactLaplaceSixthDerivativeMass c f * R⁻¹ ^ (6 : ℕ)) / 2 := by
      gcongr
    _ = compactLaplaceSixthDerivativeMass c f *
        (gaussianXiHeightScale c n)⁻¹ ^ (6 : ℕ) := by
      dsimp only [R]
      ring

/-- The selected compact-weight top integral is bounded by an inverse square of the height scale. -/
theorem exists_norm_symmetrizedCompactLaplaceTopHorizontalIntegral_le
    {f : ℝ → ℂ} (hf : ContDiff ℝ 6 f) (hfsupp : HasCompactSupport f)
    {c : ℝ} (hc : 1 < c) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ,
      ‖selectedXiTopHorizontalIntegralFor
          (symmetrizedCompactLaplaceWeight f) c n‖ ≤
        B * (gaussianXiHeightScale c n)⁻¹ ^ (2 : ℕ) := by
  obtain ⟨K, hK, hlog⟩ :=
    exists_norm_logDeriv_selectedGaussianTopEdge_le_scale_pow_four hc
  let M : ℝ := compactLaplaceSixthDerivativeMass c f
  let B : ℝ := (2 * c - 1) * M * K
  have hM : 0 ≤ M := compactLaplaceSixthDerivativeMass_nonneg c f
  refine ⟨B, by
    dsimp only [B]
    have hlength : 0 < 2 * c - 1 := by linarith
    positivity, ?_⟩
  intro n
  let R : ℝ := gaussianXiHeightScale c n
  have hRpos : 0 < R := gaussianXiHeightScale_pos hc n
  have hpoint : ∀ x ∈ Ι (1 - c) c,
      ‖symmetrizedCompactLaplaceWeight f
          ((x : ℂ) + gaussianXiSelectedHeight c n * I) *
        logDeriv riemannXi
          ((x : ℂ) + gaussianXiSelectedHeight c n * I)‖ ≤
        (M * R⁻¹ ^ (6 : ℕ)) * (K * R ^ (4 : ℕ)) := by
    intro x hx
    rw [norm_mul]
    apply mul_le_mul
    · simpa only [M, R] using
        norm_symmetrizedCompactLaplaceWeight_selectedTopEdge_le
          hf hfsupp hc n (Set.uIoc_subset_uIcc hx)
    · simpa only [R] using hlog n x (Set.uIoc_subset_uIcc hx)
    · positivity
    · positivity
  have hintegral := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  rw [selectedXiTopHorizontalIntegralFor]
  calc
    ‖∫ x : ℝ in 1 - c..c,
        symmetrizedCompactLaplaceWeight f
            ((x : ℂ) + gaussianXiSelectedHeight c n * I) *
          logDeriv riemannXi
            ((x : ℂ) + gaussianXiSelectedHeight c n * I)‖ ≤
        ((M * R⁻¹ ^ (6 : ℕ)) * (K * R ^ (4 : ℕ))) *
          |c - (1 - c)| := hintegral
    _ = B * (gaussianXiHeightScale c n)⁻¹ ^ (2 : ℕ) := by
      rw [abs_of_pos (by linarith : 0 < c - (1 - c))]
      dsimp only [B, R]
      field_simp [hRpos.ne']
      ring

theorem tendsto_symmetrizedCompactLaplaceTopHorizontalIntegral
    {f : ℝ → ℂ} (hf : ContDiff ℝ 6 f) (hfsupp : HasCompactSupport f)
    {c : ℝ} (hc : 1 < c) :
    Tendsto
      (selectedXiTopHorizontalIntegralFor
        (symmetrizedCompactLaplaceWeight f) c)
      atTop (𝓝 0) := by
  obtain ⟨B, _hB, hbound⟩ :=
    exists_norm_symmetrizedCompactLaplaceTopHorizontalIntegral_le hf hfsupp hc
  have hinv : Tendsto (fun n : ℕ => (gaussianXiHeightScale c n)⁻¹)
      atTop (𝓝 0) := tendsto_inv_atTop_zero.comp (tendsto_gaussianXiHeightScale c)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n => norm_nonneg _
  · exact Filter.Eventually.of_forall fun n => hbound n
  · simpa using (hinv.pow 2).const_mul B

/-- Every compactly supported `C^6` logarithmic test function, after explicit reflection
symmetrization, satisfies the complete multiplicity-bearing selected xi zero-cutoff limit. -/
theorem tendsto_symmetrizedCompactLaplaceXiRightVerticalIntegral_sixContDiff
    {f : ℝ → ℂ} (hf : ContDiff ℝ 6 f) (hfsupp : HasCompactSupport f)
    {c : ℝ} (hc : 1 < c) :
    Tendsto
      (selectedXiRightVerticalIntegralFor
        (symmetrizedCompactLaplaceWeight f) c)
      atTop
      (𝓝 ((Real.pi : ℂ) *
        ∑' p : RiemannXiDivisorZeroIndex,
          symmetrizedCompactLaplaceWeight f
            (riemannXiDivisorZeroValue p))) := by
  apply tendsto_selectedXiRightVerticalIntegralFor
    (differentiable_symmetrizedCompactLaplaceWeight hf.continuous hfsupp)
    (symmetrizedCompactLaplaceWeight_one_sub f)
    (summable_symmetrizedCompactLaplaceWeight_xiDivisorZero
      (hf.of_le (by norm_num)) hfsupp)
    hc
  exact tendsto_symmetrizedCompactLaplaceTopHorizontalIntegral hf hfsupp hc

/-- Compatibility form of the compact zero-cutoff theorem for smooth test functions. -/
theorem tendsto_symmetrizedCompactLaplaceXiRightVerticalIntegral
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hfsupp : HasCompactSupport f)
    {c : ℝ} (hc : 1 < c) :
    Tendsto
      (selectedXiRightVerticalIntegralFor
        (symmetrizedCompactLaplaceWeight f) c)
      atTop
      (𝓝 ((Real.pi : ℂ) *
        ∑' p : RiemannXiDivisorZeroIndex,
          symmetrizedCompactLaplaceWeight f
            (riemannXiDivisorZeroValue p))) := by
  exact tendsto_symmetrizedCompactLaplaceXiRightVerticalIntegral_sixContDiff
    (hf.of_le (WithTop.coe_le_coe.mpr (OrderTop.le_top (6 : ℕ∞)))) hfsupp hc

end

end LeanLab.Riemann
