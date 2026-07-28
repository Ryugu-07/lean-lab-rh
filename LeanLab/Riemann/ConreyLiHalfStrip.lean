import LeanLab.Riemann.ConreyLiRKHSShift
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Isomorphisms

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The Conrey--Li Hardy-RKHS half-strip continuation

This file formalizes the second stage of Conrey--Li's Theorem 2. It isolates the exact analytic
RKHS interface needed to continue the upper-half-plane Cayley transform to `Im z > -1/2`.
-/

namespace LeanLab.Riemann

open Complex ComplexConjugate Function Set
open scoped InnerProductSpace Topology UpperHalfPlane

noncomputable section

/-- The open half-strip used in the second stage of Conrey--Li's Theorem 2. -/
def conreyLiHalfStrip : Set ℂ :=
  {z : ℂ | -(1 / 2 : ℝ) < z.im}

theorem convex_conreyLiHalfStrip : Convex ℝ conreyLiHalfStrip := by
  simpa only [conreyLiHalfStrip] using
    (convex_halfSpace_im_gt (-(1 / 2 : ℝ)))

theorem isPreconnected_conreyLiHalfStrip :
    IsPreconnected conreyLiHalfStrip :=
  convex_conreyLiHalfStrip.isPreconnected

theorem zero_mem_conreyLiHalfStrip : (0 : ℂ) ∈ conreyLiHalfStrip := by
  simp [conreyLiHalfStrip]

theorem upper_mem_conreyLiHalfStrip (w : ℍ) :
    (w : ℂ) ∈ conreyLiHalfStrip := by
  dsimp only [conreyLiHalfStrip]
  exact lt_trans (by norm_num : -(1 / 2 : ℝ) < 0) w.im_pos

/-- The source Hardy kernel on `Im z > -1/2`. -/
def conreyLiHardyKernel (w z : ℂ) : ℂ :=
  1 / (2 * (Real.pi : ℂ) * I * (conj w - z - I))

theorem conreyLiHardyKernel_zero (z : ℂ) :
    conreyLiHardyKernel 0 z =
      1 / (2 * (Real.pi : ℂ) * I * (-z - I)) := by
  simp [conreyLiHardyKernel]

theorem conreyLiHardyAnchorFactor_ne_zero
    {z : ℂ} (hz : z ∈ conreyLiHalfStrip) :
    2 * (Real.pi : ℂ) * I * (-z - I) ≠ 0 := by
  have hzneg : -z - I ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp only [sub_im, neg_im, I_im, zero_im] at him
    have hzIm : z.im = -1 := by linarith
    change -(1 / 2 : ℝ) < z.im at hz
    rw [hzIm] at hz
    norm_num at hz
  exact mul_ne_zero (mul_ne_zero (by norm_num [Real.pi_ne_zero]) I_ne_zero) hzneg

theorem conreyLiHardyDiagonalDenominator_eq (z : ℂ) :
    2 * (Real.pi : ℂ) * I * (conj z - z - I) =
      ((2 * Real.pi * (2 * z.im + 1) : ℝ) : ℂ) := by
  apply Complex.ext
  · simp [mul_re]
    ring
  · simp [mul_im]

theorem conreyLiHardyDiagonalDenominator_ne_zero
    {z : ℂ} (hz : z ∈ conreyLiHalfStrip) :
    2 * (Real.pi : ℂ) * I * (conj z - z - I) ≠ 0 := by
  rw [conreyLiHardyDiagonalDenominator_eq]
  apply Complex.ofReal_ne_zero.mpr
  have hzpos : 0 < 2 * z.im + 1 := by
    change -(1 / 2 : ℝ) < z.im at hz
    linarith
  positivity

theorem conreyLiHardyKernel_self_ne_zero
    {z : ℂ} (hz : z ∈ conreyLiHalfStrip) :
    conreyLiHardyKernel z z ≠ 0 := by
  exact one_div_ne_zero
    (conreyLiHardyDiagonalDenominator_ne_zero hz)

theorem conreyLiUpperHardyDenominator_ne_zero (w z : ℍ) :
    2 * (Real.pi : ℂ) * I *
        (conj (w : ℂ) - (z : ℂ) - I) ≠ 0 := by
  apply mul_ne_zero (mul_ne_zero
    (by norm_num [Real.pi_ne_zero]) I_ne_zero)
  intro h
  have him := congrArg Complex.im h
  simp only [sub_im, conj_im, I_im, zero_im] at him
  have hw : 0 < (w : ℂ).im := w.im_pos
  have hz : 0 < (z : ℂ).im := z.im_pos
  linarith

theorem conreyLi_W_add_shift_ne_zero
    (W : ℂ → ℂ) (w : ℍ)
    (hWshift : W (conreyLiUpperShift w) ≠ 0)
    (hratio : 0 ≤ (conreyLiUpperShiftRatio W w).re) :
    W w + W (conreyLiUpperShift w) ≠ 0 := by
  have hratioDen :
      conreyLiUpperShiftRatio W w + 1 ≠ 0 :=
    conreyLi_cayley_denominator_ne_zero hratio
  have heq :
      W w + W (conreyLiUpperShift w) =
        W (conreyLiUpperShift w) *
          (conreyLiUpperShiftRatio W w + 1) := by
    rw [conreyLiUpperShiftRatio]
    field_simp
  rw [heq]
  exact mul_ne_zero hWshift hratioDen

theorem conreyLi_shiftedKernel_add_eq_halfStripDefect
    (W : ℂ → ℂ) (w z : ℍ)
    (hWw :
      W w + W (conreyLiUpperShift w) ≠ 0)
    (hWz :
      W z + W (conreyLiUpperShift z) ≠ 0) :
    conreyLiKernel W w (conreyLiUpperShift z) +
        conreyLiKernel W (conreyLiUpperShift w) z =
      ((W z + W (conreyLiUpperShift z)) *
          conj (W w + W (conreyLiUpperShift w)) / 2) *
        ((1 - conreyLiCayley W z * conj (conreyLiCayley W w)) *
          conreyLiHardyKernel w z) := by
  have hWwConj :
      conj (W w + W (conreyLiUpperShift w)) ≠ 0 := by
    intro h
    apply hWw
    have hc := congrArg conj h
    simpa using hc
  have hWwConjExpanded :
      conj (W w) + conj (W (conreyLiUpperShift w)) ≠ 0 := by
    simpa only [map_add] using hWwConj
  have hcayley :
      ((W z + W (conreyLiUpperShift z)) *
          conj (W w + W (conreyLiUpperShift w)) / 2) *
        (1 - conreyLiCayley W z * conj (conreyLiCayley W w)) =
      W z * conj (W (conreyLiUpperShift w)) +
        W (conreyLiUpperShift z) * conj (W w) := by
    simp only [conreyLiCayley, map_div₀, map_sub, map_add]
    field_simp [hWz, hWwConjExpanded]
    ring
  rw [← mul_assoc, hcayley]
  simp only [conreyLiKernel, conreyLiHardyKernel,
    coe_conreyLiUpperShift, map_add, Complex.conj_I]
  ring

/-- The set of scalar RKHS kernel vectors whose centers lie in the upper half-plane. -/
def conreyLiUpperKernelSet
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [RKHS ℂ H ℂ ℂ] : Set H :=
  {f : H | ∃ w : ℍ, f = RKHS.kerFun H (w : ℂ) 1}

/-- Analytic uniqueness makes the kernel vectors centered in the upper half-plane dense in an
RKHS whose analytic domain is the larger Conrey--Li half-strip. -/
theorem conreyLiUpperKernel_span_dense
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [RKHS ℂ H ℂ ℂ]
    (hanalytic :
      ∀ f : H, AnalyticOnNhd ℂ (fun z : ℂ => f z) conreyLiHalfStrip)
    (hunique :
      ∀ f : H, (∀ z ∈ conreyLiHalfStrip, f z = 0) → f = 0) :
    (Submodule.span ℂ (conreyLiUpperKernelSet H)).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff]
  apply (Submodule.eq_bot_iff _).mpr
  intro f hf
  apply hunique f
  have hzeroUpper : ∀ w : ℍ, f (w : ℂ) = 0 := by
    intro w
    have hmem :
        RKHS.kerFun H (w : ℂ) 1 ∈
          Submodule.span ℂ (conreyLiUpperKernelSet H) :=
      Submodule.mem_span_of_mem ⟨w, rfl⟩
    have hi :=
      Submodule.inner_right_of_mem_orthogonal hmem hf
    simpa using hi
  have hevent :
      (fun z : ℂ => f z) =ᶠ[𝓝 I] (fun _ : ℂ => 0) := by
    have hopen : IsOpen {z : ℂ | 0 < z.im} :=
      isOpen_lt continuous_const Complex.continuous_im
    have hI : I ∈ {z : ℂ | 0 < z.im} := by simp
    filter_upwards [hopen.mem_nhds hI] with z hz
    exact hzeroUpper ⟨z, hz⟩
  have hzero :
      Set.EqOn (fun z : ℂ => f z) (fun _ : ℂ => 0)
        conreyLiHalfStrip :=
    (hanalytic f).eqOn_of_preconnected_of_eventuallyEq
      analyticOnNhd_const isPreconnected_conreyLiHalfStrip
      (upper_mem_conreyLiHalfStrip ⟨I, by simp⟩) hevent
  exact fun z hz => hzero hz

/-- A norm-decreasing rule on finite linear combinations of a dense vector family extends to a
global contraction. This is the functional-analytic extension step used for the Conrey--Li
kernel multiplier. -/
theorem exists_contraction_of_finsupp_rule
    (H : Type*) [NormedAddCommGroup H] [NormedSpace ℂ H]
    [CompleteSpace H] {ι : Type*} (v u : ι → H)
    (hdense :
      (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤)
    (hnorm : ∀ c : ι →₀ ℂ,
      ‖Finsupp.linearCombination ℂ u c‖ ≤
        ‖Finsupp.linearCombination ℂ v c‖) :
    ∃ P : H →L[ℂ] H, ‖P‖ ≤ 1 ∧ ∀ i, P (v i) = u i := by
  let E : (ι →₀ ℂ) →ₗ[ℂ] H :=
    Finsupp.linearCombination ℂ v
  let M : (ι →₀ ℂ) →ₗ[ℂ] H :=
    Finsupp.linearCombination ℂ u
  have hker : LinearMap.ker E ≤ LinearMap.ker M := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    have hcNorm := hnorm c
    change ‖M c‖ ≤ ‖E c‖ at hcNorm
    rw [hc, norm_zero] at hcNorm
    exact norm_eq_zero.mp (le_antisymm hcNorm (norm_nonneg _))
  let qM : ((ι →₀ ℂ) ⧸ LinearMap.ker E) →ₗ[ℂ] H :=
    (LinearMap.ker E).liftQ M hker
  let P0 : LinearMap.range E →ₗ[ℂ] H :=
    qM.comp E.quotKerEquivRange.symm.toLinearMap
  have hP0_apply (c : ι →₀ ℂ) :
      P0 ⟨E c, ⟨c, rfl⟩⟩ = M c := by
    simp [P0, qM, LinearMap.quotKerEquivRange_symm_apply_image]
  have hP0norm : ∀ x : LinearMap.range E, ‖P0 x‖ ≤ ‖x‖ := by
    rintro ⟨x, ⟨c, rfl⟩⟩
    rw [hP0_apply]
    exact hnorm c
  let P0c : LinearMap.range E →L[ℂ] H :=
    LinearMap.mkContinuous P0 1 (fun x => by
      simpa only [one_mul] using hP0norm x)
  have hRangeClosure :
      (LinearMap.range E).topologicalClosure = ⊤ := by
    change (LinearMap.range (Finsupp.linearCombination ℂ v)).topologicalClosure = ⊤
    rw [Finsupp.range_linearCombination]
    exact hdense
  have hRangeDense : Dense (LinearMap.range E : Set H) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr hRangeClosure
  have hDenseSubtype :
      DenseRange (LinearMap.range E).subtypeL := by
    change DenseRange ((↑) : LinearMap.range E → H)
    exact hRangeDense.denseRange_val
  have hUniformSubtype :
      IsUniformInducing (LinearMap.range E).subtypeL :=
    (LinearMap.range E).subtypeₗᵢ.isometry.isUniformInducing
  let P : H →L[ℂ] H :=
    P0c.extend (LinearMap.range E).subtypeL
  have hP0cNorm : ‖P0c‖ ≤ 1 := by
    apply P0c.opNorm_le_bound zero_le_one
    intro x
    change ‖P0 x‖ ≤ 1 * ‖x‖
    simpa only [one_mul] using hP0norm x
  have hPNorm : ‖P‖ ≤ 1 := by
    have hext :
        ‖P0c.extend (LinearMap.range E).subtypeL‖ ≤ ‖P0c‖ := by
      simpa using
        (P0c.opNorm_extend_le (N := 1) hDenseSubtype
          (fun x => by simp))
    change ‖P0c.extend (LinearMap.range E).subtypeL‖ ≤ 1
    exact hext.trans (by simpa using hP0cNorm)
  refine ⟨P, hPNorm, fun i => ?_⟩
  let ci : ι →₀ ℂ := Finsupp.single i 1
  have hEi : E ci = v i := by
    simp [E, ci]
  have hMi : M ci = u i := by
    simp [M, ci]
  let xi : LinearMap.range E := ⟨E ci, ⟨ci, rfl⟩⟩
  calc
    P (v i) = P (E ci) := by rw [hEi]
    _ = P ((LinearMap.range E).subtypeL xi) := rfl
    _ = P0c xi := by
      exact P0c.extend_eq hDenseSubtype hUniformSubtype xi
    _ = u i := by
      change P0 xi = u i
      dsimp only [xi]
      rw [hP0_apply, hMi]

/-- The finite positive-kernel form whose nonnegativity says that multiplication by the
Conrey--Li Cayley transform decreases norms on upper kernel combinations. -/
def conreyLiMultiplierDefectQuadratic
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [RKHS ℂ H ℂ ℂ]
    (W : ℂ → ℂ) (c : ℍ →₀ ℂ) : ℂ :=
  c.sum fun w cw =>
    c.sum fun z cz =>
      conj cw * cz *
        (1 - conreyLiCayley W w * conj (conreyLiCayley W z)) *
          RKHS.kernel H (w : ℂ) (z : ℂ) 1

theorem conreyLiMultiplierDefectQuadratic_eq_inner_sub
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [RKHS ℂ H ℂ ℂ]
    (W : ℂ → ℂ) (c : ℍ →₀ ℂ) :
    conreyLiMultiplierDefectQuadratic H W c =
      inner ℂ
          (Finsupp.linearCombination ℂ
            (fun w : ℍ => RKHS.kerFun H (w : ℂ) 1) c)
          (Finsupp.linearCombination ℂ
            (fun w : ℍ => RKHS.kerFun H (w : ℂ) 1) c) -
        inner ℂ
          (Finsupp.linearCombination ℂ
            (fun w : ℍ =>
              conj (conreyLiCayley W w) •
                RKHS.kerFun H (w : ℂ) 1) c)
          (Finsupp.linearCombination ℂ
            (fun w : ℍ =>
              conj (conreyLiCayley W w) •
                RKHS.kerFun H (w : ℂ) 1) c) := by
  classical
  simp only [conreyLiMultiplierDefectQuadratic,
    Finsupp.linearCombination_apply]
  simp_rw [Finsupp.sum_inner, Finsupp.inner_sum, inner_smul_left,
    inner_smul_right, RKHS.kerFun_inner, RKHS.kerFun_apply]
  simp only [RCLike.inner_apply, map_one, mul_one,
    starRingEnd_self_apply]
  rw [← Finsupp.sum_sub]
  apply Finsupp.sum_congr
  intro w _hw
  rw [← Finsupp.sum_sub]
  apply Finsupp.sum_congr
  intro z _hz
  ring

theorem conreyLiKernelCombination_norm_le_of_defect_nonneg
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [RKHS ℂ H ℂ ℂ]
    (W : ℂ → ℂ)
    (hpositive :
      ∀ c : ℍ →₀ ℂ,
        0 ≤ (conreyLiMultiplierDefectQuadratic H W c).re)
    (c : ℍ →₀ ℂ) :
    ‖Finsupp.linearCombination ℂ
        (fun w : ℍ =>
          conj (conreyLiCayley W w) •
            RKHS.kerFun H (w : ℂ) 1) c‖ ≤
      ‖Finsupp.linearCombination ℂ
        (fun w : ℍ => RKHS.kerFun H (w : ℂ) 1) c‖ := by
  let u :=
    Finsupp.linearCombination ℂ
      (fun w : ℍ =>
        conj (conreyLiCayley W w) •
          RKHS.kerFun H (w : ℂ) 1) c
  let v :=
    Finsupp.linearCombination ℂ
      (fun w : ℍ => RKHS.kerFun H (w : ℂ) 1) c
  have h := hpositive c
  rw [conreyLiMultiplierDefectQuadratic_eq_inner_sub] at h
  change 0 ≤ (inner ℂ v v - inner ℂ u u).re at h
  simp only [sub_re] at h
  have hu : (inner ℂ u u).re = ‖u‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) u).symm
  have hv : (inner ℂ v v).re = ‖v‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) v).symm
  rw [hu, hv] at h
  change ‖u‖ ≤ ‖v‖
  nlinarith [norm_nonneg u, norm_nonneg v]

theorem conreyLiMultiplierDefectQuadratic_re_nonneg_of_rkhs_shift
    (Hupper Hhalf : Type*)
    [NormedAddCommGroup Hupper] [InnerProductSpace ℂ Hupper]
    [CompleteSpace Hupper] [RKHS ℂ Hupper ℍ ℂ]
    [NormedAddCommGroup Hhalf] [InnerProductSpace ℂ Hhalf]
    [CompleteSpace Hhalf] [RKHS ℂ Hhalf ℂ ℂ]
    (W : ℂ → ℂ) (T : Hupper →ₗ[ℂ] Hupper)
    (hkernelUpper : ∀ w z : ℍ,
      RKHS.kernel Hupper z w 1 = conreyLiKernel W w z)
    (hshift : ∀ w : ℍ,
      T (RKHS.kerFun Hupper w 1) =
        RKHS.kerFun Hupper (conreyLiUpperShift w) 1)
    (hpositiveUpper :
      ∀ f : Hupper, 0 ≤ (inner ℂ f (T f)).re)
    (hW : ∀ w : ℍ, W w ≠ 0)
    (hkernelHalf :
      ∀ w ∈ conreyLiHalfStrip, ∀ z ∈ conreyLiHalfStrip,
        RKHS.kernel Hhalf z w 1 = conreyLiHardyKernel w z)
    (c : ℍ →₀ ℂ) :
    0 ≤ (conreyLiMultiplierDefectQuadratic Hhalf W c).re := by
  let S : ℍ → ℂ :=
    fun w => W w + W (conreyLiUpperShift w)
  have hratio :
      ∀ w : ℍ, 0 ≤ (conreyLiUpperShiftRatio W w).re :=
    conreyLiUpperShiftRatio_re_nonneg_of_rkhs_shift
      W T hkernelUpper hshift hpositiveUpper hW
  have hS : ∀ w : ℍ, S w ≠ 0 := by
    intro w
    exact conreyLi_W_add_shift_ne_zero W w
      (hW (conreyLiUpperShift w)) (hratio w)
  let d : ℍ → ℂ := fun w => c w / conj (S w)
  have hshifted :
      0 ≤
        (conreyLiShiftedKernelQuadratic W c.support id d).re :=
    conreyLiShiftedKernelQuadratic_re_nonneg_of_rkhs_shift
      W T hkernelUpper hshift hpositiveUpper c.support id d
  have heq :
      conreyLiMultiplierDefectQuadratic Hhalf W c =
        2 * conreyLiShiftedKernelQuadratic W c.support id d := by
    classical
    simp only [conreyLiMultiplierDefectQuadratic, Finsupp.sum,
      conreyLiShiftedKernelQuadratic, id_eq]
    rw [Finset.sum_comm]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    rw [hkernelHalf (a : ℂ) (upper_mem_conreyLiHalfStrip a)
      (b : ℂ) (upper_mem_conreyLiHalfStrip b)]
    rw [conreyLi_shiftedKernel_add_eq_halfStripDefect
      W a b (hS a) (hS b)]
    change
      conj (c b) * c a *
          (1 - conreyLiCayley W b * conj (conreyLiCayley W a)) *
            conreyLiHardyKernel a b =
        2 * ((c a / conj (S a)) * conj (c b / conj (S b)) *
          ((S b * conj (S a) / 2) *
            ((1 - conreyLiCayley W b *
                conj (conreyLiCayley W a)) *
              conreyLiHardyKernel a b)))
    have hSaConj : conj (S a) ≠ 0 := by
      intro h
      apply hS a
      have hc := congrArg conj h
      simpa using hc
    simp only [map_div₀, starRingEnd_self_apply]
    field_simp [hS a, hS b, hSaConj]
  rw [heq, mul_re]
  norm_num
  linarith

theorem exists_conreyLiKernelMultiplier
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [RKHS ℂ H ℂ ℂ]
    (W : ℂ → ℂ)
    (hanalytic :
      ∀ f : H, AnalyticOnNhd ℂ (fun z : ℂ => f z) conreyLiHalfStrip)
    (hunique :
      ∀ f : H, (∀ z ∈ conreyLiHalfStrip, f z = 0) → f = 0)
    (hnorm : ∀ c : ℍ →₀ ℂ,
      ‖Finsupp.linearCombination ℂ
          (fun w : ℍ =>
            conj (conreyLiCayley W w) •
              RKHS.kerFun H (w : ℂ) 1) c‖ ≤
        ‖Finsupp.linearCombination ℂ
          (fun w : ℍ => RKHS.kerFun H (w : ℂ) 1) c‖) :
    ∃ P : H →L[ℂ] H,
      ‖P‖ ≤ 1 ∧
        ∀ w : ℍ,
          P (RKHS.kerFun H (w : ℂ) 1) =
            conj (conreyLiCayley W w) •
              RKHS.kerFun H (w : ℂ) 1 := by
  apply exists_contraction_of_finsupp_rule H
    (fun w : ℍ => RKHS.kerFun H (w : ℂ) 1)
    (fun w : ℍ =>
      conj (conreyLiCayley W w) • RKHS.kerFun H (w : ℂ) 1)
  · have hset :
        conreyLiUpperKernelSet H =
          Set.range (fun w : ℍ => RKHS.kerFun H (w : ℂ) 1) := by
      ext f
      simp only [conreyLiUpperKernelSet, Set.mem_setOf_eq,
        Set.mem_range]
      constructor
      · rintro ⟨w, rfl⟩
        exact ⟨w, rfl⟩
      · rintro ⟨w, rfl⟩
        exact ⟨w, rfl⟩
    rw [← hset]
    exact conreyLiUpperKernel_span_dense H hanalytic hunique
  · exact hnorm

theorem exists_conreyLiKernelMultiplier_of_defect_nonneg
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [RKHS ℂ H ℂ ℂ]
    (W : ℂ → ℂ)
    (hanalytic :
      ∀ f : H, AnalyticOnNhd ℂ (fun z : ℂ => f z) conreyLiHalfStrip)
    (hunique :
      ∀ f : H, (∀ z ∈ conreyLiHalfStrip, f z = 0) → f = 0)
    (hpositive :
      ∀ c : ℍ →₀ ℂ,
        0 ≤ (conreyLiMultiplierDefectQuadratic H W c).re) :
    ∃ P : H →L[ℂ] H,
      ‖P‖ ≤ 1 ∧
        ∀ w : ℍ,
          P (RKHS.kerFun H (w : ℂ) 1) =
            conj (conreyLiCayley W w) •
              RKHS.kerFun H (w : ℂ) 1 := by
  apply exists_conreyLiKernelMultiplier H W hanalytic hunique
  exact conreyLiKernelCombination_norm_le_of_defect_nonneg
    H W hpositive

section AdjointContinuation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [RKHS ℂ H ℂ ℂ]

/-- The source adjoint formula, normalized at the half-strip kernel centered at zero. -/
def conreyLiHalfStripCayleyExtension
    (P : H →L[ℂ] H) (z : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * I * (-z - I)) *
    (P.adjoint (RKHS.kerFun H 0 1)) z

theorem conreyLi_adjoint_apply_upper
    (W : ℂ → ℂ) (P : H →L[ℂ] H)
    (hPker : ∀ w : ℍ,
      P (RKHS.kerFun H (w : ℂ) 1) =
        conj (conreyLiCayley W w) • RKHS.kerFun H (w : ℂ) 1)
    (f : H) (w : ℍ) :
    (P.adjoint f) (w : ℂ) = conreyLiCayley W w * f (w : ℂ) := by
  calc
    (P.adjoint f) (w : ℂ) =
        inner ℂ (RKHS.kerFun H (w : ℂ) 1) (P.adjoint f) := by simp
    _ = inner ℂ (P (RKHS.kerFun H (w : ℂ) 1)) f := by
      rw [ContinuousLinearMap.adjoint_inner_right]
    _ = conreyLiCayley W w * f (w : ℂ) := by
      rw [hPker]
      simp only [inner_smul_left, starRingEnd_self_apply,
        RKHS.kerFun_inner, RCLike.inner_apply, map_one, mul_one]

theorem conreyLiHalfStripCayleyExtension_eq_upper
    (W : ℂ → ℂ) (P : H →L[ℂ] H)
    (hkernel : ∀ w ∈ conreyLiHalfStrip, ∀ z ∈ conreyLiHalfStrip,
      RKHS.kernel H z w 1 = conreyLiHardyKernel w z)
    (hPker : ∀ w : ℍ,
      P (RKHS.kerFun H (w : ℂ) 1) =
        conj (conreyLiCayley W w) • RKHS.kerFun H (w : ℂ) 1)
    (w : ℍ) :
    conreyLiHalfStripCayleyExtension P (w : ℂ) =
      conreyLiCayley W w := by
  have hadj :=
    conreyLi_adjoint_apply_upper W P hPker
      (RKHS.kerFun H 0 1) w
  rw [conreyLiHalfStripCayleyExtension, hadj, RKHS.kerFun_apply,
    hkernel 0 zero_mem_conreyLiHalfStrip (w : ℂ)
      (upper_mem_conreyLiHalfStrip w),
    conreyLiHardyKernel_zero]
  have hfactor :=
    conreyLiHardyAnchorFactor_ne_zero (upper_mem_conreyLiHalfStrip w)
  have htail : -(w : ℂ) - I ≠ 0 := by
    intro h
    apply hfactor
    simp [h]
  field_simp [htail]

theorem analyticOnNhd_conreyLiHalfStripCayleyExtension
    (P : H →L[ℂ] H)
    (hanalytic :
      ∀ f : H, AnalyticOnNhd ℂ (fun z : ℂ => f z) conreyLiHalfStrip) :
    AnalyticOnNhd ℂ (conreyLiHalfStripCayleyExtension P)
      conreyLiHalfStrip := by
  apply AnalyticOnNhd.mul
  · exact analyticOnNhd_const.mul
      (analyticOnNhd_id.neg.sub analyticOnNhd_const)
  · exact hanalytic (P.adjoint (RKHS.kerFun H 0 1))

theorem conreyLi_adjoint_multiplier_identity
    (W : ℂ → ℂ) (P : H →L[ℂ] H)
    (hanalytic :
      ∀ f : H, AnalyticOnNhd ℂ (fun z : ℂ => f z) conreyLiHalfStrip)
    (hkernel : ∀ w ∈ conreyLiHalfStrip, ∀ z ∈ conreyLiHalfStrip,
      RKHS.kernel H z w 1 = conreyLiHardyKernel w z)
    (hPker : ∀ w : ℍ,
      P (RKHS.kerFun H (w : ℂ) 1) =
        conj (conreyLiCayley W w) • RKHS.kerFun H (w : ℂ) 1)
    (f : H) {z : ℂ} (hz : z ∈ conreyLiHalfStrip) :
    conreyLiHalfStripCayleyExtension P z * f z =
      (P.adjoint f) z := by
  have hleft :
      AnalyticOnNhd ℂ
        (fun z : ℂ => conreyLiHalfStripCayleyExtension P z * f z)
        conreyLiHalfStrip :=
    (analyticOnNhd_conreyLiHalfStripCayleyExtension P hanalytic).mul
      (hanalytic f)
  have hright :
      AnalyticOnNhd ℂ (fun z : ℂ => (P.adjoint f) z)
        conreyLiHalfStrip :=
    hanalytic (P.adjoint f)
  have hevent :
      (fun z : ℂ => conreyLiHalfStripCayleyExtension P z * f z) =ᶠ[𝓝 I]
        (fun z : ℂ => (P.adjoint f) z) := by
    have hopen : IsOpen {z : ℂ | 0 < z.im} :=
      isOpen_lt continuous_const Complex.continuous_im
    have hI : I ∈ {z : ℂ | 0 < z.im} := by simp
    filter_upwards [hopen.mem_nhds hI] with z hzUpper
    let w : ℍ := ⟨z, hzUpper⟩
    rw [conreyLiHalfStripCayleyExtension_eq_upper W P hkernel hPker w,
      conreyLi_adjoint_apply_upper W P hPker f w]
  exact hleft.eqOn_of_preconnected_of_eventuallyEq
    hright isPreconnected_conreyLiHalfStrip
    (upper_mem_conreyLiHalfStrip ⟨I, by simp⟩) hevent hz

theorem conreyLiHardyKerFun_ne_zero
    (hkernel : ∀ w ∈ conreyLiHalfStrip, ∀ z ∈ conreyLiHalfStrip,
      RKHS.kernel H z w 1 = conreyLiHardyKernel w z)
    {z : ℂ} (hz : z ∈ conreyLiHalfStrip) :
    RKHS.kerFun H z 1 ≠ 0 := by
  intro hzero
  have heval := congrArg (fun f : H => f z) hzero
  simp only [RKHS.kerFun_apply, RKHS.coe_zero, Pi.zero_apply] at heval
  rw [hkernel z hz z hz] at heval
  exact conreyLiHardyKernel_self_ne_zero hz heval

theorem norm_conreyLiHalfStripCayleyExtension_le_one
    (W : ℂ → ℂ) (P : H →L[ℂ] H)
    (hanalytic :
      ∀ f : H, AnalyticOnNhd ℂ (fun z : ℂ => f z) conreyLiHalfStrip)
    (hkernel : ∀ w ∈ conreyLiHalfStrip, ∀ z ∈ conreyLiHalfStrip,
      RKHS.kernel H z w 1 = conreyLiHardyKernel w z)
    (hPker : ∀ w : ℍ,
      P (RKHS.kerFun H (w : ℂ) 1) =
        conj (conreyLiCayley W w) • RKHS.kerFun H (w : ℂ) 1)
    (hPnorm : ‖P‖ ≤ 1)
    {z : ℂ} (hz : z ∈ conreyLiHalfStrip) :
    ‖conreyLiHalfStripCayleyExtension P z‖ ≤ 1 := by
  let k : H := RKHS.kerFun H z 1
  have hkNe : k ≠ 0 := by
    exact conreyLiHardyKerFun_ne_zero hkernel hz
  have hkNorm : 0 < ‖k‖ := norm_pos_iff.mpr hkNe
  have hdiag : k z = ((‖k‖ : ℂ) ^ 2) := by
    calc
      k z = inner ℂ k k := by
        symm
        simp only [k, RKHS.kerFun_inner, RCLike.inner_apply,
          map_one, mul_one]
      _ = ((‖k‖ : ℂ) ^ 2) := inner_self_eq_norm_sq_to_K k
  have hmult :=
    conreyLi_adjoint_multiplier_identity W P hanalytic hkernel hPker k hz
  have hnormMult :
      ‖conreyLiHalfStripCayleyExtension P z‖ * ‖k‖ ^ 2 =
        ‖(P.adjoint k) z‖ := by
    rw [← hmult, norm_mul, hdiag, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (norm_nonneg k)]
  have hnormEval :
      ‖(P.adjoint k) z‖ ≤ ‖k‖ * ‖P.adjoint k‖ := by
    calc
      ‖(P.adjoint k) z‖ =
          ‖inner ℂ k (P.adjoint k)‖ := by
            congr 1
            symm
            simp only [k, RKHS.kerFun_inner, RCLike.inner_apply,
              map_one, mul_one]
      _ ≤ ‖k‖ * ‖P.adjoint k‖ :=
        norm_inner_le_norm k (P.adjoint k)
  have hPadj : ‖P.adjoint k‖ ≤ ‖k‖ := by
    calc
      ‖P.adjoint k‖ ≤ ‖P.adjoint‖ * ‖k‖ :=
        P.adjoint.le_opNorm k
      _ = ‖P‖ * ‖k‖ := by
        rw [ContinuousLinearMap.adjoint.norm_map]
      _ ≤ 1 * ‖k‖ :=
        mul_le_mul_of_nonneg_right hPnorm (norm_nonneg k)
      _ = ‖k‖ := one_mul _
  have hbound :
      ‖conreyLiHalfStripCayleyExtension P z‖ * ‖k‖ ^ 2 ≤
        ‖k‖ ^ 2 := by
    rw [hnormMult]
    calc
      ‖(P.adjoint k) z‖ ≤ ‖k‖ * ‖P.adjoint k‖ := hnormEval
      _ ≤ ‖k‖ * ‖k‖ :=
        mul_le_mul_of_nonneg_left hPadj (norm_nonneg k)
      _ = ‖k‖ ^ 2 := by ring
  nlinarith [sq_pos_of_pos hkNorm]

structure ConreyLiHalfStripCertificate (W : ℂ → ℂ) where
  extension : ℂ → ℂ
  analytic :
    AnalyticOnNhd ℂ extension conreyLiHalfStrip
  agrees_upper :
    ∀ w : ℍ, extension (w : ℂ) = conreyLiCayley W w
  contractive :
    ∀ z ∈ conreyLiHalfStrip, ‖extension z‖ ≤ 1

noncomputable def conreyLiHalfStrip_endpoint
    (W : ℂ → ℂ)
    (hanalytic :
      ∀ f : H, AnalyticOnNhd ℂ (fun z : ℂ => f z) conreyLiHalfStrip)
    (hunique :
      ∀ f : H, (∀ z ∈ conreyLiHalfStrip, f z = 0) → f = 0)
    (hkernel : ∀ w ∈ conreyLiHalfStrip, ∀ z ∈ conreyLiHalfStrip,
      RKHS.kernel H z w 1 = conreyLiHardyKernel w z)
    (hpositive :
      ∀ c : ℍ →₀ ℂ,
        0 ≤ (conreyLiMultiplierDefectQuadratic H W c).re) :
    ConreyLiHalfStripCertificate W := by
  let hexists :=
    exists_conreyLiKernelMultiplier_of_defect_nonneg
      H W hanalytic hunique hpositive
  let P : H →L[ℂ] H := Classical.choose hexists
  have hPspec := Classical.choose_spec hexists
  have hPnorm : ‖P‖ ≤ 1 := hPspec.1
  have hPker :
      ∀ w : ℍ,
        P (RKHS.kerFun H (w : ℂ) 1) =
          conj (conreyLiCayley W w) •
            RKHS.kerFun H (w : ℂ) 1 :=
    hPspec.2
  exact
    { extension := conreyLiHalfStripCayleyExtension P
      analytic :=
        analyticOnNhd_conreyLiHalfStripCayleyExtension P hanalytic
      agrees_upper :=
        conreyLiHalfStripCayleyExtension_eq_upper W P hkernel hPker
      contractive := fun z hz =>
        norm_conreyLiHalfStripCayleyExtension_le_one
          W P hanalytic hkernel hPker hPnorm hz }

noncomputable def conreyLiHalfStrip_endpoint_of_rkhs_shift
    (Hupper : Type*)
    [NormedAddCommGroup Hupper] [InnerProductSpace ℂ Hupper]
    [CompleteSpace Hupper] [RKHS ℂ Hupper ℍ ℂ]
    (W : ℂ → ℂ) (T : Hupper →ₗ[ℂ] Hupper)
    (hkernelUpper : ∀ w z : ℍ,
      RKHS.kernel Hupper z w 1 = conreyLiKernel W w z)
    (hshift : ∀ w : ℍ,
      T (RKHS.kerFun Hupper w 1) =
        RKHS.kerFun Hupper (conreyLiUpperShift w) 1)
    (hpositiveUpper :
      ∀ f : Hupper, 0 ≤ (inner ℂ f (T f)).re)
    (hW : ∀ w : ℍ, W w ≠ 0)
    (hanalytic :
      ∀ f : H, AnalyticOnNhd ℂ (fun z : ℂ => f z) conreyLiHalfStrip)
    (hunique :
      ∀ f : H, (∀ z ∈ conreyLiHalfStrip, f z = 0) → f = 0)
    (hkernelHalf :
      ∀ w ∈ conreyLiHalfStrip, ∀ z ∈ conreyLiHalfStrip,
        RKHS.kernel H z w 1 = conreyLiHardyKernel w z) :
    ConreyLiHalfStripCertificate W :=
  conreyLiHalfStrip_endpoint W hanalytic hunique hkernelHalf
    (conreyLiMultiplierDefectQuadratic_re_nonneg_of_rkhs_shift
      Hupper H W T hkernelUpper hshift hpositiveUpper hW hkernelHalf)

end AdjointContinuation

end

end LeanLab.Riemann
