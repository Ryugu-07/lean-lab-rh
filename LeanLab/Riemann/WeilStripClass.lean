import LeanLab.Riemann.WeilConvolution
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.CauchyIntegral

set_option linter.style.header false

/-!
# Lagarias-style Weil strip test algebra

This file packages the physical Mellin test-function conditions from Lagarias's `A_delta` space
and proves the algebra operations needed by Weil's covariance form. It does not claim metric
separation, completeness, density, an explicit formula, or positivity.
-/

noncomputable section

open Complex MeasureTheory Real Set
open scoped ComplexConjugate

namespace LeanLab.Riemann

/-- The open Mellin strip of radius `δ` centered at `Re(s) = 1/2`. -/
def weilOpenStrip (δ : ℝ) : Set ℂ :=
  {s | |s.re - 1 / 2| < δ}

/-- The closed Mellin strip of radius `δ` centered at `Re(s) = 1/2`. -/
def weilClosedStrip (δ : ℝ) : Set ℂ :=
  {s | |s.re - 1 / 2| ≤ δ}

theorem isOpen_weilOpenStrip (δ : ℝ) : IsOpen (weilOpenStrip δ) := by
  exact isOpen_lt (Complex.continuous_re.sub continuous_const).abs continuous_const

theorem weilOpenStrip_subset_closedStrip (δ : ℝ) :
    weilOpenStrip δ ⊆ weilClosedStrip δ := by
  intro s hs
  change |s.re - 1 / 2| < δ at hs
  change |s.re - 1 / 2| ≤ δ
  exact le_of_lt hs

theorem one_sub_mem_weilOpenStrip_iff {δ : ℝ} {s : ℂ} :
    1 - s ∈ weilOpenStrip δ ↔ s ∈ weilOpenStrip δ := by
  change |(1 - s).re - 1 / 2| < δ ↔ |s.re - 1 / 2| < δ
  have h : (1 - s).re - 1 / 2 = -(s.re - 1 / 2) := by
    norm_num
    ring
  rw [h, abs_neg]

theorem one_sub_mem_weilClosedStrip_iff {δ : ℝ} {s : ℂ} :
    1 - s ∈ weilClosedStrip δ ↔ s ∈ weilClosedStrip δ := by
  change |(1 - s).re - 1 / 2| ≤ δ ↔ |s.re - 1 / 2| ≤ δ
  have h : (1 - s).re - 1 / 2 = -(s.re - 1 / 2) := by
    norm_num
    ring
  rw [h, abs_neg]

theorem conj_mem_weilOpenStrip_iff {δ : ℝ} {s : ℂ} :
    conj s ∈ weilOpenStrip δ ↔ s ∈ weilOpenStrip δ := by
  simp only [weilOpenStrip, mem_setOf_eq, conj_re]

theorem conj_mem_weilClosedStrip_iff {δ : ℝ} {s : ℂ} :
    conj s ∈ weilClosedStrip δ ↔ s ∈ weilClosedStrip δ := by
  simp only [weilClosedStrip, mem_setOf_eq, conj_re]

theorem one_sub_conj_mem_weilOpenStrip_iff {δ : ℝ} {s : ℂ} :
    1 - conj s ∈ weilOpenStrip δ ↔ s ∈ weilOpenStrip δ := by
  rw [one_sub_mem_weilOpenStrip_iff, conj_mem_weilOpenStrip_iff]

theorem one_sub_conj_mem_weilClosedStrip_iff {δ : ℝ} {s : ℂ} :
    1 - conj s ∈ weilClosedStrip δ ↔ s ∈ weilClosedStrip δ := by
  rw [one_sub_mem_weilClosedStrip_iff, conj_mem_weilClosedStrip_iff]

/-- A source-facing physical Weil test function on the strip centered at `1/2`.

The explicit convergence field prevents Mathlib's value for a nonintegrable integral from being
mistaken for an analytic Mellin transform. The boundedness witness records finiteness of the
closed-strip uniform norm without claiming a separated or complete normed space of raw functions.
-/
structure IsWeilStripAdmissible (δ : ℝ) (f : ℝ → ℂ) : Prop where
  delta_pos : 0 < δ
  convergent : ∀ s ∈ weilClosedStrip δ, MellinConvergent f s
  analyticOn : AnalyticOnNhd ℂ (mellin f) (weilOpenStrip δ)
  continuousOn : ContinuousOn (mellin f) (weilClosedStrip δ)
  uniformlyBounded : ∃ C : ℝ, 0 ≤ C ∧
    ∀ s ∈ weilClosedStrip δ, ‖mellin f s‖ ≤ C

/-- The zero physical test function is admissible on every positive-width strip. -/
theorem isWeilStripAdmissible_zero {δ : ℝ} (hδ : 0 < δ) :
    IsWeilStripAdmissible δ (0 : ℝ → ℂ) := by
  refine ⟨hδ, ?_, ?_, ?_, 0, le_rfl, ?_⟩
  · intro s hs
    simp [MellinConvergent]
  · have hm : mellin (0 : ℝ → ℂ) = 0 := by
      funext s
      simp [mellin]
    rw [hm]
    exact analyticOnNhd_const
  · have hm : mellin (0 : ℝ → ℂ) = 0 := by
      funext s
      simp [mellin]
    rw [hm]
    exact continuousOn_const
  · intro s hs
    simp [mellin]

/-- The physical strip class is closed under addition. -/
theorem IsWeilStripAdmissible.add {δ : ℝ} {f g : ℝ → ℂ}
    (hf : IsWeilStripAdmissible δ f) (hg : IsWeilStripAdmissible δ g) :
    IsWeilStripAdmissible δ (f + g) := by
  refine ⟨hf.delta_pos, ?_, ?_, ?_, ?_⟩
  · intro s hs
    exact (hasMellin_add (hf.convergent s hs) (hg.convergent s hs)).1
  · apply (hf.analyticOn.add hg.analyticOn).congr (isOpen_weilOpenStrip δ)
    intro s hs
    exact (hasMellin_add (hf.convergent s (weilOpenStrip_subset_closedStrip δ hs))
      (hg.convergent s (weilOpenStrip_subset_closedStrip δ hs))).2.symm
  · apply (hf.continuousOn.add hg.continuousOn).congr
    intro s hs
    exact (hasMellin_add (hf.convergent s hs) (hg.convergent s hs)).2
  · rcases hf.uniformlyBounded with ⟨C, hC, hfC⟩
    rcases hg.uniformlyBounded with ⟨D, hD, hgD⟩
    refine ⟨C + D, add_nonneg hC hD, ?_⟩
    intro s hs
    change ‖mellin (fun t ↦ f t + g t) s‖ ≤ C + D
    rw [(hasMellin_add (hf.convergent s hs) (hg.convergent s hs)).2]
    exact (norm_add_le _ _).trans (add_le_add (hfC s hs) (hgD s hs))

/-- The physical strip class is closed under complex scalar multiplication. -/
theorem IsWeilStripAdmissible.const_smul {δ : ℝ} {f : ℝ → ℂ}
    (hf : IsWeilStripAdmissible δ f) (c : ℂ) :
    IsWeilStripAdmissible δ (c • f) := by
  refine ⟨hf.delta_pos, ?_, ?_, ?_, ?_⟩
  · intro s hs
    exact (hasMellin_const_smul (hf.convergent s hs) c).1
  · apply (hf.analyticOn.const_smul (c := c)).congr (isOpen_weilOpenStrip δ)
    intro s hs
    exact (hasMellin_const_smul
      (hf.convergent s (weilOpenStrip_subset_closedStrip δ hs)) c).2.symm
  · apply (hf.continuousOn.const_smul c).congr
    intro s hs
    exact (hasMellin_const_smul (hf.convergent s hs) c).2
  · rcases hf.uniformlyBounded with ⟨C, hC, hfC⟩
    refine ⟨‖c‖ * C, mul_nonneg (norm_nonneg _) hC, ?_⟩
    intro s hs
    change ‖mellin (fun t ↦ c • f t) s‖ ≤ ‖c‖ * C
    rw [(hasMellin_const_smul (hf.convergent s hs) c).2, norm_smul]
    exact mul_le_mul_of_nonneg_left (hfC s hs) (norm_nonneg _)

/-- The physical strip class is closed under Weil's multiplicative involution. -/
theorem IsWeilStripAdmissible.weilInvolution {δ : ℝ} {f : ℝ → ℂ}
    (hf : IsWeilStripAdmissible δ f) :
    IsWeilStripAdmissible δ (LeanLab.Riemann.weilInvolution f) := by
  refine ⟨hf.delta_pos, ?_, ?_, ?_, ?_⟩
  · intro s hs
    exact (mellinConvergent_weilInvolution_iff f s).2
      (hf.convergent (1 - s) (one_sub_mem_weilClosedStrip_iff.2 hs))
  · have hcomp : AnalyticOnNhd ℂ ((mellin f) ∘ fun s : ℂ ↦ 1 - s)
        (weilOpenStrip δ) :=
      hf.analyticOn.comp (analyticOnNhd_const.sub analyticOnNhd_id)
        (fun _ hs ↦ one_sub_mem_weilOpenStrip_iff.2 hs)
    apply hcomp.congr (isOpen_weilOpenStrip δ)
    intro s hs
    exact (mellin_weilInvolution f s).symm
  · have hcomp : ContinuousOn ((mellin f) ∘ fun s : ℂ ↦ 1 - s)
        (weilClosedStrip δ) :=
      hf.continuousOn.comp (continuous_const.sub continuous_id).continuousOn
        (fun _ hs ↦ one_sub_mem_weilClosedStrip_iff.2 hs)
    apply hcomp.congr
    intro s hs
    exact mellin_weilInvolution f s
  · rcases hf.uniformlyBounded with ⟨C, hC, hfC⟩
    refine ⟨C, hC, ?_⟩
    intro s hs
    rw [mellin_weilInvolution]
    exact hfC (1 - s) (one_sub_mem_weilClosedStrip_iff.2 hs)

/-- Complex conjugation of a physical function preserves the strip class. -/
theorem IsWeilStripAdmissible.conj {δ : ℝ} {f : ℝ → ℂ}
    (hf : IsWeilStripAdmissible δ f) :
    IsWeilStripAdmissible δ (fun x ↦ conj (f x)) := by
  refine ⟨hf.delta_pos, ?_, ?_, ?_, ?_⟩
  · intro s hs
    exact (mellinConvergent_conj_iff f s).2
      (hf.convergent (conj s) (conj_mem_weilClosedStrip_iff.2 hs))
  · have hdiff : DifferentiableOn ℂ (fun s : ℂ ↦ conj (mellin f (conj s)))
        (weilOpenStrip δ) := by
      intro s hs
      have hcs : conj s ∈ weilOpenStrip δ := conj_mem_weilOpenStrip_iff.2 hs
      have hAt : DifferentiableAt ℂ (mellin f) (conj s) :=
        (hf.analyticOn.differentiableOn (conj s) hcs).differentiableAt
          ((isOpen_weilOpenStrip δ).mem_nhds hcs)
      change DifferentiableWithinAt ℂ (conj ∘ mellin f ∘ conj) (weilOpenStrip δ) s
      simpa only [Complex.conj_conj] using hAt.conj_conj.differentiableWithinAt
    have han : AnalyticOnNhd ℂ (fun s : ℂ ↦ conj (mellin f (conj s)))
        (weilOpenStrip δ) :=
      (analyticOnNhd_iff_differentiableOn (isOpen_weilOpenStrip δ)).2 hdiff
    apply han.congr (isOpen_weilOpenStrip δ)
    intro s hs
    exact (mellin_conj f s).symm
  · have hmid : ContinuousOn (fun s : ℂ ↦ mellin f (conj s)) (weilClosedStrip δ) :=
      hf.continuousOn.comp continuous_conj.continuousOn
        (fun _ hs ↦ conj_mem_weilClosedStrip_iff.2 hs)
    have hout : ContinuousOn (fun s : ℂ ↦ conj (mellin f (conj s)))
        (weilClosedStrip δ) :=
      continuous_conj.continuousOn.comp hmid (fun _ _ ↦ mem_univ _)
    apply hout.congr
    intro s hs
    exact mellin_conj f s
  · rcases hf.uniformlyBounded with ⟨C, hC, hfC⟩
    refine ⟨C, hC, ?_⟩
    intro s hs
    rw [mellin_conj, norm_conj]
    exact hfC (conj s) (conj_mem_weilClosedStrip_iff.2 hs)

/-- The conjugate Weil star preserves the physical strip class. -/
theorem IsWeilStripAdmissible.weilStar {δ : ℝ} {f : ℝ → ℂ}
    (hf : IsWeilStripAdmissible δ f) :
    IsWeilStripAdmissible δ (LeanLab.Riemann.weilStar f) := by
  change IsWeilStripAdmissible δ (fun x ↦ conj (LeanLab.Riemann.weilInvolution f x))
  exact hf.weilInvolution.conj

/-- The physical strip class is closed under source-faithful multiplicative convolution. -/
theorem IsWeilStripAdmissible.weilConvolution {δ : ℝ} {f g : ℝ → ℂ}
    (hf : IsWeilStripAdmissible δ f) (hg : IsWeilStripAdmissible δ g) :
    IsWeilStripAdmissible δ (LeanLab.Riemann.weilConvolution f g) := by
  refine ⟨hf.delta_pos, ?_, ?_, ?_, ?_⟩
  · intro s hs
    exact mellinConvergent_weilConvolution (hf.convergent s hs) (hg.convergent s hs)
  · apply (hf.analyticOn.mul hg.analyticOn).congr (isOpen_weilOpenStrip δ)
    intro s hs
    exact (mellin_weilConvolution
      (hf.convergent s (weilOpenStrip_subset_closedStrip δ hs))
      (hg.convergent s (weilOpenStrip_subset_closedStrip δ hs))).symm
  · apply (hf.continuousOn.mul hg.continuousOn).congr
    intro s hs
    exact mellin_weilConvolution (hf.convergent s hs) (hg.convergent s hs)
  · rcases hf.uniformlyBounded with ⟨C, hC, hfC⟩
    rcases hg.uniformlyBounded with ⟨D, hD, hgD⟩
    refine ⟨C * D, mul_nonneg hC hD, ?_⟩
    intro s hs
    rw [mellin_weilConvolution (hf.convergent s hs) (hg.convergent s hs), norm_mul]
    exact mul_le_mul (hfC s hs) (hgD s hs) (norm_nonneg _) hC

/-- Every admissible test function has an admissible physical Weil autocorrelation. -/
theorem IsWeilStripAdmissible.weilAutocorrelation {δ : ℝ} {f : ℝ → ℂ}
    (hf : IsWeilStripAdmissible δ f) :
    IsWeilStripAdmissible δ
      (LeanLab.Riemann.weilConvolution f (LeanLab.Riemann.weilStar f)) :=
  hf.weilConvolution hf.weilStar

end LeanLab.Riemann
