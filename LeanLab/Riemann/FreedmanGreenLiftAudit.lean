import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option linter.style.header false

noncomputable section

/-!
# A Green-lift contraction countermodel for a Weyl/Volterra literature audit

The audited implication combines a contractive middle multiplier with trace-fiber
Euler--Lagrange orthogonality and then declares the surrounding compressed lift contractive. This
file checks a two-dimensional real model showing that those listed premises do not control the
compression and right-inverse norms.
-/

namespace LeanLab.Riemann

/-- The two-dimensional form domain in the Green-lift countermodel. -/
abbrev FreedmanGreenAuditSpace := ℝ × ℝ

/-- The trace map; its kernel is the nontrivial second-coordinate axis. -/
def freedmanGreenAuditTrace (v : FreedmanGreenAuditSpace) : ℝ := v.1

/-- The selected representative in the fiber with prescribed trace. -/
def freedmanGreenAuditRepresentative (x : ℝ) : FreedmanGreenAuditSpace := (x, 0)

/-- The positive feature of the scalar countermodel. -/
def freedmanGreenAuditPositiveFeature (v : FreedmanGreenAuditSpace) : ℝ := v.1

/-- The negative feature, twice the positive feature. -/
def freedmanGreenAuditNegativeFeature (v : FreedmanGreenAuditSpace) : ℝ := 2 * v.1

/-- The contractive middle multiplier. -/
def freedmanGreenAuditMultiplier (t : ℝ) : ℝ := t / 2

/-- The Green lift in the scalar feature coordinate. -/
def freedmanGreenAuditLift (t : ℝ) : ℝ := t

/-- The outer compression, which is not normalized as a contraction. -/
def freedmanGreenAuditCompression (t : ℝ) : ℝ := 4 * t

/-- The signed positive-minus-negative feature form. -/
def freedmanGreenAuditForm
    (v w : FreedmanGreenAuditSpace) : ℝ :=
  freedmanGreenAuditPositiveFeature v * freedmanGreenAuditPositiveFeature w -
    freedmanGreenAuditNegativeFeature v * freedmanGreenAuditNegativeFeature w

theorem freedmanGreenAudit_trace_representative (x : ℝ) :
    freedmanGreenAuditTrace (freedmanGreenAuditRepresentative x) = x := by
  rfl

theorem freedmanGreenAudit_trace_has_nontrivial_kernel :
    ∃ h : FreedmanGreenAuditSpace, h ≠ 0 ∧ freedmanGreenAuditTrace h = 0 := by
  refine ⟨(0, 1), ?_, rfl⟩
  norm_num

theorem freedmanGreenAudit_eulerLagrange_on_traceKernel
    (x : ℝ) (h : FreedmanGreenAuditSpace)
    (hh : freedmanGreenAuditTrace h = 0) :
    freedmanGreenAuditForm (freedmanGreenAuditRepresentative x) h = 0 := by
  change x * h.1 - (2 * x) * (2 * h.1) = 0
  change h.1 = 0 at hh
  rw [hh]
  ring

theorem freedmanGreenAudit_multiplier_contraction (t : ℝ) :
    |freedmanGreenAuditMultiplier t| ≤ |t| := by
  rw [freedmanGreenAuditMultiplier, abs_div]
  norm_num

theorem freedmanGreenAudit_compressed_factorization (x : ℝ) :
    freedmanGreenAuditNegativeFeature (freedmanGreenAuditRepresentative x) =
      freedmanGreenAuditCompression
        (freedmanGreenAuditMultiplier
          (freedmanGreenAuditLift
            (freedmanGreenAuditPositiveFeature (freedmanGreenAuditRepresentative x)))) := by
  norm_num [freedmanGreenAuditNegativeFeature, freedmanGreenAuditRepresentative,
    freedmanGreenAuditCompression, freedmanGreenAuditMultiplier, freedmanGreenAuditLift,
    freedmanGreenAuditPositiveFeature]
  ring

theorem not_freedmanGreenAudit_compressed_contraction :
    ¬ ∀ x : ℝ,
      |freedmanGreenAuditCompression
        (freedmanGreenAuditMultiplier
          (freedmanGreenAuditLift
            (freedmanGreenAuditPositiveFeature (freedmanGreenAuditRepresentative x))))| ≤
        |freedmanGreenAuditPositiveFeature (freedmanGreenAuditRepresentative x)| := by
  intro h
  have hunit := h 1
  norm_num [freedmanGreenAuditCompression, freedmanGreenAuditMultiplier,
    freedmanGreenAuditLift, freedmanGreenAuditPositiveFeature,
    freedmanGreenAuditRepresentative] at hunit

theorem freedmanGreenAudit_unit_form :
    freedmanGreenAuditForm (freedmanGreenAuditRepresentative 1)
      (freedmanGreenAuditRepresentative 1) = -3 := by
  norm_num [freedmanGreenAuditForm, freedmanGreenAuditPositiveFeature,
    freedmanGreenAuditNegativeFeature, freedmanGreenAuditRepresentative]

theorem freedmanGreenAudit_unit_form_neg :
    freedmanGreenAuditForm (freedmanGreenAuditRepresentative 1)
      (freedmanGreenAuditRepresentative 1) < 0 := by
  rw [freedmanGreenAudit_unit_form]
  norm_num

/-- Exact bundled endpoint: the source-listed premises hold in a model with a nontrivial trace
kernel, while the compressed map expands and the signed form is negative. -/
theorem freedmanGreenLift_listedPremises_do_not_force_contraction :
    (∀ x, freedmanGreenAuditTrace (freedmanGreenAuditRepresentative x) = x) ∧
    (∃ h : FreedmanGreenAuditSpace, h ≠ 0 ∧ freedmanGreenAuditTrace h = 0) ∧
    (∀ x h, freedmanGreenAuditTrace h = 0 →
      freedmanGreenAuditForm (freedmanGreenAuditRepresentative x) h = 0) ∧
    (∀ t, |freedmanGreenAuditMultiplier t| ≤ |t|) ∧
    (∀ x, freedmanGreenAuditNegativeFeature (freedmanGreenAuditRepresentative x) =
      freedmanGreenAuditCompression
        (freedmanGreenAuditMultiplier
          (freedmanGreenAuditLift
            (freedmanGreenAuditPositiveFeature (freedmanGreenAuditRepresentative x))))) ∧
    (¬ ∀ x,
      |freedmanGreenAuditCompression
        (freedmanGreenAuditMultiplier
          (freedmanGreenAuditLift
            (freedmanGreenAuditPositiveFeature (freedmanGreenAuditRepresentative x))))| ≤
        |freedmanGreenAuditPositiveFeature (freedmanGreenAuditRepresentative x)|) ∧
    freedmanGreenAuditForm (freedmanGreenAuditRepresentative 1)
      (freedmanGreenAuditRepresentative 1) < 0 := by
  exact ⟨freedmanGreenAudit_trace_representative,
    freedmanGreenAudit_trace_has_nontrivial_kernel,
    freedmanGreenAudit_eulerLagrange_on_traceKernel,
    freedmanGreenAudit_multiplier_contraction,
    freedmanGreenAudit_compressed_factorization,
    not_freedmanGreenAudit_compressed_contraction,
    freedmanGreenAudit_unit_form_neg⟩

/-- A repaired sufficient condition: norm control is required for every surrounding map, not only
for the middle multiplier. -/
theorem contraction_comp_three
    {C K E : ℝ → ℝ}
    (hC : ∀ t, |C t| ≤ |t|)
    (hK : ∀ t, |K t| ≤ |t|)
    (hE : ∀ t, |E t| ≤ |t|) :
    ∀ t, |C (K (E t))| ≤ |t| := by
  intro t
  exact (hC (K (E t))).trans ((hK (E t)).trans (hE t))

end LeanLab.Riemann
