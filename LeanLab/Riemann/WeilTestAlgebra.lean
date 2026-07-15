import Mathlib.Analysis.MellinTransform

set_option linter.style.header false

/-!
# Weil's multiplicative involution

This file formalizes the test-function involution and its Mellin covariance from Lagarias,
Appendix A, formulas (A.1)-(A.2).  It is test-algebra infrastructure for the Weil explicit-formula
route; it does not state the explicit formula or a positivity result.
-/

noncomputable section

open Complex MeasureTheory Set
open scoped ComplexConjugate

namespace LeanLab.Riemann

/-- Weil's multiplicative involution `f_tilde(x) = x^(-1) f(x^(-1))`. -/
def weilInvolution (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (-1 : ℂ) * f x⁻¹

/-- The multiplicative involution squares to the identity on the positive half-line. -/
theorem weilInvolution_involution_of_pos
    (f : ℝ → ℂ) {x : ℝ} (hx : 0 < x) :
    weilInvolution (weilInvolution f) x = f x := by
  simp [weilInvolution, cpow_neg_one, hx.ne']

/-- The exclusion of zero is necessary in the pointwise involution theorem. -/
theorem weilInvolution_involution_not_at_zero :
    weilInvolution (weilInvolution (fun _ : ℝ => (1 : ℂ))) 0 ≠ 1 := by
  norm_num [weilInvolution]

/-- Mellin convergence is preserved exactly under Weil's involution, with parameter `s` sent to
`1-s`.  This is separate from the transform-value identity because the Bochner integral assigns
zero to nonintegrable functions. -/
theorem mellinConvergent_weilInvolution_iff (f : ℝ → ℂ) (s : ℂ) :
    MellinConvergent (weilInvolution f) s ↔ MellinConvergent f (1 - s) := by
  change MellinConvergent
      (fun x : ℝ => (x : ℂ) ^ (-1 : ℂ) • f x⁻¹) s ↔ _
  rw [MellinConvergent.cpow_smul]
  have h := MellinConvergent.comp_rpow (f := f) (s := s + -1)
    (a := (-1 : ℝ)) (by norm_num)
  have h' : MellinConvergent (fun x : ℝ => f x⁻¹) (s + -1) ↔
      MellinConvergent f ((s + -1) / ((-1 : ℝ) : ℂ)) := by
    simpa only [Real.rpow_neg_one] using h
  rw [h']
  have heq : (s + -1) / (((-1 : ℝ) : ℂ)) = 1 - s := by
    norm_num
    ring
  rw [heq]

/-- Lagarias's formula (A.2): multiplicative inversion sends `s` to `1-s` under Mellin
transform. -/
theorem mellin_weilInvolution (f : ℝ → ℂ) (s : ℂ) :
    mellin (weilInvolution f) s = mellin f (1 - s) := by
  change mellin (fun x : ℝ => (x : ℂ) ^ (-1 : ℂ) • f x⁻¹) s = _
  rw [mellin_cpow_smul, mellin_comp_inv]
  congr 1
  ring

/-- The involution exchanges the Mellin endpoint at `0` with the endpoint at `1`. -/
theorem mellin_weilInvolution_zero (f : ℝ → ℂ) :
    mellin (weilInvolution f) 0 = mellin f 1 := by
  simpa using mellin_weilInvolution f 0

/-- The involution exchanges the Mellin endpoint at `1` with the endpoint at `0`. -/
theorem mellin_weilInvolution_one (f : ℝ → ℂ) :
    mellin (weilInvolution f) 1 = mellin f 0 := by
  simpa using mellin_weilInvolution f 1

/-- Complex conjugation of a function conjugates the Mellin parameter and value. -/
theorem mellin_conj (f : ℝ → ℂ) (s : ℂ) :
    mellin (fun x : ℝ => conj (f x)) s = conj (mellin f (conj s)) := by
  rw [mellin, mellin, ← integral_conj]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  change (x : ℂ) ^ (s - 1) * conj (f x) =
    conj ((x : ℂ) ^ (conj s - 1) * f x)
  rw [map_mul]
  congr 1
  have harg : (x : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx.le]
    exact ne_of_lt Real.pi_pos
  simpa using Complex.conj_cpow (x : ℂ) (s - 1) harg

/-- Complex conjugation preserves Mellin convergence after conjugating the parameter. -/
theorem mellinConvergent_conj_iff (f : ℝ → ℂ) (s : ℂ) :
    MellinConvergent (fun x : ℝ => conj (f x)) s ↔
      MellinConvergent f (conj s) := by
  rw [MellinConvergent, MellinConvergent]
  change IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) * conj (f x)) (Ioi 0) ↔
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (conj s - 1) * f x) (Ioi 0)
  have hEq : Set.EqOn
      (fun x : ℝ => (x : ℂ) ^ (s - 1) * conj (f x))
      (fun x : ℝ => conj ((x : ℂ) ^ (conj s - 1) * f x)) (Ioi 0) := by
    intro x hx
    change (x : ℂ) ^ (s - 1) * conj (f x) =
      conj ((x : ℂ) ^ (conj s - 1) * f x)
    rw [map_mul]
    congr 1
    have harg : (x : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hx.le]
      exact ne_of_lt Real.pi_pos
    simpa using Complex.conj_cpow (x : ℂ) (s - 1) harg
  rw [integrableOn_congr_fun hEq measurableSet_Ioi]
  change Integrable
      (fun x : ℝ => conj ((x : ℂ) ^ (conj s - 1) * f x))
        (volume.restrict (Ioi 0)) ↔
    Integrable (fun x : ℝ => (x : ℂ) ^ (conj s - 1) * f x)
      (volume.restrict (Ioi 0))
  exact Complex.conjLIE.integrable_comp_iff

/-- The conjugate multiplicative involution used in Weil's covariance form. -/
def weilStar (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  conj (weilInvolution f x)

/-- The conjugate involution preserves Mellin convergence with the covariance parameter
`1-conj(s)`. -/
theorem mellinConvergent_weilStar_iff (f : ℝ → ℂ) (s : ℂ) :
    MellinConvergent (weilStar f) s ↔ MellinConvergent f (1 - conj s) := by
  change MellinConvergent (fun x : ℝ => conj (weilInvolution f x)) s ↔ _
  rw [mellinConvergent_conj_iff, mellinConvergent_weilInvolution_iff]

/-- Mellin covariance of the conjugate multiplicative involution. -/
theorem mellin_weilStar (f : ℝ → ℂ) (s : ℂ) :
    mellin (weilStar f) s = conj (mellin f (1 - conj s)) := by
  change mellin (fun x : ℝ => conj (weilInvolution f x)) s = _
  rw [mellin_conj, mellin_weilInvolution]

/-- On the critical line, the conjugate involution becomes pointwise conjugation on the Mellin
side. -/
theorem mellin_weilStar_criticalLine (f : ℝ → ℂ) (t : ℝ) :
    mellin (weilStar f) (1 / 2 + (t : ℂ) * I) =
      conj (mellin f (1 / 2 + (t : ℂ) * I)) := by
  rw [mellin_weilStar]
  congr 2
  apply Complex.ext
  · norm_num
  · norm_num

end LeanLab.Riemann
