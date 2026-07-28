import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Berry--Keating half-line mode audit

This module checks the formal Berry--Keating generalized eigenmode and its failure to belong to
the half-line `L^2` space. It does not construct an unbounded operator or prove a spectral theorem.
-/

open MeasureTheory Set

namespace LeanLab.Riemann

noncomputable section

/-- The exponent of the unit-normalized Berry--Keating generalized mode at energy `E`. -/
def berryKeatingExponent (E : ℝ) : ℂ :=
  -(1 / 2 : ℂ) + Complex.I * E

/-- The standard generalized eigenmode of the Berry--Keating differential expression. -/
def berryKeatingMode (E x : ℝ) : ℂ :=
  (x : ℂ) ^ berryKeatingExponent E

/-- The Berry--Keating differential expression with `hbar=1`. -/
def berryKeatingFormal (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  -Complex.I * ((x : ℂ) * deriv f x + f x / 2)

@[simp]
theorem berryKeatingExponent_re (E : ℝ) :
    (berryKeatingExponent E).re = -(1 / 2 : ℝ) := by
  simp [berryKeatingExponent]

theorem berryKeatingExponent_ne_zero (E : ℝ) :
    berryKeatingExponent E ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num at hre

theorem deriv_berryKeatingMode {E x : ℝ} (hx : 0 < x) :
    deriv (berryKeatingMode E) x =
      berryKeatingExponent E * (x : ℂ) ^ (berryKeatingExponent E - 1) :=
  Complex.deriv_ofReal_cpow_const hx.ne' (berryKeatingExponent_ne_zero E)

/-- The displayed half-line mode satisfies the formal Berry--Keating eigenvalue equation. -/
theorem berryKeatingFormal_mode_eq {E x : ℝ} (hx : 0 < x) :
    berryKeatingFormal (berryKeatingMode E) x = E * berryKeatingMode E x := by
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  rw [berryKeatingFormal, deriv_berryKeatingMode hx]
  simp only [berryKeatingMode]
  rw [Complex.cpow_sub _ _ hxC]
  simp only [Complex.cpow_one]
  simp [berryKeatingExponent]
  field_simp [hxC]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The generalized mode has the exact inverse-`x` squared norm on the positive half-line. -/
theorem norm_berryKeatingMode_sq {E x : ℝ} (hx : 0 < x) :
    ‖berryKeatingMode E x‖ ^ 2 = x⁻¹ := by
  rw [berryKeatingMode, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [berryKeatingExponent_re]
  rw [← Real.rpow_mul_natCast hx.le]
  norm_num [Real.rpow_neg_one]

/-- The standard generalized mode is not an `L^2` eigenvector on the positive half-line. -/
theorem not_memLp_two_berryKeatingMode (E : ℝ) :
    ¬ MemLp (berryKeatingMode E) 2 (volume.restrict (Ioi 0)) := by
  intro hmem
  have hsquare :
      IntegrableOn (fun x : ℝ => ‖berryKeatingMode E x‖ ^ 2) (Ioi 0) :=
    (memLp_two_iff_integrable_sq_norm hmem.1).mp hmem
  have hinv : IntegrableOn (fun x : ℝ => x⁻¹) (Ioi 0) :=
    hsquare.congr_fun (fun x hx => norm_berryKeatingMode_sq hx) measurableSet_Ioi
  exact not_integrableOn_Ioi_inv hinv

/-- Aggregate audit of the naive Berry--Keating half-line generalized eigenmode. -/
theorem berryKeatingHalfLine_endpoint (E : ℝ) :
    (∀ x : ℝ, 0 < x →
      berryKeatingFormal (berryKeatingMode E) x = E * berryKeatingMode E x) ∧
    (∀ x : ℝ, 0 < x → ‖berryKeatingMode E x‖ ^ 2 = x⁻¹) ∧
    ¬ MemLp (berryKeatingMode E) 2 (volume.restrict (Ioi 0)) := by
  exact ⟨fun _ hx => berryKeatingFormal_mode_eq hx,
    fun _ hx => norm_berryKeatingMode_sq hx,
    not_memLp_two_berryKeatingMode E⟩

end

end LeanLab.Riemann
