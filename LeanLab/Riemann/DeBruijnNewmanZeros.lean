import LeanLab.Riemann.DeBruijnNewman
import LeanLab.Riemann.LiZeroDivisor

set_option linter.style.header false

/-!
# Zero coordinates for the de Bruijn-Newman family

This file aligns zeros of the source-normalized transform at time zero with nontrivial zeta zeros.
It defines no Newman threshold and proves no heat-flow preservation theorem.
-/

open Complex Set

namespace LeanLab.Riemann

noncomputable section

/-- Every complex zero of the source-normalized transform at time `t` is real. -/
def deBruijnNewmanAllZerosReal (t : ℝ) : Prop :=
  ∀ z : ℂ, deBruijnNewmanH t z = 0 → z.im = 0

/-- The inverse of the source coordinate `s = (1 + i*z) / 2`. -/
def deBruijnNewmanZeroCoordinate (s : ℂ) : ℂ :=
  -I * (2 * s - 1)

@[simp]
theorem deBruijnNewmanZeroCoordinate_re (s : ℂ) :
    (deBruijnNewmanZeroCoordinate s).re = 2 * s.im := by
  simp [deBruijnNewmanZeroCoordinate]

@[simp]
theorem deBruijnNewmanZeroCoordinate_im (s : ℂ) :
    (deBruijnNewmanZeroCoordinate s).im = 1 - 2 * s.re := by
  simp [deBruijnNewmanZeroCoordinate]

@[simp]
theorem deBruijnNewmanZeroCoordinate_source (s : ℂ) :
    (1 + I * deBruijnNewmanZeroCoordinate s) / 2 = s := by
  apply Complex.ext <;> simp [deBruijnNewmanZeroCoordinate]

@[simp]
theorem deBruijnNewmanZeroCoordinate_im_eq_zero_iff (s : ℂ) :
    (deBruijnNewmanZeroCoordinate s).im = 0 ↔ s.re = 1 / 2 := by
  rw [deBruijnNewmanZeroCoordinate_im]
  constructor <;> intro h <;> linarith

@[simp]
theorem deBruijnNewmanSourceCoordinate_re_eq_half_iff (z : ℂ) :
    (((1 + I * z) / 2 : ℂ).re) = 1 / 2 ↔ z.im = 0 := by
  simp only [div_ofNat_re, add_re, one_re, mul_re, I_re, zero_mul, I_im, one_mul,
    zero_sub, one_div]
  constructor <;> intro h <;> linarith

/-- The exact time-zero source coordinate identifies transform zeros with nontrivial zeta zeros. -/
theorem deBruijnNewmanH_zero_iff_isNontrivialZero (z : ℂ) :
    deBruijnNewmanH 0 z = 0 ↔
      IsNontrivialZero ((1 + I * z) / 2) := by
  rw [deBruijnNewmanH_zero_eq_riemannXi]
  constructor
  · intro h
    have hxi : riemannXi ((1 + I * z) / 2) = 0 := by
      rcases mul_eq_zero.mp h with hfactor | hzero
      · norm_num at hfactor
      · exact hzero
    exact (isNontrivialZero_iff_riemannXi_eq_zero _).2 hxi
  · intro h
    rw [(isNontrivialZero_iff_riemannXi_eq_zero _).1 h]
    simp

/-- The inverse source coordinate maps exactly the nontrivial zeta zeros to time-zero zeros. -/
theorem deBruijnNewmanH_zeroCoordinate_eq_zero_iff (s : ℂ) :
    deBruijnNewmanH 0 (deBruijnNewmanZeroCoordinate s) = 0 ↔
      IsNontrivialZero s := by
  rw [deBruijnNewmanH_zero_iff_isNontrivialZero,
    deBruijnNewmanZeroCoordinate_source]

private theorem dbn_isNontrivialZero_one_sub {s : ℂ} (hs : IsNontrivialZero s) :
    IsNontrivialZero (1 - s) := by
  rw [isNontrivialZero_iff_riemannXi_eq_zero, riemannXi_one_sub]
  exact (isNontrivialZero_iff_riemannXi_eq_zero s).1 hs

private theorem dbn_nontrivialZero_re_pos {s : ℂ} (hs : IsNontrivialZero s) :
    0 < s.re := by
  have hreflect := nontrivial_zero_re_lt_one (dbn_isNontrivialZero_one_sub hs)
  simp only [Complex.sub_re, Complex.one_re] at hreflect
  linarith

/-- Every time-zero zero lies in the strict strip corresponding to the critical strip. -/
theorem deBruijnNewmanH_zero_im_mem_Ioo {z : ℂ}
    (hz : deBruijnNewmanH 0 z = 0) :
    z.im ∈ Set.Ioo (-1) 1 := by
  have hs : IsNontrivialZero ((1 + I * z) / 2) :=
    (deBruijnNewmanH_zero_iff_isNontrivialZero z).1 hz
  have hsPos := dbn_nontrivialZero_re_pos hs
  have hsLt := nontrivial_zero_re_lt_one hs
  have hsRe : (((1 + I * z) / 2 : ℂ).re) = (1 - z.im) / 2 := by
    simp
    ring
  rw [hsRe] at hsPos hsLt
  constructor <;> linarith

/-- The upper critical-strip boundary is not a time-zero zero. -/
theorem deBruijnNewmanH_zero_I_ne_zero :
    deBruijnNewmanH 0 I ≠ 0 := by
  intro hz
  have hstrip := deBruijnNewmanH_zero_im_mem_Ioo hz
  norm_num at hstrip

/-- The lower critical-strip boundary is not a time-zero zero. -/
theorem deBruijnNewmanH_zero_neg_I_ne_zero :
    deBruijnNewmanH 0 (-I) ≠ 0 := by
  intro hz
  have hstrip := deBruijnNewmanH_zero_im_mem_Ioo hz
  norm_num at hstrip

/-- The project Riemann hypothesis is exactly the assertion that all time-zero transform zeros
are real. -/
theorem riemannHypothesis_iff_deBruijnNewmanAllZerosReal_zero :
    RiemannHypothesis ↔ deBruijnNewmanAllZerosReal 0 := by
  rw [riemannHypothesis_iff_nontrivial_zeros_on_line]
  constructor
  · intro hRH z hz
    have hs : IsNontrivialZero ((1 + I * z) / 2) :=
      (deBruijnNewmanH_zero_iff_isNontrivialZero z).1 hz
    have hline := hRH _ hs
    rw [OnCriticalLine] at hline
    exact (deBruijnNewmanSourceCoordinate_re_eq_half_iff z).1 hline
  · intro hAll s hs
    have hz : deBruijnNewmanH 0 (deBruijnNewmanZeroCoordinate s) = 0 :=
      (deBruijnNewmanH_zeroCoordinate_eq_zero_iff s).2 hs
    have hreal := hAll _ hz
    rw [OnCriticalLine]
    exact (deBruijnNewmanZeroCoordinate_im_eq_zero_iff s).1 hreal

/-- Aggregate witness for the complete time-zero zero-coordinate framework. -/
theorem deBruijnNewman_zeroCoordinate_framework :
    (∀ z : ℂ, deBruijnNewmanH 0 z = 0 ↔
      IsNontrivialZero ((1 + I * z) / 2)) ∧
    (∀ s : ℂ, deBruijnNewmanH 0 (deBruijnNewmanZeroCoordinate s) = 0 ↔
      IsNontrivialZero s) ∧
    (∀ z : ℂ, deBruijnNewmanH 0 z = 0 → z.im ∈ Set.Ioo (-1) 1) ∧
    (RiemannHypothesis ↔ deBruijnNewmanAllZerosReal 0) := by
  exact ⟨deBruijnNewmanH_zero_iff_isNontrivialZero,
    deBruijnNewmanH_zeroCoordinate_eq_zero_iff,
    fun _ hz ↦ deBruijnNewmanH_zero_im_mem_Ioo hz,
    riemannHypothesis_iff_deBruijnNewmanAllZerosReal_zero⟩

end

end LeanLab.Riemann
