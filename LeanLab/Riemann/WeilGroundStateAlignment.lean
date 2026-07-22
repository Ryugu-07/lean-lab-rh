import LeanLab.Riemann.WeilCompactPositivityCriterion

set_option linter.style.header false

/-!
# Weighted logarithmic coordinates for the finite-prime Weil ground-state route

This file isolates the exact coordinate change between the unweighted additive convolution used
for source functions on an interval of length `L` and the weighted compact-Laplace involution used
by the project. It does not define the finite-prime Weil operator or assert any spectral property.
-/

noncomputable section

open Complex MeasureTheory

namespace LeanLab.Riemann

/-- Center and apply the Mellin half-density to a source function on an interval of length `L`. -/
def weilGroundStateLogRoot (L : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  Complex.exp (-(x : ℂ) / 2) * f (x + L / 2)

/-- The centered positive-sign Fourier transform used to compare with xi-zero ordinates. -/
def weilGroundStateCenteredFourier (L : ℝ) (f : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ x : ℝ, Complex.exp (I * z * (x : ℂ)) * f (x + L / 2)

/-- The negative-sign Fourier transform used in the finite-prime Weil sources. -/
def weilGroundStateSourceFourier (L : ℝ) (f : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ x : ℝ, Complex.exp (-I * z * (x : ℂ)) * f (x + L / 2)

theorem weilGroundStateSourceFourier_eq_centered
    (L : ℝ) (f : ℝ → ℂ) (z : ℂ) :
    weilGroundStateSourceFourier L f z =
      weilGroundStateCenteredFourier L f (-z) := by
  unfold weilGroundStateSourceFourier weilGroundStateCenteredFourier
  apply integral_congr_ae
  filter_upwards with x
  congr 2
  ring

/-- The ordinary source autocorrelation after centering the interval at the origin. -/
def weilGroundStateCenteredAutocorrelation (L : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y : ℝ, f (y + L / 2) * (starRingEnd ℂ) (f (y - x + L / 2))

/-- The Mellin half-density conjugates the source star to the project's weighted involution. -/
theorem compactLaplaceConjInvolution_weilGroundStateLogRoot
    (L : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    compactLaplaceConjInvolution (weilGroundStateLogRoot L f) x =
      Complex.exp (-(x : ℂ) / 2) *
        (starRingEnd ℂ) (f (-x + L / 2)) := by
  unfold compactLaplaceConjInvolution weilGroundStateLogRoot
  simp only [map_mul]
  have harg : -(((-x : ℝ) : ℂ)) / 2 = (x : ℂ) / 2 := by
    push_cast
    ring
  have hhalf : (x : ℂ) / 2 = ((x / 2 : ℝ) : ℂ) := by
    push_cast
    rfl
  have hconj :
      (starRingEnd ℂ) (Complex.exp ((x : ℂ) / 2)) =
        Complex.exp ((x : ℂ) / 2) := by
    rw [hhalf, ← Complex.ofReal_exp, Complex.conj_ofReal]
  rw [harg, hconj]
  rw [Complex.ofReal_exp]
  have hnegcast : ((-x : ℝ) : ℂ) = -(x : ℂ) := by
    push_cast
    rfl
  rw [hnegcast]
  calc
    Complex.exp (-(x : ℂ)) *
        (Complex.exp ((x : ℂ) / 2) *
          (starRingEnd ℂ) (f (-x + L / 2))) =
      (Complex.exp (-(x : ℂ)) * Complex.exp ((x : ℂ) / 2)) *
        (starRingEnd ℂ) (f (-x + L / 2)) := by ring
    _ = Complex.exp (-(x : ℂ) / 2) *
        (starRingEnd ℂ) (f (-x + L / 2)) := by
      rw [← Complex.exp_add]
      congr 2
      ring

/-- In weighted logarithmic coordinates, project autocorrelation is the source correlation times
the Mellin half-density. -/
theorem compactLaplaceAutocorrelation_weilGroundStateLogRoot
    (L : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    compactLaplaceAutocorrelation (weilGroundStateLogRoot L f) x =
      Complex.exp (-(x : ℂ) / 2) *
        weilGroundStateCenteredAutocorrelation L f x := by
  unfold compactLaplaceAutocorrelation additiveConvolution MeasureTheory.convolution
    weilGroundStateCenteredAutocorrelation
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  rw [compactLaplaceConjInvolution_weilGroundStateLogRoot]
  unfold weilGroundStateLogRoot
  have hexp :
      Complex.exp (-(y : ℂ) / 2) *
          Complex.exp (-((x - y : ℝ) : ℂ) / 2) =
        Complex.exp (-(x : ℂ) / 2) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    (Complex.exp (-(y : ℂ) / 2) * f (y + L / 2)) *
        (Complex.exp (-((x - y : ℝ) : ℂ) / 2) *
          (starRingEnd ℂ) (f (-(x - y) + L / 2))) =
      (Complex.exp (-(y : ℂ) / 2) *
          Complex.exp (-((x - y : ℝ) : ℂ) / 2)) *
        (f (y + L / 2) *
          (starRingEnd ℂ) (f (y - x + L / 2))) := by ring
    _ = Complex.exp (-(x : ℂ) / 2) *
        (f (y + L / 2) *
          (starRingEnd ℂ) (f (y - x + L / 2))) := by rw [hexp]

/-- The project bilateral Laplace transform on the critical line is exactly the centered source
Fourier transform with the positive exponential convention. -/
theorem compactLaplaceTransform_weilGroundStateLogRoot_criticalLine
    (L : ℝ) (f : ℝ → ℂ) (z : ℂ) :
    compactLaplaceTransform (weilGroundStateLogRoot L f) (1 / 2 + I * z) =
      weilGroundStateCenteredFourier L f z := by
  unfold compactLaplaceTransform weilGroundStateLogRoot weilGroundStateCenteredFourier
  apply integral_congr_ae
  filter_upwards with x
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- With the source's negative Fourier convention, ordinate `z` maps to `s = 1/2 - i*z`. -/
theorem compactLaplaceTransform_weilGroundStateLogRoot_sourceCoordinate
    (L : ℝ) (f : ℝ → ℂ) (z : ℂ) :
    compactLaplaceTransform (weilGroundStateLogRoot L f) (1 / 2 - I * z) =
      weilGroundStateSourceFourier L f z := by
  rw [weilGroundStateSourceFourier_eq_centered]
  have h := compactLaplaceTransform_weilGroundStateLogRoot_criticalLine L f (-z)
  simpa only [mul_neg, sub_eq_add_neg] using h

/-- The project transform at `s = 0` is the source Fourier value at `z = i/2`. -/
theorem compactLaplaceTransform_weilGroundStateLogRoot_zero
    (L : ℝ) (f : ℝ → ℂ) :
    compactLaplaceTransform (weilGroundStateLogRoot L f) 0 =
      weilGroundStateCenteredFourier L f (I / 2) := by
  have h := compactLaplaceTransform_weilGroundStateLogRoot_criticalLine L f (I / 2)
  have hz : (1 / 2 : ℂ) + I * (I / 2) = 0 := by
    calc
      (1 / 2 : ℂ) + I * (I / 2) = 1 / 2 + (I * I) / 2 := by ring
      _ = 0 := by rw [Complex.I_mul_I]; norm_num
  rw [hz] at h
  exact h

/-- The project transform at `s = 1` is the source Fourier value at `z = -i/2`. -/
theorem compactLaplaceTransform_weilGroundStateLogRoot_one
    (L : ℝ) (f : ℝ → ℂ) :
    compactLaplaceTransform (weilGroundStateLogRoot L f) 1 =
      weilGroundStateCenteredFourier L f (-I / 2) := by
  have h := compactLaplaceTransform_weilGroundStateLogRoot_criticalLine L f (-I / 2)
  have hone : (1 / 2 : ℂ) + I * (-I / 2) = 1 := by
    calc
      (1 / 2 : ℂ) + I * (-I / 2) = 1 / 2 - (I * I) / 2 := by ring
      _ = 1 := by rw [Complex.I_mul_I]; norm_num
  rw [hone] at h
  exact h

/-- In the source Fourier convention, the project endpoint `s = 0` is the `-i/2` moment. -/
theorem compactLaplaceTransform_weilGroundStateLogRoot_zero_sourceMoment
    (L : ℝ) (f : ℝ → ℂ) :
    compactLaplaceTransform (weilGroundStateLogRoot L f) 0 =
      weilGroundStateSourceFourier L f (-I / 2) := by
  rw [weilGroundStateSourceFourier_eq_centered]
  simpa only [neg_div, neg_neg] using
    compactLaplaceTransform_weilGroundStateLogRoot_zero L f

/-- In the source Fourier convention, the project endpoint `s = 1` is the `i/2` moment. -/
theorem compactLaplaceTransform_weilGroundStateLogRoot_one_sourceMoment
    (L : ℝ) (f : ℝ → ℂ) :
    compactLaplaceTransform (weilGroundStateLogRoot L f) 1 =
      weilGroundStateSourceFourier L f (I / 2) := by
  rw [weilGroundStateSourceFourier_eq_centered]
  simpa only [neg_div] using
    compactLaplaceTransform_weilGroundStateLogRoot_one L f

end LeanLab.Riemann
