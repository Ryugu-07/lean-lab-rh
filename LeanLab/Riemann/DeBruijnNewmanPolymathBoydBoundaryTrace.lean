import LeanLab.Riemann.DeBruijnNewmanPolymathBoydBoundaryDispersion

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Boundary trace for Boyd's scaled-Gamma projection

This module separates the integrable imaginary-axis truncation from the offset-line discrepancy
in the inner-boundary limit left by the finite Cauchy rectangles.
-/

namespace LeanLab.Riemann

open Complex MeasureTheory Real Set
open scoped Interval Real Topology

noncomputable section

/-- The source boundary-jump projection with both positive rays truncated at height `T`. -/
def deBruijnNewmanPolymathBoydTruncatedBoundaryJumpProjection
    (z : ℂ) (T : ℝ) : ℂ :=
  ((∫ s : ℝ in 0..T,
      deBruijnNewmanPolymathBoydBoundaryJumpMinusIntegrand z s) -
    (∫ s : ℝ in 0..T,
      deBruijnNewmanPolymathBoydBoundaryJumpPlusIntegrand z s)) /
    (2 * Real.pi * Complex.I * z ^ 2)

/-- The canonical rectangle heights exhaust the positive real axis. -/
theorem deBruijnNewmanPolymathBoydBoundaryHeight_tendsto_atTop
    (z : ℂ) :
    Filter.Tendsto (deBruijnNewmanPolymathBoydBoundaryHeight z)
      Filter.atTop Filter.atTop := by
  rw [show deBruijnNewmanPolymathBoydBoundaryHeight z =
      fun n : ℕ => (n : ℝ) + (|z.im| + 1) by
    funext n
    rw [deBruijnNewmanPolymathBoydBoundaryHeight]
    ring]
  exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds

/-- The truncated source jump rays converge to the complete Boyd boundary projection. -/
theorem deBruijnNewmanPolymathBoydTruncatedBoundaryJumpProjection_tendsto
    {z : ℂ} (hz : 0 < z.re) :
    Filter.Tendsto
      (fun n : ℕ => deBruijnNewmanPolymathBoydTruncatedBoundaryJumpProjection z
        (deBruijnNewmanPolymathBoydBoundaryHeight z n))
      Filter.atTop
      (𝓝 (deBruijnNewmanPolymathBoydBoundaryJumpProjection z)) := by
  have hheight := deBruijnNewmanPolymathBoydBoundaryHeight_tendsto_atTop z
  have hint := deBruijnNewmanPolymathBoydBoundaryJump_integrableOn hz
  have hminus := intervalIntegral_tendsto_integral_Ioi 0 hint.2 hheight
  have hplus := intervalIntegral_tendsto_integral_Ioi 0 hint.1 hheight
  have hdiff := hminus.sub hplus
  simpa [deBruijnNewmanPolymathBoydTruncatedBoundaryJumpProjection,
    deBruijnNewmanPolymathBoydBoundaryJumpProjection] using
      hdiff.div_const (2 * Real.pi * Complex.I * z ^ 2)

/-- The two offset inner lines combined before taking their interval integral. -/
def deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand
    (z : ℂ) (epsilon y : ℝ) : ℂ :=
  Complex.I *
    (deBruijnNewmanPolymathBoydR2CauchyWeight
        ((epsilon : ℂ) + (y : ℂ) * Complex.I) /
          ((epsilon : ℂ) + (y : ℂ) * Complex.I - z) -
      deBruijnNewmanPolymathBoydInverseR2CauchyWeight
        (-(epsilon : ℂ) + (y : ℂ) * Complex.I) /
          (-(epsilon : ℂ) + (y : ℂ) * Complex.I - z))

theorem deBruijnNewmanPolymathBoydR2_shiftedLine_intervalIntegrable
    {z : ℂ} {epsilon T : ℝ} (hepsilon : 0 < epsilon)
    (hepsilonz : epsilon < z.re) :
    IntervalIntegrable
      (fun y : ℝ => deBruijnNewmanPolymathBoydR2CauchyWeight
          ((epsilon : ℂ) + (y : ℂ) * Complex.I) /
        ((epsilon : ℂ) + (y : ℂ) * Complex.I - z)) volume (-T) T := by
  apply ContinuousOn.intervalIntegrable
  intro y _
  let w : ℂ := (epsilon : ℂ) + (y : ℂ) * Complex.I
  have hw : w ∈ {q : ℂ | 0 < q.re} := by
    change 0 < w.re
    simpa [w] using hepsilon
  have hweight : DifferentiableAt ℂ deBruijnNewmanPolymathBoydR2CauchyWeight w :=
    (deBruijnNewmanPolymathBoydR2CauchyWeight_differentiableOn_rightHalfPlane w hw).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw)
  have hline : ContinuousAt
      (fun t : ℝ => (epsilon : ℂ) + (t : ℂ) * Complex.I) y := by fun_prop
  have hnum : ContinuousAt
      (fun t : ℝ => deBruijnNewmanPolymathBoydR2CauchyWeight
        ((epsilon : ℂ) + (t : ℂ) * Complex.I)) y :=
    hweight.continuousAt.comp_of_eq hline rfl
  have hden : ContinuousAt
      (fun t : ℝ => (epsilon : ℂ) + (t : ℂ) * Complex.I - z) y := by fun_prop
  have hwz : w - z ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    have hre := congrArg Complex.re h
    simp [w] at hre
    linarith
  exact (hnum.div hden hwz).continuousWithinAt

theorem deBruijnNewmanPolymathBoydInverseR2_shiftedLine_intervalIntegrable
    {z : ℂ} {epsilon T : ℝ} (hz : 0 < z.re) (hepsilon : 0 < epsilon) :
    IntervalIntegrable
      (fun y : ℝ => deBruijnNewmanPolymathBoydInverseR2CauchyWeight
          (-(epsilon : ℂ) + (y : ℂ) * Complex.I) /
        (-(epsilon : ℂ) + (y : ℂ) * Complex.I - z)) volume (-T) T := by
  apply ContinuousOn.intervalIntegrable
  intro y _
  let w : ℂ := -(epsilon : ℂ) + (y : ℂ) * Complex.I
  have hw : w ∈ {q : ℂ | q.re < 0} := by
    change w.re < 0
    simpa [w] using neg_neg_of_pos hepsilon
  have hweight : DifferentiableAt ℂ
      deBruijnNewmanPolymathBoydInverseR2CauchyWeight w :=
    (deBruijnNewmanPolymathBoydInverseR2CauchyWeight_differentiableOn_leftHalfPlane w hw).differentiableAt
      ((isOpen_lt Complex.continuous_re continuous_const).mem_nhds hw)
  have hline : ContinuousAt
      (fun t : ℝ => -(epsilon : ℂ) + (t : ℂ) * Complex.I) y := by fun_prop
  have hnum : ContinuousAt
      (fun t : ℝ => deBruijnNewmanPolymathBoydInverseR2CauchyWeight
        (-(epsilon : ℂ) + (t : ℂ) * Complex.I)) y :=
    hweight.continuousAt.comp_of_eq hline rfl
  have hden : ContinuousAt
      (fun t : ℝ => -(epsilon : ℂ) + (t : ℂ) * Complex.I - z) y := by fun_prop
  have hwz : w - z ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    have hre := congrArg Complex.re h
    simp [w] at hre
    linarith
  exact (hnum.div hden hwz).continuousWithinAt

/-- The Loop 27 finite projection is exactly one paired offset-line interval integral. -/
theorem deBruijnNewmanPolymathBoydFiniteBoundaryProjection_eq_shiftedBoundaryPairIntegral
    {z : ℂ} {epsilon T : ℝ} (hz : 0 < z.re) (hepsilon : 0 < epsilon)
    (hepsilonz : epsilon < z.re) :
    deBruijnNewmanPolymathBoydFiniteBoundaryProjection z epsilon T =
      -(1 / (2 * Real.pi * Complex.I * z)) *
        (∫ y : ℝ in -T..T,
          deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand z epsilon y) := by
  have hright := deBruijnNewmanPolymathBoydR2_shiftedLine_intervalIntegrable
    (T := T) hepsilon hepsilonz
  have hleft := deBruijnNewmanPolymathBoydInverseR2_shiftedLine_intervalIntegrable
    (T := T) hz hepsilon
  rw [deBruijnNewmanPolymathBoydFiniteBoundaryProjection]
  simp only [deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hright hleft]
  ring

theorem deBruijnNewmanPolymathGammaStirlingR2_differentiableAt_of_im_ne_zero
    {w : ℂ} (hw : w.im ≠ 0) :
    DifferentiableAt ℂ deBruijnNewmanPolymathGammaStirlingR2 w := by
  have hw0 : w ≠ 0 := by
    intro h
    exact hw (by simp [h])
  have hscaled : DifferentiableAt ℂ deBruijnNewmanPolymathScaledGamma w := by
    apply deBruijnNewmanPolymathScaledGamma_differentiableAt (Or.inr hw)
    intro m hm
    have him := congrArg Complex.im hm
    exact hw (by simpa using him)
  have hfrac : DifferentiableAt ℂ (fun q : ℂ => 1 / (12 * q)) w :=
    (differentiableAt_const (c := (1 : ℂ))).div
      ((differentiableAt_const (c := (12 : ℂ))).mul differentiableAt_id)
      (mul_ne_zero (by norm_num) hw0)
  unfold deBruijnNewmanPolymathGammaStirlingR2
  exact (hscaled.sub (differentiableAt_const (c := (1 : ℂ)))).sub hfrac

theorem deBruijnNewmanPolymathScaledGammaInverseR2_differentiableAt_of_im_ne_zero
    {w : ℂ} (hw : w.im ≠ 0) :
    DifferentiableAt ℂ deBruijnNewmanPolymathScaledGammaInverseR2 w := by
  have hw0 : w ≠ 0 := by
    intro h
    exact hw (by simp [h])
  have hscaled : DifferentiableAt ℂ deBruijnNewmanPolymathScaledGamma w := by
    apply deBruijnNewmanPolymathScaledGamma_differentiableAt (Or.inr hw)
    intro m hm
    have him := congrArg Complex.im hm
    exact hw (by simpa using him)
  have hscaled0 : deBruijnNewmanPolymathScaledGamma w ≠ 0 :=
    deBruijnNewmanPolymathScaledGamma_ne_zero hw
  have hinv : DifferentiableAt ℂ
      (fun q : ℂ => 1 / deBruijnNewmanPolymathScaledGamma q) w :=
    (differentiableAt_const (c := (1 : ℂ))).div hscaled hscaled0
  have hfrac : DifferentiableAt ℂ (fun q : ℂ => 1 / (12 * q)) w :=
    (differentiableAt_const (c := (1 : ℂ))).div
      ((differentiableAt_const (c := (12 : ℂ))).mul differentiableAt_id)
      (mul_ne_zero (by norm_num) hw0)
  unfold deBruijnNewmanPolymathScaledGammaInverseR2
  exact (hinv.sub (differentiableAt_const (c := (1 : ℂ)))).add hfrac

theorem deBruijnNewmanPolymathBoydR2CauchyWeight_continuousAt_of_im_ne_zero
    {w : ℂ} (hw : w.im ≠ 0) :
    ContinuousAt deBruijnNewmanPolymathBoydR2CauchyWeight w := by
  exact (differentiableAt_id.mul
    (deBruijnNewmanPolymathGammaStirlingR2_differentiableAt_of_im_ne_zero hw)).continuousAt

theorem deBruijnNewmanPolymathBoydInverseR2CauchyWeight_continuousAt_of_im_ne_zero
    {w : ℂ} (hw : w.im ≠ 0) :
    ContinuousAt deBruijnNewmanPolymathBoydInverseR2CauchyWeight w := by
  have hneg : (-w).im ≠ 0 := by simpa using neg_ne_zero.mpr hw
  have hcomp : DifferentiableAt ℂ
      (fun q : ℂ => deBruijnNewmanPolymathScaledGammaInverseR2 (-q)) w :=
    (deBruijnNewmanPolymathScaledGammaInverseR2_differentiableAt_of_im_ne_zero hneg).comp
      w differentiableAt_id.neg
  exact (differentiableAt_id.mul hcomp).continuousAt

/-- Away from the origin, the paired offset-line kernel tends to the exact reflection jump. -/
theorem deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand_tendsto
    {z : ℂ} (hz : 0 < z.re) {y : ℝ} (hy : y ≠ 0) :
    Filter.Tendsto
      (fun epsilon : ℝ =>
        deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand z epsilon y)
      (𝓝 0)
      (𝓝 (Complex.I *
        (((y : ℂ) * Complex.I) *
          deBruijnNewmanPolymathScaledGammaBoundaryJump
            ((y : ℂ) * Complex.I) /
          ((y : ℂ) * Complex.I - z)))) := by
  let w : ℂ := (y : ℂ) * Complex.I
  have hwim : w.im ≠ 0 := by simpa [w] using hy
  have hwz : w - z ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    have hre := congrArg Complex.re h
    simp [w] at hre
    linarith
  have hplusPath : Filter.Tendsto
      (fun epsilon : ℝ => (epsilon : ℂ) + (y : ℂ) * Complex.I)
      (𝓝 0) (𝓝 w) := by
    have hzero : Filter.Tendsto (fun epsilon : ℝ => (epsilon : ℂ))
        (𝓝 0) (𝓝 (0 : ℂ)) := Complex.continuous_ofReal.continuousAt
    simpa [w] using hzero.add tendsto_const_nhds
  have hminusPath : Filter.Tendsto
      (fun epsilon : ℝ => -(epsilon : ℂ) + (y : ℂ) * Complex.I)
      (𝓝 0) (𝓝 w) := by
    have hzero : Filter.Tendsto (fun epsilon : ℝ => (epsilon : ℂ))
        (𝓝 0) (𝓝 (0 : ℂ)) := Complex.continuous_ofReal.continuousAt
    simpa [w] using hzero.neg.add tendsto_const_nhds
  have hright :=
    ((deBruijnNewmanPolymathBoydR2CauchyWeight_continuousAt_of_im_ne_zero hwim).tendsto.comp
      hplusPath).div (hplusPath.sub tendsto_const_nhds) hwz
  have hleft :=
    ((deBruijnNewmanPolymathBoydInverseR2CauchyWeight_continuousAt_of_im_ne_zero hwim).tendsto.comp
      hminusPath).div (hminusPath.sub tendsto_const_nhds) hwz
  have hI : Filter.Tendsto (fun _ : ℝ => Complex.I)
      (𝓝 0) (𝓝 Complex.I) := tendsto_const_nhds
  have hpair := hI.mul (hright.sub hleft)
  have hpoint : Complex.I *
      (deBruijnNewmanPolymathBoydR2CauchyWeight w / (w - z) -
        deBruijnNewmanPolymathBoydInverseR2CauchyWeight w / (w - z)) =
      Complex.I *
        (w * deBruijnNewmanPolymathScaledGammaBoundaryJump w / (w - z)) := by
    rw [deBruijnNewmanPolymathBoydR2CauchyWeight,
      deBruijnNewmanPolymathBoydInverseR2CauchyWeight,
      deBruijnNewmanPolymathScaledGammaBoundaryJump_eq_remainders
        (mul_ne_zero (Complex.ofReal_ne_zero.mpr hy) Complex.I_ne_zero)]
    ring
  rw [← hpoint]
  simpa [deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand, Function.comp_def] using hpair

/-- The exact error between the canonical offset projection and the matching jump truncation. -/
def deBruijnNewmanPolymathBoydBoundaryTraceDiscrepancy
    (z : ℂ) (n : ℕ) : ℂ :=
  deBruijnNewmanPolymathBoydFiniteBoundaryProjection z
      (deBruijnNewmanPolymathBoydBoundaryEpsilon z n)
      (deBruijnNewmanPolymathBoydBoundaryHeight z n) -
    deBruijnNewmanPolymathBoydTruncatedBoundaryJumpProjection z
      (deBruijnNewmanPolymathBoydBoundaryHeight z n)

/-- Since the source jump truncations already converge, the inner trace is exactly one error
limit. -/
theorem deBruijnNewmanPolymathBoydBoundaryTrace_tendsto_iff_discrepancy
    {z : ℂ} (hz : 0 < z.re) :
    Filter.Tendsto
        (fun n : ℕ => deBruijnNewmanPolymathBoydFiniteBoundaryProjection z
          (deBruijnNewmanPolymathBoydBoundaryEpsilon z n)
          (deBruijnNewmanPolymathBoydBoundaryHeight z n))
        Filter.atTop
        (𝓝 (deBruijnNewmanPolymathBoydBoundaryJumpProjection z)) ↔
      Filter.Tendsto
        (deBruijnNewmanPolymathBoydBoundaryTraceDiscrepancy z)
        Filter.atTop (𝓝 0) := by
  have htrunc := deBruijnNewmanPolymathBoydTruncatedBoundaryJumpProjection_tendsto hz
  constructor
  · intro hfinite
    change Filter.Tendsto
      (fun n : ℕ => deBruijnNewmanPolymathBoydFiniteBoundaryProjection z
          (deBruijnNewmanPolymathBoydBoundaryEpsilon z n)
          (deBruijnNewmanPolymathBoydBoundaryHeight z n) -
        deBruijnNewmanPolymathBoydTruncatedBoundaryJumpProjection z
          (deBruijnNewmanPolymathBoydBoundaryHeight z n))
      Filter.atTop (𝓝 0)
    simpa only [sub_self] using hfinite.sub htrunc
  · intro hdiff
    change Filter.Tendsto
      (fun n : ℕ => deBruijnNewmanPolymathBoydFiniteBoundaryProjection z
          (deBruijnNewmanPolymathBoydBoundaryEpsilon z n)
          (deBruijnNewmanPolymathBoydBoundaryHeight z n) -
        deBruijnNewmanPolymathBoydTruncatedBoundaryJumpProjection z
          (deBruijnNewmanPolymathBoydBoundaryHeight z n))
      Filter.atTop (𝓝 0) at hdiff
    have hadd := hdiff.add htrunc
    convert hadd using 1 <;> simp

/-- Auditable Loop 28 boundary-trace reduction, without assuming the remaining discrepancy
limit. -/
def deBruijnNewmanPolymathBoydBoundaryTraceCertificateStatement : Prop :=
  (∀ z : ℂ,
    Filter.Tendsto (deBruijnNewmanPolymathBoydBoundaryHeight z)
      Filter.atTop Filter.atTop) ∧
  (∀ z : ℂ, 0 < z.re →
    Filter.Tendsto
      (fun n : ℕ => deBruijnNewmanPolymathBoydTruncatedBoundaryJumpProjection z
        (deBruijnNewmanPolymathBoydBoundaryHeight z n))
      Filter.atTop (𝓝 (deBruijnNewmanPolymathBoydBoundaryJumpProjection z))) ∧
  (∀ (z : ℂ) (epsilon T : ℝ), 0 < z.re → 0 < epsilon → epsilon < z.re →
    deBruijnNewmanPolymathBoydFiniteBoundaryProjection z epsilon T =
      -(1 / (2 * Real.pi * Complex.I * z)) *
        (∫ y : ℝ in -T..T,
          deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand z epsilon y)) ∧
  (∀ (z : ℂ), 0 < z.re → ∀ y : ℝ, y ≠ 0 →
    Filter.Tendsto
      (fun epsilon : ℝ =>
        deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand z epsilon y)
      (𝓝 0)
      (𝓝 (Complex.I *
        (((y : ℂ) * Complex.I) *
          deBruijnNewmanPolymathScaledGammaBoundaryJump
            ((y : ℂ) * Complex.I) /
          ((y : ℂ) * Complex.I - z))))) ∧
  (∀ z : ℂ, 0 < z.re →
    (Filter.Tendsto
        (fun n : ℕ => deBruijnNewmanPolymathBoydFiniteBoundaryProjection z
          (deBruijnNewmanPolymathBoydBoundaryEpsilon z n)
          (deBruijnNewmanPolymathBoydBoundaryHeight z n))
        Filter.atTop
        (𝓝 (deBruijnNewmanPolymathBoydBoundaryJumpProjection z)) ↔
      Filter.Tendsto
        (deBruijnNewmanPolymathBoydBoundaryTraceDiscrepancy z)
        Filter.atTop (𝓝 0)))

/-- The complete unconditional Loop 28 reduction certificate. -/
theorem deBruijnNewmanPolymathBoydBoundaryTraceCertificate :
    deBruijnNewmanPolymathBoydBoundaryTraceCertificateStatement := by
  refine ⟨deBruijnNewmanPolymathBoydBoundaryHeight_tendsto_atTop, ?_, ?_, ?_, ?_⟩
  · exact fun _ hz =>
      deBruijnNewmanPolymathBoydTruncatedBoundaryJumpProjection_tendsto hz
  · exact fun _ _ _ hz hepsilon hepsilonz =>
      deBruijnNewmanPolymathBoydFiniteBoundaryProjection_eq_shiftedBoundaryPairIntegral
        hz hepsilon hepsilonz
  · exact fun _ hz _ hy =>
      deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand_tendsto hz hy
  · exact fun _ hz =>
      deBruijnNewmanPolymathBoydBoundaryTrace_tendsto_iff_discrepancy hz

end

end LeanLab.Riemann
