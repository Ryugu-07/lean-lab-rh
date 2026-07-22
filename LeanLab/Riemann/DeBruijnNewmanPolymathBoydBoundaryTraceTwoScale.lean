import LeanLab.Riemann.DeBruijnNewmanPolymathBoydBoundaryTrace

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Two-scale reduction for the Boyd boundary trace

This module removes every fixed compact annulus from the boundary-trace discrepancy and isolates
the remaining near-zero and shifted-tail residuals.
-/

namespace LeanLab.Riemann

open Complex MeasureTheory Real Set
open scoped Interval Real Topology

noncomputable section

/-- The exact imaginary-axis kernel approached by the paired offset lines. -/
def deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand
    (z : ℂ) (y : ℝ) : ℂ :=
  Complex.I *
    (((y : ℂ) * Complex.I) *
      deBruijnNewmanPolymathScaledGammaBoundaryJump ((y : ℂ) * Complex.I) /
      ((y : ℂ) * Complex.I - z))

/-- The offset-to-axis error before interval integration. -/
def deBruijnNewmanPolymathBoydBoundaryTraceErrorIntegrand
    (z : ℂ) (epsilon y : ℝ) : ℂ :=
  deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand z epsilon y -
    deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand z y

/-- A fixed compact annulus in the boundary coordinate. -/
def deBruijnNewmanPolymathBoydBoundaryMiddleSet
    (delta A : ℝ) : Set ℝ :=
  Icc (-A) (-delta) ∪ Icc delta A

theorem isCompact_deBruijnNewmanPolymathBoydBoundaryMiddleSet
    (delta A : ℝ) :
    IsCompact (deBruijnNewmanPolymathBoydBoundaryMiddleSet delta A) := by
  exact isCompact_Icc.union isCompact_Icc

theorem deBruijnNewmanPolymathBoydBoundaryMiddleSet_nonzero
    {delta A y : ℝ} (hdelta : 0 < delta)
    (hy : y ∈ deBruijnNewmanPolymathBoydBoundaryMiddleSet delta A) :
    y ≠ 0 := by
  rw [deBruijnNewmanPolymathBoydBoundaryMiddleSet] at hy
  rcases hy with hy | hy <;> intro hy0 <;> subst y <;>
    simp only [mem_Icc] at hy <;> linarith

/-- At zero offset, the paired remainder weights are exactly the reflection-jump kernel away from
the origin. -/
theorem deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand_zero
    (z : ℂ) {y : ℝ} (hy : y ≠ 0) :
    deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand z 0 y =
      deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand z y := by
  let w : ℂ := (y : ℂ) * Complex.I
  have hw0 : w ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hy) Complex.I_ne_zero
  rw [deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand,
    deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand,
    deBruijnNewmanPolymathBoydR2CauchyWeight,
    deBruijnNewmanPolymathBoydInverseR2CauchyWeight,
    deBruijnNewmanPolymathScaledGammaBoundaryJump_eq_remainders hw0]
  simp only [ofReal_zero, neg_zero, zero_add]
  ring

/-- Joint continuity of the paired offset kernel on a pole-free epsilon slab and a compact
boundary annulus. -/
theorem deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand_continuousOn_slab_middle
    {z : ℂ} {r delta A : ℝ} (hrz : r < z.re) (hdelta : 0 < delta) :
    ContinuousOn
      (fun p : ℝ × ℝ =>
        deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand z p.1 p.2)
      (Icc (-r) r ×ˢ deBruijnNewmanPolymathBoydBoundaryMiddleSet delta A) := by
  intro p hp
  have hy : p.2 ≠ 0 :=
    deBruijnNewmanPolymathBoydBoundaryMiddleSet_nonzero hdelta hp.2
  let wplus : ℂ := (p.1 : ℂ) + (p.2 : ℂ) * Complex.I
  let wminus : ℂ := -(p.1 : ℂ) + (p.2 : ℂ) * Complex.I
  have hwplusIm : wplus.im ≠ 0 := by simpa [wplus] using hy
  have hwminusIm : wminus.im ≠ 0 := by simpa [wminus] using hy
  have hplusPath : ContinuousAt
      (fun q : ℝ × ℝ => (q.1 : ℂ) + (q.2 : ℂ) * Complex.I) p := by
    fun_prop
  have hminusPath : ContinuousAt
      (fun q : ℝ × ℝ => -(q.1 : ℂ) + (q.2 : ℂ) * Complex.I) p := by
    fun_prop
  have hplusNum : ContinuousAt
      (fun q : ℝ × ℝ => deBruijnNewmanPolymathBoydR2CauchyWeight
        ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I)) p :=
    (deBruijnNewmanPolymathBoydR2CauchyWeight_continuousAt_of_im_ne_zero
      hwplusIm).comp_of_eq hplusPath rfl
  have hminusNum : ContinuousAt
      (fun q : ℝ × ℝ => deBruijnNewmanPolymathBoydInverseR2CauchyWeight
        (-(q.1 : ℂ) + (q.2 : ℂ) * Complex.I)) p :=
    (deBruijnNewmanPolymathBoydInverseR2CauchyWeight_continuousAt_of_im_ne_zero
      hwminusIm).comp_of_eq hminusPath rfl
  have hplusDen : ContinuousAt
      (fun q : ℝ × ℝ => (q.1 : ℂ) + (q.2 : ℂ) * Complex.I - z) p := by
    fun_prop
  have hminusDen : ContinuousAt
      (fun q : ℝ × ℝ => -(q.1 : ℂ) + (q.2 : ℂ) * Complex.I - z) p := by
    fun_prop
  have hplusNe : wplus - z ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    have hre := congrArg Complex.re h
    have hpz : p.1 < z.re := lt_of_le_of_lt hp.1.2 hrz
    simp [wplus] at hre
    linarith
  have hminusNe : wminus - z ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    have hre := congrArg Complex.re h
    have hpz : -p.1 < z.re := by linarith [hp.1.1, hrz]
    simp [wminus] at hre
    linarith
  exact (continuousAt_const.mul
    ((hplusNum.div hplusDen hplusNe).sub
      (hminusNum.div hminusDen hminusNe))).continuousWithinAt

/-- The paired offset kernels converge uniformly to the exact boundary kernel on every fixed
compact annulus away from zero. -/
theorem deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand_tendstoUniformlyOn_middle
    {z : ℂ} (hz : 0 < z.re) {delta A : ℝ}
    (hdelta : 0 < delta) (_hdeltaA : delta ≤ A) :
    TendstoUniformlyOn
      (fun epsilon y =>
        deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand z epsilon y)
      (deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand z)
      (𝓝 0)
      (deBruijnNewmanPolymathBoydBoundaryMiddleSet delta A) := by
  let r : ℝ := z.re / 2
  let U : Set ℝ := Icc (-r) r
  let V : Set ℝ := deBruijnNewmanPolymathBoydBoundaryMiddleSet delta A
  have hr : 0 < r := by simp [r, hz]
  have hrz : r < z.re := by dsimp [r]; linarith
  have hcompact : IsCompact (U ×ˢ V) := by
    exact isCompact_Icc.prod
      (isCompact_deBruijnNewmanPolymathBoydBoundaryMiddleSet delta A)
  have hcontinuous : ContinuousOn
      (fun p : ℝ × ℝ =>
        deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand z p.1 p.2)
      (U ×ˢ V) := by
    exact deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand_continuousOn_slab_middle
      hrz hdelta
  have huniform : UniformContinuousOn
      (Function.uncurry fun epsilon y =>
        deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand z epsilon y)
      (U ×ˢ V) :=
    hcompact.uniformContinuousOn_of_continuous hcontinuous
  have hzero : (0 : ℝ) ∈ U := by simp [U, hr.le]
  have hUnhds : U ∈ 𝓝 (0 : ℝ) := by
    exact Icc_mem_nhds (by simpa [U] using neg_lt_zero.mpr hr) (by simpa [U] using hr)
  have hraw : TendstoUniformlyOn
      (fun epsilon y =>
        deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand z epsilon y)
      (fun y => deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand z 0 y)
      (𝓝 0) V := by
    simpa only [nhdsWithin_eq_nhds.2 hUnhds] using
      huniform.tendstoUniformlyOn hzero
  exact hraw.congr_right fun y hy =>
    deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand_zero z
      (deBruijnNewmanPolymathBoydBoundaryMiddleSet_nonzero hdelta hy)

/-- The normalized error contributed by one oriented boundary-coordinate segment. -/
def deBruijnNewmanPolymathBoydBoundarySegmentResidual
    (z : ℂ) (epsilon a b : ℝ) : ℂ :=
  -(1 / (2 * Real.pi * Complex.I * z)) *
    (∫ y : ℝ in a..b,
      deBruijnNewmanPolymathBoydBoundaryTraceErrorIntegrand z epsilon y)

/-- The central residual where the two individual remainder weights must cancel. -/
def deBruijnNewmanPolymathBoydBoundaryNearResidual
    (z : ℂ) (epsilon delta : ℝ) : ℂ :=
  deBruijnNewmanPolymathBoydBoundarySegmentResidual z epsilon (-delta) delta

/-- The residual on the two fixed compact annuli between `delta` and `A`. -/
def deBruijnNewmanPolymathBoydBoundaryMiddleResidual
    (z : ℂ) (epsilon delta A : ℝ) : ℂ :=
  deBruijnNewmanPolymathBoydBoundarySegmentResidual z epsilon (-A) (-delta) +
    deBruijnNewmanPolymathBoydBoundarySegmentResidual z epsilon delta A

/-- The two residual tails between a fixed cutoff `A` and the current rectangle height `T`. -/
def deBruijnNewmanPolymathBoydBoundaryTailResidual
    (z : ℂ) (epsilon A T : ℝ) : ℂ :=
  deBruijnNewmanPolymathBoydBoundarySegmentResidual z epsilon (-T) (-A) +
    deBruijnNewmanPolymathBoydBoundarySegmentResidual z epsilon A T

theorem deBruijnNewmanPolymathBoydBoundarySegmentResidual_tendsto_zero_of_subset_middle
    {z : ℂ} (hz : 0 < z.re) {delta A a b : ℝ}
    (hdelta : 0 < delta) (hdeltaA : delta ≤ A)
    (hsub : Ι a b ⊆ deBruijnNewmanPolymathBoydBoundaryMiddleSet delta A) :
    Filter.Tendsto
      (fun epsilon =>
        deBruijnNewmanPolymathBoydBoundarySegmentResidual z epsilon a b)
      (𝓝 0) (𝓝 0) := by
  have huniform :=
    deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand_tendstoUniformlyOn_middle
      hz hdelta hdeltaA
  have hintegral : Filter.Tendsto
      (fun epsilon => ∫ y : ℝ in a..b,
        deBruijnNewmanPolymathBoydBoundaryTraceErrorIntegrand z epsilon y)
      (𝓝 0) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro eta heta
    let c : ℝ := eta / (|b - a| + 1)
    have hlength : 0 < |b - a| + 1 := by positivity
    have hc : 0 < c := div_pos heta hlength
    have heventually := (Metric.tendstoUniformlyOn_iff.mp huniform) c hc
    filter_upwards [heventually] with epsilon hepsilon
    have hnorm :
        ‖∫ y : ℝ in a..b,
          deBruijnNewmanPolymathBoydBoundaryTraceErrorIntegrand z epsilon y‖ ≤
          c * |b - a| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro y hy
      have hdist := hepsilon y (hsub hy)
      exact (by
        simpa only [deBruijnNewmanPolymathBoydBoundaryTraceErrorIntegrand,
          dist_eq_norm, norm_sub_rev] using hdist.le)
    rw [dist_zero_right]
    calc
      ‖∫ y : ℝ in a..b,
          deBruijnNewmanPolymathBoydBoundaryTraceErrorIntegrand z epsilon y‖
          ≤ c * |b - a| := hnorm
      _ < c * (|b - a| + 1) := by
        exact mul_lt_mul_of_pos_left (by linarith [abs_nonneg (b - a)]) hc
      _ = eta := by
        dsimp [c]
        exact div_mul_cancel₀ eta (ne_of_gt hlength)
  have hconst : Filter.Tendsto
      (fun _ : ℝ => -(1 / (2 * Real.pi * Complex.I * z)))
      (𝓝 0) (𝓝 (-(1 / (2 * Real.pi * Complex.I * z)))) :=
    tendsto_const_nhds
  simpa [deBruijnNewmanPolymathBoydBoundarySegmentResidual] using
    hconst.mul hintegral

/-- Every fixed compact-annulus contribution vanishes as the two offset lines approach the
boundary. -/
theorem deBruijnNewmanPolymathBoydBoundaryMiddleResidual_tendsto
    {z : ℂ} (hz : 0 < z.re) {delta A : ℝ}
    (hdelta : 0 < delta) (hdeltaA : delta ≤ A) :
    Filter.Tendsto
      (fun epsilon =>
        deBruijnNewmanPolymathBoydBoundaryMiddleResidual z epsilon delta A)
      (𝓝 0) (𝓝 0) := by
  have hneg : Ι (-A) (-delta) ⊆
      deBruijnNewmanPolymathBoydBoundaryMiddleSet delta A := by
    intro y hy
    left
    have hy' := uIoc_subset_uIcc hy
    simpa [uIcc_of_le (neg_le_neg hdeltaA)] using hy'
  have hpos : Ι delta A ⊆
      deBruijnNewmanPolymathBoydBoundaryMiddleSet delta A := by
    intro y hy
    right
    have hy' := uIoc_subset_uIcc hy
    simpa [uIcc_of_le hdeltaA] using hy'
  have hleft :=
    deBruijnNewmanPolymathBoydBoundarySegmentResidual_tendsto_zero_of_subset_middle
      hz hdelta hdeltaA hneg
  have hright :=
    deBruijnNewmanPolymathBoydBoundarySegmentResidual_tendsto_zero_of_subset_middle
      hz hdelta hdeltaA hpos
  simpa [deBruijnNewmanPolymathBoydBoundaryMiddleResidual] using hleft.add hright

/-- The canonical positive offsets tend to zero. -/
theorem deBruijnNewmanPolymathBoydBoundaryEpsilon_tendsto_zero
    (z : ℂ) :
    Filter.Tendsto (deBruijnNewmanPolymathBoydBoundaryEpsilon z)
    Filter.atTop (𝓝 0) := by
  change Filter.Tendsto (fun n : ℕ => z.re / ((n : ℝ) + 2))
    Filter.atTop (𝓝 0)
  have hden : Filter.Tendsto (fun n : ℕ => (n : ℝ) + 2)
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hinv : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹)
      Filter.atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hden
  have hmul := (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => z.re)
    Filter.atTop (𝓝 z.re)).mul hinv
  simpa [div_eq_mul_inv] using hmul

/-- The compact-annulus residual also vanishes along the canonical rectangle family. -/
theorem deBruijnNewmanPolymathBoydBoundaryMiddleResidual_tendsto_canonical
    {z : ℂ} (hz : 0 < z.re) {delta A : ℝ}
    (hdelta : 0 < delta) (hdeltaA : delta ≤ A) :
    Filter.Tendsto
      (fun n : ℕ => deBruijnNewmanPolymathBoydBoundaryMiddleResidual z
        (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) delta A)
      Filter.atTop (𝓝 0) :=
  (deBruijnNewmanPolymathBoydBoundaryMiddleResidual_tendsto
    hz hdelta hdeltaA).comp
      (deBruijnNewmanPolymathBoydBoundaryEpsilon_tendsto_zero z)

theorem deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand_eq_plus
    {z : ℂ} (hz : 0 < z.re) (s : ℝ) :
    deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand z s =
      deBruijnNewmanPolymathBoydBoundaryJumpPlusIntegrand z s / z := by
  have hz0 : z ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hwz : (s : ℂ) * Complex.I - z ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hden : 1 - (s : ℂ) * Complex.I / z ≠ 0 := by
    intro hzero
    have hdiv : (s : ℂ) * Complex.I / z = 1 := (sub_eq_zero.mp hzero).symm
    apply hwz
    rw [sub_eq_zero]
    calc
      (s : ℂ) * Complex.I = ((s : ℂ) * Complex.I / z) * z :=
        (div_mul_cancel₀ _ hz0).symm
      _ = z := by rw [hdiv, one_mul]
  rw [deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand,
    deBruijnNewmanPolymathBoydBoundaryJumpPlusIntegrand]
  field_simp [hz0, hwz, hden]
  rw [Complex.I_sq]
  rw [show z - Complex.I * ↑s = -(Complex.I * ↑s - z) by ring, div_neg]
  ring

theorem deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand_eq_minus
    {z : ℂ} (hz : 0 < z.re) (s : ℝ) :
    deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand z (-s) =
      -(deBruijnNewmanPolymathBoydBoundaryJumpMinusIntegrand z s / z) := by
  have hz0 : z ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hwz : -(s : ℂ) * Complex.I - z ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hden : 1 + (s : ℂ) * Complex.I / z ≠ 0 := by
    intro hzero
    have hdiv : (s : ℂ) * Complex.I / z = -1 := by
      linear_combination hzero
    apply hwz
    rw [sub_eq_zero]
    calc
      -(s : ℂ) * Complex.I = -(((s : ℂ) * Complex.I / z) * z) := by
        simpa only [neg_mul] using
          (congrArg Neg.neg (div_mul_cancel₀ ((s : ℂ) * Complex.I) hz0)).symm
      _ = z := by rw [hdiv]; ring
  rw [deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand,
    deBruijnNewmanPolymathBoydBoundaryJumpMinusIntegrand]
  push_cast
  field_simp [hz0, hwz, hden]
  rw [Complex.I_sq]
  rw [show -(Complex.I * ↑s) - z = -(z + Complex.I * ↑s) by ring, div_neg]
  ring

theorem deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand_eq_minus_of_neg
    {z : ℂ} (hz : 0 < z.re) (y : ℝ) :
    deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand z y =
      -(deBruijnNewmanPolymathBoydBoundaryJumpMinusIntegrand z (-y) / z) := by
  simpa using
    (deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand_eq_minus
      hz (-y))

/-- The exact boundary-axis kernel is interval integrable across its totalized value at zero. -/
theorem deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand_intervalIntegrable
    {z : ℂ} (hz : 0 < z.re) {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable
      (deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand z) volume (-T) T := by
  have hjump := deBruijnNewmanPolymathBoydBoundaryJump_integrableOn hz
  have hplusOn : IntegrableOn
      (fun s : ℝ => deBruijnNewmanPolymathBoydBoundaryJumpPlusIntegrand z s / z)
      (Ioi 0) volume := by
    change Integrable
      (fun s : ℝ => deBruijnNewmanPolymathBoydBoundaryJumpPlusIntegrand z s / z)
      (volume.restrict (Ioi 0))
    simpa [div_eq_mul_inv] using hjump.1.mul_const z⁻¹
  have hminusOn : IntegrableOn
      (fun s : ℝ => -(deBruijnNewmanPolymathBoydBoundaryJumpMinusIntegrand z s / z))
      (Ioi 0) volume := by
    change Integrable
      (fun s : ℝ => -(deBruijnNewmanPolymathBoydBoundaryJumpMinusIntegrand z s / z))
      (volume.restrict (Ioi 0))
    have h := hjump.2.mul_const z⁻¹
    simpa [div_eq_mul_inv] using h.neg
  have hplus : IntervalIntegrable
      (fun s : ℝ => deBruijnNewmanPolymathBoydBoundaryJumpPlusIntegrand z s / z)
      volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
    exact hplusOn.mono_set Ioc_subset_Ioi_self
  have hminus : IntervalIntegrable
      (fun s : ℝ => -(deBruijnNewmanPolymathBoydBoundaryJumpMinusIntegrand z s / z))
      volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
    exact hminusOn.mono_set Ioc_subset_Ioi_self
  have haxisPlus : IntervalIntegrable
      (deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand z) volume 0 T := by
    apply hplus.congr_uIoo
    intro s _
    exact (deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand_eq_plus hz s).symm
  have hminusComp : IntervalIntegrable
      (fun y : ℝ => -(deBruijnNewmanPolymathBoydBoundaryJumpMinusIntegrand z (-y) / z))
      volume 0 (-T) := by
    simpa using ((IntervalIntegrable.iff_comp_neg
      (f := fun s : ℝ =>
        -(deBruijnNewmanPolymathBoydBoundaryJumpMinusIntegrand z s / z))
      (a := 0) (b := T)).mp hminus)
  have haxisMinus : IntervalIntegrable
      (deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand z) volume (-T) 0 := by
    apply hminusComp.symm.congr_uIoo
    intro y _
    exact (deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand_eq_minus_of_neg hz y).symm
  exact haxisMinus.trans haxisPlus

/-- The source jump truncation is exactly the normalized symmetric interval integral of the
boundary-axis kernel. -/
theorem deBruijnNewmanPolymathBoydTruncatedBoundaryJumpProjection_eq_axisIntegral
    {z : ℂ} (hz : 0 < z.re) {T : ℝ} (hT : 0 ≤ T) :
    deBruijnNewmanPolymathBoydTruncatedBoundaryJumpProjection z T =
      -(1 / (2 * Real.pi * Complex.I * z)) *
        (∫ y : ℝ in -T..T,
          deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand z y) := by
  have haxis :=
    deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand_intervalIntegrable hz hT
  have haxisOn : IntegrableOn
      (deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand z) (Ioc (-T) T) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp haxis
  have haxisMinus : IntervalIntegrable
      (deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand z) volume (-T) 0 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (neg_nonpos.mpr hT)]
    exact haxisOn.mono_set (by intro y hy; exact ⟨hy.1, hy.2.trans hT⟩)
  have haxisPlus : IntervalIntegrable
      (deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand z) volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
    exact haxisOn.mono_set (by intro y hy; exact ⟨(neg_nonpos.mpr hT).trans_lt hy.1, hy.2⟩)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals haxisMinus haxisPlus
  have hplusEq :
      (∫ y : ℝ in 0..T,
        deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand z y) =
      (∫ s : ℝ in 0..T,
        deBruijnNewmanPolymathBoydBoundaryJumpPlusIntegrand z s / z) := by
    apply intervalIntegral.integral_congr_Ioo_of_le hT
    intro s _
    exact deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand_eq_plus hz s
  have hminusEq :
      (∫ y : ℝ in -T..0,
        deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand z y) =
      (∫ s : ℝ in 0..T,
        -(deBruijnNewmanPolymathBoydBoundaryJumpMinusIntegrand z s / z)) := by
    calc
      (∫ y : ℝ in -T..0,
          deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand z y) =
          ∫ y : ℝ in -T..0,
            -(deBruijnNewmanPolymathBoydBoundaryJumpMinusIntegrand z (-y) / z) := by
            apply intervalIntegral.integral_congr_Ioo_of_le (neg_nonpos.mpr hT)
            intro y _
            exact deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand_eq_minus_of_neg
              hz y
      _ = ∫ s : ℝ in 0..T,
          -(deBruijnNewmanPolymathBoydBoundaryJumpMinusIntegrand z s / z) := by
            simpa using (intervalIntegral.integral_comp_neg
              (f := fun s : ℝ =>
                -(deBruijnNewmanPolymathBoydBoundaryJumpMinusIntegrand z s / z))
              (a := -T) (b := 0))
  rw [deBruijnNewmanPolymathBoydTruncatedBoundaryJumpProjection,
    ← hsplit, hminusEq, hplusEq]
  simp only [intervalIntegral.integral_neg, intervalIntegral.integral_div]
  have hz0 : z ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  field_simp
  ring

theorem deBruijnNewmanPolymathBoydBoundaryEpsilon_pos
    {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    0 < deBruijnNewmanPolymathBoydBoundaryEpsilon z n := by
  rw [deBruijnNewmanPolymathBoydBoundaryEpsilon]
  exact div_pos hz (by positivity)

theorem deBruijnNewmanPolymathBoydBoundaryEpsilon_lt_re
    {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    deBruijnNewmanPolymathBoydBoundaryEpsilon z n < z.re := by
  rw [deBruijnNewmanPolymathBoydBoundaryEpsilon]
  have hn : (1 : ℝ) < (n : ℝ) + 2 := by
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  exact div_lt_self hz hn

theorem deBruijnNewmanPolymathBoydBoundaryHeight_nonneg
    (z : ℂ) (n : ℕ) :
    0 ≤ deBruijnNewmanPolymathBoydBoundaryHeight z n := by
  rw [deBruijnNewmanPolymathBoydBoundaryHeight]
  positivity

theorem deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand_intervalIntegrable
    {z : ℂ} {epsilon T : ℝ} (hz : 0 < z.re) (hepsilon : 0 < epsilon)
    (hepsilonz : epsilon < z.re) :
    IntervalIntegrable
      (deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand z epsilon)
      volume (-T) T := by
  have hright := deBruijnNewmanPolymathBoydR2_shiftedLine_intervalIntegrable
    (T := T) hepsilon hepsilonz
  have hleft := deBruijnNewmanPolymathBoydInverseR2_shiftedLine_intervalIntegrable
    (T := T) hz hepsilon
  have hdiff := hright.sub hleft
  have hmul := hdiff.const_mul Complex.I
  change IntervalIntegrable
    (fun y : ℝ => Complex.I *
      (deBruijnNewmanPolymathBoydR2CauchyWeight
          ((epsilon : ℂ) + (y : ℂ) * Complex.I) /
            ((epsilon : ℂ) + (y : ℂ) * Complex.I - z) -
        deBruijnNewmanPolymathBoydInverseR2CauchyWeight
          (-(epsilon : ℂ) + (y : ℂ) * Complex.I) /
            (-(epsilon : ℂ) + (y : ℂ) * Complex.I - z))) volume (-T) T
  exact hmul

/-- Near zero, the two explicit `1/(12*w)` remainder singularities cancel into one regular
`epsilon/6` denominator correction. -/
theorem deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand_eq_nearZeroRegularized
    {z : ℂ} {epsilon y : ℝ} (hepsilon : 0 < epsilon)
    (hepsilonz : epsilon < z.re) :
    let w : ℂ := (epsilon : ℂ) + (y : ℂ) * Complex.I
    let q : ℂ := -(epsilon : ℂ) + (y : ℂ) * Complex.I
    deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand z epsilon y =
      Complex.I *
        (((w * deBruijnNewmanPolymathScaledGamma w - w) / (w - z)) -
          ((q / deBruijnNewmanPolymathScaledGamma (-q) - q) / (q - z)) +
          (epsilon : ℂ) / (6 * (w - z) * (q - z))) := by
  dsimp only
  let w : ℂ := (epsilon : ℂ) + (y : ℂ) * Complex.I
  let q : ℂ := -(epsilon : ℂ) + (y : ℂ) * Complex.I
  have hw0 : w ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [w] at hre
    linarith
  have hq0 : q ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [q] at hre
    linarith
  have hwz : w - z ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    have hre := congrArg Complex.re h
    simp [w] at hre
    linarith
  have hqz : q - z ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    have hre := congrArg Complex.re h
    simp [q] at hre
    linarith
  have hright : deBruijnNewmanPolymathBoydR2CauchyWeight w =
      w * deBruijnNewmanPolymathScaledGamma w - w - 1 / 12 := by
    rw [deBruijnNewmanPolymathBoydR2CauchyWeight,
      deBruijnNewmanPolymathGammaStirlingR2]
    change w * (deBruijnNewmanPolymathScaledGamma w - 1 - 1 / (12 * w)) = _
    field_simp [hw0]
  have hleft : deBruijnNewmanPolymathBoydInverseR2CauchyWeight q =
      q / deBruijnNewmanPolymathScaledGamma (-q) - q - 1 / 12 := by
    rw [deBruijnNewmanPolymathBoydInverseR2CauchyWeight,
      deBruijnNewmanPolymathScaledGammaInverseR2]
    field_simp [hq0]
    ring
  rw [deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand]
  change Complex.I *
    (deBruijnNewmanPolymathBoydR2CauchyWeight w / (w - z) -
      deBruijnNewmanPolymathBoydInverseR2CauchyWeight q / (q - z)) =
    Complex.I *
      (((w * deBruijnNewmanPolymathScaledGamma w - w) / (w - z)) -
        ((q / deBruijnNewmanPolymathScaledGamma (-q) - q) / (q - z)) +
        (epsilon : ℂ) / (6 * (w - z) * (q - z)))
  rw [hright, hleft]
  field_simp [hwz, hqz]
  ring

theorem deBruijnNewmanPolymathBoydBoundaryTraceErrorIntegrand_intervalIntegrable_canonical
    {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    IntervalIntegrable
      (deBruijnNewmanPolymathBoydBoundaryTraceErrorIntegrand z
        (deBruijnNewmanPolymathBoydBoundaryEpsilon z n))
      volume
      (-deBruijnNewmanPolymathBoydBoundaryHeight z n)
      (deBruijnNewmanPolymathBoydBoundaryHeight z n) := by
  have hshift :=
    deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand_intervalIntegrable
      hz (deBruijnNewmanPolymathBoydBoundaryEpsilon_pos hz n)
        (deBruijnNewmanPolymathBoydBoundaryEpsilon_lt_re hz n)
      (T := deBruijnNewmanPolymathBoydBoundaryHeight z n)
  have haxis :=
    deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand_intervalIntegrable
      hz (deBruijnNewmanPolymathBoydBoundaryHeight_nonneg z n)
  change IntervalIntegrable
    (fun y : ℝ =>
      deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand z
          (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) y -
        deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand z y)
    volume (-deBruijnNewmanPolymathBoydBoundaryHeight z n)
      (deBruijnNewmanPolymathBoydBoundaryHeight z n)
  exact hshift.sub haxis

theorem intervalIntegrable_mono_closed_interval
    {f : ℝ → ℂ} {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hac : a ≤ c) (hdb : d ≤ b)
    (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable f volume c d := by
  have hfon : IntegrableOn f (Ioc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hf
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hcd]
  exact hfon.mono_set (by
    intro x hx
    exact ⟨lt_of_le_of_lt hac hx.1, hx.2.trans hdb⟩)

/-- The Loop 28 discrepancy is the normalized symmetric interval integral of the exact error
kernel. -/
theorem deBruijnNewmanPolymathBoydBoundaryTraceDiscrepancy_eq_totalSegmentResidual
    {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    deBruijnNewmanPolymathBoydBoundaryTraceDiscrepancy z n =
      deBruijnNewmanPolymathBoydBoundarySegmentResidual z
        (deBruijnNewmanPolymathBoydBoundaryEpsilon z n)
        (-deBruijnNewmanPolymathBoydBoundaryHeight z n)
        (deBruijnNewmanPolymathBoydBoundaryHeight z n) := by
  let epsilon := deBruijnNewmanPolymathBoydBoundaryEpsilon z n
  let T := deBruijnNewmanPolymathBoydBoundaryHeight z n
  have hepsilon : 0 < epsilon := deBruijnNewmanPolymathBoydBoundaryEpsilon_pos hz n
  have hepsilonz : epsilon < z.re :=
    deBruijnNewmanPolymathBoydBoundaryEpsilon_lt_re hz n
  have hT : 0 ≤ T := deBruijnNewmanPolymathBoydBoundaryHeight_nonneg z n
  have hshift :=
    deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand_intervalIntegrable
      hz hepsilon hepsilonz (T := T)
  have haxis :=
    deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand_intervalIntegrable hz hT
  have herrorIntegral :
      (∫ y : ℝ in -T..T,
        deBruijnNewmanPolymathBoydBoundaryTraceErrorIntegrand z epsilon y) =
        (∫ y : ℝ in -T..T,
          deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand z epsilon y) -
        (∫ y : ℝ in -T..T,
          deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand z y) := by
    simpa [deBruijnNewmanPolymathBoydBoundaryTraceErrorIntegrand] using
      (intervalIntegral.integral_sub hshift haxis)
  rw [deBruijnNewmanPolymathBoydBoundaryTraceDiscrepancy,
    deBruijnNewmanPolymathBoydFiniteBoundaryProjection_eq_shiftedBoundaryPairIntegral
      hz hepsilon hepsilonz,
    deBruijnNewmanPolymathBoydTruncatedBoundaryJumpProjection_eq_axisIntegral hz hT,
    deBruijnNewmanPolymathBoydBoundarySegmentResidual,
    herrorIntegral]
  ring

/-- Exact near/middle/tail partition of the canonical trace discrepancy. -/
theorem deBruijnNewmanPolymathBoydBoundaryTraceDiscrepancy_eq_threeScale
    {z : ℂ} (hz : 0 < z.re) {n : ℕ} {delta A : ℝ}
    (hdelta : 0 < delta) (hdeltaA : delta ≤ A)
    (hAT : A ≤ deBruijnNewmanPolymathBoydBoundaryHeight z n) :
    deBruijnNewmanPolymathBoydBoundaryTraceDiscrepancy z n =
      deBruijnNewmanPolymathBoydBoundaryNearResidual z
          (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) delta +
        deBruijnNewmanPolymathBoydBoundaryMiddleResidual z
          (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) delta A +
        deBruijnNewmanPolymathBoydBoundaryTailResidual z
          (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) A
          (deBruijnNewmanPolymathBoydBoundaryHeight z n) := by
  let epsilon := deBruijnNewmanPolymathBoydBoundaryEpsilon z n
  let T := deBruijnNewmanPolymathBoydBoundaryHeight z n
  let E := deBruijnNewmanPolymathBoydBoundaryTraceErrorIntegrand z epsilon
  have hT : 0 ≤ T := deBruijnNewmanPolymathBoydBoundaryHeight_nonneg z n
  have hwhole : IntervalIntegrable E volume (-T) T :=
    deBruijnNewmanPolymathBoydBoundaryTraceErrorIntegrand_intervalIntegrable_canonical hz n
  have htailNeg : IntervalIntegrable E volume (-T) (-A) :=
    intervalIntegrable_mono_closed_interval (by linarith) (by linarith)
      (le_refl _) (by linarith) hwhole
  have hmiddleNeg : IntervalIntegrable E volume (-A) (-delta) :=
    intervalIntegrable_mono_closed_interval (by linarith) (by linarith)
      (by linarith) (by linarith) hwhole
  have hnear : IntervalIntegrable E volume (-delta) delta :=
    intervalIntegrable_mono_closed_interval (by linarith) (by linarith)
      (by linarith) (by linarith) hwhole
  have hmiddlePos : IntervalIntegrable E volume delta A :=
    intervalIntegrable_mono_closed_interval (by linarith) hdeltaA
      (by linarith) hAT hwhole
  have htailPos : IntervalIntegrable E volume A T :=
    intervalIntegrable_mono_closed_interval (by linarith) hAT
      (by linarith) (le_refl _) hwhole
  have htoNegDelta := htailNeg.trans hmiddleNeg
  have htoDelta := htoNegDelta.trans hnear
  have htoA := htoDelta.trans hmiddlePos
  have hsum :
      (∫ y : ℝ in -T..T, E y) =
        (∫ y : ℝ in -T..-A, E y) +
        (∫ y : ℝ in -A..-delta, E y) +
        (∫ y : ℝ in -delta..delta, E y) +
        (∫ y : ℝ in delta..A, E y) +
        (∫ y : ℝ in A..T, E y) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals htoA htailPos,
      ← intervalIntegral.integral_add_adjacent_intervals htoDelta hmiddlePos,
      ← intervalIntegral.integral_add_adjacent_intervals htoNegDelta hnear,
      ← intervalIntegral.integral_add_adjacent_intervals htailNeg hmiddleNeg]
  rw [deBruijnNewmanPolymathBoydBoundaryTraceDiscrepancy_eq_totalSegmentResidual hz n]
  change -(1 / (2 * Real.pi * Complex.I * z)) * (∫ y : ℝ in -T..T, E y) =
    -(1 / (2 * Real.pi * Complex.I * z)) * (∫ y : ℝ in -delta..delta, E y) +
      (-(1 / (2 * Real.pi * Complex.I * z)) * (∫ y : ℝ in -A..-delta, E y) +
        -(1 / (2 * Real.pi * Complex.I * z)) * (∫ y : ℝ in delta..A, E y)) +
      (-(1 / (2 * Real.pi * Complex.I * z)) * (∫ y : ℝ in -T..-A, E y) +
        -(1 / (2 * Real.pi * Complex.I * z)) * (∫ y : ℝ in A..T, E y))
  rw [hsum]
  ring

/-- After every fixed compact annulus is removed, the complete discrepancy limit is exactly the
sum of the near-zero and shifted-tail limits. -/
theorem deBruijnNewmanPolymathBoydBoundaryTrace_tendsto_iff_near_add_tail
    {z : ℂ} (hz : 0 < z.re) {delta A : ℝ}
    (hdelta : 0 < delta) (hdeltaA : delta ≤ A) :
    Filter.Tendsto
        (deBruijnNewmanPolymathBoydBoundaryTraceDiscrepancy z)
        Filter.atTop (𝓝 0) ↔
      Filter.Tendsto
        (fun n : ℕ =>
          deBruijnNewmanPolymathBoydBoundaryNearResidual z
              (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) delta +
            deBruijnNewmanPolymathBoydBoundaryTailResidual z
              (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) A
              (deBruijnNewmanPolymathBoydBoundaryHeight z n))
        Filter.atTop (𝓝 0) := by
  have hmiddle :=
    deBruijnNewmanPolymathBoydBoundaryMiddleResidual_tendsto_canonical
      hz hdelta hdeltaA
  have hheight := deBruijnNewmanPolymathBoydBoundaryHeight_tendsto_atTop z
  have hA : ∀ᶠ n : ℕ in Filter.atTop,
      A ≤ deBruijnNewmanPolymathBoydBoundaryHeight z n :=
    (Filter.tendsto_atTop.1 hheight A)
  have hthree : ∀ᶠ n : ℕ in Filter.atTop,
      deBruijnNewmanPolymathBoydBoundaryTraceDiscrepancy z n =
        deBruijnNewmanPolymathBoydBoundaryNearResidual z
            (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) delta +
          deBruijnNewmanPolymathBoydBoundaryMiddleResidual z
            (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) delta A +
          deBruijnNewmanPolymathBoydBoundaryTailResidual z
            (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) A
            (deBruijnNewmanPolymathBoydBoundaryHeight z n) := by
    filter_upwards [hA] with n hn
    exact deBruijnNewmanPolymathBoydBoundaryTraceDiscrepancy_eq_threeScale
      hz hdelta hdeltaA hn
  constructor
  · intro hdiscrepancy
    have hsub := hdiscrepancy.sub hmiddle
    have heq : (fun n : ℕ =>
        deBruijnNewmanPolymathBoydBoundaryTraceDiscrepancy z n -
          deBruijnNewmanPolymathBoydBoundaryMiddleResidual z
            (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) delta A) =ᶠ[Filter.atTop]
        (fun n : ℕ =>
          deBruijnNewmanPolymathBoydBoundaryNearResidual z
              (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) delta +
            deBruijnNewmanPolymathBoydBoundaryTailResidual z
              (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) A
              (deBruijnNewmanPolymathBoydBoundaryHeight z n)) := by
      filter_upwards [hthree] with n hn
      rw [hn]
      ring
    have hsub' : Filter.Tendsto (fun n : ℕ =>
        deBruijnNewmanPolymathBoydBoundaryTraceDiscrepancy z n -
          deBruijnNewmanPolymathBoydBoundaryMiddleResidual z
            (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) delta A)
        Filter.atTop (𝓝 0) := by
      simpa using hsub
    exact hsub'.congr' heq
  · intro hnearTail
    have hadd := hnearTail.add hmiddle
    have heq : (fun n : ℕ =>
        (deBruijnNewmanPolymathBoydBoundaryNearResidual z
            (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) delta +
          deBruijnNewmanPolymathBoydBoundaryTailResidual z
            (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) A
            (deBruijnNewmanPolymathBoydBoundaryHeight z n)) +
          deBruijnNewmanPolymathBoydBoundaryMiddleResidual z
            (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) delta A) =ᶠ[Filter.atTop]
        deBruijnNewmanPolymathBoydBoundaryTraceDiscrepancy z := by
      filter_upwards [hthree] with n hn
      rw [hn]
      ring
    have hadd' : Filter.Tendsto (fun n : ℕ =>
        (deBruijnNewmanPolymathBoydBoundaryNearResidual z
            (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) delta +
          deBruijnNewmanPolymathBoydBoundaryTailResidual z
            (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) A
            (deBruijnNewmanPolymathBoydBoundaryHeight z n)) +
          deBruijnNewmanPolymathBoydBoundaryMiddleResidual z
            (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) delta A)
        Filter.atTop (𝓝 0) := by
      simpa using hadd
    exact hadd'.congr' heq

/-- Auditable Loop 29 certificate: every fixed compact annulus is eliminated, and the remaining
trace limit is exactly the near-zero plus shifted-tail problem. -/
def deBruijnNewmanPolymathBoydBoundaryTraceTwoScaleCertificateStatement : Prop :=
  (∀ (z : ℂ), 0 < z.re → ∀ (delta A : ℝ), 0 < delta → delta ≤ A →
    TendstoUniformlyOn
      (fun epsilon y =>
        deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand z epsilon y)
      (deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand z)
      (𝓝 0)
      (deBruijnNewmanPolymathBoydBoundaryMiddleSet delta A)) ∧
  (∀ (z : ℂ), 0 < z.re → ∀ (delta A : ℝ), 0 < delta → delta ≤ A →
    Filter.Tendsto
      (fun epsilon =>
        deBruijnNewmanPolymathBoydBoundaryMiddleResidual z epsilon delta A)
      (𝓝 0) (𝓝 0)) ∧
  (∀ (z : ℂ), 0 < z.re → ∀ (delta A : ℝ), 0 < delta → delta ≤ A →
    Filter.Tendsto
      (fun n : ℕ => deBruijnNewmanPolymathBoydBoundaryMiddleResidual z
        (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) delta A)
      Filter.atTop (𝓝 0)) ∧
  (∀ (z : ℂ), 0 < z.re → ∀ T : ℝ, 0 ≤ T →
    deBruijnNewmanPolymathBoydTruncatedBoundaryJumpProjection z T =
      -(1 / (2 * Real.pi * Complex.I * z)) *
        (∫ y : ℝ in -T..T,
          deBruijnNewmanPolymathBoydBoundaryAxisPairIntegrand z y)) ∧
  (∀ (z : ℂ), 0 < z.re → ∀ (epsilon y : ℝ), 0 < epsilon → epsilon < z.re →
    let w : ℂ := (epsilon : ℂ) + (y : ℂ) * Complex.I
    let q : ℂ := -(epsilon : ℂ) + (y : ℂ) * Complex.I
    deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand z epsilon y =
      Complex.I *
        (((w * deBruijnNewmanPolymathScaledGamma w - w) / (w - z)) -
          ((q / deBruijnNewmanPolymathScaledGamma (-q) - q) / (q - z)) +
          (epsilon : ℂ) / (6 * (w - z) * (q - z)))) ∧
  (∀ (z : ℂ), 0 < z.re → ∀ (n : ℕ) (delta A : ℝ),
    0 < delta → delta ≤ A → A ≤ deBruijnNewmanPolymathBoydBoundaryHeight z n →
    deBruijnNewmanPolymathBoydBoundaryTraceDiscrepancy z n =
      deBruijnNewmanPolymathBoydBoundaryNearResidual z
          (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) delta +
        deBruijnNewmanPolymathBoydBoundaryMiddleResidual z
          (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) delta A +
        deBruijnNewmanPolymathBoydBoundaryTailResidual z
          (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) A
          (deBruijnNewmanPolymathBoydBoundaryHeight z n)) ∧
  (∀ (z : ℂ), 0 < z.re → ∀ (delta A : ℝ), 0 < delta → delta ≤ A →
    (Filter.Tendsto
        (deBruijnNewmanPolymathBoydBoundaryTraceDiscrepancy z)
        Filter.atTop (𝓝 0) ↔
      Filter.Tendsto
        (fun n : ℕ =>
          deBruijnNewmanPolymathBoydBoundaryNearResidual z
              (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) delta +
            deBruijnNewmanPolymathBoydBoundaryTailResidual z
              (deBruijnNewmanPolymathBoydBoundaryEpsilon z n) A
              (deBruijnNewmanPolymathBoydBoundaryHeight z n))
        Filter.atTop (𝓝 0)))

/-- The complete unconditional Loop 29 two-scale reduction certificate. -/
theorem deBruijnNewmanPolymathBoydBoundaryTraceTwoScaleCertificate :
    deBruijnNewmanPolymathBoydBoundaryTraceTwoScaleCertificateStatement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun _ hz _ _ hdelta hdeltaA =>
      deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand_tendstoUniformlyOn_middle
        hz hdelta hdeltaA
  · exact fun _ hz _ _ hdelta hdeltaA =>
      deBruijnNewmanPolymathBoydBoundaryMiddleResidual_tendsto
        hz hdelta hdeltaA
  · exact fun _ hz _ _ hdelta hdeltaA =>
      deBruijnNewmanPolymathBoydBoundaryMiddleResidual_tendsto_canonical
        hz hdelta hdeltaA
  · exact fun _ hz _ hT =>
      deBruijnNewmanPolymathBoydTruncatedBoundaryJumpProjection_eq_axisIntegral hz hT
  · exact fun _ _ _ _ hepsilon hepsilonz =>
      deBruijnNewmanPolymathBoydShiftedBoundaryPairIntegrand_eq_nearZeroRegularized
        hepsilon hepsilonz
  · exact fun _ hz _ _ _ hdelta hdeltaA hAT =>
      deBruijnNewmanPolymathBoydBoundaryTraceDiscrepancy_eq_threeScale
        hz hdelta hdeltaA hAT
  · exact fun _ hz _ _ hdelta hdeltaA =>
      deBruijnNewmanPolymathBoydBoundaryTrace_tendsto_iff_near_add_tail
        hz hdelta hdeltaA

end

end LeanLab.Riemann
