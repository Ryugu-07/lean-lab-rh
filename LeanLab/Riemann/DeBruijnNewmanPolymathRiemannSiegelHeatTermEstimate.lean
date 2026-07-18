import LeanLab.Riemann.DeBruijnNewmanPolymathRiemannSiegelHeatContourShift
import LeanLab.Riemann.DeBruijnNewmanPolymathRiemannSiegel
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Effective estimate for the heat-evolved Riemann--Siegel residue term

This module develops the quantitative chain used in Polymath Proposition 6.1.
-/

open Complex MeasureTheory ProbabilityTheory Real Set

namespace LeanLab.Riemann

noncomputable section

def deBruijnNewmanPolymathTermPoint (sigma T : ℝ) : ℂ :=
  (sigma : ℂ) + (T : ℂ) * Complex.I

def deBruijnNewmanPolymathAlphaN (sigma T : ℝ) (n : ℕ) : ℂ :=
  deBruijnNewmanPolymathAlpha (deBruijnNewmanPolymathTermPoint sigma T) -
    (Real.log n : ℂ)

def deBruijnNewmanPolymathTermEpsilon (t T : ℝ) (alphaN : ℂ) : ℝ :=
  Real.exp
    ((t ^ 2 / 8 * ‖alphaN‖ ^ 2 + t / 4 + 1 / 6) /
      (T - 333 / 100)) - 1

def deBruijnNewmanPolymathTermMain (t sigma T : ℝ) (n : ℕ) : ℂ :=
  let s := deBruijnNewmanPolymathTermPoint sigma T
  deBruijnNewmanPolymathM t s * (deBruijnNewmanPolymathBWeight t n : ℂ) /
    (n : ℂ) ^ (s + ((t / 2 : ℝ) : ℂ) * deBruijnNewmanPolymathAlpha s)

def deBruijnNewmanPolymathTermDisplacement
    (sigma T t : ℝ) (n : ℕ) (y : ℝ) : ℂ :=
  ((Real.sqrt t * y : ℝ) : ℂ) +
    ((t / 2 : ℝ) : ℂ) * deBruijnNewmanPolymathAlphaN sigma T n

def deBruijnNewmanPolymathTermLinePoint
    (sigma T t : ℝ) (n : ℕ) (y u : ℝ) : ℂ :=
  deBruijnNewmanPolymathTermPoint sigma T +
    (u : ℂ) * deBruijnNewmanPolymathTermDisplacement sigma T t n y

def deBruijnNewmanPolymathPrefactorError (s : ℂ) : ℂ :=
  Complex.log
    (deBruijnNewmanRiemannSiegelPrefactor s /
      deBruijnNewmanPolymathM0 s)

def deBruijnNewmanPolymathGammaStirlingMain (z : ℂ) : ℂ :=
  (Real.sqrt (2 * Real.pi) : ℂ) *
    Complex.exp ((z - 1 / 2) * Complex.log z - z)

def deBruijnNewmanPolymathGammaStirlingR2 (z : ℂ) : ℂ :=
  Complex.Gamma z / deBruijnNewmanPolymathGammaStirlingMain z -
    1 - 1 / (12 * z)

@[simp] theorem deBruijnNewmanPolymathTermPoint_re (sigma T : ℝ) :
    (deBruijnNewmanPolymathTermPoint sigma T).re = sigma := by
  simp [deBruijnNewmanPolymathTermPoint]

@[simp] theorem deBruijnNewmanPolymathTermPoint_im (sigma T : ℝ) :
    (deBruijnNewmanPolymathTermPoint sigma T).im = T := by
  simp [deBruijnNewmanPolymathTermPoint]

/-- The source `log M_0` branch has derivative `alpha` off the real axis. -/
theorem deBruijnNewmanPolymathLogM0_hasDerivAt_of_im_ne_zero
    {s : ℂ} (hs : s.im ≠ 0) :
    HasDerivAt deBruijnNewmanPolymathLogM0
      (deBruijnNewmanPolymathAlpha s) s := by
  have hsSlit : s ∈ Complex.slitPlane := Or.inr hs
  have hsSubSlit : s - 1 ∈ Complex.slitPlane := by
    right
    simpa using hs
  have hsHalfSlit : s / 2 ∈ Complex.slitPlane := by
    right
    have him : (s / 2).im = s.im / 2 := by simp
    rw [him]
    exact div_ne_zero hs (by norm_num)
  have hhalf : HasDerivAt (fun z : ℂ => z / 2) (1 / 2) s := by
    simpa using (hasDerivAt_id s).div_const (2 : ℂ)
  have hlogS := Complex.hasDerivAt_log hsSlit
  have hlogSub := ((hasDerivAt_id s).sub_const 1).clog hsSubSlit
  have hlogHalf := hhalf.clog hsHalfSlit
  have hpi := hhalf.mul_const (Real.log Real.pi : ℂ)
  have hconst : HasDerivAt
      (fun _ : ℂ => Complex.log (((Real.sqrt (2 * Real.pi) / 16 : ℝ) : ℂ))) 0 s :=
    hasDerivAt_const s _
  have hlinear := hhalf.sub_const (1 / 2 : ℂ)
  have hproduct := hlinear.mul hlogHalf
  have h := ((((hlogS.add hlogSub).sub hpi).add hconst).add hproduct).sub hhalf
  have hs0 : s ≠ 0 := Complex.slitPlane_ne_zero hsSlit
  have hs1 : s - 1 ≠ 0 := Complex.slitPlane_ne_zero hsSubSlit
  have hcoeff :
      s⁻¹ + 1 / (s - 1) - 1 / 2 * (Real.log Real.pi : ℂ) + 0 +
            (1 / 2 * Complex.log (s / 2) +
              (s / 2 - 1 / 2) * (1 / 2 / (s / 2))) - 1 / 2 =
        deBruijnNewmanPolymathAlpha s := by
    simp only [deBruijnNewmanPolymathAlpha]
    field_simp [hs0, hs1]
    ring
  simp only [id_eq] at h
  rw [hcoeff] at h
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  intro z
  rfl

/-- The compact source formula for `alpha`, valid off the real axis. -/
theorem deBruijnNewmanPolymathAlpha_eq_compact_of_im_ne_zero
    {s : ℂ} (hs : s.im ≠ 0) :
    deBruijnNewmanPolymathAlpha s =
      1 / (2 * s) + 1 / (s - 1) +
        Complex.log (s / (2 * Real.pi)) / 2 := by
  have hs0 : s ≠ 0 := by
    intro h
    apply hs
    simpa using congrArg Complex.im h
  have hhalf0 : s / 2 ≠ 0 := div_ne_zero hs0 (by norm_num)
  have hpi : 0 < (1 / Real.pi : ℝ) := one_div_pos.mpr Real.pi_pos
  have hlog := Complex.log_ofReal_mul hpi hhalf0
  have harg : ((1 / Real.pi : ℝ) : ℂ) * (s / 2) = s / (2 * Real.pi) := by
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [harg] at hlog
  have hlogInv : Real.log (1 / Real.pi) = -Real.log Real.pi := by
    rw [one_div, Real.log_inv]
  rw [hlogInv] at hlog
  push_cast at hlog
  rw [deBruijnNewmanPolymathAlpha, hlog]
  field_simp [hs0]
  ring

def deBruijnNewmanPolymathAlphaPrime (s : ℂ) : ℂ :=
  -(1 / (2 * s ^ 2)) - 1 / (s - 1) ^ 2 + 1 / (2 * s)

/-- Equation `(alpha-deriv)` on the nonreal domain used by Proposition 6.1. -/
theorem deBruijnNewmanPolymathAlpha_hasDerivAt
    {s : ℂ} (hs : s.im ≠ 0) :
    HasDerivAt deBruijnNewmanPolymathAlpha
      (deBruijnNewmanPolymathAlphaPrime s) s := by
  have hs0 : s ≠ 0 := by
    intro h
    apply hs
    simpa using congrArg Complex.im h
  have hs1 : s - 1 ≠ 0 := by
    intro h
    apply hs
    have := congrArg Complex.im h
    simpa using this
  have hsHalf : (s / 2).im ≠ 0 := by
    simp [hs]
  have hInvS : HasDerivAt (fun z : ℂ => 1 / z) (-(1 / s ^ 2)) s := by
    simpa only [one_div] using hasDerivAt_inv hs0
  have hInvSub : HasDerivAt (fun z : ℂ => 1 / (z - 1)) (-(1 / (s - 1) ^ 2)) s := by
    have hbase :=
      (hasDerivAt_const s (1 : ℂ)).div ((hasDerivAt_id s).sub_const 1) hs1
    simp only [id_eq, zero_mul, one_mul, zero_sub] at hbase
    have hcoeff : -(1 : ℂ) / (s - 1) ^ 2 = -(1 / (s - 1) ^ 2) := by ring
    rw [hcoeff] at hbase
    refine hbase.congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
    intro z
    simp only [Pi.div_apply, one_div]
  have hLogHalf : HasDerivAt (fun z : ℂ => Complex.log (z / 2)) (1 / s) s := by
    have hhalf : HasDerivAt (fun z : ℂ => z / 2) (1 / 2) s := by
      simpa using (hasDerivAt_id s).div_const (2 : ℂ)
    have h := hhalf.clog (Or.inr hsHalf)
    convert h using 1
    field_simp [hs0]
  have h := (((hInvS.add hInvSub).sub_const ((1 / 2 : ℂ) * Real.log Real.pi)).add
    (hLogHalf.div_const 2)).sub (hInvS.div_const 2)
  have hcoeff :
      -(1 / s ^ 2) + -(1 / (s - 1) ^ 2) + 1 / s / 2 - -(1 / s ^ 2) / 2 =
        deBruijnNewmanPolymathAlphaPrime s := by
    simp only [deBruijnNewmanPolymathAlphaPrime]
    ring
  rw [hcoeff] at h
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  intro z
  simp only [deBruijnNewmanPolymathAlpha, Pi.add_apply, Pi.sub_apply]
  ring

theorem deBruijnNewmanPolymath_norm_inv_le_inv_im
    {s : ℂ} (hs : 0 < s.im) :
    ‖s⁻¹‖ ≤ 1 / s.im := by
  rw [norm_inv]
  simpa only [one_div] using one_div_le_one_div_of_le hs (Complex.im_le_norm s)

/-- The explicit norm estimate in equation `(alpha-deriv-bound)`. -/
theorem deBruijnNewmanPolymathAlphaPrime_norm_le
    {s : ℂ} (hs : 3 < s.im) :
    ‖deBruijnNewmanPolymathAlphaPrime s‖ ≤ 1 / (2 * s.im - 6) := by
  have hsPos : 0 < s.im := by linarith
  have hsSubIm : (s - 1).im = s.im := by simp
  have hA : ‖(1 : ℂ) / (2 * s ^ 2)‖ ≤ 1 / (2 * s.im ^ 2) := by
    rw [norm_div, norm_one, norm_mul, norm_pow]
    norm_num
    have hnorm : s.im ≤ ‖s‖ := Complex.im_le_norm s
    have hnormPos : 0 < ‖s‖ := lt_of_lt_of_le hsPos hnorm
    exact inv_anti₀ (sq_pos_of_pos hsPos) (by nlinarith)
  have hB : ‖(1 : ℂ) / (s - 1) ^ 2‖ ≤ 1 / s.im ^ 2 := by
    rw [norm_div, norm_one, norm_pow]
    have hnorm : s.im ≤ ‖s - 1‖ := by
      rw [← hsSubIm]
      exact Complex.im_le_norm (s - 1)
    have hnormPos : 0 < ‖s - 1‖ := lt_of_lt_of_le hsPos hnorm
    rw [div_le_div_iff₀ (by positivity : 0 < ‖s - 1‖ ^ 2)
      (by positivity : 0 < s.im ^ 2)]
    nlinarith
  have hC : ‖(1 : ℂ) / (2 * s)‖ ≤ 1 / (2 * s.im) := by
    rw [norm_div, norm_one, norm_mul]
    norm_num
    have hnorm : s.im ≤ ‖s‖ := Complex.im_le_norm s
    have hnormPos : 0 < ‖s‖ := lt_of_lt_of_le hsPos hnorm
    exact inv_anti₀ hsPos hnorm
  have htriangle :
      ‖deBruijnNewmanPolymathAlphaPrime s‖ ≤
        ‖(1 : ℂ) / (2 * s ^ 2)‖ + ‖(1 : ℂ) / (s - 1) ^ 2‖ +
          ‖(1 : ℂ) / (2 * s)‖ := by
    unfold deBruijnNewmanPolymathAlphaPrime
    calc
      ‖-(1 / (2 * s ^ 2)) - 1 / (s - 1) ^ 2 + 1 / (2 * s)‖ ≤
          ‖-(1 / (2 * s ^ 2)) - 1 / (s - 1) ^ 2‖ + ‖(1 : ℂ) / (2 * s)‖ :=
        norm_add_le _ _
      _ ≤ (‖-(1 / (2 * s ^ 2))‖ + ‖(1 : ℂ) / (s - 1) ^ 2‖) +
          ‖(1 : ℂ) / (2 * s)‖ := by
        gcongr
        exact norm_sub_le _ _
      _ = ‖(1 : ℂ) / (2 * s ^ 2)‖ + ‖(1 : ℂ) / (s - 1) ^ 2‖ +
          ‖(1 : ℂ) / (2 * s)‖ := by rw [norm_neg]
  calc
    ‖deBruijnNewmanPolymathAlphaPrime s‖ ≤
        ‖(1 : ℂ) / (2 * s ^ 2)‖ + ‖(1 : ℂ) / (s - 1) ^ 2‖ +
          ‖(1 : ℂ) / (2 * s)‖ := htriangle
    _ ≤ 1 / (2 * s.im ^ 2) + 1 / s.im ^ 2 + 1 / (2 * s.im) := by linarith
    _ ≤ 1 / (2 * s.im - 6) := by
      have hleft : 0 < 2 * s.im ^ 2 := by positivity
      have hright : 0 < 2 * s.im - 6 := by linarith
      rw [show 1 / (2 * s.im ^ 2) + 1 / s.im ^ 2 + 1 / (2 * s.im) =
        (s.im + 3) / (2 * s.im ^ 2) by field_simp; ring]
      rw [div_le_div_iff₀ hleft hright]
      nlinarith

/-- The imaginary part of the logarithmic term in `alpha` is nonnegative in the upper half-plane. -/
theorem deBruijnNewmanPolymath_log_scaled_im_nonneg
    {s : ℂ} (hs : 0 ≤ s.im) :
    0 ≤ (Complex.log (s / (2 * Real.pi))).im := by
  rw [Complex.log_im]
  apply Complex.arg_nonneg_iff.mpr
  have hden : 0 < 2 * Real.pi := by positivity
  have him : (s / (2 * Real.pi)).im = s.im / (2 * Real.pi) := by
    rw [Complex.div_im]
    norm_num [Complex.normSq_apply]
    field_simp [Real.pi_ne_zero]
  rw [him]
  exact div_nonneg hs hden.le

/-- Source lower bound preceding equation `(iman)`. -/
theorem deBruijnNewmanPolymathAlpha_im_lower
    {s : ℂ} (hs : 0 < s.im) :
    -(1 / (2 * s.im)) - 1 / s.im ≤
      (deBruijnNewmanPolymathAlpha s).im := by
  rw [deBruijnNewmanPolymathAlpha_eq_compact_of_im_ne_zero hs.ne']
  have hnormS : s.im ^ 2 ≤ Complex.normSq s := by
    simpa [pow_two] using Complex.im_sq_le_normSq s
  have hnormSub : s.im ^ 2 ≤ Complex.normSq (s - 1) := by
    have h := Complex.im_sq_le_normSq (s - 1)
    simpa [pow_two] using h
  have hnormSPos : 0 < Complex.normSq s := Complex.normSq_pos.mpr <| by
    intro hz
    simp [hz] at hs
  have hnormSubPos : 0 < Complex.normSq (s - 1) := Complex.normSq_pos.mpr <| by
    intro hz
    have := congrArg Complex.im hz
    simp at this
    linarith
  have hfirstEq : (1 / (2 * s)).im = -s.im / (2 * Complex.normSq s) := by
    rw [one_div, Complex.inv_im]
    simp only [Complex.mul_im, Complex.normSq_mul]
    norm_num
    ring
  have hfirst : -(1 / (2 * s.im)) ≤ (1 / (2 * s)).im := by
    rw [hfirstEq]
    rw [neg_div, neg_le_neg_iff]
    have himPos : 0 < 2 * s.im := by positivity
    have hdenPos : 0 < 2 * Complex.normSq s := by positivity
    rw [div_le_div_iff₀ hdenPos himPos]
    nlinarith
  have hsecondEq : (1 / (s - 1)).im = -s.im / Complex.normSq (s - 1) := by
    rw [one_div, Complex.inv_im]
    simp
  have hsecond : -(1 / s.im) ≤ (1 / (s - 1)).im := by
    rw [hsecondEq]
    rw [neg_div, neg_le_neg_iff]
    have himPos : 0 < s.im := hs
    rw [div_le_div_iff₀ hnormSubPos himPos]
    nlinarith
  have hlog : 0 ≤ (Complex.log (s / (2 * Real.pi)) / 2).im := by
    have him : (Complex.log (s / (2 * Real.pi)) / 2).im =
        (Complex.log (s / (2 * Real.pi))).im / 2 := by
      rw [Complex.div_im]
      norm_num [Complex.normSq_apply]
      ring
    rw [him]
    exact div_nonneg (deBruijnNewmanPolymath_log_scaled_im_nonneg hs.le) (by norm_num)
  simp only [Complex.add_im]
  linarith

/-- Equation `(iman)` with the decimal source constant written as `3/20`. -/
theorem deBruijnNewmanPolymathAlphaN_im_ge_neg_three_twentieths
    (sigma T : ℝ) (n : ℕ) (hT : 10 ≤ T) :
    -(3 / 20 : ℝ) ≤ (deBruijnNewmanPolymathAlphaN sigma T n).im := by
  let s := deBruijnNewmanPolymathTermPoint sigma T
  have hsIm : s.im = T := by simp [s]
  have hsPos : 0 < s.im := by rw [hsIm]; linarith
  have hAlpha := deBruijnNewmanPolymathAlpha_im_lower hsPos
  have hrecip : -(3 / 20 : ℝ) ≤ -(1 / (2 * T)) - 1 / T := by
    have hTPos : 0 < T := by linarith
    rw [show -(1 / (2 * T)) - 1 / T = -(3 / (2 * T)) by field_simp; ring]
    rw [neg_le_neg_iff,
      div_le_div_iff₀ (by positivity : 0 < 2 * T) (by norm_num : (0 : ℝ) < 20)]
    nlinarith
  unfold deBruijnNewmanPolymathAlphaN
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero]
  rw [hsIm] at hAlpha
  linarith

/-- The saddle displacement in Proposition 6.1 remains in the strict upper half-plane. -/
theorem deBruijnNewmanPolymathTerm_sameOpenHalfPlane
    (sigma T t : ℝ) (n : ℕ) (hT : 10 ≤ T) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    deBruijnNewmanRiemannSiegelSameOpenHalfPlane
      (deBruijnNewmanPolymathTermPoint sigma T)
      (deBruijnNewmanPolymathTermPoint sigma T +
        (((t / 2 : ℝ) : ℂ) * deBruijnNewmanPolymathAlphaN sigma T n)) := by
  left
  constructor
  · simp [deBruijnNewmanPolymathTermPoint]
    linarith
  · have hAlpha := deBruijnNewmanPolymathAlphaN_im_ge_neg_three_twentieths sigma T n hT
    simp only [deBruijnNewmanPolymathTermPoint_im, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    have htHalf : t / 2 ≤ 1 / 4 := by linarith
    have htNonneg : 0 ≤ t / 2 := by positivity
    have hmul : -(3 / 80 : ℝ) ≤ t / 2 * (deBruijnNewmanPolymathAlphaN sigma T n).im := by
      have := mul_le_mul_of_nonneg_left hAlpha htNonneg
      nlinarith
    linarith

/-- Every point of the Taylor segment has the source paper's uniform imaginary lower bound. -/
theorem deBruijnNewmanPolymathTermLinePoint_im_lower
    (sigma T t : ℝ) (n : ℕ) (y u : ℝ)
    (hT : 10 ≤ T) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    T - 3 / 80 ≤
      (deBruijnNewmanPolymathTermLinePoint sigma T t n y u).im := by
  have hAlpha := deBruijnNewmanPolymathAlphaN_im_ge_neg_three_twentieths sigma T n hT
  have htNonneg : 0 ≤ t / 2 := by positivity
  have htHalf : t / 2 ≤ 1 / 4 := by linarith
  have hdisplacement :
      -(3 / 80 : ℝ) ≤
        (deBruijnNewmanPolymathTermDisplacement sigma T t n y).im := by
    simp only [deBruijnNewmanPolymathTermDisplacement, Complex.add_im,
      Complex.ofReal_im, zero_add, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero]
    have hmul := mul_le_mul_of_nonneg_left hAlpha htNonneg
    nlinarith
  have hscaled :
      -(3 / 80 : ℝ) ≤
        u * (deBruijnNewmanPolymathTermDisplacement sigma T t n y).im := by
    have hmul := mul_le_mul_of_nonneg_left hdisplacement hu0
    nlinarith
  simp only [deBruijnNewmanPolymathTermLinePoint, Complex.add_im,
    deBruijnNewmanPolymathTermPoint_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero]
  linarith

/-- Uniform form of `(alpha-deriv-bound)` on the full Taylor segment in Proposition 6.1. -/
theorem deBruijnNewmanPolymathTermLinePoint_alphaPrime_norm_le
    (sigma T t : ℝ) (n : ℕ) (y u : ℝ)
    (hT : 10 ≤ T) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖deBruijnNewmanPolymathAlphaPrime
        (deBruijnNewmanPolymathTermLinePoint sigma T t n y u)‖ ≤
      1 / (2 * (T - 77 / 25)) := by
  let z := deBruijnNewmanPolymathTermLinePoint sigma T t n y u
  have hzIm := deBruijnNewmanPolymathTermLinePoint_im_lower
    sigma T t n y u hT ht0 ht1 hu0 hu1
  have hzThree : 3 < z.im := by dsimp [z]; norm_num at *; linarith
  have hpoint := deBruijnNewmanPolymathAlphaPrime_norm_le hzThree
  have htargetPos : 0 < 2 * (T - 77 / 25) := by norm_num at *; linarith
  have hpointPos : 0 < 2 * z.im - 6 := by linarith
  have hden : 2 * (T - 77 / 25) ≤ 2 * z.im - 6 := by
    dsimp [z] at hzIm ⊢
    norm_num at *
    linarith
  exact hpoint.trans (div_le_div_of_nonneg_left zero_le_one htargetPos hden)

theorem deBruijnNewmanPolymathTerm_lineMap_eq_linePoint
    (sigma T t : ℝ) (n : ℕ) (y u : ℝ) :
    AffineMap.lineMap
        (deBruijnNewmanPolymathTermPoint sigma T)
        (deBruijnNewmanPolymathTermPoint sigma T +
          deBruijnNewmanPolymathTermDisplacement sigma T t n y) u =
      deBruijnNewmanPolymathTermLinePoint sigma T t n y u := by
  rw [AffineMap.lineMap_apply_module]
  simp only [deBruijnNewmanPolymathTermLinePoint, Complex.real_smul]
  push_cast
  ring

/-- `alpha` is uniformly Lipschitz along the Taylor segment, with the exact constant used in
the source proof before the second-order integration step. -/
theorem deBruijnNewmanPolymathTerm_alpha_sub_le
    (sigma T t : ℝ) (n : ℕ) (y : ℝ)
    (hT : 10 ≤ T) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    ‖deBruijnNewmanPolymathAlpha
          (deBruijnNewmanPolymathTermPoint sigma T +
            deBruijnNewmanPolymathTermDisplacement sigma T t n y) -
        deBruijnNewmanPolymathAlpha
          (deBruijnNewmanPolymathTermPoint sigma T)‖ ≤
      (1 / (2 * (T - 77 / 25))) *
        ‖deBruijnNewmanPolymathTermDisplacement sigma T t n y‖ := by
  let s := deBruijnNewmanPolymathTermPoint sigma T
  let d := deBruijnNewmanPolymathTermDisplacement sigma T t n y
  let e := s + d
  have hderiv : ∀ z ∈ segment ℝ s e,
      HasDerivWithinAt deBruijnNewmanPolymathAlpha
        (deBruijnNewmanPolymathAlphaPrime z) (segment ℝ s e) z := by
    intro z hz
    rw [segment_eq_image_lineMap] at hz
    rcases hz with ⟨u, hu, rfl⟩
    have hline := deBruijnNewmanPolymathTermLinePoint_im_lower
      sigma T t n y u hT ht0 ht1 hu.1 hu.2
    have him :
        (AffineMap.lineMap s e u).im ≠ 0 := by
      rw [show AffineMap.lineMap s e u =
        deBruijnNewmanPolymathTermLinePoint sigma T t n y u by
          dsimp [s, e, d]
          exact deBruijnNewmanPolymathTerm_lineMap_eq_linePoint sigma T t n y u]
      norm_num at hline ⊢
      linarith
    exact (deBruijnNewmanPolymathAlpha_hasDerivAt him).hasDerivWithinAt
  have hbound : ∀ z ∈ segment ℝ s e,
      ‖deBruijnNewmanPolymathAlphaPrime z‖ ≤
        1 / (2 * (T - 77 / 25)) := by
    intro z hz
    rw [segment_eq_image_lineMap] at hz
    rcases hz with ⟨u, hu, rfl⟩
    rw [show AffineMap.lineMap s e u =
      deBruijnNewmanPolymathTermLinePoint sigma T t n y u by
        dsimp [s, e, d]
        exact deBruijnNewmanPolymathTerm_lineMap_eq_linePoint sigma T t n y u]
    exact deBruijnNewmanPolymathTermLinePoint_alphaPrime_norm_le
      sigma T t n y u hT ht0 ht1 hu.1 hu.2
  have h := (convex_segment s e).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound (left_mem_segment ℝ s e) (right_mem_segment ℝ s e)
  simpa [s, d, e] using h

/-- Parameterized version of the `alpha` Lipschitz estimate along the Taylor segment. -/
theorem deBruijnNewmanPolymathTerm_alpha_linePoint_sub_le
    (sigma T t : ℝ) (n : ℕ) (y u : ℝ)
    (hT : 10 ≤ T) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖deBruijnNewmanPolymathAlpha
          (deBruijnNewmanPolymathTermLinePoint sigma T t n y u) -
        deBruijnNewmanPolymathAlpha
          (deBruijnNewmanPolymathTermPoint sigma T)‖ ≤
      (1 / (2 * (T - 77 / 25))) *
        (u * ‖deBruijnNewmanPolymathTermDisplacement sigma T t n y‖) := by
  let s := deBruijnNewmanPolymathTermPoint sigma T
  let d := deBruijnNewmanPolymathTermDisplacement sigma T t n y
  let e := s + d
  let p := deBruijnNewmanPolymathTermLinePoint sigma T t n y u
  have hderiv : ∀ z ∈ segment ℝ s e,
      HasDerivWithinAt deBruijnNewmanPolymathAlpha
        (deBruijnNewmanPolymathAlphaPrime z) (segment ℝ s e) z := by
    intro z hz
    rw [segment_eq_image_lineMap] at hz
    rcases hz with ⟨v, hv, rfl⟩
    have hline := deBruijnNewmanPolymathTermLinePoint_im_lower
      sigma T t n y v hT ht0 ht1 hv.1 hv.2
    have him :
        (AffineMap.lineMap s e v).im ≠ 0 := by
      rw [show AffineMap.lineMap s e v =
        deBruijnNewmanPolymathTermLinePoint sigma T t n y v by
          dsimp [s, e, d]
          exact deBruijnNewmanPolymathTerm_lineMap_eq_linePoint sigma T t n y v]
      norm_num at hline ⊢
      linarith
    exact (deBruijnNewmanPolymathAlpha_hasDerivAt him).hasDerivWithinAt
  have hbound : ∀ z ∈ segment ℝ s e,
      ‖deBruijnNewmanPolymathAlphaPrime z‖ ≤
        1 / (2 * (T - 77 / 25)) := by
    intro z hz
    rw [segment_eq_image_lineMap] at hz
    rcases hz with ⟨v, hv, rfl⟩
    rw [show AffineMap.lineMap s e v =
      deBruijnNewmanPolymathTermLinePoint sigma T t n y v by
        dsimp [s, e, d]
        exact deBruijnNewmanPolymathTerm_lineMap_eq_linePoint sigma T t n y v]
    exact deBruijnNewmanPolymathTermLinePoint_alphaPrime_norm_le
      sigma T t n y v hT ht0 ht1 hv.1 hv.2
  have hp : p ∈ segment ℝ s e := by
    rw [show p = AffineMap.lineMap s e u by
      dsimp [p, s, e, d]
      exact (deBruijnNewmanPolymathTerm_lineMap_eq_linePoint sigma T t n y u).symm]
    exact lineMap_mem_segment ℝ s e ⟨hu0, hu1⟩
  have h := (convex_segment s e).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound (left_mem_segment ℝ s e) hp
  have hnorm : ‖p - s‖ = u * ‖d‖ := by
    dsimp [p, s, d]
    simp only [deBruijnNewmanPolymathTermLinePoint, add_sub_cancel_left,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
  rw [hnorm] at h
  simpa [p, s, d] using h

theorem deBruijnNewmanPolymathTermLinePoint_hasDerivAt
    (sigma T t : ℝ) (n : ℕ) (y u : ℝ) :
    HasDerivAt
      (fun v : ℝ => deBruijnNewmanPolymathTermLinePoint sigma T t n y v)
      (deBruijnNewmanPolymathTermDisplacement sigma T t n y) u := by
  have h := (((hasDerivAt_id u).ofReal_comp.mul_const
    (deBruijnNewmanPolymathTermDisplacement sigma T t n y)).const_add
      (deBruijnNewmanPolymathTermPoint sigma T))
  simpa [deBruijnNewmanPolymathTermLinePoint] using h

theorem deBruijnNewmanPolymathTerm_alphaLine_hasDerivAt
    (sigma T t : ℝ) (n : ℕ) (y u : ℝ)
    (hT : 10 ≤ T) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    HasDerivAt
      (fun v : ℝ => deBruijnNewmanPolymathAlpha
        (deBruijnNewmanPolymathTermLinePoint sigma T t n y v))
      (deBruijnNewmanPolymathAlphaPrime
          (deBruijnNewmanPolymathTermLinePoint sigma T t n y u) *
        deBruijnNewmanPolymathTermDisplacement sigma T t n y) u := by
  have hline := deBruijnNewmanPolymathTermLinePoint_im_lower
    sigma T t n y u hT ht0 ht1 hu0 hu1
  have him :
      (deBruijnNewmanPolymathTermLinePoint sigma T t n y u).im ≠ 0 := by
    norm_num at hline ⊢
    linarith
  have hout := deBruijnNewmanPolymathAlpha_hasDerivAt him
  change HasDerivAt
    (deBruijnNewmanPolymathAlpha ∘
      fun v : ℝ => deBruijnNewmanPolymathTermLinePoint sigma T t n y v)
    _ u
  simpa only [smul_eq_mul, mul_comm] using hout.scomp u
    (deBruijnNewmanPolymathTermLinePoint_hasDerivAt sigma T t n y u)

theorem deBruijnNewmanPolymathTerm_logM0Line_hasDerivAt
    (sigma T t : ℝ) (n : ℕ) (y u : ℝ)
    (hT : 10 ≤ T) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    HasDerivAt
      (fun v : ℝ => deBruijnNewmanPolymathLogM0
        (deBruijnNewmanPolymathTermLinePoint sigma T t n y v))
      (deBruijnNewmanPolymathAlpha
          (deBruijnNewmanPolymathTermLinePoint sigma T t n y u) *
        deBruijnNewmanPolymathTermDisplacement sigma T t n y) u := by
  have hline := deBruijnNewmanPolymathTermLinePoint_im_lower
    sigma T t n y u hT ht0 ht1 hu0 hu1
  have him :
      (deBruijnNewmanPolymathTermLinePoint sigma T t n y u).im ≠ 0 := by
    norm_num at hline ⊢
    linarith
  have hout := deBruijnNewmanPolymathLogM0_hasDerivAt_of_im_ne_zero him
  change HasDerivAt
    (deBruijnNewmanPolymathLogM0 ∘
      fun v : ℝ => deBruijnNewmanPolymathTermLinePoint sigma T t n y v)
    _ u
  simpa only [smul_eq_mul, mul_comm] using hout.scomp u
    (deBruijnNewmanPolymathTermLinePoint_hasDerivAt sigma T t n y u)

/-- The explicit second-order Taylor remainder for `log M_0` used in Proposition 6.1. -/
theorem deBruijnNewmanPolymathTerm_logM0_taylor_remainder_le
    (sigma T t : ℝ) (n : ℕ) (y : ℝ)
    (hT : 10 ≤ T) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    ‖deBruijnNewmanPolymathLogM0
          (deBruijnNewmanPolymathTermLinePoint sigma T t n y 1) -
        deBruijnNewmanPolymathLogM0
          (deBruijnNewmanPolymathTermPoint sigma T) -
        deBruijnNewmanPolymathAlpha
            (deBruijnNewmanPolymathTermPoint sigma T) *
          deBruijnNewmanPolymathTermDisplacement sigma T t n y‖ ≤
      ‖deBruijnNewmanPolymathTermDisplacement sigma T t n y‖ ^ 2 /
        (4 * (T - 77 / 25)) := by
  let s := deBruijnNewmanPolymathTermPoint sigma T
  let d := deBruijnNewmanPolymathTermDisplacement sigma T t n y
  let line : ℝ → ℂ := fun u => deBruijnNewmanPolymathTermLinePoint sigma T t n y u
  let C : ℝ := 1 / (2 * (T - 77 / 25))
  have hlogDeriv : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun v => deBruijnNewmanPolymathLogM0 (line v))
        (deBruijnNewmanPolymathAlpha (line u) * d) u := by
    intro u hu
    dsimp [line, d]
    exact deBruijnNewmanPolymathTerm_logM0Line_hasDerivAt
      sigma T t n y u hT ht0 ht1 hu.1 hu.2
  have halphaDeriv : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun v => deBruijnNewmanPolymathAlpha (line v))
        (deBruijnNewmanPolymathAlphaPrime (line u) * d) u := by
    intro u hu
    dsimp [line, d]
    exact deBruijnNewmanPolymathTerm_alphaLine_hasDerivAt
      sigma T t n y u hT ht0 ht1 hu.1 hu.2
  have hcont : ContinuousOn
      (fun u => deBruijnNewmanPolymathAlpha (line u) * d)
      (Set.Icc (0 : ℝ) 1) := by
    intro u hu
    change ContinuousWithinAt
      ((fun v => deBruijnNewmanPolymathAlpha (line v)) * (fun _ : ℝ => d))
      (Set.Icc (0 : ℝ) 1) u
    exact ((halphaDeriv u hu).continuousAt.mul
      (continuousAt_const : ContinuousAt (fun _ : ℝ => d) u)).continuousWithinAt
  have hint : IntervalIntegrable
      (fun u => deBruijnNewmanPolymathAlpha (line u) * d) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le zero_le_one] using hcont
  have hftc :
      (∫ u : ℝ in 0..1, deBruijnNewmanPolymathAlpha (line u) * d) =
        deBruijnNewmanPolymathLogM0 (line 1) -
          deBruijnNewmanPolymathLogM0 (line 0) := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun v => deBruijnNewmanPolymathLogM0 (line v))
      (f' := fun u => deBruijnNewmanPolymathAlpha (line u) * d)
      (fun u hu => hlogDeriv u (by simpa [uIcc_of_le zero_le_one] using hu)) hint
  have hconstInt : IntervalIntegrable
      (fun _ : ℝ => deBruijnNewmanPolymathAlpha s * d) volume 0 1 :=
    intervalIntegrable_const
  have hrepr :
      deBruijnNewmanPolymathLogM0 (line 1) -
          deBruijnNewmanPolymathLogM0 s -
          deBruijnNewmanPolymathAlpha s * d =
        ∫ u : ℝ in 0..1,
          (deBruijnNewmanPolymathAlpha (line u) -
            deBruijnNewmanPolymathAlpha s) * d := by
    have hlineZero : line 0 = s := by
      dsimp [line, s]
      simp [deBruijnNewmanPolymathTermLinePoint]
    calc
      deBruijnNewmanPolymathLogM0 (line 1) -
            deBruijnNewmanPolymathLogM0 s -
            deBruijnNewmanPolymathAlpha s * d =
          (∫ u : ℝ in 0..1, deBruijnNewmanPolymathAlpha (line u) * d) -
            (∫ _u : ℝ in 0..1, deBruijnNewmanPolymathAlpha s * d) := by
              rw [hftc, hlineZero]
              simp
      _ = ∫ u : ℝ in 0..1,
          (deBruijnNewmanPolymathAlpha (line u) * d -
            deBruijnNewmanPolymathAlpha s * d) := by
              rw [intervalIntegral.integral_sub hint hconstInt]
      _ = ∫ u : ℝ in 0..1,
          (deBruijnNewmanPolymathAlpha (line u) -
            deBruijnNewmanPolymathAlpha s) * d := by
              congr 1
              funext u
              ring
  let g : ℝ → ℝ := fun u => C * u * ‖d‖ ^ 2
  have hgint : IntervalIntegrable g volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hpointwise : ∀ u ∈ Set.Ioc (0 : ℝ) 1,
      ‖(deBruijnNewmanPolymathAlpha (line u) -
          deBruijnNewmanPolymathAlpha s) * d‖ ≤ g u := by
    intro u hu
    have halpha := deBruijnNewmanPolymathTerm_alpha_linePoint_sub_le
      sigma T t n y u hT ht0 ht1 hu.1.le hu.2
    change ‖(deBruijnNewmanPolymathAlpha (line u) -
      deBruijnNewmanPolymathAlpha s) * d‖ ≤ g u
    rw [norm_mul]
    calc
      ‖deBruijnNewmanPolymathAlpha (line u) -
            deBruijnNewmanPolymathAlpha s‖ * ‖d‖ ≤
          (C * (u * ‖d‖)) * ‖d‖ :=
        mul_le_mul_of_nonneg_right (by simpa [C, line, s, d] using halpha) (norm_nonneg d)
      _ = g u := by dsimp [g]; ring
  have hnormIntegral := intervalIntegral.norm_integral_le_of_norm_le
    (μ := volume) (f := fun u : ℝ =>
      (deBruijnNewmanPolymathAlpha (line u) -
        deBruijnNewmanPolymathAlpha s) * d)
    (g := g) zero_le_one (ae_of_all _ fun u hu => hpointwise u hu) hgint
  have hgeval : (∫ u : ℝ in 0..1, g u) = C / 2 * ‖d‖ ^ 2 := by
    calc
      (∫ u : ℝ in 0..1, g u) =
          ∫ u : ℝ in 0..1, (C * ‖d‖ ^ 2) * u := by
            congr 1
            funext u
            dsimp [g]
            ring
      _ = (C * ‖d‖ ^ 2) * (∫ u : ℝ in 0..1, u) := by
            rw [intervalIntegral.integral_const_mul]
      _ = C / 2 * ‖d‖ ^ 2 := by
            rw [integral_id]
            norm_num
            ring
  calc
    ‖deBruijnNewmanPolymathLogM0
          (deBruijnNewmanPolymathTermLinePoint sigma T t n y 1) -
        deBruijnNewmanPolymathLogM0
          (deBruijnNewmanPolymathTermPoint sigma T) -
        deBruijnNewmanPolymathAlpha
            (deBruijnNewmanPolymathTermPoint sigma T) *
          deBruijnNewmanPolymathTermDisplacement sigma T t n y‖ =
        ‖∫ u : ℝ in 0..1,
            (deBruijnNewmanPolymathAlpha (line u) -
            deBruijnNewmanPolymathAlpha s) * d‖ := by
      rw [← hrepr]
    _ ≤ ∫ u : ℝ in 0..1, g u := hnormIntegral
    _ = C / 2 * ‖d‖ ^ 2 := hgeval
    _ = ‖deBruijnNewmanPolymathTermDisplacement sigma T t n y‖ ^ 2 /
        (4 * (T - 77 / 25)) := by
      have hden : T - 77 / 25 ≠ 0 := by norm_num at *; linarith
      dsimp [C, d]
      field_simp [hden]
      all_goals ring

/-- The displacement estimate immediately following the Taylor expansion in Proposition 6.1. -/
theorem deBruijnNewmanPolymathTermDisplacement_norm_sq_le
    (sigma T t : ℝ) (n : ℕ) (y : ℝ) (ht0 : 0 ≤ t) :
    ‖deBruijnNewmanPolymathTermDisplacement sigma T t n y‖ ^ 2 ≤
      2 * t * y ^ 2 + t ^ 2 / 2 *
        ‖deBruijnNewmanPolymathAlphaN sigma T n‖ ^ 2 := by
  let a : ℂ := ((Real.sqrt t * y : ℝ) : ℂ)
  let b : ℂ := ((t / 2 : ℝ) : ℂ) * deBruijnNewmanPolymathAlphaN sigma T n
  have htriangle : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
  have hsq : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := by
    nlinarith [norm_nonneg (a + b), norm_nonneg a, norm_nonneg b]
  have htwo : (‖a‖ + ‖b‖) ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
    nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  calc
    ‖deBruijnNewmanPolymathTermDisplacement sigma T t n y‖ ^ 2 =
        ‖a + b‖ ^ 2 := by rfl
    _ ≤ (‖a‖ + ‖b‖) ^ 2 := hsq
    _ ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := htwo
    _ = 2 * t * y ^ 2 + t ^ 2 / 2 *
        ‖deBruijnNewmanPolymathAlphaN sigma T n‖ ^ 2 := by
      dsimp [a, b]
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg t),
        abs_of_nonneg (by positivity : 0 ≤ t / 2)]
      calc
        2 * (Real.sqrt t * |y|) ^ 2 +
              2 * (t / 2 * ‖deBruijnNewmanPolymathAlphaN sigma T n‖) ^ 2 =
            2 * (Real.sqrt t) ^ 2 * |y| ^ 2 +
              2 * (t / 2) ^ 2 *
                ‖deBruijnNewmanPolymathAlphaN sigma T n‖ ^ 2 := by ring
        _ = 2 * t * y ^ 2 + t ^ 2 / 2 *
              ‖deBruijnNewmanPolymathAlphaN sigma T n‖ ^ 2 := by
          rw [Real.sq_sqrt ht0, sq_abs]
          ring

/-- Exact algebraic identification of the central factor with the source `M_t b_n^t / n^(...)`
main term. -/
theorem deBruijnNewmanPolymathTermMain_eq
    (sigma T t : ℝ) (n : ℕ) (hn : 0 < n) :
    deBruijnNewmanPolymathM0 (deBruijnNewmanPolymathTermPoint sigma T) *
        Complex.exp
          (((t / 4 : ℝ) : ℂ) *
              deBruijnNewmanPolymathAlphaN sigma T n ^ 2 -
            deBruijnNewmanPolymathTermPoint sigma T * (Real.log n : ℂ)) =
      deBruijnNewmanPolymathTermMain t sigma T n := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    simp
  rw [deBruijnNewmanPolymathTermMain]
  simp only [deBruijnNewmanPolymathM, deBruijnNewmanPolymathBWeight,
    deBruijnNewmanPolymathAlphaN]
  rw [Complex.cpow_def_of_ne_zero hnC, hlog]
  simp only [div_eq_mul_inv]
  rw [← Complex.exp_neg, Complex.ofReal_exp]
  push_cast
  have hexponent :
      (t : ℂ) * 4⁻¹ *
            (deBruijnNewmanPolymathAlpha
                (deBruijnNewmanPolymathTermPoint sigma T) -
              Complex.log (n : ℂ)) ^ 2 -
          deBruijnNewmanPolymathTermPoint sigma T * Complex.log (n : ℂ) =
        (t : ℂ) * 4⁻¹ *
            deBruijnNewmanPolymathAlpha
              (deBruijnNewmanPolymathTermPoint sigma T) ^ 2 +
          (t : ℂ) * 4⁻¹ * Complex.log (n : ℂ) ^ 2 +
          -(Complex.log (n : ℂ) *
            (deBruijnNewmanPolymathTermPoint sigma T +
              (t : ℂ) * 2⁻¹ *
                deBruijnNewmanPolymathAlpha
                  (deBruijnNewmanPolymathTermPoint sigma T))) := by
    ring
  rw [hexponent, Complex.exp_add, Complex.exp_add]
  ring

theorem deBruijnNewmanRiemannSiegelPrefactor_ne_zero_of_im_ne_zero
    {s : ℂ} (hs : s.im ≠ 0) :
    deBruijnNewmanRiemannSiegelPrefactor s ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro h
    apply hs
    simpa using congrArg Complex.im h
  have hs1 : s ≠ 1 := by
    intro h
    apply hs
    simpa using congrArg Complex.im h
  have hsHalfIm : (s / 2).im ≠ 0 := by
    simp [hs]
  have hgamma : Complex.Gamma (s / 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m h
    apply hsHalfIm
    have him := congrArg Complex.im h
    simpa using him
  have hpi : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr <| Or.inl <|
      Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [deBruijnNewmanRiemannSiegelPrefactor]
  exact mul_ne_zero
    (mul_ne_zero
      (mul_ne_zero (by norm_num)
        (div_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) (by norm_num)))
      hpi)
    hgamma

/-- Exact principal-log error factor for the completed-zeta prefactor. The open Boyd obligation is
now solely a norm bound on `deBruijnNewmanPolymathPrefactorError`. -/
theorem deBruijnNewmanRiemannSiegelPrefactor_eq_M0_mul_exp_error
    {s : ℂ} (hs : s.im ≠ 0) :
    deBruijnNewmanRiemannSiegelPrefactor s =
      deBruijnNewmanPolymathM0 s *
        Complex.exp (deBruijnNewmanPolymathPrefactorError s) := by
  have hs0 : s ≠ 0 := by
    intro h
    apply hs
    simpa using congrArg Complex.im h
  have hs1 : s ≠ 1 := by
    intro h
    apply hs
    simpa using congrArg Complex.im h
  have hM0 := deBruijnNewmanPolymathM0_ne_zero hs0 hs1
  have hpref := deBruijnNewmanRiemannSiegelPrefactor_ne_zero_of_im_ne_zero hs
  have hratio :
      deBruijnNewmanRiemannSiegelPrefactor s /
        deBruijnNewmanPolymathM0 s ≠ 0 := div_ne_zero hpref hM0
  unfold deBruijnNewmanPolymathPrefactorError
  rw [Complex.exp_log hratio]
  field_simp [hM0]

/-- The actual positive-index residue with its sole effective-Stirling error exposed exactly. -/
theorem deBruijnNewmanRiemannSiegelR0Term_eq_M0_mul_cpow_mul_exp_error
    {n : ℕ} {s : ℂ} (hs : s.im ≠ 0) :
    deBruijnNewmanRiemannSiegelR0Term n s =
      deBruijnNewmanPolymathM0 s * (n : ℂ) ^ (-s) *
        Complex.exp (deBruijnNewmanPolymathPrefactorError s) := by
  rw [deBruijnNewmanRiemannSiegelR0Term,
    deBruijnNewmanRiemannSiegelPrefactor_eq_M0_mul_exp_error hs]
  ring

/-- The exposed prefactor error is exactly the relative Stirling error of `Gamma(s/2)`. -/
theorem deBruijnNewmanRiemannSiegelPrefactor_div_M0_eq_gamma_div_stirlingMain
    {s : ℂ} (hs : s.im ≠ 0) :
    deBruijnNewmanRiemannSiegelPrefactor s /
        deBruijnNewmanPolymathM0 s =
      Complex.Gamma (s / 2) /
        deBruijnNewmanPolymathGammaStirlingMain (s / 2) := by
  have hs0 : s ≠ 0 := by
    intro h
    apply hs
    simpa using congrArg Complex.im h
  have hs1 : s ≠ 1 := by
    intro h
    apply hs
    simpa using congrArg Complex.im h
  have hpiC : (Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hsqrt : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr <| ne_of_gt <| Real.sqrt_pos.2 <| by positivity
  rw [deBruijnNewmanRiemannSiegelPrefactor, deBruijnNewmanPolymathM0,
    deBruijnNewmanPolymathGammaStirlingMain,
    Complex.cpow_def_of_ne_zero hpiC, Complex.ofReal_log Real.pi_pos.le]
  field_simp [hs0, sub_ne_zero.mpr hs1, hsqrt, Complex.exp_ne_zero]

theorem deBruijnNewmanPolymathPrefactorError_eq_log_gamma_div_stirlingMain
    {s : ℂ} (hs : s.im ≠ 0) :
    deBruijnNewmanPolymathPrefactorError s =
      Complex.log
        (Complex.Gamma (s / 2) /
          deBruijnNewmanPolymathGammaStirlingMain (s / 2)) := by
  unfold deBruijnNewmanPolymathPrefactorError
  rw [deBruijnNewmanRiemannSiegelPrefactor_div_M0_eq_gamma_div_stirlingMain hs]

/-- Polymath Lemma 5.1(ii): a relative error of size `1/x` gives a principal-log error of
size `1/(x-1)`. -/
theorem norm_log_one_add_le_inv_sub_one
    {e : ℂ} {x : ℝ} (hx : 1 < x) (he : ‖e‖ ≤ 1 / x) :
    ‖Complex.log (1 + e)‖ ≤ 1 / (x - 1) := by
  have hx0 : 0 < x := by linarith
  have herx : ‖e‖ * x ≤ 1 := by
    calc
      ‖e‖ * x ≤ (1 / x) * x := mul_le_mul_of_nonneg_right he hx0.le
      _ = 1 := by field_simp [hx0.ne']
  have he1 : ‖e‖ < 1 := by
    have hinv : 1 / x < 1 := by
      rw [div_lt_one hx0]
      exact hx
    exact he.trans_lt hinv
  have hdenE : 0 < 1 - ‖e‖ := sub_pos.mpr he1
  have hdenX : 0 < x - 1 := sub_pos.mpr hx
  have hlog := Complex.norm_log_one_add_le he1
  let q : ℝ := ‖e‖ ^ 2 * (1 - ‖e‖)⁻¹
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hhalf : q / 2 ≤ q := div_le_self hq0 (by norm_num)
  have hfirst :
      ‖e‖ ^ 2 * (1 - ‖e‖)⁻¹ / 2 + ‖e‖ ≤
        ‖e‖ / (1 - ‖e‖) := by
    calc
      ‖e‖ ^ 2 * (1 - ‖e‖)⁻¹ / 2 + ‖e‖ ≤ q + ‖e‖ := by
        dsimp [q] at hhalf ⊢
        linarith
      _ = ‖e‖ / (1 - ‖e‖) := by
        dsimp [q]
        field_simp [hdenE.ne']
        ring
  have hsecond : ‖e‖ / (1 - ‖e‖) ≤ 1 / (x - 1) := by
    rw [div_le_div_iff₀ hdenE hdenX]
    nlinarith
  exact hlog.trans (hfirst.trans hsecond)

/-- The complete `0.246 -> 0.33` conversion in Polymath Lemma 5.1(v). Only the Boyd relative
Stirling witness remains as a hypothesis. -/
theorem deBruijnNewmanPolymathPrefactorError_norm_le_of_relative_stirling
    {s e : ℂ} (hs : s.im ≠ 0) (hsNorm : 1 ≤ ‖s / 2‖)
    (hrelative :
      Complex.Gamma (s / 2) /
          deBruijnNewmanPolymathGammaStirlingMain (s / 2) = 1 + e)
    (he : ‖e‖ ≤ 1 / (12 * (‖s / 2‖ - 123 / 500))) :
    ‖deBruijnNewmanPolymathPrefactorError s‖ ≤
      1 / (12 * (‖s / 2‖ - 33 / 100)) := by
  let x : ℝ := 12 * (‖s / 2‖ - 123 / 500)
  have hx : 1 < x := by dsimp [x]; norm_num at *; linarith
  have hlog := norm_log_one_add_le_inv_sub_one hx (by simpa [x] using he)
  have herror :
      deBruijnNewmanPolymathPrefactorError s = Complex.log (1 + e) := by
    rw [deBruijnNewmanPolymathPrefactorError_eq_log_gamma_div_stirlingMain hs,
      hrelative]
  rw [herror]
  have htargetPos : 0 < 12 * (‖s / 2‖ - 33 / 100) := by
    norm_num at *
    linarith
  have hxPos : 0 < x - 1 := by linarith
  have hden : 12 * (‖s / 2‖ - 33 / 100) ≤ x - 1 := by
    dsimp [x]
    norm_num
    linarith
  exact hlog.trans (div_le_div_of_nonneg_left zero_le_one htargetPos hden)

/-- The arithmetic step from Boyd's `R_2` bound `0.0205/|z|^2` to the relative-error radius
`1/(12(|z|-0.246))`. -/
theorem deBruijnNewmanPolymath_relative_stirling_of_R2_bound
    {z : ℂ} (hzNorm : 1 ≤ ‖z‖)
    (hR2 : ‖deBruijnNewmanPolymathGammaStirlingR2 z‖ ≤
      (41 / 2000 : ℝ) / ‖z‖ ^ 2) :
    ∃ e : ℂ,
      Complex.Gamma z / deBruijnNewmanPolymathGammaStirlingMain z = 1 + e ∧
      ‖e‖ ≤ 1 / (12 * (‖z‖ - 123 / 500)) := by
  let e : ℂ := 1 / (12 * z) + deBruijnNewmanPolymathGammaStirlingR2 z
  refine ⟨e, ?_, ?_⟩
  · dsimp [e, deBruijnNewmanPolymathGammaStirlingR2]
    ring
  · have hzPos : 0 < ‖z‖ := lt_of_lt_of_le zero_lt_one hzNorm
    have hz0 : z ≠ 0 := norm_ne_zero_iff.mp hzPos.ne'
    have hfirst : ‖(1 : ℂ) / (12 * z)‖ = 1 / (12 * ‖z‖) := by
      rw [norm_div, norm_one, norm_mul]
      norm_num
    have htriangle :
        ‖e‖ ≤ ‖(1 : ℂ) / (12 * z)‖ +
          ‖deBruijnNewmanPolymathGammaStirlingR2 z‖ := by
      dsimp [e]
      exact norm_add_le _ _
    have hshift : 0 < ‖z‖ - 123 / 500 := by norm_num at *; linarith
    have hrearrange :
        1 / (12 * ‖z‖) + (41 / 2000 : ℝ) / ‖z‖ ^ 2 =
          (‖z‖ + 123 / 500) / (12 * ‖z‖ ^ 2) := by
      field_simp [hzPos.ne']
      ring
    have hcompare :
        (‖z‖ + 123 / 500) / (12 * ‖z‖ ^ 2) ≤
          1 / (12 * (‖z‖ - 123 / 500)) := by
      rw [div_le_div_iff₀ (by positivity : 0 < 12 * ‖z‖ ^ 2)
        (by positivity : 0 < 12 * (‖z‖ - 123 / 500))]
      nlinarith [sq_nonneg (123 / 500 : ℝ)]
    calc
      ‖e‖ ≤ ‖(1 : ℂ) / (12 * z)‖ +
          ‖deBruijnNewmanPolymathGammaStirlingR2 z‖ := htriangle
      _ = 1 / (12 * ‖z‖) +
          ‖deBruijnNewmanPolymathGammaStirlingR2 z‖ := by rw [hfirst]
      _ ≤ 1 / (12 * ‖z‖) + (41 / 2000 : ℝ) / ‖z‖ ^ 2 := by linarith
      _ = (‖z‖ + 123 / 500) / (12 * ‖z‖ ^ 2) := hrearrange
      _ ≤ 1 / (12 * (‖z‖ - 123 / 500)) := hcompare

/-- End-to-end reduction of the prefactor logarithmic bound to the single Boyd `R_2` estimate. -/
theorem deBruijnNewmanPolymathPrefactorError_norm_le_of_R2_bound
    {s : ℂ} (hs : s.im ≠ 0) (hsNorm : 1 ≤ ‖s / 2‖)
    (hR2 : ‖deBruijnNewmanPolymathGammaStirlingR2 (s / 2)‖ ≤
      (41 / 2000 : ℝ) / ‖s / 2‖ ^ 2) :
    ‖deBruijnNewmanPolymathPrefactorError s‖ ≤
      1 / (12 * (‖s / 2‖ - 33 / 100)) := by
  obtain ⟨e, hrelative, he⟩ :=
    deBruijnNewmanPolymath_relative_stirling_of_R2_bound hsNorm hR2
  exact deBruijnNewmanPolymathPrefactorError_norm_le_of_relative_stirling
    hs hsNorm hrelative he

/-- Source form of the prefactor error after substituting `z = s/2`. -/
theorem deBruijnNewmanPolymathPrefactorError_norm_le_source_of_R2_bound
    {s : ℂ} (hs : s.im ≠ 0) (hsNorm : 2 ≤ ‖s‖)
    (hR2 : ‖deBruijnNewmanPolymathGammaStirlingR2 (s / 2)‖ ≤
      (41 / 2000 : ℝ) / ‖s / 2‖ ^ 2) :
    ‖deBruijnNewmanPolymathPrefactorError s‖ ≤
      1 / (6 * (‖s‖ - 33 / 50)) := by
  have hsHalfNorm : 1 ≤ ‖s / 2‖ := by
    rw [norm_div]
    norm_num
    linarith
  have h := deBruijnNewmanPolymathPrefactorError_norm_le_of_R2_bound
    hs hsHalfNorm hR2
  convert h using 1
  rw [norm_div]
  norm_num
  have hden : ‖s‖ - 33 / 50 ≠ 0 := by norm_num at *; linarith
  have hdenHalf : ‖s‖ * (1 / 2) - 33 / 100 ≠ 0 := by norm_num at *; linarith
  field_simp [hden, hdenHalf]
  have hD : -33 + ‖s‖ * 50 ≠ 0 := by norm_num at *; linarith
  rw [show ‖s‖ * 100 - 33 * 2 = 2 * (‖s‖ * 50 - 33) by ring]
  field_simp [hD]
  ring

/-- Exact quadratic exponential moment for the variance-two Gaussian used by the project. -/
theorem integral_exp_sq_gaussianReal_two
    {c : ℝ} (hc : c < 1 / 4) :
    (∫ y : ℝ, Real.exp (c * y ^ 2) ∂gaussianReal 0 2) =
      (Real.sqrt (1 - 4 * c))⁻¹ := by
  rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul (by norm_num)]
  simp only [ProbabilityTheory.gaussianPDFReal, sub_zero, NNReal.coe_ofNat,
    smul_eq_mul]
  let a : ℝ := 1 / 4 - c
  have ha : 0 < a := by dsimp [a]; linarith
  have hpoint : ∀ y : ℝ,
      (Real.sqrt (2 * Real.pi * 2))⁻¹ * Real.exp (-y ^ 2 / (2 * 2)) *
          Real.exp (c * y ^ 2) =
        (Real.sqrt (2 * Real.pi * 2))⁻¹ * Real.exp (-a * y ^ 2) := by
    intro y
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    dsimp [a]
    ring
  simp_rw [hpoint]
  rw [MeasureTheory.integral_const_mul, integral_gaussian a]
  have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hsqrtA : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hsqrtFourPi : Real.sqrt (2 * Real.pi * 2) = 2 * Real.sqrt Real.pi := by
    rw [show 2 * Real.pi * 2 = 4 * Real.pi by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have hsqrtDiv : Real.sqrt (Real.pi / a) = Real.sqrt Real.pi / Real.sqrt a := by
    rw [Real.sqrt_div Real.pi_pos.le]
  have hsqrtTarget : Real.sqrt (1 - 4 * c) = 2 * Real.sqrt a := by
    rw [show 1 - 4 * c = 4 * a by dsimp [a]; ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  rw [hsqrtFourPi, hsqrtDiv, hsqrtTarget]
  field_simp

/-- A logarithmic upper bound for the reciprocal square root singularity. -/
theorem inv_sqrt_one_sub_le_exp
    {x y : ℝ} (hx1 : x < 1)
    (hxy : x / (2 * (1 - x)) ≤ y) :
    (Real.sqrt (1 - x))⁻¹ ≤ Real.exp y := by
  have hpos : 0 < 1 - x := by linarith
  have hsqrtPos : 0 < Real.sqrt (1 - x) := Real.sqrt_pos.2 hpos
  apply (Real.log_le_iff_le_exp (inv_pos.mpr hsqrtPos)).mp
  rw [Real.log_inv, Real.log_sqrt hpos.le]
  have hbase := Real.one_sub_inv_le_log_of_pos hpos
  have hlog : -Real.log (1 - x) ≤ x / (1 - x) := by
    have hid : (1 - x)⁻¹ - 1 = x / (1 - x) := by
      field_simp [hpos.ne']
      ring
    rw [← hid]
    linarith
  have hhalf : x / (2 * (1 - x)) = (x / (1 - x)) / 2 := by
    field_simp [hpos.ne']
  rw [hhalf] at hxy
  linarith

/-- Equation `(ax)` from the proof of Polymath Proposition 6.1, in the project's
variance-two Gaussian normalization (`y = 2v` relative to the paper). -/
theorem deBruijnNewmanPolymathTerm_gaussian_error_le
    {t T : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) (hT : 10 ≤ T) :
    (∫ y : ℝ,
        Real.exp (t * y ^ 2 / (8 * (T - 77 / 25)))
          ∂gaussianReal 0 2) ≤
      Real.exp (t / (4 * (T - 333 / 100))) := by
  let A : ℝ := T - 77 / 25
  let B : ℝ := T - 333 / 100
  let c : ℝ := t / (8 * A)
  have hA : 0 < A := by dsimp [A]; norm_num at *; linarith
  have hB : 0 < B := by dsimp [B]; norm_num at *; linarith
  have hAstrong : 1 < A := by dsimp [A]; norm_num at *; linarith
  have hc : c < 1 / 4 := by
    dsimp [c]
    rw [div_lt_iff₀ (by positivity : 0 < 8 * A)]
    nlinarith
  have hintegrand : ∀ y : ℝ,
      t * y ^ 2 / (8 * (T - 77 / 25)) = c * y ^ 2 := by
    intro y
    dsimp [c, A]
    ring
  simp_rw [hintegrand]
  rw [integral_exp_sq_gaussianReal_two hc]
  have hx1 : 4 * c < 1 := by linarith
  apply inv_sqrt_one_sub_le_exp hx1
  have hleftDen : 0 < 4 * A - 2 * t := by nlinarith
  have hrightDen : 0 < 4 * B := by positivity
  have hdenOrder : 4 * B ≤ 4 * A - 2 * t := by
    dsimp [A, B]
    norm_num at *
    linarith
  have hratio :
      (4 * c) / (2 * (1 - 4 * c)) = t / (4 * A - 2 * t) := by
    have hnum : 4 * c = t / (2 * A) := by
      dsimp [c]
      field_simp [hA.ne']
      ring
    have hone : 1 - 4 * c = (2 * A - t) / (2 * A) := by
      dsimp [c]
      field_simp [hA.ne']
      ring
    have hden : 2 * ((2 * A - t) / (2 * A)) = (2 * A - t) / A := by
      field_simp [hA.ne']
    have hnum' : t / (2 * A) = (t / 2) / A := by ring
    rw [hone, hnum, hden, hnum', div_div_div_cancel_right₀ hA.ne']
    rw [show 4 * A - 2 * t = 2 * (2 * A - t) by ring]
    rw [div_div]
  rw [hratio]
  exact div_le_div_of_nonneg_left ht0 hrightDen hdenOrder

end

end LeanLab.Riemann
