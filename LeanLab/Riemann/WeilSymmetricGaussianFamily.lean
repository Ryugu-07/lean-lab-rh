import LeanLab.Riemann.WeilGaussianExplicitFormula

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# A symmetric translated Gaussian family for the xi explicit formula

The weight `exp(a*(s-1/2)^2) * cosh(b*(s-1/2))` introduces a real translation parameter on the
log-prime side while retaining functional-equation symmetry and Gaussian vertical decay. No
density, positivity, temperedness, or Riemann hypothesis statement is asserted.
-/

open Complex Filter Function MeasureTheory Set Topology
open scoped BigOperators Interval LSeries.notation Topology

namespace LeanLab.Riemann

noncomputable section

/-- The reflection-symmetric Gaussian family with real Fourier-modulation parameter `b`. -/
def riemannXiSymmetricGaussianWeight (a b : ℝ) (z : ℂ) : ℂ :=
  riemannXiGaussianWeight a z * Complex.cosh ((b : ℂ) * (z - 1 / 2))

theorem differentiable_riemannXiSymmetricGaussianWeight (a b : ℝ) :
    Differentiable ℂ (riemannXiSymmetricGaussianWeight a b) := by
  unfold riemannXiSymmetricGaussianWeight
  exact (differentiable_riemannXiGaussianWeight a).mul (by fun_prop)

theorem riemannXiSymmetricGaussianWeight_neg (a b : ℝ) (z : ℂ) :
    riemannXiSymmetricGaussianWeight a (-b) z =
      riemannXiSymmetricGaussianWeight a b z := by
  unfold riemannXiSymmetricGaussianWeight
  rw [show ((-b : ℝ) : ℂ) * (z - 1 / 2) = -((b : ℂ) * (z - 1 / 2)) by
    push_cast
    ring]
  rw [Complex.cosh_neg]

theorem riemannXiSymmetricGaussianWeight_zero (a : ℝ) (z : ℂ) :
    riemannXiSymmetricGaussianWeight a 0 z = riemannXiGaussianWeight a z := by
  simp [riemannXiSymmetricGaussianWeight]

theorem riemannXiSymmetricGaussianWeight_one_sub (a b : ℝ) (z : ℂ) :
    riemannXiSymmetricGaussianWeight a b (1 - z) =
      riemannXiSymmetricGaussianWeight a b z := by
  unfold riemannXiSymmetricGaussianWeight
  rw [riemannXiGaussianWeight_one_sub]
  rw [show (b : ℂ) * (1 - z - 1 / 2) = -((b : ℂ) * (z - 1 / 2)) by ring]
  rw [Complex.cosh_neg]

/-- A complex hyperbolic cosine is controlled by the exponential of its real part. -/
theorem norm_cosh_le_exp_abs_re (z : ℂ) :
    ‖Complex.cosh z‖ ≤ Real.exp |z.re| := by
  rw [Complex.cosh, norm_div]
  norm_num
  calc
    ‖Complex.exp z + Complex.exp (-z)‖ / 2 ≤
        (‖Complex.exp z‖ + ‖Complex.exp (-z)‖) / 2 := by
      gcongr
      exact norm_add_le _ _
    _ = (Real.exp z.re + Real.exp (-z.re)) / 2 := by
      rw [Complex.norm_exp, Complex.norm_exp]
      simp
    _ ≤ (Real.exp |z.re| + Real.exp |z.re|) / 2 := by
      gcongr
      · exact le_abs_self _
      · exact neg_le_abs _
    _ = Real.exp |z.re| := by ring

/-- On a fixed vertical strip, the modulation factor is bounded independently of height. -/
theorem norm_cosh_mul_center_le
    {b x y M : ℝ} (hM : |x - 1 / 2| ≤ M) :
    ‖Complex.cosh ((b : ℂ) * (((x : ℂ) + y * I) - 1 / 2))‖ ≤
      Real.exp (|b| * M) := by
  apply (norm_cosh_le_exp_abs_re _).trans
  apply Real.exp_le_exp.mpr
  have hreal :
      (((b : ℂ) * (((x : ℂ) + y * I) - 1 / 2)).re) = b * (x - 1 / 2) := by
    norm_num [mul_re, div_re]
  rw [hreal, abs_mul]
  exact mul_le_mul_of_nonneg_left hM (abs_nonneg b)

theorem norm_cosh_mul_riemannXiZero_center_le
    (b : ℝ) (p : RiemannXiDivisorZeroIndex) :
    ‖Complex.cosh ((b : ℂ) * (riemannXiDivisorZeroValue p - 1 / 2))‖ ≤
      Real.exp (|b| / 2) := by
  apply (norm_cosh_le_exp_abs_re _).trans
  apply Real.exp_le_exp.mpr
  have hrho : IsNontrivialZero (riemannXiDivisorZeroValue p) :=
    riemannXiDivisorZeroIndex_val_isNontrivialZero p
  have hreflect : IsNontrivialZero (1 - riemannXiDivisorZeroValue p) := by
    rw [isNontrivialZero_iff_riemannXi_eq_zero, riemannXi_one_sub]
    exact (isNontrivialZero_iff_riemannXi_eq_zero _).mp hrho
  have hre0 : 0 < (riemannXiDivisorZeroValue p).re := by
    have h := nontrivial_zero_re_lt_one hreflect
    simp only [sub_re, one_re] at h
    linarith
  have hre1 : (riemannXiDivisorZeroValue p).re < 1 :=
    nontrivial_zero_re_lt_one hrho
  have hreal :
      (((b : ℂ) * (riemannXiDivisorZeroValue p - 1 / 2)).re) =
        b * ((riemannXiDivisorZeroValue p).re - 1 / 2) := by
    norm_num [mul_re, div_re]
  rw [hreal, abs_mul]
  have hcenter : |(riemannXiDivisorZeroValue p).re - 1 / 2| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith
  nlinarith [abs_nonneg b]

/-- The entire two-parameter family is absolutely summable over xi zeros with multiplicity. -/
theorem summable_riemannXiSymmetricGaussianWeight
    {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      riemannXiSymmetricGaussianWeight a b (riemannXiDivisorZeroValue p)) := by
  apply Summable.of_norm_bounded
    ((summable_riemannXiGaussianWeight ha).norm.mul_left (Real.exp (|b| / 2)))
  intro p
  rw [riemannXiSymmetricGaussianWeight, norm_mul]
  calc
    ‖riemannXiGaussianWeight a (riemannXiDivisorZeroValue p)‖ *
        ‖Complex.cosh ((b : ℂ) * (riemannXiDivisorZeroValue p - 1 / 2))‖ ≤
      ‖riemannXiGaussianWeight a (riemannXiDivisorZeroValue p)‖ *
        Real.exp (|b| / 2) := by
      gcongr
      exact norm_cosh_mul_riemannXiZero_center_le b p
    _ = Real.exp (|b| / 2) *
        ‖riemannXiGaussianWeight a (riemannXiDivisorZeroValue p)‖ := by ring

/-- The top horizontal integral at the already-constructed zero-free selected heights. -/
noncomputable def selectedXiTopHorizontalIntegralFor
    (F : ℂ → ℂ) (c : ℝ) (n : ℕ) : ℂ :=
  ∫ x : ℝ in 1 - c..c,
    F ((x : ℂ) + gaussianXiSelectedHeight c n * I) *
      logDeriv riemannXi ((x : ℂ) + gaussianXiSelectedHeight c n * I)

/-- The right vertical integral at the selected heights. -/
noncomputable def selectedXiRightVerticalIntegralFor
    (F : ℂ → ℂ) (c : ℝ) (n : ℕ) : ℂ :=
  ∫ y : ℝ in -gaussianXiSelectedHeight c n..gaussianXiSelectedHeight c n,
    F ((c : ℂ) + y * I) * logDeriv riemannXi ((c : ℂ) + y * I)

/-- The finite multiplicity-bearing zero sum in a selected symmetric rectangle. -/
noncomputable def selectedXiRectangleZeroFinsumFor
    (F : ℂ → ℂ) (c : ℝ) (n : ℕ) : ℂ :=
  ∑ᶠ p : RiemannXiDivisorZeroIndex,
    if riemannXiZeroStrictlyInsideRectangle
        (1 - c) c (-gaussianXiSelectedHeight c n) (gaussianXiSelectedHeight c n) p then
      F (riemannXiDivisorZeroValue p)
    else 0

/-- The selected top-edge integral for the symmetric Gaussian family. -/
noncomputable def symmetricGaussianXiTopHorizontalIntegral
    (a b c : ℝ) (n : ℕ) : ℂ :=
  selectedXiTopHorizontalIntegralFor (riemannXiSymmetricGaussianWeight a b) c n

theorem norm_riemannXiSymmetricGaussianWeight_selectedTopEdge_le
    {a c : ℝ} (ha : 0 < a) (hc : 1 < c) (b : ℝ) (n : ℕ) {x : ℝ}
    (hx : x ∈ [[1 - c, c]]) :
    ‖riemannXiSymmetricGaussianWeight a b
        ((x : ℂ) + gaussianXiSelectedHeight c n * I)‖ ≤
      Real.exp (|b| * (c - 1 / 2)) *
        Real.exp (a * (c - 1 / 2) ^ 2) *
          Real.exp (-a * gaussianXiHeightScale c n ^ 2) := by
  have hlr : 1 - c ≤ c := by linarith
  rw [uIcc_of_le hlr] at hx
  have hcenter : |x - 1 / 2| ≤ c - 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2]
  rw [riemannXiSymmetricGaussianWeight, norm_mul]
  calc
    ‖riemannXiGaussianWeight a
          ((x : ℂ) + gaussianXiSelectedHeight c n * I)‖ *
        ‖Complex.cosh ((b : ℂ) *
          (((x : ℂ) + gaussianXiSelectedHeight c n * I) - 1 / 2))‖ ≤
      (Real.exp (a * (c - 1 / 2) ^ 2) *
          Real.exp (-a * gaussianXiHeightScale c n ^ 2)) *
        Real.exp (|b| * (c - 1 / 2)) := by
      gcongr
      · exact norm_riemannXiGaussianWeight_selectedTopEdge_le ha hc n
          (by simpa only [uIcc_of_le hlr] using hx)
      · exact norm_cosh_mul_center_le hcenter
    _ = Real.exp (|b| * (c - 1 / 2)) *
        Real.exp (a * (c - 1 / 2) ^ 2) *
          Real.exp (-a * gaussianXiHeightScale c n ^ 2) := by ring

theorem exists_norm_symmetricGaussianXiTopHorizontalIntegral_le
    {a c : ℝ} (ha : 0 < a) (hc : 1 < c) (b : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ,
      ‖symmetricGaussianXiTopHorizontalIntegral a b c n‖ ≤
        B * (gaussianXiHeightScale c n ^ 4 *
          Real.exp (-a * gaussianXiHeightScale c n ^ 2)) := by
  obtain ⟨K, hK, hlog⟩ :=
    exists_norm_logDeriv_selectedGaussianTopEdge_le_scale_pow_four hc
  let B : ℝ := (2 * c - 1) * Real.exp (|b| * (c - 1 / 2)) *
    Real.exp (a * (c - 1 / 2) ^ 2) * K
  refine ⟨B, by
    dsimp only [B]
    have hlength : 0 < 2 * c - 1 := by linarith
    positivity, ?_⟩
  intro n
  let R : ℝ := gaussianXiHeightScale c n
  let D : ℝ := Real.exp (|b| * (c - 1 / 2)) *
    Real.exp (a * (c - 1 / 2) ^ 2) * Real.exp (-a * R ^ 2)
  have hpoint : ∀ x ∈ Ι (1 - c) c,
      ‖riemannXiSymmetricGaussianWeight a b
          ((x : ℂ) + gaussianXiSelectedHeight c n * I) *
        logDeriv riemannXi ((x : ℂ) + gaussianXiSelectedHeight c n * I)‖ ≤
        D * (K * R ^ 4) := by
    intro x hx
    rw [norm_mul]
    apply mul_le_mul
    · simpa only [D, R] using
        norm_riemannXiSymmetricGaussianWeight_selectedTopEdge_le ha hc b n
          (Set.uIoc_subset_uIcc hx)
    · simpa only [R] using hlog n x (Set.uIoc_subset_uIcc hx)
    · positivity
    · positivity
  have hintegral := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  rw [symmetricGaussianXiTopHorizontalIntegral]
  calc
    ‖∫ x : ℝ in 1 - c..c,
        riemannXiSymmetricGaussianWeight a b
            ((x : ℂ) + gaussianXiSelectedHeight c n * I) *
          logDeriv riemannXi ((x : ℂ) + gaussianXiSelectedHeight c n * I)‖ ≤
        (D * (K * R ^ 4)) * |c - (1 - c)| := hintegral
    _ = B * (gaussianXiHeightScale c n ^ 4 *
        Real.exp (-a * gaussianXiHeightScale c n ^ 2)) := by
      rw [abs_of_pos (by linarith : 0 < c - (1 - c))]
      dsimp only [B, D, R]
      ring

theorem tendsto_symmetricGaussianXiTopHorizontalIntegral
    {a c : ℝ} (ha : 0 < a) (hc : 1 < c) (b : ℝ) :
    Tendsto (symmetricGaussianXiTopHorizontalIntegral a b c) atTop (𝓝 0) := by
  obtain ⟨B, _hB, hbound⟩ :=
    exists_norm_symmetricGaussianXiTopHorizontalIntegral_le ha hc b
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n => norm_nonneg _
  · exact Filter.Eventually.of_forall fun n => hbound n
  · simpa using
      (tendsto_gaussianXiHeightScale_pow_four_mul_exp_neg_sq
        (a := a) (c := c) ha).const_mul B

/-- A reflection-symmetric weight makes the weighted xi logarithmic derivative odd. -/
theorem selectedXiWeightedLogDeriv_one_sub
    {F : ℂ → ℂ} (hsym : ∀ z : ℂ, F (1 - z) = F z) (z : ℂ) :
    F (1 - z) * logDeriv riemannXi (1 - z) =
      -(F z * logDeriv riemannXi z) := by
  rw [hsym, logDeriv_riemannXi_one_sub]
  ring

/-- Reflection identifies the bottom horizontal integral with the negative top integral. -/
theorem selectedXiBottomHorizontalIntegral_eq_neg_top
    {F : ℂ → ℂ} (hsym : ∀ z : ℂ, F (1 - z) = F z) (c : ℝ) (n : ℕ) :
    (∫ x : ℝ in 1 - c..c,
      F ((x : ℂ) - gaussianXiSelectedHeight c n * I) *
        logDeriv riemannXi ((x : ℂ) - gaussianXiSelectedHeight c n * I)) =
      -selectedXiTopHorizontalIntegralFor F c n := by
  let T : ℝ := gaussianXiSelectedHeight c n
  let f : ℝ → ℂ := fun x =>
    F ((x : ℂ) + T * I) * logDeriv riemannXi ((x : ℂ) + T * I)
  have hpoint : ∀ x : ℝ,
      F ((x : ℂ) - T * I) * logDeriv riemannXi ((x : ℂ) - T * I) =
        -f (1 - x) := by
    intro x
    have href := selectedXiWeightedLogDeriv_one_sub hsym ((x : ℂ) - T * I)
    have harg : (1 : ℂ) - ((x : ℂ) - T * I) = ((1 - x : ℝ) : ℂ) + T * I := by
      push_cast
      ring
    rw [harg] at href
    simpa only [f, neg_neg] using (congrArg Neg.neg href).symm
  calc
    (∫ x : ℝ in 1 - c..c,
      F ((x : ℂ) - T * I) * logDeriv riemannXi ((x : ℂ) - T * I)) =
        ∫ x : ℝ in 1 - c..c, -f (1 - x) := by
      apply intervalIntegral.integral_congr
      intro x _hx
      exact hpoint x
    _ = -(∫ x : ℝ in 1 - c..c, f (1 - x)) := by
      rw [intervalIntegral.integral_neg]
    _ = -(∫ x : ℝ in 1 - c..c, f x) := by
      rw [intervalIntegral.integral_comp_sub_left f 1]
      congr 2
      all_goals ring
    _ = -selectedXiTopHorizontalIntegralFor F c n := by
      rfl

/-- Reflection and ordinate reversal identify the left vertical integral with the negative right
vertical integral. -/
theorem selectedXiLeftVerticalIntegral_eq_neg_right
    {F : ℂ → ℂ} (hsym : ∀ z : ℂ, F (1 - z) = F z) (c : ℝ) (n : ℕ) :
    (∫ y : ℝ in -gaussianXiSelectedHeight c n..gaussianXiSelectedHeight c n,
      F (((1 - c : ℝ) : ℂ) + y * I) *
        logDeriv riemannXi (((1 - c : ℝ) : ℂ) + y * I)) =
      -selectedXiRightVerticalIntegralFor F c n := by
  let T : ℝ := gaussianXiSelectedHeight c n
  let f : ℝ → ℂ := fun y =>
    F ((c : ℂ) + y * I) * logDeriv riemannXi ((c : ℂ) + y * I)
  have hpoint : ∀ y : ℝ,
      F (((1 - c : ℝ) : ℂ) + y * I) *
          logDeriv riemannXi (((1 - c : ℝ) : ℂ) + y * I) = -f (-y) := by
    intro y
    have href := selectedXiWeightedLogDeriv_one_sub hsym ((c : ℂ) - y * I)
    have harg : (1 : ℂ) - ((c : ℂ) - y * I) =
        ((1 - c : ℝ) : ℂ) + y * I := by
      push_cast
      ring
    rw [harg] at href
    simpa only [f, Complex.ofReal_neg, neg_mul, sub_eq_add_neg, neg_neg] using href
  calc
    (∫ y : ℝ in -T..T,
      F (((1 - c : ℝ) : ℂ) + y * I) *
        logDeriv riemannXi (((1 - c : ℝ) : ℂ) + y * I)) =
        ∫ y : ℝ in -T..T, -f (-y) := by
      apply intervalIntegral.integral_congr
      intro y _hy
      exact hpoint y
    _ = -(∫ y : ℝ in -T..T, f (-y)) := by
      rw [intervalIntegral.integral_neg]
    _ = -(∫ y : ℝ in -T..T, f y) := by
      simpa only [zero_sub, neg_neg] using congrArg Neg.neg
        (intervalIntegral.integral_comp_sub_left (a := -T) (b := T) f 0)
    _ = -selectedXiRightVerticalIntegralFor F c n := by
      rfl

/-- Reflection reduces the full selected rectangle boundary to one top and one right edge. -/
theorem selectedXiRectangleBoundary_eq_top_right
    {F : ℂ → ℂ} (hsym : ∀ z : ℂ, F (1 - z) = F z) (c : ℝ) (n : ℕ) :
    rectangleBoundaryIntegral (fun z => F z * logDeriv riemannXi z)
        (1 - c) c (-gaussianXiSelectedHeight c n) (gaussianXiSelectedHeight c n) =
      -2 * selectedXiTopHorizontalIntegralFor F c n +
        2 * I * selectedXiRightVerticalIntegralFor F c n := by
  let T : ℝ := gaussianXiSelectedHeight c n
  rw [rectangleBoundaryIntegral]
  simp only [Complex.ofReal_neg]
  rw [show (∫ x : ℝ in 1 - c..c,
      F ((x : ℂ) + (-T) * I) * logDeriv riemannXi ((x : ℂ) + (-T) * I)) =
      -selectedXiTopHorizontalIntegralFor F c n by
        simpa only [T, neg_mul, sub_eq_add_neg] using
          selectedXiBottomHorizontalIntegral_eq_neg_top hsym c n]
  rw [show (∫ x : ℝ in 1 - c..c,
      F ((x : ℂ) + T * I) * logDeriv riemannXi ((x : ℂ) + T * I)) =
      selectedXiTopHorizontalIntegralFor F c n by rfl]
  rw [show (∫ y : ℝ in -T..T,
      F ((c : ℂ) + y * I) * logDeriv riemannXi ((c : ℂ) + y * I)) =
      selectedXiRightVerticalIntegralFor F c n by rfl]
  rw [show (∫ y : ℝ in -T..T,
      F (((1 - c : ℝ) : ℂ) + y * I) *
        logDeriv riemannXi (((1 - c : ℝ) : ℂ) + y * I)) =
      -selectedXiRightVerticalIntegralFor F c n by
        exact selectedXiLeftVerticalIntegral_eq_neg_right hsym c n]
  ring

/-- The finite weighted argument principle solved for the selected right edge. -/
theorem selectedXiRightVerticalIntegral_eq_top_add_zeroFinsum
    {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hsym : ∀ z : ℂ, F (1 - z) = F z)
    {c : ℝ} (hc : 1 < c) (n : ℕ) :
    selectedXiRightVerticalIntegralFor F c n =
      -I * selectedXiTopHorizontalIntegralFor F c n +
        (Real.pi : ℂ) * selectedXiRectangleZeroFinsumFor F c n := by
  have hTpos : 0 < gaussianXiSelectedHeight c n :=
    lt_trans (gaussianXiHeightScale_pos hc n)
      (gaussianXiSelectedHeight_spec c n).1.1
  have hres := rectangleBoundaryIntegral_weighted_logDeriv_riemannXi_eq_finsum hF
    (show 1 - c < c by linarith)
    (show -gaussianXiSelectedHeight c n < gaussianXiSelectedHeight c n by linarith)
    (gaussianXiSelectedHeight_zeroFreeBoundary hc n)
  rw [selectedXiRectangleBoundary_eq_top_right hsym] at hres
  change
    -2 * selectedXiTopHorizontalIntegralFor F c n +
        2 * I * selectedXiRightVerticalIntegralFor F c n =
      2 * (Real.pi : ℂ) * I * selectedXiRectangleZeroFinsumFor F c n at hres
  have hres' :
      2 * I * selectedXiRightVerticalIntegralFor F c n =
        2 * selectedXiTopHorizontalIntegralFor F c n +
          2 * (Real.pi : ℂ) * I * selectedXiRectangleZeroFinsumFor F c n := by
    linear_combination hres
  apply mul_left_cancel₀ (show (2 : ℂ) * I ≠ 0 by simp)
  calc
    ((2 : ℂ) * I) * selectedXiRightVerticalIntegralFor F c n =
        2 * I * selectedXiRightVerticalIntegralFor F c n := by ring
    _ = 2 * selectedXiTopHorizontalIntegralFor F c n +
          2 * (Real.pi : ℂ) * I * selectedXiRectangleZeroFinsumFor F c n := hres'
    _ = ((2 : ℂ) * I) *
        (-I * selectedXiTopHorizontalIntegralFor F c n +
          (Real.pi : ℂ) * selectedXiRectangleZeroFinsumFor F c n) := by
      calc
        2 * selectedXiTopHorizontalIntegralFor F c n +
            2 * (Real.pi : ℂ) * I * selectedXiRectangleZeroFinsumFor F c n =
          2 * (-(I * I)) * selectedXiTopHorizontalIntegralFor F c n +
            2 * (Real.pi : ℂ) * I * selectedXiRectangleZeroFinsumFor F c n := by
              rw [Complex.I_mul_I]
              ring
        _ = ((2 : ℂ) * I) *
            (-I * selectedXiTopHorizontalIntegralFor F c n +
              (Real.pi : ℂ) * selectedXiRectangleZeroFinsumFor F c n) := by ring

/-- Any interior-zero cutoff has finite support on a finite rectangle. -/
theorem hasFiniteSupport_selectedXiRectangleZeroCutoff
    (F : ℂ → ℂ) (l r b t : ℝ) :
    Function.HasFiniteSupport
      (fun p : RiemannXiDivisorZeroIndex =>
        if riemannXiZeroStrictlyInsideRectangle l r b t p then
          F (riemannXiDivisorZeroValue p)
        else 0) := by
  classical
  apply (finite_riemannXiZeroStrictlyInsideRectangle l r b t).subset
  intro p hp
  simp only [Function.mem_support] at hp
  by_contra hout
  have hout' : ¬riemannXiZeroStrictlyInsideRectangle l r b t p := by
    simpa only [Set.mem_setOf_eq] using hout
  exact hp (if_neg hout')

/-- A summable zero weight is recovered by expanding symmetric rectangle cutoffs. -/
theorem tendsto_selectedXiRectangleZeroFinsumFor
    {F : ℂ → ℂ} (hFsum : Summable (fun p : RiemannXiDivisorZeroIndex =>
      F (riemannXiDivisorZeroValue p)))
    {c : ℝ} (hc : 1 < c) :
    Tendsto (selectedXiRectangleZeroFinsumFor F c) atTop
      (𝓝 (∑' p : RiemannXiDivisorZeroIndex, F (riemannXiDivisorZeroValue p))) := by
  classical
  let f : ℕ → RiemannXiDivisorZeroIndex → ℂ := fun n p =>
    if riemannXiZeroStrictlyInsideRectangle (1 - c) c
        (-gaussianXiSelectedHeight c n) (gaussianXiSelectedHeight c n) p then
      F (riemannXiDivisorZeroValue p)
    else 0
  let g : RiemannXiDivisorZeroIndex → ℂ := fun p => F (riemannXiDivisorZeroValue p)
  have hpoint : ∀ p : RiemannXiDivisorZeroIndex,
      Tendsto (fun n => f n p) atTop (𝓝 (g p)) := by
    intro p
    let rho : ℂ := riemannXiDivisorZeroValue p
    have hrho : IsNontrivialZero rho :=
      riemannXiDivisorZeroIndex_val_isNontrivialZero p
    have hreflect : IsNontrivialZero (1 - rho) := by
      rw [isNontrivialZero_iff_riemannXi_eq_zero, riemannXi_one_sub]
      exact (isNontrivialZero_iff_riemannXi_eq_zero rho).mp hrho
    have hre0 : 0 < rho.re := by
      have hreflectRe := nontrivial_zero_re_lt_one hreflect
      simp only [sub_re, one_re] at hreflectRe
      linarith
    have hre1 : rho.re < 1 := nontrivial_zero_re_lt_one hrho
    have hheight : ∀ᶠ n : ℕ in atTop, |rho.im| < gaussianXiSelectedHeight c n :=
      (tendsto_gaussianXiSelectedHeight c).eventually (eventually_gt_atTop |rho.im|)
    apply tendsto_const_nhds.congr'
    filter_upwards [hheight] with n hn
    have hinside : riemannXiZeroStrictlyInsideRectangle (1 - c) c
        (-gaussianXiSelectedHeight c n) (gaussianXiSelectedHeight c n) p := by
      unfold riemannXiZeroStrictlyInsideRectangle
      dsimp only [rho] at hre0 hre1 hn ⊢
      rw [abs_lt] at hn
      constructor
      · linarith
      · constructor
        · linarith
        · constructor <;> linarith
    simp only [f, g, if_pos hinside]
  have hbound : ∀ᶠ n : ℕ in atTop, ∀ p : RiemannXiDivisorZeroIndex,
      ‖f n p‖ ≤ ‖g p‖ := by
    filter_upwards [] with n
    intro p
    by_cases hinside : riemannXiZeroStrictlyInsideRectangle (1 - c) c
        (-gaussianXiSelectedHeight c n) (gaussianXiSelectedHeight c n) p
    · simp only [f, g, if_pos hinside]
      exact le_rfl
    · simp only [f, g, if_neg hinside, norm_zero, norm_nonneg]
  have hlim := tendsto_tsum_of_dominated_convergence hFsum.norm hpoint hbound
  have heq : (fun n => ∑' p : RiemannXiDivisorZeroIndex, f n p) =
      selectedXiRectangleZeroFinsumFor F c := by
    funext n
    change (∑' p : RiemannXiDivisorZeroIndex, f n p) =
      ∑ᶠ p : RiemannXiDivisorZeroIndex, f n p
    rw [tsum_eq_finsum]
    exact hasFiniteSupport_selectedXiRectangleZeroCutoff F
      (1 - c) c (-gaussianXiSelectedHeight c n) (gaussianXiSelectedHeight c n)
  rw [← heq]
  exact hlim

/-- Generic selected-height endpoint for any analytic reflection-symmetric summable weight whose
top edge vanishes. -/
theorem tendsto_selectedXiRightVerticalIntegralFor
    {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hsym : ∀ z : ℂ, F (1 - z) = F z)
    (hFsum : Summable (fun p : RiemannXiDivisorZeroIndex =>
      F (riemannXiDivisorZeroValue p)))
    {c : ℝ} (hc : 1 < c)
    (htop : Tendsto (selectedXiTopHorizontalIntegralFor F c) atTop (𝓝 0)) :
    Tendsto (selectedXiRightVerticalIntegralFor F c) atTop
      (𝓝 ((Real.pi : ℂ) *
        ∑' p : RiemannXiDivisorZeroIndex, F (riemannXiDivisorZeroValue p))) := by
  have htop' := htop.const_mul (-I)
  have hzero := (tendsto_selectedXiRectangleZeroFinsumFor hFsum hc).const_mul
    (Real.pi : ℂ)
  have hcombined := htop'.add hzero
  simpa only [mul_zero, zero_add] using hcombined.congr'
    (Filter.Eventually.of_forall fun n =>
      (selectedXiRightVerticalIntegral_eq_top_add_zeroFinsum hF hsym hc n).symm)

/-- The selected right vertical integral for the symmetric translated Gaussian family converges
to its absolutely convergent multiplicity-bearing xi-zero sum. -/
theorem tendsto_symmetricGaussianXiRightVerticalIntegral
    {a c : ℝ} (ha : 0 < a) (hc : 1 < c) (b : ℝ) :
    Tendsto
      (selectedXiRightVerticalIntegralFor (riemannXiSymmetricGaussianWeight a b) c)
      atTop
      (𝓝 ((Real.pi : ℂ) *
        ∑' p : RiemannXiDivisorZeroIndex,
          riemannXiSymmetricGaussianWeight a b (riemannXiDivisorZeroValue p))) := by
  apply tendsto_selectedXiRightVerticalIntegralFor
    (differentiable_riemannXiSymmetricGaussianWeight a b)
    (riemannXiSymmetricGaussianWeight_one_sub a b)
    (summable_riemannXiSymmetricGaussianWeight ha b) hc
  exact tendsto_symmetricGaussianXiTopHorizontalIntegral ha hc b

/-- One exponentially modulated branch of the translated Gaussian von-Mangoldt weight. -/
def shiftedGaussianVonMangoldtWeight (a b : ℝ) (n : ℕ) : ℂ :=
  (((Real.pi / a : ℝ) : ℂ) ^ (1 / 2 : ℂ)) *
    (ArithmeticFunction.vonMangoldt n : ℂ) *
      Complex.exp
        (-(Real.log n : ℂ) / 2 -
          ((Real.log n : ℂ) - b) ^ 2 / (4 * a))

/-- The average of the two translated prime-power Gaussian kernels. -/
def symmetricGaussianVonMangoldtWeight (a b : ℝ) (n : ℕ) : ℂ :=
  (shiftedGaussianVonMangoldtWeight a b n +
    shiftedGaussianVonMangoldtWeight a (-b) n) / 2

theorem symmetricGaussianVonMangoldtWeight_zero (a : ℝ) (n : ℕ) :
    symmetricGaussianVonMangoldtWeight a 0 n = gaussianVonMangoldtWeight a n := by
  simp [symmetricGaussianVonMangoldtWeight, shiftedGaussianVonMangoldtWeight,
    gaussianVonMangoldtWeight]

/-- One exponentially modulated prime-line summand. -/
def shiftedGaussianXiPrimeLineTerm (a b c : ℝ) (n : ℕ) (y : ℝ) : ℂ :=
  Complex.exp ((b : ℂ) * (((c : ℂ) + y * I) - 1 / 2)) *
    gaussianXiPrimeLineTerm a c n y

/-- Exact quadratic-exponential form of one shifted prime-line summand. -/
theorem shiftedGaussianXiPrimeLineTerm_vertical
    {a b c : ℝ} {n : ℕ} (hn : n ≠ 0) (y : ℝ) :
    shiftedGaussianXiPrimeLineTerm a b c n y =
      (ArithmeticFunction.vonMangoldt n : ℂ) *
        Complex.exp
          (-(a : ℂ) * y ^ 2 +
            (((2 * a * (c - 1 / 2) - Real.log n + b : ℝ) : ℂ) * I) * y +
            (a * (c - 1 / 2) ^ 2 - c * Real.log n + b * (c - 1 / 2) : ℝ)) := by
  rw [shiftedGaussianXiPrimeLineTerm, gaussianXiPrimeLineTerm_vertical hn]
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The full-line integral of one shifted prime summand is the corresponding translated kernel. -/
theorem integral_shiftedGaussianXiPrimeLineTerm
    {a b c : ℝ} (ha : 0 < a) (n : ℕ) :
    (∫ y : ℝ, shiftedGaussianXiPrimeLineTerm a b c n y) =
      shiftedGaussianVonMangoldtWeight a b n := by
  by_cases hn : n = 0
  · subst n
    simp [shiftedGaussianXiPrimeLineTerm, shiftedGaussianVonMangoldtWeight,
      gaussianXiPrimeLineTerm, LSeries.term_zero]
  simp_rw [shiftedGaussianXiPrimeLineTerm_vertical hn]
  rw [MeasureTheory.integral_const_mul]
  have haC : (-(a : ℂ)).re < 0 := by simpa using ha
  rw [integral_cexp_quadratic haC]
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hexp :
      ((a * (c - 1 / 2) ^ 2 - c * Real.log n + b * (c - 1 / 2) : ℝ) : ℂ) -
          ((((2 * a * (c - 1 / 2) - Real.log n + b : ℝ) : ℂ) * I) ^ 2) /
            (4 * (-(a : ℂ))) =
        -(Real.log n : ℂ) / 2 -
          ((Real.log n : ℂ) - b) ^ 2 / (4 * a) := by
    field_simp [ha0]
    rw [Complex.I_sq]
    push_cast
    ring
  rw [hexp]
  unfold shiftedGaussianVonMangoldtWeight
  simp only [neg_neg]
  push_cast
  ring

/-- The shifted branch has the same Gaussian norm decay with a fixed modulation factor. -/
theorem norm_shiftedGaussianXiPrimeLineTerm
    (a b c : ℝ) (n : ℕ) (y : ℝ) :
    ‖shiftedGaussianXiPrimeLineTerm a b c n y‖ =
      Real.exp (b * (c - 1 / 2)) *
        (Real.exp (a * (c - 1 / 2) ^ 2) * Real.exp (-a * y ^ 2) *
          ‖LSeries.term (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
            (c : ℂ) n‖) := by
  rw [shiftedGaussianXiPrimeLineTerm, norm_mul, Complex.norm_exp,
    norm_gaussianXiPrimeLineTerm]
  congr 2
  norm_num [mul_re, div_re]

theorem integrable_shiftedGaussianXiPrimeLineTerm
    {a b c : ℝ} (ha : 0 < a) (n : ℕ) :
    Integrable (shiftedGaussianXiPrimeLineTerm a b c n) := by
  by_cases hn : n = 0
  · subst n
    have hzero : shiftedGaussianXiPrimeLineTerm a b c 0 = 0 := by
      funext y
      simp [shiftedGaussianXiPrimeLineTerm, gaussianXiPrimeLineTerm, LSeries.term_zero]
    rw [hzero]
    exact MeasureTheory.integrable_zero ℝ ℂ volume
  rw [show shiftedGaussianXiPrimeLineTerm a b c n = fun y : ℝ =>
      (ArithmeticFunction.vonMangoldt n : ℂ) *
        Complex.exp
          (-(a : ℂ) * y ^ 2 +
            (((2 * a * (c - 1 / 2) - Real.log n + b : ℝ) : ℂ) * I) * y +
            (a * (c - 1 / 2) ^ 2 - c * Real.log n + b * (c - 1 / 2) : ℝ)) from
      funext (shiftedGaussianXiPrimeLineTerm_vertical hn)]
  exact (integrable_cexp_quadratic' (by simpa using ha)
    (((2 * a * (c - 1 / 2) - Real.log n + b : ℝ) : ℂ) * I)
    (a * (c - 1 / 2) ^ 2 - c * Real.log n + b * (c - 1 / 2) : ℝ)).const_mul _

theorem integral_norm_shiftedGaussianXiPrimeLineTerm
    {a b c : ℝ} (_ha : 0 < a) (n : ℕ) :
    (∫ y : ℝ, ‖shiftedGaussianXiPrimeLineTerm a b c n y‖) =
      Real.exp (b * (c - 1 / 2)) *
        (Real.exp (a * (c - 1 / 2) ^ 2) * Real.sqrt (Real.pi / a) *
          ‖LSeries.term (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
            (c : ℂ) n‖) := by
  simp_rw [norm_shiftedGaussianXiPrimeLineTerm, mul_assoc]
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_mul_const, integral_gaussian]

theorem summable_integral_norm_shiftedGaussianXiPrimeLineTerm
    {a b c : ℝ} (ha : 0 < a) (hc : 1 < c) :
    Summable (fun n : ℕ =>
      ∫ y : ℝ, ‖shiftedGaussianXiPrimeLineTerm a b c n y‖) := by
  have hbase := summable_integral_norm_gaussianXiPrimeLineTerm ha hc
  apply Summable.congr (hbase.mul_left (Real.exp (b * (c - 1 / 2))))
  intro n
  rw [integral_norm_shiftedGaussianXiPrimeLineTerm ha,
    integral_norm_gaussianXiPrimeLineTerm ha]

theorem hasSum_integral_shiftedGaussianXiPrimeLineTerm
    {a b c : ℝ} (ha : 0 < a) (hc : 1 < c) :
    HasSum (shiftedGaussianVonMangoldtWeight a b)
      (∫ y : ℝ, ∑' n : ℕ, shiftedGaussianXiPrimeLineTerm a b c n y) := by
  refine (MeasureTheory.hasSum_integral_of_summable_integral_norm
    (fun n : ℕ => integrable_shiftedGaussianXiPrimeLineTerm ha n)
    (summable_integral_norm_shiftedGaussianXiPrimeLineTerm ha hc)).congr_fun ?_
  intro n
  exact (integral_shiftedGaussianXiPrimeLineTerm ha n).symm

theorem tsum_shiftedGaussianXiPrimeLineTerm (a b c y : ℝ) :
    (∑' n : ℕ, shiftedGaussianXiPrimeLineTerm a b c n y) =
      Complex.exp ((b : ℂ) * (((c : ℂ) + y * I) - 1 / 2)) *
        (riemannXiGaussianWeight a ((c : ℂ) + y * I) *
          L ↗ArithmeticFunction.vonMangoldt ((c : ℂ) + y * I)) := by
  unfold shiftedGaussianXiPrimeLineTerm
  rw [← tsum_gaussianXiPrimeLineTerm]
  exact tsum_mul_left

theorem integrable_shiftedGaussianXi_mul_vonMangoldtLSeries
    {a b c : ℝ} (ha : 0 < a) (hc : 1 < c) :
    Integrable (fun y : ℝ =>
      Complex.exp ((b : ℂ) * (((c : ℂ) + y * I) - 1 / 2)) *
        (riemannXiGaussianWeight a ((c : ℂ) + y * I) *
          L ↗ArithmeticFunction.vonMangoldt ((c : ℂ) + y * I))) := by
  apply (integrable_gaussianXi_mul_vonMangoldtLSeries ha hc).bdd_mul
  · exact (by fun_prop : Continuous (fun y : ℝ =>
      Complex.exp ((b : ℂ) * (((c : ℂ) + y * I) - 1 / 2)))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun y => by
      change ‖Complex.exp ((b : ℂ) * (((c : ℂ) + y * I) - 1 / 2))‖ ≤
        Real.exp (b * (c - 1 / 2))
      rw [Complex.norm_exp]
      norm_num [mul_re, div_re]

theorem tsum_shiftedGaussianVonMangoldtWeight_eq_integral
    {a b c : ℝ} (ha : 0 < a) (hc : 1 < c) :
    (∑' n : ℕ, shiftedGaussianVonMangoldtWeight a b n) =
      ∫ y : ℝ,
        Complex.exp ((b : ℂ) * (((c : ℂ) + y * I) - 1 / 2)) *
          (riemannXiGaussianWeight a ((c : ℂ) + y * I) *
            L ↗ArithmeticFunction.vonMangoldt ((c : ℂ) + y * I)) := by
  calc
    (∑' n : ℕ, shiftedGaussianVonMangoldtWeight a b n) =
        ∫ y : ℝ, ∑' n : ℕ, shiftedGaussianXiPrimeLineTerm a b c n y :=
      (hasSum_integral_shiftedGaussianXiPrimeLineTerm ha hc).tsum_eq
    _ = _ := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall (tsum_shiftedGaussianXiPrimeLineTerm a b c)

/-- The symmetric prime integrand is the average of the two exponential branches. -/
theorem symmetricGaussianXi_mul_vonMangoldtLSeries_eq_branches
    (a b c y : ℝ) :
    riemannXiSymmetricGaussianWeight a b ((c : ℂ) + y * I) *
        L ↗ArithmeticFunction.vonMangoldt ((c : ℂ) + y * I) =
      (Complex.exp ((b : ℂ) * (((c : ℂ) + y * I) - 1 / 2)) *
          (riemannXiGaussianWeight a ((c : ℂ) + y * I) *
            L ↗ArithmeticFunction.vonMangoldt ((c : ℂ) + y * I)) +
        Complex.exp ((-b : ℝ) * (((c : ℂ) + y * I) - 1 / 2)) *
          (riemannXiGaussianWeight a ((c : ℂ) + y * I) *
            L ↗ArithmeticFunction.vonMangoldt ((c : ℂ) + y * I))) / 2 := by
  rw [riemannXiSymmetricGaussianWeight, Complex.cosh]
  have hneg : -((b : ℂ) * (((c : ℂ) + y * I) - 1 / 2)) =
      ((-b : ℝ) : ℂ) * (((c : ℂ) + y * I) - 1 / 2) := by
    push_cast
    ring
  rw [hneg]
  ring

theorem integrable_symmetricGaussianXi_mul_vonMangoldtLSeries
    {a b c : ℝ} (ha : 0 < a) (hc : 1 < c) :
    Integrable (fun y : ℝ =>
      riemannXiSymmetricGaussianWeight a b ((c : ℂ) + y * I) *
        L ↗ArithmeticFunction.vonMangoldt ((c : ℂ) + y * I)) := by
  rw [show (fun y : ℝ =>
      riemannXiSymmetricGaussianWeight a b ((c : ℂ) + y * I) *
        L ↗ArithmeticFunction.vonMangoldt ((c : ℂ) + y * I)) = fun y : ℝ =>
      (Complex.exp ((b : ℂ) * (((c : ℂ) + y * I) - 1 / 2)) *
          (riemannXiGaussianWeight a ((c : ℂ) + y * I) *
            L ↗ArithmeticFunction.vonMangoldt ((c : ℂ) + y * I)) +
        Complex.exp ((-b : ℝ) * (((c : ℂ) + y * I) - 1 / 2)) *
          (riemannXiGaussianWeight a ((c : ℂ) + y * I) *
            L ↗ArithmeticFunction.vonMangoldt ((c : ℂ) + y * I))) / 2 by
    funext y
    exact symmetricGaussianXi_mul_vonMangoldtLSeries_eq_branches a b c y]
  exact ((integrable_shiftedGaussianXi_mul_vonMangoldtLSeries ha hc).add
    (integrable_shiftedGaussianXi_mul_vonMangoldtLSeries (b := -b) ha hc)).div_const 2

/-- The full symmetric prime integral is the explicit average of translated von-Mangoldt
kernels. -/
theorem tsum_symmetricGaussianVonMangoldtWeight_eq_integral
    {a b c : ℝ} (ha : 0 < a) (hc : 1 < c) :
    (∑' n : ℕ, symmetricGaussianVonMangoldtWeight a b n) =
      ∫ y : ℝ,
        riemannXiSymmetricGaussianWeight a b ((c : ℂ) + y * I) *
          L ↗ArithmeticFunction.vonMangoldt ((c : ℂ) + y * I) := by
  have hp := hasSum_integral_shiftedGaussianXiPrimeLineTerm
    (b := b) ha hc
  have hm := hasSum_integral_shiftedGaussianXiPrimeLineTerm
    (b := -b) ha hc
  have hsum := (hp.add hm).div_const (2 : ℂ)
  have hexplicit : HasSum (symmetricGaussianVonMangoldtWeight a b)
      (((∫ y : ℝ, ∑' n : ℕ, shiftedGaussianXiPrimeLineTerm a b c n y) +
        (∫ y : ℝ, ∑' n : ℕ, shiftedGaussianXiPrimeLineTerm a (-b) c n y)) / 2) := by
    apply hsum.congr_fun
    intro n
    rfl
  rw [hexplicit.tsum_eq]
  simp_rw [tsum_shiftedGaussianXiPrimeLineTerm]
  rw [← MeasureTheory.integral_add
    (integrable_shiftedGaussianXi_mul_vonMangoldtLSeries ha hc)
    (integrable_shiftedGaussianXi_mul_vonMangoldtLSeries (b := -b) ha hc),
    ← MeasureTheory.integral_div]
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    exact (symmetricGaussianXi_mul_vonMangoldtLSeries_eq_branches a b c y).symm

/-- The translated symmetric von-Mangoldt prime-power series is absolutely summable. -/
theorem summable_symmetricGaussianVonMangoldtWeight
    {a b c : ℝ} (ha : 0 < a) (hc : 1 < c) :
    Summable (symmetricGaussianVonMangoldtWeight a b) := by
  have hp := hasSum_integral_shiftedGaussianXiPrimeLineTerm (b := b) ha hc
  have hm := hasSum_integral_shiftedGaussianXiPrimeLineTerm (b := -b) ha hc
  have hsum := (hp.add hm).div_const (2 : ℂ)
  exact (hsum.congr_fun fun n => by rfl).summable

/-- The real-place contribution for the symmetric translated Gaussian family. -/
def symmetricGaussianXiArchimedeanIntegral (a b c : ℝ) : ℂ :=
  ∫ y : ℝ,
    riemannXiSymmetricGaussianWeight a b ((c : ℂ) + y * I) *
      logDeriv Gammaℝ ((c : ℂ) + y * I)

theorem symmetricGaussianXiArchimedeanIntegral_zero (a c : ℝ) :
    symmetricGaussianXiArchimedeanIntegral a 0 c =
      gaussianXiArchimedeanIntegral a c := by
  simp [symmetricGaussianXiArchimedeanIntegral, gaussianXiArchimedeanIntegral,
    riemannXiSymmetricGaussianWeight_zero]

theorem integrable_symmetricGaussianXiArchimedean
    {a b c : ℝ} (ha : 0 < a) (hc : 1 < c) :
    Integrable (fun y : ℝ =>
      riemannXiSymmetricGaussianWeight a b ((c : ℂ) + y * I) *
        logDeriv Gammaℝ ((c : ℂ) + y * I)) := by
  have hbase := integrable_gaussianXiArchimedean ha hc
  have hcoshMeasurable : AEStronglyMeasurable (fun y : ℝ =>
      Complex.cosh ((b : ℂ) * (((c : ℂ) + y * I) - 1 / 2))) :=
    (by fun_prop : Continuous (fun y : ℝ =>
      Complex.cosh ((b : ℂ) * (((c : ℂ) + y * I) - 1 / 2)))).aestronglyMeasurable
  have hbounded : ∀ᶠ y : ℝ in MeasureTheory.ae volume,
      ‖Complex.cosh ((b : ℂ) * (((c : ℂ) + y * I) - 1 / 2))‖ ≤
        Real.exp (|b| * (c - 1 / 2)) :=
    Filter.Eventually.of_forall fun y => norm_cosh_mul_center_le (by
      rw [abs_of_pos (by linarith : 0 < c - 1 / 2)])
  have hproduct := hbase.bdd_mul hcoshMeasurable hbounded
  simpa only [riemannXiSymmetricGaussianWeight, mul_assoc, mul_left_comm] using hproduct

/-- The elementary pole pair for an arbitrary weight. -/
def selectedXiPolePairIntegrandFor (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  F z / (z - 0) + F z / (z - 1)

noncomputable def selectedXiPoleTopHorizontalIntegralFor
    (F : ℂ → ℂ) (c : ℝ) (n : ℕ) : ℂ :=
  ∫ x : ℝ in 1 - c..c,
    selectedXiPolePairIntegrandFor F
      ((x : ℂ) + gaussianXiSelectedHeight c n * I)

noncomputable def selectedXiPoleRightVerticalIntegralFor
    (F : ℂ → ℂ) (c : ℝ) (n : ℕ) : ℂ :=
  ∫ y : ℝ in -gaussianXiSelectedHeight c n..gaussianXiSelectedHeight c n,
    selectedXiPolePairIntegrandFor F ((c : ℂ) + y * I)

theorem selectedXiPolePairIntegrand_one_sub
    {F : ℂ → ℂ} (hsym : ∀ z : ℂ, F (1 - z) = F z) (z : ℂ) :
    selectedXiPolePairIntegrandFor F (1 - z) =
      -selectedXiPolePairIntegrandFor F z := by
  unfold selectedXiPolePairIntegrandFor
  rw [hsym]
  have hzero : (1 : ℂ) - z - 0 = -(z - 1) := by ring
  have hone : (1 : ℂ) - z - 1 = -(z - 0) := by ring
  rw [hzero, hone, div_neg, div_neg]
  ring

theorem selectedXiPoleBottomHorizontalIntegral_eq_neg_top
    {F : ℂ → ℂ} (hsym : ∀ z : ℂ, F (1 - z) = F z) (c : ℝ) (n : ℕ) :
    (∫ x : ℝ in 1 - c..c,
      selectedXiPolePairIntegrandFor F
        ((x : ℂ) - gaussianXiSelectedHeight c n * I)) =
      -selectedXiPoleTopHorizontalIntegralFor F c n := by
  let T : ℝ := gaussianXiSelectedHeight c n
  let f : ℝ → ℂ := fun x =>
    selectedXiPolePairIntegrandFor F ((x : ℂ) + T * I)
  have hpoint (x : ℝ) :
      selectedXiPolePairIntegrandFor F ((x : ℂ) - T * I) = -f (1 - x) := by
    have href := selectedXiPolePairIntegrand_one_sub hsym ((x : ℂ) - T * I)
    have harg : (1 : ℂ) - ((x : ℂ) - T * I) = ((1 - x : ℝ) : ℂ) + T * I := by
      push_cast
      ring
    rw [harg] at href
    simpa only [f, neg_neg, Complex.ofReal_neg] using (congrArg Neg.neg href).symm
  calc
    (∫ x : ℝ in 1 - c..c,
      selectedXiPolePairIntegrandFor F ((x : ℂ) - T * I)) =
        ∫ x : ℝ in 1 - c..c, -f (1 - x) := by
      apply intervalIntegral.integral_congr
      intro x _hx
      exact hpoint x
    _ = -(∫ x : ℝ in 1 - c..c, f (1 - x)) := by
      rw [intervalIntegral.integral_neg]
    _ = -(∫ x : ℝ in 1 - c..c, f x) := by
      rw [intervalIntegral.integral_comp_sub_left f 1]
      congr 2
      all_goals ring
    _ = -selectedXiPoleTopHorizontalIntegralFor F c n := by rfl

theorem selectedXiPoleLeftVerticalIntegral_eq_neg_right
    {F : ℂ → ℂ} (hsym : ∀ z : ℂ, F (1 - z) = F z) (c : ℝ) (n : ℕ) :
    (∫ y : ℝ in -gaussianXiSelectedHeight c n..gaussianXiSelectedHeight c n,
      selectedXiPolePairIntegrandFor F (((1 - c : ℝ) : ℂ) + y * I)) =
      -selectedXiPoleRightVerticalIntegralFor F c n := by
  let T : ℝ := gaussianXiSelectedHeight c n
  let f : ℝ → ℂ := fun y =>
    selectedXiPolePairIntegrandFor F ((c : ℂ) + y * I)
  have hpoint (y : ℝ) :
      selectedXiPolePairIntegrandFor F (((1 - c : ℝ) : ℂ) + y * I) = -f (-y) := by
    have href := selectedXiPolePairIntegrand_one_sub hsym
      (((1 - c : ℝ) : ℂ) + y * I)
    have harg : (1 : ℂ) - (((1 - c : ℝ) : ℂ) + y * I) =
        (c : ℂ) + (-y) * I := by
      push_cast
      ring
    rw [harg] at href
    simpa only [f, neg_neg, Complex.ofReal_neg] using (congrArg Neg.neg href).symm
  calc
    (∫ y : ℝ in -T..T,
      selectedXiPolePairIntegrandFor F (((1 - c : ℝ) : ℂ) + y * I)) =
        ∫ y : ℝ in -T..T, -f (-y) := by
      apply intervalIntegral.integral_congr
      intro y _hy
      exact hpoint y
    _ = -(∫ y : ℝ in -T..T, f (-y)) := by
      rw [intervalIntegral.integral_neg]
    _ = -(∫ y : ℝ in -T..T, f y) := by
      simpa only [zero_sub, neg_neg] using congrArg Neg.neg
        (intervalIntegral.integral_comp_sub_left (a := -T) (b := T) f 0)
    _ = -selectedXiPoleRightVerticalIntegralFor F c n := by rfl

theorem selectedXiPoleRectangleBoundary_eq_top_right
    {F : ℂ → ℂ} (hsym : ∀ z : ℂ, F (1 - z) = F z) (c : ℝ) (n : ℕ) :
    rectangleBoundaryIntegral (selectedXiPolePairIntegrandFor F)
        (1 - c) c (-gaussianXiSelectedHeight c n) (gaussianXiSelectedHeight c n) =
      -2 * selectedXiPoleTopHorizontalIntegralFor F c n +
        2 * I * selectedXiPoleRightVerticalIntegralFor F c n := by
  let T : ℝ := gaussianXiSelectedHeight c n
  rw [rectangleBoundaryIntegral]
  simp only [Complex.ofReal_neg]
  rw [show (∫ x : ℝ in 1 - c..c,
      selectedXiPolePairIntegrandFor F ((x : ℂ) + (-T) * I)) =
        -selectedXiPoleTopHorizontalIntegralFor F c n by
      simpa only [T, neg_mul, sub_eq_add_neg] using
        selectedXiPoleBottomHorizontalIntegral_eq_neg_top hsym c n]
  rw [show (∫ x : ℝ in 1 - c..c,
      selectedXiPolePairIntegrandFor F ((x : ℂ) + T * I)) =
        selectedXiPoleTopHorizontalIntegralFor F c n by rfl]
  rw [show (∫ y : ℝ in -T..T,
      selectedXiPolePairIntegrandFor F ((c : ℂ) + y * I)) =
        selectedXiPoleRightVerticalIntegralFor F c n by rfl]
  rw [show (∫ y : ℝ in -T..T,
      selectedXiPolePairIntegrandFor F (((1 - c : ℝ) : ℂ) + y * I)) =
        -selectedXiPoleRightVerticalIntegralFor F c n by
      exact selectedXiPoleLeftVerticalIntegral_eq_neg_right hsym c n]
  ring

/-- A selected rectangle encloses both elementary poles for every analytic weight. -/
theorem selectedXiPoleRectangleBoundary_eq_residues
    {F : ℂ → ℂ} (hF : Differentiable ℂ F) {c : ℝ} (hc : 1 < c) (n : ℕ) :
    rectangleBoundaryIntegral (selectedXiPolePairIntegrandFor F)
        (1 - c) c (-gaussianXiSelectedHeight c n) (gaussianXiSelectedHeight c n) =
      2 * (Real.pi : ℂ) * I * (F 0 + F 1) := by
  let T : ℝ := gaussianXiSelectedHeight c n
  have hT : 0 < T := lt_trans (gaussianXiHeightScale_pos hc n)
    (gaussianXiSelectedHeight_spec c n).1.1
  have hbottom (rho : ℂ) (him : rho.im = 0) :
      IntervalIntegrable (fun x : ℝ => F ((x : ℂ) + ((-T : ℝ) : ℂ) * I) /
        ((x : ℂ) + ((-T : ℝ) : ℂ) * I - rho)) volume (1 - c) c := by
    apply intervalIntegrable_weighted_cauchyKernel_of_avoids hF (by fun_prop)
    intro x _hx heq
    have hi := congrArg Complex.im heq
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero,
      mul_one, zero_add, Complex.ofReal_neg, neg_re] at hi
    rw [him] at hi
    linarith
  have htop (rho : ℂ) (him : rho.im = 0) :
      IntervalIntegrable (fun x : ℝ => F ((x : ℂ) + T * I) /
        ((x : ℂ) + T * I - rho)) volume (1 - c) c := by
    apply intervalIntegrable_weighted_cauchyKernel_of_avoids hF (by fun_prop)
    intro x _hx heq
    have hi := congrArg Complex.im heq
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero,
      mul_one, zero_add] at hi
    rw [him] at hi
    linarith
  have hright (rho : ℂ) (hre : rho.re < c) :
      IntervalIntegrable (fun y : ℝ => F ((c : ℂ) + y * I) /
        ((c : ℂ) + y * I - rho)) volume (-T) T := by
    apply intervalIntegrable_weighted_cauchyKernel_of_avoids hF (by fun_prop)
    intro y _hy heq
    have hr := congrArg Complex.re heq
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
      zero_mul] at hr
    linarith
  have hleft (rho : ℂ) (hre : 1 - c < rho.re) :
      IntervalIntegrable (fun y : ℝ => F (((1 - c : ℝ) : ℂ) + y * I) /
        (((1 - c : ℝ) : ℂ) + y * I - rho)) volume (-T) T := by
    apply intervalIntegrable_weighted_cauchyKernel_of_avoids hF (by fun_prop)
    intro y _hy heq
    have hr := congrArg Complex.re heq
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
      zero_mul] at hr
    linarith
  have hadd :
      rectangleBoundaryIntegral (selectedXiPolePairIntegrandFor F)
          (1 - c) c (-T) T =
        rectangleBoundaryIntegral (fun z : ℂ => F z / (z - 0))
            (1 - c) c (-T) T +
          rectangleBoundaryIntegral (fun z : ℂ => F z / (z - 1))
            (1 - c) c (-T) T := by
    unfold selectedXiPolePairIntegrandFor
    apply rectangleBoundaryIntegral_add
    · exact hbottom 0 (by simp)
    · exact hbottom 1 (by simp)
    · exact htop 0 (by simp)
    · exact htop 1 (by simp)
    · exact hright 0 (by simp; linarith)
    · exact hright 1 (by simp; linarith)
    · exact hleft 0 (by simp; linarith)
    · exact hleft 1 (by simp; linarith)
  have hres0 :
      rectangleBoundaryIntegral (fun z : ℂ => F z / (z - 0))
          (1 - c) c (-T) T = 2 * (Real.pi : ℂ) * I * F 0 := by
    apply rectangleBoundaryIntegral_weighted_cauchyKernel hF
    all_goals norm_num
    all_goals linarith
  have hres1 :
      rectangleBoundaryIntegral (fun z : ℂ => F z / (z - 1))
          (1 - c) c (-T) T = 2 * (Real.pi : ℂ) * I * F 1 := by
    apply rectangleBoundaryIntegral_weighted_cauchyKernel hF
    all_goals norm_num
    all_goals linarith
  rw [hadd, hres0, hres1]
  ring

theorem selectedXiPoleRightVerticalIntegral_eq_top_add_residues
    {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hsym : ∀ z : ℂ, F (1 - z) = F z)
    {c : ℝ} (hc : 1 < c) (n : ℕ) :
    selectedXiPoleRightVerticalIntegralFor F c n =
      -I * selectedXiPoleTopHorizontalIntegralFor F c n +
        (Real.pi : ℂ) * (F 0 + F 1) := by
  have hres := selectedXiPoleRectangleBoundary_eq_residues hF hc n
  rw [selectedXiPoleRectangleBoundary_eq_top_right hsym] at hres
  apply mul_left_cancel₀ (show (2 : ℂ) * I ≠ 0 by simp)
  calc
    ((2 : ℂ) * I) * selectedXiPoleRightVerticalIntegralFor F c n =
        2 * selectedXiPoleTopHorizontalIntegralFor F c n +
          2 * (Real.pi : ℂ) * I * (F 0 + F 1) := by
      linear_combination hres
    _ = ((2 : ℂ) * I) *
        (-I * selectedXiPoleTopHorizontalIntegralFor F c n +
          (Real.pi : ℂ) * (F 0 + F 1)) := by
      ring_nf
      rw [Complex.I_sq]
      ring

theorem riemannXiSymmetricGaussianWeight_zero_value (a b : ℝ) :
    riemannXiSymmetricGaussianWeight a b 0 =
      (Real.exp (a / 4) * Real.cosh (b / 2) : ℝ) := by
  rw [riemannXiSymmetricGaussianWeight, riemannXiGaussianWeight_zero]
  rw [show (b : ℂ) * (0 - 1 / 2) = ((-b / 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cosh, show -b / 2 = -(b / 2) by ring, Real.cosh_neg]
  push_cast
  ring

theorem riemannXiSymmetricGaussianWeight_one_value (a b : ℝ) :
    riemannXiSymmetricGaussianWeight a b 1 =
      (Real.exp (a / 4) * Real.cosh (b / 2) : ℝ) := by
  rw [show (1 : ℂ) = 1 - 0 by ring,
    riemannXiSymmetricGaussianWeight_one_sub,
    riemannXiSymmetricGaussianWeight_zero_value]

theorem norm_selectedXiPolePairIntegrandFor_horizontal_le
    {F : ℂ → ℂ} {x T : ℝ} (hT : 1 ≤ T) :
    ‖selectedXiPolePairIntegrandFor F ((x : ℂ) + T * I)‖ ≤
      2 * ‖F ((x : ℂ) + T * I)‖ := by
  unfold selectedXiPolePairIntegrandFor
  simp only [sub_zero, div_eq_mul_inv]
  calc
    ‖F ((x : ℂ) + T * I) * ((x : ℂ) + T * I)⁻¹ +
        F ((x : ℂ) + T * I) * ((x : ℂ) + T * I - 1)⁻¹‖ ≤
      ‖F ((x : ℂ) + T * I) * ((x : ℂ) + T * I)⁻¹‖ +
        ‖F ((x : ℂ) + T * I) * ((x : ℂ) + T * I - 1)⁻¹‖ := norm_add_le _ _
    _ ≤ ‖F ((x : ℂ) + T * I)‖ * 1 +
        ‖F ((x : ℂ) + T * I)‖ * 1 := by
      simp only [norm_mul]
      gcongr
      · simpa using norm_inv_horizontal_sub_real_le_one (rho := 0) hT
      · simpa using norm_inv_horizontal_sub_real_le_one (rho := 1) hT
    _ = 2 * ‖F ((x : ℂ) + T * I)‖ := by ring

theorem norm_symmetricGaussianXiPoleTopHorizontalIntegral_le
    {a b c : ℝ} (ha : 0 < a) (hc : 1 < c) (n : ℕ) :
    ‖selectedXiPoleTopHorizontalIntegralFor
        (riemannXiSymmetricGaussianWeight a b) c n‖ ≤
      (2 * (2 * c - 1) * Real.exp (|b| * (c - 1 / 2)) *
        Real.exp (a * (c - 1 / 2) ^ 2)) *
        (gaussianXiHeightScale c n ^ 4 *
          Real.exp (-a * gaussianXiHeightScale c n ^ 2)) := by
  let R : ℝ := gaussianXiHeightScale c n
  let T : ℝ := gaussianXiSelectedHeight c n
  have hRone : 1 ≤ R := by
    dsimp only [R, gaussianXiHeightScale]
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hTone : 1 ≤ T := hRone.trans (gaussianXiSelectedHeight_spec c n).1.1.le
  have hRfour : 1 ≤ R ^ 4 := one_le_pow₀ hRone
  have hpoint : ∀ x ∈ Ι (1 - c) c,
      ‖selectedXiPolePairIntegrandFor (riemannXiSymmetricGaussianWeight a b)
          ((x : ℂ) + T * I)‖ ≤
        2 * Real.exp (|b| * (c - 1 / 2)) *
          Real.exp (a * (c - 1 / 2) ^ 2) *
            (R ^ 4 * Real.exp (-a * R ^ 2)) := by
    intro x hx
    calc
      ‖selectedXiPolePairIntegrandFor (riemannXiSymmetricGaussianWeight a b)
          ((x : ℂ) + T * I)‖ ≤
        2 * ‖riemannXiSymmetricGaussianWeight a b ((x : ℂ) + T * I)‖ :=
          norm_selectedXiPolePairIntegrandFor_horizontal_le hTone
      _ ≤ 2 * (Real.exp (|b| * (c - 1 / 2)) *
          Real.exp (a * (c - 1 / 2) ^ 2) * Real.exp (-a * R ^ 2)) := by
        gcongr
        simpa only [T, R] using
          norm_riemannXiSymmetricGaussianWeight_selectedTopEdge_le ha hc b n
            (Set.uIoc_subset_uIcc hx)
      _ ≤ 2 * Real.exp (|b| * (c - 1 / 2)) *
          Real.exp (a * (c - 1 / 2) ^ 2) *
            (R ^ 4 * Real.exp (-a * R ^ 2)) := by
        have hdecay : Real.exp (-a * R ^ 2) ≤ R ^ 4 * Real.exp (-a * R ^ 2) :=
          le_mul_of_one_le_left (Real.exp_pos _).le hRfour
        calc
          2 * (Real.exp (|b| * (c - 1 / 2)) *
              Real.exp (a * (c - 1 / 2) ^ 2) * Real.exp (-a * R ^ 2)) =
            (2 * Real.exp (|b| * (c - 1 / 2)) *
              Real.exp (a * (c - 1 / 2) ^ 2)) * Real.exp (-a * R ^ 2) := by ring
          _ ≤ (2 * Real.exp (|b| * (c - 1 / 2)) *
              Real.exp (a * (c - 1 / 2) ^ 2)) *
                (R ^ 4 * Real.exp (-a * R ^ 2)) :=
            mul_le_mul_of_nonneg_left hdecay (by positivity)
          _ = 2 * Real.exp (|b| * (c - 1 / 2)) *
              Real.exp (a * (c - 1 / 2) ^ 2) *
                (R ^ 4 * Real.exp (-a * R ^ 2)) := by ring
  have hintegral := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  rw [selectedXiPoleTopHorizontalIntegralFor]
  calc
    ‖∫ x : ℝ in 1 - c..c,
      selectedXiPolePairIntegrandFor (riemannXiSymmetricGaussianWeight a b)
        ((x : ℂ) + T * I)‖ ≤
      (2 * Real.exp (|b| * (c - 1 / 2)) *
        Real.exp (a * (c - 1 / 2) ^ 2) *
          (R ^ 4 * Real.exp (-a * R ^ 2))) * |c - (1 - c)| := hintegral
    _ = _ := by
      rw [abs_of_pos (by linarith : 0 < c - (1 - c))]
      dsimp only [R]
      ring

theorem tendsto_symmetricGaussianXiPoleTopHorizontalIntegral
    {a b c : ℝ} (ha : 0 < a) (hc : 1 < c) :
    Tendsto (selectedXiPoleTopHorizontalIntegralFor
      (riemannXiSymmetricGaussianWeight a b) c) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n => norm_nonneg _
  · exact Filter.Eventually.of_forall fun n =>
      norm_symmetricGaussianXiPoleTopHorizontalIntegral_le ha hc n
  · simpa using
      (tendsto_gaussianXiHeightScale_pow_four_mul_exp_neg_sq
        (a := a) (c := c) ha).const_mul
          (2 * (2 * c - 1) * Real.exp (|b| * (c - 1 / 2)) *
            Real.exp (a * (c - 1 / 2) ^ 2))

theorem tendsto_symmetricGaussianXiPoleRightVerticalIntegral
    {a b c : ℝ} (ha : 0 < a) (hc : 1 < c) :
    Tendsto (selectedXiPoleRightVerticalIntegralFor
      (riemannXiSymmetricGaussianWeight a b) c) atTop
      (𝓝 (2 * (Real.pi : ℂ) *
        (Real.exp (a / 4) * Real.cosh (b / 2) : ℝ))) := by
  have htop := (tendsto_symmetricGaussianXiPoleTopHorizontalIntegral
    (b := b) ha hc).const_mul (-I)
  have hconst : Tendsto (fun _ : ℕ =>
      (Real.pi : ℂ) *
        (riemannXiSymmetricGaussianWeight a b 0 +
          riemannXiSymmetricGaussianWeight a b 1)) atTop
      (𝓝 ((Real.pi : ℂ) *
        (riemannXiSymmetricGaussianWeight a b 0 +
          riemannXiSymmetricGaussianWeight a b 1))) := tendsto_const_nhds
  have hsum := htop.add hconst
  have hright := hsum.congr' (Filter.Eventually.of_forall fun n =>
    (selectedXiPoleRightVerticalIntegral_eq_top_add_residues
      (differentiable_riemannXiSymmetricGaussianWeight a b)
      (riemannXiSymmetricGaussianWeight_one_sub a b) hc n).symm)
  have hvalue :
      (Real.pi : ℂ) *
          ((Real.exp (a / 4) * Real.cosh (b / 2) : ℝ) +
            (Real.exp (a / 4) * Real.cosh (b / 2) : ℝ)) =
        2 * (Real.pi : ℂ) *
          (Real.exp (a / 4) * Real.cosh (b / 2) : ℝ) := by ring
  simpa only [mul_zero, zero_add, riemannXiSymmetricGaussianWeight_zero_value,
    riemannXiSymmetricGaussianWeight_one_value, hvalue] using hright

theorem integrable_symmetricGaussianXiPolePair
    {a b c : ℝ} (ha : 0 < a) (hc : 1 < c) :
    Integrable (fun y : ℝ => selectedXiPolePairIntegrandFor
      (riemannXiSymmetricGaussianWeight a b) ((c : ℂ) + y * I)) := by
  have hbase := integrable_gaussianXiPolePair ha hc
  have hcoshMeasurable : AEStronglyMeasurable (fun y : ℝ =>
      Complex.cosh ((b : ℂ) * (((c : ℂ) + y * I) - 1 / 2))) :=
    (by fun_prop : Continuous (fun y : ℝ =>
      Complex.cosh ((b : ℂ) * (((c : ℂ) + y * I) - 1 / 2)))).aestronglyMeasurable
  have hbounded : ∀ᶠ y : ℝ in MeasureTheory.ae volume,
      ‖Complex.cosh ((b : ℂ) * (((c : ℂ) + y * I) - 1 / 2))‖ ≤
        Real.exp (|b| * (c - 1 / 2)) :=
    Filter.Eventually.of_forall fun y => norm_cosh_mul_center_le (by
      rw [abs_of_pos (by linarith : 0 < c - 1 / 2)])
  have hproduct := hbase.bdd_mul hcoshMeasurable hbounded
  rw [show (fun y : ℝ => selectedXiPolePairIntegrandFor
      (riemannXiSymmetricGaussianWeight a b) ((c : ℂ) + y * I)) =
    fun y : ℝ =>
      Complex.cosh ((b : ℂ) * (((c : ℂ) + y * I) - 1 / 2)) *
        gaussianXiPolePairIntegrand a ((c : ℂ) + y * I) by
      funext y
      unfold selectedXiPolePairIntegrandFor riemannXiSymmetricGaussianWeight
        gaussianXiPolePairIntegrand
      ring]
  exact hproduct

/-- The symmetric pole pair has exactly the two elementary residues. -/
theorem integral_symmetricGaussianXiPolePair_eq
    {a b c : ℝ} (ha : 0 < a) (hc : 1 < c) :
    (∫ y : ℝ, selectedXiPolePairIntegrandFor
      (riemannXiSymmetricGaussianWeight a b) ((c : ℂ) + y * I)) =
      2 * (Real.pi : ℂ) *
        (Real.exp (a / 4) * Real.cosh (b / 2) : ℝ) := by
  have hfull := intervalIntegral_tendsto_integral
    (integrable_symmetricGaussianXiPolePair (b := b) ha hc)
    (tendsto_neg_atTop_atBot.comp (tendsto_gaussianXiSelectedHeight c))
    (tendsto_gaussianXiSelectedHeight c)
  have hfull' : Tendsto (selectedXiPoleRightVerticalIntegralFor
      (riemannXiSymmetricGaussianWeight a b) c) atTop
      (𝓝 (∫ y : ℝ, selectedXiPolePairIntegrandFor
        (riemannXiSymmetricGaussianWeight a b) ((c : ℂ) + y * I))) := by
    change Tendsto
      (fun n : ℕ => ∫ y : ℝ in
        -gaussianXiSelectedHeight c n..gaussianXiSelectedHeight c n,
          selectedXiPolePairIntegrandFor
            (riemannXiSymmetricGaussianWeight a b) ((c : ℂ) + y * I)) atTop
      (𝓝 (∫ y : ℝ, selectedXiPolePairIntegrandFor
        (riemannXiSymmetricGaussianWeight a b) ((c : ℂ) + y * I)))
    simpa only [Function.comp_apply] using hfull
  exact tendsto_nhds_unique hfull'
    (tendsto_symmetricGaussianXiPoleRightVerticalIntegral ha hc)

/-- On each selected right edge, the logarithmic derivative splits into pole, real-place, and
von-Mangoldt terms for the symmetric Gaussian weight. -/
theorem symmetricGaussianXiRightVerticalIntegral_eq_arithmetic_truncations
    {a b c : ℝ} (ha : 0 < a) (hc : 1 < c) (n : ℕ) :
    selectedXiRightVerticalIntegralFor (riemannXiSymmetricGaussianWeight a b) c n =
      selectedXiPoleRightVerticalIntegralFor
          (riemannXiSymmetricGaussianWeight a b) c n +
        (∫ y : ℝ in -gaussianXiSelectedHeight c n..gaussianXiSelectedHeight c n,
          riemannXiSymmetricGaussianWeight a b ((c : ℂ) + y * I) *
            logDeriv Gammaℝ ((c : ℂ) + y * I)) -
        (∫ y : ℝ in -gaussianXiSelectedHeight c n..gaussianXiSelectedHeight c n,
          riemannXiSymmetricGaussianWeight a b ((c : ℂ) + y * I) *
            L ↗ArithmeticFunction.vonMangoldt ((c : ℂ) + y * I)) := by
  let T : ℝ := gaussianXiSelectedHeight c n
  have hpole : IntervalIntegrable (fun y : ℝ =>
      selectedXiPolePairIntegrandFor (riemannXiSymmetricGaussianWeight a b)
        ((c : ℂ) + y * I)) volume (-T) T :=
    (integrable_symmetricGaussianXiPolePair ha hc).intervalIntegrable
  have harch : IntervalIntegrable (fun y : ℝ =>
      riemannXiSymmetricGaussianWeight a b ((c : ℂ) + y * I) *
        logDeriv Gammaℝ ((c : ℂ) + y * I)) volume (-T) T :=
    (integrable_symmetricGaussianXiArchimedean ha hc).intervalIntegrable
  have hprime : IntervalIntegrable (fun y : ℝ =>
      riemannXiSymmetricGaussianWeight a b ((c : ℂ) + y * I) *
        L ↗ArithmeticFunction.vonMangoldt ((c : ℂ) + y * I)) volume (-T) T :=
    (integrable_symmetricGaussianXi_mul_vonMangoldtLSeries ha hc).intervalIntegrable
  have hpoint (y : ℝ) :
      riemannXiSymmetricGaussianWeight a b ((c : ℂ) + y * I) *
          logDeriv riemannXi ((c : ℂ) + y * I) =
        selectedXiPolePairIntegrandFor (riemannXiSymmetricGaussianWeight a b)
            ((c : ℂ) + y * I) +
          riemannXiSymmetricGaussianWeight a b ((c : ℂ) + y * I) *
            logDeriv Gammaℝ ((c : ℂ) + y * I) -
          riemannXiSymmetricGaussianWeight a b ((c : ℂ) + y * I) *
            L ↗ArithmeticFunction.vonMangoldt ((c : ℂ) + y * I) := by
    rw [logDeriv_riemannXi_eq_poles_archimedean_sub_vonMangoldt
      (by simpa using hc)]
    unfold selectedXiPolePairIntegrandFor
    simp only [sub_zero, div_eq_mul_inv]
    ring
  rw [selectedXiRightVerticalIntegralFor, selectedXiPoleRightVerticalIntegralFor]
  change
    (∫ y : ℝ in -T..T,
      riemannXiSymmetricGaussianWeight a b ((c : ℂ) + y * I) *
        logDeriv riemannXi ((c : ℂ) + y * I)) = _
  calc
    (∫ y : ℝ in -T..T,
      riemannXiSymmetricGaussianWeight a b ((c : ℂ) + y * I) *
        logDeriv riemannXi ((c : ℂ) + y * I)) =
      ∫ y : ℝ in -T..T,
        selectedXiPolePairIntegrandFor (riemannXiSymmetricGaussianWeight a b)
            ((c : ℂ) + y * I) +
          riemannXiSymmetricGaussianWeight a b ((c : ℂ) + y * I) *
            logDeriv Gammaℝ ((c : ℂ) + y * I) -
          riemannXiSymmetricGaussianWeight a b ((c : ℂ) + y * I) *
            L ↗ArithmeticFunction.vonMangoldt ((c : ℂ) + y * I) := by
      apply intervalIntegral.integral_congr
      intro y _hy
      exact hpoint y
    _ = (∫ y : ℝ in -T..T,
          selectedXiPolePairIntegrandFor (riemannXiSymmetricGaussianWeight a b)
            ((c : ℂ) + y * I)) +
        (∫ y : ℝ in -T..T,
          riemannXiSymmetricGaussianWeight a b ((c : ℂ) + y * I) *
            logDeriv Gammaℝ ((c : ℂ) + y * I)) -
        (∫ y : ℝ in -T..T,
          riemannXiSymmetricGaussianWeight a b ((c : ℂ) + y * I) *
            L ↗ArithmeticFunction.vonMangoldt ((c : ℂ) + y * I)) := by
      rw [intervalIntegral.integral_sub (hpole.add harch) hprime,
        intervalIntegral.integral_add hpole harch]

theorem tendsto_selectedSymmetricGaussianXiArchimedeanIntegral
    {a b c : ℝ} (ha : 0 < a) (hc : 1 < c) :
    Tendsto
      (fun n : ℕ => ∫ y : ℝ in
        -gaussianXiSelectedHeight c n..gaussianXiSelectedHeight c n,
          riemannXiSymmetricGaussianWeight a b ((c : ℂ) + y * I) *
            logDeriv Gammaℝ ((c : ℂ) + y * I))
      atTop (𝓝 (symmetricGaussianXiArchimedeanIntegral a b c)) := by
  simpa only [symmetricGaussianXiArchimedeanIntegral] using
    tendsto_selectedGaussianXiSymmetricIntervalIntegral
      (integrable_symmetricGaussianXiArchimedean ha hc)

theorem tendsto_selectedSymmetricGaussianXiPrimeIntegral
    {a b c : ℝ} (ha : 0 < a) (hc : 1 < c) :
    Tendsto
      (fun n : ℕ => ∫ y : ℝ in
        -gaussianXiSelectedHeight c n..gaussianXiSelectedHeight c n,
          riemannXiSymmetricGaussianWeight a b ((c : ℂ) + y * I) *
            L ↗ArithmeticFunction.vonMangoldt ((c : ℂ) + y * I))
      atTop (𝓝 (∑' n : ℕ, symmetricGaussianVonMangoldtWeight a b n)) := by
  rw [tsum_symmetricGaussianVonMangoldtWeight_eq_integral ha hc]
  exact tendsto_selectedGaussianXiSymmetricIntervalIntegral
    (integrable_symmetricGaussianXi_mul_vonMangoldtLSeries ha hc)

/-- The two-parameter symmetric translated-Gaussian xi explicit formula. It exposes the absolute
multiplicity-bearing zero sum, both elementary poles, the real-place term, and the two translated
von-Mangoldt Gaussian kernels. -/
theorem symmetricGaussianXi_arithmetic_explicit_formula
    {a b c : ℝ} (ha : 0 < a) (hc : 1 < c) :
    (Real.pi : ℂ) *
        ∑' p : RiemannXiDivisorZeroIndex,
          riemannXiSymmetricGaussianWeight a b (riemannXiDivisorZeroValue p) =
      2 * (Real.pi : ℂ) *
          (Real.exp (a / 4) * Real.cosh (b / 2) : ℝ) +
        symmetricGaussianXiArchimedeanIntegral a b c -
          ∑' n : ℕ, symmetricGaussianVonMangoldtWeight a b n := by
  have hpole := tendsto_symmetricGaussianXiPoleRightVerticalIntegral
    (b := b) ha hc
  have harch := tendsto_selectedSymmetricGaussianXiArchimedeanIntegral
    (b := b) ha hc
  have hprime := tendsto_selectedSymmetricGaussianXiPrimeIntegral
    (b := b) ha hc
  have harithmetic := (hpole.add harch).sub hprime
  have hright : Tendsto
      (selectedXiRightVerticalIntegralFor (riemannXiSymmetricGaussianWeight a b) c)
      atTop
      (𝓝 (2 * (Real.pi : ℂ) *
          (Real.exp (a / 4) * Real.cosh (b / 2) : ℝ) +
        symmetricGaussianXiArchimedeanIntegral a b c -
          ∑' n : ℕ, symmetricGaussianVonMangoldtWeight a b n)) := by
    apply harithmetic.congr'
    exact Filter.Eventually.of_forall fun n =>
      (symmetricGaussianXiRightVerticalIntegral_eq_arithmetic_truncations ha hc n).symm
  exact tendsto_nhds_unique
    (tendsto_symmetricGaussianXiRightVerticalIntegral ha hc b) hright

/-- At zero translation the two-parameter theorem is definitionally compatible with the previous
centered-Gaussian explicit formula. -/
theorem symmetricGaussianXi_arithmetic_explicit_formula_zero
    {a c : ℝ} (ha : 0 < a) (hc : 1 < c) :
    (Real.pi : ℂ) *
        ∑' p : RiemannXiDivisorZeroIndex,
          riemannXiSymmetricGaussianWeight a 0 (riemannXiDivisorZeroValue p) =
      2 * (Real.pi : ℂ) *
          (Real.exp (a / 4) * Real.cosh (0 / 2) : ℝ) +
        symmetricGaussianXiArchimedeanIntegral a 0 c -
          ∑' n : ℕ, symmetricGaussianVonMangoldtWeight a 0 n := by
  simpa only [riemannXiSymmetricGaussianWeight_zero,
    symmetricGaussianXiArchimedeanIntegral_zero,
    symmetricGaussianVonMangoldtWeight_zero, Real.cosh_zero, zero_div, mul_one,
    Complex.ofReal_exp] using gaussianXi_arithmetic_explicit_formula ha hc

end

end LeanLab.Riemann
