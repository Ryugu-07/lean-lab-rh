import LeanLab.Riemann.HardyTangentialTheta

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Hardy's all-order interior integral derivatives

This module identifies every alpha derivative of Hardy's actual Xi integral with an explicit
polynomially weighted kernel.
-/

open Complex Filter MeasureTheory Real Set Topology

namespace LeanLab.Riemann

noncomputable section

/-- The explicit order-`m` alpha derivative of Hardy's interior Xi kernel. -/
def hardyXiInteriorKernelOrder
    (m : ℕ) (alpha : ℂ) (t : ℝ) : ℂ :=
  (Complex.exp (alpha * (t : ℂ)) * (t : ℂ) ^ m +
      Complex.exp (-alpha * (t : ℂ)) * (-(t : ℂ)) ^ m) *
    (hardyXi (2 * t) : ℂ) / (1 / 4 + 4 * t ^ 2)

/-- The integral of the explicit order-`m` kernel. -/
def hardyXiInteriorDerivativeIntegral
    (m : ℕ) (alpha : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0, hardyXiInteriorKernelOrder m alpha t

theorem hasDerivAt_hardyXiInteriorKernelOrder
    (m : ℕ) (alpha : ℂ) (t : ℝ) :
    HasDerivAt
      (fun beta : ℂ =>
        hardyXiInteriorKernelOrder m beta t)
      (hardyXiInteriorKernelOrder (m + 1) alpha t)
      alpha := by
  have hpos :
      HasDerivAt
        (fun beta : ℂ =>
          Complex.exp (beta * (t : ℂ)))
        (Complex.exp (alpha * (t : ℂ)) * (t : ℂ))
        alpha :=
    (Complex.hasDerivAt_exp _).comp alpha
      (by
        simpa only [id_eq, one_mul] using
          (hasDerivAt_id alpha).mul_const (t : ℂ))
  have hneg :
      HasDerivAt
        (fun beta : ℂ =>
          Complex.exp (-beta * (t : ℂ)))
        (Complex.exp (-alpha * (t : ℂ)) * (-(t : ℂ)))
        alpha :=
    (Complex.hasDerivAt_exp _).comp alpha
      (by
        simpa only [id_eq, neg_one_mul] using
          (hasDerivAt_neg alpha).mul_const (t : ℂ))
  have hsum :=
    (hpos.mul_const ((t : ℂ) ^ m)).add
      (hneg.mul_const ((-(t : ℂ)) ^ m))
  have hmul :=
    hsum.mul_const (hardyXi (2 * t) : ℂ)
  have hdiv :=
    hmul.div_const (1 / 4 + 4 * (t : ℂ) ^ 2)
  refine (hdiv.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards with beta
    rfl
  · unfold hardyXiInteriorKernelOrder
    rw [pow_succ, pow_succ]
    ring

private theorem continuous_hardyXiInteriorKernelOrder
    (m : ℕ) (alpha : ℂ) :
    Continuous (hardyXiInteriorKernelOrder m alpha) := by
  unfold hardyXiInteriorKernelOrder
  apply Continuous.div
  · have hExp :
        Continuous fun t : ℝ =>
          Complex.exp (alpha * (t : ℂ)) * (t : ℂ) ^ m +
            Complex.exp (-alpha * (t : ℂ)) *
              (-(t : ℂ)) ^ m := by
      fun_prop
    have hXi :
        Continuous fun t : ℝ =>
          (hardyXi (2 * t) : ℂ) :=
      Complex.continuous_ofReal.comp
        (continuous_hardyXi.comp (by fun_prop))
    exact hExp.mul hXi
  · exact continuous_const.add
      (continuous_const.mul
        (Complex.continuous_ofReal.pow 2))
  · intro t
    rw [show
      (1 / 4 + 4 * (t : ℂ) ^ 2 : ℂ) =
        (((1 / 4 : ℝ) + 4 * t ^ 2 : ℝ) : ℂ) by
          push_cast
          ring]
    exact_mod_cast
      (show (1 / 4 : ℝ) + 4 * t ^ 2 ≠ 0 by
        positivity)

theorem norm_hardyXiInteriorKernelOrder_le
    (m : ℕ) (alpha : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    ‖hardyXiInteriorKernelOrder m alpha t‖ ≤
      2 * |t| ^ m *
        hardyXiExponentialWeight |alpha.re| t := by
  have hden : 0 < (1 / 4 : ℝ) + 4 * t ^ 2 := by
    positivity
  have htAbs : |t| = t := abs_of_nonneg ht
  have hpos :
      alpha.re * t ≤ |alpha.re| * |t| := by
    rw [htAbs]
    exact mul_le_mul_of_nonneg_right
      (le_abs_self alpha.re) ht
  have hneg :
      -alpha.re * t ≤ |alpha.re| * |t| := by
    rw [htAbs]
    exact mul_le_mul_of_nonneg_right
      (neg_le_abs alpha.re) ht
  have hnum :
      ‖Complex.exp (alpha * (t : ℂ)) * (t : ℂ) ^ m +
          Complex.exp (-alpha * (t : ℂ)) *
            (-(t : ℂ)) ^ m‖ ≤
        2 * |t| ^ m *
          Real.exp (|alpha.re| * |t|) := by
    calc
      ‖Complex.exp (alpha * (t : ℂ)) * (t : ℂ) ^ m +
          Complex.exp (-alpha * (t : ℂ)) *
            (-(t : ℂ)) ^ m‖ ≤
          ‖Complex.exp (alpha * (t : ℂ)) *
              (t : ℂ) ^ m‖ +
            ‖Complex.exp (-alpha * (t : ℂ)) *
              (-(t : ℂ)) ^ m‖ :=
        norm_add_le _ _
      _ =
          Real.exp (alpha.re * t) * |t| ^ m +
            Real.exp (-alpha.re * t) * |t| ^ m := by
        rw [norm_mul, norm_mul, Complex.norm_exp,
          Complex.norm_exp, norm_pow, norm_pow,
          norm_neg, Complex.norm_real, Real.norm_eq_abs]
        simp
      _ ≤
          Real.exp (|alpha.re| * |t|) * |t| ^ m +
            Real.exp (|alpha.re| * |t|) * |t| ^ m := by
        gcongr
      _ =
          2 * |t| ^ m *
            Real.exp (|alpha.re| * |t|) := by
        ring
  have hdenNorm :
      ‖(1 / 4 + 4 * (t : ℂ) ^ 2 : ℂ)‖ =
        (1 / 4 : ℝ) + 4 * t ^ 2 := by
    rw [show
      (1 / 4 + 4 * (t : ℂ) ^ 2 : ℂ) =
        (((1 / 4 : ℝ) + 4 * t ^ 2 : ℝ) : ℂ) by
          push_cast
          ring,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hden]
  unfold hardyXiInteriorKernelOrder
    hardyXiExponentialWeight
  rw [norm_div, norm_mul, hdenNorm]
  rw [show
    2 * |t| ^ m *
          (Real.exp (|alpha.re| * |t|) *
            ‖hardyXi (2 * t)‖ /
              ((1 / 4 : ℝ) + 4 * t ^ 2)) =
        (2 * |t| ^ m *
            Real.exp (|alpha.re| * |t|) *
              ‖hardyXi (2 * t)‖) /
          ((1 / 4 : ℝ) + 4 * t ^ 2) by
      ring]
  apply div_le_div_of_nonneg_right _ hden.le
  rw [Complex.norm_real]
  exact mul_le_mul_of_nonneg_right hnum (norm_nonneg _)

theorem integrableOn_hardyXiInteriorKernelOrder
    (m : ℕ) {alpha : ℂ}
    (halpha : alpha ∈ hardyAlphaStrip) :
    IntegrableOn
      (hardyXiInteriorKernelOrder m alpha)
      (Ioi (0 : ℝ)) := by
  have ha : |alpha.re| < Real.pi / 2 := halpha
  have hmajor :
      IntegrableOn
        (fun t : ℝ =>
          2 * |t| ^ m *
            hardyXiExponentialWeight |alpha.re| t)
        (Ioi (0 : ℝ)) := by
    have hfull :=
      (integrable_abs_pow_mul_hardyXiExponentialWeight
        m ha).const_mul 2
    simpa [mul_assoc] using hfull.integrableOn
  refine Integrable.mono' hmajor
    (continuous_hardyXiInteriorKernelOrder
      m alpha).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards with t ht
  have hbound :=
    norm_hardyXiInteriorKernelOrder_le
      m alpha (le_of_lt ht)
  have hmajorNonneg :
      0 ≤ 2 * |t| ^ m *
        hardyXiExponentialWeight |alpha.re| t := by
    unfold hardyXiExponentialWeight
    positivity
  simpa [Real.norm_eq_abs,
    abs_of_nonneg hmajorNonneg] using hbound

private theorem hardyXiExponentialWeight_mono_local
    {a c t : ℝ} (hac : a ≤ c) :
    hardyXiExponentialWeight a t ≤
      hardyXiExponentialWeight c t := by
  unfold hardyXiExponentialWeight
  have hden :
      0 ≤ (1 / 4 : ℝ) + 4 * t ^ 2 := by
    positivity
  apply div_le_div_of_nonneg_right _ hden
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right hac (abs_nonneg t))

theorem hasDerivAt_hardyXiInteriorDerivativeIntegral
    (m : ℕ) {alpha : ℂ}
    (halpha : alpha ∈ hardyAlphaStrip) :
    HasDerivAt (hardyXiInteriorDerivativeIntegral m)
      (hardyXiInteriorDerivativeIntegral (m + 1) alpha)
      alpha := by
  let a : ℝ :=
    (|alpha.re| + Real.pi / 2) / 2
  have halphaA : |alpha.re| < a := by
    dsimp only [a]
    have hstrip : |alpha.re| < Real.pi / 2 :=
      halpha
    linarith
  have ha : a < Real.pi / 2 := by
    dsimp only [a]
    have hstrip : |alpha.re| < Real.pi / 2 :=
      halpha
    linarith
  let s : Set ℂ :=
    {beta : ℂ | |beta.re| < a}
  have hsOpen : IsOpen s := by
    exact isOpen_lt Complex.continuous_re.abs
      continuous_const
  have hs : s ∈ 𝓝 alpha :=
    hsOpen.mem_nhds halphaA
  have hFMeas :
      ∀ᶠ beta : ℂ in 𝓝 alpha,
        AEStronglyMeasurable
          (hardyXiInteriorKernelOrder m beta)
          (volume.restrict (Ioi (0 : ℝ))) :=
    Eventually.of_forall fun beta =>
      (continuous_hardyXiInteriorKernelOrder
        m beta).aestronglyMeasurable
  have hFInt :
      Integrable
        (hardyXiInteriorKernelOrder m alpha)
        (volume.restrict (Ioi (0 : ℝ))) :=
    integrableOn_hardyXiInteriorKernelOrder
      m halpha
  have hF'Meas :
      AEStronglyMeasurable
        (hardyXiInteriorKernelOrder (m + 1) alpha)
        (volume.restrict (Ioi (0 : ℝ))) :=
    (continuous_hardyXiInteriorKernelOrder
      (m + 1) alpha).aestronglyMeasurable
  have hBound :
      ∀ᵐ t : ℝ ∂volume.restrict (Ioi (0 : ℝ)),
        ∀ beta ∈ s,
          ‖hardyXiInteriorKernelOrder
              (m + 1) beta t‖ ≤
            2 * |t| ^ (m + 1) *
              hardyXiExponentialWeight a t := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with t ht
    intro beta hbeta
    calc
      ‖hardyXiInteriorKernelOrder
          (m + 1) beta t‖ ≤
          2 * |t| ^ (m + 1) *
            hardyXiExponentialWeight |beta.re| t :=
        norm_hardyXiInteriorKernelOrder_le
          (m + 1) beta (le_of_lt ht)
      _ ≤
          2 * |t| ^ (m + 1) *
            hardyXiExponentialWeight a t := by
        gcongr
        exact hardyXiExponentialWeight_mono_local
          (le_of_lt hbeta)
  have hBoundInt :
      Integrable
        (fun t : ℝ =>
          2 * |t| ^ (m + 1) *
            hardyXiExponentialWeight a t)
        (volume.restrict (Ioi (0 : ℝ))) := by
    change IntegrableOn
      (fun t : ℝ =>
        2 * |t| ^ (m + 1) *
          hardyXiExponentialWeight a t)
      (Ioi (0 : ℝ)) volume
    have hfull :=
      (integrable_abs_pow_mul_hardyXiExponentialWeight
        (m + 1) ha).const_mul 2
    simpa [mul_assoc] using hfull.integrableOn
  have hDiff :
      ∀ᵐ t : ℝ ∂volume.restrict (Ioi (0 : ℝ)),
        ∀ beta ∈ s,
          HasDerivAt
            (fun gamma : ℂ =>
              hardyXiInteriorKernelOrder
                m gamma t)
            (hardyXiInteriorKernelOrder
              (m + 1) beta t) beta :=
    Eventually.of_forall fun t beta _ =>
      hasDerivAt_hardyXiInteriorKernelOrder
        m beta t
  have hIntegral :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Ioi (0 : ℝ)))
      (F := hardyXiInteriorKernelOrder m)
      (F' := hardyXiInteriorKernelOrder (m + 1))
      (bound := fun t : ℝ =>
        2 * |t| ^ (m + 1) *
          hardyXiExponentialWeight a t)
      hs hFMeas hFInt hF'Meas hBound hBoundInt hDiff
  refine (hIntegral.2.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards with beta
    rfl
  · rfl

theorem hardyXiInteriorDerivativeIntegral_zero
    (alpha : ℂ) :
    hardyXiInteriorDerivativeIntegral 0 alpha =
      hardyXiInteriorIntegral alpha := by
  unfold hardyXiInteriorDerivativeIntegral
    hardyXiInteriorIntegral
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  unfold hardyXiInteriorKernelOrder
  simp

theorem iteratedDeriv_hardyXiInteriorIntegral_eq
    (m : ℕ) {alpha : ℂ}
    (halpha : alpha ∈ hardyAlphaStrip) :
    iteratedDeriv m hardyXiInteriorIntegral alpha =
      hardyXiInteriorDerivativeIntegral m alpha := by
  induction m generalizing alpha with
  | zero =>
      rw [iteratedDeriv_zero,
        hardyXiInteriorDerivativeIntegral_zero]
  | succ m ih =>
      rw [show m + 1 = Nat.succ m by omega,
        iteratedDeriv_succ]
      have heq :
          iteratedDeriv m hardyXiInteriorIntegral =ᶠ[𝓝 alpha]
            hardyXiInteriorDerivativeIntegral m := by
        filter_upwards
            [isOpen_hardyAlphaStrip.mem_nhds halpha]
            with beta hbeta
        exact ih hbeta
      rw [heq.deriv_eq]
      exact
        (hasDerivAt_hardyXiInteriorDerivativeIntegral
          m halpha).deriv

theorem hardyXiInteriorKernelOrder_even_ofReal
    (alpha : ℝ) (p : ℕ) (t : ℝ) :
    hardyXiInteriorKernelOrder
        (2 * p) (alpha : ℂ) t =
      (hardyXiAbelMomentIntegrand alpha p t : ℂ) := by
  have hpos :
      Complex.exp ((alpha : ℂ) * (t : ℂ)) =
        (Real.exp (alpha * t) : ℂ) := by
    rw [← Complex.ofReal_mul, Complex.ofReal_exp]
  have hneg :
      Complex.exp (-(alpha : ℂ) * (t : ℂ)) =
        (Real.exp (-alpha * t) : ℂ) := by
    rw [show
        -(alpha : ℂ) * (t : ℂ) =
          ((-alpha * t : ℝ) : ℂ) by
        push_cast
        ring,
      Complex.ofReal_exp]
  have hnegPow :
      (-(t : ℂ)) ^ (2 * p) =
        (t : ℂ) ^ (2 * p) := by
    rw [pow_mul, pow_mul]
    congr 1
    ring
  unfold hardyXiInteriorKernelOrder
    hardyXiAbelMomentIntegrand
  rw [hpos, hneg, hnegPow]
  push_cast
  ring

theorem hardyXiInteriorDerivativeIntegral_even_ofReal
    (alpha : ℝ) (p : ℕ) :
    hardyXiInteriorDerivativeIntegral
        (2 * p) (alpha : ℂ) =
      (hardyXiAbelMoment alpha p : ℂ) := by
  unfold hardyXiInteriorDerivativeIntegral
    hardyXiAbelMoment
  rw [← integral_complex_ofReal]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  exact hardyXiInteriorKernelOrder_even_ofReal
    alpha p t

theorem hardyXiInteriorIntegral_iteratedDeriv_real
    (p : ℕ) {alpha : ℝ}
    (halpha : |alpha| < Real.pi / 2) :
    iteratedDeriv (2 * p) hardyXiInteriorIntegral
        (alpha : ℂ) =
      (hardyXiAbelMoment alpha p : ℂ) := by
  have halphaComplex :
      (alpha : ℂ) ∈ hardyAlphaStrip := by
    simpa [hardyAlphaStrip] using halpha
  rw [iteratedDeriv_hardyXiInteriorIntegral_eq
      (2 * p) halphaComplex,
    hardyXiInteriorDerivativeIntegral_even_ofReal]

theorem integrableOn_hardyXiAbelMomentIntegrand_unconditional
    (alpha : ℝ) (p : ℕ)
    (halpha : |alpha| < Real.pi / 2) :
    IntegrableOn
      (hardyXiAbelMomentIntegrand alpha p)
      (Ioi (0 : ℝ)) := by
  change Integrable
    (hardyXiAbelMomentIntegrand alpha p)
    (volume.restrict (Ioi (0 : ℝ)))
  have halphaComplex :
      (alpha : ℂ) ∈ hardyAlphaStrip := by
    simpa [hardyAlphaStrip] using halpha
  have hcomplex :
      Integrable
        (hardyXiInteriorKernelOrder
          (2 * p) (alpha : ℂ))
        (volume.restrict (Ioi (0 : ℝ))) :=
    integrableOn_hardyXiInteriorKernelOrder
      (2 * p) halphaComplex
  refine Integrable.mono' hcomplex.norm
    (continuous_hardyXiAbelMomentIntegrand
      alpha p).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards with t ht
  rw [← Complex.norm_real,
    ← hardyXiInteriorKernelOrder_even_ofReal]

/-- Hardy's equation (3) before differentiation: the interior integral plus the theta
boundary term is an elementary cosine. -/
theorem hardyEquationThreePrimitive
    {alpha : ℂ} (halpha : alpha ∈ hardyAlphaStrip) :
    hardyXiInteriorIntegral alpha +
        hardyThetaBoundaryTerm alpha =
      (Real.pi : ℂ) * Complex.cos (alpha / 4) := by
  have hexpCancel :
      Complex.exp (Complex.I * alpha / 4) *
          Complex.exp (-(Complex.I * alpha) / 4) =
        1 := by
    rw [← Complex.exp_add]
    rw [show
      Complex.I * alpha / 4 +
          -(Complex.I * alpha) / 4 = 0 by
        ring,
      Complex.exp_zero]
  have hexpHalf :
      Complex.exp (Complex.I * alpha / 4) *
          Complex.exp (-(Complex.I * alpha) / 2) =
        Complex.exp (-(Complex.I * alpha) / 4) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hcosPos :
      Complex.exp ((alpha / 4) * Complex.I) =
        Complex.exp (Complex.I * alpha / 4) := by
    congr 1
    ring
  have hcosNeg :
      Complex.exp (-(alpha / 4) * Complex.I) =
        Complex.exp (-(Complex.I * alpha) / 4) := by
    congr 1
    ring
  rw [hardyThetaBoundaryTerm, ← hardyEquationTwo halpha]
  unfold hardyEquationTwoLeft Complex.cos
  rw [hcosPos, hcosNeg]
  calc
    hardyXiInteriorIntegral alpha +
          (((Real.pi / 2 : ℝ) : ℂ)) *
            Complex.exp (Complex.I * alpha / 4) *
              (1 + Complex.exp (-(Complex.I * alpha) / 2) -
                (((2 / Real.pi : ℝ) : ℂ)) *
                  Complex.exp (-(Complex.I * alpha) / 4) *
                    hardyXiInteriorIntegral alpha) =
        hardyXiInteriorIntegral alpha +
          (((Real.pi / 2 : ℝ) : ℂ)) *
            Complex.exp (Complex.I * alpha / 4) +
          (((Real.pi / 2 : ℝ) : ℂ)) *
            (Complex.exp (Complex.I * alpha / 4) *
              Complex.exp (-(Complex.I * alpha) / 2)) -
          (((Real.pi / 2 : ℝ) : ℂ)) *
            (((2 / Real.pi : ℝ) : ℂ)) *
            (Complex.exp (Complex.I * alpha / 4) *
              Complex.exp (-(Complex.I * alpha) / 4)) *
            hardyXiInteriorIntegral alpha := by
          ring
    _ =
        hardyXiInteriorIntegral alpha +
          (((Real.pi / 2 : ℝ) : ℂ)) *
            Complex.exp (Complex.I * alpha / 4) +
          (((Real.pi / 2 : ℝ) : ℂ)) *
            Complex.exp (-(Complex.I * alpha) / 4) -
          (((Real.pi / 2 : ℝ) : ℂ)) *
            (((2 / Real.pi : ℝ) : ℂ)) *
            hardyXiInteriorIntegral alpha := by
          rw [hexpHalf, hexpCancel]
          ring
    _ =
        (Real.pi : ℂ) *
          ((Complex.exp (Complex.I * alpha / 4) +
              Complex.exp (-(Complex.I * alpha) / 4)) / 2) := by
          push_cast
          field_simp [Real.pi_ne_zero]
          ring

/-- The exact even derivative of the elementary side of Hardy's equation (3). -/
theorem iteratedDeriv_hardyEquationThreeRight
    (p : ℕ) (alpha : ℂ) :
    iteratedDeriv (2 * p)
        (fun beta : ℂ =>
          (Real.pi : ℂ) * Complex.cos (beta / 4))
        alpha =
      (Real.pi : ℂ) * (1 / 4 : ℂ) ^ (2 * p) *
        (-1 : ℂ) ^ p * Complex.cos (alpha / 4) := by
  rw [iteratedDeriv_const_mul_field]
  have hscale :=
    congrFun
      (iteratedDeriv_comp_const_mul
        (n := 2 * p) Complex.contDiff_cos
        (1 / 4 : ℂ))
      alpha
  rw [show
      (fun beta : ℂ => Complex.cos (beta / 4)) =
        (fun beta : ℂ =>
          Complex.cos ((1 / 4 : ℂ) * beta)) by
        funext beta
        congr 1
        ring,
    hscale,
    Complex.iteratedDeriv_even_cos]
  simp only [Pi.mul_apply, Pi.pow_apply,
    Pi.neg_apply, Pi.one_apply]
  ring

/-- Hardy's equation (3) after `2p` complex derivatives, still at an interior strip point. -/
theorem hardyEquationThreeEvenDerivative
    (p : ℕ) {alpha : ℂ}
    (halpha : alpha ∈ hardyAlphaStrip) :
    iteratedDeriv (2 * p)
          hardyXiInteriorIntegral alpha +
        iteratedDeriv (2 * p)
          hardyThetaBoundaryTerm alpha =
      (Real.pi : ℂ) * (1 / 4 : ℂ) ^ (2 * p) *
        (-1 : ℂ) ^ p * Complex.cos (alpha / 4) := by
  have hInterior :
      ContDiffAt ℂ (2 * p)
        hardyXiInteriorIntegral alpha :=
    (analyticOnNhd_hardyXiInteriorIntegral
      alpha halpha).contDiffAt
  have hTheta :
      ContDiffAt ℂ (2 * p)
        hardyThetaAlpha alpha :=
    (analyticOnNhd_hardyThetaAlpha
      alpha halpha).contDiffAt
  have hExp :
      ContDiffAt ℂ (2 * p)
        (fun beta : ℂ =>
          Complex.exp (Complex.I * beta / 4))
        alpha := by
    fun_prop
  have hBoundary :
      ContDiffAt ℂ (2 * p)
        hardyThetaBoundaryTerm alpha := by
    unfold hardyThetaBoundaryTerm
    exact (contDiffAt_const.mul hExp).mul hTheta
  have hlocal :
      (hardyXiInteriorIntegral +
        hardyThetaBoundaryTerm) =ᶠ[𝓝 alpha]
        (fun beta : ℂ =>
          (Real.pi : ℂ) *
            Complex.cos (beta / 4)) := by
    filter_upwards
        [isOpen_hardyAlphaStrip.mem_nhds halpha]
        with beta hbeta
    exact hardyEquationThreePrimitive hbeta
  have hderiv :=
    hlocal.iteratedDeriv_eq (2 * p)
  rw [iteratedDeriv_add hInterior hBoundary,
    iteratedDeriv_hardyEquationThreeRight] at hderiv
  exact hderiv

/-- Equation (3) expressed with Hardy's real Abel moment at an interior real parameter. -/
theorem hardyEquationThreeMomentIdentity
    (p : ℕ) {alpha : ℝ}
    (halpha : |alpha| < Real.pi / 2) :
    (hardyXiAbelMoment alpha p : ℂ) +
        iteratedDeriv (2 * p)
          hardyThetaBoundaryTerm (alpha : ℂ) =
      (Real.pi : ℂ) * (1 / 4 : ℂ) ^ (2 * p) *
        (-1 : ℂ) ^ p *
          Complex.cos ((alpha : ℂ) / 4) := by
  have halphaComplex :
      (alpha : ℂ) ∈ hardyAlphaStrip := by
    simpa [hardyAlphaStrip] using halpha
  have hEq :=
    hardyEquationThreeEvenDerivative
      p halphaComplex
  rw [hardyXiInteriorIntegral_iteratedDeriv_real
      p halpha] at hEq
  exact hEq

/-- The elementary endpoint value in equation (3), in the real normalization of the
Abel-moment law. -/
theorem hardyEquationThreeEndpointValue
    (p : ℕ) :
    (Real.pi : ℂ) * (1 / 4 : ℂ) ^ (2 * p) *
          (-1 : ℂ) ^ p *
          Complex.cos
            (((Real.pi / 2 : ℝ) : ℂ) / 4) =
      ((((-1 : ℝ) ^ p) * Real.pi *
          Real.cos (Real.pi / 8) /
          4 ^ (2 * p) : ℝ) : ℂ) := by
  rw [show
      (((Real.pi / 2 : ℝ) : ℂ) / 4) =
        ((Real.pi / 8 : ℝ) : ℂ) by
      push_cast
      ring,
    ← Complex.ofReal_cos]
  push_cast
  norm_num [div_pow]
  ring

/-- The elementary side of equation (3) has Hardy's stated left endpoint limit. -/
theorem tendsto_hardyEquationThreeRight_ofReal
    (p : ℕ) :
    Tendsto
      (fun alpha : ℝ =>
        (Real.pi : ℂ) * (1 / 4 : ℂ) ^ (2 * p) *
          (-1 : ℂ) ^ p *
          Complex.cos ((alpha : ℂ) / 4))
      (𝓝[<] (Real.pi / 2))
      (𝓝 ((((-1 : ℝ) ^ p) * Real.pi *
          Real.cos (Real.pi / 8) /
          4 ^ (2 * p) : ℝ) : ℂ)) := by
  have hcontinuous :
      Continuous
        (fun alpha : ℝ =>
          (Real.pi : ℂ) * (1 / 4 : ℂ) ^ (2 * p) *
            (-1 : ℂ) ^ p *
            Complex.cos ((alpha : ℂ) / 4)) := by
    fun_prop
  have hfull :
      Tendsto
        (fun alpha : ℝ =>
          (Real.pi : ℂ) * (1 / 4 : ℂ) ^ (2 * p) *
            (-1 : ℂ) ^ p *
            Complex.cos ((alpha : ℂ) / 4))
        (𝓝 (Real.pi / 2))
        (𝓝 ((Real.pi : ℂ) *
          (1 / 4 : ℂ) ^ (2 * p) *
          (-1 : ℂ) ^ p *
          Complex.cos
            (((Real.pi / 2 : ℝ) : ℂ) / 4))) :=
    hcontinuous.continuousAt
  have hlimit :
      Tendsto
        (fun alpha : ℝ =>
          (Real.pi : ℂ) * (1 / 4 : ℂ) ^ (2 * p) *
            (-1 : ℂ) ^ p *
            Complex.cos ((alpha : ℂ) / 4))
        (𝓝[<] (Real.pi / 2))
        (𝓝 ((Real.pi : ℂ) *
          (1 / 4 : ℂ) ^ (2 * p) *
          (-1 : ℂ) ^ p *
          Complex.cos
            (((Real.pi / 2 : ℝ) : ℂ) / 4))) :=
    hfull.mono_left inf_le_left
  rw [hardyEquationThreeEndpointValue p] at hlimit
  exact hlimit

/-- Hardy's Abel moment has the source left endpoint limit, with no boundary
integrability assumption. -/
theorem tendsto_hardyXiAbelMoment_unconditional
    (p : ℕ) :
    Tendsto
      (fun alpha : ℝ =>
        hardyXiAbelMoment alpha p)
      (𝓝[<] (Real.pi / 2))
      (𝓝 (((-1 : ℝ) ^ p) * Real.pi *
        Real.cos (Real.pi / 8) /
        4 ^ (2 * p))) := by
  let endpoint : ℝ :=
    ((-1 : ℝ) ^ p) * Real.pi *
      Real.cos (Real.pi / 8) /
      4 ^ (2 * p)
  have hRight :=
    tendsto_hardyEquationThreeRight_ofReal p
  have hTheta :=
    tendsto_iteratedDeriv_hardyThetaBoundaryTerm p
  have hDifference :
      Tendsto
        (fun alpha : ℝ =>
          (Real.pi : ℂ) *
              (1 / 4 : ℂ) ^ (2 * p) *
              (-1 : ℂ) ^ p *
              Complex.cos ((alpha : ℂ) / 4) -
            iteratedDeriv (2 * p)
              hardyThetaBoundaryTerm
              (alpha : ℂ))
        (𝓝[<] (Real.pi / 2))
        (𝓝 (endpoint : ℂ)) := by
    simpa only [sub_zero] using hRight.sub hTheta
  have heventual :
      (fun alpha : ℝ =>
        (Real.pi : ℂ) *
            (1 / 4 : ℂ) ^ (2 * p) *
            (-1 : ℂ) ^ p *
            Complex.cos ((alpha : ℂ) / 4) -
          iteratedDeriv (2 * p)
            hardyThetaBoundaryTerm
            (alpha : ℂ)) =ᶠ[𝓝[<] (Real.pi / 2)]
        (fun alpha : ℝ =>
          (hardyXiAbelMoment alpha p : ℂ)) := by
    filter_upwards
        [Ioo_mem_nhdsLT
          (neg_lt_self Real.pi_div_two_pos)]
        with alpha hstrip
    have hmoment :=
      hardyEquationThreeMomentIdentity p
        (abs_lt.mpr hstrip)
    exact (eq_sub_iff_add_eq.mpr hmoment).symm
  have hComplex :
      Tendsto
        (fun alpha : ℝ =>
          (hardyXiAbelMoment alpha p : ℂ))
        (𝓝[<] (Real.pi / 2))
        (𝓝 (endpoint : ℂ)) :=
    hDifference.congr' heventual
  have hRe :
      ContinuousAt Complex.re
        (endpoint : ℂ) :=
    Complex.continuous_re.continuousAt
  have hReTendsto :
      Tendsto Complex.re
        (𝓝 (endpoint : ℂ))
        (𝓝 ((endpoint : ℂ).re)) :=
    hRe
  have hReal :=
    hReTendsto.comp hComplex
  change Tendsto
    (fun alpha : ℝ =>
      ((hardyXiAbelMoment alpha p : ℂ)).re)
    (𝓝[<] (Real.pi / 2))
    (𝓝 ((endpoint : ℂ).re)) at hReal
  dsimp only [endpoint] at hReal
  simpa only [Complex.ofReal_re] using hReal

/-- The analytic input used by Hardy's sign-amplification argument is unconditional. -/
theorem hardyXiAbelMomentLaw_unconditional :
    HardyXiAbelMomentLaw where
  integrable :=
    integrableOn_hardyXiAbelMomentIntegrand_unconditional
  tendsto :=
    tendsto_hardyXiAbelMoment_unconditional

/-- Hardy's 1914 theorem: the completed zeta function has infinitely many zeros on the
critical line. -/
theorem infinite_criticalLineZeros_hardy :
    Set.Infinite {t : ℝ |
      IsNontrivialZero (hardyCriticalLinePoint t)} :=
  infinite_criticalLineZeros_of_hardyXiAbelMomentLaw
    hardyXiAbelMomentLaw_unconditional

end

end LeanLab.Riemann
