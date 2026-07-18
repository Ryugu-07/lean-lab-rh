import LeanLab.Riemann.DeBruijnNewmanHermiteSplitting

set_option linter.style.header false

/-!
# The Polymath imaginary Gaussian representation

This file formalizes the heat-kernel identity used in equation `(htz)` of the Polymath
de Bruijn-Newman upper-bound paper. The Gaussian normalization is `gaussianReal 0 2`, so an
imaginary translation by `r * Y` advances the heat parameter by exactly `r ^ 2`.
-/

open Complex Filter MeasureTheory ProbabilityTheory Real Set Topology

namespace LeanLab.Riemann

noncomputable section

/-- Every complex exponential has a finite moment under the centered variance-two Gaussian. -/
theorem integrable_cexp_mul_gaussianReal_zero_two (a : ℂ) :
    MeasureTheory.Integrable (fun y : ℝ ↦ Complex.exp (a * y))
      (ProbabilityTheory.gaussianReal 0 2) := by
  apply integrable_cexp_mul_of_re_mem_integrableExpSet (X := id)
  · exact measurable_id.aemeasurable
  · simp

/-- The exact complex MGF of the centered variance-two Gaussian. -/
theorem integral_cexp_mul_gaussianReal_zero_two (a : ℂ) :
    ∫ y : ℝ, Complex.exp (a * y) ∂ProbabilityTheory.gaussianReal 0 2 =
      Complex.exp (a ^ 2) := by
  change ProbabilityTheory.complexMGF id (ProbabilityTheory.gaussianReal 0 2) a = _
  rw [ProbabilityTheory.complexMGF_id_gaussianReal]
  congr 1
  norm_num

/-- Absolute-value exponential moments are finite under the centered variance-two Gaussian. -/
theorem integrable_rexp_mul_abs_gaussianReal_zero_two (a : ℝ) :
    MeasureTheory.Integrable (fun y : ℝ ↦ Real.exp (a * |y|))
      (ProbabilityTheory.gaussianReal 0 2) := by
  let μ := ProbabilityTheory.gaussianReal 0 2
  have hpos : MeasureTheory.Integrable (fun y : ℝ ↦ Real.exp (a * y)) μ :=
    ProbabilityTheory.integrable_exp_mul_gaussianReal a
  have hneg : MeasureTheory.Integrable (fun y : ℝ ↦ Real.exp (-a * y)) μ :=
    ProbabilityTheory.integrable_exp_mul_gaussianReal (-a)
  have hpoint (y : ℝ) :
      Real.exp (a * |y|) ≤ Real.exp (a * y) + Real.exp (-a * y) := by
    rcases le_total 0 y with hy | hy
    · rw [abs_of_nonneg hy]
      exact le_add_of_nonneg_right (Real.exp_pos _).le
    · rw [abs_of_nonpos hy]
      have : a * -y = -a * y := by ring
      rw [this]
      exact le_add_of_nonneg_left (Real.exp_pos _).le
  apply MeasureTheory.Integrable.mono' (hpos.add hneg)
  · fun_prop
  · apply MeasureTheory.ae_of_all μ
    intro y
    simpa only [Pi.add_apply, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hpoint y

/-- The absolute-value exponential moment is bounded by the sum of the two exact Gaussian
moments. This is the domination input for the imaginary-shift product integral. -/
theorem integral_rexp_mul_abs_gaussianReal_zero_two_le (a : ℝ) :
    ∫ y : ℝ, Real.exp (a * |y|) ∂ProbabilityTheory.gaussianReal 0 2 ≤
      2 * Real.exp (a ^ 2) := by
  let μ := ProbabilityTheory.gaussianReal 0 2
  have hpos : MeasureTheory.Integrable (fun y : ℝ ↦ Real.exp (a * y)) μ :=
    ProbabilityTheory.integrable_exp_mul_gaussianReal a
  have hneg : MeasureTheory.Integrable (fun y : ℝ ↦ Real.exp (-a * y)) μ :=
    ProbabilityTheory.integrable_exp_mul_gaussianReal (-a)
  have hpoint (y : ℝ) :
      Real.exp (a * |y|) ≤ Real.exp (a * y) + Real.exp (-a * y) := by
    rcases le_total 0 y with hy | hy
    · rw [abs_of_nonneg hy]
      exact le_add_of_nonneg_right (Real.exp_pos _).le
    · rw [abs_of_nonpos hy]
      have : a * -y = -a * y := by ring
      rw [this]
      exact le_add_of_nonneg_left (Real.exp_pos _).le
  have habs := integrable_rexp_mul_abs_gaussianReal_zero_two a
  calc
    (∫ y : ℝ, Real.exp (a * |y|) ∂μ) ≤
        ∫ y : ℝ, (Real.exp (a * y) + Real.exp (-a * y)) ∂μ :=
      MeasureTheory.integral_mono_ae habs (hpos.add hneg)
        (MeasureTheory.ae_of_all μ hpoint)
    _ = Real.exp (a ^ 2) + Real.exp ((-a) ^ 2) := by
      rw [MeasureTheory.integral_add hpos hneg]
      change ProbabilityTheory.mgf id μ a + ProbabilityTheory.mgf id μ (-a) = _
      rw [ProbabilityTheory.mgf_id_gaussianReal]
      norm_num
    _ = 2 * Real.exp (a ^ 2) := by ring_nf

/-- Exponential expansion of the cosine along an imaginary translate. -/
theorem complex_cos_imaginary_shift_expansion (w : ℂ) (r u y : ℝ) :
    Complex.cos ((w - (r * y : ℝ) * Complex.I) * (u : ℂ)) =
      (Complex.exp (w * (u : ℂ) * Complex.I) *
            Complex.exp (((r * u : ℝ) : ℂ) * y) +
          Complex.exp (-(w * (u : ℂ) * Complex.I)) *
            Complex.exp ((-(r * u : ℝ) : ℂ) * y)) / 2 := by
  let a := r * u
  have hargPos :
      ((w - (r * y : ℝ) * Complex.I) * (u : ℂ)) * Complex.I =
        w * (u : ℂ) * Complex.I + ((a * y : ℝ) : ℂ) := by
    dsimp [a]
    calc
      ((w - (r * y : ℝ) * Complex.I) * (u : ℂ)) * Complex.I =
          w * (u : ℂ) * Complex.I -
            ((r * y * u : ℝ) : ℂ) * (Complex.I * Complex.I) := by
        push_cast
        ring
      _ = _ := by
        rw [Complex.I_mul_I]
        push_cast
        ring
  have hargNeg :
      -((w - (r * y : ℝ) * Complex.I) * (u : ℂ)) * Complex.I =
        -(w * (u : ℂ) * Complex.I) + ((-a * y : ℝ) : ℂ) := by
    dsimp [a]
    calc
      -((w - (r * y : ℝ) * Complex.I) * (u : ℂ)) * Complex.I =
          -(w * (u : ℂ) * Complex.I) +
            ((r * y * u : ℝ) : ℂ) * (Complex.I * Complex.I) := by
        push_cast
        ring
      _ = _ := by
        rw [Complex.I_mul_I]
        push_cast
        ring
  rw [Complex.cos, hargPos, hargNeg, Complex.exp_add, Complex.exp_add]
  dsimp [a]
  push_cast
  rfl

/-- The imaginary-shifted complex cosine is integrable under the centered variance-two
Gaussian. -/
theorem integrable_complex_cos_imaginary_gaussian_shift (w : ℂ) (r u : ℝ) :
    MeasureTheory.Integrable
      (fun y : ℝ ↦ Complex.cos
        ((w - (r * y : ℝ) * Complex.I) * (u : ℂ)))
      (ProbabilityTheory.gaussianReal 0 2) := by
  let a := r * u
  have hpos := integrable_cexp_mul_gaussianReal_zero_two (a : ℂ)
  have hneg := integrable_cexp_mul_gaussianReal_zero_two (-a : ℂ)
  have hsum := (hpos.const_mul (Complex.exp (w * (u : ℂ) * Complex.I))).add
    (hneg.const_mul (Complex.exp (-(w * (u : ℂ) * Complex.I))))
  apply hsum.div_const 2 |>.congr
  apply MeasureTheory.ae_of_all
  intro y
  exact (complex_cos_imaginary_shift_expansion w r u y).symm

/-- Averaging a complex cosine after an imaginary Gaussian translation changes the Fourier
multiplier from `1` to `exp ((r*u)^2)`. -/
theorem integral_complex_cos_imaginary_gaussian_shift (w : ℂ) (r u : ℝ) :
    ∫ y : ℝ, Complex.cos
        ((w - (r * y : ℝ) * Complex.I) * (u : ℂ))
        ∂ProbabilityTheory.gaussianReal 0 2 =
      (Real.exp ((r * u) ^ 2) : ℂ) * Complex.cos (w * (u : ℂ)) := by
  let μ := ProbabilityTheory.gaussianReal 0 2
  let a := r * u
  have hpos := integrable_cexp_mul_gaussianReal_zero_two (a : ℂ)
  have hneg := integrable_cexp_mul_gaussianReal_zero_two (-a : ℂ)
  rw [MeasureTheory.integral_congr_ae
    (MeasureTheory.ae_of_all μ (complex_cos_imaginary_shift_expansion w r u))]
  rw [MeasureTheory.integral_div, MeasureTheory.integral_add
    (hpos.const_mul _) (hneg.const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    integral_cexp_mul_gaussianReal_zero_two,
    integral_cexp_mul_gaussianReal_zero_two]
  have hsq : (-a : ℂ) ^ 2 = (a : ℂ) ^ 2 := by ring
  rw [hsq]
  have hexp : Complex.exp ((a : ℂ) ^ 2) = (Real.exp (a ^ 2) : ℂ) := by
    push_cast
    rfl
  rw [hexp, Complex.cos]
  dsimp [a]
  ring_nf

/-- The defining kernel of `H_t` after an imaginary Gaussian translation is integrable on the
full product space. This is the Fubini gate missing from the real-translation semigroup theorem. -/
theorem integrable_deBruijnNewmanH_imaginary_gaussian_shift_kernel
    (t r : ℝ) (w : ℂ) :
    MeasureTheory.Integrable
      (fun p : ℝ × ℝ ↦
        (((Real.exp (t * p.2 ^ 2) * deBruijnNewmanPhi p.2 : ℝ) : ℂ) *
          Complex.cos
            ((w - (r * p.1 : ℝ) * Complex.I) * (p.2 : ℂ))))
      ((ProbabilityTheory.gaussianReal 0 2).prod
        (MeasureTheory.volume.restrict (Set.Ioi 0))) := by
  let μ := ProbabilityTheory.gaussianReal 0 2
  let ν : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Ioi 0)
  let F : ℝ × ℝ → ℂ := fun p ↦
    (((Real.exp (t * p.2 ^ 2) * deBruijnNewmanPhi p.2 : ℝ) : ℂ) *
      Complex.cos ((w - (r * p.1 : ℝ) * Complex.I) * (p.2 : ℂ)))
  have hscalar : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦ Real.exp (t * p.2 ^ 2) * deBruijnNewmanPhi p.2)
      (μ.prod ν) := by
    have hexp : MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ ↦ Real.exp (t * p.2 ^ 2)) (μ.prod ν) :=
      (by fun_prop : Continuous (fun p : ℝ × ℝ ↦
        Real.exp (t * p.2 ^ 2))).aestronglyMeasurable
    have hphi := (aestronglyMeasurable_deBruijnNewmanPhi ν).comp_snd (μ := μ)
    exact hexp.mul hphi
  have hcos : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦ Complex.cos
        ((w - (r * p.1 : ℝ) * Complex.I) * (p.2 : ℂ))) (μ.prod ν) :=
    (by fun_prop : Continuous (fun p : ℝ × ℝ ↦ Complex.cos
      ((w - (r * p.1 : ℝ) * Complex.I) * (p.2 : ℂ)))).aestronglyMeasurable
  have hmeas : MeasureTheory.AEStronglyMeasurable F (μ.prod ν) :=
    (Complex.continuous_ofReal.comp_aestronglyMeasurable hscalar).mul hcos
  change MeasureTheory.Integrable F (μ.prod ν)
  apply (MeasureTheory.integrable_prod_iff' hmeas).2
  constructor
  · apply MeasureTheory.ae_of_all ν
    intro u
    exact (integrable_complex_cos_imaginary_gaussian_shift w r u).const_mul
      (((Real.exp (t * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ))
  · let M : ℝ → ℝ := fun u ↦
      2 * ((1 + u ^ 2) *
        Real.exp ((|t| + r ^ 2) * u ^ 2 + |w.im| * u) *
          ‖deBruijnNewmanPhi u‖)
    have hM : MeasureTheory.Integrable M ν := by
      exact (integrableOn_one_add_sq_mul_exp_mul_norm_deBruijnNewmanPhi
        (|t| + r ^ 2) (by positivity) |w.im|).const_mul 2
    apply MeasureTheory.Integrable.mono' hM
    · simpa only [Function.comp_apply, Prod.swap_prod_mk] using
        hmeas.norm.prod_swap.integral_prod_right'
    · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
      apply MeasureTheory.ae_of_all
      intro u hu
      have hu0 : 0 ≤ u := hu.le
      let a : ℝ := |r| * u
      let C : ℝ := Real.exp (t * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
        Real.exp (|w.im| * u)
      have hC0 : 0 ≤ C := by
        dsimp [C]
        positivity
      have hsection : MeasureTheory.Integrable
          (fun y : ℝ ↦ ‖F (y, u)‖) μ :=
        ((integrable_complex_cos_imaginary_gaussian_shift w r u).const_mul
          (((Real.exp (t * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ))).norm
      have hmajorY : MeasureTheory.Integrable
          (fun y : ℝ ↦ C * Real.exp (a * |y|)) μ :=
        (integrable_rexp_mul_abs_gaussianReal_zero_two a).const_mul C
      have hpoint (y : ℝ) : ‖F (y, u)‖ ≤ C * Real.exp (a * |y|) := by
        have him :
            (((w - (r * y : ℝ) * Complex.I) * (u : ℂ))).im =
              (w.im - r * y) * u := by
          simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im,
            Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
            Complex.ofReal_im]
          ring
        have habs :
            |(((w - (r * y : ℝ) * Complex.I) * (u : ℂ))).im| ≤
              |w.im| * u + a * |y| := by
          rw [him, abs_mul, abs_of_nonneg hu0]
          calc
            |w.im - r * y| * u ≤ (|w.im| + |r * y|) * u := by
              gcongr
              exact abs_sub _ _
            _ = |w.im| * u + a * |y| := by
              rw [abs_mul]
              dsimp [a]
              ring
        have hcosBound :
            ‖Complex.cos
                ((w - (r * y : ℝ) * Complex.I) * (u : ℂ))‖ ≤
              Real.exp (|w.im| * u) * Real.exp (a * |y|) := by
          calc
            ‖Complex.cos
                ((w - (r * y : ℝ) * Complex.I) * (u : ℂ))‖ ≤
                Real.exp |(((w - (r * y : ℝ) * Complex.I) * (u : ℂ))).im| :=
              norm_complex_cos_le_exp_abs_im _
            _ ≤ Real.exp (|w.im| * u + a * |y|) :=
              Real.exp_le_exp.mpr habs
            _ = Real.exp (|w.im| * u) * Real.exp (a * |y|) := by
              rw [Real.exp_add]
        have hscalarNorm :
            ‖(((Real.exp (t * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ))‖ =
              Real.exp (t * u ^ 2) * ‖deBruijnNewmanPhi u‖ := by
          rw [norm_real, Real.norm_eq_abs, abs_mul,
            abs_of_pos (Real.exp_pos _), ← Real.norm_eq_abs]
        dsimp only [F]
        rw [norm_mul, hscalarNorm]
        dsimp [C]
        calc
          Real.exp (t * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
                ‖Complex.cos
                  ((w - (r * y : ℝ) * Complex.I) * (u : ℂ))‖ ≤
              Real.exp (t * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
                (Real.exp (|w.im| * u) * Real.exp (a * |y|)) := by
            gcongr
          _ = Real.exp (t * u ^ 2) * ‖deBruijnNewmanPhi u‖ *
              Real.exp (|w.im| * u) * Real.exp (a * |y|) := by ring
      rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg fun _ ↦ norm_nonneg _)]
      calc
        (∫ y : ℝ, ‖F (y, u)‖ ∂μ) ≤
            ∫ y : ℝ, C * Real.exp (a * |y|) ∂μ :=
          MeasureTheory.integral_mono_ae hsection hmajorY
            (MeasureTheory.ae_of_all μ hpoint)
        _ = C * ∫ y : ℝ, Real.exp (a * |y|) ∂μ := by
          rw [MeasureTheory.integral_const_mul]
        _ ≤ C * (2 * Real.exp (a ^ 2)) := by
          gcongr
          exact integral_rexp_mul_abs_gaussianReal_zero_two_le a
        _ ≤ M u := by
          have htExp : Real.exp (t * u ^ 2) ≤ Real.exp (|t| * u ^ 2) := by
            apply Real.exp_le_exp.mpr
            gcongr
            exact le_abs_self t
          have haSq : a ^ 2 = r ^ 2 * u ^ 2 := by
            dsimp [a]
            rw [mul_pow, sq_abs]
          have hexp :
              Real.exp (|t| * u ^ 2) * Real.exp (a ^ 2) *
                  Real.exp (|w.im| * u) =
                Real.exp ((|t| + r ^ 2) * u ^ 2 + |w.im| * u) := by
            rw [← Real.exp_add, ← Real.exp_add, haSq]
            congr 1
            ring
          calc
            C * (2 * Real.exp (a ^ 2)) =
                2 * (Real.exp (t * u ^ 2) * Real.exp (a ^ 2) *
                  Real.exp (|w.im| * u) * ‖deBruijnNewmanPhi u‖) := by
              dsimp [C]
              ring
            _ ≤
                2 * (Real.exp (|t| * u ^ 2) * Real.exp (a ^ 2) *
                  Real.exp (|w.im| * u) * ‖deBruijnNewmanPhi u‖) := by
              gcongr
            _ = 2 * (Real.exp
                  ((|t| + r ^ 2) * u ^ 2 + |w.im| * u) *
                    ‖deBruijnNewmanPhi u‖) := by
              rw [hexp]
            _ ≤ M u := by
              have hscale :
                  Real.exp ((|t| + r ^ 2) * u ^ 2 + |w.im| * u) *
                      ‖deBruijnNewmanPhi u‖ ≤
                    (1 + u ^ 2) *
                      (Real.exp ((|t| + r ^ 2) * u ^ 2 + |w.im| * u) *
                        ‖deBruijnNewmanPhi u‖) := by
                exact le_mul_of_one_le_left
                  (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
                  (by nlinarith [sq_nonneg u])
              calc
                2 * (Real.exp
                      ((|t| + r ^ 2) * u ^ 2 + |w.im| * u) *
                        ‖deBruijnNewmanPhi u‖) ≤
                    2 * ((1 + u ^ 2) *
                      (Real.exp
                        ((|t| + r ^ 2) * u ^ 2 + |w.im| * u) *
                          ‖deBruijnNewmanPhi u‖)) := by
                  gcongr
                _ = M u := by
                  dsimp [M]
                  ring

/-- Averaging `H_t` over a centered imaginary Gaussian translation of size `r` advances the heat
parameter by `r²`. -/
theorem integral_deBruijnNewmanH_imaginary_gaussian_shift
    (t r : ℝ) (w : ℂ) :
    ∫ y : ℝ, deBruijnNewmanH t
        (w - (r * y : ℝ) * Complex.I)
        ∂ProbabilityTheory.gaussianReal 0 2 =
      deBruijnNewmanH (t + r ^ 2) w := by
  have hswap :
      (∫ y : ℝ, (∫ u : ℝ in Set.Ioi 0,
          (((Real.exp (t * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ) *
            Complex.cos
              ((w - (r * y : ℝ) * Complex.I) * (u : ℂ))))
          ∂ProbabilityTheory.gaussianReal 0 2) =
        ∫ u : ℝ in Set.Ioi 0, (∫ y : ℝ,
          (((Real.exp (t * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ) *
            Complex.cos
              ((w - (r * y : ℝ) * Complex.I) * (u : ℂ)))
          ∂ProbabilityTheory.gaussianReal 0 2) :=
    MeasureTheory.integral_integral_swap
      (integrable_deBruijnNewmanH_imaginary_gaussian_shift_kernel t r w)
  simp_rw [deBruijnNewmanH]
  rw [hswap]
  apply MeasureTheory.integral_congr_ae
  apply MeasureTheory.ae_of_all
  intro u
  simp only
  rw [MeasureTheory.integral_const_mul,
    integral_complex_cos_imaginary_gaussian_shift]
  have hexp :
      Real.exp (t * u ^ 2) * Real.exp ((r * u) ^ 2) =
        Real.exp ((t + r ^ 2) * u ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    ((Real.exp (t * u ^ 2) * deBruijnNewmanPhi u : ℝ) : ℂ) *
          ((Real.exp ((r * u) ^ 2) : ℂ) *
            Complex.cos (w * (u : ℂ))) =
        (((Real.exp (t * u ^ 2) * Real.exp ((r * u) ^ 2)) *
          deBruijnNewmanPhi u : ℝ) : ℂ) *
            Complex.cos (w * (u : ℂ)) := by
      push_cast
      ring
    _ = (((Real.exp ((t + r ^ 2) * u ^ 2) *
          deBruijnNewmanPhi u : ℝ) : ℂ) *
            Complex.cos (w * (u : ℂ))) := by
      rw [hexp]

/-- Positive heat time is reconstructed exactly from `H_0` by the Polymath imaginary Gaussian
shift. -/
theorem deBruijnNewmanH_eq_gaussian_zero_imaginary_shift
    {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    deBruijnNewmanH t z =
      ∫ y : ℝ, deBruijnNewmanH 0
        (z - (Real.sqrt t * y : ℝ) * Complex.I)
        ∂ProbabilityTheory.gaussianReal 0 2 := by
  symm
  calc
    (∫ y : ℝ, deBruijnNewmanH 0
        (z - (Real.sqrt t * y : ℝ) * Complex.I)
        ∂ProbabilityTheory.gaussianReal 0 2) =
      deBruijnNewmanH (0 + (Real.sqrt t) ^ 2) z :=
        integral_deBruijnNewmanH_imaginary_gaussian_shift 0 (Real.sqrt t) z
    _ = deBruijnNewmanH t z := by rw [Real.sq_sqrt ht, zero_add]

/-- Equation `(htz)` in the project's variance-two Gaussian normalization. The paper's variable
has density `exp (-v²)/sqrt(pi)`; this statement uses `Y=2v`. -/
theorem deBruijnNewmanH_eq_gaussian_riemannXi
    {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    deBruijnNewmanH t z =
      ∫ y : ℝ, (1 / 8 : ℂ) * riemannXi
        ((1 + Complex.I * z) / 2 +
          ((Real.sqrt t / 2 * y : ℝ) : ℂ))
        ∂ProbabilityTheory.gaussianReal 0 2 := by
  rw [deBruijnNewmanH_eq_gaussian_zero_imaginary_shift ht]
  apply MeasureTheory.integral_congr_ae
  apply MeasureTheory.ae_of_all
  intro y
  simp only
  rw [deBruijnNewmanH_zero_eq_riemannXi]
  congr 2
  calc
    (1 + Complex.I *
          (z - (Real.sqrt t * y : ℝ) * Complex.I)) / 2 =
        (1 + Complex.I * z -
          ((Real.sqrt t * y : ℝ) : ℂ) * (Complex.I * Complex.I)) / 2 := by
      push_cast
      ring
    _ =
        (1 + Complex.I * z) / 2 +
          ((Real.sqrt t / 2 * y : ℝ) : ℂ) := by
      rw [Complex.I_mul_I]
      push_cast
      ring

end

end LeanLab.Riemann
