import LeanLab.Riemann.WeilGroundStatePrimeBlock
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The finite Guinand--Weil Volterra source calculus

This module formalizes the finite single-frequency source calculation behind the
Guinand--Weil dictionary. It constructs the literal centered trigonometric polynomial and
Volterra kernel, identifies the corresponding divided-difference quadratic form, and instantiates
the actual finite von Mangoldt source. It does not prove the full zero-sum dictionary.
-/

open Matrix MeasureTheory
open scoped BigOperators Matrix

namespace LeanLab.Riemann

noncomputable section

/-- The complex exponential at one centered finite frequency. -/
def weilFiniteTrigMonomial (N : ℕ) (i : Fin (2 * N + 1)) (t : ℝ) : ℂ :=
  Complex.exp
    (((2 * Real.pi * (weilFiniteCenteredFrequency N i : ℝ) * t : ℝ) : ℂ) * Complex.I)

/-- The source trigonometric polynomial `T_u`. -/
def weilFiniteTrigPolynomial (N : ℕ) (u : Fin (2 * N + 1) → ℝ) (t : ℝ) : ℂ :=
  ∑ i, (u i : ℂ) * weilFiniteTrigMonomial N i t

/-- The literal interval-integral Volterra sine-chord kernel `K_u`. -/
def weilFiniteVolterraKernel (N : ℕ) (u : Fin (2 * N + 1) → ℝ) (ω : ℝ) : ℂ :=
  2 * ∫ t : ℝ in (0 : ℝ)..ω,
    weilFiniteTrigPolynomial N u t * weilFiniteTrigPolynomial N u (ω - t)

/-- One pair contribution to the Volterra kernel. -/
def weilFiniteVolterraPair (N : ℕ) (i j : Fin (2 * N + 1)) (ω : ℝ) : ℂ :=
  2 * ∫ t : ℝ in (0 : ℝ)..ω,
    weilFiniteTrigMonomial N i t * weilFiniteTrigMonomial N j (ω - t)

@[simp]
theorem weilFiniteTrigMonomial_re (N : ℕ) (i : Fin (2 * N + 1)) (t : ℝ) :
    (weilFiniteTrigMonomial N i t).re =
      Real.cos (2 * Real.pi * (weilFiniteCenteredFrequency N i : ℝ) * t) := by
  simpa only [weilFiniteTrigMonomial] using
    Complex.exp_ofReal_mul_I_re
      (2 * Real.pi * (weilFiniteCenteredFrequency N i : ℝ) * t)

@[simp]
theorem weilFiniteTrigMonomial_im (N : ℕ) (i : Fin (2 * N + 1)) (t : ℝ) :
    (weilFiniteTrigMonomial N i t).im =
      Real.sin (2 * Real.pi * (weilFiniteCenteredFrequency N i : ℝ) * t) := by
  simpa only [weilFiniteTrigMonomial] using
    Complex.exp_ofReal_mul_I_im
      (2 * Real.pi * (weilFiniteCenteredFrequency N i : ℝ) * t)

theorem weilFiniteTrigMonomial_rev (N : ℕ)
    (i : Fin (2 * N + 1)) (t : ℝ) :
    weilFiniteTrigMonomial N i.rev t =
      starRingEnd ℂ (weilFiniteTrigMonomial N i t) := by
  apply Complex.ext
  · simp only [weilFiniteTrigMonomial_re, Complex.conj_re]
    rw [weilFiniteCenteredFrequency_rev]
    push_cast
    rw [show 2 * Real.pi * -(weilFiniteCenteredFrequency N i : ℝ) * t =
      -(2 * Real.pi * (weilFiniteCenteredFrequency N i : ℝ) * t) by ring,
      Real.cos_neg]
  · simp only [weilFiniteTrigMonomial_im, Complex.conj_im]
    rw [weilFiniteCenteredFrequency_rev]
    push_cast
    rw [show 2 * Real.pi * -(weilFiniteCenteredFrequency N i : ℝ) * t =
      -(2 * Real.pi * (weilFiniteCenteredFrequency N i : ℝ) * t) by ring,
      Real.sin_neg]

theorem weilFiniteTrigPolynomial_im_eq_zero {N : ℕ}
    {u : Fin (2 * N + 1) → ℝ} (hu : WeilFiniteIsEven u) (t : ℝ) :
    (weilFiniteTrigPolynomial N u t).im = 0 := by
  rw [weilFiniteTrigPolynomial, Complex.im_sum]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    add_zero, weilFiniteTrigMonomial_im]
  rw [weilFiniteIsEven_iff] at hu
  let f : Fin (2 * N + 1) → ℝ := fun i =>
    u i * Real.sin (2 * Real.pi * (weilFiniteCenteredFrequency N i : ℝ) * t)
  have hsum :=
    Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (2 * N + 1))) f
  have hneg :
      (∑ i : Fin (2 * N + 1), f i.rev) = -(∑ i, f i) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [f]
    rw [hu i, weilFiniteCenteredFrequency_rev]
    push_cast
    rw [show 2 * Real.pi * -(weilFiniteCenteredFrequency N i : ℝ) * t =
      -(2 * Real.pi * (weilFiniteCenteredFrequency N i : ℝ) * t) by ring,
      Real.sin_neg]
    ring
  change ∑ i, f i = 0
  have hself : (∑ i, f i) = -(∑ i, f i) := by
    calc
      (∑ i, f i) = ∑ i : Fin (2 * N + 1), f i.rev := by simpa using hsum.symm
      _ = -(∑ i, f i) := hneg
  linarith

theorem weilFiniteTrigPolynomial_eq_ofReal_re {N : ℕ}
    {u : Fin (2 * N + 1) → ℝ} (hu : WeilFiniteIsEven u) (t : ℝ) :
    weilFiniteTrigPolynomial N u t =
      ((weilFiniteTrigPolynomial N u t).re : ℂ) := by
  apply Complex.ext
  · simp
  · simp [weilFiniteTrigPolynomial_im_eq_zero hu]

theorem weilFiniteTrigMonomial_mul_sub (N : ℕ)
    (i j : Fin (2 * N + 1)) (ω t : ℝ) :
    weilFiniteTrigMonomial N i t * weilFiniteTrigMonomial N j (ω - t) =
      weilFiniteTrigMonomial N j ω *
        Complex.exp
          (((2 * Real.pi *
            ((weilFiniteCenteredFrequency N i : ℝ) -
              (weilFiniteCenteredFrequency N j : ℝ)) * t : ℝ) : ℂ) * Complex.I) := by
  rw [weilFiniteTrigMonomial, weilFiniteTrigMonomial, weilFiniteTrigMonomial,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem weilFiniteVolterraPair_same (N : ℕ) (i : Fin (2 * N + 1)) (ω : ℝ) :
    weilFiniteVolterraPair N i i ω =
      2 * ω * weilFiniteTrigMonomial N i ω := by
  rw [weilFiniteVolterraPair]
  have hconst : ∀ t : ℝ,
      weilFiniteTrigMonomial N i t * weilFiniteTrigMonomial N i (ω - t) =
        weilFiniteTrigMonomial N i ω := by
    intro t
    rw [weilFiniteTrigMonomial_mul_sub]
    simp
  simp_rw [hconst]
  simp
  ring

theorem weilFiniteVolterraPair_ne {N : ℕ} {i j : Fin (2 * N + 1)}
    (hij : i ≠ j) (ω : ℝ) :
    weilFiniteVolterraPair N i j ω =
      (weilFiniteTrigMonomial N i ω - weilFiniteTrigMonomial N j ω) /
        (((Real.pi *
          ((weilFiniteCenteredFrequency N i : ℝ) -
            (weilFiniteCenteredFrequency N j : ℝ)) : ℝ) : ℂ) * Complex.I) := by
  have hfreqInt := weilFiniteCenteredFrequency_sub_ne_zero hij
  have hfreq :
      (weilFiniteCenteredFrequency N i : ℝ) -
        (weilFiniteCenteredFrequency N j : ℝ) ≠ 0 := by
    exact_mod_cast hfreqInt
  let c : ℂ :=
    ((2 * Real.pi *
      ((weilFiniteCenteredFrequency N i : ℝ) -
        (weilFiniteCenteredFrequency N j : ℝ)) : ℝ) : ℂ) * Complex.I
  let d : ℂ :=
    ((Real.pi *
      ((weilFiniteCenteredFrequency N i : ℝ) -
        (weilFiniteCenteredFrequency N j : ℝ)) : ℝ) : ℂ) * Complex.I
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero
      (Complex.ofReal_ne_zero.mpr
        (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hfreq))
      Complex.I_ne_zero
  have hd : d ≠ 0 := by
    dsimp [d]
    exact mul_ne_zero
      (Complex.ofReal_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero hfreq))
      Complex.I_ne_zero
  have hcd : c = 2 * d := by
    dsimp [c, d]
    push_cast
    ring
  rw [weilFiniteVolterraPair]
  simp_rw [weilFiniteTrigMonomial_mul_sub]
  rw [intervalIntegral.integral_const_mul]
  have hinter :
      (∫ t : ℝ in (0 : ℝ)..ω,
        Complex.exp
          (((2 * Real.pi *
            ((weilFiniteCenteredFrequency N i : ℝ) -
              (weilFiniteCenteredFrequency N j : ℝ)) * t : ℝ) : ℂ) * Complex.I)) =
        ∫ t : ℝ in (0 : ℝ)..ω, Complex.exp (c * t) := by
    apply intervalIntegral.integral_congr
    intro t _
    apply congrArg Complex.exp
    dsimp [c]
    push_cast
    ring
  rw [hinter]
  rw [integral_exp_mul_complex hc]
  have hexp :
      weilFiniteTrigMonomial N j ω * Complex.exp (c * (ω : ℂ)) =
        weilFiniteTrigMonomial N i ω := by
    dsimp [c]
    rw [weilFiniteTrigMonomial, weilFiniteTrigMonomial, ← Complex.exp_add]
    push_cast
    ring
  rw [show ((0 : ℝ) : ℂ) = 0 by norm_num, mul_zero, Complex.exp_zero]
  rw [show
    weilFiniteTrigMonomial N j ω *
        ((Complex.exp (c * (ω : ℂ)) - 1) / c) =
      (weilFiniteTrigMonomial N j ω * Complex.exp (c * (ω : ℂ)) -
        weilFiniteTrigMonomial N j ω) / c by ring,
    hexp]
  change
    2 * ((weilFiniteTrigMonomial N i ω - weilFiniteTrigMonomial N j ω) / c) =
      (weilFiniteTrigMonomial N i ω - weilFiniteTrigMonomial N j ω) / d
  rw [hcd]
  field_simp [hd]

theorem complex_re_div_ofReal_mul_I (z : ℂ) {d : ℝ} (hd : d ≠ 0) :
    (z / ((d : ℂ) * Complex.I)).re = z.im / d := by
  rw [Complex.div_re]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one, zero_add,
    Complex.normSq_apply]
  field_simp [hd]
  ring

theorem weilFiniteVolterraPair_re_same (N : ℕ)
    (i : Fin (2 * N + 1)) (ω : ℝ) :
    (weilFiniteVolterraPair N i i ω).re =
      2 * ω *
        Real.cos (2 * Real.pi * ω * (weilFiniteCenteredFrequency N i : ℝ)) := by
  rw [weilFiniteVolterraPair_same]
  rw [show (2 : ℂ) * (ω : ℂ) = ((2 * ω : ℝ) : ℂ) by norm_num]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, weilFiniteTrigMonomial_re]
  congr 1
  ring

theorem weilFiniteVolterraPair_re_ne {N : ℕ} {i j : Fin (2 * N + 1)}
    (hij : i ≠ j) (ω : ℝ) :
    (weilFiniteVolterraPair N i j ω).re =
      (Real.sin (2 * Real.pi * ω * (weilFiniteCenteredFrequency N i : ℝ)) -
        Real.sin (2 * Real.pi * ω * (weilFiniteCenteredFrequency N j : ℝ))) /
        (Real.pi *
          ((weilFiniteCenteredFrequency N i : ℝ) -
            (weilFiniteCenteredFrequency N j : ℝ))) := by
  rw [weilFiniteVolterraPair_ne hij]
  have hfreqInt := weilFiniteCenteredFrequency_sub_ne_zero hij
  have hfreq :
      (weilFiniteCenteredFrequency N i : ℝ) -
        (weilFiniteCenteredFrequency N j : ℝ) ≠ 0 := by
    exact_mod_cast hfreqInt
  rw [complex_re_div_ofReal_mul_I
    (weilFiniteTrigMonomial N i ω - weilFiniteTrigMonomial N j ω) (d :=
    Real.pi *
      ((weilFiniteCenteredFrequency N i : ℝ) -
        (weilFiniteCenteredFrequency N j : ℝ)))
    (mul_ne_zero Real.pi_ne_zero hfreq)]
  simp only [Complex.sub_im, weilFiniteTrigMonomial_im]
  ring_nf

/-- The generic sine source `alpha/pi * sin(2*pi*omega*x)`. -/
def weilFiniteSineAtomSource (α ω x : ℝ) : ℝ :=
  α / Real.pi * Real.sin (2 * Real.pi * ω * x)

/-- The derivative of the generic sine source. -/
def weilFiniteSineAtomSourceDerivative (α ω x : ℝ) : ℝ :=
  2 * α * ω * Real.cos (2 * Real.pi * ω * x)

theorem hasDerivAt_weilFiniteSineAtomSource (α ω x : ℝ) :
    HasDerivAt (weilFiniteSineAtomSource α ω)
      (weilFiniteSineAtomSourceDerivative α ω x) x := by
  change HasDerivAt
    (fun y : ℝ => α / Real.pi * Real.sin (2 * Real.pi * ω * y))
    (2 * α * ω * Real.cos (2 * Real.pi * ω * x)) x
  let k : ℝ := 2 * Real.pi * ω
  have hinner : HasDerivAt (fun y : ℝ => k * y) k x :=
    by simpa using (hasDerivAt_id x).const_mul k
  have hsin : HasDerivAt (fun y : ℝ => Real.sin (k * y))
      (Real.cos (k * x) * k) x :=
    (Real.hasDerivAt_sin (k * x)).comp x hinner
  have hscaled := hsin.const_mul (α / Real.pi)
  have hder :
      α / Real.pi * (Real.cos (k * x) * k) =
        2 * α * ω * Real.cos (2 * Real.pi * ω * x) := by
    dsimp [k]
    field_simp [Real.pi_ne_zero]
  simpa only [k] using hscaled.congr_deriv hder

/-- Value samples of the generic sine source. -/
def weilFiniteSineAtomValue (N : ℕ) (α ω : ℝ)
    (i : Fin (2 * N + 1)) : ℝ :=
  weilFiniteSineAtomSource α ω (weilFiniteCenteredFrequency N i)

/-- Derivative samples of the generic sine source. -/
def weilFiniteSineAtomDerivative (N : ℕ) (α ω : ℝ)
    (i : Fin (2 * N + 1)) : ℝ :=
  weilFiniteSineAtomSourceDerivative α ω (weilFiniteCenteredFrequency N i)

/-- The finite divided-difference matrix of the generic sine source. -/
def weilFiniteSineAtomMatrix (N : ℕ) (α ω : ℝ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ :=
  weilFiniteDividedDifferenceMatrix N
    (weilFiniteSineAtomDerivative N α ω) (weilFiniteSineAtomValue N α ω)

theorem weilFiniteSineAtomMatrix_apply_same (N : ℕ) (α ω : ℝ)
    (i : Fin (2 * N + 1)) :
    weilFiniteSineAtomMatrix N α ω i i =
      2 * α * ω *
        Real.cos (2 * Real.pi * ω * (weilFiniteCenteredFrequency N i : ℝ)) := by
  simp [weilFiniteSineAtomMatrix, weilFiniteDividedDifferenceMatrix,
    weilFiniteSineAtomDerivative, weilFiniteSineAtomSourceDerivative]

theorem weilFiniteSineAtomMatrix_apply_ne {N : ℕ} {i j : Fin (2 * N + 1)}
    (hij : i ≠ j) (α ω : ℝ) :
    weilFiniteSineAtomMatrix N α ω i j =
      α *
        (Real.sin (2 * Real.pi * ω * (weilFiniteCenteredFrequency N i : ℝ)) -
          Real.sin (2 * Real.pi * ω * (weilFiniteCenteredFrequency N j : ℝ))) /
          (Real.pi *
            ((weilFiniteCenteredFrequency N i : ℝ) -
              (weilFiniteCenteredFrequency N j : ℝ))) := by
  simp only [weilFiniteSineAtomMatrix, weilFiniteDividedDifferenceMatrix, hij, if_false,
    weilFiniteSineAtomValue, weilFiniteSineAtomSource]
  push_cast
  have hfreqInt := weilFiniteCenteredFrequency_sub_ne_zero hij
  have hfreq :
      (weilFiniteCenteredFrequency N i : ℝ) -
        (weilFiniteCenteredFrequency N j : ℝ) ≠ 0 := by
    exact_mod_cast hfreqInt
  field_simp [Real.pi_ne_zero, hfreq]

/-- The real pair matrix supplied by the actual Volterra integral. -/
def weilFiniteVolterraPairMatrix (N : ℕ) (ω : ℝ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ :=
  fun i j => (weilFiniteVolterraPair N i j ω).re

theorem weilFiniteTrigPolynomial_mul (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) (ω t : ℝ) :
    weilFiniteTrigPolynomial N u t * weilFiniteTrigPolynomial N u (ω - t) =
      ∑ i, ∑ j,
        (((u i * u j : ℝ) : ℂ) *
          (weilFiniteTrigMonomial N i t * weilFiniteTrigMonomial N j (ω - t))) := by
  rw [weilFiniteTrigPolynomial, weilFiniteTrigPolynomial, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  ring

theorem intervalIntegrable_weilFiniteVolterraPairIntegrand
    (N : ℕ) (i j : Fin (2 * N + 1)) (ω : ℝ) :
    IntervalIntegrable
      (fun t : ℝ =>
        weilFiniteTrigMonomial N i t * weilFiniteTrigMonomial N j (ω - t))
      volume 0 ω := by
  apply Continuous.intervalIntegrable
  unfold weilFiniteTrigMonomial
  fun_prop

theorem intervalIntegrable_weilFiniteVolterraKernelIntegrand
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) (ω : ℝ) :
    IntervalIntegrable
      (fun t : ℝ =>
        weilFiniteTrigPolynomial N u t * weilFiniteTrigPolynomial N u (ω - t))
      volume 0 ω := by
  apply Continuous.intervalIntegrable
  unfold weilFiniteTrigPolynomial weilFiniteTrigMonomial
  fun_prop

theorem weilFiniteVolterraKernel_im_eq_zero {N : ℕ}
    {u : Fin (2 * N + 1) → ℝ} (hu : WeilFiniteIsEven u) (ω : ℝ) :
    (weilFiniteVolterraKernel N u ω).im = 0 := by
  have hint := intervalIntegrable_weilFiniteVolterraKernelIntegrand N u ω
  rw [weilFiniteVolterraKernel]
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  have him :
      (∫ t : ℝ in (0 : ℝ)..ω,
          (weilFiniteTrigPolynomial N u t *
            weilFiniteTrigPolynomial N u (ω - t)).im) =
        (∫ t : ℝ in (0 : ℝ)..ω,
          weilFiniteTrigPolynomial N u t *
            weilFiniteTrigPolynomial N u (ω - t)).im := by
    simpa only [Complex.imCLM_apply] using
      Complex.imCLM.intervalIntegral_comp_comm hint
  rw [← him]
  simp [weilFiniteTrigPolynomial_im_eq_zero hu]

theorem weilFiniteVolterraKernel_eq_ofReal_re {N : ℕ}
    {u : Fin (2 * N + 1) → ℝ} (hu : WeilFiniteIsEven u) (ω : ℝ) :
    weilFiniteVolterraKernel N u ω =
      ((weilFiniteVolterraKernel N u ω).re : ℂ) := by
  apply Complex.ext
  · simp
  · simp [weilFiniteVolterraKernel_im_eq_zero hu]

theorem weilFiniteVolterraKernel_eq_sum_pairs
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) (ω : ℝ) :
    weilFiniteVolterraKernel N u ω =
      ∑ i, ∑ j,
        (((u i * u j : ℝ) : ℂ) * weilFiniteVolterraPair N i j ω) := by
  have hint (i j : Fin (2 * N + 1)) :
      IntervalIntegrable
        (fun t : ℝ =>
          (((u i * u j : ℝ) : ℂ) *
            (weilFiniteTrigMonomial N i t * weilFiniteTrigMonomial N j (ω - t))))
        volume 0 ω :=
    (intervalIntegrable_weilFiniteVolterraPairIntegrand N i j ω).const_mul _
  have hintegral :
      (∫ t : ℝ in (0 : ℝ)..ω,
        ∑ i, ∑ j,
          (((u i * u j : ℝ) : ℂ) *
            (weilFiniteTrigMonomial N i t * weilFiniteTrigMonomial N j (ω - t)))) =
        ∑ i, ∑ j,
          ∫ t : ℝ in (0 : ℝ)..ω,
            (((u i * u j : ℝ) : ℂ) *
              (weilFiniteTrigMonomial N i t *
                weilFiniteTrigMonomial N j (ω - t))) := by
    calc
      _ = ∑ i, ∫ t : ℝ in (0 : ℝ)..ω,
          ∑ j,
            (((u i * u j : ℝ) : ℂ) *
              (weilFiniteTrigMonomial N i t *
                weilFiniteTrigMonomial N j (ω - t))) := by
        rw [intervalIntegral.integral_finsetSum]
        intro i _
        apply Continuous.intervalIntegrable
        unfold weilFiniteTrigMonomial
        fun_prop
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [intervalIntegral.integral_finsetSum]
        intro j _
        exact hint i j
  rw [weilFiniteVolterraKernel]
  simp_rw [weilFiniteTrigPolynomial_mul]
  rw [hintegral]
  simp_rw [intervalIntegral.integral_const_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [weilFiniteVolterraPair]
  ring

theorem weilFiniteVolterraPairMatrix_quadratic
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) (ω : ℝ) :
    u ⬝ᵥ (weilFiniteVolterraPairMatrix N ω *ᵥ u) =
      (weilFiniteVolterraKernel N u ω).re := by
  rw [weilFiniteVolterraKernel_eq_sum_pairs]
  have hre :
      (∑ i, ∑ j,
        (((u i * u j : ℝ) : ℂ) * weilFiniteVolterraPair N i j ω)).re =
        ∑ i, ∑ j,
          (u i * u j) * (weilFiniteVolterraPair N i j ω).re := by
    simp
  rw [hre]
  simp only [dotProduct, mulVec, weilFiniteVolterraPairMatrix]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem weilFiniteSineAtomMatrix_eq_volterraPairMatrix
    (N : ℕ) (α ω : ℝ) :
    weilFiniteSineAtomMatrix N α ω =
      α • weilFiniteVolterraPairMatrix N ω := by
  ext i j
  by_cases hij : i = j
  · subst j
    rw [weilFiniteSineAtomMatrix_apply_same]
    simp [weilFiniteVolterraPairMatrix, weilFiniteVolterraPair_re_same]
    ring
  · rw [weilFiniteSineAtomMatrix_apply_ne hij]
    simp [weilFiniteVolterraPairMatrix, weilFiniteVolterraPair_re_ne hij]
    ring

theorem weilFiniteSineAtomMatrix_quadratic
    (N : ℕ) (α ω : ℝ) (u : Fin (2 * N + 1) → ℝ) :
    u ⬝ᵥ (weilFiniteSineAtomMatrix N α ω *ᵥ u) =
      α * (weilFiniteVolterraKernel N u ω).re := by
  rw [weilFiniteSineAtomMatrix_eq_volterraPairMatrix, Matrix.smul_mulVec,
    dotProduct_smul, weilFiniteVolterraPairMatrix_quadratic]
  rfl

theorem weilFiniteSineAtomMatrix_quadratic_complex
    (N : ℕ) (α ω : ℝ) (u : Fin (2 * N + 1) → ℝ)
    (hu : WeilFiniteIsEven u) :
    ((u ⬝ᵥ (weilFiniteSineAtomMatrix N α ω *ᵥ u) : ℝ) : ℂ) =
      (α : ℂ) * weilFiniteVolterraKernel N u ω := by
  rw [weilFiniteVolterraKernel_eq_ofReal_re hu]
  exact_mod_cast weilFiniteSineAtomMatrix_quadratic N α ω u

theorem weilFiniteMatrixSum_quadratic
    {ι : Type*} {N : ℕ} (s : Finset ι)
    (A : ι → Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ)
    (u : Fin (2 * N + 1) → ℝ) :
    u ⬝ᵥ ((∑ k ∈ s, A k) *ᵥ u) =
      ∑ k ∈ s, u ⬝ᵥ (A k *ᵥ u) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert k s hk ih =>
      simp only [Finset.sum_insert hk, Matrix.add_mulVec, dotProduct_add, ih]

theorem weilFiniteSineAtomSum_quadratic
    {ι : Type*} {N : ℕ} (s : Finset ι) (α ω : ι → ℝ)
    (u : Fin (2 * N + 1) → ℝ) :
    u ⬝ᵥ ((∑ k ∈ s, weilFiniteSineAtomMatrix N (α k) (ω k)) *ᵥ u) =
      ∑ k ∈ s, α k * (weilFiniteVolterraKernel N u (ω k)).re := by
  classical
  rw [weilFiniteMatrixSum_quadratic]
  apply Finset.sum_congr rfl
  intro k _
  exact weilFiniteSineAtomMatrix_quadratic N (α k) (ω k) u

theorem weilFinitePrimeAtomMatrix_eq_sineAtom (C q N : ℕ) :
    weilFinitePrimeAtomMatrix C q N =
      weilFiniteSineAtomMatrix N (weilPrimeAtomCoefficient q) (weilPrimeFrequency C q) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [weilFinitePrimeAtomMatrix, weilFiniteSineAtomMatrix,
      weilFiniteDividedDifferenceMatrix, weilPrimeAtomSourceDerivative,
      weilFiniteSineAtomDerivative, weilFiniteSineAtomSourceDerivative]
  · simp only [weilFinitePrimeAtomMatrix, weilFiniteSineAtomMatrix,
      weilFiniteDividedDifferenceMatrix, hij, if_false, weilPrimeAtomSourceValue,
      weilFiniteSineAtomValue, weilFiniteSineAtomSource]

theorem weilFinitePrimeAtomMatrix_quadratic (C q N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) :
    u ⬝ᵥ (weilFinitePrimeAtomMatrix C q N *ᵥ u) =
      weilPrimeAtomCoefficient q *
        (weilFiniteVolterraKernel N u (weilPrimeFrequency C q)).re := by
  rw [weilFinitePrimeAtomMatrix_eq_sineAtom]
  exact weilFiniteSineAtomMatrix_quadratic N
    (weilPrimeAtomCoefficient q) (weilPrimeFrequency C q) u

theorem weilFinitePrimeSourceMatrix_quadratic_eq_volterra
    (C N : ℕ) (u : Fin (2 * N + 1) → ℝ) :
    u ⬝ᵥ (weilFinitePrimeSourceMatrix C N *ᵥ u) =
      ∑ q ∈ Finset.Icc 2 C,
        weilPrimeAtomCoefficient q *
          (weilFiniteVolterraKernel N u (weilPrimeFrequency C q)).re := by
  rw [weilFinitePrimeSourceMatrix_eq_sum_atoms,
    weilFiniteMatrixSum_quadratic]
  apply Finset.sum_congr rfl
  intro q _
  exact weilFinitePrimeAtomMatrix_quadratic C q N u

/-- The source Fourier half-bandwidth `Delta=log(C)/(2*pi)`. -/
def weilFiniteDictionaryBandwidth (C : ℕ) : ℝ :=
  Real.log C / (2 * Real.pi)

/-- The source band-limited Fourier weight induced by the Volterra kernel. -/
def weilFiniteDictionaryFourierWeight (C N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) (ξ : ℝ) : ℝ :=
  if |ξ| ≤ weilFiniteDictionaryBandwidth C then
    Real.pi * (weilFiniteVolterraKernel N u
      (1 - |ξ| / weilFiniteDictionaryBandwidth C)).re
  else
    0

theorem weilFiniteDictionaryFourierWeight_neg (C N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) (ξ : ℝ) :
    weilFiniteDictionaryFourierWeight C N u (-ξ) =
      weilFiniteDictionaryFourierWeight C N u ξ := by
  simp [weilFiniteDictionaryFourierWeight]

theorem weilFiniteDictionaryFourierWeight_eq_zero_of_bandwidth_lt
    {C N : ℕ} {u : Fin (2 * N + 1) → ℝ} {ξ : ℝ}
    (hξ : weilFiniteDictionaryBandwidth C < |ξ|) :
    weilFiniteDictionaryFourierWeight C N u ξ = 0 := by
  simp [weilFiniteDictionaryFourierWeight, not_le_of_gt hξ]

theorem weilFiniteDictionaryBandwidth_pos {C : ℕ} (hC : 2 ≤ C) :
    0 < weilFiniteDictionaryBandwidth C := by
  exact div_pos (Real.log_pos (by exact_mod_cast hC)) (mul_pos (by norm_num) Real.pi_pos)

theorem weilFiniteDictionary_prime_coordinate {C q N : ℕ}
    (hC : 2 ≤ C) (hq : 2 ≤ q) (hqC : q ≤ C)
    (u : Fin (2 * N + 1) → ℝ) :
    weilFiniteDictionaryFourierWeight C N u (Real.log q / (2 * Real.pi)) =
      Real.pi *
        (weilFiniteVolterraKernel N u (weilPrimeFrequency C q)).re := by
  have hqpos : (0 : ℝ) < q := by positivity
  have hlogq : 0 ≤ Real.log q :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
  have hlog_le : Real.log q ≤ Real.log C :=
    Real.log_le_log hqpos (by exact_mod_cast hqC)
  have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hband : Real.log q / (2 * Real.pi) ≤ weilFiniteDictionaryBandwidth C := by
    exact div_le_div_of_nonneg_right hlog_le hpi.le
  have hcoord :
      1 - |Real.log q / (2 * Real.pi)| / weilFiniteDictionaryBandwidth C =
        weilPrimeFrequency C q := by
    rw [abs_of_nonneg (div_nonneg hlogq hpi.le)]
    rw [weilFiniteDictionaryBandwidth, weilPrimeFrequency]
    have hlogC : Real.log (C : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hC)).ne'
    field_simp [Real.pi_ne_zero, hlogC]
  rw [weilFiniteDictionaryFourierWeight, if_pos]
  · rw [hcoord]
  · rw [abs_of_nonneg (div_nonneg hlogq hpi.le)]
    exact hband

theorem weilFinitePrimeSourceMatrix_quadratic_eq_fourierWeight
    {C N : ℕ} (hC : 2 ≤ C) (u : Fin (2 * N + 1) → ℝ) :
    u ⬝ᵥ (weilFinitePrimeSourceMatrix C N *ᵥ u) =
      ∑ q ∈ Finset.Icc 2 C,
        weilPrimeAtomCoefficient q / Real.pi *
          weilFiniteDictionaryFourierWeight C N u
            (Real.log q / (2 * Real.pi)) := by
  rw [weilFinitePrimeSourceMatrix_quadratic_eq_volterra]
  apply Finset.sum_congr rfl
  intro q hq
  obtain ⟨hq2, hqC⟩ := Finset.mem_Icc.mp hq
  rw [weilFiniteDictionary_prime_coordinate hC hq2 hqC]
  field_simp [Real.pi_ne_zero]

/-- The seven-part finite source-calculus certificate fixed by the campaign preregistration. -/
structure WeilFiniteDictionarySourceCalculusCertificate : Prop where
  trigPolynomial_real :
    ∀ {N : ℕ} {u : Fin (2 * N + 1) → ℝ}, WeilFiniteIsEven u → ∀ t : ℝ,
      weilFiniteTrigPolynomial N u t =
        ((weilFiniteTrigPolynomial N u t).re : ℂ)
  volterraKernel_real :
    ∀ {N : ℕ} {u : Fin (2 * N + 1) → ℝ}, WeilFiniteIsEven u → ∀ ω : ℝ,
      weilFiniteVolterraKernel N u ω =
        ((weilFiniteVolterraKernel N u ω).re : ℂ)
  sineAtom_diagonal :
    ∀ (N : ℕ) (α ω : ℝ) (i : Fin (2 * N + 1)),
      weilFiniteSineAtomMatrix N α ω i i =
        2 * α * ω *
          Real.cos (2 * Real.pi * ω * (weilFiniteCenteredFrequency N i : ℝ))
  sineAtom_offDiagonal :
    ∀ {N : ℕ} {i j : Fin (2 * N + 1)}, i ≠ j → ∀ α ω : ℝ,
      weilFiniteSineAtomMatrix N α ω i j =
        α *
          (Real.sin (2 * Real.pi * ω * (weilFiniteCenteredFrequency N i : ℝ)) -
            Real.sin (2 * Real.pi * ω * (weilFiniteCenteredFrequency N j : ℝ))) /
            (Real.pi *
              ((weilFiniteCenteredFrequency N i : ℝ) -
                (weilFiniteCenteredFrequency N j : ℝ)))
  volterraPair_diagonal :
    ∀ (N : ℕ) (i : Fin (2 * N + 1)) (ω : ℝ),
      weilFiniteVolterraPair N i i ω =
        2 * ω * weilFiniteTrigMonomial N i ω
  volterraPair_offDiagonal :
    ∀ {N : ℕ} {i j : Fin (2 * N + 1)}, i ≠ j → ∀ ω : ℝ,
      weilFiniteVolterraPair N i j ω =
        (weilFiniteTrigMonomial N i ω - weilFiniteTrigMonomial N j ω) /
          (((Real.pi *
            ((weilFiniteCenteredFrequency N i : ℝ) -
              (weilFiniteCenteredFrequency N j : ℝ)) : ℝ) : ℂ) * Complex.I)
  sineAtom_quadratic :
    ∀ (N : ℕ) (α ω : ℝ) (u : Fin (2 * N + 1) → ℝ),
      u ⬝ᵥ (weilFiniteSineAtomMatrix N α ω *ᵥ u) =
        α * (weilFiniteVolterraKernel N u ω).re
  sineAtom_quadratic_real :
    ∀ (N : ℕ) (α ω : ℝ) (u : Fin (2 * N + 1) → ℝ), WeilFiniteIsEven u →
      ((u ⬝ᵥ (weilFiniteSineAtomMatrix N α ω *ᵥ u) : ℝ) : ℂ) =
        (α : ℂ) * weilFiniteVolterraKernel N u ω
  finiteSuperposition :
    ∀ {ι : Type} {N : ℕ} (s : Finset ι) (α ω : ι → ℝ)
        (u : Fin (2 * N + 1) → ℝ),
      u ⬝ᵥ ((∑ k ∈ s, weilFiniteSineAtomMatrix N (α k) (ω k)) *ᵥ u) =
        ∑ k ∈ s, α k * (weilFiniteVolterraKernel N u (ω k)).re
  primeAtom_identification :
    ∀ C q N : ℕ,
      weilFinitePrimeAtomMatrix C q N =
        weilFiniteSineAtomMatrix N
          (weilPrimeAtomCoefficient q) (weilPrimeFrequency C q)
  primeSource_volterra :
    ∀ (C N : ℕ) (u : Fin (2 * N + 1) → ℝ),
      u ⬝ᵥ (weilFinitePrimeSourceMatrix C N *ᵥ u) =
        ∑ q ∈ Finset.Icc 2 C,
          weilPrimeAtomCoefficient q *
            (weilFiniteVolterraKernel N u (weilPrimeFrequency C q)).re
  fourierWeight_even :
    ∀ (C N : ℕ) (u : Fin (2 * N + 1) → ℝ) (ξ : ℝ),
      weilFiniteDictionaryFourierWeight C N u (-ξ) =
        weilFiniteDictionaryFourierWeight C N u ξ
  fourierWeight_outside :
    ∀ {C N : ℕ} {u : Fin (2 * N + 1) → ℝ} {ξ : ℝ},
      weilFiniteDictionaryBandwidth C < |ξ| →
        weilFiniteDictionaryFourierWeight C N u ξ = 0
  primeCoordinate :
    ∀ {C q N : ℕ}, 2 ≤ C → 2 ≤ q → q ≤ C →
      ∀ u : Fin (2 * N + 1) → ℝ,
        weilFiniteDictionaryFourierWeight C N u (Real.log q / (2 * Real.pi)) =
          Real.pi *
            (weilFiniteVolterraKernel N u (weilPrimeFrequency C q)).re
  primeSource_fourierWeight :
    ∀ {C N : ℕ}, 2 ≤ C → ∀ u : Fin (2 * N + 1) → ℝ,
      u ⬝ᵥ (weilFinitePrimeSourceMatrix C N *ᵥ u) =
        ∑ q ∈ Finset.Icc 2 C,
          weilPrimeAtomCoefficient q / Real.pi *
            weilFiniteDictionaryFourierWeight C N u
              (Real.log q / (2 * Real.pi))

/-- The complete finite Volterra-to-prime source endpoint; no zero-side formula is asserted. -/
theorem weilFiniteDictionarySourceCalculus_endpoint :
    WeilFiniteDictionarySourceCalculusCertificate where
  trigPolynomial_real := weilFiniteTrigPolynomial_eq_ofReal_re
  volterraKernel_real := weilFiniteVolterraKernel_eq_ofReal_re
  sineAtom_diagonal := weilFiniteSineAtomMatrix_apply_same
  sineAtom_offDiagonal := weilFiniteSineAtomMatrix_apply_ne
  volterraPair_diagonal := weilFiniteVolterraPair_same
  volterraPair_offDiagonal := weilFiniteVolterraPair_ne
  sineAtom_quadratic := weilFiniteSineAtomMatrix_quadratic
  sineAtom_quadratic_real := weilFiniteSineAtomMatrix_quadratic_complex
  finiteSuperposition := weilFiniteSineAtomSum_quadratic
  primeAtom_identification := weilFinitePrimeAtomMatrix_eq_sineAtom
  primeSource_volterra := weilFinitePrimeSourceMatrix_quadratic_eq_volterra
  fourierWeight_even := weilFiniteDictionaryFourierWeight_neg
  fourierWeight_outside := weilFiniteDictionaryFourierWeight_eq_zero_of_bandwidth_lt
  primeCoordinate := weilFiniteDictionary_prime_coordinate
  primeSource_fourierWeight := weilFinitePrimeSourceMatrix_quadratic_eq_fourierWeight

end

end LeanLab.Riemann
