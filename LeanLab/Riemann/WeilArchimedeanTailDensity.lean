import LeanLab.Riemann.WeilGroundStatePoleBlock
import LeanLab.Riemann.WeilGroundStatePrimeBlock
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The finite Weil archimedean tail density

This module instantiates the literal archimedean interval source used in the finite Weil matrix.
It proves the integer-node and true-source diagonal formulas, the rank-two Cauchy density, and a
conditional positive-semidefinite interval increment. The sign of the digamma density is kept as
an explicit hypothesis.
-/

open Matrix
open scoped BigOperators Matrix Interval

namespace LeanLab.Riemann

noncomputable section

/-- The literal archimedean density `h_+(r)`. -/
def weilArchimedeanDensity (r : ℝ) : ℝ :=
  (Complex.digamma ((1 / 4 : ℂ) + (r / 2 : ℂ) * Complex.I)).re - Real.log Real.pi

/-- The band scale `rho=2*pi/L`. -/
def weilArchimedeanBandScale (L : ℝ) : ℝ :=
  2 * Real.pi / L

/-- The literal finite-interval kernel `S(r,x,L)`. -/
def weilArchimedeanKernel (L r x : ℝ) : ℝ :=
  ∫ y in 0..L,
    Real.sin (2 * Real.pi * x * (1 - y / L)) * Real.cos (r * y)

/-- The pointwise derivative of the literal kernel integrand with respect to `x`. -/
def weilArchimedeanKernelDerivativeIntegrand (L r x y : ℝ) : ℝ :=
  2 * Real.pi * (1 - y / L) *
    Real.cos (2 * Real.pi * x * (1 - y / L)) * Real.cos (r * y)

/-- The derivative supplied by the literal interval source. -/
def weilArchimedeanKernelDerivative (L r x : ℝ) : ℝ :=
  ∫ y in 0..L, weilArchimedeanKernelDerivativeIntegrand L r x y

/-- The source tail-density factor `(1/pi^2) h_+(r) S(r,x,L)`. -/
def weilArchimedeanTailSource (L r x : ℝ) : ℝ :=
  weilArchimedeanDensity r / Real.pi ^ 2 * weilArchimedeanKernel L r x

/-- Its derivative sample, still defined from the literal differentiated interval source. -/
def weilArchimedeanTailSourceDerivative (L r x : ℝ) : ℝ :=
  weilArchimedeanDensity r / Real.pi ^ 2 * weilArchimedeanKernelDerivative L r x

theorem hasDerivAt_weilArchimedeanKernel_integrand (L r x y : ℝ) :
    HasDerivAt
      (fun z : ℝ =>
        Real.sin (2 * Real.pi * z * (1 - y / L)) * Real.cos (r * y))
      (weilArchimedeanKernelDerivativeIntegrand L r x y) x := by
  have hinner : HasDerivAt
      (fun z : ℝ => 2 * Real.pi * z * (1 - y / L))
      (2 * Real.pi * (1 - y / L)) x := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id x).const_mul (2 * Real.pi)).mul_const (1 - y / L)
  have hsin : HasDerivAt
      (fun z : ℝ => Real.sin (2 * Real.pi * z * (1 - y / L)))
      (Real.cos (2 * Real.pi * x * (1 - y / L)) *
        (2 * Real.pi * (1 - y / L))) x := by
    change HasDerivAt
      (Real.sin ∘ fun z : ℝ => 2 * Real.pi * z * (1 - y / L))
      (Real.cos (2 * Real.pi * x * (1 - y / L)) *
        (2 * Real.pi * (1 - y / L))) x
    exact (Real.hasDerivAt_sin _).comp x hinner
  simpa only [weilArchimedeanKernelDerivativeIntegrand, mul_assoc, mul_left_comm,
    mul_comm] using hsin.mul_const (Real.cos (r * y))

theorem hasDerivAt_weilArchimedeanKernel (L r x : ℝ) :
    HasDerivAt (weilArchimedeanKernel L r)
      (weilArchimedeanKernelDerivative L r x) x := by
  let F : ℝ → ℝ → ℝ := fun z y =>
    Real.sin (2 * Real.pi * z * (1 - y / L)) * Real.cos (r * y)
  let F' : ℝ → ℝ → ℝ := fun z y =>
    weilArchimedeanKernelDerivativeIntegrand L r z y
  let bound : ℝ → ℝ := fun y => |2 * Real.pi * (1 - y / L)|
  have hF_cont (z : ℝ) : Continuous (F z) := by
    fun_prop
  have hF'_cont : Continuous (F' x) := by
    dsimp only [F']
    unfold weilArchimedeanKernelDerivativeIntegrand
    fun_prop
  have hbound_cont : Continuous bound := by
    fun_prop
  have hbound : ∀ y : ℝ, ∀ z : ℝ, ‖F' z y‖ ≤ bound y := by
    intro y z
    dsimp [F', bound, weilArchimedeanKernelDerivativeIntegrand]
    calc
      |2 * Real.pi * (1 - y / L) *
          Real.cos (2 * Real.pi * z * (1 - y / L)) * Real.cos (r * y)| ≤
          |2 * Real.pi * (1 - y / L)| * 1 * 1 := by
            rw [abs_mul, abs_mul]
            gcongr <;> exact Real.abs_cos_le_one _
      _ = |2 * Real.pi * (1 - y / L)| := by ring
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (a := (0 : ℝ)) (b := L) (F := F) (F' := F') (x₀ := x)
    (μ := MeasureTheory.volume)
    (s := Set.univ) (bound := bound)
    (Filter.univ_mem)
    (Filter.Eventually.of_forall fun z =>
      (hF_cont z).aestronglyMeasurable.restrict)
    ((hF_cont x).intervalIntegrable 0 L)
    hF'_cont.aestronglyMeasurable.restrict
    (Filter.Eventually.of_forall fun y _ z _ => hbound y z)
    (hbound_cont.intervalIntegrable 0 L)
    (Filter.Eventually.of_forall fun y _ z _ => by
      exact hasDerivAt_weilArchimedeanKernel_integrand L r z y)
  convert h.2 using 1
  all_goals first
    | with_reducible rfl
    | ext z; rfl
    | simp only [F', weilArchimedeanKernelDerivative]

theorem hasDerivAt_weilArchimedeanTailSource (L r x : ℝ) :
    HasDerivAt (weilArchimedeanTailSource L r)
      (weilArchimedeanTailSourceDerivative L r x) x := by
  change HasDerivAt
    (fun y => weilArchimedeanDensity r / Real.pi ^ 2 * weilArchimedeanKernel L r y)
    (weilArchimedeanDensity r / Real.pi ^ 2 * weilArchimedeanKernelDerivative L r x) x
  exact (hasDerivAt_weilArchimedeanKernel L r x).const_mul
    (weilArchimedeanDensity r / Real.pi ^ 2)

/-- A primitive proof for the sine-cosine product integral. -/
theorem integral_neg_sin_mul_cos {L k r : ℝ}
    (hplus : k + r ≠ 0) (hminus : k - r ≠ 0) :
    (∫ y in 0..L, -Real.sin (k * y) * Real.cos (r * y)) =
      (Real.cos ((k + r) * L) - 1) / (2 * (k + r)) +
        (Real.cos ((k - r) * L) - 1) / (2 * (k - r)) := by
  let P : ℝ → ℝ := fun y =>
    Real.cos ((k + r) * y) / (2 * (k + r)) +
      Real.cos ((k - r) * y) / (2 * (k - r))
  have hderiv (y : ℝ) :
      HasDerivAt P (-Real.sin (k * y) * Real.cos (r * y)) y := by
    have h₁ := ((Real.hasDerivAt_cos ((k + r) * y)).comp y
      ((hasDerivAt_id y).const_mul (k + r))).div_const (2 * (k + r))
    have h₂ := ((Real.hasDerivAt_cos ((k - r) * y)).comp y
      ((hasDerivAt_id y).const_mul (k - r))).div_const (2 * (k - r))
    have h₁' : HasDerivAt
        (fun z : ℝ => Real.cos ((k + r) * z) / (2 * (k + r)))
        (-Real.sin ((k + r) * y) / 2) y := by
      simpa only [Function.comp_apply] using h₁.congr_deriv (by
        field_simp [hplus])
    have h₂' : HasDerivAt
        (fun z : ℝ => Real.cos ((k - r) * z) / (2 * (k - r)))
        (-Real.sin ((k - r) * y) / 2) y := by
      simpa only [Function.comp_apply] using h₂.congr_deriv (by
        field_simp [hminus])
    have hvalue :
        -Real.sin (k * y) * Real.cos (r * y) =
          -Real.sin ((k + r) * y) / 2 + -Real.sin ((k - r) * y) / 2 := by
      rw [show (k + r) * y = k * y + r * y by ring,
        show (k - r) * y = k * y - r * y by ring]
      rw [Real.sin_add, Real.sin_sub]
      ring
    change HasDerivAt
      ((fun z : ℝ => Real.cos ((k + r) * z) / (2 * (k + r))) +
        fun z : ℝ => Real.cos ((k - r) * z) / (2 * (k - r)))
      (-Real.sin (k * y) * Real.cos (r * y)) y
    exact (h₁'.add h₂').congr_deriv hvalue.symm
  have hint : IntervalIntegrable
      (fun y : ℝ => -Real.sin (k * y) * Real.cos (r * y)) MeasureTheory.volume 0 L :=
    (by fun_prop : Continuous
      (fun y : ℝ => -Real.sin (k * y) * Real.cos (r * y))).intervalIntegrable 0 L
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hderiv y) hint]
  dsimp [P]
  simp
  field_simp [hplus, hminus]
  ring

/-- A primitive proof for the linearly weighted cosine integral. -/
theorem integral_one_sub_div_mul_cos {L c : ℝ} (hL : L ≠ 0) (hc : c ≠ 0) :
    (∫ y in 0..L, (1 - y / L) * Real.cos (c * y)) =
      (1 - Real.cos (c * L)) / (L * c ^ 2) := by
  let P : ℝ → ℝ := fun y =>
    (1 - y / L) * Real.sin (c * y) / c - Real.cos (c * y) / (L * c ^ 2)
  have hderiv (y : ℝ) :
      HasDerivAt P ((1 - y / L) * Real.cos (c * y)) y := by
    have hlin : HasDerivAt (fun z : ℝ => 1 - z / L) (-1 / L) y := by
      have hdiv : HasDerivAt (fun z : ℝ => z / L) (1 / L) y := by
        simpa only [id_eq] using (hasDerivAt_id y).div_const L
      change HasDerivAt
        ((fun _ : ℝ => 1) - fun z : ℝ => z / L) (-1 / L) y
      exact ((hasDerivAt_const y 1).sub hdiv).congr_deriv (by ring)
    have hcinner : HasDerivAt (fun z : ℝ => c * z) c y := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id y).const_mul c
    have hsin : HasDerivAt (fun z : ℝ => Real.sin (c * z))
        (Real.cos (c * y) * c) y := by
      change HasDerivAt (Real.sin ∘ fun z : ℝ => c * z)
        (Real.cos (c * y) * c) y
      exact (Real.hasDerivAt_sin _).comp y hcinner
    have hcos : HasDerivAt (fun z : ℝ => Real.cos (c * z))
        (-Real.sin (c * y) * c) y := by
      change HasDerivAt (Real.cos ∘ fun z : ℝ => c * z)
        (-Real.sin (c * y) * c) y
      exact (Real.hasDerivAt_cos _).comp y hcinner
    have hmain := (hlin.mul hsin).div_const c
    have htail := hcos.div_const (L * c ^ 2)
    have hvalue :
        (1 - y / L) * Real.cos (c * y) =
          ((-1 / L) * Real.sin (c * y) +
              (1 - y / L) * (Real.cos (c * y) * c)) / c -
            (-Real.sin (c * y) * c) / (L * c ^ 2) := by
      field_simp [hL, hc]
      ring
    change HasDerivAt
      ((fun z : ℝ => (1 - z / L) * Real.sin (c * z) / c) -
        fun z : ℝ => Real.cos (c * z) / (L * c ^ 2))
      ((1 - y / L) * Real.cos (c * y)) y
    exact (hmain.sub htail).congr_deriv hvalue.symm
  have hint : IntervalIntegrable
      (fun y : ℝ => (1 - y / L) * Real.cos (c * y)) MeasureTheory.volume 0 L :=
    (by fun_prop : Continuous
      (fun y : ℝ => (1 - y / L) * Real.cos (c * y))).intervalIntegrable 0 L
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hderiv y) hint]
  dsimp [P]
  simp [hL]
  field_simp [hL, hc]
  ring

theorem weilArchimedeanKernel_integer_phase {L y : ℝ} (hL : L ≠ 0) (n : ℤ) :
    Real.sin (2 * Real.pi * (n : ℝ) * (1 - y / L)) =
      -Real.sin (weilArchimedeanBandScale L * (n : ℝ) * y) := by
  rw [show 2 * Real.pi * (n : ℝ) * (1 - y / L) =
      (n : ℝ) * (2 * Real.pi) -
        weilArchimedeanBandScale L * (n : ℝ) * y by
    rw [weilArchimedeanBandScale]
    field_simp [hL]
  ]
  simpa only using Real.sin_int_mul_two_pi_sub _ n

theorem weilArchimedeanKernel_integer_cos_phase {L y : ℝ} (hL : L ≠ 0) (n : ℤ) :
    Real.cos (2 * Real.pi * (n : ℝ) * (1 - y / L)) =
      Real.cos (weilArchimedeanBandScale L * (n : ℝ) * y) := by
  rw [show 2 * Real.pi * (n : ℝ) * (1 - y / L) =
      (n : ℝ) * (2 * Real.pi) -
        weilArchimedeanBandScale L * (n : ℝ) * y by
    rw [weilArchimedeanBandScale]
    field_simp [hL]
  ]
  simpa only using Real.cos_int_mul_two_pi_sub _ n

/-- The literal interval kernel evaluated at an integer node, before the `a=r/rho` rewrite. -/
theorem weilArchimedeanKernel_integer_eq_raw {L r : ℝ} (hL : L ≠ 0) (n : ℤ)
    (hplus : weilArchimedeanBandScale L * (n : ℝ) + r ≠ 0)
    (hminus : weilArchimedeanBandScale L * (n : ℝ) - r ≠ 0) :
    weilArchimedeanKernel L r n =
      2 * Real.sin (L * r / 2) ^ 2 *
        (weilArchimedeanBandScale L * (n : ℝ)) /
          (r ^ 2 - (weilArchimedeanBandScale L * (n : ℝ)) ^ 2) := by
  let k : ℝ := weilArchimedeanBandScale L * (n : ℝ)
  change weilArchimedeanKernel L r n =
    2 * Real.sin (L * r / 2) ^ 2 * k / (r ^ 2 - k ^ 2)
  have hcosPlus : Real.cos ((k + r) * L) = Real.cos (r * L) := by
    rw [show (k + r) * L = r * L + (n : ℝ) * (2 * Real.pi) by
      dsimp [k]
      rw [weilArchimedeanBandScale]
      field_simp [hL]
      ring]
    simpa only using Real.cos_add_int_mul_two_pi _ n
  have hcosMinus : Real.cos ((k - r) * L) = Real.cos (r * L) := by
    rw [show (k - r) * L = (n : ℝ) * (2 * Real.pi) - r * L by
      dsimp [k]
      rw [weilArchimedeanBandScale]
      field_simp [hL]
    ]
    simpa only using Real.cos_int_mul_two_pi_sub _ n
  have hcosHalf : Real.cos (r * L) = 1 - 2 * Real.sin (L * r / 2) ^ 2 := by
    rw [show r * L = 2 * (L * r / 2) by ring, Real.cos_two_mul_eq_one_sub]
  rw [weilArchimedeanKernel]
  have hcongr :
      (∫ y in 0..L,
        Real.sin (2 * Real.pi * (n : ℝ) * (1 - y / L)) * Real.cos (r * y)) =
        ∫ y in 0..L, -Real.sin (k * y) * Real.cos (r * y) := by
    apply intervalIntegral.integral_congr
    intro y _
    change Real.sin (2 * Real.pi * (n : ℝ) * (1 - y / L)) * Real.cos (r * y) =
      -Real.sin (k * y) * Real.cos (r * y)
    rw [weilArchimedeanKernel_integer_phase hL n]
  rw [hcongr, integral_neg_sin_mul_cos hplus hminus, hcosPlus, hcosMinus, hcosHalf]
  have hden : r ^ 2 - k ^ 2 ≠ 0 := by
    rw [show r ^ 2 - k ^ 2 = -(k + r) * (k - r) by ring]
    exact mul_ne_zero (neg_ne_zero.mpr hplus) hminus
  field_simp [hplus, hminus, hden]
  ring

/-- The derivative of the true literal interval kernel at an integer node. -/
theorem weilArchimedeanKernelDerivative_integer_eq_raw {L r : ℝ}
    (hL : L ≠ 0) (n : ℤ)
    (hplus : weilArchimedeanBandScale L * (n : ℝ) + r ≠ 0)
    (hminus : weilArchimedeanBandScale L * (n : ℝ) - r ≠ 0) :
    weilArchimedeanKernelDerivative L r n =
      2 * weilArchimedeanBandScale L * Real.sin (L * r / 2) ^ 2 *
        (r ^ 2 + (weilArchimedeanBandScale L * (n : ℝ)) ^ 2) /
          (r ^ 2 - (weilArchimedeanBandScale L * (n : ℝ)) ^ 2) ^ 2 := by
  let k : ℝ := weilArchimedeanBandScale L * (n : ℝ)
  change weilArchimedeanKernelDerivative L r n =
    2 * weilArchimedeanBandScale L * Real.sin (L * r / 2) ^ 2 *
      (r ^ 2 + k ^ 2) / (r ^ 2 - k ^ 2) ^ 2
  have hkminus : k - r ≠ 0 := hminus
  have hkplus : k + r ≠ 0 := hplus
  have hden : r ^ 2 - k ^ 2 ≠ 0 := by
    rw [show r ^ 2 - k ^ 2 = -(k + r) * (k - r) by ring]
    exact mul_ne_zero (neg_ne_zero.mpr hkplus) hkminus
  have hcosMinus : Real.cos ((k - r) * L) = Real.cos (r * L) := by
    rw [show (k - r) * L = (n : ℝ) * (2 * Real.pi) - r * L by
      dsimp [k]
      rw [weilArchimedeanBandScale]
      field_simp [hL]
    ]
    simpa only using Real.cos_int_mul_two_pi_sub _ n
  have hcosPlus : Real.cos ((k + r) * L) = Real.cos (r * L) := by
    rw [show (k + r) * L = r * L + (n : ℝ) * (2 * Real.pi) by
      dsimp [k]
      rw [weilArchimedeanBandScale]
      field_simp [hL]
      ring]
    simpa only using Real.cos_add_int_mul_two_pi _ n
  have hcosHalf : Real.cos (r * L) = 1 - 2 * Real.sin (L * r / 2) ^ 2 := by
    rw [show r * L = 2 * (L * r / 2) by ring, Real.cos_two_mul_eq_one_sub]
  rw [weilArchimedeanKernelDerivative]
  have hcongr :
      (∫ y in 0..L, weilArchimedeanKernelDerivativeIntegrand L r (n : ℝ) y) =
        ∫ y in 0..L,
          Real.pi * ((1 - y / L) * Real.cos ((k - r) * y) +
            (1 - y / L) * Real.cos ((k + r) * y)) := by
    apply intervalIntegral.integral_congr
    intro y _
    rw [weilArchimedeanKernelDerivativeIntegrand,
      weilArchimedeanKernel_integer_cos_phase hL n]
    change 2 * Real.pi * (1 - y / L) * Real.cos (k * y) * Real.cos (r * y) =
      Real.pi * ((1 - y / L) * Real.cos ((k - r) * y) +
        (1 - y / L) * Real.cos ((k + r) * y))
    rw [show (k - r) * y = k * y - r * y by ring,
      show (k + r) * y = k * y + r * y by ring]
    calc
      2 * Real.pi * (1 - y / L) * Real.cos (k * y) * Real.cos (r * y) =
          Real.pi * (1 - y / L) *
            (2 * Real.cos (k * y) * Real.cos (r * y)) := by ring
      _ = Real.pi * (1 - y / L) *
          (Real.cos (k * y - r * y) + Real.cos (k * y + r * y)) := by
            rw [Real.two_mul_cos_mul_cos]
      _ = Real.pi * ((1 - y / L) * Real.cos (k * y - r * y) +
          (1 - y / L) * Real.cos (k * y + r * y)) := by ring
  rw [hcongr, intervalIntegral.integral_const_mul]
  have hminusInt : IntervalIntegrable
      (fun y : ℝ => (1 - y / L) * Real.cos ((k - r) * y))
      MeasureTheory.volume 0 L := (by fun_prop : Continuous
        (fun y : ℝ => (1 - y / L) * Real.cos ((k - r) * y))).intervalIntegrable 0 L
  have hplusInt : IntervalIntegrable
      (fun y : ℝ => (1 - y / L) * Real.cos ((k + r) * y))
      MeasureTheory.volume 0 L := (by fun_prop : Continuous
        (fun y : ℝ => (1 - y / L) * Real.cos ((k + r) * y))).intervalIntegrable 0 L
  rw [intervalIntegral.integral_add hminusInt hplusInt,
    integral_one_sub_div_mul_cos hL hkminus,
    integral_one_sub_div_mul_cos hL hkplus,
    hcosMinus, hcosPlus, hcosHalf]
  rw [weilArchimedeanBandScale]
  field_simp [hL, hkplus, hkminus, hden, Real.pi_ne_zero]
  ring

theorem weilArchimedeanBandScale_pos {L : ℝ} (hL : 0 < L) :
    0 < weilArchimedeanBandScale L := by
  exact div_pos (mul_pos (by norm_num) Real.pi_pos) hL

theorem abs_weilFiniteCenteredFrequency_le (N : ℕ) (i : Fin (2 * N + 1)) :
    |(weilFiniteCenteredFrequency N i : ℝ)| ≤ N := by
  rw [abs_le]
  have hbound :
    -(N : ℤ) ≤ weilFiniteCenteredFrequency N i ∧
      weilFiniteCenteredFrequency N i ≤ (N : ℤ) := by
    unfold weilFiniteCenteredFrequency
    omega
  exact_mod_cast hbound

theorem weilArchimedeanBand_separation {L r : ℝ} {N : ℕ}
    (hL : 0 < L) (hr : weilArchimedeanBandScale L * N < r)
    (i : Fin (2 * N + 1)) :
    weilArchimedeanBandScale L * (weilFiniteCenteredFrequency N i : ℝ) + r ≠ 0 ∧
      weilArchimedeanBandScale L * (weilFiniteCenteredFrequency N i : ℝ) - r ≠ 0 := by
  have hrho := weilArchimedeanBandScale_pos hL
  have habs :
      |weilArchimedeanBandScale L * (weilFiniteCenteredFrequency N i : ℝ)| ≤
        weilArchimedeanBandScale L * N := by
    rw [abs_mul, abs_of_pos hrho]
    exact mul_le_mul_of_nonneg_left (abs_weilFiniteCenteredFrequency_le N i) hrho.le
  have hlower :
      -r < weilArchimedeanBandScale L * (weilFiniteCenteredFrequency N i : ℝ) := by
    have := (neg_le_of_abs_le habs)
    linarith
  have hupper :
      weilArchimedeanBandScale L * (weilFiniteCenteredFrequency N i : ℝ) < r := by
    have := (le_of_abs_le habs)
    linarith
  constructor <;> linarith

/-- The exact source node formula in the source variables `rho` and `a=r/rho`. -/
theorem weilArchimedeanKernel_integer_eq {L r : ℝ} (hL : 0 < L) (n : ℤ)
    (hplus : weilArchimedeanBandScale L * (n : ℝ) + r ≠ 0)
    (hminus : weilArchimedeanBandScale L * (n : ℝ) - r ≠ 0) :
    weilArchimedeanKernel L r n =
      (2 * Real.sin (L * r / 2) ^ 2 / weilArchimedeanBandScale L) *
        (n : ℝ) /
          ((r / weilArchimedeanBandScale L) ^ 2 - (n : ℝ) ^ 2) := by
  let rho : ℝ := weilArchimedeanBandScale L
  have hrho : rho ≠ 0 := (weilArchimedeanBandScale_pos hL).ne'
  have hraw : r ^ 2 - (rho * (n : ℝ)) ^ 2 ≠ 0 := by
    rw [show r ^ 2 - (rho * (n : ℝ)) ^ 2 =
      -(rho * (n : ℝ) + r) * (rho * (n : ℝ) - r) by ring]
    exact mul_ne_zero (neg_ne_zero.mpr hplus) hminus
  have hnorm : (r / rho) ^ 2 - (n : ℝ) ^ 2 ≠ 0 := by
    intro hz
    apply hraw
    field_simp [hrho] at hz ⊢
    nlinarith
  rw [weilArchimedeanKernel_integer_eq_raw hL.ne' n hplus hminus]
  change 2 * Real.sin (L * r / 2) ^ 2 * (rho * (n : ℝ)) /
      (r ^ 2 - (rho * (n : ℝ)) ^ 2) =
    (2 * Real.sin (L * r / 2) ^ 2 / rho) * (n : ℝ) /
      ((r / rho) ^ 2 - (n : ℝ) ^ 2)
  field_simp [hrho, hraw, hnorm]

/-- The exact true-source diagonal formula in the source variables `rho` and `a=r/rho`. -/
theorem weilArchimedeanKernelDerivative_integer_eq {L r : ℝ}
    (hL : 0 < L) (n : ℤ)
    (hplus : weilArchimedeanBandScale L * (n : ℝ) + r ≠ 0)
    (hminus : weilArchimedeanBandScale L * (n : ℝ) - r ≠ 0) :
    weilArchimedeanKernelDerivative L r n =
      (2 * Real.sin (L * r / 2) ^ 2 / weilArchimedeanBandScale L) *
        ((r / weilArchimedeanBandScale L) ^ 2 + (n : ℝ) ^ 2) /
          ((r / weilArchimedeanBandScale L) ^ 2 - (n : ℝ) ^ 2) ^ 2 := by
  let rho : ℝ := weilArchimedeanBandScale L
  have hrho : rho ≠ 0 := (weilArchimedeanBandScale_pos hL).ne'
  have hraw : r ^ 2 - (rho * (n : ℝ)) ^ 2 ≠ 0 := by
    rw [show r ^ 2 - (rho * (n : ℝ)) ^ 2 =
      -(rho * (n : ℝ) + r) * (rho * (n : ℝ) - r) by ring]
    exact mul_ne_zero (neg_ne_zero.mpr hplus) hminus
  have hnorm : (r / rho) ^ 2 - (n : ℝ) ^ 2 ≠ 0 := by
    intro hz
    apply hraw
    field_simp [hrho] at hz ⊢
    nlinarith
  rw [weilArchimedeanKernelDerivative_integer_eq_raw hL.ne' n hplus hminus]
  change 2 * rho * Real.sin (L * r / 2) ^ 2 *
      (r ^ 2 + (rho * (n : ℝ)) ^ 2) /
        (r ^ 2 - (rho * (n : ℝ)) ^ 2) ^ 2 =
    (2 * Real.sin (L * r / 2) ^ 2 / rho) *
      ((r / rho) ^ 2 + (n : ℝ) ^ 2) /
        ((r / rho) ^ 2 - (n : ℝ) ^ 2) ^ 2
  field_simp [hrho, hraw, hnorm]

/-- The normalized tail parameter `a=r/rho`. -/
def weilArchimedeanTailParameter (L r : ℝ) : ℝ :=
  r / weilArchimedeanBandScale L

/-- The scalar in the closed divided-difference entry. -/
def weilArchimedeanTailCoefficient (L r : ℝ) : ℝ :=
  2 * weilArchimedeanDensity r * Real.sin (L * r / 2) ^ 2 /
    (Real.pi ^ 2 * weilArchimedeanBandScale L)

/-- The half-coefficient multiplying the two Cauchy outer products. -/
def weilArchimedeanCauchyCoefficient (L r : ℝ) : ℝ :=
  weilArchimedeanDensity r * Real.sin (L * r / 2) ^ 2 /
    (Real.pi ^ 2 * weilArchimedeanBandScale L)

theorem weilArchimedeanTailCoefficient_eq_two_mul (L r : ℝ) :
    weilArchimedeanTailCoefficient L r =
      2 * weilArchimedeanCauchyCoefficient L r := by
  rw [weilArchimedeanTailCoefficient, weilArchimedeanCauchyCoefficient]
  ring

/-- Values sampled from the literal archimedean tail source. -/
def weilArchimedeanSourceValue (L r : ℝ) (N : ℕ)
    (i : Fin (2 * N + 1)) : ℝ :=
  weilArchimedeanTailSource L r (weilFiniteCenteredFrequency N i)

/-- Derivatives sampled from the differentiated literal archimedean tail source. -/
def weilArchimedeanSourceDerivative (L r : ℝ) (N : ℕ)
    (i : Fin (2 * N + 1)) : ℝ :=
  weilArchimedeanTailSourceDerivative L r (weilFiniteCenteredFrequency N i)

theorem hasDerivAt_weilArchimedeanTailSource_centered (L r : ℝ) (N : ℕ)
    (i : Fin (2 * N + 1)) :
    HasDerivAt (weilArchimedeanTailSource L r)
      (weilArchimedeanSourceDerivative L r N i)
      (weilFiniteCenteredFrequency N i) := by
  exact hasDerivAt_weilArchimedeanTailSource L r _

theorem weilArchimedeanSourceValue_eq {L r : ℝ} {N : ℕ}
    (hL : 0 < L) (hr : weilArchimedeanBandScale L * N < r)
    (i : Fin (2 * N + 1)) :
    weilArchimedeanSourceValue L r N i =
      weilArchimedeanTailCoefficient L r *
        (weilFiniteCenteredFrequency N i : ℝ) /
          (weilArchimedeanTailParameter L r ^ 2 -
            (weilFiniteCenteredFrequency N i : ℝ) ^ 2) := by
  obtain ⟨hplus, hminus⟩ := weilArchimedeanBand_separation hL hr i
  rw [weilArchimedeanSourceValue, weilArchimedeanTailSource,
    weilArchimedeanKernel_integer_eq hL _ hplus hminus]
  rw [weilArchimedeanTailCoefficient, weilArchimedeanTailParameter]
  ring

theorem weilArchimedeanSourceDerivative_eq {L r : ℝ} {N : ℕ}
    (hL : 0 < L) (hr : weilArchimedeanBandScale L * N < r)
    (i : Fin (2 * N + 1)) :
    weilArchimedeanSourceDerivative L r N i =
      weilArchimedeanTailCoefficient L r *
        (weilArchimedeanTailParameter L r ^ 2 +
          (weilFiniteCenteredFrequency N i : ℝ) ^ 2) /
          (weilArchimedeanTailParameter L r ^ 2 -
            (weilFiniteCenteredFrequency N i : ℝ) ^ 2) ^ 2 := by
  obtain ⟨hplus, hminus⟩ := weilArchimedeanBand_separation hL hr i
  rw [weilArchimedeanSourceDerivative, weilArchimedeanTailSourceDerivative,
    weilArchimedeanKernelDerivative_integer_eq hL _ hplus hminus]
  rw [weilArchimedeanTailCoefficient, weilArchimedeanTailParameter]
  ring

theorem weilArchimedeanTailParameter_sub_frequency_ne_zero {L r : ℝ} {N : ℕ}
    (hL : 0 < L) (hr : weilArchimedeanBandScale L * N < r)
    (i : Fin (2 * N + 1)) :
    weilArchimedeanTailParameter L r -
      (weilFiniteCenteredFrequency N i : ℝ) ≠ 0 := by
  have hrho := (weilArchimedeanBandScale_pos hL).ne'
  have hsep := (weilArchimedeanBand_separation hL hr i).2
  rw [weilArchimedeanTailParameter]
  intro hz
  apply hsep
  field_simp [hrho] at hz ⊢
  linarith

theorem weilArchimedeanTailParameter_add_frequency_ne_zero {L r : ℝ} {N : ℕ}
    (hL : 0 < L) (hr : weilArchimedeanBandScale L * N < r)
    (i : Fin (2 * N + 1)) :
    weilArchimedeanTailParameter L r +
      (weilFiniteCenteredFrequency N i : ℝ) ≠ 0 := by
  have hrho := (weilArchimedeanBandScale_pos hL).ne'
  have hsep := (weilArchimedeanBand_separation hL hr i).1
  rw [weilArchimedeanTailParameter]
  intro hz
  apply hsep
  field_simp [hrho] at hz ⊢
  linarith

theorem weilArchimedeanTailDenominator_ne_zero {L r : ℝ} {N : ℕ}
    (hL : 0 < L) (hr : weilArchimedeanBandScale L * N < r)
    (i : Fin (2 * N + 1)) :
    weilArchimedeanTailParameter L r ^ 2 -
      (weilFiniteCenteredFrequency N i : ℝ) ^ 2 ≠ 0 := by
  rw [show weilArchimedeanTailParameter L r ^ 2 -
      (weilFiniteCenteredFrequency N i : ℝ) ^ 2 =
    (weilArchimedeanTailParameter L r - (weilFiniteCenteredFrequency N i : ℝ)) *
      (weilArchimedeanTailParameter L r + (weilFiniteCenteredFrequency N i : ℝ)) by
        ring]
  exact mul_ne_zero
    (weilArchimedeanTailParameter_sub_frequency_ne_zero hL hr i)
    (weilArchimedeanTailParameter_add_frequency_ne_zero hL hr i)

theorem weilArchimedeanSourceValue_rev {L r : ℝ} {N : ℕ}
    (hL : 0 < L) (hr : weilArchimedeanBandScale L * N < r)
    (i : Fin (2 * N + 1)) :
    weilArchimedeanSourceValue L r N i.rev =
      -weilArchimedeanSourceValue L r N i := by
  rw [weilArchimedeanSourceValue_eq hL hr, weilArchimedeanSourceValue_eq hL hr,
    weilFiniteCenteredFrequency_rev]
  push_cast
  ring

theorem weilArchimedeanSourceDerivative_rev {L r : ℝ} {N : ℕ}
    (hL : 0 < L) (hr : weilArchimedeanBandScale L * N < r)
    (i : Fin (2 * N + 1)) :
    weilArchimedeanSourceDerivative L r N i.rev =
      weilArchimedeanSourceDerivative L r N i := by
  rw [weilArchimedeanSourceDerivative_eq hL hr,
    weilArchimedeanSourceDerivative_eq hL hr, weilFiniteCenteredFrequency_rev]
  push_cast
  ring

/-- The finite divided-difference matrix built from the literal source samples. -/
def weilFiniteArchimedeanDensityMatrix (L r : ℝ) (N : ℕ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ :=
  weilFiniteDividedDifferenceMatrix N
    (weilArchimedeanSourceDerivative L r N) (weilArchimedeanSourceValue L r N)

/-- The rational closed entry forced by the literal source samples. -/
def weilFiniteArchimedeanClosedEntry (L r : ℝ) (N : ℕ)
    (i j : Fin (2 * N + 1)) : ℝ :=
  weilArchimedeanTailCoefficient L r *
    (weilArchimedeanTailParameter L r ^ 2 +
      (weilFiniteCenteredFrequency N i : ℝ) *
        (weilFiniteCenteredFrequency N j : ℝ)) /
      ((weilArchimedeanTailParameter L r ^ 2 -
          (weilFiniteCenteredFrequency N i : ℝ) ^ 2) *
        (weilArchimedeanTailParameter L r ^ 2 -
          (weilFiniteCenteredFrequency N j : ℝ) ^ 2))

theorem weilFiniteArchimedeanDensityMatrix_apply {L r : ℝ} {N : ℕ}
    (hL : 0 < L) (hr : weilArchimedeanBandScale L * N < r)
    (i j : Fin (2 * N + 1)) :
    weilFiniteArchimedeanDensityMatrix L r N i j =
      weilFiniteArchimedeanClosedEntry L r N i j := by
  by_cases hij : i = j
  · subst j
    rw [weilFiniteArchimedeanDensityMatrix, weilFiniteDividedDifferenceMatrix]
    simp only [if_pos]
    rw [weilArchimedeanSourceDerivative_eq hL hr,
      weilFiniteArchimedeanClosedEntry]
    ring
  · have hfreqInt := weilFiniteCenteredFrequency_sub_ne_zero hij
    have hfreq :
        (weilFiniteCenteredFrequency N i : ℝ) -
          (weilFiniteCenteredFrequency N j : ℝ) ≠ 0 := by
      exact_mod_cast hfreqInt
    have hdi := weilArchimedeanTailDenominator_ne_zero hL hr i
    have hdj := weilArchimedeanTailDenominator_ne_zero hL hr j
    rw [weilFiniteArchimedeanDensityMatrix, weilFiniteDividedDifferenceMatrix]
    simp only [hij, if_false]
    rw [weilArchimedeanSourceValue_eq hL hr,
      weilArchimedeanSourceValue_eq hL hr,
      show ((weilFiniteCenteredFrequency N i -
          weilFiniteCenteredFrequency N j : ℤ) : ℝ) =
        (weilFiniteCenteredFrequency N i : ℝ) -
          (weilFiniteCenteredFrequency N j : ℝ) by push_cast; rfl,
      weilFiniteArchimedeanClosedEntry]
    field_simp [hfreq, hdi, hdj]
    ring

/-- The Cauchy vector `p_r(n)=1/(a-n)`. -/
def weilFiniteArchimedeanMinusVector (L r : ℝ) (N : ℕ) :
    Fin (2 * N + 1) → ℝ :=
  fun i => 1 / (weilArchimedeanTailParameter L r -
    (weilFiniteCenteredFrequency N i : ℝ))

/-- The Cauchy vector `q_r(n)=1/(a+n)`. -/
def weilFiniteArchimedeanPlusVector (L r : ℝ) (N : ℕ) :
    Fin (2 * N + 1) → ℝ :=
  fun i => 1 / (weilArchimedeanTailParameter L r +
    (weilFiniteCenteredFrequency N i : ℝ))

theorem weilFiniteArchimedeanMinusVector_rev (L r : ℝ) (N : ℕ)
    (i : Fin (2 * N + 1)) :
    weilFiniteArchimedeanMinusVector L r N i.rev =
      weilFiniteArchimedeanPlusVector L r N i := by
  rw [weilFiniteArchimedeanMinusVector, weilFiniteArchimedeanPlusVector,
    weilFiniteCenteredFrequency_rev]
  push_cast
  ring

theorem weilFiniteArchimedeanPlusVector_rev (L r : ℝ) (N : ℕ)
    (i : Fin (2 * N + 1)) :
    weilFiniteArchimedeanPlusVector L r N i.rev =
      weilFiniteArchimedeanMinusVector L r N i := by
  rw [weilFiniteArchimedeanMinusVector, weilFiniteArchimedeanPlusVector,
    weilFiniteCenteredFrequency_rev]
  push_cast
  ring

theorem weilFiniteArchimedeanClosedEntry_eq_cauchy {L r : ℝ} {N : ℕ}
    (hL : 0 < L) (hr : weilArchimedeanBandScale L * N < r)
    (i j : Fin (2 * N + 1)) :
    weilFiniteArchimedeanClosedEntry L r N i j =
      weilArchimedeanCauchyCoefficient L r *
        (weilFiniteArchimedeanMinusVector L r N i *
            weilFiniteArchimedeanMinusVector L r N j +
          weilFiniteArchimedeanPlusVector L r N i *
            weilFiniteArchimedeanPlusVector L r N j) := by
  have him := weilArchimedeanTailParameter_sub_frequency_ne_zero hL hr i
  have hip := weilArchimedeanTailParameter_add_frequency_ne_zero hL hr i
  have hjm := weilArchimedeanTailParameter_sub_frequency_ne_zero hL hr j
  have hjp := weilArchimedeanTailParameter_add_frequency_ne_zero hL hr j
  have hdi := weilArchimedeanTailDenominator_ne_zero hL hr i
  have hdj := weilArchimedeanTailDenominator_ne_zero hL hr j
  rw [weilFiniteArchimedeanClosedEntry, weilArchimedeanTailCoefficient_eq_two_mul]
  simp only [weilFiniteArchimedeanMinusVector, weilFiniteArchimedeanPlusVector]
  field_simp [him, hip, hjm, hjp, hdi, hdj]
  ring

theorem weilFiniteArchimedeanDensityMatrix_rankTwo {L r : ℝ} {N : ℕ}
    (hL : 0 < L) (hr : weilArchimedeanBandScale L * N < r) :
    weilFiniteArchimedeanDensityMatrix L r N =
      weilArchimedeanCauchyCoefficient L r •
        (Matrix.vecMulVec (weilFiniteArchimedeanMinusVector L r N)
            (weilFiniteArchimedeanMinusVector L r N) +
          Matrix.vecMulVec (weilFiniteArchimedeanPlusVector L r N)
            (weilFiniteArchimedeanPlusVector L r N)) := by
  ext i j
  rw [weilFiniteArchimedeanDensityMatrix_apply hL hr,
    weilFiniteArchimedeanClosedEntry_eq_cauchy hL hr]
  simp [Matrix.vecMulVec]

theorem weilFiniteArchimedeanDensityMatrix_reflection {L r : ℝ} {N : ℕ}
    (hL : 0 < L) (hr : weilArchimedeanBandScale L * N < r)
    (i j : Fin (2 * N + 1)) :
    weilFiniteArchimedeanDensityMatrix L r N i.rev j.rev =
      weilFiniteArchimedeanDensityMatrix L r N i j := by
  exact weilFiniteDividedDifferenceMatrix_reflection N _ _
    (weilArchimedeanSourceDerivative_rev hL hr)
    (weilArchimedeanSourceValue_rev hL hr) i j

theorem weilFiniteArchimedeanDensityMatrix_mulVec_isEven {L r : ℝ} {N : ℕ}
    (hL : 0 < L) (hr : weilArchimedeanBandScale L * N < r)
    {x : Fin (2 * N + 1) → ℝ} (hx : WeilFiniteIsEven x) :
    WeilFiniteIsEven (weilFiniteArchimedeanDensityMatrix L r N *ᵥ x) :=
  weilFiniteMatrix_mulVec_isEven _
    (weilFiniteArchimedeanDensityMatrix_reflection hL hr) hx

theorem weilFiniteArchimedeanDensityMatrix_mulVec_isOdd {L r : ℝ} {N : ℕ}
    (hL : 0 < L) (hr : weilArchimedeanBandScale L * N < r)
    {x : Fin (2 * N + 1) → ℝ} (hx : WeilFiniteIsOdd x) :
    WeilFiniteIsOdd (weilFiniteArchimedeanDensityMatrix L r N *ᵥ x) :=
  weilFiniteMatrix_mulVec_isOdd _
    (weilFiniteArchimedeanDensityMatrix_reflection hL hr) hx

theorem weilFiniteArchimedeanDensityMatrix_quadratic {L r : ℝ} {N : ℕ}
    (hL : 0 < L) (hr : weilArchimedeanBandScale L * N < r)
    (x : Fin (2 * N + 1) → ℝ) :
    x ⬝ᵥ (weilFiniteArchimedeanDensityMatrix L r N *ᵥ x) =
      weilArchimedeanCauchyCoefficient L r *
        ((weilFiniteArchimedeanMinusVector L r N ⬝ᵥ x) ^ 2 +
          (weilFiniteArchimedeanPlusVector L r N ⬝ᵥ x) ^ 2) := by
  rw [weilFiniteArchimedeanDensityMatrix_rankTwo hL hr, Matrix.smul_mulVec,
    Matrix.add_mulVec, Matrix.vecMulVec_mulVec, Matrix.vecMulVec_mulVec]
  simp only [dotProduct_smul, dotProduct_add, op_smul_eq_mul]
  rw [dotProduct_comm x (weilFiniteArchimedeanMinusVector L r N),
    dotProduct_comm x (weilFiniteArchimedeanPlusVector L r N)]
  ring

theorem weilArchimedeanCauchyCoefficient_nonneg {L r : ℝ}
    (hL : 0 < L) (hdensity : 0 ≤ weilArchimedeanDensity r) :
    0 ≤ weilArchimedeanCauchyCoefficient L r := by
  rw [weilArchimedeanCauchyCoefficient]
  exact div_nonneg (mul_nonneg hdensity (sq_nonneg _))
    (mul_nonneg (sq_nonneg _) (weilArchimedeanBandScale_pos hL).le)

theorem weilFiniteArchimedeanDensityMatrix_nonneg {L r : ℝ} {N : ℕ}
    (hL : 0 < L) (hr : weilArchimedeanBandScale L * N < r)
    (hdensity : 0 ≤ weilArchimedeanDensity r)
    (x : Fin (2 * N + 1) → ℝ) :
    0 ≤ x ⬝ᵥ (weilFiniteArchimedeanDensityMatrix L r N *ᵥ x) := by
  rw [weilFiniteArchimedeanDensityMatrix_quadratic hL hr]
  exact mul_nonneg (weilArchimedeanCauchyCoefficient_nonneg hL hdensity)
    (add_nonneg (sq_nonneg _) (sq_nonneg _))

@[fun_prop]
theorem continuous_weilArchimedeanDensity : Continuous weilArchimedeanDensity := by
  let U : Set ℂ := {z | 0 < z.re}
  have hU : IsOpen U := by
    dsimp [U]
    exact Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
  have hGammaDiff : DifferentiableOn ℂ Complex.Gamma U := by
    intro z hz
    exact (Complex.differentiableAt_Gamma z (fun m hm => by
      have hre := congrArg Complex.re hm
      simp only [Complex.neg_re, Complex.natCast_re] at hre
      dsimp [U] at hz
      linarith)).differentiableWithinAt
  have hGammaAnalytic : AnalyticOnNhd ℂ Complex.Gamma U :=
    (Complex.analyticOnNhd_iff_differentiableOn hU).2 hGammaDiff
  rw [continuous_iff_continuousAt]
  intro t
  let z : ℂ := (1 / 4 : ℂ) + (t / 2 : ℂ) * Complex.I
  have hz : z ∈ U := by
    simp [z, U]
  have hGammaNe : Complex.Gamma z ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos hz
  have hlog : AnalyticAt ℂ (deriv Complex.Gamma / Complex.Gamma) z :=
    (hGammaAnalytic.deriv z hz).div (hGammaAnalytic z hz) hGammaNe
  have hdigamma : ContinuousAt Complex.digamma z := by
    rw [Complex.digamma_def]
    change ContinuousAt (deriv Complex.Gamma / Complex.Gamma) z
    exact hlog.continuousAt
  have hzmap : ContinuousAt
      (fun u : ℝ => (1 / 4 : ℂ) + (u / 2 : ℂ) * Complex.I) t := by
    fun_prop
  have hcomp : ContinuousAt
      (fun u : ℝ => Complex.digamma ((1 / 4 : ℂ) + (u / 2 : ℂ) * Complex.I)) t := by
    change ContinuousAt
      (Complex.digamma ∘ fun u : ℝ => (1 / 4 : ℂ) + (u / 2 : ℂ) * Complex.I) t
    exact hdigamma.comp_of_eq hzmap (by rfl)
  have hre : ContinuousAt
      (fun u : ℝ =>
        (Complex.digamma ((1 / 4 : ℂ) + (u / 2 : ℂ) * Complex.I)).re) t :=
    Complex.continuous_re.continuousAt.comp hcomp
  change ContinuousAt
    (fun u : ℝ =>
      (Complex.digamma ((1 / 4 : ℂ) + (u / 2 : ℂ) * Complex.I)).re -
        Real.log Real.pi) t
  exact hre.sub continuousAt_const

@[fun_prop]
theorem continuous_weilArchimedeanCauchyCoefficient (L : ℝ) :
    Continuous (weilArchimedeanCauchyCoefficient L) := by
  unfold weilArchimedeanCauchyCoefficient
  fun_prop

theorem continuousOn_weilFiniteArchimedeanMinusVector {L T₁ T₂ : ℝ} {N : ℕ}
    (hL : 0 < L) (hband : weilArchimedeanBandScale L * N < T₁)
    (hT : T₁ ≤ T₂) (i : Fin (2 * N + 1)) :
    ContinuousOn (fun r => weilFiniteArchimedeanMinusVector L r N i)
      (Set.uIcc T₁ T₂) := by
  have hden : ∀ r ∈ Set.uIcc T₁ T₂,
      weilArchimedeanTailParameter L r -
        (weilFiniteCenteredFrequency N i : ℝ) ≠ 0 := by
    intro r hr
    have hrIcc : r ∈ Set.Icc T₁ T₂ := by
      simpa only [Set.uIcc_of_le hT] using hr
    exact weilArchimedeanTailParameter_sub_frequency_ne_zero hL
      (lt_of_lt_of_le hband hrIcc.1) i
  have hcont : Continuous (fun r =>
      weilArchimedeanTailParameter L r -
        (weilFiniteCenteredFrequency N i : ℝ)) := by
    unfold weilArchimedeanTailParameter
    fun_prop
  simpa only [weilFiniteArchimedeanMinusVector, one_div] using
    hcont.continuousOn.inv₀ hden

theorem continuousOn_weilFiniteArchimedeanPlusVector {L T₁ T₂ : ℝ} {N : ℕ}
    (hL : 0 < L) (hband : weilArchimedeanBandScale L * N < T₁)
    (hT : T₁ ≤ T₂) (i : Fin (2 * N + 1)) :
    ContinuousOn (fun r => weilFiniteArchimedeanPlusVector L r N i)
      (Set.uIcc T₁ T₂) := by
  have hden : ∀ r ∈ Set.uIcc T₁ T₂,
      weilArchimedeanTailParameter L r +
        (weilFiniteCenteredFrequency N i : ℝ) ≠ 0 := by
    intro r hr
    have hrIcc : r ∈ Set.Icc T₁ T₂ := by
      simpa only [Set.uIcc_of_le hT] using hr
    exact weilArchimedeanTailParameter_add_frequency_ne_zero hL
      (lt_of_lt_of_le hband hrIcc.1) i
  have hcont : Continuous (fun r =>
      weilArchimedeanTailParameter L r +
        (weilFiniteCenteredFrequency N i : ℝ)) := by
    unfold weilArchimedeanTailParameter
    fun_prop
  simpa only [weilFiniteArchimedeanPlusVector, one_div] using
    hcont.continuousOn.inv₀ hden

theorem weilFiniteArchimedeanDensityMatrix_intervalIntegrable {L T₁ T₂ : ℝ}
    {N : ℕ} (hL : 0 < L) (hband : weilArchimedeanBandScale L * N < T₁)
    (hT : T₁ ≤ T₂) (i j : Fin (2 * N + 1)) :
    IntervalIntegrable (fun r => weilFiniteArchimedeanDensityMatrix L r N i j)
      MeasureTheory.volume T₁ T₂ := by
  let g : ℝ → ℝ := fun r =>
    weilArchimedeanCauchyCoefficient L r *
      (weilFiniteArchimedeanMinusVector L r N i *
          weilFiniteArchimedeanMinusVector L r N j +
        weilFiniteArchimedeanPlusVector L r N i *
          weilFiniteArchimedeanPlusVector L r N j)
  have hg : ContinuousOn g (Set.uIcc T₁ T₂) := by
    exact continuous_weilArchimedeanCauchyCoefficient L |>.continuousOn.mul
      (((continuousOn_weilFiniteArchimedeanMinusVector hL hband hT i).mul
          (continuousOn_weilFiniteArchimedeanMinusVector hL hband hT j)).add
        ((continuousOn_weilFiniteArchimedeanPlusVector hL hband hT i).mul
          (continuousOn_weilFiniteArchimedeanPlusVector hL hband hT j)))
  have heq : Set.EqOn (fun r => weilFiniteArchimedeanDensityMatrix L r N i j) g
      (Set.uIcc T₁ T₂) := by
    intro r hr
    have hrIcc : r ∈ Set.Icc T₁ T₂ := by
      simpa only [Set.uIcc_of_le hT] using hr
    change weilFiniteArchimedeanDensityMatrix L r N i j =
      weilArchimedeanCauchyCoefficient L r *
        (weilFiniteArchimedeanMinusVector L r N i *
            weilFiniteArchimedeanMinusVector L r N j +
          weilFiniteArchimedeanPlusVector L r N i *
            weilFiniteArchimedeanPlusVector L r N j)
    rw [weilFiniteArchimedeanDensityMatrix_apply hL
      (lt_of_lt_of_le hband hrIcc.1),
      weilFiniteArchimedeanClosedEntry_eq_cauchy hL
        (lt_of_lt_of_le hband hrIcc.1)]
  exact hg.intervalIntegrable.congr fun _ hr =>
    (heq (Set.uIoc_subset_uIcc hr)).symm

/-- Entrywise interval integration commutes with a finite matrix quadratic form. -/
theorem finiteMatrix_quadratic_intervalIntegral {m : ℕ} {T₁ T₂ : ℝ}
    (A : ℝ → Matrix (Fin m) (Fin m) ℝ)
    (hA : ∀ i j, IntervalIntegrable (fun r => A r i j)
      MeasureTheory.volume T₁ T₂)
    (x : Fin m → ℝ) :
    x ⬝ᵥ ((fun i j => ∫ r in T₁..T₂, A r i j) *ᵥ x) =
      ∫ r in T₁..T₂, x ⬝ᵥ (A r *ᵥ x) := by
  have hterm (i j : Fin m) : IntervalIntegrable
      (fun r => x i * (A r i j * x j)) MeasureTheory.volume T₁ T₂ :=
    ((hA i j).mul_const (x j)).const_mul (x i)
  have hrow (i : Fin m) : IntervalIntegrable
      (fun r => ∑ j, x i * (A r i j * x j)) MeasureTheory.volume T₁ T₂ := by
    have hsum := IntervalIntegrable.sum Finset.univ fun j _ => hterm i j
    exact hsum.congr fun r _ => by simp only [Finset.sum_apply]
  simp only [dotProduct, mulVec]
  simp_rw [Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum (s := Finset.univ)
    (fun i _ => hrow i)]
  congr 1
  funext i
  rw [intervalIntegral.integral_finsetSum (s := Finset.univ)
    (fun j _ => hterm i j)]
  simp only [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_mul_const]

/-- The entrywise interval increment of the literal archimedean density matrices. -/
def weilFiniteArchimedeanIncrement (L T₁ T₂ : ℝ) (N : ℕ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ :=
  fun i j => ∫ r in T₁..T₂, weilFiniteArchimedeanDensityMatrix L r N i j

/-- The pointwise sum-of-squares density of the finite quadratic form. -/
def weilFiniteArchimedeanQuadraticDensity (L r : ℝ) (N : ℕ)
    (x : Fin (2 * N + 1) → ℝ) : ℝ :=
  weilArchimedeanCauchyCoefficient L r *
    ((weilFiniteArchimedeanMinusVector L r N ⬝ᵥ x) ^ 2 +
      (weilFiniteArchimedeanPlusVector L r N ⬝ᵥ x) ^ 2)

theorem weilFiniteArchimedeanIncrement_quadratic {L T₁ T₂ : ℝ} {N : ℕ}
    (hL : 0 < L) (hband : weilArchimedeanBandScale L * N < T₁)
    (hT : T₁ ≤ T₂) (x : Fin (2 * N + 1) → ℝ) :
    x ⬝ᵥ (weilFiniteArchimedeanIncrement L T₁ T₂ N *ᵥ x) =
      ∫ r in T₁..T₂, weilFiniteArchimedeanQuadraticDensity L r N x := by
  change x ⬝ᵥ
      ((fun i j => ∫ r in T₁..T₂,
        weilFiniteArchimedeanDensityMatrix L r N i j) *ᵥ x) = _
  rw [finiteMatrix_quadratic_intervalIntegral
    (fun r => weilFiniteArchimedeanDensityMatrix L r N)
    (weilFiniteArchimedeanDensityMatrix_intervalIntegrable hL hband hT) x]
  apply intervalIntegral.integral_congr
  intro r hr
  have hrIcc : r ∈ Set.Icc T₁ T₂ := by
    simpa only [Set.uIcc_of_le hT] using hr
  change x ⬝ᵥ (weilFiniteArchimedeanDensityMatrix L r N *ᵥ x) =
    weilFiniteArchimedeanQuadraticDensity L r N x
  rw [weilFiniteArchimedeanDensityMatrix_quadratic hL
    (lt_of_lt_of_le hband hrIcc.1)]
  rfl

theorem weilFiniteArchimedeanIncrement_nonneg {L T₁ T₂ : ℝ} {N : ℕ}
    (hL : 0 < L) (hband : weilArchimedeanBandScale L * N < T₁)
    (hT : T₁ ≤ T₂)
    (hdensity : ∀ r ∈ Set.Icc T₁ T₂, 0 ≤ weilArchimedeanDensity r)
    (x : Fin (2 * N + 1) → ℝ) :
    0 ≤ x ⬝ᵥ (weilFiniteArchimedeanIncrement L T₁ T₂ N *ᵥ x) := by
  rw [weilFiniteArchimedeanIncrement_quadratic hL hband hT]
  apply intervalIntegral.integral_nonneg hT
  intro r hr
  rw [weilFiniteArchimedeanQuadraticDensity]
  exact mul_nonneg (weilArchimedeanCauchyCoefficient_nonneg hL (hdensity r hr))
    (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem weilArchimedeanTailDensityAudit_endpoint {L T₁ T₂ : ℝ} {N : ℕ}
    (hL : 0 < L) (hband : weilArchimedeanBandScale L * N < T₁)
    (hT : T₁ ≤ T₂)
    (hdensity : ∀ r ∈ Set.Icc T₁ T₂, 0 ≤ weilArchimedeanDensity r) :
    (∀ r, T₁ ≤ r →
      weilFiniteArchimedeanDensityMatrix L r N =
        weilArchimedeanCauchyCoefficient L r •
          (Matrix.vecMulVec (weilFiniteArchimedeanMinusVector L r N)
              (weilFiniteArchimedeanMinusVector L r N) +
            Matrix.vecMulVec (weilFiniteArchimedeanPlusVector L r N)
              (weilFiniteArchimedeanPlusVector L r N))) ∧
      (∀ x, 0 ≤ x ⬝ᵥ (weilFiniteArchimedeanIncrement L T₁ T₂ N *ᵥ x)) := by
  constructor
  · intro r hr
    exact weilFiniteArchimedeanDensityMatrix_rankTwo hL (lt_of_lt_of_le hband hr)
  · intro x
    exact weilFiniteArchimedeanIncrement_nonneg hL hband hT hdensity x

end

end LeanLab.Riemann
