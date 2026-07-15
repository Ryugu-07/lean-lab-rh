import LeanLab.Riemann.LiZeroFormula
import LeanLab.Riemann.TruncatedPerron
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The finite-height zero cutoff in Weil's explicit formula

This module proves the finite rectangular argument-principle identity for the logarithmic
derivative of Riemann's xi function. Height limits and endpoint regularization are not asserted.
-/

open Complex Filter Function MeasureTheory Metric Set Topology
open scoped BigOperators Interval Topology

namespace LeanLab.Riemann

noncomputable section

/-- The positively oriented boundary integral of a rectangle with real bounds `l`, `r` and
imaginary bounds `b`, `t`. -/
def rectangleBoundaryIntegral (f : ℂ → ℂ) (l r b t : ℝ) : ℂ :=
  (∫ x : ℝ in l..r, f (x + b * I)) -
      (∫ x : ℝ in l..r, f (x + t * I)) +
    I * (∫ y : ℝ in b..t, f (r + y * I)) -
    I * (∫ y : ℝ in b..t, f (l + y * I))

/-- A multiplicity-bearing xi zero lies strictly inside the open rectangle. -/
def riemannXiZeroStrictlyInsideRectangle
    (l r b t : ℝ) (p : RiemannXiDivisorZeroIndex) : Prop :=
  l < (riemannXiDivisorZeroValue p).re ∧
    (riemannXiDivisorZeroValue p).re < r ∧
    b < (riemannXiDivisorZeroValue p).im ∧
    (riemannXiDivisorZeroValue p).im < t

instance decidableRiemannXiZeroStrictlyInsideRectangle
    (l r b t : ℝ) (p : RiemannXiDivisorZeroIndex) :
    Decidable (riemannXiZeroStrictlyInsideRectangle l r b t p) := by
  unfold riemannXiZeroStrictlyInsideRectangle
  infer_instance

/-- A multiplicity-bearing xi zero lies on one of the four closed rectangle edges. -/
def riemannXiZeroOnRectangleBoundary
    (l r b t : ℝ) (p : RiemannXiDivisorZeroIndex) : Prop :=
  let rho := riemannXiDivisorZeroValue p
  (rho.im = b ∧ l ≤ rho.re ∧ rho.re ≤ r) ∨
    (rho.im = t ∧ l ≤ rho.re ∧ rho.re ≤ r) ∨
    (rho.re = l ∧ b ≤ rho.im ∧ rho.im ≤ t) ∨
    (rho.re = r ∧ b ≤ rho.im ∧ rho.im ≤ t)

/-- The compensated genus-one xi zero terms are locally uniformly summable away from xi's zeros.

The compensation improves the far-zero bound from reciprocal-linear to reciprocal-quadratic,
which is exactly the summability supplied by the order-one Hadamard product. -/
theorem summableLocallyUniformlyOn_riemannXiLogDerivZeroTerm :
    SummableLocallyUniformlyOn
      (fun p : RiemannXiDivisorZeroIndex => riemannXiLogDerivZeroTerm p)
      riemannXiNonzeroSet := by
  apply SummableLocallyUniformlyOn.of_locally_bounded_eventually
    isOpen_riemannXiNonzeroSet
  intro K hKU hK
  rcases (isBounded_iff_forall_norm_le.1 hK.isBounded) with ⟨R0, hR0⟩
  let R : ℝ := max R0 1
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  have hnormK : ∀ z ∈ K, ‖z‖ ≤ R := fun z hzK =>
    le_trans (hR0 z hzK) (le_max_left _ _)
  let u : RiemannXiDivisorZeroIndex → ℝ := fun p =>
    (2 * R) * (‖riemannXiDivisorZeroValue p‖⁻¹ ^ (2 : ℕ))
  have hu : Summable u :=
    summable_riemannXiDivisorZeroIndex_norm_inv_sq.mul_left (2 * R)
  refine ⟨u, hu, ?_⟩
  have h_big :
      ∀ᶠ p : RiemannXiDivisorZeroIndex in Filter.cofinite,
        (2 * R : ℝ) < ‖riemannXiDivisorZeroValue p‖ := by
    have hfin :
        ({p : RiemannXiDivisorZeroIndex |
          ‖riemannXiDivisorZeroValue p‖ ≤ 2 * R} : Set _).Finite := by
      have hball : Metric.closedBall (0 : ℂ) (2 * R) ⊆ (Set.univ : Set ℂ) := by simp
      exact Complex.Hadamard.divisorZeroIndex₀_norm_le_finite
        (f := riemannXi) (U := (Set.univ : Set ℂ)) (B := 2 * R) hball
    filter_upwards [hfin.eventually_cofinite_notMem] with p hp
    have hnot : ¬‖riemannXiDivisorZeroValue p‖ ≤ 2 * R := by simpa using hp
    exact lt_of_not_ge hnot
  filter_upwards [h_big] with p hp z hzK
  let a : ℂ := riemannXiDivisorZeroValue p
  have ha0 : a ≠ 0 := Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p
  have hza0 : z - a ≠ 0 := sub_ne_zero.mpr
    (ne_riemannXiDivisorZeroValue_of_mem_nonzeroSet (hKU hzK) p)
  have hterm : riemannXiLogDerivZeroTerm p z = z / (a * (z - a)) := by
    rw [riemannXiLogDerivZeroTerm]
    change 1 / (z - a) + 1 / a = z / (a * (z - a))
    field_simp [ha0, hza0]
    ring
  have htri : ‖a‖ ≤ ‖z‖ + ‖z - a‖ := by
    have hraw : ‖a‖ ≤ ‖z‖ + ‖a - z‖ := by
      have h := norm_add_le z (a - z)
      simpa [a, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
    simpa [norm_sub_rev] using hraw
  have hza_lower : ‖a‖ / 2 ≤ ‖z - a‖ := by
    nlinarith [htri, hnormK z hzK, hp]
  rw [hterm, norm_div, norm_mul, div_eq_mul_inv]
  have ha_norm_pos : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  have hza_norm_pos : 0 < ‖z - a‖ := norm_pos_iff.mpr hza0
  calc
    ‖z‖ * (‖a‖ * ‖z - a‖)⁻¹
        = ‖z‖ * ‖a‖⁻¹ * ‖z - a‖⁻¹ := by
            field_simp [ha_norm_pos.ne', hza_norm_pos.ne']
    _ ≤ R * ‖a‖⁻¹ * ‖z - a‖⁻¹ := by
      gcongr
      exact hnormK z hzK
    _ ≤ R * ‖a‖⁻¹ * (2 * ‖a‖⁻¹) := by
            gcongr
            have hhalf_pos : 0 < ‖a‖ / 2 := by positivity
            have hinv : ‖z - a‖⁻¹ ≤ (‖a‖ / 2)⁻¹ := by
              simpa [one_div] using one_div_le_one_div_of_le hhalf_pos hza_lower
            have hhalf_inv : (‖a‖ / 2)⁻¹ = 2 * ‖a‖⁻¹ := by
              field_simp [ha_norm_pos.ne']
            simpa [hhalf_inv] using hinv
    _ = u p := by simp [u, a]; ring

/-- Only finitely many multiplicity-bearing xi zeros lie strictly inside a fixed rectangle. -/
theorem finite_riemannXiZeroStrictlyInsideRectangle (l r b t : ℝ) :
    ({p : RiemannXiDivisorZeroIndex |
      riemannXiZeroStrictlyInsideRectangle l r b t p} : Set _).Finite := by
  let B : ℝ := max |l| |r| + max |b| |t|
  apply (Complex.Hadamard.divisorZeroIndex₀_norm_le_finite
    (f := riemannXi) (U := (Set.univ : Set ℂ)) B (by simp)).subset
  intro p hp
  have hre : l ≤ (riemannXiDivisorZeroValue p).re ∧
      (riemannXiDivisorZeroValue p).re ≤ r := by
    exact ⟨hp.1.le, hp.2.1.le⟩
  have him : b ≤ (riemannXiDivisorZeroValue p).im ∧
      (riemannXiDivisorZeroValue p).im ≤ t := by
    exact ⟨hp.2.2.1.le, hp.2.2.2.le⟩
  calc
    ‖riemannXiDivisorZeroValue p‖ ≤
        |(riemannXiDivisorZeroValue p).re| +
          |(riemannXiDivisorZeroValue p).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ max |l| |r| + max |b| |t| := by
      gcongr
      · exact abs_le_max_abs_abs hre.1 hre.2
      · exact abs_le_max_abs_abs him.1 him.2
    _ = B := rfl

/-- The multiplicity-bearing xi zero index is countable. -/
theorem countable_riemannXiDivisorZeroIndex : Countable RiemannXiDivisorZeroIndex := by
  have hsupp :
      (Function.support (fun p : RiemannXiDivisorZeroIndex =>
        ‖riemannXiDivisorZeroValue p‖⁻¹ ^ (2 : ℕ))).Countable :=
    summable_riemannXiDivisorZeroIndex_norm_inv_sq.countable_support
  have huniv :
      Function.support (fun p : RiemannXiDivisorZeroIndex =>
        ‖riemannXiDivisorZeroValue p‖⁻¹ ^ (2 : ℕ)) = Set.univ := by
    ext p
    simp only [Function.mem_support, ne_eq, Set.mem_univ, iff_true]
    exact pow_ne_zero _ (inv_ne_zero (norm_ne_zero_iff.mpr
      (Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p)))
  rw [huniv] at hsupp
  exact Set.countable_univ_iff.mp hsupp

/-- Project wrapper for Cauchy--Goursat on a rectangular boundary. -/
theorem rectangleBoundaryIntegral_eq_zero_of_differentiableOn
    {f : ℂ → ℂ} {l r b t : ℝ}
    (hf : DifferentiableOn ℂ f ([[l, r]] ×ℂ [[b, t]])) :
    rectangleBoundaryIntegral f l r b t = 0 := by
  let z : ℂ := Complex.mk l b
  let w : ℂ := Complex.mk r t
  have hboundary :=
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn f z w hf
  simpa only [rectangleBoundaryIntegral, z, w, smul_eq_mul] using hboundary

/-- The boundary integral is additive when a rectangle is split along a horizontal line. -/
theorem rectangleBoundaryIntegral_vertical_add
    {f : ℂ → ℂ} {l r b m t : ℝ}
    (hr₁ : IntervalIntegrable (fun y : ℝ => f (r + y * I)) volume b m)
    (hr₂ : IntervalIntegrable (fun y : ℝ => f (r + y * I)) volume m t)
    (hl₁ : IntervalIntegrable (fun y : ℝ => f (l + y * I)) volume b m)
    (hl₂ : IntervalIntegrable (fun y : ℝ => f (l + y * I)) volume m t) :
    rectangleBoundaryIntegral f l r b m + rectangleBoundaryIntegral f l r m t =
      rectangleBoundaryIntegral f l r b t := by
  have hr := intervalIntegral.integral_add_adjacent_intervals hr₁ hr₂
  have hl := intervalIntegral.integral_add_adjacent_intervals hl₁ hl₂
  unfold rectangleBoundaryIntegral
  rw [← hr, ← hl]
  ring

/-- A reciprocal translated off a vertical boundary line is interval integrable there. -/
theorem intervalIntegrable_inv_sub_const_vertical
    {rho : ℂ} {c p q : ℝ} (hc : c ≠ rho.re) :
    IntervalIntegrable
      (fun y : ℝ => (((c : ℂ) + y * I) - rho)⁻¹) volume p q := by
  apply Continuous.intervalIntegrable
  apply Continuous.inv₀
  · fun_prop
  · intro y hzero
    have hre := congrArg Complex.re hzero
    simp only [sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
      mul_one, zero_sub, Complex.zero_re] at hre
    apply hc
    linarith

/-- The reciprocal kernel has zero rectangle integral when its pole's imaginary part lies outside
the rectangle's vertical interval. -/
theorem rectangleBoundaryIntegral_inv_sub_eq_zero_of_im_notMem
    {rho : ℂ} {l r b t : ℝ} (him : rho.im ∉ [[b, t]]) :
    rectangleBoundaryIntegral (fun z : ℂ => (z - rho)⁻¹) l r b t = 0 := by
  apply rectangleBoundaryIntegral_eq_zero_of_differentiableOn
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.inv
  · fun_prop
  · intro hzero
    have hzrho : z = rho := sub_eq_zero.mp hzero
    exact him (hzrho ▸ hz.2)

/-- Translating the argument translates all four bounds of the rectangle boundary integral. -/
theorem rectangleBoundaryIntegral_comp_sub
    (f : ℂ → ℂ) (rho : ℂ) (l r b t : ℝ) :
    rectangleBoundaryIntegral (fun z : ℂ => f (z - rho)) l r b t =
      rectangleBoundaryIntegral f (l - rho.re) (r - rho.re)
        (b - rho.im) (t - rho.im) := by
  have hbottom :
      (∫ x : ℝ in l..r, f (((x : ℂ) + b * I) - rho)) =
        ∫ x : ℝ in l - rho.re..r - rho.re,
          f ((x : ℂ) + (b - rho.im) * I) := by
    have h := intervalIntegral.integral_comp_add_right
      (a := l - rho.re) (b := r - rho.re)
      (fun x : ℝ => f ((x - rho.re : ℝ) + (b - rho.im) * I)) rho.re
    have hshift :
        (∫ x : ℝ in l..r, f ((x - rho.re : ℝ) + (b - rho.im) * I)) =
          ∫ x : ℝ in l - rho.re..r - rho.re,
            f ((x : ℂ) + (b - rho.im) * I) := by
      simpa only [sub_add_cancel, add_sub_cancel_right, Complex.ofReal_add,
        Complex.ofReal_sub] using h.symm
    calc
      (∫ x : ℝ in l..r, f (((x : ℂ) + b * I) - rho)) =
          ∫ x : ℝ in l..r, f ((x - rho.re : ℝ) + (b - rho.im) * I) := by
        apply intervalIntegral.integral_congr
        intro x _
        apply congrArg f
        apply Complex.ext <;> simp
      _ = _ := hshift
  have htop :
      (∫ x : ℝ in l..r, f (((x : ℂ) + t * I) - rho)) =
        ∫ x : ℝ in l - rho.re..r - rho.re,
          f ((x : ℂ) + (t - rho.im) * I) := by
    have h := intervalIntegral.integral_comp_add_right
      (a := l - rho.re) (b := r - rho.re)
      (fun x : ℝ => f ((x - rho.re : ℝ) + (t - rho.im) * I)) rho.re
    have hshift :
        (∫ x : ℝ in l..r, f ((x - rho.re : ℝ) + (t - rho.im) * I)) =
          ∫ x : ℝ in l - rho.re..r - rho.re,
            f ((x : ℂ) + (t - rho.im) * I) := by
      simpa only [sub_add_cancel, add_sub_cancel_right, Complex.ofReal_add,
        Complex.ofReal_sub] using h.symm
    calc
      (∫ x : ℝ in l..r, f (((x : ℂ) + t * I) - rho)) =
          ∫ x : ℝ in l..r, f ((x - rho.re : ℝ) + (t - rho.im) * I) := by
        apply intervalIntegral.integral_congr
        intro x _
        apply congrArg f
        apply Complex.ext <;> simp
      _ = _ := hshift
  have hright :
      (∫ y : ℝ in b..t, f (((r : ℂ) + y * I) - rho)) =
        ∫ y : ℝ in b - rho.im..t - rho.im,
          f ((r - rho.re : ℝ) + y * I) := by
    have h := intervalIntegral.integral_comp_add_right
      (a := b - rho.im) (b := t - rho.im)
      (fun y : ℝ => f ((r - rho.re : ℝ) + (y - rho.im) * I)) rho.im
    have hshift :
        (∫ y : ℝ in b..t, f ((r - rho.re : ℝ) + (y - rho.im) * I)) =
          ∫ y : ℝ in b - rho.im..t - rho.im,
            f ((r - rho.re : ℝ) + y * I) := by
      simpa only [sub_add_cancel, add_sub_cancel_right, Complex.ofReal_add,
        Complex.ofReal_sub] using h.symm
    calc
      (∫ y : ℝ in b..t, f (((r : ℂ) + y * I) - rho)) =
          ∫ y : ℝ in b..t, f ((r - rho.re : ℝ) + (y - rho.im) * I) := by
        apply intervalIntegral.integral_congr
        intro y _
        apply congrArg f
        apply Complex.ext <;> simp
      _ = _ := hshift
  have hleft :
      (∫ y : ℝ in b..t, f (((l : ℂ) + y * I) - rho)) =
        ∫ y : ℝ in b - rho.im..t - rho.im,
          f ((l - rho.re : ℝ) + y * I) := by
    have h := intervalIntegral.integral_comp_add_right
      (a := b - rho.im) (b := t - rho.im)
      (fun y : ℝ => f ((l - rho.re : ℝ) + (y - rho.im) * I)) rho.im
    have hshift :
        (∫ y : ℝ in b..t, f ((l - rho.re : ℝ) + (y - rho.im) * I)) =
          ∫ y : ℝ in b - rho.im..t - rho.im,
            f ((l - rho.re : ℝ) + y * I) := by
      simpa only [sub_add_cancel, add_sub_cancel_right, Complex.ofReal_add,
        Complex.ofReal_sub] using h.symm
    calc
      (∫ y : ℝ in b..t, f (((l : ℂ) + y * I) - rho)) =
          ∫ y : ℝ in b..t, f ((l - rho.re : ℝ) + (y - rho.im) * I) := by
        apply intervalIntegral.integral_congr
        intro y _
        apply congrArg f
        apply Complex.ext <;> simp
      _ = _ := hshift
  unfold rectangleBoundaryIntegral
  rw [hbottom, htop, hright, hleft]
  simp only [Complex.ofReal_sub]

/-- The reciprocal kernel has the expected positive integral around any rectangle containing its
pole strictly in the interior. -/
theorem rectangleBoundaryIntegral_inv_sub_eq_two_pi_mul_I
    {rho : ℂ} {l r b t : ℝ}
    (hl : l < rho.re) (hr : rho.re < r)
    (hb : b < rho.im) (ht : rho.im < t) :
    rectangleBoundaryIntegral (fun z : ℂ => (z - rho)⁻¹) l r b t =
      2 * (Real.pi : ℂ) * I := by
  let b₀ : ℝ := rho.im - 1
  let t₀ : ℝ := rho.im + 1
  have hlne : l ≠ rho.re := ne_of_lt hl
  have hrne : r ≠ rho.re := ne_of_gt hr
  have hright_b : IntervalIntegrable
      (fun y : ℝ => (((r : ℂ) + y * I) - rho)⁻¹) volume b b₀ :=
    intervalIntegrable_inv_sub_const_vertical hrne
  have hright_b' : IntervalIntegrable
      (fun y : ℝ => (((r : ℂ) + y * I) - rho)⁻¹) volume b₀ t :=
    intervalIntegrable_inv_sub_const_vertical hrne
  have hleft_b : IntervalIntegrable
      (fun y : ℝ => (((l : ℂ) + y * I) - rho)⁻¹) volume b b₀ :=
    intervalIntegrable_inv_sub_const_vertical hlne
  have hleft_b' : IntervalIntegrable
      (fun y : ℝ => (((l : ℂ) + y * I) - rho)⁻¹) volume b₀ t :=
    intervalIntegrable_inv_sub_const_vertical hlne
  have hadd_bottom := rectangleBoundaryIntegral_vertical_add
    (f := fun z : ℂ => (z - rho)⁻¹) (l := l) (r := r) (b := b) (m := b₀) (t := t)
      hright_b hright_b' hleft_b hleft_b'
  have him_bottom : rho.im ∉ [[b, b₀]] := by
    simp only [Set.mem_uIcc, not_or]
    constructor <;> intro h <;> dsimp only [b₀] at h <;> linarith
  have hzero_bottom := rectangleBoundaryIntegral_inv_sub_eq_zero_of_im_notMem
    (rho := rho) (l := l) (r := r) him_bottom
  rw [hzero_bottom, zero_add] at hadd_bottom
  have hright_t : IntervalIntegrable
      (fun y : ℝ => (((r : ℂ) + y * I) - rho)⁻¹) volume b₀ t₀ :=
    intervalIntegrable_inv_sub_const_vertical hrne
  have hright_t' : IntervalIntegrable
      (fun y : ℝ => (((r : ℂ) + y * I) - rho)⁻¹) volume t₀ t :=
    intervalIntegrable_inv_sub_const_vertical hrne
  have hleft_t : IntervalIntegrable
      (fun y : ℝ => (((l : ℂ) + y * I) - rho)⁻¹) volume b₀ t₀ :=
    intervalIntegrable_inv_sub_const_vertical hlne
  have hleft_t' : IntervalIntegrable
      (fun y : ℝ => (((l : ℂ) + y * I) - rho)⁻¹) volume t₀ t :=
    intervalIntegrable_inv_sub_const_vertical hlne
  have hadd_top := rectangleBoundaryIntegral_vertical_add
    (f := fun z : ℂ => (z - rho)⁻¹) (l := l) (r := r) (b := b₀) (m := t₀) (t := t)
      hright_t hright_t' hleft_t hleft_t'
  have him_top : rho.im ∉ [[t₀, t]] := by
    simp only [Set.mem_uIcc, not_or]
    constructor <;> intro h <;> dsimp only [t₀] at h <;> linarith
  have hzero_top := rectangleBoundaryIntegral_inv_sub_eq_zero_of_im_notMem
    (rho := rho) (l := l) (r := r) him_top
  rw [hzero_top, add_zero] at hadd_top
  have htranslated := rectangleBoundaryIntegral_comp_sub (fun z : ℂ => z⁻¹)
    rho l r b₀ t₀
  have hinv := integral_inv_boundary_rect_eq_two_pi_mul_I
    (l := l - rho.re) (R := r - rho.re) (T := (1 : ℝ)) (by linarith) (by linarith)
      (by norm_num)
  have hsymmetric :
      rectangleBoundaryIntegral (fun z : ℂ => (z - rho)⁻¹) l r b₀ t₀ =
        2 * (Real.pi : ℂ) * I := by
    rw [htranslated]
    convert hinv using 1; norm_num [b₀, t₀, rectangleBoundaryIntegral]
  rw [← hadd_bottom, ← hadd_top]
  exact hsymmetric

/-- Rectangle boundary integration is additive for edgewise interval-integrable functions. -/
theorem rectangleBoundaryIntegral_add
    {f g : ℂ → ℂ} {l r b t : ℝ}
    (hfb : IntervalIntegrable (fun x : ℝ => f (x + b * I)) volume l r)
    (hgb : IntervalIntegrable (fun x : ℝ => g (x + b * I)) volume l r)
    (hft : IntervalIntegrable (fun x : ℝ => f (x + t * I)) volume l r)
    (hgt : IntervalIntegrable (fun x : ℝ => g (x + t * I)) volume l r)
    (hfr : IntervalIntegrable (fun y : ℝ => f (r + y * I)) volume b t)
    (hgr : IntervalIntegrable (fun y : ℝ => g (r + y * I)) volume b t)
    (hfl : IntervalIntegrable (fun y : ℝ => f (l + y * I)) volume b t)
    (hgl : IntervalIntegrable (fun y : ℝ => g (l + y * I)) volume b t) :
    rectangleBoundaryIntegral (fun z => f z + g z) l r b t =
      rectangleBoundaryIntegral f l r b t + rectangleBoundaryIntegral g l r b t := by
  unfold rectangleBoundaryIntegral
  rw [intervalIntegral.integral_add hfb hgb, intervalIntegral.integral_add hft hgt,
    intervalIntegral.integral_add hfr hgr, intervalIntegral.integral_add hfl hgl]
  ring

/-- Constants pull out of the rectangle boundary integral. -/
theorem rectangleBoundaryIntegral_const_mul
    (c : ℂ) (f : ℂ → ℂ) (l r b t : ℝ) :
    rectangleBoundaryIntegral (fun z => c * f z) l r b t =
      c * rectangleBoundaryIntegral f l r b t := by
  unfold rectangleBoundaryIntegral
  simp only [intervalIntegral.integral_const_mul]
  ring

/-- A reciprocal translated off a horizontal boundary line is interval integrable there. -/
theorem intervalIntegrable_inv_sub_const_horizontal
    {rho : ℂ} {c p q : ℝ} (hc : c ≠ rho.im) :
    IntervalIntegrable
      (fun x : ℝ => (((x : ℂ) + c * I) - rho)⁻¹) volume p q := by
  apply Continuous.intervalIntegrable
  apply Continuous.inv₀
  · fun_prop
  · intro x hzero
    have him := congrArg Complex.im hzero
    simp only [sub_im, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero,
      mul_one, zero_add, Complex.zero_im] at him
    apply hc
    linarith

/-- The pole-subtracted weighted Cauchy kernel, extended at the pole by the derivative of the
weight. -/
def weightedCauchyRemovable (F : ℂ → ℂ) (rho : ℂ) : ℂ → ℂ :=
  dslope F rho

/-- Away from its pole, a weighted Cauchy kernel is its residue kernel plus the removable part. -/
theorem weightedCauchyKernel_eq_residue_add_removable
    {F : ℂ → ℂ} {rho z : ℂ} (hz : z ≠ rho) :
    F z / (z - rho) = F rho * (z - rho)⁻¹ + weightedCauchyRemovable F rho z := by
  have hden : z - rho ≠ 0 := sub_ne_zero.mpr hz
  have hs := sub_smul_dslope F rho z
  have hmul : (z - rho) * weightedCauchyRemovable F rho z = F z - F rho := by
    simpa only [weightedCauchyRemovable, smul_eq_mul] using hs
  field_simp [hden]
  rw [hmul]
  ring

/-- The removable part of a weighted Cauchy kernel is entire when the weight is entire. -/
theorem differentiable_weightedCauchyRemovable
    {F : ℂ → ℂ} (hF : Differentiable ℂ F) (rho : ℂ) :
    Differentiable ℂ (weightedCauchyRemovable F rho) := by
  rw [← differentiableOn_univ, weightedCauchyRemovable,
    Complex.differentiableOn_dslope (s := Set.univ) (c := rho) univ_mem]
  exact hF.differentiableOn

/-- A weighted simple pole contributes `2 * pi * I` times the weight at the pole. -/
theorem rectangleBoundaryIntegral_weighted_cauchyKernel
    {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {rho : ℂ} {l r b t : ℝ}
    (hl : l < rho.re) (hr : rho.re < r)
    (hb : b < rho.im) (ht : rho.im < t) :
    rectangleBoundaryIntegral (fun z => F z / (z - rho)) l r b t =
      2 * (Real.pi : ℂ) * I * F rho := by
  let K : ℂ → ℂ := fun z => F rho * (z - rho)⁻¹
  let G : ℂ → ℂ := weightedCauchyRemovable F rho
  have hlne : l ≠ rho.re := ne_of_lt hl
  have hrne : r ≠ rho.re := ne_of_gt hr
  have hbne : b ≠ rho.im := ne_of_lt hb
  have htne : t ≠ rho.im := ne_of_gt ht
  have hKb : IntervalIntegrable (fun x : ℝ => K (x + b * I)) volume l r :=
    (intervalIntegrable_inv_sub_const_horizontal hbne).const_mul _
  have hKt : IntervalIntegrable (fun x : ℝ => K (x + t * I)) volume l r :=
    (intervalIntegrable_inv_sub_const_horizontal htne).const_mul _
  have hKr : IntervalIntegrable (fun y : ℝ => K (r + y * I)) volume b t :=
    (intervalIntegrable_inv_sub_const_vertical hrne).const_mul _
  have hKl : IntervalIntegrable (fun y : ℝ => K (l + y * I)) volume b t :=
    (intervalIntegrable_inv_sub_const_vertical hlne).const_mul _
  have hGdiff : Differentiable ℂ G := differentiable_weightedCauchyRemovable hF rho
  have hGb : IntervalIntegrable (fun x : ℝ => G (x + b * I)) volume l r := by
    apply Continuous.intervalIntegrable
    exact hGdiff.continuous.comp (by fun_prop)
  have hGt : IntervalIntegrable (fun x : ℝ => G (x + t * I)) volume l r := by
    apply Continuous.intervalIntegrable
    exact hGdiff.continuous.comp (by fun_prop)
  have hGr : IntervalIntegrable (fun y : ℝ => G (r + y * I)) volume b t := by
    apply Continuous.intervalIntegrable
    exact hGdiff.continuous.comp (by fun_prop)
  have hGl : IntervalIntegrable (fun y : ℝ => G (l + y * I)) volume b t := by
    apply Continuous.intervalIntegrable
    exact hGdiff.continuous.comp (by fun_prop)
  have hbottom :
      (∫ x : ℝ in l..r, F (x + b * I) / (x + b * I - rho)) =
        ∫ x : ℝ in l..r, K (x + b * I) + G (x + b * I) := by
    apply intervalIntegral.integral_congr
    intro x _
    simpa only [K, G] using weightedCauchyKernel_eq_residue_add_removable (by
      intro h
      have him := congrArg Complex.im h
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero, mul_one,
        zero_add] at him
      apply hbne
      linarith)
  have htop :
      (∫ x : ℝ in l..r, F (x + t * I) / (x + t * I - rho)) =
        ∫ x : ℝ in l..r, K (x + t * I) + G (x + t * I) := by
    apply intervalIntegral.integral_congr
    intro x _
    simpa only [K, G] using weightedCauchyKernel_eq_residue_add_removable (by
      intro h
      have him := congrArg Complex.im h
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero, mul_one,
        zero_add] at him
      apply htne
      linarith)
  have hright :
      (∫ y : ℝ in b..t, F (r + y * I) / (r + y * I - rho)) =
        ∫ y : ℝ in b..t, K (r + y * I) + G (r + y * I) := by
    apply intervalIntegral.integral_congr
    intro y _
    simpa only [K, G] using weightedCauchyKernel_eq_residue_add_removable (by
      intro h
      have hre := congrArg Complex.re h
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one] at hre
      apply hrne
      linarith)
  have hleft :
      (∫ y : ℝ in b..t, F (l + y * I) / (l + y * I - rho)) =
        ∫ y : ℝ in b..t, K (l + y * I) + G (l + y * I) := by
    apply intervalIntegral.integral_congr
    intro y _
    simpa only [K, G] using weightedCauchyKernel_eq_residue_add_removable (by
      intro h
      have hre := congrArg Complex.re h
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one] at hre
      apply hlne
      linarith)
  have hdecomp :
      rectangleBoundaryIntegral (fun z => F z / (z - rho)) l r b t =
        rectangleBoundaryIntegral (fun z => K z + G z) l r b t := by
    unfold rectangleBoundaryIntegral
    rw [hbottom, htop, hright, hleft]
  have hadd := rectangleBoundaryIntegral_add hKb hGb hKt hGt hKr hGr hKl hGl
  have hGzero : rectangleBoundaryIntegral G l r b t = 0 :=
    rectangleBoundaryIntegral_eq_zero_of_differentiableOn hGdiff.differentiableOn
  have hK : rectangleBoundaryIntegral K l r b t =
      F rho * rectangleBoundaryIntegral (fun z : ℂ => (z - rho)⁻¹) l r b t := by
    exact rectangleBoundaryIntegral_const_mul (F rho) (fun z : ℂ => (z - rho)⁻¹) l r b t
  rw [hdecomp, hadd, hK, hGzero, add_zero,
    rectangleBoundaryIntegral_inv_sub_eq_two_pi_mul_I hl hr hb ht]
  ring

/-- A weighted Cauchy kernel is interval integrable along any continuous path segment that avoids
its pole. -/
theorem intervalIntegrable_weighted_cauchyKernel_of_avoids
    {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {phi : ℝ → ℂ} (hphi : Continuous phi) {a c : ℝ} {rho : ℂ}
    (havoid : ∀ x ∈ [[a, c]], phi x ≠ rho) :
    IntervalIntegrable (fun x : ℝ => F (phi x) / (phi x - rho)) volume a c := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.div
  · exact hF.continuous.continuousAt.comp hphi.continuousAt
  · fun_prop
  · exact sub_ne_zero.mpr (havoid x hx)

/-- A function differentiable on an open set is interval integrable along a continuous compact
path segment contained in that set. -/
theorem intervalIntegrable_comp_of_differentiableOn
    {U : Set ℂ} (hU : IsOpen U) {G : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G U)
    {phi : ℝ → ℂ} (hphi : Continuous phi) {a c : ℝ}
    (hmap : MapsTo phi [[a, c]] U) :
    IntervalIntegrable (fun x : ℝ => G (phi x)) volume a c := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  apply ContinuousAt.continuousWithinAt
  have hGat : DifferentiableAt ℂ G (phi x) :=
    (hG (phi x) (hmap hx)).differentiableAt (hU.mem_nhds (hmap hx))
  exact hGat.continuousAt.comp hphi.continuousAt

/-- A weighted Cauchy kernel has zero rectangle integral when its pole lies outside the closed
rectangle in at least one coordinate. -/
theorem rectangleBoundaryIntegral_weighted_cauchyKernel_eq_zero_of_outside
    {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {rho : ℂ} {l r b t : ℝ}
    (hout : rho.re ∉ [[l, r]] ∨ rho.im ∉ [[b, t]]) :
    rectangleBoundaryIntegral (fun z => F z / (z - rho)) l r b t = 0 := by
  apply rectangleBoundaryIntegral_eq_zero_of_differentiableOn
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.div
  · exact hF z
  · fun_prop
  · intro hzero
    have hzrho : z = rho := sub_eq_zero.mp hzero
    rcases hout with hre | him
    · exact hre (hzrho ▸ hz.1)
    · exact him (hzrho ▸ hz.2)

/-- A point avoids xi's zero set exactly when it avoids every multiplicity-bearing divisor
index value. -/
theorem mem_riemannXiNonzeroSet_iff_forall_ne_zeroValue (z : ℂ) :
    z ∈ riemannXiNonzeroSet ↔
      ∀ p : RiemannXiDivisorZeroIndex, z ≠ riemannXiDivisorZeroValue p := by
  constructor
  · exact fun hz p => ne_riemannXiDivisorZeroValue_of_mem_nonzeroSet hz p
  · intro hz
    rw [riemannXiNonzeroSet]
    intro hzero
    have hnontrivial : IsNontrivialZero z :=
      (isNontrivialZero_iff_riemannXi_eq_zero z).2 hzero
    obtain ⟨p, hp⟩ := exists_riemannXiDivisorZeroIndex_of_isNontrivialZero hnontrivial
    exact hz p hp.symm

/-- On any continuous compact edge contained in the xi nonzero set, interval integration commutes
with the entire-weighted compensated xi zero sum. -/
theorem hasSum_intervalIntegral_weighted_riemannXiLogDerivZeroTerm
    {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {phi : ℝ → ℂ} (hphi : Continuous phi) {a c : ℝ}
    (hmap : MapsTo phi [[a, c]] riemannXiNonzeroSet) :
    HasSum
      (fun p : RiemannXiDivisorZeroIndex =>
        ∫ x : ℝ in a..c, F (phi x) * riemannXiLogDerivZeroTerm p (phi x))
      (∫ x : ℝ in a..c,
        F (phi x) *
          ∑' p : RiemannXiDivisorZeroIndex,
            riemannXiLogDerivZeroTerm p (phi x)) := by
  letI : Countable RiemannXiDivisorZeroIndex := countable_riemannXiDivisorZeroIndex
  let S : ℂ → ℂ := fun z =>
    ∑' p : RiemannXiDivisorZeroIndex, riemannXiLogDerivZeroTerm p z
  have hsumLocal : HasSumLocallyUniformlyOn
      (fun p : RiemannXiDivisorZeroIndex => riemannXiLogDerivZeroTerm p)
      S riemannXiNonzeroSet := by
    exact summableLocallyUniformlyOn_riemannXiLogDerivZeroTerm.hasSumLocallyUniformlyOn
  have hsumComp : HasSumLocallyUniformlyOn
      (fun p : RiemannXiDivisorZeroIndex => fun x =>
        riemannXiLogDerivZeroTerm p (phi x))
      (S ∘ phi) [[a, c]] :=
    hsumLocal.comp phi hmap hphi.continuousOn
  have hsumUniform : TendstoUniformlyOn
      (fun s : Finset RiemannXiDivisorZeroIndex => fun x =>
        ∑ p ∈ s, riemannXiLogDerivZeroTerm p (phi x))
      (S ∘ phi) Filter.atTop [[a, c]] :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact isCompact_uIcc).mp hsumComp
  obtain ⟨C, hC⟩ := isCompact_uIcc.exists_bound_of_continuousOn
    (hF.continuous.comp hphi).continuousOn
  let M : ℝ := max C 1
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  have hFM : ∀ x ∈ [[a, c]], ‖F (phi x)‖ ≤ M := fun x hx =>
    (hC x hx).trans (le_max_left _ _)
  have hweighted : TendstoUniformlyOn
      (fun s : Finset RiemannXiDivisorZeroIndex => fun x =>
        ∑ p ∈ s, F (phi x) * riemannXiLogDerivZeroTerm p (phi x))
      (fun x => F (phi x) * S (phi x)) Filter.atTop [[a, c]] := by
    rw [tendstoUniformlyOn_iff] at hsumUniform ⊢
    intro epsilon hepsilon
    have hepsilonM : 0 < epsilon / M := div_pos hepsilon hMpos
    filter_upwards [hsumUniform (epsilon / M) hepsilonM] with s hs
    intro x hx
    have hsx := hs x hx
    simp only [Function.comp_apply, dist_eq_norm] at hsx ⊢
    rw [← Finset.mul_sum, ← mul_sub, norm_mul]
    calc
      ‖F (phi x)‖ *
          ‖S (phi x) - ∑ p ∈ s, riemannXiLogDerivZeroTerm p (phi x)‖
          ≤ M * ‖S (phi x) -
            ∑ p ∈ s, riemannXiLogDerivZeroTerm p (phi x)‖ := by
        gcongr
        exact hFM x hx
      _ < M * (epsilon / M) := by gcongr
      _ = epsilon := by field_simp [hMpos.ne']
  have htermContinuous (p : RiemannXiDivisorZeroIndex) :
      ContinuousOn
        (fun x : ℝ => F (phi x) * riemannXiLogDerivZeroTerm p (phi x)) [[a, c]] := by
    intro x hx
    have hxnonzero : phi x ∈ riemannXiNonzeroSet := hmap hx
    have hxne : phi x ≠ riemannXiDivisorZeroValue p :=
      ne_riemannXiDivisorZeroValue_of_mem_nonzeroSet hxnonzero p
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.mul
    · exact hF.continuous.continuousAt.comp hphi.continuousAt
    · have hzeroContinuousAt :
          ContinuousAt (riemannXiLogDerivZeroTerm p) (phi x) := by
        unfold riemannXiLogDerivZeroTerm
        apply ContinuousAt.add
        · apply ContinuousAt.div
          · fun_prop
          · fun_prop
          · exact sub_ne_zero.mpr hxne
        · fun_prop
      simpa only [Function.comp_def] using
        hzeroContinuousAt.comp hphi.continuousAt
  have hpartialContinuous :
      ∀ s : Finset RiemannXiDivisorZeroIndex,
        ContinuousOn
          (fun x : ℝ => ∑ p ∈ s,
            F (phi x) * riemannXiLogDerivZeroTerm p (phi x)) [[a, c]] := by
    intro s
    exact continuousOn_finsetSum s fun p _ => htermContinuous p
  have hlimit : Tendsto
      (fun s : Finset RiemannXiDivisorZeroIndex =>
        ∫ x : ℝ in a..c,
          ∑ p ∈ s, F (phi x) * riemannXiLogDerivZeroTerm p (phi x))
      Filter.atTop
      (𝓝 (∫ x : ℝ in a..c, F (phi x) * S (phi x))) :=
    hweighted.tendsto_intervalIntegral_of_continuousOn
      (Filter.Eventually.of_forall hpartialContinuous)
  have hintegralSum :
      (fun s : Finset RiemannXiDivisorZeroIndex =>
        ∫ x : ℝ in a..c,
          ∑ p ∈ s, F (phi x) * riemannXiLogDerivZeroTerm p (phi x)) =
      fun s : Finset RiemannXiDivisorZeroIndex =>
        ∑ p ∈ s,
          ∫ x : ℝ in a..c, F (phi x) * riemannXiLogDerivZeroTerm p (phi x) := by
    funext s
    rw [intervalIntegral.integral_finsetSum]
    intro p _
    exact (htermContinuous p).intervalIntegrable
  change Tendsto
    (fun s : Finset RiemannXiDivisorZeroIndex =>
      ∑ p ∈ s,
        ∫ x : ℝ in a..c, F (phi x) * riemannXiLogDerivZeroTerm p (phi x))
    Filter.atTop
    (𝓝 (∫ x : ℝ in a..c,
      F (phi x) * ∑' p : RiemannXiDivisorZeroIndex,
        riemannXiLogDerivZeroTerm p (phi x)))
  rw [← hintegralSum]
  exact hlimit

/-- If a rectangle boundary contains no xi zero, all four edge parameterizations map into the xi
nonzero set. -/
theorem mapsTo_riemannXiNonzeroSet_rectangle_edges
    {l r b t : ℝ} (hlr : l < r) (hbt : b < t)
    (hboundary : ∀ p : RiemannXiDivisorZeroIndex,
      ¬riemannXiZeroOnRectangleBoundary l r b t p) :
    MapsTo (fun x : ℝ => (x : ℂ) + b * I) [[l, r]] riemannXiNonzeroSet ∧
      MapsTo (fun x : ℝ => (x : ℂ) + t * I) [[l, r]] riemannXiNonzeroSet ∧
      MapsTo (fun y : ℝ => (r : ℂ) + y * I) [[b, t]] riemannXiNonzeroSet ∧
      MapsTo (fun y : ℝ => (l : ℂ) + y * I) [[b, t]] riemannXiNonzeroSet := by
  constructor
  · intro x hx
    rw [mem_riemannXiNonzeroSet_iff_forall_ne_zeroValue]
    intro p heq
    have hre := congrArg Complex.re heq
    have him := congrArg Complex.im heq
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one] at hre
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero, mul_one,
      zero_add] at him
    rw [uIcc_of_le hlr.le] at hx
    exact (hboundary p) (by
      unfold riemannXiZeroOnRectangleBoundary
      left
      constructor
      · linarith
      · constructor <;> linarith [hx.1, hx.2])
  · constructor
    · intro x hx
      rw [mem_riemannXiNonzeroSet_iff_forall_ne_zeroValue]
      intro p heq
      have hre := congrArg Complex.re heq
      have him := congrArg Complex.im heq
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one] at hre
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero, mul_one,
        zero_add] at him
      rw [uIcc_of_le hlr.le] at hx
      exact (hboundary p) (by
        unfold riemannXiZeroOnRectangleBoundary
        right
        left
        constructor
        · linarith
        · constructor <;> linarith [hx.1, hx.2])
    · constructor
      · intro y hy
        rw [mem_riemannXiNonzeroSet_iff_forall_ne_zeroValue]
        intro p heq
        have hre := congrArg Complex.re heq
        have him := congrArg Complex.im heq
        simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one] at hre
        simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero, mul_one,
          zero_add] at him
        rw [uIcc_of_le hbt.le] at hy
        exact (hboundary p) (by
          unfold riemannXiZeroOnRectangleBoundary
          right
          right
          right
          constructor
          · linarith
          · constructor <;> linarith [hy.1, hy.2])
      · intro y hy
        rw [mem_riemannXiNonzeroSet_iff_forall_ne_zeroValue]
        intro p heq
        have hre := congrArg Complex.re heq
        have him := congrArg Complex.im heq
        simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one] at hre
        simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero, mul_one,
          zero_add] at him
        rw [uIcc_of_le hbt.le] at hy
        exact (hboundary p) (by
          unfold riemannXiZeroOnRectangleBoundary
          right
          right
          left
          constructor
          · linarith
          · constructor <;> linarith [hy.1, hy.2])

/-- Rectangle boundary integration commutes with the entire-weighted compensated xi zero sum when
the boundary contains no xi zero. -/
theorem hasSum_rectangleBoundaryIntegral_weighted_riemannXiLogDerivZeroTerm
    {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {l r b t : ℝ} (hlr : l < r) (hbt : b < t)
    (hboundary : ∀ p : RiemannXiDivisorZeroIndex,
      ¬riemannXiZeroOnRectangleBoundary l r b t p) :
    HasSum
      (fun p : RiemannXiDivisorZeroIndex =>
        rectangleBoundaryIntegral
          (fun z => F z * riemannXiLogDerivZeroTerm p z) l r b t)
      (rectangleBoundaryIntegral
        (fun z => F z *
          ∑' p : RiemannXiDivisorZeroIndex, riemannXiLogDerivZeroTerm p z)
        l r b t) := by
  obtain ⟨hbottomMap, htopMap, hrightMap, hleftMap⟩ :=
    mapsTo_riemannXiNonzeroSet_rectangle_edges hlr hbt hboundary
  have hbottom := hasSum_intervalIntegral_weighted_riemannXiLogDerivZeroTerm
    hF (phi := fun x : ℝ => (x : ℂ) + b * I) (by fun_prop) hbottomMap
  have htop := hasSum_intervalIntegral_weighted_riemannXiLogDerivZeroTerm
    hF (phi := fun x : ℝ => (x : ℂ) + t * I) (by fun_prop) htopMap
  have hright := hasSum_intervalIntegral_weighted_riemannXiLogDerivZeroTerm
    hF (phi := fun y : ℝ => (r : ℂ) + y * I) (by fun_prop) hrightMap
  have hleft := hasSum_intervalIntegral_weighted_riemannXiLogDerivZeroTerm
    hF (phi := fun y : ℝ => (l : ℂ) + y * I) (by fun_prop) hleftMap
  have hcombined := (hbottom.sub htop).add
    ((hright.mul_left I).sub (hleft.mul_left I))
  have hterm : ∀ p : RiemannXiDivisorZeroIndex,
      rectangleBoundaryIntegral
          (fun z => F z * riemannXiLogDerivZeroTerm p z) l r b t =
        ((∫ x : ℝ in l..r,
            F (x + b * I) * riemannXiLogDerivZeroTerm p (x + b * I)) -
          (∫ x : ℝ in l..r,
            F (x + t * I) * riemannXiLogDerivZeroTerm p (x + t * I))) +
        ((I * ∫ y : ℝ in b..t,
            F (r + y * I) * riemannXiLogDerivZeroTerm p (r + y * I)) -
          (I * ∫ y : ℝ in b..t,
            F (l + y * I) * riemannXiLogDerivZeroTerm p (l + y * I))) := by
    intro p
    unfold rectangleBoundaryIntegral
    ring
  have hlimit :
      rectangleBoundaryIntegral
          (fun z => F z *
            ∑' p : RiemannXiDivisorZeroIndex, riemannXiLogDerivZeroTerm p z)
          l r b t =
        ((∫ x : ℝ in l..r,
            F (x + b * I) *
              ∑' p : RiemannXiDivisorZeroIndex,
                riemannXiLogDerivZeroTerm p (x + b * I)) -
          (∫ x : ℝ in l..r,
            F (x + t * I) *
              ∑' p : RiemannXiDivisorZeroIndex,
                riemannXiLogDerivZeroTerm p (x + t * I))) +
        ((I * ∫ y : ℝ in b..t,
            F (r + y * I) *
              ∑' p : RiemannXiDivisorZeroIndex,
                riemannXiLogDerivZeroTerm p (r + y * I)) -
          (I * ∫ y : ℝ in b..t,
            F (l + y * I) *
              ∑' p : RiemannXiDivisorZeroIndex,
                riemannXiLogDerivZeroTerm p (l + y * I))) := by
    unfold rectangleBoundaryIntegral
    ring
  rw [hlimit]
  exact HasSum.congr_fun hcombined hterm

/-- Under a zero-free rectangle boundary, one entire-weighted compensated xi zero term contributes
its residue exactly when that multiplicity-bearing zero lies strictly inside. -/
theorem rectangleBoundaryIntegral_weighted_riemannXiLogDerivZeroTerm
    {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {l r b t : ℝ} (hlr : l < r) (hbt : b < t)
    (hboundary : ∀ q : RiemannXiDivisorZeroIndex,
      ¬riemannXiZeroOnRectangleBoundary l r b t q)
    (p : RiemannXiDivisorZeroIndex) :
    rectangleBoundaryIntegral
        (fun z => F z * riemannXiLogDerivZeroTerm p z) l r b t =
      if riemannXiZeroStrictlyInsideRectangle l r b t p then
        2 * (Real.pi : ℂ) * I * F (riemannXiDivisorZeroValue p)
      else 0 := by
  classical
  let rho : ℂ := riemannXiDivisorZeroValue p
  let K : ℂ → ℂ := fun z => F z / (z - rho)
  let G : ℂ → ℂ := fun z => F z * rho⁻¹
  obtain ⟨hbottomMap, htopMap, hrightMap, hleftMap⟩ :=
    mapsTo_riemannXiNonzeroSet_rectangle_edges hlr hbt hboundary
  have hKb : IntervalIntegrable (fun x : ℝ => K (x + b * I)) volume l r := by
    apply intervalIntegrable_weighted_cauchyKernel_of_avoids hF (by fun_prop)
    intro x hx
    simpa only [rho] using
      ne_riemannXiDivisorZeroValue_of_mem_nonzeroSet (hbottomMap hx) p
  have hKt : IntervalIntegrable (fun x : ℝ => K (x + t * I)) volume l r := by
    apply intervalIntegrable_weighted_cauchyKernel_of_avoids hF (by fun_prop)
    intro x hx
    simpa only [rho] using
      ne_riemannXiDivisorZeroValue_of_mem_nonzeroSet (htopMap hx) p
  have hKr : IntervalIntegrable (fun y : ℝ => K (r + y * I)) volume b t := by
    apply intervalIntegrable_weighted_cauchyKernel_of_avoids hF (by fun_prop)
    intro y hy
    simpa only [rho] using
      ne_riemannXiDivisorZeroValue_of_mem_nonzeroSet (hrightMap hy) p
  have hKl : IntervalIntegrable (fun y : ℝ => K (l + y * I)) volume b t := by
    apply intervalIntegrable_weighted_cauchyKernel_of_avoids hF (by fun_prop)
    intro y hy
    simpa only [rho] using
      ne_riemannXiDivisorZeroValue_of_mem_nonzeroSet (hleftMap hy) p
  have hGdiff : Differentiable ℂ G := by
    dsimp only [G]
    fun_prop
  have hGb : IntervalIntegrable (fun x : ℝ => G (x + b * I)) volume l r := by
    apply Continuous.intervalIntegrable
    exact hGdiff.continuous.comp (by fun_prop)
  have hGt : IntervalIntegrable (fun x : ℝ => G (x + t * I)) volume l r := by
    apply Continuous.intervalIntegrable
    exact hGdiff.continuous.comp (by fun_prop)
  have hGr : IntervalIntegrable (fun y : ℝ => G (r + y * I)) volume b t := by
    apply Continuous.intervalIntegrable
    exact hGdiff.continuous.comp (by fun_prop)
  have hGl : IntervalIntegrable (fun y : ℝ => G (l + y * I)) volume b t := by
    apply Continuous.intervalIntegrable
    exact hGdiff.continuous.comp (by fun_prop)
  have hdecomp :
      (fun z => F z * riemannXiLogDerivZeroTerm p z) = fun z => K z + G z := by
    funext z
    simp only [riemannXiLogDerivZeroTerm, K, G, rho, div_eq_mul_inv, mul_add, one_mul]
  have hadd := rectangleBoundaryIntegral_add hKb hGb hKt hGt hKr hGr hKl hGl
  have hGzero : rectangleBoundaryIntegral G l r b t = 0 :=
    rectangleBoundaryIntegral_eq_zero_of_differentiableOn hGdiff.differentiableOn
  rw [hdecomp, hadd, hGzero, add_zero]
  by_cases hins : riemannXiZeroStrictlyInsideRectangle l r b t p
  · rw [if_pos hins]
    simpa only [K, rho] using rectangleBoundaryIntegral_weighted_cauchyKernel hF
      hins.1 hins.2.1 hins.2.2.1 hins.2.2.2
  · rw [if_neg hins]
    apply rectangleBoundaryIntegral_weighted_cauchyKernel_eq_zero_of_outside hF
    by_cases hre : rho.re ∈ [[l, r]]
    · by_cases him : rho.im ∈ [[b, t]]
      · rw [uIcc_of_le hlr.le] at hre
        rw [uIcc_of_le hbt.le] at him
        have hrel : rho.re ≠ l := by
          intro heq
          exact (hboundary p) (by
            unfold riemannXiZeroOnRectangleBoundary
            right
            right
            left
            simpa only [rho] using And.intro heq (And.intro him.1 him.2))
        have hrer : rho.re ≠ r := by
          intro heq
          exact (hboundary p) (by
            unfold riemannXiZeroOnRectangleBoundary
            right
            right
            right
            simpa only [rho] using And.intro heq (And.intro him.1 him.2))
        have himb : rho.im ≠ b := by
          intro heq
          exact (hboundary p) (by
            unfold riemannXiZeroOnRectangleBoundary
            left
            simpa only [rho] using And.intro heq (And.intro hre.1 hre.2))
        have himt : rho.im ≠ t := by
          intro heq
          exact (hboundary p) (by
            unfold riemannXiZeroOnRectangleBoundary
            right
            left
            simpa only [rho] using And.intro heq (And.intro hre.1 hre.2))
        exfalso
        apply hins
        unfold riemannXiZeroStrictlyInsideRectangle
        dsimp only [rho] at hre him hrel hrer himb himt ⊢
        constructor
        · exact lt_of_le_of_ne hre.1 (Ne.symm hrel)
        · constructor
          · exact lt_of_le_of_ne hre.2 hrer
          · constructor
            · exact lt_of_le_of_ne him.1 (Ne.symm himb)
            · exact lt_of_le_of_ne him.2 himt
      · exact Or.inr him
    · exact Or.inl hre

/-- The entire-weighted compensated xi zero sum has the finite multiplicity-bearing interior-zero
residue formula on a zero-free rectangle boundary. -/
theorem rectangleBoundaryIntegral_weighted_riemannXiZeroSum_eq_finsum
    {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {l r b t : ℝ} (hlr : l < r) (hbt : b < t)
    (hboundary : ∀ p : RiemannXiDivisorZeroIndex,
      ¬riemannXiZeroOnRectangleBoundary l r b t p) :
    rectangleBoundaryIntegral
        (fun z => F z *
          ∑' p : RiemannXiDivisorZeroIndex, riemannXiLogDerivZeroTerm p z)
        l r b t =
      2 * (Real.pi : ℂ) * I *
        ∑ᶠ p : RiemannXiDivisorZeroIndex,
          if riemannXiZeroStrictlyInsideRectangle l r b t p then
            F (riemannXiDivisorZeroValue p)
          else 0 := by
  have hsum := hasSum_rectangleBoundaryIntegral_weighted_riemannXiLogDerivZeroTerm
    hF hlr hbt hboundary
  have hpoint : ∀ p : RiemannXiDivisorZeroIndex,
      2 * (Real.pi : ℂ) * I *
          (if riemannXiZeroStrictlyInsideRectangle l r b t p then
            F (riemannXiDivisorZeroValue p)
          else 0) =
        rectangleBoundaryIntegral
          (fun z => F z * riemannXiLogDerivZeroTerm p z) l r b t := by
    intro p
    rw [rectangleBoundaryIntegral_weighted_riemannXiLogDerivZeroTerm
      hF hlr hbt hboundary p]
    by_cases hins : riemannXiZeroStrictlyInsideRectangle l r b t p
    · simp only [if_pos hins]
    · simp only [if_neg hins, mul_zero]
  have hsumResidues : HasSum
      (fun p : RiemannXiDivisorZeroIndex =>
        2 * (Real.pi : ℂ) * I *
          (if riemannXiZeroStrictlyInsideRectangle l r b t p then
            F (riemannXiDivisorZeroValue p)
          else 0))
      (rectangleBoundaryIntegral
        (fun z => F z *
          ∑' p : RiemannXiDivisorZeroIndex, riemannXiLogDerivZeroTerm p z)
        l r b t) :=
    HasSum.congr_fun hsum hpoint
  have hfinite : Function.HasFiniteSupport
      (fun p : RiemannXiDivisorZeroIndex =>
        if riemannXiZeroStrictlyInsideRectangle l r b t p then
          F (riemannXiDivisorZeroValue p)
        else 0) := by
    apply (finite_riemannXiZeroStrictlyInsideRectangle l r b t).subset
    intro p hp
    simp only [Function.mem_support] at hp
    by_contra hout
    have hout' : ¬riemannXiZeroStrictlyInsideRectangle l r b t p := by
      simpa only [Set.mem_setOf_eq] using hout
    exact hp (if_neg hout')
  have htsum := hsumResidues.tsum_eq
  rw [tsum_mul_left, tsum_eq_finsum hfinite] at htsum
  exact htsum.symm

/-- Finite-height weighted argument principle for Riemann's xi function, with analytic
multiplicity retained by the divisor index. -/
theorem rectangleBoundaryIntegral_weighted_logDeriv_riemannXi_eq_finsum
    {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {l r b t : ℝ} (hlr : l < r) (hbt : b < t)
    (hboundary : ∀ p : RiemannXiDivisorZeroIndex,
      ¬riemannXiZeroOnRectangleBoundary l r b t p) :
    rectangleBoundaryIntegral (fun z => F z * logDeriv riemannXi z) l r b t =
      2 * (Real.pi : ℂ) * I *
        ∑ᶠ p : RiemannXiDivisorZeroIndex,
          if riemannXiZeroStrictlyInsideRectangle l r b t p then
            F (riemannXiDivisorZeroValue p)
          else 0 := by
  obtain ⟨P, _hdegree, hfac⟩ := exists_riemannXi_hadamard_factorization
  let Q : ℂ → ℂ := fun z => Polynomial.eval z P.derivative
  let S : ℂ → ℂ := fun z =>
    ∑' p : RiemannXiDivisorZeroIndex, riemannXiLogDerivZeroTerm p z
  let H : ℂ → ℂ := fun z => F z * Q z
  let Z : ℂ → ℂ := fun z => F z * S z
  have hQdiff : Differentiable ℂ Q := by
    dsimp only [Q]
    exact P.derivative.differentiable
  have hSdiff : DifferentiableOn ℂ S riemannXiNonzeroSet := by
    dsimp only [S]
    apply SummableLocallyUniformlyOn.differentiableOn isOpen_riemannXiNonzeroSet
      summableLocallyUniformlyOn_riemannXiLogDerivZeroTerm
    intro p z hz
    unfold riemannXiLogDerivZeroTerm
    apply DifferentiableAt.add
    · apply DifferentiableAt.div
      · fun_prop
      · fun_prop
      · exact sub_ne_zero.mpr
          (ne_riemannXiDivisorZeroValue_of_mem_nonzeroSet hz p)
    · fun_prop
  have hHdiff : Differentiable ℂ H := by
    dsimp only [H]
    exact hF.mul hQdiff
  have hZdiff : DifferentiableOn ℂ Z riemannXiNonzeroSet := by
    dsimp only [Z]
    exact hF.differentiableOn.mul hSdiff
  obtain ⟨hbottomMap, htopMap, hrightMap, hleftMap⟩ :=
    mapsTo_riemannXiNonzeroSet_rectangle_edges hlr hbt hboundary
  have hHb : IntervalIntegrable (fun x : ℝ => H (x + b * I)) volume l r := by
    apply Continuous.intervalIntegrable
    exact hHdiff.continuous.comp (by fun_prop)
  have hHt : IntervalIntegrable (fun x : ℝ => H (x + t * I)) volume l r := by
    apply Continuous.intervalIntegrable
    exact hHdiff.continuous.comp (by fun_prop)
  have hHr : IntervalIntegrable (fun y : ℝ => H (r + y * I)) volume b t := by
    apply Continuous.intervalIntegrable
    exact hHdiff.continuous.comp (by fun_prop)
  have hHl : IntervalIntegrable (fun y : ℝ => H (l + y * I)) volume b t := by
    apply Continuous.intervalIntegrable
    exact hHdiff.continuous.comp (by fun_prop)
  have hZb : IntervalIntegrable (fun x : ℝ => Z (x + b * I)) volume l r :=
    intervalIntegrable_comp_of_differentiableOn isOpen_riemannXiNonzeroSet hZdiff
      (by fun_prop) hbottomMap
  have hZt : IntervalIntegrable (fun x : ℝ => Z (x + t * I)) volume l r :=
    intervalIntegrable_comp_of_differentiableOn isOpen_riemannXiNonzeroSet hZdiff
      (by fun_prop) htopMap
  have hZr : IntervalIntegrable (fun y : ℝ => Z (r + y * I)) volume b t :=
    intervalIntegrable_comp_of_differentiableOn isOpen_riemannXiNonzeroSet hZdiff
      (by fun_prop) hrightMap
  have hZl : IntervalIntegrable (fun y : ℝ => Z (l + y * I)) volume b t :=
    intervalIntegrable_comp_of_differentiableOn isOpen_riemannXiNonzeroSet hZdiff
      (by fun_prop) hleftMap
  have hbottom :
      (∫ x : ℝ in l..r, F (x + b * I) * logDeriv riemannXi (x + b * I)) =
        ∫ x : ℝ in l..r, H (x + b * I) + Z (x + b * I) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hlog := riemannXi_logDeriv_eq_polynomial_derivative_add_tsum
      hfac (hbottomMap hx)
    dsimp only [H, Z, Q, S]
    rw [hlog]
    ring
  have htop :
      (∫ x : ℝ in l..r, F (x + t * I) * logDeriv riemannXi (x + t * I)) =
        ∫ x : ℝ in l..r, H (x + t * I) + Z (x + t * I) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hlog := riemannXi_logDeriv_eq_polynomial_derivative_add_tsum
      hfac (htopMap hx)
    dsimp only [H, Z, Q, S]
    rw [hlog]
    ring
  have hright :
      (∫ y : ℝ in b..t, F (r + y * I) * logDeriv riemannXi (r + y * I)) =
        ∫ y : ℝ in b..t, H (r + y * I) + Z (r + y * I) := by
    apply intervalIntegral.integral_congr
    intro y hy
    have hlog := riemannXi_logDeriv_eq_polynomial_derivative_add_tsum
      hfac (hrightMap hy)
    dsimp only [H, Z, Q, S]
    rw [hlog]
    ring
  have hleft :
      (∫ y : ℝ in b..t, F (l + y * I) * logDeriv riemannXi (l + y * I)) =
        ∫ y : ℝ in b..t, H (l + y * I) + Z (l + y * I) := by
    apply intervalIntegral.integral_congr
    intro y hy
    have hlog := riemannXi_logDeriv_eq_polynomial_derivative_add_tsum
      hfac (hleftMap hy)
    dsimp only [H, Z, Q, S]
    rw [hlog]
    ring
  have hboundaryEq :
      rectangleBoundaryIntegral (fun z => F z * logDeriv riemannXi z) l r b t =
        rectangleBoundaryIntegral (fun z => H z + Z z) l r b t := by
    unfold rectangleBoundaryIntegral
    rw [hbottom, htop, hright, hleft]
  have hadd := rectangleBoundaryIntegral_add hHb hZb hHt hZt hHr hZr hHl hZl
  have hHzero : rectangleBoundaryIntegral H l r b t = 0 :=
    rectangleBoundaryIntegral_eq_zero_of_differentiableOn hHdiff.differentiableOn
  calc
    rectangleBoundaryIntegral (fun z => F z * logDeriv riemannXi z) l r b t =
        rectangleBoundaryIntegral (fun z => H z + Z z) l r b t := hboundaryEq
    _ = rectangleBoundaryIntegral H l r b t + rectangleBoundaryIntegral Z l r b t := hadd
    _ = rectangleBoundaryIntegral Z l r b t := by rw [hHzero, zero_add]
    _ = 2 * (Real.pi : ℂ) * I *
          ∑ᶠ p : RiemannXiDivisorZeroIndex,
            if riemannXiZeroStrictlyInsideRectangle l r b t p then
              F (riemannXiDivisorZeroValue p)
            else 0 := by
      simpa only [Z, S] using
        rectangleBoundaryIntegral_weighted_riemannXiZeroSum_eq_finsum
          hF hlr hbt hboundary

end

end LeanLab.Riemann
