import LeanLab.Riemann.LevinsonMontgomeryCriticalIndentation
import Mathlib.Topology.Order.IntermediateValue

/-!
# The Conrey--Li phase obstruction

This file formalizes the topological and algebraic core of the nonnumerical obstruction recorded
in the concluding Sarnak remark of Conrey--Li (1998).
-/

namespace LeanLab

namespace Riemann

open Complex Function Set

noncomputable section

def ConreyLiShiftRatioNonnegative (W : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, -(1 / 2 : ℝ) < z.im →
    0 ≤ (W z / W (z + I)).re

theorem conreyLi_im_unbounded_above_of_denseRange
    {X : Type*} {u : X → ℂ} (hu : DenseRange u) (A : ℝ) :
    ∃ x : X, A < (u x).im := by
  obtain ⟨x, hx⟩ :=
    hu.exists_dist_lt (((A + 2 : ℝ) : ℂ) * I) (by norm_num : (0 : ℝ) < 1)
  have hnorm :
      ‖(((A + 2 : ℝ) : ℂ) * I) - u x‖ < 1 := by
    simpa [Complex.dist_eq] using hx
  have him :
      |(A + 2) - (u x).im| < 1 := by
    have :=
      lt_of_le_of_lt
        (Complex.abs_im_le_norm ((((A + 2 : ℝ) : ℂ) * I) - u x)) hnorm
    simpa using this
  refine ⟨x, ?_⟩
  have := (abs_lt.mp him).2
  linarith

theorem conreyLi_im_unbounded_below_of_denseRange
    {X : Type*} {u : X → ℂ} (hu : DenseRange u) (A : ℝ) :
    ∃ x : X, (u x).im < A := by
  obtain ⟨x, hx⟩ :=
    hu.exists_dist_lt (((A - 2 : ℝ) : ℂ) * I) (by norm_num : (0 : ℝ) < 1)
  have hnorm :
      ‖(((A - 2 : ℝ) : ℂ) * I) - u x‖ < 1 := by
    simpa [Complex.dist_eq] using hx
  have him :
      |(A - 2) - (u x).im| < 1 := by
    have :=
      lt_of_le_of_lt
        (Complex.abs_im_le_norm ((((A - 2 : ℝ) : ℂ) * I) - u x)) hnorm
    simpa using this
  refine ⟨x, ?_⟩
  have := (abs_lt.mp him).1
  linarith

theorem conreyLi_corrected_im_unbounded_above
    {X : Type*} {u ell : X → ℂ} (hu : DenseRange u)
    {C : ℝ} (hbound : ∀ x : X, |(ell x - u x).im| ≤ C) (A : ℝ) :
    ∃ x : X, A < (ell x).im := by
  obtain ⟨x, hx⟩ :=
    conreyLi_im_unbounded_above_of_denseRange hu (A + C + 1)
  have hcorrection := (abs_le.mp (hbound x)).1
  refine ⟨x, ?_⟩
  simp only [sub_im] at hcorrection
  linarith

theorem conreyLi_corrected_im_unbounded_below
    {X : Type*} {u ell : X → ℂ} (hu : DenseRange u)
    {C : ℝ} (hbound : ∀ x : X, |(ell x - u x).im| ≤ C) (A : ℝ) :
    ∃ x : X, (ell x).im < A := by
  obtain ⟨x, hx⟩ :=
    conreyLi_im_unbounded_below_of_denseRange hu (A - C - 1)
  have hcorrection := (abs_le.mp (hbound x)).2
  refine ⟨x, ?_⟩
  simp only [sub_im] at hcorrection
  linarith

theorem conreyLi_exists_phase_eq_pi
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X] [Nonempty X]
    {u ell : X → ℂ} (hu : DenseRange u)
    (hell : Continuous fun x => (ell x).im)
    {C : ℝ} (hbound : ∀ x : X, |(ell x - u x).im| ≤ C) :
    ∃ x : X, (ell x).im = Real.pi := by
  obtain ⟨a, ha⟩ :=
    conreyLi_corrected_im_unbounded_below hu hbound Real.pi
  obtain ⟨b, hb⟩ :=
    conreyLi_corrected_im_unbounded_above hu hbound Real.pi
  have hpi :
      Real.pi ∈ Set.Icc ((ell a).im) ((ell b).im) :=
    ⟨ha.le, hb.le⟩
  obtain ⟨x, hx⟩ :=
    intermediate_value_univ a b hell hpi
  exact ⟨x, hx⟩

theorem conreyLi_exists_exp_re_neg
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X] [Nonempty X]
    {u ell : X → ℂ} (hu : DenseRange u)
    (hell : Continuous fun x => (ell x).im)
    {C : ℝ} (hbound : ∀ x : X, |(ell x - u x).im| ≤ C) :
    ∃ x : X, (Complex.exp (ell x)).re < 0 := by
  obtain ⟨x, hx⟩ :=
    conreyLi_exists_phase_eq_pi hu hell hbound
  refine ⟨x, ?_⟩
  rw [Complex.exp_re, hx, Real.cos_pi]
  simpa using neg_neg_of_pos (Real.exp_pos (ell x).re)

def conreyLiShiftCoordinate (s : ℂ) : ℂ :=
  I * (s - 1)

def conreyLiReciprocalModel (Xi : ℂ → ℂ) (z : ℂ) : ℂ :=
  (Xi (1 - I * z))⁻¹

theorem conreyLi_one_sub_I_mul_shiftCoordinate (s : ℂ) :
    1 - I * conreyLiShiftCoordinate s = s := by
  simp only [conreyLiShiftCoordinate]
  rw [← mul_assoc, I_mul_I]
  ring

theorem conreyLi_one_sub_I_mul_shiftCoordinate_add_I (s : ℂ) :
    1 - I * (conreyLiShiftCoordinate s + I) = s + 1 := by
  simp only [conreyLiShiftCoordinate, mul_add]
  rw [← mul_assoc, I_mul_I]
  ring

theorem conreyLi_reciprocal_shift_ratio_eq_inv
    {Xi : ℂ → ℂ} {s : ℂ} (hXi : Xi s ≠ 0) (hXiShift : Xi (s + 1) ≠ 0) :
    conreyLiReciprocalModel Xi (conreyLiShiftCoordinate s) /
        conreyLiReciprocalModel Xi (conreyLiShiftCoordinate s + I) =
      (Xi s / Xi (s + 1))⁻¹ := by
  rw [conreyLiReciprocalModel, conreyLiReciprocalModel,
    conreyLi_one_sub_I_mul_shiftCoordinate,
    conreyLi_one_sub_I_mul_shiftCoordinate_add_I]
  field_simp

theorem conreyLi_inv_re_neg_of_re_neg {z : ℂ} (hz : z.re < 0) :
    (z⁻¹).re < 0 := by
  rw [Complex.inv_re]
  exact div_neg_of_neg_of_pos hz (Complex.normSq_pos.mpr (by
    intro hzero
    subst z
    simp at hz))

theorem conreyLi_shiftCoordinate_im (s : ℂ) :
    (conreyLiShiftCoordinate s).im = s.re - 1 := by
  simp [conreyLiShiftCoordinate, mul_im]

theorem not_conreyLiShiftRatioNonnegative_of_phase_data
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X] [Nonempty X]
    {Xi : ℂ → ℂ} {s u ell : X → ℂ}
    (hu : DenseRange u)
    (hell : Continuous fun x => (ell x).im)
    {C : ℝ} (hbound : ∀ x : X, |(ell x - u x).im| ≤ C)
    (hstrip : ∀ x : X, 1 / 2 < (s x).re)
    (hnonzero : ∀ x : X, Xi (s x) ≠ 0 ∧ Xi (s x + 1) ≠ 0)
    (hlog : ∀ x : X, Complex.exp (ell x) = Xi (s x) / Xi (s x + 1)) :
    ¬ConreyLiShiftRatioNonnegative (conreyLiReciprocalModel Xi) := by
  intro hnonnegative
  obtain ⟨x, hx⟩ :=
    conreyLi_exists_exp_re_neg hu hell hbound
  have hratio : (Xi (s x) / Xi (s x + 1)).re < 0 := by
    rw [← hlog x]
    exact hx
  have hinv :
      ((Xi (s x) / Xi (s x + 1))⁻¹).re < 0 :=
    conreyLi_inv_re_neg_of_re_neg hratio
  have hcoordinate :
      -(1 / 2 : ℝ) < (conreyLiShiftCoordinate (s x)).im := by
    rw [conreyLi_shiftCoordinate_im]
    have := hstrip x
    linarith
  have hsource :=
    hnonnegative (conreyLiShiftCoordinate (s x)) hcoordinate
  rw [conreyLi_reciprocal_shift_ratio_eq_inv
    (hnonzero x).1 (hnonzero x).2] at hsource
  linarith

theorem not_conreyLiRiemannXiShiftRatioNonnegative_of_phase_data
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X] [Nonempty X]
    {s u ell : X → ℂ}
    (hu : DenseRange u)
    (hell : Continuous fun x => (ell x).im)
    {C : ℝ} (hbound : ∀ x : X, |(ell x - u x).im| ≤ C)
    (hstrip : ∀ x : X, 1 / 2 < (s x).re)
    (hnonzero : ∀ x : X,
      riemannXi (s x) ≠ 0 ∧ riemannXi (s x + 1) ≠ 0)
    (hlog : ∀ x : X, Complex.exp (ell x) =
      riemannXi (s x) / riemannXi (s x + 1)) :
    ¬ConreyLiShiftRatioNonnegative
      (conreyLiReciprocalModel riemannXi) :=
  not_conreyLiShiftRatioNonnegative_of_phase_data
    hu hell hbound hstrip hnonzero hlog

end

end Riemann

end LeanLab
