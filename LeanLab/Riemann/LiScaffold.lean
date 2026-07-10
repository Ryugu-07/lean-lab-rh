import LeanLab.Riemann.Basic
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

set_option linter.style.header false

/-!
# First Li-criterion scaffold

This file introduces a project-local xi-like entire function built from mathlib's
pole-removed completed zeta function. It is only scaffolding for later Li
coefficient work.
-/

namespace LeanLab.Riemann

open Complex
open Filter Asymptotics
open HurwitzZeta
open Real Set MeasureTheory
open scoped Topology

noncomputable section

/--
Project-local xi function, written using `completedRiemannZeta₀` rather than
`completedRiemannZeta`, whose values at the poles of the completed zeta are
implementation-dependent.
-/
def riemannXi (s : ℂ) : ℂ :=
  s * (s - 1) / 2 * completedRiemannZeta₀ s + 1 / 2

theorem riemannXi_eq_mul_completedRiemannZeta {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    riemannXi s = s * (s - 1) / 2 * completedRiemannZeta s := by
  rw [riemannXi, completedRiemannZeta_eq]
  have h1s : (1 : ℂ) - s ≠ 0 := by
    exact sub_ne_zero.mpr (Ne.symm hs1)
  field_simp [hs0, h1s]
  ring

theorem isZetaZero_of_riemannXi_eq_zero {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hxi : riemannXi s = 0) :
    IsZetaZero s := by
  rw [IsZetaZero]
  rw [riemannZeta_def_of_ne_zero hs0]
  have hcomp : completedRiemannZeta s = 0 := by
    have hbridge := riemannXi_eq_mul_completedRiemannZeta hs0 hs1
    rw [hbridge] at hxi
    have hs_sub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    have hfactor : s * (s - 1) / 2 ≠ 0 := by
      exact div_ne_zero (mul_ne_zero hs0 hs_sub) (by norm_num : (2 : ℂ) ≠ 0)
    exact (mul_eq_zero.mp hxi).resolve_left hfactor
  rw [hcomp]
  simp

theorem completedRiemannZeta_eq_zero_of_isZetaZero_of_Gammaℝ_ne_zero {s : ℂ}
    (hs0 : s ≠ 0) (hgamma : Gammaℝ s ≠ 0) (hz : IsZetaZero s) :
    completedRiemannZeta s = 0 := by
  rw [IsZetaZero] at hz
  rw [riemannZeta_def_of_ne_zero hs0] at hz
  exact (div_eq_zero_iff.mp hz).resolve_right hgamma

theorem riemannXi_eq_zero_of_isZetaZero_of_Gammaℝ_ne_zero {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hgamma : Gammaℝ s ≠ 0) (hz : IsZetaZero s) :
    riemannXi s = 0 := by
  have hcomp : completedRiemannZeta s = 0 :=
    completedRiemannZeta_eq_zero_of_isZetaZero_of_Gammaℝ_ne_zero
      hs0 hgamma hz
  rw [riemannXi_eq_mul_completedRiemannZeta hs0 hs1, hcomp]
  simp

theorem eq_zero_or_isTrivialZeroPoint_of_Gammaℝ_eq_zero {s : ℂ}
    (hgamma : Gammaℝ s = 0) :
    s = 0 ∨ IsTrivialZeroPoint s := by
  rcases Gammaℝ_eq_zero_iff.mp hgamma with ⟨n, hn⟩
  cases n with
  | zero =>
      left
      simpa using hn
  | succ n =>
      right
      refine ⟨n, ?_⟩
      rw [hn]
      norm_num

theorem Gammaℝ_ne_zero_of_isNontrivialZero {s : ℂ}
    (hs : IsNontrivialZero s) :
    Gammaℝ s ≠ 0 := by
  intro hgamma
  rcases eq_zero_or_isTrivialZeroPoint_of_Gammaℝ_eq_zero hgamma with hzero | htriv
  · have hz0 : riemannZeta (0 : ℂ) = 0 := by
      simpa [IsZetaZero, hzero] using hs.1
    have hval : riemannZeta (0 : ℂ) ≠ 0 := by
      rw [riemannZeta_zero]
      norm_num
    exact hval hz0
  · exact hs.2.1 htriv

theorem ne_zero_of_isNontrivialZero {s : ℂ}
    (hs : IsNontrivialZero s) :
    s ≠ 0 := by
  intro hzero
  have hz0 : riemannZeta (0 : ℂ) = 0 := by
    simpa [IsZetaZero, hzero] using hs.1
  have hval : riemannZeta (0 : ℂ) ≠ 0 := by
    rw [riemannZeta_zero]
    norm_num
  exact hval hz0

theorem riemannXi_eq_zero_of_isNontrivialZero {s : ℂ}
    (hs : IsNontrivialZero s) :
    riemannXi s = 0 := by
  exact riemannXi_eq_zero_of_isZetaZero_of_Gammaℝ_ne_zero
    (ne_zero_of_isNontrivialZero hs) hs.2.2
    (Gammaℝ_ne_zero_of_isNontrivialZero hs) hs.1

theorem riemannXi_zero :
    riemannXi 0 = 1 / 2 := by
  norm_num [riemannXi]

theorem riemannXi_zero_ne_zero :
    riemannXi 0 ≠ 0 := by
  rw [riemannXi_zero]
  norm_num

theorem riemannXi_one :
    riemannXi 1 = 1 / 2 := by
  norm_num [riemannXi]

theorem riemannXi_one_ne_zero :
    riemannXi 1 ≠ 0 := by
  rw [riemannXi_one]
  norm_num

theorem isNontrivialZero_iff_riemannXi_eq_zero_and_not_trivial (s : ℂ) :
    IsNontrivialZero s ↔ riemannXi s = 0 ∧ ¬ IsTrivialZeroPoint s := by
  constructor
  · intro hs
    exact ⟨riemannXi_eq_zero_of_isNontrivialZero hs, hs.2.1⟩
  · intro h
    rcases h with ⟨hxi, hnottriv⟩
    have hs0 : s ≠ 0 := by
      intro hs_zero
      have hxi0 : riemannXi 0 = 0 := by
        simpa [hs_zero] using hxi
      exact riemannXi_zero_ne_zero hxi0
    have hs1 : s ≠ 1 := by
      intro hs_one
      have hxi1 : riemannXi 1 = 0 := by
        simpa [hs_one] using hxi
      exact riemannXi_one_ne_zero hxi1
    exact ⟨isZetaZero_of_riemannXi_eq_zero hs0 hs1 hxi, hnottriv, hs1⟩

theorem riemannXi_one_mem_slitPlane :
    riemannXi 1 ∈ slitPlane := by
  rw [riemannXi_one, mem_slitPlane_iff]
  left
  norm_num

theorem riemannXi_one_sub (s : ℂ) :
    riemannXi (1 - s) = riemannXi s := by
  rw [riemannXi, riemannXi, completedRiemannZeta₀_one_sub]
  ring

theorem riemannXi_half :
    riemannXi (1 / 2) = 1 / 2 - (1 / 8) * completedRiemannZeta₀ (1 / 2) := by
  unfold riemannXi
  ring

theorem completedRiemannZeta₀_half_eq_riemannXi_half :
    completedRiemannZeta₀ (1 / 2) = 4 - 8 * riemannXi (1 / 2) := by
  rw [riemannXi_half]
  ring

theorem half_sub_eq_of_one_sub_eq_self (f : ℂ → ℂ)
    (hsym : ∀ s : ℂ, f (1 - s) = f s) (z : ℂ) :
    f (1 / 2 - z) = f (1 / 2 + z) := by
  have h := hsym (1 / 2 + z)
  have harg : 1 - (1 / 2 + z) = 1 / 2 - z := by ring
  rw [harg] at h
  exact h

theorem centered_even_of_one_sub_eq_self (f : ℂ → ℂ)
    (hsym : ∀ s : ℂ, f (1 - s) = f s) (z : ℂ) :
    (fun w : ℂ ↦ f (1 / 2 + w)) (-z) =
      (fun w : ℂ ↦ f (1 / 2 + w)) z := by
  simpa [sub_eq_add_neg] using half_sub_eq_of_one_sub_eq_self f hsym z

theorem riemannXi_half_sub (z : ℂ) :
    riemannXi (1 / 2 - z) = riemannXi (1 / 2 + z) :=
  half_sub_eq_of_one_sub_eq_self riemannXi riemannXi_one_sub z

theorem centered_riemannXi_even (z : ℂ) :
    (fun w : ℂ ↦ riemannXi (1 / 2 + w)) (-z) =
      (fun w : ℂ ↦ riemannXi (1 / 2 + w)) z :=
  centered_even_of_one_sub_eq_self riemannXi riemannXi_one_sub z

theorem completedRiemannZeta₀_half_sub (z : ℂ) :
    completedRiemannZeta₀ (1 / 2 - z) =
      completedRiemannZeta₀ (1 / 2 + z) :=
  half_sub_eq_of_one_sub_eq_self
    completedRiemannZeta₀ completedRiemannZeta₀_one_sub z

theorem centered_completedRiemannZeta₀_even (z : ℂ) :
    (fun w : ℂ ↦ completedRiemannZeta₀ (1 / 2 + w)) (-z) =
      (fun w : ℂ ↦ completedRiemannZeta₀ (1 / 2 + w)) z :=
  centered_even_of_one_sub_eq_self
    completedRiemannZeta₀ completedRiemannZeta₀_one_sub z

theorem deriv_eq_zero_at_half_of_one_sub_eq_self (f : ℂ → ℂ)
    (hsym : ∀ s : ℂ, f (1 - s) = f s) :
    deriv f (1 / 2) = 0 := by
  have hsymEvent :
      (fun s : ℂ ↦ f (1 - s)) =ᶠ[𝓝 (1 / 2 : ℂ)] f :=
    Filter.Eventually.of_forall hsym
  have hderiv :
      deriv (fun s : ℂ ↦ f (1 - s)) (1 / 2 : ℂ) =
        deriv f (1 / 2 : ℂ) :=
    Filter.EventuallyEq.deriv_eq hsymEvent
  rw [deriv_comp_const_sub] at hderiv
  norm_num at hderiv
  exact neg_eq_self.mp hderiv

theorem deriv_riemannXi_half_eq_zero :
    deriv riemannXi (1 / 2) = 0 :=
  deriv_eq_zero_at_half_of_one_sub_eq_self riemannXi riemannXi_one_sub

theorem deriv_completedRiemannZeta₀_half_eq_zero :
    deriv completedRiemannZeta₀ (1 / 2) = 0 :=
  deriv_eq_zero_at_half_of_one_sub_eq_self
    completedRiemannZeta₀ completedRiemannZeta₀_one_sub

theorem deriv_centered_zero_of_one_sub_eq_self (f : ℂ → ℂ)
    (hsym : ∀ s : ℂ, f (1 - s) = f s) :
    deriv (fun z : ℂ ↦ f (1 / 2 + z)) 0 = 0 := by
  rw [deriv_comp_const_add]
  simpa using deriv_eq_zero_at_half_of_one_sub_eq_self f hsym

theorem deriv_centered_riemannXi_zero :
    deriv (fun z : ℂ ↦ riemannXi (1 / 2 + z)) 0 = 0 :=
  deriv_centered_zero_of_one_sub_eq_self riemannXi riemannXi_one_sub

theorem deriv_centered_completedRiemannZeta₀_zero :
    deriv (fun z : ℂ ↦ completedRiemannZeta₀ (1 / 2 + z)) 0 = 0 :=
  deriv_centered_zero_of_one_sub_eq_self
    completedRiemannZeta₀ completedRiemannZeta₀_one_sub

theorem iteratedDeriv_odd_eq_zero_of_even (g : ℂ → ℂ) (k : ℕ)
    (heven : ∀ z : ℂ, g (-z) = g z) :
    iteratedDeriv (2 * k + 1) g 0 = 0 := by
  let n : ℕ := 2 * k + 1
  have hfun : (fun z : ℂ ↦ g (-z)) = g := by
    funext z
    exact heven z
  have hderiv :
      iteratedDeriv n (fun z : ℂ ↦ g (-z)) 0 = iteratedDeriv n g 0 := by
    rw [hfun]
  rw [iteratedDeriv_comp_neg] at hderiv
  have hpow : (-1 : ℂ) ^ n = -1 := by
    unfold n
    rw [pow_add]
    norm_num
  have hneg : -iteratedDeriv n g 0 = iteratedDeriv n g 0 := by
    simpa [hpow] using hderiv
  exact neg_eq_self.mp hneg

theorem iteratedDeriv_centered_odd_eq_zero_of_one_sub_eq_self
    (f : ℂ → ℂ) (k : ℕ) (hsym : ∀ s : ℂ, f (1 - s) = f s) :
    iteratedDeriv (2 * k + 1) (fun z : ℂ ↦ f (1 / 2 + z)) 0 = 0 :=
  iteratedDeriv_odd_eq_zero_of_even
    (fun z : ℂ ↦ f (1 / 2 + z)) k
    (centered_even_of_one_sub_eq_self f hsym)

theorem iteratedDeriv_centered_riemannXi_odd_eq_zero (k : ℕ) :
    iteratedDeriv (2 * k + 1) (fun z : ℂ ↦ riemannXi (1 / 2 + z)) 0 = 0 :=
  iteratedDeriv_centered_odd_eq_zero_of_one_sub_eq_self
    riemannXi k riemannXi_one_sub

theorem iteratedDeriv_centered_completedRiemannZeta₀_odd_eq_zero (k : ℕ) :
    iteratedDeriv (2 * k + 1)
      (fun z : ℂ ↦ completedRiemannZeta₀ (1 / 2 + z)) 0 = 0 :=
  iteratedDeriv_centered_odd_eq_zero_of_one_sub_eq_self
    completedRiemannZeta₀ k completedRiemannZeta₀_one_sub

theorem iteratedDeriv_centered_eq (f : ℂ → ℂ) (n : ℕ) :
    iteratedDeriv n (fun z : ℂ ↦ f (1 / 2 + z)) 0 =
      iteratedDeriv n f (1 / 2) := by
  rw [iteratedDeriv_comp_const_add]
  norm_num

theorem iteratedDeriv_centered_riemannXi_eq (n : ℕ) :
    iteratedDeriv n (fun z : ℂ ↦ riemannXi (1 / 2 + z)) 0 =
      iteratedDeriv n riemannXi (1 / 2) :=
  iteratedDeriv_centered_eq riemannXi n

theorem iteratedDeriv_centered_riemannXi_zero_eq_half :
    iteratedDeriv 0 (fun z : ℂ ↦ riemannXi (1 / 2 + z)) 0 =
      riemannXi (1 / 2) := by
  simp [iteratedDeriv_zero]

theorem iteratedDeriv_centered_riemannXi_zero_eq_completedZeta₀_half :
    iteratedDeriv 0 (fun z : ℂ ↦ riemannXi (1 / 2 + z)) 0 =
      1 / 2 - (1 / 8) * completedRiemannZeta₀ (1 / 2) := by
  rw [iteratedDeriv_centered_riemannXi_zero_eq_half, riemannXi_half]

theorem iteratedDeriv_centered_completedRiemannZeta₀_eq (n : ℕ) :
    iteratedDeriv n (fun z : ℂ ↦ completedRiemannZeta₀ (1 / 2 + z)) 0 =
      iteratedDeriv n completedRiemannZeta₀ (1 / 2) :=
  iteratedDeriv_centered_eq completedRiemannZeta₀ n

theorem iteratedDeriv_centered_riemannXi_two_eq_deriv_deriv :
    iteratedDeriv 2 (fun z : ℂ ↦ riemannXi (1 / 2 + z)) 0 =
      deriv (deriv riemannXi) (1 / 2) := by
  rw [iteratedDeriv_centered_riemannXi_eq]
  simp [iteratedDeriv_succ]

theorem iteratedDeriv_centered_completedRiemannZeta₀_two_eq_deriv_deriv :
    iteratedDeriv 2 (fun z : ℂ ↦ completedRiemannZeta₀ (1 / 2 + z)) 0 =
      deriv (deriv completedRiemannZeta₀) (1 / 2) := by
  rw [iteratedDeriv_centered_completedRiemannZeta₀_eq]
  simp [iteratedDeriv_succ]

theorem differentiable_riemannXi :
    Differentiable ℂ riemannXi := by
  unfold riemannXi
  have hpoly : Differentiable ℂ (fun s : ℂ ↦ s * (s - 1) / 2) := by
    fun_prop
  have hconst : Differentiable ℂ (fun _ : ℂ ↦ (1 / 2 : ℂ)) := by
    fun_prop
  exact (hpoly.mul differentiable_completedZeta₀).add hconst

theorem analyticAt_riemannXi (s : ℂ) :
    AnalyticAt ℂ riemannXi s :=
  differentiable_riemannXi.analyticAt s

theorem analyticAt_log_riemannXi_one :
    AnalyticAt ℂ (fun s : ℂ ↦ log (riemannXi s)) 1 :=
  (analyticAt_riemannXi 1).clog riemannXi_one_mem_slitPlane

theorem differentiableAt_log_riemannXi_one :
    DifferentiableAt ℂ (fun s : ℂ ↦ log (riemannXi s)) 1 :=
  analyticAt_log_riemannXi_one.differentiableAt

theorem hasDerivAt_log_riemannXi_one :
    HasDerivAt (fun s : ℂ ↦ log (riemannXi s))
      (deriv riemannXi 1 / riemannXi 1) 1 := by
  exact (differentiable_riemannXi 1).hasDerivAt.clog riemannXi_one_mem_slitPlane

theorem deriv_log_riemannXi_one :
    deriv (fun s : ℂ ↦ log (riemannXi s)) 1 =
      deriv riemannXi 1 / riemannXi 1 :=
  hasDerivAt_log_riemannXi_one.deriv

theorem deriv_riemannXi_factor_one :
    deriv (fun s : ℂ ↦ s * (s - 1) / 2) 1 = 1 / 2 := by
  simp [deriv_div_const, deriv_fun_mul]

theorem deriv_riemannXi_factor (s : ℂ) :
    deriv (fun z : ℂ ↦ z * (z - 1) / 2) s = s - 1 / 2 := by
  simp [deriv_div_const, deriv_fun_mul]
  ring

theorem deriv_riemannXi_one :
    deriv riemannXi 1 = completedRiemannZeta₀ 1 / 2 := by
  unfold riemannXi
  rw [deriv_add_const]
  rw [deriv_fun_mul]
  · rw [deriv_riemannXi_factor_one]
    ring
  · fun_prop
  · exact differentiable_completedZeta₀.differentiableAt

theorem deriv_riemannXi (s : ℂ) :
    deriv riemannXi s =
      (s - 1 / 2) * completedRiemannZeta₀ s +
        (s * (s - 1) / 2) * deriv completedRiemannZeta₀ s := by
  unfold riemannXi
  rw [deriv_add_const]
  rw [deriv_fun_mul]
  · rw [deriv_riemannXi_factor]
  · fun_prop
  · exact differentiable_completedZeta₀.differentiableAt

theorem analyticAt_deriv_completedRiemannZeta₀_one :
    AnalyticAt ℂ (deriv completedRiemannZeta₀) 1 :=
  (differentiable_completedZeta₀.analyticAt 1).deriv

theorem differentiableAt_deriv_completedRiemannZeta₀_one :
    DifferentiableAt ℂ (deriv completedRiemannZeta₀) 1 :=
  analyticAt_deriv_completedRiemannZeta₀_one.differentiableAt

theorem analyticAt_deriv_completedRiemannZeta₀_half :
    AnalyticAt ℂ (deriv completedRiemannZeta₀) (1 / 2 : ℂ) :=
  (differentiable_completedZeta₀.analyticAt (1 / 2 : ℂ)).deriv

theorem differentiableAt_deriv_completedRiemannZeta₀_half :
    DifferentiableAt ℂ (deriv completedRiemannZeta₀) (1 / 2 : ℂ) :=
  analyticAt_deriv_completedRiemannZeta₀_half.differentiableAt

theorem deriv_deriv_riemannXi_half :
    deriv (deriv riemannXi) (1 / 2) =
      completedRiemannZeta₀ (1 / 2) -
        (1 / 8) * deriv (deriv completedRiemannZeta₀) (1 / 2) := by
  have hderiv :
      (deriv riemannXi) =ᶠ[𝓝 (1 / 2 : ℂ)]
          (fun s : ℂ ↦ (s - 1 / 2) * completedRiemannZeta₀ s +
            (s * (s - 1) / 2) * deriv completedRiemannZeta₀ s) :=
    Filter.Eventually.of_forall deriv_riemannXi
  rw [Filter.EventuallyEq.deriv_eq hderiv]
  have hfirst :
      deriv (fun s : ℂ ↦ (s - 1 / 2) * completedRiemannZeta₀ s)
          (1 / 2 : ℂ) =
        completedRiemannZeta₀ (1 / 2) := by
    rw [deriv_fun_mul]
    · simp
    · fun_prop
    · exact differentiable_completedZeta₀.differentiableAt
  have hsecond :
      deriv (fun s : ℂ ↦ (s * (s - 1) / 2) * deriv completedRiemannZeta₀ s)
          (1 / 2 : ℂ) =
        -(1 / 8) * deriv (deriv completedRiemannZeta₀) (1 / 2) := by
    rw [deriv_fun_mul]
    · rw [deriv_riemannXi_factor]
      ring
    · fun_prop
    · exact differentiableAt_deriv_completedRiemannZeta₀_half
  rw [deriv_fun_add]
  · rw [hfirst, hsecond]
    ring
  · exact (by
      have hlin : DifferentiableAt ℂ (fun s : ℂ ↦ s - 1 / 2) (1 / 2 : ℂ) := by
        fun_prop
      exact hlin.mul differentiable_completedZeta₀.differentiableAt)
  · exact (by
      have hpoly : DifferentiableAt ℂ (fun s : ℂ ↦ s * (s - 1) / 2)
          (1 / 2 : ℂ) := by
        fun_prop
      exact hpoly.mul differentiableAt_deriv_completedRiemannZeta₀_half)

theorem iteratedDeriv_centered_riemannXi_two_eq_completedZeta₀_half :
    iteratedDeriv 2 (fun z : ℂ ↦ riemannXi (1 / 2 + z)) 0 =
      completedRiemannZeta₀ (1 / 2) -
        (1 / 8) * deriv (deriv completedRiemannZeta₀) (1 / 2) := by
  rw [iteratedDeriv_centered_riemannXi_two_eq_deriv_deriv,
    deriv_deriv_riemannXi_half]

theorem deriv_deriv_riemannXi_one :
    deriv (deriv riemannXi) 1 =
      completedRiemannZeta₀ 1 + deriv completedRiemannZeta₀ 1 := by
  have hderiv :
      (deriv riemannXi) =ᶠ[𝓝 (1 : ℂ)]
          (fun s : ℂ ↦ (s - 1 / 2) * completedRiemannZeta₀ s +
            (s * (s - 1) / 2) * deriv completedRiemannZeta₀ s) :=
    Filter.Eventually.of_forall deriv_riemannXi
  rw [Filter.EventuallyEq.deriv_eq hderiv]
  have hfirst :
      deriv (fun s : ℂ ↦ (s - 1 / 2) * completedRiemannZeta₀ s) 1 =
        completedRiemannZeta₀ 1 + (1 / 2) * deriv completedRiemannZeta₀ 1 := by
    rw [deriv_fun_mul]
    · rw [deriv_sub_const, deriv_id'']
      ring
    · fun_prop
    · exact differentiable_completedZeta₀.differentiableAt
  have hsecond :
      deriv (fun s : ℂ ↦ (s * (s - 1) / 2) * deriv completedRiemannZeta₀ s) 1 =
        (1 / 2) * deriv completedRiemannZeta₀ 1 := by
    rw [deriv_fun_mul]
    · rw [deriv_riemannXi_factor_one]
      ring
    · fun_prop
    · exact differentiableAt_deriv_completedRiemannZeta₀_one
  rw [deriv_fun_add]
  · rw [hfirst, hsecond]
    ring
  · exact (by
      have hlin : DifferentiableAt ℂ (fun s : ℂ ↦ s - 1 / 2) 1 := by
        fun_prop
      exact hlin.mul differentiable_completedZeta₀.differentiableAt)
  · exact (by
      have hpoly : DifferentiableAt ℂ (fun s : ℂ ↦ s * (s - 1) / 2) 1 := by
        fun_prop
      exact hpoly.mul differentiableAt_deriv_completedRiemannZeta₀_one)

theorem deriv_completedRiemannZeta₀_one_eq_neg_zero :
    deriv completedRiemannZeta₀ 1 = -deriv completedRiemannZeta₀ 0 := by
  have hsym :
      (fun s : ℂ ↦ completedRiemannZeta₀ (1 - s)) =ᶠ[𝓝 (0 : ℂ)]
        completedRiemannZeta₀ :=
    Filter.Eventually.of_forall completedRiemannZeta₀_one_sub
  have hderiv :
      deriv (fun s : ℂ ↦ completedRiemannZeta₀ (1 - s)) 0 =
        deriv completedRiemannZeta₀ 0 :=
    Filter.EventuallyEq.deriv_eq hsym
  rw [deriv_comp_const_sub] at hderiv
  norm_num at hderiv
  simpa using congrArg Neg.neg hderiv

theorem deriv_riemannZeta_zero_numerator :
    deriv (fun s : ℂ ↦ (s * completedRiemannZeta₀ s - 1) - s / (1 - s)) 0 =
      completedRiemannZeta₀ 0 - 1 := by
  have hleft :
      deriv (fun s : ℂ ↦ s * completedRiemannZeta₀ s - 1) 0 =
        completedRiemannZeta₀ 0 := by
    rw [deriv_sub_const]
    rw [deriv_fun_mul]
    · rw [deriv_id'']
      ring
    · exact differentiableAt_fun_id
    · exact differentiable_completedZeta₀.differentiableAt
  have hright : deriv (fun s : ℂ ↦ s / (1 - s)) 0 = 1 := by
    rw [deriv_fun_div differentiableAt_fun_id (by fun_prop) (by norm_num)]
    rw [deriv_id'', deriv_const_sub_id]
    ring
  rw [deriv_fun_sub]
  · rw [hleft, hright]
  · exact (by
      have hprod : DifferentiableAt ℂ (fun s : ℂ ↦ s * completedRiemannZeta₀ s) 0 :=
        differentiableAt_fun_id.mul differentiable_completedZeta₀.differentiableAt
      exact hprod.sub (by fun_prop))
  · exact differentiableAt_fun_id.div (by fun_prop) (by norm_num)

theorem completedRiemannZeta₀_zero_eq_one :
    completedRiemannZeta₀ 0 = completedRiemannZeta₀ 1 := by
  simpa using completedRiemannZeta₀_one_sub (1 : ℂ)

/--
Candidate expression for the `(n + 1)`-st Li coefficient, using the local
`riemannXi`. This is only a definition; no equivalence with RH is claimed here.
-/
def liCoefficientCandidate (n : ℕ) : ℂ :=
  iteratedDeriv (n + 1) (fun s : ℂ ↦ s ^ n * log (riemannXi s)) 1 /
    (Nat.factorial n : ℂ)

theorem liCoefficientCandidate_zero :
    liCoefficientCandidate 0 = deriv (fun s : ℂ ↦ log (riemannXi s)) 1 := by
  simp [liCoefficientCandidate, iteratedDeriv_one]

theorem liCoefficientCandidate_one_eq_secondDeriv :
    liCoefficientCandidate 1 =
      deriv (deriv (fun s : ℂ ↦ s * log (riemannXi s))) 1 := by
  simp [liCoefficientCandidate, iteratedDeriv_succ]

theorem liCoefficientCandidate_zero_eq_logDeriv :
    liCoefficientCandidate 0 = deriv riemannXi 1 / riemannXi 1 := by
  rw [liCoefficientCandidate_zero, deriv_log_riemannXi_one]

theorem deriv_id_mul_log_riemannXi_one :
    deriv (fun s : ℂ ↦ s * log (riemannXi s)) 1 =
      log (riemannXi 1) + deriv riemannXi 1 / riemannXi 1 := by
  rw [deriv_fun_mul]
  · rw [deriv_log_riemannXi_one]
    simp
  · exact differentiableAt_fun_id
  · exact differentiableAt_log_riemannXi_one

theorem deriv_id_mul_log_riemannXi_one_eq_completedZeta₀ :
    deriv (fun s : ℂ ↦ s * log (riemannXi s)) 1 =
      log (1 / 2 : ℂ) + completedRiemannZeta₀ 1 := by
  rw [deriv_id_mul_log_riemannXi_one, riemannXi_one, deriv_riemannXi_one]
  ring

theorem analyticAt_id_mul_log_riemannXi_one :
    AnalyticAt ℂ (fun s : ℂ ↦ s * log (riemannXi s)) 1 := by
  have hid : AnalyticAt ℂ (fun s : ℂ ↦ s) 1 := by
    fun_prop
  exact hid.mul analyticAt_log_riemannXi_one

theorem analyticAt_deriv_id_mul_log_riemannXi_one :
    AnalyticAt ℂ (deriv (fun s : ℂ ↦ s * log (riemannXi s))) 1 :=
  analyticAt_id_mul_log_riemannXi_one.deriv

theorem differentiableAt_deriv_id_mul_log_riemannXi_one :
    DifferentiableAt ℂ (deriv (fun s : ℂ ↦ s * log (riemannXi s))) 1 :=
  analyticAt_deriv_id_mul_log_riemannXi_one.differentiableAt

theorem hasDerivAt_deriv_id_mul_log_riemannXi_one :
    HasDerivAt (deriv (fun s : ℂ ↦ s * log (riemannXi s)))
      (liCoefficientCandidate 1) 1 := by
  rw [liCoefficientCandidate_one_eq_secondDeriv]
  exact differentiableAt_deriv_id_mul_log_riemannXi_one.hasDerivAt

theorem eventually_deriv_id_mul_log_riemannXi_eq :
    (fun s : ℂ ↦ deriv (fun t : ℂ ↦ t * log (riemannXi t)) s)
      =ᶠ[𝓝 (1 : ℂ)]
    (fun s : ℂ ↦ log (riemannXi s) +
      s * deriv (fun t : ℂ ↦ log (riemannXi t)) s) := by
  filter_upwards [analyticAt_log_riemannXi_one.eventually_analyticAt] with s hs
  rw [deriv_fun_mul]
  · simp
  · exact differentiableAt_fun_id
  · exact hs.differentiableAt

theorem liCoefficientCandidate_one_eq_deriv_productRule :
    liCoefficientCandidate 1 =
      deriv (fun s : ℂ ↦ log (riemannXi s) +
        s * deriv (fun t : ℂ ↦ log (riemannXi t)) s) 1 := by
  rw [liCoefficientCandidate_one_eq_secondDeriv]
  exact Filter.EventuallyEq.deriv_eq eventually_deriv_id_mul_log_riemannXi_eq

theorem eventually_riemannXi_mem_slitPlane_one :
    ∀ᶠ s in 𝓝 (1 : ℂ), riemannXi s ∈ slitPlane := by
  exact (differentiable_riemannXi 1).continuousAt.preimage_mem_nhds
    (isOpen_slitPlane.mem_nhds riemannXi_one_mem_slitPlane)

theorem eventually_deriv_log_riemannXi_eq_logDeriv :
    (fun s : ℂ ↦ deriv (fun t : ℂ ↦ log (riemannXi t)) s)
      =ᶠ[𝓝 (1 : ℂ)]
    logDeriv riemannXi := by
  filter_upwards [eventually_riemannXi_mem_slitPlane_one] with s hs
  simpa [Function.comp_def] using
    (Complex.deriv_log_comp_eq_logDeriv (f := riemannXi) (x := s)
      (differentiable_riemannXi s) hs)

theorem eventually_deriv_log_riemannXi_eq :
    (fun s : ℂ ↦ deriv (fun t : ℂ ↦ log (riemannXi t)) s)
      =ᶠ[𝓝 (1 : ℂ)]
    (fun s : ℂ ↦ deriv riemannXi s / riemannXi s) := by
  filter_upwards [eventually_deriv_log_riemannXi_eq_logDeriv] with s hs
  rw [hs]
  exact logDeriv_apply riemannXi s

theorem eventually_productRule_eq_logDeriv :
    (fun s : ℂ ↦ log (riemannXi s) +
      s * deriv (fun t : ℂ ↦ log (riemannXi t)) s)
      =ᶠ[𝓝 (1 : ℂ)]
    (fun s : ℂ ↦ log (riemannXi s) + s * logDeriv riemannXi s) := by
  filter_upwards [eventually_deriv_log_riemannXi_eq_logDeriv] with s hs
  rw [hs]

theorem eventually_productRule_eq_logDeriv_fraction :
    (fun s : ℂ ↦ log (riemannXi s) +
      s * deriv (fun t : ℂ ↦ log (riemannXi t)) s)
      =ᶠ[𝓝 (1 : ℂ)]
    (fun s : ℂ ↦ log (riemannXi s) + s * (deriv riemannXi s / riemannXi s)) := by
  filter_upwards [eventually_deriv_log_riemannXi_eq] with s hs
  rw [hs]

theorem liCoefficientCandidate_one_eq_deriv_logDeriv :
    liCoefficientCandidate 1 =
      deriv (fun s : ℂ ↦ log (riemannXi s) + s * logDeriv riemannXi s) 1 := by
  rw [liCoefficientCandidate_one_eq_deriv_productRule]
  exact Filter.EventuallyEq.deriv_eq eventually_productRule_eq_logDeriv

theorem liCoefficientCandidate_one_eq_deriv_logDeriv_fraction :
    liCoefficientCandidate 1 =
      deriv (fun s : ℂ ↦ log (riemannXi s) +
        s * (deriv riemannXi s / riemannXi s)) 1 := by
  rw [liCoefficientCandidate_one_eq_deriv_productRule]
  exact Filter.EventuallyEq.deriv_eq eventually_productRule_eq_logDeriv_fraction

theorem analyticAt_deriv_riemannXi_one :
    AnalyticAt ℂ (deriv riemannXi) 1 :=
  (analyticAt_riemannXi 1).deriv

theorem differentiableAt_deriv_riemannXi_one :
    DifferentiableAt ℂ (deriv riemannXi) 1 :=
  analyticAt_deriv_riemannXi_one.differentiableAt

theorem differentiableAt_logDeriv_riemannXi_one :
    DifferentiableAt ℂ (logDeriv riemannXi) 1 := by
  unfold logDeriv
  exact differentiableAt_deriv_riemannXi_one.div
    (differentiable_riemannXi 1) riemannXi_one_ne_zero

theorem differentiableAt_id_mul_logDeriv_riemannXi_one :
    DifferentiableAt ℂ (fun s : ℂ ↦ s * logDeriv riemannXi s) 1 :=
  differentiableAt_fun_id.mul differentiableAt_logDeriv_riemannXi_one

theorem deriv_id_mul_logDeriv_riemannXi_one :
    deriv (fun s : ℂ ↦ s * logDeriv riemannXi s) 1 =
      logDeriv riemannXi 1 + deriv (logDeriv riemannXi) 1 := by
  rw [deriv_fun_mul]
  · simp
  · exact differentiableAt_fun_id
  · exact differentiableAt_logDeriv_riemannXi_one

theorem liCoefficientCandidate_one_eq_two_logDeriv_add_deriv_logDeriv :
    liCoefficientCandidate 1 =
      logDeriv riemannXi 1 + (logDeriv riemannXi 1 + deriv (logDeriv riemannXi) 1) := by
  rw [liCoefficientCandidate_one_eq_deriv_logDeriv]
  rw [deriv_fun_add]
  · rw [deriv_id_mul_logDeriv_riemannXi_one]
    rw [deriv_log_riemannXi_one, logDeriv_apply]
  · exact differentiableAt_log_riemannXi_one
  · exact differentiableAt_id_mul_logDeriv_riemannXi_one

theorem logDeriv_riemannXi_one_eq_liCoefficientCandidate_zero :
    logDeriv riemannXi 1 = liCoefficientCandidate 0 := by
  rw [liCoefficientCandidate_zero_eq_logDeriv, logDeriv_apply]

theorem liCoefficientCandidate_one_eq_zero_add_deriv_logDeriv :
    liCoefficientCandidate 1 =
      liCoefficientCandidate 0 +
        (liCoefficientCandidate 0 + deriv (logDeriv riemannXi) 1) := by
  rw [liCoefficientCandidate_one_eq_two_logDeriv_add_deriv_logDeriv]
  rw [logDeriv_riemannXi_one_eq_liCoefficientCandidate_zero]

theorem deriv_logDeriv_riemannXi_one :
    deriv (logDeriv riemannXi) 1 =
      (deriv (deriv riemannXi) 1 * riemannXi 1 -
        deriv riemannXi 1 * deriv riemannXi 1) / riemannXi 1 ^ 2 := by
  unfold logDeriv
  rw [deriv_div]
  · exact differentiableAt_deriv_riemannXi_one
  · exact differentiable_riemannXi 1
  · exact riemannXi_one_ne_zero

theorem liCoefficientCandidate_one_eq_zero_add_logDeriv_quotient :
    liCoefficientCandidate 1 =
      liCoefficientCandidate 0 +
        (liCoefficientCandidate 0 +
          (deriv (deriv riemannXi) 1 * riemannXi 1 -
            deriv riemannXi 1 * deriv riemannXi 1) / riemannXi 1 ^ 2) := by
  rw [liCoefficientCandidate_one_eq_zero_add_deriv_logDeriv]
  rw [deriv_logDeriv_riemannXi_one]

theorem deriv_logDeriv_riemannXi_one_eq_secondDeriv :
    deriv (logDeriv riemannXi) 1 =
      2 * deriv (deriv riemannXi) 1 - completedRiemannZeta₀ 1 ^ 2 := by
  rw [deriv_logDeriv_riemannXi_one, riemannXi_one, deriv_riemannXi_one]
  ring

theorem liCoefficientCandidate_one_eq_zero_add_secondDeriv :
    liCoefficientCandidate 1 =
      liCoefficientCandidate 0 +
        (liCoefficientCandidate 0 +
          (2 * deriv (deriv riemannXi) 1 - completedRiemannZeta₀ 1 ^ 2)) := by
  rw [liCoefficientCandidate_one_eq_zero_add_deriv_logDeriv]
  rw [deriv_logDeriv_riemannXi_one_eq_secondDeriv]

theorem logDeriv_riemannXi_eq (s : ℂ) :
    logDeriv riemannXi s =
      ((s - 1 / 2) * completedRiemannZeta₀ s +
        (s * (s - 1) / 2) * deriv completedRiemannZeta₀ s) / riemannXi s := by
  rw [logDeriv_apply, deriv_riemannXi]

theorem eventually_logDeriv_riemannXi_eq :
    (fun s : ℂ ↦ log (riemannXi s) + s * logDeriv riemannXi s)
      =ᶠ[𝓝 (1 : ℂ)]
    (fun s : ℂ ↦ log (riemannXi s) +
      s * (((s - 1 / 2) * completedRiemannZeta₀ s +
        (s * (s - 1) / 2) * deriv completedRiemannZeta₀ s) / riemannXi s)) := by
  exact Filter.Eventually.of_forall fun s => by
    change log (riemannXi s) + s * logDeriv riemannXi s =
      log (riemannXi s) +
        s * (((s - 1 / 2) * completedRiemannZeta₀ s +
          (s * (s - 1) / 2) * deriv completedRiemannZeta₀ s) / riemannXi s)
    rw [logDeriv_riemannXi_eq]

theorem liCoefficientCandidate_one_eq_deriv_expandedLogDeriv :
    liCoefficientCandidate 1 =
      deriv (fun s : ℂ ↦ log (riemannXi s) +
        s * (((s - 1 / 2) * completedRiemannZeta₀ s +
          (s * (s - 1) / 2) * deriv completedRiemannZeta₀ s) / riemannXi s)) 1 := by
  rw [liCoefficientCandidate_one_eq_deriv_logDeriv]
  exact Filter.EventuallyEq.deriv_eq eventually_logDeriv_riemannXi_eq

theorem liCoefficientCandidate_zero_eq_completedZeta₀ :
    liCoefficientCandidate 0 = completedRiemannZeta₀ 1 := by
  rw [liCoefficientCandidate_zero_eq_logDeriv, deriv_riemannXi_one, riemannXi_one]
  ring

theorem liCoefficientCandidate_zero_eq_completedZeta₀_zero :
    liCoefficientCandidate 0 = completedRiemannZeta₀ 0 := by
  rw [liCoefficientCandidate_zero_eq_completedZeta₀, completedRiemannZeta₀_zero_eq_one]

theorem liCoefficientCandidate_one_eq_completedZeta₀_deriv :
    liCoefficientCandidate 1 =
      4 * completedRiemannZeta₀ 1 +
        2 * deriv completedRiemannZeta₀ 1 - completedRiemannZeta₀ 1 ^ 2 := by
  rw [liCoefficientCandidate_one_eq_zero_add_secondDeriv,
    liCoefficientCandidate_zero_eq_completedZeta₀, deriv_deriv_riemannXi_one]
  ring

theorem liCoefficientCandidate_one_eq_completedZeta₀_neg_deriv_zero :
    liCoefficientCandidate 1 =
      4 * completedRiemannZeta₀ 1 -
        2 * deriv completedRiemannZeta₀ 0 - completedRiemannZeta₀ 1 ^ 2 := by
  rw [liCoefficientCandidate_one_eq_completedZeta₀_deriv,
    deriv_completedRiemannZeta₀_one_eq_neg_zero]
  ring

theorem liCoefficientCandidate_one_eq_completedZeta₀_zero_neg_deriv_zero :
    liCoefficientCandidate 1 =
      4 * completedRiemannZeta₀ 0 -
        2 * deriv completedRiemannZeta₀ 0 - completedRiemannZeta₀ 0 ^ 2 := by
  rw [liCoefficientCandidate_one_eq_completedZeta₀_neg_deriv_zero,
    completedRiemannZeta₀_zero_eq_one]

theorem liCoefficientCandidate_one_eq_zero_neg_deriv_zero :
    liCoefficientCandidate 1 =
      4 * liCoefficientCandidate 0 -
        2 * deriv completedRiemannZeta₀ 0 - liCoefficientCandidate 0 ^ 2 := by
  rw [liCoefficientCandidate_one_eq_completedZeta₀_zero_neg_deriv_zero,
    liCoefficientCandidate_zero_eq_completedZeta₀_zero]

theorem liCoefficientCandidate_one_eq_zero_mul_sub_deriv_zero :
    liCoefficientCandidate 1 =
      liCoefficientCandidate 0 * (4 - liCoefficientCandidate 0) -
        2 * deriv completedRiemannZeta₀ 0 := by
  rw [liCoefficientCandidate_one_eq_zero_neg_deriv_zero]
  ring

theorem liCoefficientCandidate_zero_eq_eulerMascheroni :
    liCoefficientCandidate 0 =
      ((Real.eulerMascheroniConstant : ℂ) - Complex.log (4 * (Real.pi : ℂ))) / 2 + 1 := by
  rw [liCoefficientCandidate_zero_eq_completedZeta₀, completedRiemannZeta₀_one]

theorem liCoefficientCandidate_one_eq_eulerMascheroni_neg_deriv_zero :
    liCoefficientCandidate 1 =
      4 * (((Real.eulerMascheroniConstant : ℂ) - Complex.log (4 * (Real.pi : ℂ))) / 2 + 1) -
        2 * deriv completedRiemannZeta₀ 0 -
          (((Real.eulerMascheroniConstant : ℂ) - Complex.log (4 * (Real.pi : ℂ))) / 2 + 1) ^ 2 := by
  rw [liCoefficientCandidate_one_eq_completedZeta₀_neg_deriv_zero, completedRiemannZeta₀_one]

theorem liCoefficientCandidate_zero_eq_ofReal :
    liCoefficientCandidate 0 =
      (((Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2 + 1 : ℝ) : ℂ) := by
  rw [liCoefficientCandidate_zero_eq_eulerMascheroni]
  have harg : 4 * (Real.pi : ℂ) = ((4 * Real.pi : ℝ) : ℂ) := by
    norm_num
  rw [harg]
  rw [← Complex.ofReal_log (show 0 ≤ 4 * Real.pi by positivity)]
  norm_num

theorem liCoefficientCandidate_zero_im_eq_zero :
    (liCoefficientCandidate 0).im = 0 := by
  rw [liCoefficientCandidate_zero_eq_ofReal]
  simp

theorem liCoefficientCandidate_one_im_eq_neg_two_deriv_completedZeta₀_zero_im :
    (liCoefficientCandidate 1).im = -2 * (deriv completedRiemannZeta₀ 0).im := by
  rw [liCoefficientCandidate_one_eq_zero_mul_sub_deriv_zero]
  have hzero : (liCoefficientCandidate 0).im = 0 :=
    liCoefficientCandidate_zero_im_eq_zero
  simp [Complex.mul_im, hzero]

theorem liCoefficientCandidate_one_re_eq_zero_re_deriv_completedZeta₀_zero_re :
    (liCoefficientCandidate 1).re =
      (liCoefficientCandidate 0).re * (4 - (liCoefficientCandidate 0).re) -
        2 * (deriv completedRiemannZeta₀ 0).re := by
  rw [liCoefficientCandidate_one_eq_zero_mul_sub_deriv_zero]
  have hzero : (liCoefficientCandidate 0).im = 0 :=
    liCoefficientCandidate_zero_im_eq_zero
  simp [Complex.mul_re, hzero]

theorem deriv_zero_im_eq_zero_of_conj_conj_eq_self (f : ℂ → ℂ)
    (hconj : ((starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ)) = f) :
    (deriv f 0).im = 0 := by
  have hderiv :
      deriv f 0 = (starRingEnd ℂ) (deriv f 0) := by
    calc
      deriv f 0 = deriv ((starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ)) 0 := by
        rw [hconj]
      _ = ((starRingEnd ℂ) ∘ deriv f ∘ (starRingEnd ℂ)) 0 := by
        simpa [Function.comp_def] using
          congrFun (deriv_conj_conj (f := f)) (0 : ℂ)
      _ = (starRingEnd ℂ) (deriv f 0) := by
        simp
  exact conj_eq_iff_im.mp hderiv.symm

theorem value_im_eq_zero_of_conj_conj_eq_self_at_fixed (f : ℂ → ℂ) {x : ℂ}
    (hconj : ((starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ)) = f)
    (hx : (starRingEnd ℂ) x = x) :
    (f x).im = 0 := by
  have h : (starRingEnd ℂ) (f x) = f x := by
    calc
      (starRingEnd ℂ) (f x) =
          (((starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ)) x) := by
        simp [Function.comp_def, hx]
      _ = f x := by rw [hconj]
  exact conj_eq_iff_im.mp h

theorem deriv_conj_conj_eq_self (f : ℂ → ℂ)
    (hconj : ((starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ)) = f) :
    ((starRingEnd ℂ) ∘ deriv f ∘ (starRingEnd ℂ)) = deriv f := by
  funext s
  calc
    (((starRingEnd ℂ) ∘ deriv f ∘ (starRingEnd ℂ)) s) =
        deriv (((starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ))) s := by
      simpa [Function.comp_def] using
        (congrFun (deriv_conj_conj (f := f)).symm s)
    _ = deriv f s := by rw [hconj]

theorem complex_half_star :
    (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
  norm_num [starRingEnd_apply]

theorem deriv_completedRiemannZeta₀_zero_im_eq_zero_of_conj_conj
    (hconj :
      ((starRingEnd ℂ) ∘ completedRiemannZeta₀ ∘ (starRingEnd ℂ)) =
        completedRiemannZeta₀) :
    (deriv completedRiemannZeta₀ 0).im = 0 :=
  deriv_zero_im_eq_zero_of_conj_conj_eq_self completedRiemannZeta₀ hconj

theorem liCoefficientCandidate_one_im_eq_zero_of_completedZeta₀_conj_conj
    (hconj :
      ((starRingEnd ℂ) ∘ completedRiemannZeta₀ ∘ (starRingEnd ℂ)) =
        completedRiemannZeta₀) :
    (liCoefficientCandidate 1).im = 0 := by
  rw [liCoefficientCandidate_one_im_eq_neg_two_deriv_completedZeta₀_zero_im]
  rw [deriv_completedRiemannZeta₀_zero_im_eq_zero_of_conj_conj hconj]
  norm_num

theorem mellin_conj_of_forall_mem_Ioi (f : ℝ → ℂ)
    (hreal : ∀ x ∈ Ioi (0 : ℝ), (starRingEnd ℂ) (f x) = f x) (s : ℂ) :
    mellin f ((starRingEnd ℂ) s) = (starRingEnd ℂ) (mellin f s) := by
  unfold mellin
  rw [← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro x hx
  have hpow :
      (x : ℂ) ^ ((starRingEnd ℂ) s - 1) =
        (starRingEnd ℂ) ((x : ℂ) ^ (s - 1)) := by
    have harg : (x : ℂ).arg ≠ π := by
      simp [Complex.arg_ofReal_of_nonneg hx.le, ne_of_lt Real.pi_pos]
    calc
      (x : ℂ) ^ ((starRingEnd ℂ) s - 1)
          = (x : ℂ) ^ ((starRingEnd ℂ) (s - 1)) := by simp
      _ = (starRingEnd ℂ) (((starRingEnd ℂ) (x : ℂ)) ^ (s - 1)) := by
        rw [Complex.cpow_conj (x : ℂ) (s - 1) harg]
      _ = (starRingEnd ℂ) ((x : ℂ) ^ (s - 1)) := by simp
  simp [smul_eq_mul, hpow, hreal x hx]

theorem hurwitzEvenFEPair_zero_f_modif_conj (x : ℝ) :
    (starRingEnd ℂ) ((hurwitzEvenFEPair 0).f_modif x) =
      (hurwitzEvenFEPair 0).f_modif x := by
  unfold WeakFEPair.f_modif
  by_cases h1 : x ∈ Ioi (1 : ℝ)
  · by_cases h2 : x ∈ Ioo (0 : ℝ) 1
    · simp [h1, h2, hurwitzEvenFEPair]
    · simp [h1, h2, hurwitzEvenFEPair]
  · by_cases h2 : x ∈ Ioo (0 : ℝ) 1
    · simp [h1, h2, hurwitzEvenFEPair]
    · simp [h1, h2, hurwitzEvenFEPair]

theorem hurwitzEvenFEPair_zero_f_modif_of_one_lt {x : ℝ} (hx : 1 < x) :
    (hurwitzEvenFEPair 0).f_modif x = (evenKernel 0 x : ℂ) - 1 := by
  unfold WeakFEPair.f_modif hurwitzEvenFEPair
  simp [mem_Ioi.mpr hx, notMem_Ioo_of_ge hx.le]

theorem hasSum_int_hurwitzEvenFEPair_zero_f_modif_of_one_lt {x : ℝ} (hx : 1 < x) :
    HasSum (fun n : ℤ ↦ if n = 0 then 0 else rexp (-π * (n : ℝ) ^ 2 * x))
      ((hurwitzEvenFEPair 0).f_modif x).re := by
  rw [hurwitzEvenFEPair_zero_f_modif_of_one_lt hx]
  simpa using (hasSum_int_evenKernel₀ 0 (zero_lt_one.trans hx))

theorem hurwitzEvenFEPair_zero_f_modif_re_nonneg_of_one_lt {x : ℝ} (hx : 1 < x) :
    0 ≤ ((hurwitzEvenFEPair 0).f_modif x).re := by
  rw [← (hasSum_int_hurwitzEvenFEPair_zero_f_modif_of_one_lt hx).tsum_eq]
  exact tsum_nonneg fun n => by
    by_cases hn : n = 0
    · simp only [hn, ↓reduceIte, le_refl]
    · simp only [hn, ↓reduceIte]
      exact (exp_pos _).le

theorem hurwitzEvenFEPair_zero_f_modif_of_pos_lt_one {x : ℝ} (h0 : 0 < x)
    (h1 : x < 1) :
    (hurwitzEvenFEPair 0).f_modif x =
      (evenKernel 0 x : ℂ) - ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  unfold WeakFEPair.f_modif hurwitzEvenFEPair
  simp [notMem_Ioi.mpr h1.le, mem_Ioo.mpr ⟨h0, h1⟩]

theorem hurwitzEvenFEPair_zero_f_modif_of_pos_lt_one_eq_scaled_cosKernel {x : ℝ}
    (h0 : 0 < x) (h1 : x < 1) :
    (hurwitzEvenFEPair 0).f_modif x =
      ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ((cosKernel 0 (1 / x) : ℂ) - 1) := by
  rw [hurwitzEvenFEPair_zero_f_modif_of_pos_lt_one h0 h1]
  rw [evenKernel_functional_equation 0 x]
  rw [rpow_neg h0.le]
  push_cast
  ring

theorem hasSum_nat_hurwitzEvenFEPair_zero_f_modif_of_pos_lt_one {x : ℝ}
    (h0 : 0 < x) (h1 : x < 1) :
    HasSum
      (fun n : ℕ ↦ x ^ (-(1 / 2 : ℝ)) *
        (2 * rexp (-π * ((n + 1 : ℕ) : ℝ) ^ 2 * (1 / x))))
      ((hurwitzEvenFEPair 0).f_modif x).re := by
  rw [hurwitzEvenFEPair_zero_f_modif_of_pos_lt_one_eq_scaled_cosKernel h0 h1]
  have hsum := (hasSum_nat_cosKernel₀ 0 (one_div_pos.mpr h0)).mul_left
    (x ^ (-(1 / 2 : ℝ)))
  simpa [mul_assoc] using hsum

theorem hurwitzEvenFEPair_zero_f_modif_re_nonneg_of_pos_lt_one {x : ℝ}
    (h0 : 0 < x) (h1 : x < 1) :
    0 ≤ ((hurwitzEvenFEPair 0).f_modif x).re := by
  rw [← (hasSum_nat_hurwitzEvenFEPair_zero_f_modif_of_pos_lt_one h0 h1).tsum_eq]
  exact tsum_nonneg fun n => by
    positivity

theorem hurwitzEvenFEPair_zero_f_modif_one :
    (hurwitzEvenFEPair 0).f_modif 1 = 0 := by
  unfold WeakFEPair.f_modif hurwitzEvenFEPair
  simp

theorem hurwitzEvenFEPair_zero_f_modif_re_nonneg_of_pos {x : ℝ} (hx : 0 < x) :
    0 ≤ ((hurwitzEvenFEPair 0).f_modif x).re := by
  rcases lt_trichotomy x 1 with hlt | rfl | hgt
  · exact hurwitzEvenFEPair_zero_f_modif_re_nonneg_of_pos_lt_one hx hlt
  · rw [hurwitzEvenFEPair_zero_f_modif_one]
    norm_num
  · exact hurwitzEvenFEPair_zero_f_modif_re_nonneg_of_one_lt hgt

theorem hurwitzEvenFEPair_zero_Λ₀_conj (s : ℂ) :
    (hurwitzEvenFEPair 0).Λ₀ ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) ((hurwitzEvenFEPair 0).Λ₀ s) := by
  unfold WeakFEPair.Λ₀
  exact mellin_conj_of_forall_mem_Ioi (hurwitzEvenFEPair 0).f_modif
    (fun x _ => hurwitzEvenFEPair_zero_f_modif_conj x) s

theorem completedRiemannZeta₀_conj (s : ℂ) :
    completedRiemannZeta₀ ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (completedRiemannZeta₀ s) := by
  unfold completedRiemannZeta₀ completedHurwitzZetaEven₀
  have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := by
    rw [starRingEnd_apply, star_ofNat]
  have hdiv : (starRingEnd ℂ) s / 2 = (starRingEnd ℂ) (s / 2) := by
    rw [map_div₀, htwo]
  rw [hdiv]
  rw [hurwitzEvenFEPair_zero_Λ₀_conj]
  rw [map_div₀, htwo]

theorem completedRiemannZeta₀_conj_conj :
    ((starRingEnd ℂ) ∘ completedRiemannZeta₀ ∘ (starRingEnd ℂ)) =
      completedRiemannZeta₀ := by
  funext s
  simp [Function.comp_def, completedRiemannZeta₀_conj]

theorem deriv_completedRiemannZeta₀_conj_conj :
    ((starRingEnd ℂ) ∘ deriv completedRiemannZeta₀ ∘ (starRingEnd ℂ)) =
      deriv completedRiemannZeta₀ :=
  deriv_conj_conj_eq_self completedRiemannZeta₀ completedRiemannZeta₀_conj_conj

theorem deriv_deriv_completedRiemannZeta₀_conj_conj :
    ((starRingEnd ℂ) ∘ deriv (deriv completedRiemannZeta₀) ∘ (starRingEnd ℂ)) =
      deriv (deriv completedRiemannZeta₀) :=
  deriv_conj_conj_eq_self (deriv completedRiemannZeta₀)
    deriv_completedRiemannZeta₀_conj_conj

theorem completedRiemannZeta₀_half_im_eq_zero :
    (completedRiemannZeta₀ (1 / 2)).im = 0 :=
  value_im_eq_zero_of_conj_conj_eq_self_at_fixed
    completedRiemannZeta₀ completedRiemannZeta₀_conj_conj complex_half_star

theorem deriv_deriv_completedRiemannZeta₀_half_im_eq_zero :
    (deriv (deriv completedRiemannZeta₀) (1 / 2)).im = 0 :=
  value_im_eq_zero_of_conj_conj_eq_self_at_fixed
    (deriv (deriv completedRiemannZeta₀))
    deriv_deriv_completedRiemannZeta₀_conj_conj complex_half_star

theorem completedRiemannZeta₀_half_eq_ofReal_re :
    completedRiemannZeta₀ (1 / 2) =
      ((completedRiemannZeta₀ (1 / 2)).re : ℂ) := by
  apply Complex.ext
  · simp
  · exact value_im_eq_zero_of_conj_conj_eq_self_at_fixed
      completedRiemannZeta₀ completedRiemannZeta₀_conj_conj
      (by norm_num [starRingEnd_apply])

theorem deriv_deriv_completedRiemannZeta₀_half_eq_ofReal_re :
    deriv (deriv completedRiemannZeta₀) (1 / 2) =
      ((deriv (deriv completedRiemannZeta₀) (1 / 2)).re : ℂ) := by
  apply Complex.ext
  · simp
  · exact value_im_eq_zero_of_conj_conj_eq_self_at_fixed
      (deriv (deriv completedRiemannZeta₀))
      deriv_deriv_completedRiemannZeta₀_conj_conj
      (by norm_num [starRingEnd_apply])

theorem riemannXi_half_im_eq_zero :
    (riemannXi (1 / 2)).im = 0 := by
  rw [riemannXi_half]
  simp only [one_div, sub_im, inv_im, im_ofNat, neg_zero, normSq_ofNat,
    zero_div, mul_im, inv_re, re_ofNat, div_self_mul_self', zero_mul, add_zero,
    zero_sub, neg_eq_zero, mul_eq_zero, inv_eq_zero, OfNat.ofNat_ne_zero, false_or]
  exact value_im_eq_zero_of_conj_conj_eq_self_at_fixed
    completedRiemannZeta₀ completedRiemannZeta₀_conj_conj
    (by norm_num [starRingEnd_apply])

theorem riemannXi_half_eq_ofReal_re :
    riemannXi (1 / 2) = ((riemannXi (1 / 2)).re : ℂ) := by
  apply Complex.ext
  · simp
  · exact riemannXi_half_im_eq_zero

theorem riemannXi_half_re_eq_completedZeta₀_half_re :
    (riemannXi (1 / 2)).re =
      1 / 2 - (1 / 8) * (completedRiemannZeta₀ (1 / 2)).re := by
  rw [riemannXi_half]
  simp [Complex.sub_re, Complex.mul_re]

theorem riemannXi_half_eq_ofReal_re_formula :
    riemannXi (1 / 2) =
      ((1 / 2 - (1 / 8) * (completedRiemannZeta₀ (1 / 2)).re : ℝ) : ℂ) := by
  rw [riemannXi_half_eq_ofReal_re]
  rw [riemannXi_half_re_eq_completedZeta₀_half_re]

theorem riemannXi_half_re_pos_iff :
    0 < (riemannXi (1 / 2)).re ↔
      0 < 1 / 2 - (1 / 8) * (completedRiemannZeta₀ (1 / 2)).re := by
  rw [riemannXi_half_re_eq_completedZeta₀_half_re]

theorem completedRiemannZeta₀_half_re_eq_riemannXi_half_re :
    (completedRiemannZeta₀ (1 / 2)).re = 4 - 8 * (riemannXi (1 / 2)).re := by
  have h := riemannXi_half_re_eq_completedZeta₀_half_re
  linarith

theorem riemannXi_half_re_pos_iff_completedZeta₀_half_re_lt_four :
    0 < (riemannXi (1 / 2)).re ↔
      (completedRiemannZeta₀ (1 / 2)).re < 4 := by
  rw [riemannXi_half_re_eq_completedZeta₀_half_re]
  constructor <;> intro h <;> linarith

theorem iteratedDeriv_centered_riemannXi_zero_re_pos_iff_completedZeta₀_half_re_lt_four :
    0 < (iteratedDeriv 0 (fun z : ℂ ↦ riemannXi (1 / 2 + z)) 0).re ↔
      (completedRiemannZeta₀ (1 / 2)).re < 4 := by
  rw [iteratedDeriv_centered_riemannXi_zero_eq_half]
  exact riemannXi_half_re_pos_iff_completedZeta₀_half_re_lt_four

theorem completedRiemannZeta₀_half_eq_hurwitzEvenFEPair_Λ₀ :
    completedRiemannZeta₀ (1 / 2) =
      (hurwitzEvenFEPair 0).Λ₀ (1 / 4 : ℂ) / 2 := by
  unfold completedRiemannZeta₀ completedHurwitzZetaEven₀
  ring_nf

theorem completedRiemannZeta₀_half_eq_mellin_hurwitzEvenFEPair_zero :
    completedRiemannZeta₀ (1 / 2) =
      mellin (hurwitzEvenFEPair 0).f_modif (1 / 4 : ℂ) / 2 := by
  rw [completedRiemannZeta₀_half_eq_hurwitzEvenFEPair_Λ₀]
  rfl

theorem completedRiemannZeta₀_half_re_eq_hurwitzEvenFEPair_Λ₀_re :
    (completedRiemannZeta₀ (1 / 2)).re =
      ((hurwitzEvenFEPair 0).Λ₀ (1 / 4 : ℂ)).re / 2 := by
  rw [completedRiemannZeta₀_half_eq_hurwitzEvenFEPair_Λ₀]
  simp

theorem completedRiemannZeta₀_half_re_eq_mellin_hurwitzEvenFEPair_zero_re :
    (completedRiemannZeta₀ (1 / 2)).re =
      (mellin (hurwitzEvenFEPair 0).f_modif (1 / 4 : ℂ)).re / 2 := by
  rw [completedRiemannZeta₀_half_eq_mellin_hurwitzEvenFEPair_zero]
  simp

theorem riemannXi_half_re_pos_iff_hurwitzEvenFEPair_Λ₀_re_lt_eight :
    0 < (riemannXi (1 / 2)).re ↔
      ((hurwitzEvenFEPair 0).Λ₀ (1 / 4 : ℂ)).re < 8 := by
  rw [riemannXi_half_re_pos_iff_completedZeta₀_half_re_lt_four]
  rw [completedRiemannZeta₀_half_re_eq_hurwitzEvenFEPair_Λ₀_re]
  constructor <;> intro h <;> linarith

theorem riemannXi_half_re_pos_iff_mellin_hurwitzEvenFEPair_zero_re_lt_eight :
    0 < (riemannXi (1 / 2)).re ↔
      (mellin (hurwitzEvenFEPair 0).f_modif (1 / 4 : ℂ)).re < 8 := by
  rw [riemannXi_half_re_pos_iff_completedZeta₀_half_re_lt_four]
  rw [completedRiemannZeta₀_half_re_eq_mellin_hurwitzEvenFEPair_zero_re]
  constructor <;> intro h <;> linarith

theorem ofReal_cpow_quarter_sub_one {x : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ ((1 / 4 : ℂ) - 1) =
      ((x ^ (-(3 / 4 : ℝ)) : ℝ) : ℂ) := by
  have hexp : ((1 / 4 : ℂ) - 1) = ((-(3 / 4 : ℝ) : ℝ) : ℂ) := by
    norm_num
  rw [hexp, ofReal_cpow hx.le]

theorem mellin_hurwitzEvenFEPair_zero_quarter_integrand_re_eq {x : ℝ} (hx : 0 < x) :
    (((x : ℂ) ^ ((1 / 4 : ℂ) - 1)) • (hurwitzEvenFEPair 0).f_modif x).re =
      x ^ (-(3 / 4 : ℝ)) * ((hurwitzEvenFEPair 0).f_modif x).re := by
  rw [ofReal_cpow_quarter_sub_one hx]
  simp [smul_eq_mul, Complex.mul_re]

theorem mellin_hurwitzEvenFEPair_zero_quarter_integrand_re_nonneg {x : ℝ}
    (hx : 0 < x) :
    0 ≤ (((x : ℂ) ^ ((1 / 4 : ℂ) - 1)) • (hurwitzEvenFEPair 0).f_modif x).re := by
  rw [mellin_hurwitzEvenFEPair_zero_quarter_integrand_re_eq hx]
  exact mul_nonneg (rpow_nonneg hx.le _) (hurwitzEvenFEPair_zero_f_modif_re_nonneg_of_pos hx)

theorem mellin_hurwitzEvenFEPair_zero_quarter_re_eq_integral :
    (mellin (hurwitzEvenFEPair 0).f_modif (1 / 4 : ℂ)).re =
      ∫ x : ℝ in Ioi 0,
        (((x : ℂ) ^ ((1 / 4 : ℂ) - 1)) • (hurwitzEvenFEPair 0).f_modif x).re := by
  have hM : HasMellin (hurwitzEvenFEPair 0).f_modif (1 / 4 : ℂ)
      ((hurwitzEvenFEPair 0).Λ₀ (1 / 4 : ℂ)) := by
    unfold WeakFEPair.Λ₀
    exact (hurwitzEvenFEPair 0).toStrongFEPair.hasMellin (1 / 4 : ℂ)
  unfold mellin
  change RCLike.re (∫ t : ℝ in Ioi 0,
      (t : ℂ) ^ ((1 / 4 : ℂ) - 1) • (hurwitzEvenFEPair 0).f_modif t) =
    ∫ x : ℝ in Ioi 0,
      RCLike.re (((x : ℂ) ^ ((1 / 4 : ℂ) - 1)) • (hurwitzEvenFEPair 0).f_modif x)
  rw [← integral_re hM.1]

theorem mellin_hurwitzEvenFEPair_zero_quarter_re_nonneg :
    0 ≤ (mellin (hurwitzEvenFEPair 0).f_modif (1 / 4 : ℂ)).re := by
  rw [mellin_hurwitzEvenFEPair_zero_quarter_re_eq_integral]
  exact setIntegral_nonneg measurableSet_Ioi fun x hx =>
    mellin_hurwitzEvenFEPair_zero_quarter_integrand_re_nonneg hx

theorem hurwitzEvenFEPair_zero_Λ₀_quarter_re_nonneg :
    0 ≤ ((hurwitzEvenFEPair 0).Λ₀ (1 / 4 : ℂ)).re := by
  unfold WeakFEPair.Λ₀
  exact mellin_hurwitzEvenFEPair_zero_quarter_re_nonneg

theorem completedRiemannZeta₀_half_re_nonneg :
    0 ≤ (completedRiemannZeta₀ (1 / 2)).re := by
  rw [completedRiemannZeta₀_half_re_eq_mellin_hurwitzEvenFEPair_zero_re]
  linarith [mellin_hurwitzEvenFEPair_zero_quarter_re_nonneg]

theorem riemannXi_half_re_le_one_half :
    (riemannXi (1 / 2)).re ≤ 1 / 2 := by
  rw [riemannXi_half_re_eq_completedZeta₀_half_re]
  linarith [completedRiemannZeta₀_half_re_nonneg]

theorem hasSum_nat_hurwitzEvenFEPair_zero_f_modif_of_one_lt {x : ℝ} (hx : 1 < x) :
    HasSum (fun n : ℕ ↦ 2 * rexp (-π * ((n + 1 : ℕ) : ℝ) ^ 2 * x))
      ((hurwitzEvenFEPair 0).f_modif x).re := by
  rw [hurwitzEvenFEPair_zero_f_modif_of_one_lt hx]
  rw [show ((evenKernel 0 x : ℂ) - 1).re = cosKernel 0 x - 1 by
    rw [evenKernel_eq_cosKernel_of_zero]
    simp]
  simpa using (hasSum_nat_cosKernel₀ 0 (zero_lt_one.trans hx))

theorem hurwitzEvenFEPair_zero_f_modif_re_eq_two_F_nat_one_of_one_lt {x : ℝ}
    (hx : 1 < x) :
    ((hurwitzEvenFEPair 0).f_modif x).re =
      2 * HurwitzKernelBounds.F_nat 0 1 x := by
  rw [← (hasSum_nat_hurwitzEvenFEPair_zero_f_modif_of_one_lt hx).tsum_eq]
  rw [HurwitzKernelBounds.F_nat]
  simp [HurwitzKernelBounds.f_nat, tsum_mul_left]

theorem hurwitzEvenFEPair_zero_f_modif_re_le_exp_tail_of_one_lt {x : ℝ}
    (hx : 1 < x) :
    ((hurwitzEvenFEPair 0).f_modif x).re ≤
      2 * (rexp (-π * x) / (1 - rexp (-π * x))) := by
  rw [hurwitzEvenFEPair_zero_f_modif_re_eq_two_F_nat_one_of_one_lt hx]
  have hbound := HurwitzKernelBounds.F_nat_zero_le (a := 1) zero_le_one
    (zero_lt_one.trans hx)
  have hle :
      HurwitzKernelBounds.F_nat 0 1 x ≤ rexp (-π * x) / (1 - rexp (-π * x)) := by
    calc
      HurwitzKernelBounds.F_nat 0 1 x ≤ ‖HurwitzKernelBounds.F_nat 0 1 x‖ :=
        le_abs_self _
      _ ≤ rexp (-π * 1 ^ 2 * x) / (1 - rexp (-π * x)) := hbound
      _ = rexp (-π * x) / (1 - rexp (-π * x)) := by ring_nf
  nlinarith

theorem mellin_quarter_integrand_re_le_exp_tail_of_one_lt {x : ℝ} (hx : 1 < x) :
    (((x : ℂ) ^ ((1 / 4 : ℂ) - 1)) • (hurwitzEvenFEPair 0).f_modif x).re ≤
      x ^ (-(3 / 4 : ℝ)) * (2 * (rexp (-π * x) / (1 - rexp (-π * x)))) := by
  rw [mellin_hurwitzEvenFEPair_zero_quarter_integrand_re_eq (zero_lt_one.trans hx)]
  exact mul_le_mul_of_nonneg_left
    (hurwitzEvenFEPair_zero_f_modif_re_le_exp_tail_of_one_lt hx)
    (rpow_nonneg (le_of_lt (zero_lt_one.trans hx)) _)

theorem hurwitzEvenFEPair_zero_f_modif_re_eq_scaled_two_F_nat_one_of_pos_lt_one
    {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    ((hurwitzEvenFEPair 0).f_modif x).re =
      x ^ (-(1 / 2 : ℝ)) * (2 * HurwitzKernelBounds.F_nat 0 1 (1 / x)) := by
  rw [← (hasSum_nat_hurwitzEvenFEPair_zero_f_modif_of_pos_lt_one h0 h1).tsum_eq]
  rw [HurwitzKernelBounds.F_nat]
  simp [HurwitzKernelBounds.f_nat, tsum_mul_left, mul_assoc]

theorem hurwitzEvenFEPair_zero_f_modif_re_le_exp_tail_of_pos_lt_one {x : ℝ}
    (h0 : 0 < x) (h1 : x < 1) :
    ((hurwitzEvenFEPair 0).f_modif x).re ≤
      x ^ (-(1 / 2 : ℝ)) *
        (2 * (rexp (-π * (1 / x)) / (1 - rexp (-π * (1 / x))))) := by
  rw [hurwitzEvenFEPair_zero_f_modif_re_eq_scaled_two_F_nat_one_of_pos_lt_one h0 h1]
  have hxinv : 0 < 1 / x := one_div_pos.mpr h0
  have hbound := HurwitzKernelBounds.F_nat_zero_le (a := 1) zero_le_one hxinv
  have hle :
      HurwitzKernelBounds.F_nat 0 1 (1 / x) ≤
        rexp (-π * (1 / x)) / (1 - rexp (-π * (1 / x))) := by
    calc
      HurwitzKernelBounds.F_nat 0 1 (1 / x) ≤
          ‖HurwitzKernelBounds.F_nat 0 1 (1 / x)‖ := le_abs_self _
      _ ≤ rexp (-π * 1 ^ 2 * (1 / x)) / (1 - rexp (-π * (1 / x))) := hbound
      _ = rexp (-π * (1 / x)) / (1 - rexp (-π * (1 / x))) := by ring_nf
  exact mul_le_mul_of_nonneg_left (by nlinarith) (rpow_nonneg h0.le _)

theorem mellin_quarter_integrand_re_le_exp_tail_of_pos_lt_one {x : ℝ}
    (h0 : 0 < x) (h1 : x < 1) :
    (((x : ℂ) ^ ((1 / 4 : ℂ) - 1)) • (hurwitzEvenFEPair 0).f_modif x).re ≤
      x ^ (-(3 / 4 : ℝ)) *
        (x ^ (-(1 / 2 : ℝ)) *
          (2 * (rexp (-π * (1 / x)) / (1 - rexp (-π * (1 / x)))))) := by
  rw [mellin_hurwitzEvenFEPair_zero_quarter_integrand_re_eq h0]
  exact mul_le_mul_of_nonneg_left
    (hurwitzEvenFEPair_zero_f_modif_re_le_exp_tail_of_pos_lt_one h0 h1)
    (rpow_nonneg h0.le _)

theorem mellin_hurwitzEvenFEPair_zero_quarter_re_eq_integral_split :
    (mellin (hurwitzEvenFEPair 0).f_modif (1 / 4 : ℂ)).re =
      (∫ x : ℝ in Ioo 0 1,
        (((x : ℂ) ^ ((1 / 4 : ℂ) - 1)) • (hurwitzEvenFEPair 0).f_modif x).re) +
      ∫ x : ℝ in Ioi 1,
        (((x : ℂ) ^ ((1 / 4 : ℂ) - 1)) • (hurwitzEvenFEPair 0).f_modif x).re := by
  let g : ℝ → ℝ := fun x =>
    (((x : ℂ) ^ ((1 / 4 : ℂ) - 1)) • (hurwitzEvenFEPair 0).f_modif x).re
  have hM : HasMellin (hurwitzEvenFEPair 0).f_modif (1 / 4 : ℂ)
      ((hurwitzEvenFEPair 0).Λ₀ (1 / 4 : ℂ)) := by
    unfold WeakFEPair.Λ₀
    exact (hurwitzEvenFEPair 0).toStrongFEPair.hasMellin (1 / 4 : ℂ)
  have hgInt : IntegrableOn g (Ioi (0 : ℝ)) := by
    change IntegrableOn (fun x : ℝ =>
      (((x : ℂ) ^ ((1 / 4 : ℂ) - 1)) • (hurwitzEvenFEPair 0).f_modif x).re)
      (Ioi (0 : ℝ))
    exact hM.1.re
  rw [mellin_hurwitzEvenFEPair_zero_quarter_re_eq_integral]
  change ∫ x : ℝ in Ioi 0, g x =
    (∫ x : ℝ in Ioo 0 1, g x) + ∫ x : ℝ in Ioi 1, g x
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  rw [setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hgInt.mono_set (by intro x hx; exact Ioc_subset_Ioi_self hx))
    (hgInt.mono_set (by intro x hx; exact zero_lt_one.trans (by simpa using hx)))]
  rw [integral_Ioc_eq_integral_Ioo]

theorem mellin_quarter_integral_Ioo_zero_one_nonneg :
    0 ≤ ∫ x : ℝ in Ioo 0 1,
      (((x : ℂ) ^ ((1 / 4 : ℂ) - 1)) • (hurwitzEvenFEPair 0).f_modif x).re := by
  exact setIntegral_nonneg measurableSet_Ioo fun x hx =>
    mellin_hurwitzEvenFEPair_zero_quarter_integrand_re_nonneg hx.1

theorem mellin_quarter_integral_Ioi_one_nonneg :
    0 ≤ ∫ x : ℝ in Ioi 1,
      (((x : ℂ) ^ ((1 / 4 : ℂ) - 1)) • (hurwitzEvenFEPair 0).f_modif x).re := by
  exact setIntegral_nonneg measurableSet_Ioi fun x hx =>
    mellin_hurwitzEvenFEPair_zero_quarter_integrand_re_nonneg
      (zero_lt_one.trans (by simpa using hx))

theorem mellin_quarter_integral_Ioo_zero_one_le_exp_tail
    (hInt : IntegrableOn (fun x : ℝ =>
      x ^ (-(3 / 4 : ℝ)) *
        (x ^ (-(1 / 2 : ℝ)) *
          (2 * (rexp (-π * (1 / x)) / (1 - rexp (-π * (1 / x)))))))
      (Ioo 0 1)) :
    (∫ x : ℝ in Ioo 0 1,
      (((x : ℂ) ^ ((1 / 4 : ℂ) - 1)) • (hurwitzEvenFEPair 0).f_modif x).re) ≤
    ∫ x : ℝ in Ioo 0 1,
      x ^ (-(3 / 4 : ℝ)) *
        (x ^ (-(1 / 2 : ℝ)) *
          (2 * (rexp (-π * (1 / x)) / (1 - rexp (-π * (1 / x)))))) := by
  have hM : HasMellin (hurwitzEvenFEPair 0).f_modif (1 / 4 : ℂ)
      ((hurwitzEvenFEPair 0).Λ₀ (1 / 4 : ℂ)) := by
    unfold WeakFEPair.Λ₀
    exact (hurwitzEvenFEPair 0).toStrongFEPair.hasMellin (1 / 4 : ℂ)
  have hAllInt : IntegrableOn (fun x : ℝ =>
      (((x : ℂ) ^ ((1 / 4 : ℂ) - 1)) • (hurwitzEvenFEPair 0).f_modif x).re)
      (Ioi (0 : ℝ)) := by
    exact hM.1.re
  have hLeftInt : IntegrableOn (fun x : ℝ =>
      (((x : ℂ) ^ ((1 / 4 : ℂ) - 1)) • (hurwitzEvenFEPair 0).f_modif x).re)
      (Ioo 0 1) := by
    exact hAllInt.mono_set (by intro x hx; exact hx.1)
  exact setIntegral_mono_on hLeftInt hInt measurableSet_Ioo fun x hx =>
    mellin_quarter_integrand_re_le_exp_tail_of_pos_lt_one hx.1 hx.2

theorem mellin_quarter_integral_Ioi_one_le_exp_tail
    (hInt : IntegrableOn (fun x : ℝ =>
      x ^ (-(3 / 4 : ℝ)) * (2 * (rexp (-π * x) / (1 - rexp (-π * x)))))
      (Ioi 1)) :
    (∫ x : ℝ in Ioi 1,
      (((x : ℂ) ^ ((1 / 4 : ℂ) - 1)) • (hurwitzEvenFEPair 0).f_modif x).re) ≤
    ∫ x : ℝ in Ioi 1,
      x ^ (-(3 / 4 : ℝ)) * (2 * (rexp (-π * x) / (1 - rexp (-π * x)))) := by
  have hM : HasMellin (hurwitzEvenFEPair 0).f_modif (1 / 4 : ℂ)
      ((hurwitzEvenFEPair 0).Λ₀ (1 / 4 : ℂ)) := by
    unfold WeakFEPair.Λ₀
    exact (hurwitzEvenFEPair 0).toStrongFEPair.hasMellin (1 / 4 : ℂ)
  have hAllInt : IntegrableOn (fun x : ℝ =>
      (((x : ℂ) ^ ((1 / 4 : ℂ) - 1)) • (hurwitzEvenFEPair 0).f_modif x).re)
      (Ioi (0 : ℝ)) := by
    exact hM.1.re
  have hRightInt : IntegrableOn (fun x : ℝ =>
      (((x : ℂ) ^ ((1 / 4 : ℂ) - 1)) • (hurwitzEvenFEPair 0).f_modif x).re)
      (Ioi 1) := by
    exact hAllInt.mono_set (by intro x hx; exact zero_lt_one.trans (by simpa using hx))
  exact setIntegral_mono_on hRightInt hInt measurableSet_Ioi fun x hx =>
    mellin_quarter_integrand_re_le_exp_tail_of_one_lt (by simpa using hx)

theorem one_sub_rexp_neg_pi_mul_pos_of_pos {x : ℝ} (hx : 0 < x) :
    0 < 1 - rexp (-π * x) := by
  exact sub_pos.mpr (by
    simpa only [exp_lt_one_iff, neg_mul, neg_lt_zero] using mul_pos pi_pos hx)

theorem one_sub_rexp_neg_pi_le_one_sub_rexp_neg_pi_mul_of_one_le {x : ℝ}
    (hx : 1 ≤ x) :
    1 - rexp (-π) ≤ 1 - rexp (-π * x) := by
  have harg : -π * x ≤ -π := by
    nlinarith [mul_le_mul_of_nonneg_left hx pi_pos.le]
  have hle : rexp (-π * x) ≤ rexp (-π) := exp_le_exp.mpr harg
  linarith

theorem rexp_neg_pi_mul_div_one_sub_le_const_mul_rexp_neg_pi_mul_of_one_le {x : ℝ}
    (hx : 1 ≤ x) :
    rexp (-π * x) / (1 - rexp (-π * x)) ≤
      (1 - rexp (-π))⁻¹ * rexp (-π * x) := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hdenx : 0 < 1 - rexp (-π * x) :=
    one_sub_rexp_neg_pi_mul_pos_of_pos hxpos
  have hden1 : 0 < 1 - rexp (-π) := by
    simpa only [mul_one] using one_sub_rexp_neg_pi_mul_pos_of_pos (x := 1) zero_lt_one
  have hden_le : 1 - rexp (-π) ≤ 1 - rexp (-π * x) :=
    one_sub_rexp_neg_pi_le_one_sub_rexp_neg_pi_mul_of_one_le hx
  have hinv :
      (1 - rexp (-π * x))⁻¹ ≤ (1 - rexp (-π))⁻¹ :=
    (inv_le_inv₀ hdenx hden1).mpr hden_le
  rw [div_eq_mul_inv]
  exact (mul_le_mul_of_nonneg_left hinv (exp_pos _).le).trans_eq (mul_comm _ _)

theorem mellin_quarter_right_exp_tail_le_const_mul_rexp {x : ℝ} (hx : 1 ≤ x) :
    x ^ (-(3 / 4 : ℝ)) * (2 * (rexp (-π * x) / (1 - rexp (-π * x)))) ≤
      (2 * (1 - rexp (-π))⁻¹) * rexp (-π * x) := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hrpow : x ^ (-(3 / 4 : ℝ)) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (-(3 / 4 : ℝ)) ≤ 0)
  have htail :
      rexp (-π * x) / (1 - rexp (-π * x)) ≤
        (1 - rexp (-π))⁻¹ * rexp (-π * x) :=
    rexp_neg_pi_mul_div_one_sub_le_const_mul_rexp_neg_pi_mul_of_one_le hx
  have htail_nonneg :
      0 ≤ 2 * (rexp (-π * x) / (1 - rexp (-π * x))) := by
    have hden : 0 < 1 - rexp (-π * x) := one_sub_rexp_neg_pi_mul_pos_of_pos hxpos
    positivity
  have hscaled :
      2 * (rexp (-π * x) / (1 - rexp (-π * x))) ≤
        2 * ((1 - rexp (-π))⁻¹ * rexp (-π * x)) :=
    mul_le_mul_of_nonneg_left htail zero_le_two
  calc
    x ^ (-(3 / 4 : ℝ)) * (2 * (rexp (-π * x) / (1 - rexp (-π * x))))
        ≤ 1 * (2 * ((1 - rexp (-π))⁻¹ * rexp (-π * x))) :=
          mul_le_mul hrpow hscaled htail_nonneg zero_le_one
    _ = (2 * (1 - rexp (-π))⁻¹) * rexp (-π * x) := by ring

theorem integrableOn_mellin_quarter_right_exp_tail :
    IntegrableOn (fun x : ℝ =>
      x ^ (-(3 / 4 : ℝ)) * (2 * (rexp (-π * x) / (1 - rexp (-π * x)))))
      (Ioi 1) := by
  have hcont : ContinuousOn (fun x : ℝ =>
      x ^ (-(3 / 4 : ℝ)) * (2 * (rexp (-π * x) / (1 - rexp (-π * x)))))
      (Ici 1) := by
    have hpow : ContinuousOn (fun x : ℝ => x ^ (-(3 / 4 : ℝ))) (Ici 1) :=
      continuous_id.continuousOn.rpow_const fun x hx =>
        Or.inl (ne_of_gt (zero_lt_one.trans_le hx))
    have hexp : ContinuousOn (fun x : ℝ => rexp (-π * x)) (Ici 1) := by
      fun_prop
    have hden : ∀ x ∈ Ici (1 : ℝ), 1 - rexp (-π * x) ≠ 0 := by
      intro x hx
      exact (one_sub_rexp_neg_pi_mul_pos_of_pos (zero_lt_one.trans_le hx)).ne'
    have hquot : ContinuousOn (fun x : ℝ =>
        rexp (-π * x) / (1 - rexp (-π * x))) (Ici 1) :=
      hexp.div (continuousOn_const.sub hexp) hden
    exact hpow.mul (continuousOn_const.mul hquot)
  have hO : (fun x : ℝ =>
      x ^ (-(3 / 4 : ℝ)) * (2 * (rexp (-π * x) / (1 - rexp (-π * x)))))
      =O[atTop] fun x : ℝ => rexp (-π * x) := by
    have hO' : (fun x : ℝ =>
        x ^ (-(3 / 4 : ℝ)) * (2 * (rexp (-π * x) / (1 - rexp (-π * x)))))
        =O[atTop] fun x : ℝ => (2 * (1 - rexp (-π))⁻¹) * rexp (-π * x) := by
      apply Eventually.isBigO
      filter_upwards [eventually_ge_atTop 1] with x hx
      have hxpos : 0 < x := zero_lt_one.trans_le hx
      have hnonneg :
          0 ≤ x ^ (-(3 / 4 : ℝ)) *
            (2 * (rexp (-π * x) / (1 - rexp (-π * x)))) := by
        have hden : 0 < 1 - rexp (-π * x) := one_sub_rexp_neg_pi_mul_pos_of_pos hxpos
        positivity
      rw [norm_of_nonneg hnonneg]
      exact mellin_quarter_right_exp_tail_le_const_mul_rexp hx
    exact hO'.trans ((isBigO_refl (fun x : ℝ => rexp (-π * x)) atTop).const_mul_left _)
  exact integrable_of_isBigO_exp_neg pi_pos hcont hO

theorem mellin_quarter_integral_Ioi_one_le_integral_exp_tail :
    (∫ x : ℝ in Ioi 1,
      (((x : ℂ) ^ ((1 / 4 : ℂ) - 1)) • (hurwitzEvenFEPair 0).f_modif x).re) ≤
    ∫ x : ℝ in Ioi 1,
      x ^ (-(3 / 4 : ℝ)) * (2 * (rexp (-π * x) / (1 - rexp (-π * x)))) :=
  mellin_quarter_integral_Ioi_one_le_exp_tail integrableOn_mellin_quarter_right_exp_tail

theorem one_sub_rexp_neg_pi_le_one_sub_rexp_neg_pi_mul_inv_of_pos_le_one {x : ℝ}
    (h0 : 0 < x) (h1 : x ≤ 1) :
    1 - rexp (-π) ≤ 1 - rexp (-π * (1 / x)) :=
  one_sub_rexp_neg_pi_le_one_sub_rexp_neg_pi_mul_of_one_le (one_le_one_div h0 h1)

theorem rexp_neg_pi_mul_inv_div_one_sub_le_const_mul_rexp_neg_pi_mul_inv_of_pos_le_one
    {x : ℝ} (h0 : 0 < x) (h1 : x ≤ 1) :
    rexp (-π * (1 / x)) / (1 - rexp (-π * (1 / x))) ≤
      (1 - rexp (-π))⁻¹ * rexp (-π * (1 / x)) :=
  rexp_neg_pi_mul_div_one_sub_le_const_mul_rexp_neg_pi_mul_of_one_le
    (one_le_one_div h0 h1)

theorem mellin_quarter_left_exp_tail_le_const_mul_rexp_inv {x : ℝ}
    (h0 : 0 < x) (h1 : x ≤ 1) :
    x ^ (-(3 / 4 : ℝ)) *
        (x ^ (-(1 / 2 : ℝ)) *
          (2 * (rexp (-π * (1 / x)) / (1 - rexp (-π * (1 / x)))))) ≤
      (2 * (1 - rexp (-π))⁻¹) *
        (x ^ (-(5 / 4 : ℝ)) * rexp (-π * (1 / x))) := by
  have htail :
      rexp (-π * (1 / x)) / (1 - rexp (-π * (1 / x))) ≤
        (1 - rexp (-π))⁻¹ * rexp (-π * (1 / x)) :=
    rexp_neg_pi_mul_inv_div_one_sub_le_const_mul_rexp_neg_pi_mul_inv_of_pos_le_one h0 h1
  have hscaled :
      2 * (rexp (-π * (1 / x)) / (1 - rexp (-π * (1 / x)))) ≤
        2 * ((1 - rexp (-π))⁻¹ * rexp (-π * (1 / x))) :=
    mul_le_mul_of_nonneg_left htail zero_le_two
  have hpow :
      x ^ (-(3 / 4 : ℝ)) * x ^ (-(1 / 2 : ℝ)) = x ^ (-(5 / 4 : ℝ)) := by
    rw [← Real.rpow_add h0]
    ring_nf
  calc
    x ^ (-(3 / 4 : ℝ)) *
        (x ^ (-(1 / 2 : ℝ)) *
          (2 * (rexp (-π * (1 / x)) / (1 - rexp (-π * (1 / x))))))
        ≤ x ^ (-(3 / 4 : ℝ)) *
            (x ^ (-(1 / 2 : ℝ)) *
              (2 * ((1 - rexp (-π))⁻¹ * rexp (-π * (1 / x))))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hscaled (rpow_nonneg h0.le _))
            (rpow_nonneg h0.le _)
    _ = (2 * (1 - rexp (-π))⁻¹) *
        (x ^ (-(5 / 4 : ℝ)) * rexp (-π * (1 / x))) := by
          rw [← mul_assoc, hpow]
          ring

theorem integrableOn_mellin_quarter_left_near_zero_bound_Ioi :
    IntegrableOn (fun x : ℝ =>
      x ^ (-(5 / 4 : ℝ)) * rexp (-π * (1 / x))) (Ioi (0 : ℝ)) := by
  let f : ℝ → ℝ := fun u => u ^ (-(3 / 4 : ℝ)) * rexp (-π * u)
  have hf : IntegrableOn f (Ioi (0 : ℝ)) := by
    dsimp [f]
    simpa [Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := 1) (s := (-(3 / 4 : ℝ))) (b := π)
        (by norm_num : (-1 : ℝ) < -(3 / 4 : ℝ))
        (by norm_num : (1 : ℝ) ≤ 1) pi_pos)
  have hchange : IntegrableOn (fun x : ℝ => x ^ ((-1 : ℝ) - 1) • f (x ^ (-1 : ℝ)))
      (Ioi (0 : ℝ)) :=
    (integrableOn_Ioi_comp_rpow_iff' f (by norm_num : (-1 : ℝ) ≠ 0)).2 hf
  have htarget : IntegrableOn (fun x : ℝ =>
      x ^ (-(5 / 4 : ℝ)) * rexp (-π * (1 / x))) (Ioi (0 : ℝ)) := by
    refine hchange.congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hxpos : 0 < x := hx
    have hxpow_inv : x ^ (-1 : ℝ) = 1 / x := by
      rw [Real.rpow_neg hxpos.le, Real.rpow_one]
      rw [one_div]
    have hpow :
        x ^ ((-1 : ℝ) - 1) * (x ^ (-1 : ℝ)) ^ (-(3 / 4 : ℝ)) =
          x ^ (-(5 / 4 : ℝ)) := by
      have hmul :
          (x ^ (-1 : ℝ)) ^ (-(3 / 4 : ℝ)) =
            x ^ ((-1 : ℝ) * (-(3 / 4 : ℝ))) := by
        rw [← Real.rpow_mul hxpos.le]
      rw [hmul, ← Real.rpow_add hxpos]
      ring_nf
    dsimp [f]
    calc
      x ^ ((-1 : ℝ) - 1) *
          ((x ^ (-1 : ℝ)) ^ (-(3 / 4 : ℝ)) * rexp (-π * x ^ (-1 : ℝ))) =
          (x ^ ((-1 : ℝ) - 1) * (x ^ (-1 : ℝ)) ^ (-(3 / 4 : ℝ))) *
            rexp (-π * x ^ (-1 : ℝ)) := by
            ring
      _ = x ^ (-(5 / 4 : ℝ)) * rexp (-π * x ^ (-1 : ℝ)) := by
            rw [hpow]
      _ = x ^ (-(5 / 4 : ℝ)) * rexp (-π * (1 / x)) := by
            rw [hxpow_inv]
  exact htarget

theorem integrableOn_mellin_quarter_left_near_zero_bound :
    IntegrableOn (fun x : ℝ =>
      x ^ (-(5 / 4 : ℝ)) * rexp (-π * (1 / x))) (Ioo 0 1) :=
  integrableOn_mellin_quarter_left_near_zero_bound_Ioi.mono_set Ioo_subset_Ioi_self

theorem integrableOn_mellin_quarter_left_exp_tail :
    IntegrableOn (fun x : ℝ =>
      x ^ (-(3 / 4 : ℝ)) *
        (x ^ (-(1 / 2 : ℝ)) *
          (2 * (rexp (-π * (1 / x)) / (1 - rexp (-π * (1 / x)))))))
      (Ioo 0 1) := by
  have hboundInt : IntegrableOn (fun x : ℝ =>
      (2 * (1 - rexp (-π))⁻¹) *
        (x ^ (-(5 / 4 : ℝ)) * rexp (-π * (1 / x)))) (Ioo 0 1) :=
    integrableOn_mellin_quarter_left_near_zero_bound.const_mul _
  have hcont : ContinuousOn (fun x : ℝ =>
      x ^ (-(3 / 4 : ℝ)) *
        (x ^ (-(1 / 2 : ℝ)) *
          (2 * (rexp (-π * (1 / x)) / (1 - rexp (-π * (1 / x)))))))
      (Ioo 0 1) := by
    have hpow34 : ContinuousOn (fun x : ℝ => x ^ (-(3 / 4 : ℝ))) (Ioo 0 1) :=
      continuous_id.continuousOn.rpow_const fun x hx =>
        Or.inl (ne_of_gt hx.1)
    have hpow12 : ContinuousOn (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) (Ioo 0 1) :=
      continuous_id.continuousOn.rpow_const fun x hx =>
        Or.inl (ne_of_gt hx.1)
    have hinv : ContinuousOn (fun x : ℝ => 1 / x) (Ioo 0 1) := by
      exact
        (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Ioo 0 1)).div
          continuous_id.continuousOn (by intro x hx; exact ne_of_gt hx.1)
    have hexp : ContinuousOn (fun x : ℝ => rexp (-π * (1 / x))) (Ioo 0 1) :=
      (continuousOn_const.mul hinv).rexp
    have hden : ∀ x ∈ Ioo (0 : ℝ) 1, 1 - rexp (-π * (1 / x)) ≠ 0 := by
      intro x hx
      exact (one_sub_rexp_neg_pi_mul_pos_of_pos (one_div_pos.mpr hx.1)).ne'
    have hquot : ContinuousOn (fun x : ℝ =>
        rexp (-π * (1 / x)) / (1 - rexp (-π * (1 / x)))) (Ioo 0 1) :=
      hexp.div (continuousOn_const.sub hexp) hden
    exact hpow34.mul (hpow12.mul (continuousOn_const.mul hquot))
  exact Integrable.mono' hboundInt (hcont.aestronglyMeasurable measurableSet_Ioo) <|
    (ae_restrict_iff' measurableSet_Ioo).2 <| Eventually.of_forall fun x hx => by
      have hxpos : 0 < x := hx.1
      have hden : 0 < 1 - rexp (-π * (1 / x)) :=
        one_sub_rexp_neg_pi_mul_pos_of_pos (one_div_pos.mpr hxpos)
      have hnonneg :
          0 ≤ x ^ (-(3 / 4 : ℝ)) *
            (x ^ (-(1 / 2 : ℝ)) *
              (2 * (rexp (-π * (1 / x)) / (1 - rexp (-π * (1 / x)))))) := by
        positivity
      rw [Real.norm_of_nonneg hnonneg]
      exact mellin_quarter_left_exp_tail_le_const_mul_rexp_inv hx.1 hx.2.le

theorem mellin_quarter_integral_Ioo_zero_one_le_integral_exp_tail :
    (∫ x : ℝ in Ioo 0 1,
      (((x : ℂ) ^ ((1 / 4 : ℂ) - 1)) • (hurwitzEvenFEPair 0).f_modif x).re) ≤
    ∫ x : ℝ in Ioo 0 1,
      x ^ (-(3 / 4 : ℝ)) *
        (x ^ (-(1 / 2 : ℝ)) *
          (2 * (rexp (-π * (1 / x)) / (1 - rexp (-π * (1 / x)))))) :=
  mellin_quarter_integral_Ioo_zero_one_le_exp_tail
    integrableOn_mellin_quarter_left_exp_tail

theorem mellin_hurwitzEvenFEPair_zero_quarter_re_le_integral_exp_tails :
    (mellin (hurwitzEvenFEPair 0).f_modif (1 / 4 : ℂ)).re ≤
      (∫ x : ℝ in Ioo 0 1,
        x ^ (-(3 / 4 : ℝ)) *
          (x ^ (-(1 / 2 : ℝ)) *
            (2 * (rexp (-π * (1 / x)) / (1 - rexp (-π * (1 / x))))))) +
      ∫ x : ℝ in Ioi 1,
        x ^ (-(3 / 4 : ℝ)) * (2 * (rexp (-π * x) / (1 - rexp (-π * x)))) := by
  rw [mellin_hurwitzEvenFEPair_zero_quarter_re_eq_integral_split]
  exact add_le_add
    mellin_quarter_integral_Ioo_zero_one_le_integral_exp_tail
    mellin_quarter_integral_Ioi_one_le_integral_exp_tail

theorem mellin_quarter_left_exp_tail_integral_le_const_integral_rexp_inv :
    (∫ x : ℝ in Ioo 0 1,
      x ^ (-(3 / 4 : ℝ)) *
        (x ^ (-(1 / 2 : ℝ)) *
          (2 * (rexp (-π * (1 / x)) / (1 - rexp (-π * (1 / x))))))) ≤
    ∫ x : ℝ in Ioo 0 1,
      (2 * (1 - rexp (-π))⁻¹) *
        (x ^ (-(5 / 4 : ℝ)) * rexp (-π * (1 / x))) := by
  have hboundInt : IntegrableOn (fun x : ℝ =>
      (2 * (1 - rexp (-π))⁻¹) *
        (x ^ (-(5 / 4 : ℝ)) * rexp (-π * (1 / x)))) (Ioo 0 1) :=
    integrableOn_mellin_quarter_left_near_zero_bound.const_mul _
  exact setIntegral_mono_on integrableOn_mellin_quarter_left_exp_tail
    hboundInt measurableSet_Ioo fun x hx =>
      mellin_quarter_left_exp_tail_le_const_mul_rexp_inv hx.1 hx.2.le

theorem mellin_quarter_right_exp_tail_integral_le_const_integral_rexp :
    (∫ x : ℝ in Ioi 1,
      x ^ (-(3 / 4 : ℝ)) * (2 * (rexp (-π * x) / (1 - rexp (-π * x))))) ≤
    ∫ x : ℝ in Ioi 1,
      (2 * (1 - rexp (-π))⁻¹) * rexp (-π * x) := by
  have hboundInt : IntegrableOn (fun x : ℝ =>
      (2 * (1 - rexp (-π))⁻¹) * rexp (-π * x)) (Ioi 1) :=
    (exp_neg_integrableOn_Ioi 1 pi_pos).const_mul _
  exact setIntegral_mono_on integrableOn_mellin_quarter_right_exp_tail
    hboundInt measurableSet_Ioi fun x hx => by
      have hxle : (1 : ℝ) ≤ x := (by simpa using hx : (1 : ℝ) < x).le
      exact mellin_quarter_right_exp_tail_le_const_mul_rexp hxle

theorem mellin_hurwitzEvenFEPair_zero_quarter_re_le_integral_const_exp_bounds :
    (mellin (hurwitzEvenFEPair 0).f_modif (1 / 4 : ℂ)).re ≤
      (∫ x : ℝ in Ioo 0 1,
        (2 * (1 - rexp (-π))⁻¹) *
          (x ^ (-(5 / 4 : ℝ)) * rexp (-π * (1 / x)))) +
      ∫ x : ℝ in Ioi 1,
        (2 * (1 - rexp (-π))⁻¹) * rexp (-π * x) := by
  exact mellin_hurwitzEvenFEPair_zero_quarter_re_le_integral_exp_tails.trans
    (add_le_add
      mellin_quarter_left_exp_tail_integral_le_const_integral_rexp_inv
      mellin_quarter_right_exp_tail_integral_le_const_integral_rexp)

theorem integral_Ioi_one_rexp_neg_pi_mul_eq :
    (∫ x : ℝ in Ioi 1, rexp (-π * x)) = rexp (-π) / π := by
  have h := integral_exp_mul_Ioi (a := -π) (c := (1 : ℝ)) (by nlinarith [pi_pos])
  simpa using h

theorem integral_Ioi_one_const_mul_rexp_neg_pi_mul_eq :
    (∫ x : ℝ in Ioi 1,
      (2 * (1 - rexp (-π))⁻¹) * rexp (-π * x)) =
    (2 * (1 - rexp (-π))⁻¹) * (rexp (-π) / π) := by
  rw [integral_const_mul, integral_Ioi_one_rexp_neg_pi_mul_eq]

theorem integral_Ioi_near_zero_bound_eq_integral_exp_tail :
    (∫ x : ℝ in Ioi 0,
      x ^ (-(5 / 4 : ℝ)) * rexp (-π * (1 / x))) =
    ∫ u : ℝ in Ioi 0,
      u ^ (-(3 / 4 : ℝ)) * rexp (-π * u) := by
  let f : ℝ → ℝ := fun u => u ^ (-(3 / 4 : ℝ)) * rexp (-π * u)
  have hchange := integral_comp_rpow_Ioi (g := f) (p := (-1 : ℝ))
    (by norm_num : (-1 : ℝ) ≠ 0)
  rw [← hchange]
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro x hx
  have hxpos : 0 < x := hx
  have hxpow_inv : x ^ (-1 : ℝ) = 1 / x := by
    rw [Real.rpow_neg hxpos.le, Real.rpow_one]
    rw [one_div]
  have hpow :
      x ^ ((-1 : ℝ) - 1) * (x ^ (-1 : ℝ)) ^ (-(3 / 4 : ℝ)) =
        x ^ (-(5 / 4 : ℝ)) := by
    have hmul :
        (x ^ (-1 : ℝ)) ^ (-(3 / 4 : ℝ)) =
          x ^ ((-1 : ℝ) * (-(3 / 4 : ℝ))) := by
      rw [← Real.rpow_mul hxpos.le]
    rw [hmul, ← Real.rpow_add hxpos]
    ring_nf
  dsimp [f]
  symm
  calc
    (|-1| * x ^ ((-1 : ℝ) - 1)) •
        ((x ^ (-1 : ℝ)) ^ (-(3 / 4 : ℝ)) * rexp (-π * x ^ (-1 : ℝ))) =
        x ^ ((-1 : ℝ) - 1) *
          ((x ^ (-1 : ℝ)) ^ (-(3 / 4 : ℝ)) * rexp (-π * x ^ (-1 : ℝ))) := by
          norm_num [smul_eq_mul]
    _ = (x ^ ((-1 : ℝ) - 1) * (x ^ (-1 : ℝ)) ^ (-(3 / 4 : ℝ))) *
          rexp (-π * x ^ (-1 : ℝ)) := by
          ring
    _ = x ^ (-(5 / 4 : ℝ)) * rexp (-π * x ^ (-1 : ℝ)) := by
          rw [hpow]
    _ = x ^ (-(5 / 4 : ℝ)) * rexp (-π * (1 / x)) := by
          rw [hxpow_inv]

theorem integral_Ioo_near_zero_bound_le_integral_Ioi_near_zero_bound :
    (∫ x : ℝ in Ioo 0 1,
      x ^ (-(5 / 4 : ℝ)) * rexp (-π * (1 / x))) ≤
    ∫ x : ℝ in Ioi 0,
      x ^ (-(5 / 4 : ℝ)) * rexp (-π * (1 / x)) := by
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun x : ℝ => x ^ (-(5 / 4 : ℝ)) * rexp (-π * (1 / x)) := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 ?_
    exact Eventually.of_forall fun x hx =>
      mul_nonneg (rpow_nonneg hx.le _) (exp_pos _).le
  exact setIntegral_mono_set
    integrableOn_mellin_quarter_left_near_zero_bound_Ioi
    hnonneg Ioo_subset_Ioi_self.eventuallyLE

theorem integral_Ioo_near_zero_bound_le_integral_exp_tail_Ioi :
    (∫ x : ℝ in Ioo 0 1,
      x ^ (-(5 / 4 : ℝ)) * rexp (-π * (1 / x))) ≤
    ∫ u : ℝ in Ioi 0,
      u ^ (-(3 / 4 : ℝ)) * rexp (-π * u) :=
  integral_Ioo_near_zero_bound_le_integral_Ioi_near_zero_bound.trans_eq
    integral_Ioi_near_zero_bound_eq_integral_exp_tail

theorem integral_Ioi_exp_tail_eq_gamma_quarter :
    (∫ u : ℝ in Ioi 0, u ^ (-(3 / 4 : ℝ)) * rexp (-π * u)) =
      (1 / π) ^ (1 / 4 : ℝ) * Real.Gamma (1 / 4 : ℝ) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (1 / 4 : ℝ)) (r := π) (by positivity) pi_pos
  calc
    (∫ u : ℝ in Ioi 0, u ^ (-(3 / 4 : ℝ)) * rexp (-π * u)) =
        ∫ u : ℝ in Ioi 0, u ^ ((1 / 4 : ℝ) - 1) * rexp (-(π * u)) := by
          refine setIntegral_congr_fun measurableSet_Ioi ?_
          intro u _hu
          rw [show ((1 / 4 : ℝ) - 1) = -(3 / 4 : ℝ) by ring]
          ring_nf
    _ = (1 / π) ^ (1 / 4 : ℝ) * Real.Gamma (1 / 4 : ℝ) := by
          simpa using h

theorem integral_Ioi_const_mul_exp_tail_eq_gamma_quarter :
    (∫ u : ℝ in Ioi 0,
      (2 * (1 - rexp (-π))⁻¹) * (u ^ (-(3 / 4 : ℝ)) * rexp (-π * u))) =
    (2 * (1 - rexp (-π))⁻¹) *
      ((1 / π) ^ (1 / 4 : ℝ) * Real.Gamma (1 / 4 : ℝ)) := by
  rw [integral_const_mul, integral_Ioi_exp_tail_eq_gamma_quarter]

theorem integral_Ioo_const_near_zero_bound_le_gamma_quarter :
    (∫ x : ℝ in Ioo 0 1,
      (2 * (1 - rexp (-π))⁻¹) *
        (x ^ (-(5 / 4 : ℝ)) * rexp (-π * (1 / x)))) ≤
    (2 * (1 - rexp (-π))⁻¹) *
      ((1 / π) ^ (1 / 4 : ℝ) * Real.Gamma (1 / 4 : ℝ)) := by
  have hden : 0 < 1 - rexp (-π) := by
    simpa only [mul_one] using
      one_sub_rexp_neg_pi_mul_pos_of_pos (x := 1) zero_lt_one
  have hconst_nonneg : 0 ≤ 2 * (1 - rexp (-π))⁻¹ := by
    positivity
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left
    (integral_Ioo_near_zero_bound_le_integral_exp_tail_Ioi.trans_eq
      integral_Ioi_exp_tail_eq_gamma_quarter)
    hconst_nonneg

theorem mellin_hurwitzEvenFEPair_zero_quarter_re_le_gamma_exp_bound :
    (mellin (hurwitzEvenFEPair 0).f_modif (1 / 4 : ℂ)).re ≤
      (2 * (1 - rexp (-π))⁻¹) *
        ((1 / π) ^ (1 / 4 : ℝ) * Real.Gamma (1 / 4 : ℝ)) +
      (2 * (1 - rexp (-π))⁻¹) * (rexp (-π) / π) := by
  exact mellin_hurwitzEvenFEPair_zero_quarter_re_le_integral_const_exp_bounds.trans
    (add_le_add
      integral_Ioo_const_near_zero_bound_le_gamma_quarter
      (le_of_eq integral_Ioi_one_const_mul_rexp_neg_pi_mul_eq))

theorem Real.gamma_five_quarter_le_one :
    Real.Gamma (5 / 4 : ℝ) ≤ 1 := by
  have hconv := Real.convexOn_Gamma
  have h := hconv.2 (by norm_num : (1 : ℝ) ∈ Ioi (0 : ℝ))
    (by norm_num : (2 : ℝ) ∈ Ioi (0 : ℝ))
    (by norm_num : 0 ≤ (3 / 4 : ℝ))
    (by norm_num : 0 ≤ (1 / 4 : ℝ))
    (by norm_num : (3 / 4 : ℝ) + (1 / 4 : ℝ) = 1)
  norm_num at h
  simpa [Real.Gamma_one, Real.Gamma_two] using h

theorem Real.gamma_one_quarter_le_four :
    Real.Gamma (1 / 4 : ℝ) ≤ 4 := by
  have hadd := Real.Gamma_add_one (s := (1 / 4 : ℝ))
    (by norm_num : (1 / 4 : ℝ) ≠ 0)
  have hquarter : (1 / 4 : ℝ) * Real.Gamma (1 / 4 : ℝ) ≤ 1 := by
    rw [← hadd]
    convert Real.gamma_five_quarter_le_one using 1
    ring_nf
  nlinarith

theorem Real.one_div_pi_rpow_quarter_le_four_fifths :
    (1 / π) ^ (1 / 4 : ℝ) ≤ (4 / 5 : ℝ) := by
  apply (Real.rpow_le_rpow_iff
    (Real.rpow_nonneg (by positivity : 0 ≤ (1 / π : ℝ)) _)
    (by norm_num : 0 ≤ (4 / 5 : ℝ))
    (by norm_num : 0 < (4 : ℝ))).1
  have hbase : (1 / π : ℝ) ≤ (4 / 5 : ℝ) ^ 4 := by
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith [Real.pi_gt_three]
  calc
    ((1 / π) ^ (1 / 4 : ℝ)) ^ (4 : ℝ) = (1 / π : ℝ) := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num]
      rw [Real.rpow_natCast]
      simpa [one_div] using
        Real.rpow_inv_natCast_pow (by positivity : 0 ≤ (1 / π : ℝ))
          (by norm_num : (4 : ℕ) ≠ 0)
    _ ≤ (4 / 5 : ℝ) ^ 4 := hbase
    _ = (4 / 5 : ℝ) ^ (4 : ℝ) := by norm_num [Real.rpow_natCast]

theorem Real.rexp_neg_pi_lt_one_twentieth :
    rexp (-π) < (1 / 20 : ℝ) := by
  have h1 : (1359 / 500 : ℝ) < rexp 1 := by
    linarith [Real.exp_one_gt_d9]
  have h3 : (20 : ℝ) < rexp 3 := by
    have hpow : rexp 3 = rexp 1 ^ 3 := by
      rw [← Real.exp_nat_mul (1 : ℝ) 3]
      norm_num
    rw [hpow]
    have hcube : (1359 / 500 : ℝ) ^ 3 < rexp 1 ^ 3 := by
      exact pow_lt_pow_left₀ h1
        (by norm_num : (0 : ℝ) ≤ 1359 / 500)
        (by norm_num : (3 : ℕ) ≠ 0)
    have hnum : (20 : ℝ) < (1359 / 500 : ℝ) ^ 3 := by
      norm_num
    exact hnum.trans hcube
  have hneg3 : rexp (-3 : ℝ) < (1 / 20 : ℝ) := by
    rw [Real.exp_neg]
    simpa [one_div] using
      one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 20) h3
  have harg : -π < (-3 : ℝ) := by
    nlinarith [Real.pi_gt_three]
  exact (Real.exp_lt_exp.mpr harg).trans hneg3

theorem Real.rexp_neg_pi_div_pi_lt_one_twentieth :
    rexp (-π) / π < (1 / 20 : ℝ) := by
  have hdiv : rexp (-π) / π < rexp (-π) := by
    rw [div_lt_iff₀ Real.pi_pos]
    have hpos : 0 < rexp (-π) := Real.exp_pos (-π)
    have hpi1 : (1 : ℝ) < π := by
      nlinarith [Real.pi_gt_three]
    nlinarith
  exact hdiv.trans Real.rexp_neg_pi_lt_one_twentieth

theorem Real.two_mul_one_sub_rexp_neg_pi_inv_lt_seventeen_eighths :
    2 * (1 - rexp (-π))⁻¹ < (17 / 8 : ℝ) := by
  have hden_lower : (19 / 20 : ℝ) < 1 - rexp (-π) := by
    nlinarith [Real.rexp_neg_pi_lt_one_twentieth]
  have hinv : (1 - rexp (-π))⁻¹ < (20 / 19 : ℝ) := by
    have h := one_div_lt_one_div_of_lt
      (by norm_num : (0 : ℝ) < 19 / 20) hden_lower
    simpa [one_div] using h
  have hmul :
      2 * (1 - rexp (-π))⁻¹ < 2 * (20 / 19 : ℝ) := by
    exact mul_lt_mul_of_pos_left hinv (by norm_num : (0 : ℝ) < 2)
  exact hmul.trans (by norm_num : 2 * (20 / 19 : ℝ) < 17 / 8)

theorem mellin_gamma_exp_bound_lt_eight :
    (2 * (1 - rexp (-π))⁻¹) *
        ((1 / π) ^ (1 / 4 : ℝ) * Real.Gamma (1 / 4 : ℝ)) +
      (2 * (1 - rexp (-π))⁻¹) * (rexp (-π) / π) < (8 : ℝ) := by
  let C : ℝ := 2 * (1 - rexp (-π))⁻¹
  let A : ℝ := (1 / π) ^ (1 / 4 : ℝ) * Real.Gamma (1 / 4 : ℝ)
  let B : ℝ := rexp (-π) / π
  have hC : C < (17 / 8 : ℝ) := by
    simpa [C] using Real.two_mul_one_sub_rexp_neg_pi_inv_lt_seventeen_eighths
  have hgamma_nonneg : 0 ≤ Real.Gamma (1 / 4 : ℝ) := by
    exact le_of_lt (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 4))
  have hA : A ≤ (16 / 5 : ℝ) := by
    dsimp [A]
    have hprod := mul_le_mul Real.one_div_pi_rpow_quarter_le_four_fifths
      Real.gamma_one_quarter_le_four hgamma_nonneg
      (by norm_num : (0 : ℝ) ≤ 4 / 5)
    norm_num at hprod
    simpa [one_div] using hprod
  have hA_pos : 0 < A := by
    dsimp [A]
    have hroot_pos : 0 < (1 / π) ^ (1 / 4 : ℝ) := by
      exact Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < 1 / π) _
    have hgamma_pos : 0 < Real.Gamma (1 / 4 : ℝ) :=
      Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 4)
    positivity
  have hB : B < (1 / 20 : ℝ) := by
    simpa [B] using Real.rexp_neg_pi_div_pi_lt_one_twentieth
  have hB_pos : 0 < B := by
    dsimp [B]
    positivity
  have htermA : C * A < (17 / 8 : ℝ) * (16 / 5 : ℝ) := by
    exact mul_lt_mul hC hA hA_pos (by norm_num : (0 : ℝ) ≤ 17 / 8)
  have htermB : C * B < (17 / 8 : ℝ) * (1 / 20 : ℝ) := by
    exact mul_lt_mul hC (le_of_lt hB) hB_pos
      (by norm_num : (0 : ℝ) ≤ 17 / 8)
  calc
    (2 * (1 - rexp (-π))⁻¹) *
        ((1 / π) ^ (1 / 4 : ℝ) * Real.Gamma (1 / 4 : ℝ)) +
      (2 * (1 - rexp (-π))⁻¹) * (rexp (-π) / π) = C * A + C * B := by rfl
    _ < (17 / 8 : ℝ) * (16 / 5 : ℝ) +
        (17 / 8 : ℝ) * (1 / 20 : ℝ) := add_lt_add htermA htermB
    _ < (8 : ℝ) := by norm_num

theorem mellin_hurwitzEvenFEPair_zero_quarter_re_lt_eight :
    (mellin (hurwitzEvenFEPair 0).f_modif (1 / 4 : ℂ)).re < (8 : ℝ) := by
  exact lt_of_le_of_lt
    mellin_hurwitzEvenFEPair_zero_quarter_re_le_gamma_exp_bound
    mellin_gamma_exp_bound_lt_eight

theorem riemannXi_half_re_pos :
    0 < (riemannXi (1 / 2)).re := by
  exact riemannXi_half_re_pos_iff_mellin_hurwitzEvenFEPair_zero_re_lt_eight.2
    mellin_hurwitzEvenFEPair_zero_quarter_re_lt_eight

theorem riemannXi_half_mem_slitPlane :
    riemannXi (1 / 2) ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  left
  exact riemannXi_half_re_pos

theorem analyticAt_log_riemannXi_half :
    AnalyticAt ℂ (fun s : ℂ ↦ log (riemannXi s)) (1 / 2) := by
  exact (analyticAt_riemannXi (1 / 2)).clog riemannXi_half_mem_slitPlane

theorem differentiableAt_log_riemannXi_half :
    DifferentiableAt ℂ (fun s : ℂ ↦ log (riemannXi s)) (1 / 2) :=
  analyticAt_log_riemannXi_half.differentiableAt

theorem hasDerivAt_log_riemannXi_half :
    HasDerivAt (fun s : ℂ ↦ log (riemannXi s))
      (deriv riemannXi (1 / 2) / riemannXi (1 / 2)) (1 / 2) := by
  exact (differentiable_riemannXi (1 / 2)).hasDerivAt.clog
    riemannXi_half_mem_slitPlane

theorem deriv_log_riemannXi_half :
    deriv (fun s : ℂ ↦ log (riemannXi s)) (1 / 2) =
      deriv riemannXi (1 / 2) / riemannXi (1 / 2) :=
  hasDerivAt_log_riemannXi_half.deriv

theorem deriv_log_riemannXi_half_eq_zero :
    deriv (fun s : ℂ ↦ log (riemannXi s)) (1 / 2) = 0 := by
  rw [deriv_log_riemannXi_half, deriv_riemannXi_half_eq_zero]
  simp

theorem iteratedDeriv_centered_riemannXi_two_im_eq_zero :
    (iteratedDeriv 2 (fun z : ℂ ↦ riemannXi (1 / 2 + z)) 0).im = 0 := by
  rw [iteratedDeriv_centered_riemannXi_two_eq_completedZeta₀_half]
  simp only [one_div, sub_im, mul_im, inv_re, re_ofNat, normSq_ofNat,
    div_self_mul_self', inv_im, im_ofNat, neg_zero, zero_div, zero_mul, add_zero]
  have hval : (completedRiemannZeta₀ (2⁻¹ : ℂ)).im = 0 :=
    value_im_eq_zero_of_conj_conj_eq_self_at_fixed
      completedRiemannZeta₀ completedRiemannZeta₀_conj_conj
      (by norm_num [starRingEnd_apply])
  have hderiv : (deriv (deriv completedRiemannZeta₀) (2⁻¹ : ℂ)).im = 0 :=
    value_im_eq_zero_of_conj_conj_eq_self_at_fixed
      (deriv (deriv completedRiemannZeta₀))
      deriv_deriv_completedRiemannZeta₀_conj_conj
      (by norm_num [starRingEnd_apply])
  rw [hval, hderiv]
  norm_num

theorem iteratedDeriv_centered_riemannXi_two_eq_ofReal_re :
    iteratedDeriv 2 (fun z : ℂ ↦ riemannXi (1 / 2 + z)) 0 =
      ((iteratedDeriv 2 (fun z : ℂ ↦ riemannXi (1 / 2 + z)) 0).re : ℂ) := by
  apply Complex.ext
  · simp
  · exact iteratedDeriv_centered_riemannXi_two_im_eq_zero

theorem iteratedDeriv_centered_riemannXi_two_re_eq_completedZeta₀_half_re :
    (iteratedDeriv 2 (fun z : ℂ ↦ riemannXi (1 / 2 + z)) 0).re =
      (completedRiemannZeta₀ (1 / 2)).re -
        (1 / 8) * (deriv (deriv completedRiemannZeta₀) (1 / 2)).re := by
  rw [iteratedDeriv_centered_riemannXi_two_eq_completedZeta₀_half]
  simp [Complex.sub_re, Complex.mul_re]

theorem iteratedDeriv_centered_riemannXi_two_eq_ofReal_re_formula :
    iteratedDeriv 2 (fun z : ℂ ↦ riemannXi (1 / 2 + z)) 0 =
      (((completedRiemannZeta₀ (1 / 2)).re -
        (1 / 8) * (deriv (deriv completedRiemannZeta₀) (1 / 2)).re : ℝ) : ℂ) := by
  rw [iteratedDeriv_centered_riemannXi_two_eq_ofReal_re]
  rw [iteratedDeriv_centered_riemannXi_two_re_eq_completedZeta₀_half_re]

theorem iteratedDeriv_centered_riemannXi_two_re_pos_iff :
    0 < (iteratedDeriv 2 (fun z : ℂ ↦ riemannXi (1 / 2 + z)) 0).re ↔
      0 < (completedRiemannZeta₀ (1 / 2)).re -
        (1 / 8) * (deriv (deriv completedRiemannZeta₀) (1 / 2)).re := by
  rw [iteratedDeriv_centered_riemannXi_two_re_eq_completedZeta₀_half_re]

theorem deriv_completedRiemannZeta₀_zero_im_eq_zero :
    (deriv completedRiemannZeta₀ 0).im = 0 :=
  deriv_completedRiemannZeta₀_zero_im_eq_zero_of_conj_conj
    completedRiemannZeta₀_conj_conj

theorem liCoefficientCandidate_one_im_eq_zero :
    (liCoefficientCandidate 1).im = 0 :=
  liCoefficientCandidate_one_im_eq_zero_of_completedZeta₀_conj_conj
    completedRiemannZeta₀_conj_conj

theorem deriv_completedRiemannZeta₀_zero_eq_ofReal_re :
    deriv completedRiemannZeta₀ 0 =
      ((deriv completedRiemannZeta₀ 0).re : ℂ) := by
  apply Complex.ext
  · simp
  · simp [deriv_completedRiemannZeta₀_zero_im_eq_zero]

theorem liCoefficientCandidate_one_eq_ofReal_re :
    liCoefficientCandidate 1 = ((liCoefficientCandidate 1).re : ℂ) := by
  apply Complex.ext
  · simp
  · simp [liCoefficientCandidate_one_im_eq_zero]

theorem liCoefficientCandidate_one_eq_ofReal_re_formula :
    liCoefficientCandidate 1 =
      (((liCoefficientCandidate 0).re * (4 - (liCoefficientCandidate 0).re) -
        2 * (deriv completedRiemannZeta₀ 0).re : ℝ) : ℂ) := by
  rw [liCoefficientCandidate_one_eq_ofReal_re]
  rw [liCoefficientCandidate_one_re_eq_zero_re_deriv_completedZeta₀_zero_re]

theorem liCoefficientCandidate_one_re_pos_iff_re_formula :
    0 < (liCoefficientCandidate 1).re ↔
      0 < (liCoefficientCandidate 0).re * (4 - (liCoefficientCandidate 0).re) -
        2 * (deriv completedRiemannZeta₀ 0).re := by
  rw [liCoefficientCandidate_one_re_eq_zero_re_deriv_completedZeta₀_zero_re]

theorem liCoefficientCandidate_one_re_pos_iff_deriv_completedZeta₀_zero_re_lt :
    0 < (liCoefficientCandidate 1).re ↔
      (deriv completedRiemannZeta₀ 0).re <
        ((liCoefficientCandidate 0).re * (4 - (liCoefficientCandidate 0).re)) / 2 := by
  rw [liCoefficientCandidate_one_re_pos_iff_re_formula]
  constructor <;> intro h <;> linarith

theorem liCoefficientCandidate_zero_real_pos :
    0 < (Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2 + 1 := by
  let U : ℝ := 1.0986122888 + 2 * 0.6931471808
  let c : ℝ := 3.1416 / 3 - 1
  let H : ℝ := 83711 / 27720
  have hgamma : H - Real.log 12 < Real.eulerMascheroniConstant := by
    have h := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 11
    rw [Real.eulerMascheroniSeq] at h
    norm_num [H] at h ⊢
    exact h
  have hlog12 : Real.log 12 < U := by
    have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    calc
      Real.log 12 = Real.log ((3 : ℝ) * 4) := by norm_num
      _ = Real.log 3 + Real.log 4 := by rw [Real.log_mul] <;> norm_num
      _ = Real.log 3 + 2 * Real.log 2 := by rw [hlog4]
      _ < U := by
        unfold U
        linarith [Real.log_three_lt_d9, Real.log_two_lt_d9]
  have hlog4pi : Real.log (4 * Real.pi) < Real.log 12 + c := by
    have hsplitArg : 4 * Real.pi = (12 : ℝ) * (Real.pi / 3) := by ring
    calc
      Real.log (4 * Real.pi) = Real.log ((12 : ℝ) * (Real.pi / 3)) := by rw [hsplitArg]
      _ = Real.log 12 + Real.log (Real.pi / 3) := by
        rw [Real.log_mul]
        · norm_num
        · positivity
      _ ≤ Real.log 12 + (Real.pi / 3 - 1) := by
        gcongr
        exact Real.log_le_sub_one_of_pos (by positivity)
      _ < Real.log 12 + c := by
        unfold c
        linarith [Real.pi_lt_d4]
  have hnum : U + c < H + 2 - U := by
    norm_num [U, c, H]
  have hmain : Real.log (4 * Real.pi) < Real.eulerMascheroniConstant + 2 := by
    calc
      Real.log (4 * Real.pi) < Real.log 12 + c := hlog4pi
      _ < U + c := by linarith [hlog12]
      _ < H + 2 - U := hnum
      _ < H + 2 - Real.log 12 := by linarith [hlog12]
      _ < Real.eulerMascheroniConstant + 2 := by linarith [hgamma]
  linarith

theorem liCoefficientCandidate_zero_re_pos :
    0 < (liCoefficientCandidate 0).re := by
  rw [liCoefficientCandidate_zero_eq_ofReal]
  simpa using liCoefficientCandidate_zero_real_pos

theorem liCoefficientCandidate_zero_re_lt_four :
    (liCoefficientCandidate 0).re < 4 := by
  rw [liCoefficientCandidate_zero_eq_ofReal]
  have hgamma : Real.eulerMascheroniConstant < 2 / 3 :=
    Real.eulerMascheroniConstant_lt_two_thirds
  have hlog_nonneg : 0 ≤ Real.log (4 * Real.pi) := by
    exact Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  simp
  linarith

theorem Real.eulerMascheroniConstant_gt_571_over_1000 :
    (571 / 1000 : ℝ) < Real.eulerMascheroniConstant := by
  let U : ℝ := 2 * (0.6931471808 + 1.6094379126)
  have hseq :
      (harmonic 99 : ℝ) - Real.log (100 : ℝ) <
        Real.eulerMascheroniConstant := by
    have h := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 99
    rw [Real.eulerMascheroniSeq] at h
    norm_num only [Nat.cast_ofNat, Nat.reduceAdd] at h
    exact h
  have hlog100 : Real.log (100 : ℝ) < U := by
    have hlog100_eq :
        Real.log (100 : ℝ) = 2 * (Real.log 2 + Real.log 5) := by
      calc
        Real.log (100 : ℝ) = Real.log ((10 : ℝ) ^ 2) := by norm_num
        _ = 2 * Real.log (10 : ℝ) := by
          rw [Real.log_pow]
          norm_num
        _ = 2 * (Real.log 2 + Real.log 5) := by
          rw [show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul] <;> norm_num
    calc
      Real.log (100 : ℝ) = 2 * (Real.log 2 + Real.log 5) := hlog100_eq
      _ < U := by
        unfold U
        linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
  have hlower : (571 / 1000 : ℝ) < (harmonic 99 : ℝ) - U := by
    norm_num [harmonic, U]
  have hmid : (harmonic 99 : ℝ) - U < (harmonic 99 : ℝ) - Real.log (100 : ℝ) := by
    linarith
  exact hlower.trans (hmid.trans hseq)

theorem Real.log_four_mul_pi_lt_2533_over_1000 :
    Real.log (4 * Real.pi) < 2533 / 1000 := by
  let U : ℝ := 1.0986122888 + 2 * 0.6931471808
  let c : ℝ := 3.1416 / 3 - 1
  have hlog12 : Real.log 12 < U := by
    have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    calc
      Real.log 12 = Real.log ((3 : ℝ) * 4) := by norm_num
      _ = Real.log 3 + Real.log 4 := by rw [Real.log_mul] <;> norm_num
      _ = Real.log 3 + 2 * Real.log 2 := by rw [hlog4]
      _ < U := by
        unfold U
        linarith [Real.log_three_lt_d9, Real.log_two_lt_d9]
  have hlog4pi : Real.log (4 * Real.pi) < Real.log 12 + c := by
    have hsplitArg : 4 * Real.pi = (12 : ℝ) * (Real.pi / 3) := by ring
    calc
      Real.log (4 * Real.pi) = Real.log ((12 : ℝ) * (Real.pi / 3)) := by rw [hsplitArg]
      _ = Real.log 12 + Real.log (Real.pi / 3) := by
        rw [Real.log_mul]
        · norm_num
        · positivity
      _ ≤ Real.log 12 + (Real.pi / 3 - 1) := by
        gcongr
        exact Real.log_le_sub_one_of_pos (by positivity)
      _ < Real.log 12 + c := by
        unfold c
        linarith [Real.pi_lt_d4]
  have hUc : U + c < 2533 / 1000 := by
    norm_num [U, c]
  have hmid : Real.log 12 + c < U + c := by
    linarith
  exact hlog4pi.trans (hmid.trans hUc)

theorem liCoefficientCandidate_zero_re_gt_seventeen_over_nine_hundred_sixty :
    17 / 960 < (liCoefficientCandidate 0).re := by
  rw [liCoefficientCandidate_zero_eq_ofReal]
  simp only [ofReal_add, ofReal_div, ofReal_sub, ofReal_ofNat, ofReal_one, add_re, div_ofNat_re,
    sub_re, ofReal_re, one_re]
  have hgamma : (571 / 1000 : ℝ) < Real.eulerMascheroniConstant :=
    Real.eulerMascheroniConstant_gt_571_over_1000
  have hlog : Real.log (4 * Real.pi) < 2533 / 1000 :=
    Real.log_four_mul_pi_lt_2533_over_1000
  linarith

theorem liCoefficientCandidate_zero_re_lt_one :
    (liCoefficientCandidate 0).re < 1 := by
  rw [liCoefficientCandidate_zero_eq_ofReal]
  simp only [ofReal_add, ofReal_div, ofReal_sub, ofReal_ofNat, ofReal_one, add_re, div_ofNat_re,
    sub_re, ofReal_re, one_re, add_lt_iff_neg_right]
  have hgamma : Real.eulerMascheroniConstant < 2 / 3 :=
    Real.eulerMascheroniConstant_lt_two_thirds
  have hlog4pi : 2 / 3 < Real.log (4 * Real.pi) := by
    have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    have hlog4_gt : 2 / 3 < Real.log (4 : ℝ) := by
      rw [hlog4]
      linarith [Real.log_two_gt_d9]
    have hlog4_le : Real.log (4 : ℝ) < Real.log (4 * Real.pi) := by
      exact Real.log_lt_log (by norm_num) (by nlinarith [Real.pi_gt_three])
    exact hlog4_gt.trans hlog4_le
  linarith

theorem liCoefficientCandidate_zero_threshold_gt_seventeen_over_one_sixty :
    17 / 160 <
      2 * ((liCoefficientCandidate 0).re * (4 - (liCoefficientCandidate 0).re)) := by
  have hlow := liCoefficientCandidate_zero_re_gt_seventeen_over_nine_hundred_sixty
  have hhigh := liCoefficientCandidate_zero_re_lt_one
  nlinarith

theorem liCoefficientCandidate_zero_re_mul_four_sub_pos :
    0 < (liCoefficientCandidate 0).re * (4 - (liCoefficientCandidate 0).re) := by
  nlinarith [liCoefficientCandidate_zero_re_pos, liCoefficientCandidate_zero_re_lt_four]

theorem deriv_completedRiemannZeta₀_zero_eq_quarter_deriv_hurwitzEvenFEPair_Λ₀_zero :
    deriv completedRiemannZeta₀ 0 =
      deriv (hurwitzEvenFEPair 0).Λ₀ 0 / 4 := by
  unfold completedRiemannZeta₀ completedHurwitzZetaEven₀
  have hcomp :
      deriv (fun s : ℂ ↦ (hurwitzEvenFEPair 0).Λ₀ (s / 2)) 0 =
        deriv (hurwitzEvenFEPair 0).Λ₀ 0 / 2 := by
    change deriv ((hurwitzEvenFEPair 0).Λ₀ ∘ fun s : ℂ ↦ s / 2) 0 =
      deriv (hurwitzEvenFEPair 0).Λ₀ 0 / 2
    have hlin : HasDerivAt (fun s : ℂ ↦ s / 2) (1 / 2 : ℂ) 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).div_const (2 : ℂ)
    have hLam : HasDerivAt (hurwitzEvenFEPair 0).Λ₀
        (deriv (hurwitzEvenFEPair 0).Λ₀ (0 / 2)) (0 / 2) :=
      ((hurwitzEvenFEPair 0).differentiable_Λ₀ (0 / 2)).hasDerivAt
    have h := hLam.comp (0 : ℂ) hlin
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h.deriv
  rw [deriv_div_const]
  rw [hcomp]
  ring

theorem deriv_completedRiemannZeta₀_zero_re_eq_quarter_deriv_hurwitzEvenFEPair_Λ₀_zero_re :
    (deriv completedRiemannZeta₀ 0).re =
      (deriv (hurwitzEvenFEPair 0).Λ₀ 0).re / 4 := by
  rw [deriv_completedRiemannZeta₀_zero_eq_quarter_deriv_hurwitzEvenFEPair_Λ₀_zero]
  simp

theorem liCoefficientCandidate_one_re_pos_iff_deriv_hurwitzEvenFEPair_Λ₀_zero_re_lt :
    0 < (liCoefficientCandidate 1).re ↔
      (deriv (hurwitzEvenFEPair 0).Λ₀ 0).re <
        2 * ((liCoefficientCandidate 0).re * (4 - (liCoefficientCandidate 0).re)) := by
  rw [liCoefficientCandidate_one_re_pos_iff_deriv_completedZeta₀_zero_re_lt]
  rw [deriv_completedRiemannZeta₀_zero_re_eq_quarter_deriv_hurwitzEvenFEPair_Λ₀_zero_re]
  constructor <;> intro h <;> linarith

theorem mellin_hasDerivAt_hurwitzEvenFEPair_f_modif_zero :
    MellinConvergent
        (fun t : ℝ => Real.log t • (hurwitzEvenFEPair 0).f_modif t) 0 ∧
      HasDerivAt (mellin (hurwitzEvenFEPair 0).f_modif)
        (mellin (fun t : ℝ => Real.log t • (hurwitzEvenFEPair 0).f_modif t) 0) 0 := by
  obtain ⟨a, ha⟩ := exists_gt (0 : ℂ).re
  obtain ⟨b, hb⟩ := exists_lt (0 : ℂ).re
  exact mellin_hasDerivAt_of_isBigO_rpow
    (hfc := (hurwitzEvenFEPair 0).toStrongFEPair.hf_int)
    (hf_top := (hurwitzEvenFEPair 0).toStrongFEPair.hf_top' (-a))
    (hs_top := ha)
    (hf_bot := (hurwitzEvenFEPair 0).toStrongFEPair.hf_zero' (-b))
    (hs_bot := hb)

theorem deriv_hurwitzEvenFEPair_Λ₀_zero_eq_mellin_log_f_modif_zero :
    deriv (hurwitzEvenFEPair 0).Λ₀ 0 =
      mellin (fun t : ℝ => Real.log t • (hurwitzEvenFEPair 0).f_modif t) 0 := by
  unfold WeakFEPair.Λ₀
  exact mellin_hasDerivAt_hurwitzEvenFEPair_f_modif_zero.2.deriv

theorem liCoefficientCandidate_one_re_pos_iff_mellin_log_hurwitzEvenFEPair_f_modif_zero_re_lt :
    0 < (liCoefficientCandidate 1).re ↔
      (mellin (fun t : ℝ => Real.log t • (hurwitzEvenFEPair 0).f_modif t) 0).re <
        2 * ((liCoefficientCandidate 0).re * (4 - (liCoefficientCandidate 0).re)) := by
  rw [liCoefficientCandidate_one_re_pos_iff_deriv_hurwitzEvenFEPair_Λ₀_zero_re_lt]
  rw [deriv_hurwitzEvenFEPair_Λ₀_zero_eq_mellin_log_f_modif_zero]

theorem ofReal_cpow_zero_sub_one {x : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ ((0 : ℂ) - 1) = ((x ^ (-1 : ℝ) : ℝ) : ℂ) := by
  have hexp : ((0 : ℂ) - 1) = ((-1 : ℝ) : ℂ) := by
    norm_num
  rw [hexp, ofReal_cpow hx.le]

theorem mellin_log_hurwitzEvenFEPair_f_modif_zero_integrand_re_eq {x : ℝ}
    (hx : 0 < x) :
    (((x : ℂ) ^ ((0 : ℂ) - 1)) •
        (Real.log x • (hurwitzEvenFEPair 0).f_modif x)).re =
      x ^ (-1 : ℝ) * Real.log x * ((hurwitzEvenFEPair 0).f_modif x).re := by
  rw [ofReal_cpow_zero_sub_one hx]
  simp [smul_eq_mul, Complex.mul_re, mul_assoc]

theorem mellin_log_hurwitzEvenFEPair_f_modif_zero_re_eq_integral :
    (mellin (fun t : ℝ => Real.log t • (hurwitzEvenFEPair 0).f_modif t) 0).re =
      ∫ x : ℝ in Ioi 0,
        (((x : ℂ) ^ ((0 : ℂ) - 1)) •
          (Real.log x • (hurwitzEvenFEPair 0).f_modif x)).re := by
  have hM := mellin_hasDerivAt_hurwitzEvenFEPair_f_modif_zero.1
  unfold mellin
  change RCLike.re (∫ t : ℝ in Ioi 0,
      (t : ℂ) ^ ((0 : ℂ) - 1) •
        (Real.log t • (hurwitzEvenFEPair 0).f_modif t)) =
    ∫ x : ℝ in Ioi 0,
      RCLike.re (((x : ℂ) ^ ((0 : ℂ) - 1)) •
        (Real.log x • (hurwitzEvenFEPair 0).f_modif x))
  rw [← integral_re hM]

theorem mellin_log_hurwitzEvenFEPair_f_modif_zero_re_eq_integral_split :
    (mellin (fun t : ℝ => Real.log t • (hurwitzEvenFEPair 0).f_modif t) 0).re =
      (∫ x : ℝ in Ioo 0 1,
        (((x : ℂ) ^ ((0 : ℂ) - 1)) •
          (Real.log x • (hurwitzEvenFEPair 0).f_modif x)).re) +
      ∫ x : ℝ in Ioi 1,
        (((x : ℂ) ^ ((0 : ℂ) - 1)) •
          (Real.log x • (hurwitzEvenFEPair 0).f_modif x)).re := by
  let g : ℝ → ℝ := fun x =>
    (((x : ℂ) ^ ((0 : ℂ) - 1)) •
      (Real.log x • (hurwitzEvenFEPair 0).f_modif x)).re
  have hM := mellin_hasDerivAt_hurwitzEvenFEPair_f_modif_zero.1
  have hgInt : IntegrableOn g (Ioi (0 : ℝ)) := by
    change IntegrableOn (fun x : ℝ =>
      (((x : ℂ) ^ ((0 : ℂ) - 1)) •
        (Real.log x • (hurwitzEvenFEPair 0).f_modif x)).re)
      (Ioi (0 : ℝ))
    exact hM.re
  rw [mellin_log_hurwitzEvenFEPair_f_modif_zero_re_eq_integral]
  change ∫ x : ℝ in Ioi 0, g x =
    (∫ x : ℝ in Ioo 0 1, g x) + ∫ x : ℝ in Ioi 1, g x
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  rw [setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hgInt.mono_set (by intro x hx; exact Ioc_subset_Ioi_self hx))
    (hgInt.mono_set (by intro x hx; exact zero_lt_one.trans (by simpa using hx)))]
  rw [integral_Ioc_eq_integral_Ioo]

theorem mellin_log_hurwitzEvenFEPair_f_modif_zero_re_eq_integral_split_real :
    (mellin (fun t : ℝ => Real.log t • (hurwitzEvenFEPair 0).f_modif t) 0).re =
      (∫ x : ℝ in Ioo 0 1,
        x ^ (-1 : ℝ) * Real.log x * ((hurwitzEvenFEPair 0).f_modif x).re) +
      ∫ x : ℝ in Ioi 1,
        x ^ (-1 : ℝ) * Real.log x * ((hurwitzEvenFEPair 0).f_modif x).re := by
  rw [mellin_log_hurwitzEvenFEPair_f_modif_zero_re_eq_integral_split]
  congr 1
  · refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    exact mellin_log_hurwitzEvenFEPair_f_modif_zero_integrand_re_eq hx.1
  · refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    exact mellin_log_hurwitzEvenFEPair_f_modif_zero_integrand_re_eq
      (zero_lt_one.trans (by simpa using hx))

theorem mellin_log_integral_Ioo_zero_one_nonpos :
    (∫ x : ℝ in Ioo 0 1,
      x ^ (-1 : ℝ) * Real.log x * ((hurwitzEvenFEPair 0).f_modif x).re) ≤ 0 := by
  exact setIntegral_nonpos measurableSet_Ioo fun x hx => by
    have hxpos : 0 < x := hx.1
    have hxlt : x < 1 := hx.2
    have hxpow : 0 ≤ x ^ (-1 : ℝ) := rpow_nonneg hxpos.le _
    have hxlog : Real.log x ≤ 0 := Real.log_nonpos hxpos.le hxlt.le
    have hkernel : 0 ≤ ((hurwitzEvenFEPair 0).f_modif x).re :=
      hurwitzEvenFEPair_zero_f_modif_re_nonneg_of_pos hxpos
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hxpow hxlog) hkernel

theorem mellin_log_hurwitzEvenFEPair_f_modif_zero_re_le_integral_Ioi_one :
    (mellin (fun t : ℝ => Real.log t • (hurwitzEvenFEPair 0).f_modif t) 0).re ≤
      ∫ x : ℝ in Ioi 1,
        x ^ (-1 : ℝ) * Real.log x * ((hurwitzEvenFEPair 0).f_modif x).re := by
  rw [mellin_log_hurwitzEvenFEPair_f_modif_zero_re_eq_integral_split_real]
  linarith [mellin_log_integral_Ioo_zero_one_nonpos]

theorem mellin_log_right_integrand_re_le_exp_tail_of_one_lt {x : ℝ} (hx : 1 < x) :
    x ^ (-1 : ℝ) * Real.log x * ((hurwitzEvenFEPair 0).f_modif x).re ≤
      x ^ (-1 : ℝ) * Real.log x *
        (2 * (rexp (-π * x) / (1 - rexp (-π * x)))) := by
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hxpow : 0 ≤ x ^ (-1 : ℝ) := rpow_nonneg hxpos.le _
  have hxlog : 0 ≤ Real.log x := Real.log_nonneg hx.le
  have hcoef : 0 ≤ x ^ (-1 : ℝ) * Real.log x := mul_nonneg hxpow hxlog
  exact mul_le_mul_of_nonneg_left
    (hurwitzEvenFEPair_zero_f_modif_re_le_exp_tail_of_one_lt hx) hcoef

theorem mellin_log_integral_Ioi_one_le_exp_tail
    (hInt : IntegrableOn (fun x : ℝ =>
      x ^ (-1 : ℝ) * Real.log x *
        (2 * (rexp (-π * x) / (1 - rexp (-π * x)))))
      (Ioi 1)) :
    (∫ x : ℝ in Ioi 1,
      x ^ (-1 : ℝ) * Real.log x * ((hurwitzEvenFEPair 0).f_modif x).re) ≤
    ∫ x : ℝ in Ioi 1,
      x ^ (-1 : ℝ) * Real.log x *
        (2 * (rexp (-π * x) / (1 - rexp (-π * x)))) := by
  have hRawInt : IntegrableOn (fun x : ℝ =>
      (((x : ℂ) ^ ((0 : ℂ) - 1)) •
        (Real.log x • (hurwitzEvenFEPair 0).f_modif x)).re)
      (Ioi (0 : ℝ)) := by
    exact mellin_hasDerivAt_hurwitzEvenFEPair_f_modif_zero.1.re
  have hRawRightInt : IntegrableOn (fun x : ℝ =>
      (((x : ℂ) ^ ((0 : ℂ) - 1)) •
        (Real.log x • (hurwitzEvenFEPair 0).f_modif x)).re)
      (Ioi 1) := by
    exact hRawInt.mono_set (by intro x hx; exact zero_lt_one.trans (by simpa using hx))
  have hRightInt : IntegrableOn (fun x : ℝ =>
      x ^ (-1 : ℝ) * Real.log x * ((hurwitzEvenFEPair 0).f_modif x).re)
      (Ioi 1) := by
    refine hRawRightInt.congr_fun (fun x hx => ?_) measurableSet_Ioi
    exact mellin_log_hurwitzEvenFEPair_f_modif_zero_integrand_re_eq
      (zero_lt_one.trans (by simpa using hx))
  exact setIntegral_mono_on hRightInt hInt measurableSet_Ioi fun x hx =>
    mellin_log_right_integrand_re_le_exp_tail_of_one_lt (by simpa using hx)

theorem mellin_log_right_exp_tail_le_const_mul_rexp {x : ℝ} (hx : 1 ≤ x) :
    x ^ (-1 : ℝ) * Real.log x *
        (2 * (rexp (-π * x) / (1 - rexp (-π * x)))) ≤
      (2 * (1 - rexp (-π))⁻¹) * rexp (-π * x) := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hcoef_nonneg : 0 ≤ x ^ (-1 : ℝ) * Real.log x := by
    exact mul_nonneg (rpow_nonneg hxpos.le _) (Real.log_nonneg hx)
  have hcoef_le_one : x ^ (-1 : ℝ) * Real.log x ≤ 1 := by
    rw [Real.rpow_neg_one]
    calc
      x⁻¹ * Real.log x ≤ x⁻¹ * x :=
        mul_le_mul_of_nonneg_left (Real.log_le_self hxpos.le) (inv_nonneg.mpr hxpos.le)
      _ = 1 := inv_mul_cancel₀ hxpos.ne'
  have htail :
      rexp (-π * x) / (1 - rexp (-π * x)) ≤
        (1 - rexp (-π))⁻¹ * rexp (-π * x) :=
    rexp_neg_pi_mul_div_one_sub_le_const_mul_rexp_neg_pi_mul_of_one_le hx
  have htail_nonneg :
      0 ≤ 2 * (rexp (-π * x) / (1 - rexp (-π * x))) := by
    have hden : 0 < 1 - rexp (-π * x) := one_sub_rexp_neg_pi_mul_pos_of_pos hxpos
    positivity
  have hscaled :
      2 * (rexp (-π * x) / (1 - rexp (-π * x))) ≤
        2 * ((1 - rexp (-π))⁻¹ * rexp (-π * x)) :=
    mul_le_mul_of_nonneg_left htail zero_le_two
  calc
    x ^ (-1 : ℝ) * Real.log x *
        (2 * (rexp (-π * x) / (1 - rexp (-π * x))))
        ≤ 1 * (2 * ((1 - rexp (-π))⁻¹ * rexp (-π * x))) :=
          mul_le_mul hcoef_le_one hscaled htail_nonneg zero_le_one
    _ = (2 * (1 - rexp (-π))⁻¹) * rexp (-π * x) := by ring

theorem integrableOn_mellin_log_right_exp_tail :
    IntegrableOn (fun x : ℝ =>
      x ^ (-1 : ℝ) * Real.log x *
        (2 * (rexp (-π * x) / (1 - rexp (-π * x)))))
      (Ioi 1) := by
  have hcont : ContinuousOn (fun x : ℝ =>
      x ^ (-1 : ℝ) * Real.log x *
        (2 * (rexp (-π * x) / (1 - rexp (-π * x)))))
      (Ici 1) := by
    have hpow : ContinuousOn (fun x : ℝ => x ^ (-1 : ℝ)) (Ici 1) :=
      continuous_id.continuousOn.rpow_const fun x hx =>
        Or.inl (ne_of_gt (zero_lt_one.trans_le hx))
    have hlog : ContinuousOn (fun x : ℝ => Real.log x) (Ici 1) := by
      exact continuous_id.continuousOn.log fun x hx =>
        ne_of_gt (zero_lt_one.trans_le hx)
    have hexp : ContinuousOn (fun x : ℝ => rexp (-π * x)) (Ici 1) := by
      fun_prop
    have hden : ∀ x ∈ Ici (1 : ℝ), 1 - rexp (-π * x) ≠ 0 := by
      intro x hx
      exact (one_sub_rexp_neg_pi_mul_pos_of_pos (zero_lt_one.trans_le hx)).ne'
    have hquot : ContinuousOn (fun x : ℝ =>
        rexp (-π * x) / (1 - rexp (-π * x))) (Ici 1) :=
      hexp.div (continuousOn_const.sub hexp) hden
    exact (hpow.mul hlog).mul (continuousOn_const.mul hquot)
  have hO : (fun x : ℝ =>
      x ^ (-1 : ℝ) * Real.log x *
        (2 * (rexp (-π * x) / (1 - rexp (-π * x)))))
      =O[atTop] fun x : ℝ => rexp (-π * x) := by
    have hO' : (fun x : ℝ =>
        x ^ (-1 : ℝ) * Real.log x *
          (2 * (rexp (-π * x) / (1 - rexp (-π * x)))))
        =O[atTop] fun x : ℝ => (2 * (1 - rexp (-π))⁻¹) * rexp (-π * x) := by
      apply Eventually.isBigO
      filter_upwards [eventually_ge_atTop 1] with x hx
      have hxpos : 0 < x := zero_lt_one.trans_le hx
      have hnonneg :
          0 ≤ x ^ (-1 : ℝ) * Real.log x *
            (2 * (rexp (-π * x) / (1 - rexp (-π * x)))) := by
        have hden : 0 < 1 - rexp (-π * x) := one_sub_rexp_neg_pi_mul_pos_of_pos hxpos
        have hxpow : 0 ≤ x ^ (-1 : ℝ) := rpow_nonneg hxpos.le _
        have hxlog : 0 ≤ Real.log x := Real.log_nonneg hx
        have htail : 0 ≤ 2 * (rexp (-π * x) / (1 - rexp (-π * x))) := by
          positivity
        exact mul_nonneg (mul_nonneg hxpow hxlog) htail
      rw [norm_of_nonneg hnonneg]
      exact mellin_log_right_exp_tail_le_const_mul_rexp hx
    exact hO'.trans ((isBigO_refl (fun x : ℝ => rexp (-π * x)) atTop).const_mul_left _)
  exact integrable_of_isBigO_exp_neg pi_pos hcont hO

theorem mellin_log_integral_Ioi_one_le_integral_exp_tail :
    (∫ x : ℝ in Ioi 1,
      x ^ (-1 : ℝ) * Real.log x * ((hurwitzEvenFEPair 0).f_modif x).re) ≤
    ∫ x : ℝ in Ioi 1,
      x ^ (-1 : ℝ) * Real.log x *
        (2 * (rexp (-π * x) / (1 - rexp (-π * x)))) := by
  exact mellin_log_integral_Ioi_one_le_exp_tail integrableOn_mellin_log_right_exp_tail

theorem mellin_log_hurwitzEvenFEPair_f_modif_zero_re_le_integral_exp_tail :
    (mellin (fun t : ℝ => Real.log t • (hurwitzEvenFEPair 0).f_modif t) 0).re ≤
    ∫ x : ℝ in Ioi 1,
      x ^ (-1 : ℝ) * Real.log x *
        (2 * (rexp (-π * x) / (1 - rexp (-π * x)))) := by
  exact mellin_log_hurwitzEvenFEPair_f_modif_zero_re_le_integral_Ioi_one.trans
    mellin_log_integral_Ioi_one_le_integral_exp_tail

theorem mellin_log_right_exp_tail_integral_le_const_integral_rexp :
    (∫ x : ℝ in Ioi 1,
      x ^ (-1 : ℝ) * Real.log x *
        (2 * (rexp (-π * x) / (1 - rexp (-π * x))))) ≤
    ∫ x : ℝ in Ioi 1,
      (2 * (1 - rexp (-π))⁻¹) * rexp (-π * x) := by
  have hboundInt : IntegrableOn (fun x : ℝ =>
      (2 * (1 - rexp (-π))⁻¹) * rexp (-π * x)) (Ioi 1) :=
    (exp_neg_integrableOn_Ioi 1 pi_pos).const_mul _
  exact setIntegral_mono_on integrableOn_mellin_log_right_exp_tail
    hboundInt measurableSet_Ioi fun x hx => by
      exact mellin_log_right_exp_tail_le_const_mul_rexp
        ((by simpa using hx : (1 : ℝ) < x).le)

theorem mellin_log_hurwitzEvenFEPair_f_modif_zero_re_le_integral_const_exp :
    (mellin (fun t : ℝ => Real.log t • (hurwitzEvenFEPair 0).f_modif t) 0).re ≤
    ∫ x : ℝ in Ioi 1,
      (2 * (1 - rexp (-π))⁻¹) * rexp (-π * x) := by
  exact mellin_log_hurwitzEvenFEPair_f_modif_zero_re_le_integral_exp_tail.trans
    mellin_log_right_exp_tail_integral_le_const_integral_rexp

theorem mellin_log_hurwitzEvenFEPair_f_modif_zero_re_le_const_exp_bound :
    (mellin (fun t : ℝ => Real.log t • (hurwitzEvenFEPair 0).f_modif t) 0).re ≤
      (2 * (1 - rexp (-π))⁻¹) * (rexp (-π) / π) := by
  exact mellin_log_hurwitzEvenFEPair_f_modif_zero_re_le_integral_const_exp.trans
    (le_of_eq integral_Ioi_one_const_mul_rexp_neg_pi_mul_eq)

theorem mellin_log_const_exp_bound_lt_seventeen_over_one_sixty :
    (2 * (1 - rexp (-π))⁻¹) * (rexp (-π) / π) < 17 / 160 := by
  have htail : rexp (-π) / π < 1 / 20 :=
    Real.rexp_neg_pi_div_pi_lt_one_twentieth
  have htail_pos : 0 < rexp (-π) / π := div_pos (Real.exp_pos _) pi_pos
  have hconst : 2 * (1 - rexp (-π))⁻¹ < 17 / 8 :=
    Real.two_mul_one_sub_rexp_neg_pi_inv_lt_seventeen_eighths
  have hstep₁ :
      (2 * (1 - rexp (-π))⁻¹) * (rexp (-π) / π) <
        (17 / 8) * (rexp (-π) / π) :=
    mul_lt_mul_of_pos_right hconst htail_pos
  have hstep₂ : (17 / 8 : ℝ) * (rexp (-π) / π) < (17 / 8) * (1 / 20) :=
    mul_lt_mul_of_pos_left htail (by norm_num)
  calc
    (2 * (1 - rexp (-π))⁻¹) * (rexp (-π) / π)
        < (17 / 8) * (rexp (-π) / π) := hstep₁
    _ < (17 / 8) * (1 / 20) := hstep₂
    _ = 17 / 160 := by norm_num

theorem mellin_log_hurwitzEvenFEPair_f_modif_zero_re_lt_seventeen_over_one_sixty :
    (mellin (fun t : ℝ => Real.log t • (hurwitzEvenFEPair 0).f_modif t) 0).re <
      17 / 160 := by
  exact lt_of_le_of_lt
    mellin_log_hurwitzEvenFEPair_f_modif_zero_re_le_const_exp_bound
    mellin_log_const_exp_bound_lt_seventeen_over_one_sixty

theorem liCoefficientCandidate_one_re_pos :
    0 < (liCoefficientCandidate 1).re := by
  rw [liCoefficientCandidate_one_re_pos_iff_mellin_log_hurwitzEvenFEPair_f_modif_zero_re_lt]
  exact mellin_log_hurwitzEvenFEPair_f_modif_zero_re_lt_seventeen_over_one_sixty.trans
    liCoefficientCandidate_zero_threshold_gt_seventeen_over_one_sixty

end

end LeanLab.Riemann
