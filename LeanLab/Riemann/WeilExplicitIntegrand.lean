import LeanLab.Riemann.LiHadamard
import Mathlib.NumberTheory.LSeries.Dirichlet

set_option linter.style.header false

/-!
# The right-half-plane integrand of Weil's explicit formula

This module joins the project's xi logarithmic derivative to the pole terms, the real-place
Gamma factor, and the von Mangoldt Dirichlet series on `re s > 1`. It then splices that identity
with the compiled genus-one Hadamard zero sum. No contour limit or regularization is asserted.
-/

namespace LeanLab.Riemann

open Complex Filter Function Set
open scoped BigOperators LSeries.notation Topology

noncomputable section

/-- Deligne's real Gamma factor is differentiable throughout the positive half-plane. -/
theorem differentiableAt_GammaR_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ Gammaℝ s := by
  change DifferentiableAt ℂ
    (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Gamma (z / 2)) s
  refine ((differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow ?_).mul ?_
  · exact Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero)
  · refine (differentiableAt_Gamma (s / 2) ?_).comp s
      (differentiableAt_id.div_const (2 : ℂ))
    intro m
    apply ne_of_apply_ne re
    have hpos : 0 < (s / 2).re := by
      norm_num [div_re]
      linarith
    have hnonpos : (-((m : ℕ) : ℂ)).re ≤ 0 := by simp
    exact ne_of_gt (lt_of_le_of_lt hnonpos hpos)

/-- The elementary pole-removal factor contributes the two simple pole terms. -/
theorem logDeriv_riemannXiFactor {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    logDeriv (fun z : ℂ => z * (z - 1) / 2) s = 1 / s + 1 / (s - 1) := by
  rw [logDeriv_apply, deriv_riemannXi_factor]
  field_simp [hs0, sub_ne_zero.mpr hs1]
  ring

/-- On the Euler-product half-plane, project xi is the pole-removal factor times the real Gamma
factor and the Riemann zeta function. -/
theorem riemannXi_eq_factor_mul_GammaR_mul_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    riemannXi s = s * (s - 1) / 2 * Gammaℝ s * riemannZeta s := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hgamma : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (lt_trans zero_lt_one hs)
  rw [riemannXi_eq_mul_completedRiemannZeta hs0 hs1,
    riemannZeta_def_of_ne_zero hs0]
  field_simp

/-- The von Mangoldt L-series is the negative zeta logarithmic derivative on `re s > 1`. -/
theorem logDeriv_riemannZeta_eq_neg_vonMangoldtLSeries {s : ℂ} (hs : 1 < s.re) :
    logDeriv riemannZeta s = -L ↗ArithmeticFunction.vonMangoldt s := by
  have h := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  rw [logDeriv_apply]
  calc
    deriv riemannZeta s / riemannZeta s =
        -(-deriv riemannZeta s / riemannZeta s) := by ring
    _ = -L ↗ArithmeticFunction.vonMangoldt s := by rw [h]

/-- The exact right-half-plane analytic integrand underlying Weil's explicit formula. -/
theorem logDeriv_riemannXi_eq_poles_archimedean_sub_vonMangoldt
    {s : ℂ} (hs : 1 < s.re) :
    logDeriv riemannXi s =
      1 / s + 1 / (s - 1) + logDeriv Gammaℝ s -
        L ↗ArithmeticFunction.vonMangoldt s := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hgamma : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (lt_trans zero_lt_one hs)
  have hzeta : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  let A : ℂ → ℂ := fun z => z * (z - 1) / 2
  have hA : A s ≠ 0 := by
    dsimp [A]
    exact div_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) (by norm_num)
  have hdA : DifferentiableAt ℂ A s := by
    dsimp [A]
    fun_prop
  have hdGamma : DifferentiableAt ℂ Gammaℝ s :=
    differentiableAt_GammaR_of_re_pos (lt_trans zero_lt_one hs)
  have hdZeta : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have hAGamma : A s * Gammaℝ s ≠ 0 := mul_ne_zero hA hgamma
  have hxi : riemannXi =ᶠ[𝓝 s] fun z => A z * Gammaℝ z * riemannZeta z := by
    filter_upwards [isOpen_lt continuous_const continuous_re |>.mem_nhds hs] with z hz
    simpa [A] using riemannXi_eq_factor_mul_GammaR_mul_riemannZeta hz
  have hlogEq :
      logDeriv riemannXi s = logDeriv (fun z => A z * Gammaℝ z * riemannZeta z) s := by
    rw [logDeriv_apply, logDeriv_apply, hxi.deriv_eq, hxi.self_of_nhds]
  rw [hlogEq,
    logDeriv_mul (f := fun z => A z * Gammaℝ z) (g := riemannZeta)
      s hAGamma hzeta (hdA.mul hdGamma) hdZeta,
    logDeriv_mul (f := A) (g := Gammaℝ) s hA hgamma hdA hdGamma,
    show logDeriv A s = 1 / s + 1 / (s - 1) by
      simpa [A] using logDeriv_riemannXiFactor hs0 hs1,
    logDeriv_riemannZeta_eq_neg_vonMangoldtLSeries hs]
  ring

/-- The Hadamard zero sum and the prime/archimedean integrand are the same logarithmic derivative
on the Euler-product half-plane. -/
theorem exists_weilExplicitIntegrand_eq_hadamardZeroSum
    {s : ℂ} (hs : 1 < s.re) :
    ∃ P : Polynomial ℂ, P.degree ≤ 1 ∧
      Polynomial.eval s P.derivative +
          ∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (univ : Set ℂ),
            (1 / (s - Complex.Hadamard.divisorZeroIndex₀_val p) +
              1 / Complex.Hadamard.divisorZeroIndex₀_val p) =
        1 / s + 1 / (s - 1) + logDeriv Gammaℝ s -
          L ↗ArithmeticFunction.vonMangoldt s := by
  have hzeta : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hnot : ¬IsNontrivialZero s := by
    intro hzero
    exact hzeta hzero.1
  obtain ⟨P, hP, hzeroSum⟩ :=
    exists_riemannXi_logDeriv_eq_polynomial_derivative_add_tsum hnot
  refine ⟨P, hP, ?_⟩
  calc
    Polynomial.eval s P.derivative +
          ∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (univ : Set ℂ),
            (1 / (s - Complex.Hadamard.divisorZeroIndex₀_val p) +
              1 / Complex.Hadamard.divisorZeroIndex₀_val p) =
        logDeriv riemannXi s := hzeroSum.symm
    _ = 1 / s + 1 / (s - 1) + logDeriv Gammaℝ s -
          L ↗ArithmeticFunction.vonMangoldt s :=
      logDeriv_riemannXi_eq_poles_archimedean_sub_vonMangoldt hs

end

end LeanLab.Riemann
