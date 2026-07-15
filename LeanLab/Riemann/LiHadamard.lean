import LeanLab.Riemann.LiZeroDivisor
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaHadamard

set_option linter.style.header false

/-!
# Global Hadamard bridge for the project xi function

This file identifies the project-local `riemannXi` with the independently audited
`Complex.riemannXi`, then transports the order-one growth, multiplicity-indexed canonical product,
and logarithmic-derivative zero sum to the project's `IsNontrivialZero` carrier.
-/

namespace LeanLab.Riemann

open Complex Function Set
open scoped BigOperators

noncomputable section

/-- The project xi definition and the audited finite-order xi definition are the same function. -/
theorem riemannXi_eq_complex_riemannXi :
    riemannXi = Complex.riemannXi := by
  funext s
  simp only [riemannXi, Complex.riemannXi]
  ring

/-- The previous campaign's divisor is exactly the divisor used by the audited Hadamard theory. -/
theorem riemannXiZeroDivisor_eq_complex_riemannXi_divisor :
    riemannXiZeroDivisor = MeromorphicOn.divisor Complex.riemannXi univ := by
  rw [riemannXiZeroDivisor, riemannXi_eq_complex_riemannXi]

/-- The natural size of the divisor-index fiber is the project's analytic zero multiplicity. -/
theorem riemannXi_divisor_toNat_eq_zeroMultiplicity (s : ℂ) :
    Int.toNat (MeromorphicOn.divisor riemannXi univ s) =
      riemannXiZeroMultiplicity s := by
  have hdiv :
      MeromorphicOn.divisor riemannXi univ s = (riemannXiZeroMultiplicity s : ℤ) := by
    simpa [riemannXiZeroDivisor] using riemannXiZeroDivisor_apply s
  rw [hdiv]
  simp

/-- A nonzero divisor index always lies over a project nontrivial zeta zero. -/
theorem riemannXiDivisorZeroIndex_val_isNontrivialZero
    (p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (univ : Set ℂ)) :
    IsNontrivialZero (Complex.Hadamard.divisorZeroIndex₀_val p) := by
  have hp : Complex.Hadamard.divisorZeroIndex₀_val p ∈
      Function.support riemannXiZeroDivisor := by
    exact Complex.Hadamard.divisorZeroIndex₀_val_mem_divisor_support' (p := p)
  rw [support_riemannXiZeroDivisor] at hp
  exact hp

/-- Every project nontrivial zero occurs in the multiplicity-bearing nonzero divisor index. -/
theorem exists_riemannXiDivisorZeroIndex_of_isNontrivialZero
    {ρ : ℂ} (hρ : IsNontrivialZero ρ) :
    ∃ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (univ : Set ℂ),
      Complex.Hadamard.divisorZeroIndex₀_val p = ρ := by
  have hmult : 0 < riemannXiZeroMultiplicity ρ :=
    (riemannXiZeroMultiplicity_pos_iff ρ).2 hρ
  have hfiber : 0 < Int.toNat (MeromorphicOn.divisor riemannXi univ ρ) := by
    rw [riemannXi_divisor_toNat_eq_zeroMultiplicity]
    exact hmult
  let q : Complex.Hadamard.divisorZeroIndex riemannXi (univ : Set ℂ) :=
    ⟨ρ, ⟨0, hfiber⟩⟩
  refine ⟨⟨q, ne_zero_of_isNontrivialZero hρ⟩, rfl⟩

/-- The values represented by the nonzero xi divisor index are exactly the nontrivial zeros. -/
theorem exists_riemannXiDivisorZeroIndex_val_iff (ρ : ℂ) :
    (∃ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (univ : Set ℂ),
      Complex.Hadamard.divisorZeroIndex₀_val p = ρ) ↔ IsNontrivialZero ρ := by
  constructor
  · rintro ⟨p, rfl⟩
    exact riemannXiDivisorZeroIndex_val_isNontrivialZero p
  · exact exists_riemannXiDivisorZeroIndex_of_isNontrivialZero

/-- The project xi function has entire-function order at most one. -/
theorem riemannXi_entireOfOrderAtMost_one :
    Complex.Hadamard.EntireOfOrderAtMost (1 : ℝ) riemannXi := by
  rw [riemannXi_eq_complex_riemannXi]
  exact _root_.riemannXi_entireOfOrderAtMost_one

/-- The squared reciprocal norms of the nonzero xi zeros, repeated by multiplicity, are summable. -/
theorem summable_riemannXiDivisorZeroIndex_norm_inv_sq :
    Summable
      (fun p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (univ : Set ℂ) =>
        ‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹ ^ (2 : ℕ)) := by
  rw [riemannXi_eq_complex_riemannXi]
  exact _root_.summable_riemannXi_divisorZeroIndex₀_norm_inv_sq

/-- Genus-one Hadamard factorization for the project xi function, with no origin monomial. -/
theorem exists_riemannXi_hadamard_factorization :
    ∃ P : Polynomial ℂ, P.degree ≤ 1 ∧ ∀ z : ℂ,
      riemannXi z = Complex.exp (Polynomial.eval z P) *
        Complex.Hadamard.divisorCanonicalProduct 1 riemannXi (univ : Set ℂ) z := by
  rw [riemannXi_eq_complex_riemannXi]
  exact _root_.riemannXi_hadamard_factorization_no_monomial

/-- The genus-one logarithmic-derivative zero terms are summable off the nontrivial zero set. -/
theorem summable_riemannXi_logDerivTerms_of_not_isNontrivialZero
    {z : ℂ} (hz : ¬IsNontrivialZero z) :
    Summable
      (fun p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (univ : Set ℂ) =>
        1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
          1 / Complex.Hadamard.divisorZeroIndex₀_val p) := by
  apply Complex.Hadamard.summable_logDerivTerms_divisorZeroIndex₀_of_summable_inv_sq
    summable_riemannXiDivisorZeroIndex_norm_inv_sq
  intro p hzp
  apply hz
  rw [hzp]
  exact riemannXiDivisorZeroIndex_val_isNontrivialZero p

/-- Global logarithmic-derivative formula for the project xi function away from its zeros. -/
theorem exists_riemannXi_logDeriv_eq_polynomial_derivative_add_tsum
    {z : ℂ} (hz : ¬IsNontrivialZero z) :
    ∃ P : Polynomial ℂ, P.degree ≤ 1 ∧
      logDeriv riemannXi z = Polynomial.eval z P.derivative +
        ∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (univ : Set ℂ),
          (1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
            1 / Complex.Hadamard.divisorZeroIndex₀_val p) := by
  have haway :
      ∀ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (univ : Set ℂ),
        z ≠ Complex.Hadamard.divisorZeroIndex₀_val p := by
    intro p hzp
    apply hz
    rw [hzp]
    exact riemannXiDivisorZeroIndex_val_isNontrivialZero p
  rw [riemannXi_eq_complex_riemannXi] at haway ⊢
  exact _root_.exists_riemannXi_logDeriv_eq_polynomial_derivative_add_tsum haway

end

end LeanLab.Riemann
