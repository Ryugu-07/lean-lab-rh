import LeanLab.Riemann.DeBruijnNewmanPolymathRiemannSiegelShift

set_option linter.style.header false

/-!
# Finite Riemann--Siegel source decomposition

This file telescopes the adjacent source-contour shift and transports the resulting finite sum
through the exact completed-zeta prefactor used in `R_(0,N)`.
-/

open scoped BigOperators

namespace LeanLab.Riemann

noncomputable section

/-- The adjacent contour shifts telescope from the initial source line to any natural-indexed
source line. -/
theorem deBruijnNewmanRiemannSiegelRawIntegral_finite_shift
    (N : ℕ) (s : ℂ) :
    deBruijnNewmanRiemannSiegelRawIntegral 0 s =
      (∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℂ) ^ (-s)) +
        deBruijnNewmanRiemannSiegelRawIntegral N s := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [ih, deBruijnNewmanRiemannSiegelRawIntegral_adjacent_shift,
        Finset.sum_range_succ]
      ring

/-- Exact finite decomposition of the source remainder `R_(0,0)` into residue terms and the
shifted remainder `R_(0,N)`. -/
theorem deBruijnNewmanRiemannSiegelR0N_finite_decomposition
    (N : ℕ) (s : ℂ) :
    deBruijnNewmanRiemannSiegelR0N 0 s =
      (∑ k ∈ Finset.range N, deBruijnNewmanRiemannSiegelR0Term (k + 1) s) +
        deBruijnNewmanRiemannSiegelR0N N s := by
  simp only [deBruijnNewmanRiemannSiegelR0N, deBruijnNewmanRiemannSiegelR0Term]
  rw [deBruijnNewmanRiemannSiegelRawIntegral_finite_shift, mul_add, Finset.mul_sum]

end

end LeanLab.Riemann
