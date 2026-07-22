import LeanLab.Riemann.WeilGroundStateFiniteMatrix

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Quantitative Rayleigh-gap control for the finite Weil ground-state route

This module isolates a generic variational consumer for the proposed prolate approximation. It
does not assert that the arithmetic Weil matrices or prolate vectors satisfy the required ratio.
-/

open Matrix
open scoped BigOperators Matrix

namespace LeanLab.Riemann

noncomputable section

/-- Quadratic excess above a candidate eigenvalue. -/
def weilRayleighExcess {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (mu : ℝ) (x : ι → ℝ) : ℝ :=
  x ⬝ᵥ (A *ᵥ x) - mu * (x ⬝ᵥ x)

/-- Squared distance to the line spanned by a unit vector `xi`. -/
def weilProjectiveDefect {ι : Type*} [Fintype ι]
    (xi x : ι → ℝ) : ℝ :=
  x ⬝ᵥ x - (xi ⬝ᵥ x) ^ 2

/-- The component left after projecting onto the line spanned by `xi`. -/
def weilGroundLineRemainder {ι : Type*} [Fintype ι]
    (xi x : ι → ℝ) : ι → ℝ :=
  x - (xi ⬝ᵥ x) • xi

theorem weilGroundLineRemainder_orthogonal {ι : Type*} [Fintype ι]
    (xi x : ι → ℝ) (hxi : xi ⬝ᵥ xi = 1) :
    xi ⬝ᵥ weilGroundLineRemainder xi x = 0 := by
  simp [weilGroundLineRemainder, dotProduct_sub, dotProduct_smul, hxi]

theorem weilGroundLine_decomposition {ι : Type*} [Fintype ι]
    (xi x : ι → ℝ) :
    x = (xi ⬝ᵥ x) • xi + weilGroundLineRemainder xi x := by
  ext i
  simp [weilGroundLineRemainder]

theorem weilGroundLineRemainder_dot_self {ι : Type*} [Fintype ι]
    (xi x : ι → ℝ) (hxi : xi ⬝ᵥ xi = 1) :
    weilGroundLineRemainder xi x ⬝ᵥ weilGroundLineRemainder xi x =
      weilProjectiveDefect xi x := by
  simp only [weilGroundLineRemainder, weilProjectiveDefect,
    sub_dotProduct, dotProduct_sub, dotProduct_smul, smul_dotProduct]
  rw [hxi, dotProduct_comm x xi]
  ring

theorem weilProjectiveDefect_eq_one_sub_sq {ι : Type*} [Fintype ι]
    (xi x : ι → ℝ) (hx : x ⬝ᵥ x = 1) :
    weilProjectiveDefect xi x = 1 - (xi ⬝ᵥ x) ^ 2 := by
  simp [weilProjectiveDefect, hx]

theorem weilProjectiveDefect_nonneg {ι : Type*} [Fintype ι]
    (xi x : ι → ℝ) (hxi : xi ⬝ᵥ xi = 1) :
    0 ≤ weilProjectiveDefect xi x := by
  rw [← weilGroundLineRemainder_dot_self xi x hxi]
  simpa using dotProduct_star_self_nonneg (weilGroundLineRemainder xi x)

theorem weilRayleighExcess_smul_eigen_add_orthogonal
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (hAT : Aᵀ = A) (mu : ℝ) (xi y : ι → ℝ)
    (heigen : A *ᵥ xi = mu • xi) (horth : xi ⬝ᵥ y = 0) (c : ℝ) :
    weilRayleighExcess A mu (c • xi + y) =
      weilRayleighExcess A mu y := by
  have horth' : y ⬝ᵥ xi = 0 := by
    rw [dotProduct_comm]
    exact horth
  have hcross : xi ⬝ᵥ (A *ᵥ y) = 0 := by
    have ht := Matrix.dotProduct_transpose_mulVec A y xi
    rw [hAT, heigen] at ht
    calc
      xi ⬝ᵥ (A *ᵥ y) = y ⬝ᵥ (mu • xi) := ht.symm
      _ = 0 := by simp [horth']
  rw [weilRayleighExcess, weilRayleighExcess,
    Matrix.mulVec_add, Matrix.mulVec_smul, heigen]
  simp only [add_dotProduct, dotProduct_add]
  simp [horth, horth', hcross]
  ring

/-- A normalized eigenline with a quantitative Rayleigh gap on its orthogonal complement. -/
structure WeilQuantitativeGroundStateCertificate
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (mu : ℝ) (xi : ι → ℝ) (delta : ℝ) : Prop where
  symmetric : Aᵀ = A
  normalized_xi : xi ⬝ᵥ xi = 1
  eigen_xi : A *ᵥ xi = mu • xi
  gap_pos : 0 < delta
  gap_lower : ∀ y : ι → ℝ, xi ⬝ᵥ y = 0 →
    delta * (y ⬝ᵥ y) ≤ weilRayleighExcess A mu y

theorem WeilQuantitativeGroundStateCertificate.rayleighExcess_eq_remainder
    {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℝ} {mu delta : ℝ} {xi : ι → ℝ}
    (h : WeilQuantitativeGroundStateCertificate A mu xi delta)
    (x : ι → ℝ) :
    weilRayleighExcess A mu x =
      weilRayleighExcess A mu (weilGroundLineRemainder xi x) := by
  conv_lhs => rw [weilGroundLine_decomposition xi x]
  exact weilRayleighExcess_smul_eigen_add_orthogonal
    A h.symmetric mu xi (weilGroundLineRemainder xi x) h.eigen_xi
      (weilGroundLineRemainder_orthogonal xi x h.normalized_xi) (xi ⬝ᵥ x)

theorem WeilQuantitativeGroundStateCertificate.gap_mul_projectiveDefect_le
    {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℝ} {mu delta : ℝ} {xi : ι → ℝ}
    (h : WeilQuantitativeGroundStateCertificate A mu xi delta)
    (x : ι → ℝ) :
    delta * weilProjectiveDefect xi x ≤ weilRayleighExcess A mu x := by
  have hgap := h.gap_lower (weilGroundLineRemainder xi x)
    (weilGroundLineRemainder_orthogonal xi x h.normalized_xi)
  calc
    delta * weilProjectiveDefect xi x =
        delta * (weilGroundLineRemainder xi x ⬝ᵥ weilGroundLineRemainder xi x) := by
          rw [weilGroundLineRemainder_dot_self xi x h.normalized_xi]
    _ ≤ weilRayleighExcess A mu (weilGroundLineRemainder xi x) := hgap
    _ = weilRayleighExcess A mu x := (h.rayleighExcess_eq_remainder x).symm

theorem WeilQuantitativeGroundStateCertificate.projectiveDefect_le_ratio
    {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℝ} {mu delta : ℝ} {xi : ι → ℝ}
    (h : WeilQuantitativeGroundStateCertificate A mu xi delta)
    (x : ι → ℝ) :
    weilProjectiveDefect xi x ≤ weilRayleighExcess A mu x / delta := by
  apply (le_div_iff₀ h.gap_pos).2
  simpa [mul_comm] using h.gap_mul_projectiveDefect_le x

theorem WeilQuantitativeGroundStateCertificate.gap_mul_one_sub_groundCoefficient_sq_le
    {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℝ} {mu delta : ℝ} {xi : ι → ℝ}
    (h : WeilQuantitativeGroundStateCertificate A mu xi delta)
    (x : ι → ℝ) (hx : x ⬝ᵥ x = 1) :
    delta * (1 - (xi ⬝ᵥ x) ^ 2) ≤ weilRayleighExcess A mu x := by
  rw [← weilProjectiveDefect_eq_one_sub_sq xi x hx]
  exact h.gap_mul_projectiveDefect_le x

theorem WeilQuantitativeGroundStateCertificate.one_sub_groundCoefficient_sq_le_ratio
    {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℝ} {mu delta : ℝ} {xi : ι → ℝ}
    (h : WeilQuantitativeGroundStateCertificate A mu xi delta)
    (x : ι → ℝ) (hx : x ⬝ᵥ x = 1) :
    1 - (xi ⬝ᵥ x) ^ 2 ≤ weilRayleighExcess A mu x / delta := by
  rw [← weilProjectiveDefect_eq_one_sub_sq xi x hx]
  exact h.projectiveDefect_le_ratio x

theorem tendsto_projectiveDefect_zero_of_le_ratio
    (defect ratio : ℕ → ℝ)
    (hdefect : ∀ n, 0 ≤ defect n)
    (hle : ∀ n, defect n ≤ ratio n)
    (hratio : Filter.Tendsto ratio Filter.atTop (nhds 0)) :
    Filter.Tendsto defect Filter.atTop (nhds 0) := by
  exact squeeze_zero'
    (Filter.Eventually.of_forall hdefect)
    (Filter.Eventually.of_forall hle) hratio

/-- A two-dimensional family whose spectral gap collapses with its Rayleigh excess. -/
def weilCollapsingGapMatrix (epsilon : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 0; 0, epsilon]

def weilCollapsingGapGround : Fin 2 → ℝ :=
  ![1, 0]

def weilCollapsingGapTest : Fin 2 → ℝ :=
  ![0, 1]

theorem weilCollapsingGapCertificate (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    WeilQuantitativeGroundStateCertificate
      (weilCollapsingGapMatrix epsilon) 0 weilCollapsingGapGround epsilon := by
  refine
    { symmetric := ?_
      normalized_xi := ?_
      eigen_xi := ?_
      gap_pos := hepsilon
      gap_lower := ?_ }
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [weilCollapsingGapMatrix, Matrix.transpose]
  · norm_num [weilCollapsingGapGround, dotProduct, Fin.sum_univ_two]
  · ext i
    fin_cases i <;>
      norm_num [weilCollapsingGapMatrix, weilCollapsingGapGround,
        Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · intro y horth
    have hy0 : y 0 = 0 := by
      simpa [weilCollapsingGapGround, dotProduct, Fin.sum_univ_two] using horth
    simp [weilRayleighExcess, weilCollapsingGapMatrix, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, hy0]
    ring_nf
    exact le_rfl

theorem weilCollapsingGap_projectiveDefect :
    weilProjectiveDefect weilCollapsingGapGround weilCollapsingGapTest = 1 := by
  norm_num [weilProjectiveDefect, weilCollapsingGapGround, weilCollapsingGapTest,
    dotProduct, Fin.sum_univ_two]

theorem weilCollapsingGap_rayleighExcess (epsilon : ℝ) :
    weilRayleighExcess (weilCollapsingGapMatrix epsilon) 0 weilCollapsingGapTest = epsilon := by
  norm_num [weilRayleighExcess, weilCollapsingGapMatrix, weilCollapsingGapTest,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]

def weilCollapsingGapScale (n : ℕ) : ℝ :=
  1 / (n + 1 : ℝ)

theorem weilCollapsingGapScale_pos (n : ℕ) :
    0 < weilCollapsingGapScale n := by
  unfold weilCollapsingGapScale
  positivity

theorem tendsto_weilCollapsingGap_rayleighExcess :
    Filter.Tendsto
      (fun n : ℕ => weilRayleighExcess
        (weilCollapsingGapMatrix (weilCollapsingGapScale n)) 0 weilCollapsingGapTest)
      Filter.atTop (nhds 0) := by
  simpa [weilCollapsingGap_rayleighExcess, weilCollapsingGapScale, one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem weilCollapsingGap_ratio_eq_one (n : ℕ) :
    weilRayleighExcess
        (weilCollapsingGapMatrix (weilCollapsingGapScale n)) 0 weilCollapsingGapTest /
      weilCollapsingGapScale n = 1 := by
  rw [weilCollapsingGap_rayleighExcess]
  exact div_self (ne_of_gt (weilCollapsingGapScale_pos n))

theorem weilCollapsingGapAudit_endpoint :
    Filter.Tendsto
        (fun n : ℕ => weilRayleighExcess
          (weilCollapsingGapMatrix (weilCollapsingGapScale n)) 0 weilCollapsingGapTest)
        Filter.atTop (nhds 0) ∧
      (∀ _n : ℕ,
        weilProjectiveDefect weilCollapsingGapGround weilCollapsingGapTest = 1) ∧
      (∀ n : ℕ,
        weilRayleighExcess
            (weilCollapsingGapMatrix (weilCollapsingGapScale n)) 0 weilCollapsingGapTest /
          weilCollapsingGapScale n = 1) := by
  exact ⟨tendsto_weilCollapsingGap_rayleighExcess,
    fun _ => weilCollapsingGap_projectiveDefect,
    weilCollapsingGap_ratio_eq_one⟩

end

end LeanLab.Riemann
