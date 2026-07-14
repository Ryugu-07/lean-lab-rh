import LeanLab.Riemann.BurnolGram
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

set_option linter.style.header false

/-!
# Burnol's finite-zero-set lower bound

This file formalizes the finite orthogonal-projection assembly in Burnol's lower bound.
-/

noncomputable section

open Complex Filter Metric Set
open scoped ComplexConjugate ENNReal InnerProductSpace Real Topology

namespace LeanLab.Riemann

/-- The canonical natural multiplicity of a zeta zero. -/
def burnolZetaZeroMultiplicity (rho : ℂ) : ℕ :=
  analyticOrderNatAt riemannZeta rho

theorem analyticOrderAt_riemannZeta_ne_top_of_isNontrivialZero
    {rho : ℂ} (hrho : IsNontrivialZero rho) :
    analyticOrderAt riemannZeta rho ≠ ⊤ := by
  have hconnected : IsPreconnected ({1} : Set ℂ)ᶜ :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
  have hzero : analyticOrderAt riemannZeta (0 : ℂ) ≠ ⊤ := by
    have hzeta0 : riemannZeta (0 : ℂ) ≠ 0 := by
      rw [riemannZeta_zero]
      norm_num
    have horder0 : analyticOrderAt riemannZeta (0 : ℂ) = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr hzeta0)
    rw [horder0]
    exact ENat.zero_ne_top
  exact analyticOn_riemannZeta.analyticOrderAt_ne_top_of_isPreconnected
    hconnected (by simp) (by simpa using hrho.2.2) hzero

theorem burnolZetaZeroMultiplicity_cast
    {rho : ℂ} (hrho : IsNontrivialZero rho) :
    (burnolZetaZeroMultiplicity rho : ℕ∞) = analyticOrderAt riemannZeta rho := by
  exact Nat.cast_analyticOrderNatAt
    (analyticOrderAt_riemannZeta_ne_top_of_isNontrivialZero hrho)

theorem burnolZetaZeroMultiplicity_pos
    {rho : ℂ} (hrho : IsNontrivialZero rho) :
    0 < burnolZetaZeroMultiplicity rho := by
  have hanalytic : AnalyticAt ℂ riemannZeta rho :=
    analyticOn_riemannZeta rho (by simpa using hrho.2.2)
  have horder : analyticOrderAt riemannZeta rho ≠ 0 :=
    analyticOrderAt_ne_zero.mpr ⟨hanalytic, hrho.1⟩
  apply Nat.pos_of_ne_zero
  intro hzero
  apply horder
  rw [← burnolZetaZeroMultiplicity_cast hrho, hzero]
  rfl

/-! ## Finite Gram projections -/

section FiniteGramProjection

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [Fintype ι] [DecidableEq ι]

/-- Coefficients of the explicit finite Gram projection. -/
def finiteGramProjectionCoeffs (v : ι → E) (x : E) : ι → ℂ :=
  Matrix.mulVec (Matrix.gram ℂ v)⁻¹ fun i => inner ℂ (v i) x

/-- The explicit finite Gram projection formed from inverse-Gram coefficients. -/
def finiteGramProjection (v : ι → E) (x : E) : E :=
  ∑ i, finiteGramProjectionCoeffs v x i • v i

theorem gram_mulVec_finiteGramProjectionCoeffs
    {v : ι → E} {x : E} (hdet : (Matrix.gram ℂ v).det ≠ 0) :
    Matrix.mulVec (Matrix.gram ℂ v) (finiteGramProjectionCoeffs v x) =
      fun i => inner ℂ (v i) x := by
  rw [finiteGramProjectionCoeffs, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]

theorem inner_finiteGramProjection
    {v : ι → E} {x : E} (hdet : (Matrix.gram ℂ v).det ≠ 0) (i : ι) :
    inner ℂ (v i) (finiteGramProjection v x) = inner ℂ (v i) x := by
  have hcoeff := congrFun
    (gram_mulVec_finiteGramProjectionCoeffs (v := v) (x := x) hdet) i
  simpa [finiteGramProjection, Matrix.mulVec, dotProduct, inner_sum,
    inner_smul_right, mul_comm] using hcoeff

theorem finiteGramProjection_mem_span (v : ι → E) (x : E) :
    finiteGramProjection v x ∈ Submodule.span ℂ (Set.range v) := by
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_range_self i))

theorem sub_finiteGramProjection_mem_orthogonal
    {v : ι → E} {x : E} (hdet : (Matrix.gram ℂ v).det ≠ 0) :
    x - finiteGramProjection v x ∈ (Submodule.span ℂ (Set.range v))ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro u hu
  refine Submodule.span_induction
    (p := fun u _ => inner ℂ u (x - finiteGramProjection v x) = 0)
    ?gen ?zero ?add ?smul hu
  · rintro _ ⟨i, rfl⟩
    rw [inner_sub_right, inner_finiteGramProjection hdet, sub_self]
  · simp
  · intro y z hy hz hy0 hz0
    simp only [inner_add_left, hy0, hz0, add_zero]
  · intro c y hy hy0
    simp only [inner_smul_left, hy0, mul_zero]

theorem norm_finiteGramProjection_le_infDist
    {v : ι → E} {x : E} {K : Submodule ℂ E}
    (hdet : (Matrix.gram ℂ v).det ≠ 0)
    (hv : ∀ i, v i ∈ Kᗮ) :
    ‖finiteGramProjection v x‖ ≤ infDist x (K : Set E) := by
  let H := Submodule.span ℂ (Set.range v)
  letI : FiniteDimensional ℂ H :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range v)
  letI : CompleteSpace H := FiniteDimensional.complete ℂ H
  have hHK : H ≤ Kᗮ := by
    apply Submodule.span_le.2
    rintro _ ⟨i, rfl⟩
    exact hv i
  apply (le_infDist K.nonempty).2
  intro c hc
  have hcH : c ∈ Hᗮ := by
    rw [Submodule.mem_orthogonal]
    intro y hy
    rw [inner_eq_zero_symm]
    exact hHK hy c hc
  have hprojc : H.starProjection c = 0 :=
    H.starProjection_apply_eq_zero_iff.mpr hcH
  have hprojx : H.starProjection x = finiteGramProjection v x := by
    apply H.eq_starProjection_of_mem_of_inner_eq_zero
    · exact finiteGramProjection_mem_span v x
    · intro u hu
      rw [inner_eq_zero_symm]
      exact sub_finiteGramProjection_mem_orthogonal hdet u hu
  calc
    ‖finiteGramProjection v x‖ = ‖H.starProjection x‖ := by rw [hprojx]
    _ = ‖H.starProjection (x - c)‖ := by rw [map_sub, hprojc, sub_zero]
    _ ≤ ‖x - c‖ := H.norm_starProjection_apply_le (x - c)
    _ = dist x c := by rw [dist_eq_norm]

end FiniteGramProjection

/-! ## Burnol's finite vector family -/

section BurnolFiniteFamily

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Burnol's normalized vectors with a parameter-dependent number of derivatives. -/
def burnolFiniteVector (lambda : ℝ) (rho : ι → ℂ) (multiplicity : ι → ℕ) :
    (Σ a, Fin (multiplicity a)) → positiveHalfLineComplexL2 :=
  fun i => burnolX lambda (rho i.1) (i.2 : ℕ)

/-- The conventional Gram matrix `inner (v i) (v j)` of the finite Burnol family. -/
def burnolConventionalGramMatrix
    (lambda : ℝ) (rho : ι → ℂ) (multiplicity : ι → ℕ) :
    Matrix (Σ a, Fin (multiplicity a)) (Σ a, Fin (multiplicity a)) ℂ :=
  Matrix.gram ℂ (burnolFiniteVector lambda rho multiplicity)

omit [Fintype ι] [DecidableEq ι] in
theorem burnolConventionalGramMatrix_eq_transpose
    (lambda : ℝ) (rho : ι → ℂ) (multiplicity : ι → ℕ) :
    burnolConventionalGramMatrix lambda rho multiplicity =
      (burnolFiniteGramMatrix lambda rho multiplicity).transpose := by
  ext i j
  rfl

omit [Fintype ι] in
theorem burnolFiniteHilbertMatrix_transpose (multiplicity : ι → ℕ) :
    (burnolFiniteHilbertMatrix multiplicity).transpose =
      burnolFiniteHilbertMatrix multiplicity := by
  ext ⟨a, i⟩ ⟨b, j⟩
  by_cases hab : a = b
  · subst b
    simp [burnolFiniteHilbertMatrix, Matrix.blockDiagonal'_apply,
      burnolHilbertMatrix, add_comm]
  · have hba : b ≠ a := fun h => hab h.symm
    simp [burnolFiniteHilbertMatrix, Matrix.blockDiagonal'_apply, hab, hba]

omit [Fintype ι] in
theorem tendsto_burnolConventionalGramMatrix
    {rho : ι → ℂ} (hcritical : ∀ a, (rho a).re = 1 / 2)
    (hinjective : Function.Injective rho) (multiplicity : ι → ℕ) :
    Tendsto (fun lambda : ℝ =>
      burnolConventionalGramMatrix lambda rho multiplicity)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (burnolFiniteHilbertMatrix multiplicity)) := by
  have hbase := tendsto_burnolFiniteGramMatrix
    hcritical hinjective multiplicity
  have htranspose := continuous_id.matrix_transpose.continuousAt.tendsto.comp hbase
  change Tendsto (fun lambda : ℝ =>
      (burnolFiniteGramMatrix lambda rho multiplicity).transpose)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (burnolFiniteHilbertMatrix multiplicity).transpose) at htranspose
  simpa only [burnolConventionalGramMatrix_eq_transpose,
    burnolFiniteHilbertMatrix_transpose] using htranspose

theorem tendsto_burnolConventionalGramMatrix_inv
    {rho : ι → ℂ} (hcritical : ∀ a, (rho a).re = 1 / 2)
    (hinjective : Function.Injective rho) (multiplicity : ι → ℕ) :
    Tendsto (fun lambda : ℝ =>
      (burnolConventionalGramMatrix lambda rho multiplicity)⁻¹)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (burnolFiniteHilbertMatrix multiplicity)⁻¹) :=
  tendsto_matrix_nonsingInv
    (tendsto_burnolConventionalGramMatrix hcritical hinjective multiplicity)
    (burnolFiniteHilbertMatrix_det_ne_zero multiplicity)

theorem eventually_burnolConventionalGramMatrix_det_ne_zero
    {rho : ι → ℂ} (hcritical : ∀ a, (rho a).re = 1 / 2)
    (hinjective : Function.Injective rho) (multiplicity : ι → ℕ) :
    ∀ᶠ lambda in nhdsWithin (0 : ℝ) (Ioi 0),
      (burnolConventionalGramMatrix lambda rho multiplicity).det ≠ 0 := by
  have hdet : Tendsto (fun lambda : ℝ =>
      (burnolConventionalGramMatrix lambda rho multiplicity).det)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (burnolFiniteHilbertMatrix multiplicity).det) :=
    continuous_id.matrix_det.continuousAt.tendsto.comp
      (tendsto_burnolConventionalGramMatrix hcritical hinjective multiplicity)
  exact hdet.eventually
    (isOpen_compl_singleton.mem_nhds
      (burnolFiniteHilbertMatrix_det_ne_zero multiplicity))

omit [Fintype ι] [DecidableEq ι] in
/-- Every retained normalized zero vector is orthogonal to Burnol's model space. -/
theorem burnolFiniteVector_mem_modelKernelSpan_orthogonal
    {lambda : ℝ} (hlambda0 : 0 < lambda) (hlambda1 : lambda ≤ 1)
    {rho : ι → ℂ} (hcritical : ∀ a, (rho a).re = 1 / 2)
    (hzero : ∀ a, IsNontrivialZero (rho a))
    (i : Σ a, Fin (burnolZetaZeroMultiplicity (rho a))) :
    burnolFiniteVector lambda rho
        (fun a => burnolZetaZeroMultiplicity (rho a)) i ∈
      (burnolModelKernelSpan lambda)ᗮ := by
  rw [burnolFiniteVector, burnolX]
  apply Submodule.smul_mem
  apply burnolY_mem_modelKernelSpan_orthogonal
    hlambda0 hlambda1 (rho i.1) (i.2 : ℕ) (hcritical i.1) (hzero i.1).1
  calc
    ((i.2 : ℕ) + 1 : ℕ∞) ≤
        (burnolZetaZeroMultiplicity (rho i.1) : ℕ∞) := by
      exact_mod_cast Nat.succ_le_iff.mpr i.2.isLt
    _ = analyticOrderAt riemannZeta (rho i.1) :=
      burnolZetaZeroMultiplicity_cast (hzero i.1)

/-- The finite inverse-Gram projection of `chi1` at selected zeta zeros. -/
def burnolFiniteZetaProjection
    (lambda : ℝ) (rho : ι → ℂ) : positiveHalfLineComplexL2 :=
  finiteGramProjection
    (burnolFiniteVector lambda rho
      (fun a => burnolZetaZeroMultiplicity (rho a)))
    burnolChiOneL2

theorem norm_burnolFiniteZetaProjection_le_distance
    {lambda : ℝ} (hlambda0 : 0 < lambda) (hlambda1 : lambda ≤ 1)
    {rho : ι → ℂ} (hcritical : ∀ a, (rho a).re = 1 / 2)
    (hzero : ∀ a, IsNontrivialZero (rho a))
    (hdet : (burnolConventionalGramMatrix lambda rho
      (fun a => burnolZetaZeroMultiplicity (rho a))).det ≠ 0) :
    ‖burnolFiniteZetaProjection lambda rho‖ ≤ burnolDistance lambda := by
  rw [burnolDistance_eq_modelDistance]
  apply norm_finiteGramProjection_le_infDist hdet
  intro i
  exact burnolFiniteVector_mem_modelKernelSpan_orthogonal
    hlambda0 hlambda1 hcritical hzero i

/-! ### Scaled target vector and projection energy -/

/-- The `sqrt(log(1/lambda))`-scaled target pairings. -/
def burnolScaledTargetVector
    (lambda : ℝ) (rho : ι → ℂ) (multiplicity : ι → ℕ) :
    (Σ a, Fin (multiplicity a)) → ℂ :=
  fun i => ((Real.sqrt (burnolLogScale lambda) : ℝ) : ℂ) *
    inner ℂ (burnolFiniteVector lambda rho multiplicity i) burnolChiOneL2

/-- The limiting scaled target vector; only the zeroth derivative survives. -/
def burnolLimitTargetVector
    (rho : ι → ℂ) (multiplicity : ι → ℕ) :
    (Σ a, Fin (multiplicity a)) → ℂ :=
  fun i => if (i.2 : ℕ) = 0 then (rho i.1 - 1) / (rho i.1) ^ 2 else 0

omit [Fintype ι] [DecidableEq ι] in
theorem tendsto_burnolScaledTargetVector
    {rho : ι → ℂ} (hcritical : ∀ a, (rho a).re = 1 / 2)
    (multiplicity : ι → ℕ) :
    Tendsto (fun lambda : ℝ =>
      burnolScaledTargetVector lambda rho multiplicity)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (burnolLimitTargetVector rho multiplicity)) := by
  rw [tendsto_pi_nhds]
  rintro ⟨a, k⟩
  simpa [burnolScaledTargetVector, burnolFiniteVector,
    burnolLimitTargetVector] using
      tendsto_sqrtLog_inner_chiOne_burnolX (hcritical a) (k : ℕ)

/-- Coefficients of the scaled finite Burnol projection. -/
def burnolScaledProjectionCoeffs
    (lambda : ℝ) (rho : ι → ℂ) (multiplicity : ι → ℕ) :
    (Σ a, Fin (multiplicity a)) → ℂ :=
  Matrix.mulVec (burnolConventionalGramMatrix lambda rho multiplicity)⁻¹
    (burnolScaledTargetVector lambda rho multiplicity)

/-- The limiting inverse-Hilbert coefficients. -/
def burnolLimitProjectionCoeffs
    (rho : ι → ℂ) (multiplicity : ι → ℕ) :
    (Σ a, Fin (multiplicity a)) → ℂ :=
  Matrix.mulVec (burnolFiniteHilbertMatrix multiplicity)⁻¹
    (burnolLimitTargetVector rho multiplicity)

theorem tendsto_burnolScaledProjectionCoeffs
    {rho : ι → ℂ} (hcritical : ∀ a, (rho a).re = 1 / 2)
    (hinjective : Function.Injective rho) (multiplicity : ι → ℕ) :
    Tendsto (fun lambda : ℝ =>
      burnolScaledProjectionCoeffs lambda rho multiplicity)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (burnolLimitProjectionCoeffs rho multiplicity)) := by
  rw [tendsto_pi_nhds]
  intro i
  simp only [burnolScaledProjectionCoeffs, burnolLimitProjectionCoeffs,
    Matrix.mulVec, dotProduct]
  apply tendsto_finsetSum
  intro j _
  have hinv := tendsto_matrix_nonsingInv_apply
    (tendsto_burnolConventionalGramMatrix hcritical hinjective multiplicity)
    (burnolFiniteHilbertMatrix_det_ne_zero multiplicity) i j
  have htarget := tendsto_sqrtLog_inner_chiOne_burnolX
    (hcritical j.1) (j.2 : ℕ)
  have htarget' : Tendsto (fun lambda : ℝ =>
      burnolScaledTargetVector lambda rho multiplicity j)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (burnolLimitTargetVector rho multiplicity j)) := by
    simpa [burnolScaledTargetVector, burnolFiniteVector,
      burnolLimitTargetVector] using htarget
  exact hinv.mul htarget'

/-- The real quadratic energy of the scaled explicit projection. -/
def burnolScaledProjectionEnergy
    (lambda : ℝ) (rho : ι → ℂ) (multiplicity : ι → ℕ) : ℝ :=
  Complex.re (dotProduct (star (burnolScaledProjectionCoeffs lambda rho multiplicity))
    (Matrix.mulVec (burnolConventionalGramMatrix lambda rho multiplicity)
      (burnolScaledProjectionCoeffs lambda rho multiplicity)))

/-- The real quadratic energy of the limiting inverse-Hilbert coefficients. -/
def burnolLimitProjectionEnergy
    (rho : ι → ℂ) (multiplicity : ι → ℕ) : ℝ :=
  Complex.re (dotProduct (star (burnolLimitProjectionCoeffs rho multiplicity))
    (Matrix.mulVec (burnolFiniteHilbertMatrix multiplicity)
      (burnolLimitProjectionCoeffs rho multiplicity)))

theorem tendsto_burnolScaledProjectionEnergy
    {rho : ι → ℂ} (hcritical : ∀ a, (rho a).re = 1 / 2)
    (hinjective : Function.Injective rho) (multiplicity : ι → ℕ) :
    Tendsto (fun lambda : ℝ =>
      burnolScaledProjectionEnergy lambda rho multiplicity)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (burnolLimitProjectionEnergy rho multiplicity)) := by
  have hcoeff := tendsto_burnolScaledProjectionCoeffs
    hcritical hinjective multiplicity
  have hgram := tendsto_burnolConventionalGramMatrix
    hcritical hinjective multiplicity
  have hmul : Tendsto (fun lambda : ℝ =>
      Matrix.mulVec (burnolConventionalGramMatrix lambda rho multiplicity)
        (burnolScaledProjectionCoeffs lambda rho multiplicity))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (Matrix.mulVec (burnolFiniteHilbertMatrix multiplicity)
        (burnolLimitProjectionCoeffs rho multiplicity))) := by
    rw [tendsto_pi_nhds]
    intro i
    simp only [Matrix.mulVec, dotProduct]
    apply tendsto_finsetSum
    intro j _
    have hentry : Tendsto (fun lambda : ℝ =>
        burnolConventionalGramMatrix lambda rho multiplicity i j)
        (nhdsWithin (0 : ℝ) (Ioi 0))
        (nhds (burnolFiniteHilbertMatrix multiplicity i j)) := by
      exact ((continuous_apply j).comp (continuous_apply i)).continuousAt.tendsto.comp hgram
    have hcoeffPoint := hcoeff
    rw [tendsto_pi_nhds] at hcoeffPoint
    exact hentry.mul (hcoeffPoint j)
  simp only [burnolScaledProjectionEnergy, burnolLimitProjectionEnergy]
  apply Complex.continuous_re.continuousAt.tendsto.comp
  simp only [dotProduct]
  apply tendsto_finsetSum
  intro i _
  have hcoeffPoint := hcoeff
  have hmulPoint := hmul
  rw [tendsto_pi_nhds] at hcoeffPoint hmulPoint
  exact (hcoeffPoint i).star.mul (hmulPoint i)

theorem burnolHilbertMatrix_inv_zero_zero_of_pos
    {m : ℕ} (hm : 0 < m) :
    (burnolHilbertMatrix m)⁻¹ ⟨0, hm⟩ ⟨0, hm⟩ = ((m : ℂ) ^ 2) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  exact burnolHilbertMatrix_inv_zero_zero n

theorem norm_sq_burnolTargetFactor_of_critical
    {rho : ℂ} (hcritical : rho.re = 1 / 2) :
    ‖(rho - 1) / rho ^ 2‖ ^ 2 = 1 / ‖rho‖ ^ 2 := by
  have hrho0 : rho ≠ 0 := by
    intro hrho
    have hre := congrArg Complex.re hrho
    simp [hcritical] at hre
  have hnorm : ‖rho - 1‖ = ‖rho‖ := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
      ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    rw [Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
      sub_zero, hcritical]
    ring
  rw [norm_div, norm_pow, hnorm]
  field_simp [norm_ne_zero_iff.mpr hrho0]

theorem burnolFiniteHilbertMatrix_mulVec_limitProjectionCoeffs
    (rho : ι → ℂ) (multiplicity : ι → ℕ) :
    Matrix.mulVec (burnolFiniteHilbertMatrix multiplicity)
        (burnolLimitProjectionCoeffs rho multiplicity) =
      burnolLimitTargetVector rho multiplicity := by
  rw [burnolLimitProjectionCoeffs, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _
      (burnolFiniteHilbertMatrix_isUnit_det multiplicity), Matrix.one_mulVec]

theorem burnolLimitProjectionCoeffs_zero
    (rho : ι → ℂ) (multiplicity : ι → ℕ)
    (hpos : ∀ a, 0 < multiplicity a) (a : ι) :
    burnolLimitProjectionCoeffs rho multiplicity ⟨a, ⟨0, hpos a⟩⟩ =
      ((multiplicity a : ℂ) ^ 2) * ((rho a - 1) / (rho a) ^ 2) := by
  rw [burnolLimitProjectionCoeffs, burnolFiniteHilbertMatrix_inv]
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_sigma]
  simp only [Matrix.blockDiagonal'_apply, burnolLimitTargetVector]
  let k0 : Fin (multiplicity a) := ⟨0, hpos a⟩
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single k0]
    · simp [k0, burnolHilbertMatrix_inv_zero_zero_of_pos]
    · intro k _ hk
      have hk0 : (k : ℕ) ≠ 0 := by
        intro hval
        apply hk
        exact Fin.ext hval
      simp [hk0]
    · simp
  · intro b _ hba
    have hab : a ≠ b := fun h => hba h.symm
    simp [hab]
  · simp

theorem dotProduct_burnolLimitProjectionCoeffs_target
    (rho : ι → ℂ) (multiplicity : ι → ℕ)
    (hpos : ∀ a, 0 < multiplicity a) :
    dotProduct (star (burnolLimitProjectionCoeffs rho multiplicity))
        (burnolLimitTargetVector rho multiplicity) =
      ∑ a, ((multiplicity a : ℂ) ^ 2) *
        ((‖(rho a - 1) / (rho a) ^ 2‖ ^ 2 : ℝ) : ℂ) := by
  rw [dotProduct, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro a _
  let k0 : Fin (multiplicity a) := ⟨0, hpos a⟩
  rw [Finset.sum_eq_single k0]
  · rw [Pi.star_apply, burnolLimitProjectionCoeffs_zero rho multiplicity hpos a]
    dsimp [burnolLimitTargetVector, k0]
    have hnorm : (starRingEnd ℂ) ((rho a - 1) / (rho a) ^ 2) *
        ((rho a - 1) / (rho a) ^ 2) =
          ((‖(rho a - 1) / (rho a) ^ 2‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_pow]
      exact Complex.conj_mul' ((rho a - 1) / (rho a) ^ 2)
    rw [map_mul, map_pow, map_natCast, mul_assoc, hnorm]
  · intro k _ hk
    have hk0 : (k : ℕ) ≠ 0 := by
      intro hval
      apply hk
      exact Fin.ext hval
    simp [burnolLimitTargetVector, hk0]
  · simp

theorem burnolLimitProjectionEnergy_eq_sum_norm
    (rho : ι → ℂ) (multiplicity : ι → ℕ)
    (hpos : ∀ a, 0 < multiplicity a) :
    burnolLimitProjectionEnergy rho multiplicity =
      ∑ a, (multiplicity a : ℝ) ^ 2 *
        ‖(rho a - 1) / (rho a) ^ 2‖ ^ 2 := by
  rw [burnolLimitProjectionEnergy,
    burnolFiniteHilbertMatrix_mulVec_limitProjectionCoeffs,
    dotProduct_burnolLimitProjectionCoeffs_target rho multiplicity hpos]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro a _
  norm_cast

theorem burnolLimitProjectionEnergy_eq_sum
    (rho : ι → ℂ) (multiplicity : ι → ℕ)
    (hcritical : ∀ a, (rho a).re = 1 / 2)
    (hpos : ∀ a, 0 < multiplicity a) :
    burnolLimitProjectionEnergy rho multiplicity =
      ∑ a, (multiplicity a : ℝ) ^ 2 / ‖rho a‖ ^ 2 := by
  rw [burnolLimitProjectionEnergy_eq_sum_norm rho multiplicity hpos]
  apply Finset.sum_congr rfl
  intro a _
  rw [norm_sq_burnolTargetFactor_of_critical (hcritical a)]
  ring

/-- The finite vector represented by the scaled inverse-Gram coefficients. -/
def burnolScaledProjectionVector
    (lambda : ℝ) (rho : ι → ℂ) (multiplicity : ι → ℕ) :
    positiveHalfLineComplexL2 :=
  ∑ i, burnolScaledProjectionCoeffs lambda rho multiplicity i •
    burnolFiniteVector lambda rho multiplicity i

theorem burnolScaledProjectionEnergy_eq_norm_sq
    (lambda : ℝ) (rho : ι → ℂ) (multiplicity : ι → ℕ) :
    burnolScaledProjectionEnergy lambda rho multiplicity =
      ‖burnolScaledProjectionVector lambda rho multiplicity‖ ^ 2 := by
  let v := burnolFiniteVector lambda rho multiplicity
  let q := burnolScaledProjectionCoeffs lambda rho multiplicity
  have hgram := Matrix.star_dotProduct_gram_mulVec v q q
  calc
    burnolScaledProjectionEnergy lambda rho multiplicity =
        Complex.re (dotProduct (star q)
          (Matrix.mulVec (Matrix.gram ℂ v) q)) := by
      rfl
    _ = Complex.re (inner ℂ (∑ i, q i • v i) (∑ i, q i • v i)) :=
      congrArg Complex.re hgram
    _ = ‖∑ i, q i • v i‖ ^ 2 := by
      change RCLike.re (inner ℂ (∑ i, q i • v i) (∑ i, q i • v i)) = _
      exact inner_self_eq_norm_sq _
    _ = ‖burnolScaledProjectionVector lambda rho multiplicity‖ ^ 2 := by rfl

theorem burnolScaledProjectionCoeffs_eq_smul
    (lambda : ℝ) (rho : ι → ℂ) (multiplicity : ι → ℕ) :
    burnolScaledProjectionCoeffs lambda rho multiplicity =
      ((Real.sqrt (burnolLogScale lambda) : ℝ) : ℂ) •
        finiteGramProjectionCoeffs
          (burnolFiniteVector lambda rho multiplicity) burnolChiOneL2 := by
  ext i
  simp [burnolScaledProjectionCoeffs, burnolScaledTargetVector,
    burnolConventionalGramMatrix, finiteGramProjectionCoeffs,
    Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm]

theorem burnolScaledProjectionVector_eq_smul
    (lambda : ℝ) (rho : ι → ℂ) :
    burnolScaledProjectionVector lambda rho
        (fun a => burnolZetaZeroMultiplicity (rho a)) =
      ((Real.sqrt (burnolLogScale lambda) : ℝ) : ℂ) •
        burnolFiniteZetaProjection lambda rho := by
  rw [burnolScaledProjectionVector, burnolFiniteZetaProjection,
    finiteGramProjection]
  rw [burnolScaledProjectionCoeffs_eq_smul]
  change
    (∑ i, (((Real.sqrt (burnolLogScale lambda) : ℝ) : ℂ) *
        finiteGramProjectionCoeffs
          (burnolFiniteVector lambda rho
            (fun a => burnolZetaZeroMultiplicity (rho a))) burnolChiOneL2 i) •
      burnolFiniteVector lambda rho
        (fun a => burnolZetaZeroMultiplicity (rho a)) i) =
      ((Real.sqrt (burnolLogScale lambda) : ℝ) : ℂ) •
        ∑ i, finiteGramProjectionCoeffs
            (burnolFiniteVector lambda rho
              (fun a => burnolZetaZeroMultiplicity (rho a))) burnolChiOneL2 i •
          burnolFiniteVector lambda rho
            (fun a => burnolZetaZeroMultiplicity (rho a)) i
  rw [Finset.smul_sum]
  simp only [smul_smul]

theorem burnolScaledZetaProjectionEnergy_eq_sq
    (lambda : ℝ) (rho : ι → ℂ) :
    burnolScaledProjectionEnergy lambda rho
        (fun a => burnolZetaZeroMultiplicity (rho a)) =
      (Real.sqrt (burnolLogScale lambda) *
        ‖burnolFiniteZetaProjection lambda rho‖) ^ 2 := by
  rw [burnolScaledProjectionEnergy_eq_norm_sq,
    burnolScaledProjectionVector_eq_smul, norm_smul]
  simp [abs_of_nonneg (Real.sqrt_nonneg _)]

theorem tendsto_burnolScaledZetaProjectionEnergy
    {rho : ι → ℂ} (hcritical : ∀ a, (rho a).re = 1 / 2)
    (hinjective : Function.Injective rho)
    (hzero : ∀ a, IsNontrivialZero (rho a)) :
    Tendsto (fun lambda : ℝ =>
      burnolScaledProjectionEnergy lambda rho
        (fun a => burnolZetaZeroMultiplicity (rho a)))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∑ a, (burnolZetaZeroMultiplicity (rho a) : ℝ) ^ 2 /
        ‖rho a‖ ^ 2)) := by
  rw [← burnolLimitProjectionEnergy_eq_sum rho
    (fun a => burnolZetaZeroMultiplicity (rho a)) hcritical
    (fun a => burnolZetaZeroMultiplicity_pos (hzero a))]
  exact tendsto_burnolScaledProjectionEnergy hcritical hinjective _

/-- The real scaled norm of the explicit finite zeta projection. -/
def burnolScaledZetaProjectionNorm (lambda : ℝ) (rho : ι → ℂ) : ℝ :=
  Real.sqrt (burnolLogScale lambda) * ‖burnolFiniteZetaProjection lambda rho‖

theorem burnolScaledZetaProjectionNorm_nonneg (lambda : ℝ) (rho : ι → ℂ) :
    0 ≤ burnolScaledZetaProjectionNorm lambda rho :=
  mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)

theorem tendsto_burnolScaledZetaProjectionNorm
    {rho : ι → ℂ} (hcritical : ∀ a, (rho a).re = 1 / 2)
    (hinjective : Function.Injective rho)
    (hzero : ∀ a, IsNontrivialZero (rho a)) :
    Tendsto (fun lambda : ℝ => burnolScaledZetaProjectionNorm lambda rho)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (Real.sqrt (∑ a,
        (burnolZetaZeroMultiplicity (rho a) : ℝ) ^ 2 / ‖rho a‖ ^ 2))) := by
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp
    (tendsto_burnolScaledZetaProjectionEnergy hcritical hinjective hzero)
  change Tendsto (fun lambda : ℝ => Real.sqrt
      (burnolScaledProjectionEnergy lambda rho
        (fun a => burnolZetaZeroMultiplicity (rho a))))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (Real.sqrt (∑ a,
        (burnolZetaZeroMultiplicity (rho a) : ℝ) ^ 2 / ‖rho a‖ ^ 2))) at hsqrt
  simpa only [burnolScaledZetaProjectionEnergy_eq_sq,
    Real.sqrt_sq_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)),
    burnolScaledZetaProjectionNorm] using hsqrt

theorem eventually_burnolScaledZetaProjectionNorm_le_distance
    {rho : ι → ℂ} (hcritical : ∀ a, (rho a).re = 1 / 2)
    (hinjective : Function.Injective rho)
    (hzero : ∀ a, IsNontrivialZero (rho a)) :
    ∀ᶠ lambda : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      burnolScaledZetaProjectionNorm lambda rho ≤
        burnolDistance lambda * Real.sqrt (burnolLogScale lambda) := by
  have hlt : ∀ᶠ lambda : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), lambda < 1 :=
    (eventually_lt_nhds one_pos).filter_mono inf_le_left
  filter_upwards [eventually_mem_nhdsWithin, hlt,
    eventually_burnolConventionalGramMatrix_det_ne_zero hcritical hinjective
      (fun a => burnolZetaZeroMultiplicity (rho a))] with lambda hlambda0 hlambda1 hdet
  rw [burnolScaledZetaProjectionNorm, mul_comm (burnolDistance lambda)]
  exact mul_le_mul_of_nonneg_left
    (norm_burnolFiniteZetaProjection_le_distance hlambda0 hlambda1.le
      hcritical hzero hdet)
    (Real.sqrt_nonneg _)

theorem eventually_burnolScaledZetaProjectionNorm_le_distance_ennreal
    {rho : ι → ℂ} (hcritical : ∀ a, (rho a).re = 1 / 2)
    (hinjective : Function.Injective rho)
    (hzero : ∀ a, IsNontrivialZero (rho a)) :
    ∀ᶠ lambda : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      ENNReal.ofReal (burnolScaledZetaProjectionNorm lambda rho) ≤
        ENNReal.ofReal (burnolDistance lambda) *
          ENNReal.ofReal (Real.sqrt (burnolLogScale lambda)) := by
  filter_upwards [eventually_burnolScaledZetaProjectionNorm_le_distance
    hcritical hinjective hzero] with lambda hlambda
  rw [← ENNReal.ofReal_mul' (Real.sqrt_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hlambda

omit [DecidableEq ι] in
theorem burnolDistance_liminf_ge_finiteFamily
    {rho : ι → ℂ} (hcritical : ∀ a, (rho a).re = 1 / 2)
    (hinjective : Function.Injective rho)
    (hzero : ∀ a, IsNontrivialZero (rho a)) :
    ENNReal.ofReal (Real.sqrt (∑ a,
        (burnolZetaZeroMultiplicity (rho a) : ℝ) ^ 2 / ‖rho a‖ ^ 2)) ≤
      Filter.liminf (fun lambda : ℝ =>
        ENNReal.ofReal (burnolDistance lambda) *
          ENNReal.ofReal (Real.sqrt (burnolLogScale lambda)))
        (nhdsWithin 0 (Ioi 0)) := by
  classical
  have hlimit := ENNReal.tendsto_ofReal
    (tendsto_burnolScaledZetaProjectionNorm hcritical hinjective hzero)
  rw [← hlimit.liminf_eq]
  exact Filter.liminf_le_liminf
    (eventually_burnolScaledZetaProjectionNorm_le_distance_ennreal
      hcritical hinjective hzero)

end BurnolFiniteFamily

theorem RiemannHypothesis.burnolDistance_liminf_ge_finset
    (hRH : RiemannHypothesis)
    (R : Finset {rho : ℂ // IsNontrivialZero rho}) :
    ENNReal.ofReal (Real.sqrt (
      ∑ rho ∈ R,
        (burnolZetaZeroMultiplicity (rho : ℂ) : ℝ) ^ 2 /
          ‖(rho : ℂ)‖ ^ 2)) ≤
      Filter.liminf (fun lambda : ℝ =>
        ENNReal.ofReal (burnolDistance lambda) *
          ENNReal.ofReal (Real.sqrt (burnolLogScale lambda)))
        (nhdsWithin 0 (Ioi 0)) := by
  let rho : ↥R → ℂ := fun a => (a.1 : ℂ)
  have hcritical : ∀ a, (rho a).re = 1 / 2 := by
    intro a
    exact RiemannHypothesis.nontrivial_zero_on_line hRH a.1.property
  have hinjective : Function.Injective rho := by
    intro a b hab
    exact Subtype.ext (Subtype.ext hab)
  have hzero : ∀ a, IsNontrivialZero (rho a) := fun a => a.1.property
  rw [← R.sum_attach]
  simpa [rho] using
    (burnolDistance_liminf_ge_finiteFamily hcritical hinjective hzero)

end LeanLab.Riemann
