import LeanLab.Riemann.BombieriStepanovFrobeniusAuxiliary
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Polynomial.DegreeLT

/-!
# The Bombieri--Stepanov polar-injectivity gate

This file isolates the finite-dimensional logic between a Riemann--Roch dimension surplus and a
nonzero auxiliary function. A coefficient-block equivalence models the noncancellation supplied
by Bombieri's polar-order lemma.
-/

namespace LeanLab

namespace Riemann

open Polynomial

noncomputable section

theorem exists_ne_zero_mem_ker_of_finrank_lt
    {K U W : Type*} [Field K]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (delta : U →ₗ[K] W) (hdim : Module.finrank K W < Module.finrank K U) :
    ∃ u : U, u ≠ 0 ∧ delta u = 0 := by
  have hker : LinearMap.ker delta ≠ ⊥ :=
    delta.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨u, huKer, hu⟩ := (Submodule.ne_bot_iff _).mp hker
  exact ⟨u, hu, LinearMap.mem_ker.mp huKer⟩

theorem exists_descent_zero_realize_ne_zero_of_finrank_lt
    {K U W F : Type*} [Field K]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    [AddCommGroup F] [Module K F]
    (delta : U →ₗ[K] W) (realize : U →ₗ[K] F)
    (hrealize : Function.Injective realize)
    (hdim : Module.finrank K W < Module.finrank K U) :
    ∃ u : U, delta u = 0 ∧ realize u ≠ 0 := by
  obtain ⟨u, hu, hdelta⟩ :=
    exists_ne_zero_mem_ker_of_finrank_lt delta hdim
  refine ⟨u, hdelta, ?_⟩
  intro hzero
  apply hu
  apply hrealize
  simpa using hzero

/-- Reindex a rectangular coefficient family as one coefficient vector. -/
def stepanovFinCurryLinearEquiv (K : Type*) [Field K] (n q : ℕ) :
    (Fin n → Fin q → K) ≃ₗ[K] Fin (n * q) → K where
  toFun f k :=
    f (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  invFun f i j :=
    f (finProdFinEquiv (i, j))
  map_add' f g := by
    ext k
    rfl
  map_smul' c f := by
    ext k
    rfl
  left_inv f := by
    ext i j
    simp
  right_inv f := by
    ext k
    change f (finProdFinEquiv (finProdFinEquiv.symm k)) = f k
    rw [Equiv.apply_symm_apply]

/--
Each polynomial block has `q` coefficients, and the blocks concatenate to one polynomial of
degree less than `n*q`. This is a finite coefficient analogue of polar-order separation.
-/
def stepanovPolarBlockEquiv (K : Type*) [Field K] (n q : ℕ) :
    (Fin n → Polynomial.degreeLT K q) ≃ₗ[K] Polynomial.degreeLT K (n * q) :=
  ((LinearEquiv.piCongrRight fun _ : Fin n => Polynomial.degreeLTEquiv K q).trans
      (stepanovFinCurryLinearEquiv K n q)).trans
    (Polynomial.degreeLTEquiv K (n * q)).symm

theorem stepanovPolarBlockEquiv_coeff
    (K : Type*) [Field K] (n q : ℕ)
    (u : Fin n → Polynomial.degreeLT K q) (i : Fin n) (j : Fin q) :
    ((stepanovPolarBlockEquiv K n q u : Polynomial.degreeLT K (n * q)) :
        K[X]).coeff (finProdFinEquiv (i, j)) =
      (u i : K[X]).coeff j := by
  change
    Polynomial.degreeLTEquiv K (n * q)
        (stepanovPolarBlockEquiv K n q u) (finProdFinEquiv (i, j)) =
      Polynomial.degreeLTEquiv K q (u i) j
  have hpair :
      ((finProdFinEquiv (i, j)).divNat, (finProdFinEquiv (i, j)).modNat) =
        (i, j) :=
    finProdFinEquiv.left_inv (i, j)
  have hi : (finProdFinEquiv (i, j)).divNat = i :=
    congrArg Prod.fst hpair
  have hj : (finProdFinEquiv (i, j)).modNat = j :=
    congrArg Prod.snd hpair
  simp [stepanovPolarBlockEquiv, stepanovFinCurryLinearEquiv, hi, hj]

theorem exists_stepanovPolarBlock_ne_zero_mem_ker
    {K W : Type*} [Field K]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (n q : ℕ)
    (delta : (Fin n → Polynomial.degreeLT K q) →ₗ[K] W)
    (hdim : Module.finrank K W < n * q) :
    ∃ u : Fin n → Polynomial.degreeLT K q,
      delta u = 0 ∧ stepanovPolarBlockEquiv K n q u ≠ 0 := by
  have hsource :
      Module.finrank K W <
        Module.finrank K (Fin n → Polynomial.degreeLT K q) := by
    rw [(stepanovPolarBlockEquiv K n q).finrank_eq,
      Module.finrank_eq_card_basis (Polynomial.degreeLT.basis K (n * q)),
      Fintype.card_fin]
    exact hdim
  exact
    exists_descent_zero_realize_ne_zero_of_finrank_lt delta
      (stepanovPolarBlockEquiv K n q).toLinearMap
      (stepanovPolarBlockEquiv K n q).injective hsource

def stepanovNoninjectiveDescent : ℚ × ℚ →ₗ[ℚ] ℚ :=
  LinearMap.fst ℚ ℚ ℚ

def stepanovNoninjectiveRealize : ℚ × ℚ →ₗ[ℚ] ℚ :=
  LinearMap.fst ℚ ℚ ℚ

theorem stepanovDimensionSurplus_not_enough_without_injective :
    Module.finrank ℚ ℚ < Module.finrank ℚ (ℚ × ℚ) ∧
      (∃ u : ℚ × ℚ, u ≠ 0 ∧ stepanovNoninjectiveDescent u = 0) ∧
      (∀ u : ℚ × ℚ, stepanovNoninjectiveDescent u = 0 →
        stepanovNoninjectiveRealize u = 0) := by
  constructor
  · norm_num
  constructor
  · exact ⟨(0, 1), by norm_num, by simp [stepanovNoninjectiveDescent]⟩
  · intro u hu
    simpa [stepanovNoninjectiveDescent, stepanovNoninjectiveRealize] using hu

def stepanovPolarBlockTwoInput : Fin 2 → Polynomial.degreeLT ℚ 2
  | 0 => ⟨1, by simp [Polynomial.mem_degreeLT]⟩
  | 1 => ⟨X, by simp [Polynomial.mem_degreeLT]⟩

theorem stepanovPolarBlockTwoInput_ne_zero :
    stepanovPolarBlockTwoInput ≠ 0 := by
  intro hzero
  have hzero0 := congrFun hzero (0 : Fin 2)
  have hval := congrArg Subtype.val hzero0
  change (1 : ℚ[X]) = 0 at hval
  exact one_ne_zero hval

theorem stepanovPolarBlock_two_witness :
    stepanovPolarBlockEquiv ℚ 2 2 stepanovPolarBlockTwoInput ≠ 0 ∧
      (((stepanovPolarBlockEquiv ℚ 2 2 stepanovPolarBlockTwoInput :
          Polynomial.degreeLT ℚ 4) : ℚ[X]).coeff
        (finProdFinEquiv ((0 : Fin 2), (0 : Fin 2)))) = 1 ∧
      (((stepanovPolarBlockEquiv ℚ 2 2 stepanovPolarBlockTwoInput :
          Polynomial.degreeLT ℚ 4) : ℚ[X]).coeff
        (finProdFinEquiv ((1 : Fin 2), (1 : Fin 2)))) = 1 := by
  constructor
  · intro hzero
    apply stepanovPolarBlockTwoInput_ne_zero
    apply (stepanovPolarBlockEquiv ℚ 2 2).injective
    rw [map_zero]
    exact hzero
  constructor
  · rw [stepanovPolarBlockEquiv_coeff]
    simp [stepanovPolarBlockTwoInput]
  · rw [stepanovPolarBlockEquiv_coeff]
    simp [stepanovPolarBlockTwoInput]

end

end Riemann

end LeanLab
