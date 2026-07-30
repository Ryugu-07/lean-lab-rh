/-
Copyright (c) 2026 LeanLab contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanLab contributors
-/
import LeanLab.Riemann.BombieriStepanovPolarInjectivity
import Mathlib.FieldTheory.RatFunc.Valuation

/-!
# Bombieri--Stepanov polar separation in the rational function field

This file realizes the polar blocks from the Bombieri--Stepanov construction in `K(t)`. On the
rational curve, the source basis indexed by `(i, j)` maps to `X ^ (i * pPower + j * q)`.
The strict source inequality `l * pPower < q` separates these exponents.
-/

namespace LeanLab

namespace Riemann

open Polynomial

noncomputable section

abbrev StepanovPolarSource (K : Type*) [Zero K] (l m : ℕ) :=
  (Fin (l + 1) × Fin (m + 1)) →₀ K

def stepanovPolarExponent (l m pPower q : ℕ) :
    Fin (l + 1) × Fin (m + 1) → ℕ :=
  fun ij => ij.1.val * pPower + ij.2.val * q

theorem stepanovPolarExponent_injective
    (l m pPower q : ℕ) (hpPower : 0 < pPower)
    (hseparate : l * pPower < q) :
    Function.Injective (stepanovPolarExponent l m pPower q) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ hij
  change i.val * pPower + j.val * q =
    i'.val * pPower + j'.val * q at hij
  have hiBound : i.val * pPower < q := by
    exact lt_of_le_of_lt
      (Nat.mul_le_mul_right pPower (Nat.le_of_lt_succ i.isLt)) hseparate
  have hiBound' : i'.val * pPower < q := by
    exact lt_of_le_of_lt
      (Nat.mul_le_mul_right pPower (Nat.le_of_lt_succ i'.isLt)) hseparate
  have hq : 0 < q := lt_of_le_of_lt (Nat.zero_le (l * pPower)) hseparate
  have hjVal : j.val = j'.val := by
    have hdiv := congrArg (fun n : ℕ => n / q) hij
    have hleft :
        (i.val * pPower + j.val * q) / q = j.val := by
      rw [Nat.mul_comm j.val q, Nat.add_mul_div_left _ _ hq,
        Nat.div_eq_of_lt hiBound, Nat.zero_add]
    have hright :
        (i'.val * pPower + j'.val * q) / q = j'.val := by
      rw [Nat.mul_comm j'.val q, Nat.add_mul_div_left _ _ hq,
        Nat.div_eq_of_lt hiBound', Nat.zero_add]
    exact hleft.symm.trans (hdiv.trans hright)
  have hiMul : i.val * pPower = i'.val * pPower := by
    have hsums : i.val * pPower + j.val * q =
        i'.val * pPower + j.val * q := by
      simpa [hjVal] using hij
    exact Nat.add_right_cancel hsums
  have hiVal : i.val = i'.val :=
    Nat.eq_of_mul_eq_mul_right hpPower hiMul
  exact Prod.ext (Fin.ext hiVal) (Fin.ext hjVal)

def stepanovPolarExponentEmbedding
    (l m pPower q : ℕ) (hpPower : 0 < pPower)
    (hseparate : l * pPower < q) :
    Fin (l + 1) × Fin (m + 1) ↪ ℕ :=
  ⟨stepanovPolarExponent l m pPower q,
    stepanovPolarExponent_injective l m pPower q hpPower hseparate⟩

/-- The raw polar realization in the polynomial ring. Colliding exponents are added. -/
def stepanovPolarPolynomialRealize
    (K : Type*) [Field K] (l m pPower q : ℕ) :
    StepanovPolarSource K l m →ₗ[K] K[X] :=
  (Polynomial.toFinsuppIsoLinear K).symm.toLinearMap.comp
    (Finsupp.lmapDomain K K (stepanovPolarExponent l m pPower q))

/-- The same realization in the actual rational function field `K(t)`. -/
def stepanovRationalPolarRealize
    (K : Type*) [Field K] (l m pPower q : ℕ) :
    StepanovPolarSource K l m →ₗ[K] RatFunc K :=
  (IsScalarTower.toAlgHom K K[X] (RatFunc K)).toLinearMap.comp
    (stepanovPolarPolynomialRealize K l m pPower q)

theorem stepanovPolarPolynomialRealize_coeff
    (K : Type*) [Field K] (l m pPower q : ℕ)
    (hpPower : 0 < pPower) (hseparate : l * pPower < q)
    (u : StepanovPolarSource K l m)
    (ij : Fin (l + 1) × Fin (m + 1)) :
    (stepanovPolarPolynomialRealize K l m pPower q u).coeff
        (stepanovPolarExponent l m pPower q ij) = u ij := by
  let e :=
    stepanovPolarExponentEmbedding l m pPower q hpPower hseparate
  change
    Finsupp.mapDomain (e : Fin (l + 1) × Fin (m + 1) → ℕ) u (e ij) = u ij
  rw [← Finsupp.embDomain_eq_mapDomain e]
  exact Finsupp.embDomain_apply_self e u ij

theorem stepanovPolarPolynomialRealize_injective
    (K : Type*) [Field K] (l m pPower q : ℕ)
    (hpPower : 0 < pPower) (hseparate : l * pPower < q) :
    Function.Injective (stepanovPolarPolynomialRealize K l m pPower q) := by
  intro u v huv
  apply Finsupp.ext
  intro ij
  rw [← stepanovPolarPolynomialRealize_coeff K l m pPower q hpPower hseparate u ij,
    ← stepanovPolarPolynomialRealize_coeff K l m pPower q hpPower hseparate v ij, huv]

theorem stepanovRationalPolarRealize_injective
    (K : Type*) [Field K] (l m pPower q : ℕ)
    (hpPower : 0 < pPower) (hseparate : l * pPower < q) :
    Function.Injective (stepanovRationalPolarRealize K l m pPower q) := by
  intro u v huv
  apply stepanovPolarPolynomialRealize_injective K l m pPower q hpPower hseparate
  apply RatFunc.algebraMap_injective K
  simpa [stepanovRationalPolarRealize] using huv

theorem exists_stepanovRationalPolar_ne_zero_mem_ker
    {K W : Type*} [Field K]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (l m pPower q : ℕ) (hpPower : 0 < pPower)
    (hseparate : l * pPower < q)
    (delta : StepanovPolarSource K l m →ₗ[K] W)
    (hdim : Module.finrank K W <
      Module.finrank K (StepanovPolarSource K l m)) :
    ∃ u : StepanovPolarSource K l m,
      delta u = 0 ∧ stepanovRationalPolarRealize K l m pPower q u ≠ 0 :=
  exists_descent_zero_realize_ne_zero_of_finrank_lt delta
    (stepanovRationalPolarRealize K l m pPower q)
    (stepanovRationalPolarRealize_injective K l m pPower q hpPower hseparate) hdim

theorem stepanovPolarPolynomialRealize_single
    (K : Type*) [Field K] (l m pPower q : ℕ)
    (ij : Fin (l + 1) × Fin (m + 1)) :
    stepanovPolarPolynomialRealize K l m pPower q (Finsupp.single ij 1) =
      X ^ stepanovPolarExponent l m pPower q ij := by
  apply Polynomial.toFinsupp_injective
  change
    Finsupp.mapDomain (stepanovPolarExponent l m pPower q) (Finsupp.single ij 1) =
      (X ^ stepanovPolarExponent l m pPower q ij : K[X]).toFinsupp
  simp

theorem stepanovRationalPolarRealize_single
    (K : Type*) [Field K] (l m pPower q : ℕ)
    (ij : Fin (l + 1) × Fin (m + 1)) :
    stepanovRationalPolarRealize K l m pPower q (Finsupp.single ij 1) =
      RatFunc.X ^ stepanovPolarExponent l m pPower q ij := by
  rw [stepanovRationalPolarRealize, LinearMap.comp_apply,
    stepanovPolarPolynomialRealize_single]
  simp [RatFunc.algebraMap_X]

theorem stepanovRationalPolarRealize_single_inftyValuation
    (K : Type*) [Field K] [DecidableEq (RatFunc K)]
    (l m pPower q : ℕ) (ij : Fin (l + 1) × Fin (m + 1)) :
    RatFunc.inftyValuation K
        (stepanovRationalPolarRealize K l m pPower q (Finsupp.single ij 1)) =
      WithZero.exp
        (stepanovPolarExponent l m pPower q ij : ℤ) := by
  rw [stepanovRationalPolarRealize_single]
  change RatFunc.inftyValuation K
      (RatFunc.X ^ (stepanovPolarExponent l m pPower q ij : ℤ)) =
    WithZero.exp (stepanovPolarExponent l m pPower q ij : ℤ)
  exact RatFunc.inftyValuation.X_zpow K
    (stepanovPolarExponent l m pPower q ij : ℤ)

def stepanovPolarEqualityCollision :
    StepanovPolarSource ℚ 1 1 :=
  Finsupp.single ((1 : Fin 2), (0 : Fin 2)) 1 -
    Finsupp.single ((0 : Fin 2), (1 : Fin 2)) 1

theorem stepanovPolarEqualityCollision_ne_zero :
    stepanovPolarEqualityCollision ≠ 0 := by
  intro hzero
  have hvalue := congrArg
    (fun u : StepanovPolarSource ℚ 1 1 => u ((1 : Fin 2), (0 : Fin 2))) hzero
  norm_num [stepanovPolarEqualityCollision] at hvalue

theorem stepanovPolarEqualityCollision_realize_eq_zero :
    stepanovRationalPolarRealize ℚ 1 1 1 1
      stepanovPolarEqualityCollision = 0 := by
  change
    stepanovRationalPolarRealize ℚ 1 1 1 1
      (Finsupp.single ((1 : Fin 2), (0 : Fin 2)) 1 -
        Finsupp.single ((0 : Fin 2), (1 : Fin 2)) 1) = 0
  rw [map_sub, stepanovRationalPolarRealize_single,
    stepanovRationalPolarRealize_single]
  norm_num [stepanovPolarExponent]

theorem stepanovPolar_strict_separation_is_sharp :
    stepanovPolarEqualityCollision ≠ 0 ∧
      stepanovRationalPolarRealize ℚ 1 1 1 1
        stepanovPolarEqualityCollision = 0 :=
  ⟨stepanovPolarEqualityCollision_ne_zero,
    stepanovPolarEqualityCollision_realize_eq_zero⟩

end

end Riemann

end LeanLab
