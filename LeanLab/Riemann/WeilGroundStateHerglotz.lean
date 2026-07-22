import LeanLab.Riemann.WeilGroundStateFiniteMatrix

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Finite odd-sector Herglotz rank-one criterion

This module proves the finite rank-one positivity equivalence underlying the source Herglotz
reduction of the simple-even ground-state hypothesis. It does not assert the scalar inequality for
an arithmetic Weil matrix.
-/

open Matrix
open scoped BigOperators Matrix

namespace LeanLab.Riemann

noncomputable section

/-- The source odd-sector pole update `P - 2 |S><S|`. -/
def weilFiniteRankOneDeflation {N : ℕ}
    (P : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ)
    (S : Fin (2 * N + 1) → ℝ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ :=
  P - (2 : ℝ) • Matrix.vecMulVec S S

theorem weilFiniteRankOneDeflation_mulVec {N : ℕ}
    (P : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ)
    (S y : Fin (2 * N + 1) → ℝ) :
    weilFiniteRankOneDeflation P S *ᵥ y =
      P *ᵥ y - (2 * (S ⬝ᵥ y)) • S := by
  rw [weilFiniteRankOneDeflation, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec]
  ext i
  simp
  ring

/-- Completion of squares for the source odd-sector rank-one pole update. -/
theorem weilFiniteRankOneDeflectionQuadratic {N : ℕ}
    (P : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ)
    (S u y : Fin (2 * N + 1) → ℝ)
    (hPT : Pᵀ = P) (hPu : P *ᵥ u = S) :
    y ⬝ᵥ (weilFiniteRankOneDeflation P S *ᵥ y) =
      (y - (2 * (S ⬝ᵥ y)) • u) ⬝ᵥ
          (P *ᵥ (y - (2 * (S ⬝ᵥ y)) • u)) +
        2 * (S ⬝ᵥ y) ^ 2 * (1 - 2 * (S ⬝ᵥ u)) := by
  have hcross : u ⬝ᵥ (P *ᵥ y) = S ⬝ᵥ y := by
    have ht := Matrix.dotProduct_transpose_mulVec P y u
    rw [hPT, hPu] at ht
    calc
      u ⬝ᵥ (P *ᵥ y) = y ⬝ᵥ S := ht.symm
      _ = S ⬝ᵥ y := dotProduct_comm _ _
  rw [weilFiniteRankOneDeflation_mulVec, Matrix.mulVec_sub, Matrix.mulVec_smul]
  simp only [dotProduct_sub, dotProduct_smul, sub_dotProduct, smul_dotProduct]
  rw [hPu, hcross, dotProduct_comm y S, dotProduct_comm u S]
  ring

/-- On the odd sector, strict positivity after the source rank-one pole update is exactly the
scalar resolvent inequality `2 * <S,u> < 1`. -/
theorem weilFiniteOddRankOneStrict_iff_resolvent {N : ℕ}
    (P : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ)
    (S u : Fin (2 * N + 1) → ℝ)
    (hPT : Pᵀ = P)
    (hSne : S ≠ 0)
    (huodd : WeilFiniteIsOdd u) (hPu : P *ᵥ u = S)
    (hPodd : ∀ y, WeilFiniteIsOdd y → y ≠ 0 → 0 < y ⬝ᵥ (P *ᵥ y)) :
    (∀ y, WeilFiniteIsOdd y → y ≠ 0 →
        0 < y ⬝ᵥ (weilFiniteRankOneDeflation P S *ᵥ y)) ↔
      2 * (S ⬝ᵥ u) < 1 := by
  constructor
  · intro hstrict
    have hune : u ≠ 0 := by
      intro huzero
      apply hSne
      rw [← hPu, huzero]
      simp
    have hmpos : 0 < S ⬝ᵥ u := by
      have hp := hPodd u huodd hune
      rw [hPu, dotProduct_comm] at hp
      exact hp
    have hu := hstrict u huodd hune
    rw [weilFiniteRankOneDeflation_mulVec, hPu] at hu
    simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul] at hu
    have huS : u ⬝ᵥ S = S ⬝ᵥ u := dotProduct_comm _ _
    rw [huS] at hu
    nlinarith
  · intro hscalar y hyodd hyne
    let a := S ⬝ᵥ y
    let z := y - (2 * a) • u
    have hzodd : WeilFiniteIsOdd z := by
      exact hyodd.sub (huodd.smul (2 * a))
    have hid := weilFiniteRankOneDeflectionQuadratic P S u y hPT hPu
    change y ⬝ᵥ (weilFiniteRankOneDeflation P S *ᵥ y) =
      z ⬝ᵥ (P *ᵥ z) + 2 * a ^ 2 * (1 - 2 * (S ⬝ᵥ u)) at hid
    have hfactor : 0 < 1 - 2 * (S ⬝ᵥ u) := by linarith
    by_cases hz : z = 0
    · have hane : a ≠ 0 := by
        intro hazero
        apply hyne
        dsimp [z] at hz
        simpa [hazero] using hz
      have hsecond : 0 < 2 * a ^ 2 * (1 - 2 * (S ⬝ᵥ u)) := by
        positivity
      rw [hid, hz]
      simpa using hsecond
    · have hp := hPodd z hzodd hz
      have hsecond : 0 ≤ 2 * a ^ 2 * (1 - 2 * (S ⬝ᵥ u)) := by
        positivity
      rw [hid]
      exact add_pos_of_pos_of_nonneg hp hsecond

/-- Finite source-aligned Herglotz certificate. The arithmetic scalar inequality is an explicit
field, not a theorem or hidden premise. -/
structure WeilFiniteOddHerglotzCertificate {N : ℕ}
    (A P : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ)
    (mu : ℝ) (xi S u : Fin (2 * N + 1) → ℝ) : Prop where
  even_xi : WeilFiniteIsEven xi
  normalized_xi : xi ⬝ᵥ xi = 1
  eigen_xi : A *ᵥ xi = mu • xi
  strict_even : ∀ y, WeilFiniteIsEven y → xi ⬝ᵥ y = 0 → y ≠ 0 →
    mu * (y ⬝ᵥ y) < y ⬝ᵥ (A *ᵥ y)
  symmetric_P : Pᵀ = P
  odd_S : WeilFiniteIsOdd S
  S_ne_zero : S ≠ 0
  odd_u : WeilFiniteIsOdd u
  resolvent_u : P *ᵥ u = S
  strict_poleFree_odd : ∀ y, WeilFiniteIsOdd y → y ≠ 0 →
    0 < y ⬝ᵥ (P *ᵥ y)
  odd_defect_eq : ∀ y, WeilFiniteIsOdd y →
    weilFiniteRayleighDefect A mu y =
      y ⬝ᵥ (weilFiniteRankOneDeflation P S *ᵥ y)
  scalar_lt_half : 2 * (S ⬝ᵥ u) < 1

theorem WeilFiniteOddHerglotzCertificate.strict_odd {N : ℕ}
    {A P : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ}
    {mu : ℝ} {xi S u : Fin (2 * N + 1) → ℝ}
    (h : WeilFiniteOddHerglotzCertificate A P mu xi S u) :
    ∀ y, WeilFiniteIsOdd y → y ≠ 0 →
      mu * (y ⬝ᵥ y) < y ⬝ᵥ (A *ᵥ y) := by
  have hstrict := (weilFiniteOddRankOneStrict_iff_resolvent
    P S u h.symmetric_P h.S_ne_zero h.odd_u h.resolvent_u
    h.strict_poleFree_odd).mpr h.scalar_lt_half
  intro y hyodd hyne
  have hpositive := hstrict y hyodd hyne
  rw [← h.odd_defect_eq y hyodd] at hpositive
  unfold weilFiniteRayleighDefect at hpositive
  linarith

theorem WeilFiniteOddHerglotzCertificate.parityRayleighCertificate {N : ℕ}
    {A P : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ}
    {mu : ℝ} {xi S u : Fin (2 * N + 1) → ℝ}
    (h : WeilFiniteOddHerglotzCertificate A P mu xi S u) :
    WeilFiniteParityRayleighCertificate A mu xi where
  even_xi := h.even_xi
  normalized_xi := h.normalized_xi
  eigen_xi := h.eigen_xi
  strict_even := h.strict_even
  strict_odd := h.strict_odd

theorem WeilFiniteOddHerglotzCertificate.evenSimpleGroundState {N : ℕ}
    {A P : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ}
    {mu : ℝ} {xi S u : Fin (2 * N + 1) → ℝ}
    (h : WeilFiniteOddHerglotzCertificate A P mu xi S u)
    (hAT : Aᵀ = A) (hAR : ∀ i j, A i.rev j.rev = A i j) :
    WeilFiniteEvenSimpleGroundState A mu xi :=
  h.parityRayleighCertificate.evenSimpleGroundState hAT hAR

end

end LeanLab.Riemann
