import LeanLab.Riemann.DeBruijnNewmanDynamics
import LeanLab.Riemann.DeBruijnNewmanHermiteSplitting
import LeanLab.Riemann.DeBruijnNewmanGeneralStrip

set_option linter.style.header false

/-!
# Polymath zero-free-region criterion

This file formalizes the three closed zero-free regions used in Polymath Proposition 3.3 and
develops the boundary and zero-dynamics infrastructure needed by its first-contact proof.
-/

open Complex Filter MeasureTheory Real Set Topology
open scoped BigOperators ComplexConjugate

namespace LeanLab.Riemann

noncomputable section

/-- The time-zero compact region in Polymath Proposition 3.3. -/
def deBruijnNewmanPolymathInitialRegionZeroFree (t0 X y0 : ℝ) : Prop :=
  ∀ x y : ℝ,
    0 ≤ x → x ≤ X →
    Real.sqrt (y0 ^ 2 + 2 * t0) ≤ y → y ≤ 1 →
    deBruijnNewmanH 0 ((x : ℂ) + (y : ℂ) * I) ≠ 0

/-- The terminal asymptotic region in Polymath Proposition 3.3. -/
def deBruijnNewmanPolymathFinalRegionZeroFree (t0 X y0 : ℝ) : Prop :=
  ∀ x y : ℝ,
    X + Real.sqrt (1 - y0 ^ 2) ≤ x →
    y0 ≤ y → y ≤ Real.sqrt (1 - 2 * t0) →
    deBruijnNewmanH t0 ((x : ℂ) + (y : ℂ) * I) ≠ 0

/-- The spacetime barrier region in Polymath Proposition 3.3. -/
def deBruijnNewmanPolymathBarrierRegionZeroFree (t0 X y0 : ℝ) : Prop :=
  ∀ t x y : ℝ,
    0 ≤ t → t ≤ t0 →
    X ≤ x → x ≤ X + Real.sqrt (1 - y0 ^ 2) →
    Real.sqrt (y0 ^ 2 + 2 * (t0 - t)) ≤ y →
    y ≤ Real.sqrt (1 - 2 * t) →
    deBruijnNewmanH t ((x : ℂ) + (y : ℂ) * I) ≠ 0

/-- The moving lower boundary in the Polymath first-contact argument. -/
def deBruijnNewmanPolymathBoundaryHeight (t0 y0 t : ℝ) : ℝ :=
  Real.sqrt (y0 ^ 2 + 2 * (t0 - t))

/-- The multiplicity-bearing nonzero divisor of the source-normalized heat family. -/
abbrev DeBruijnNewmanHDivisorZeroIndex (t : ℝ) :=
  Complex.Hadamard.divisorZeroIndex₀ (deBruijnNewmanH t) (Set.univ : Set ℂ)

/-- The zero represented by a source-family divisor index. -/
abbrev deBruijnNewmanHDivisorZeroValue
    {t : ℝ} (p : DeBruijnNewmanHDivisorZeroIndex t) : ℂ :=
  Complex.Hadamard.divisorZeroIndex₀_val p

/-- Conjugation as an equivalence of the source-family divisor, preserving multiplicity. -/
def deBruijnNewmanHDivisorZeroConjEquiv (t : ℝ) :
    DeBruijnNewmanHDivisorZeroIndex t ≃ DeBruijnNewmanHDivisorZeroIndex t :=
  divisorZeroIndexConjEquiv
    (deBruijnNewmanH_entireOfOrderAtMost_one t).differentiable
    ⟨0, deBruijnNewmanH_zero_ne_zero t⟩
    (deBruijnNewmanH_conj t)

@[simp]
theorem deBruijnNewmanHDivisorZeroConjEquiv_value
    {t : ℝ} (p : DeBruijnNewmanHDivisorZeroIndex t) :
    deBruijnNewmanHDivisorZeroValue (deBruijnNewmanHDivisorZeroConjEquiv t p) =
      conj (deBruijnNewmanHDivisorZeroValue p) := by
  rfl

/-- Negation as an equivalence of the source-family divisor, preserving multiplicity. -/
def deBruijnNewmanHDivisorZeroNegEquiv (t : ℝ) :
    DeBruijnNewmanHDivisorZeroIndex t ≃ DeBruijnNewmanHDivisorZeroIndex t :=
  divisorZeroIndexNegEquiv
    (deBruijnNewmanH_entireOfOrderAtMost_one t).differentiable
    ⟨0, deBruijnNewmanH_zero_ne_zero t⟩
    (deBruijnNewmanH_neg t)

@[simp]
theorem deBruijnNewmanHDivisorZeroNegEquiv_value
    {t : ℝ} (p : DeBruijnNewmanHDivisorZeroIndex t) :
    deBruijnNewmanHDivisorZeroValue (deBruijnNewmanHDivisorZeroNegEquiv t p) =
      -deBruijnNewmanHDivisorZeroValue p := by
  rfl

theorem deBruijnNewmanHDivisorZeroNegEquiv_conjEquiv
    {t : ℝ} (p : DeBruijnNewmanHDivisorZeroIndex t) :
    deBruijnNewmanHDivisorZeroNegEquiv t
        (deBruijnNewmanHDivisorZeroConjEquiv t p) =
      deBruijnNewmanHDivisorZeroConjEquiv t
        (deBruijnNewmanHDivisorZeroNegEquiv t p) := by
  apply Subtype.ext
  apply Sigma.ext
  · simp
  · rw [Fin.heq_ext_iff]
    · simp [deBruijnNewmanHDivisorZeroNegEquiv,
        deBruijnNewmanHDivisorZeroConjEquiv, divisorZeroIndexNegEquiv,
        divisorZeroIndexConjEquiv, divisorZeroIndexNeg, divisorZeroIndexConj]
    · simp

/-- Every divisor zero can be moved by the source symmetries to the closed first quadrant. -/
theorem exists_deBruijnNewmanHDivisorZeroIndex_value_eq_abs_cartesian
    {t : ℝ} (p : DeBruijnNewmanHDivisorZeroIndex t) :
    ∃ q : DeBruijnNewmanHDivisorZeroIndex t,
      deBruijnNewmanHDivisorZeroValue q =
        ((|(deBruijnNewmanHDivisorZeroValue p).re| : ℝ) : ℂ) +
          ((|(deBruijnNewmanHDivisorZeroValue p).im| : ℝ) : ℂ) * I := by
  by_cases hre : 0 ≤ (deBruijnNewmanHDivisorZeroValue p).re
  · by_cases him : 0 ≤ (deBruijnNewmanHDivisorZeroValue p).im
    · refine ⟨p, ?_⟩
      apply Complex.ext <;> simp [abs_of_nonneg hre, abs_of_nonneg him]
    · refine ⟨deBruijnNewmanHDivisorZeroConjEquiv t p, ?_⟩
      apply Complex.ext <;>
        simp [abs_of_nonneg hre, abs_of_neg (lt_of_not_ge him)]
  · by_cases him : 0 ≤ (deBruijnNewmanHDivisorZeroValue p).im
    · refine ⟨deBruijnNewmanHDivisorZeroNegEquiv t
          (deBruijnNewmanHDivisorZeroConjEquiv t p), ?_⟩
      apply Complex.ext <;>
        simp [abs_of_neg (lt_of_not_ge hre), abs_of_nonneg him]
    · refine ⟨deBruijnNewmanHDivisorZeroNegEquiv t p, ?_⟩
      apply Complex.ext <;>
        simp [abs_of_neg (lt_of_not_ge hre), abs_of_neg (lt_of_not_ge him)]

@[simp]
theorem deBruijnNewmanHDivisorZeroNegEquiv_apply_apply
    {t : ℝ} (p : DeBruijnNewmanHDivisorZeroIndex t) :
    deBruijnNewmanHDivisorZeroNegEquiv t
        (deBruijnNewmanHDivisorZeroNegEquiv t p) = p := by
  change divisorZeroIndexNeg
      (deBruijnNewmanH_entireOfOrderAtMost_one t).differentiable
      ⟨0, deBruijnNewmanH_zero_ne_zero t⟩ (deBruijnNewmanH_neg t)
      (divisorZeroIndexNeg
        (deBruijnNewmanH_entireOfOrderAtMost_one t).differentiable
        ⟨0, deBruijnNewmanH_zero_ne_zero t⟩ (deBruijnNewmanH_neg t) p) = p
  exact divisorZeroIndexNeg_involutive
    (deBruijnNewmanH_entireOfOrderAtMost_one t).differentiable
    ⟨0, deBruijnNewmanH_zero_ne_zero t⟩ (deBruijnNewmanH_neg t) p

@[simp]
theorem deBruijnNewmanHDivisorZeroConjEquiv_apply_apply
    {t : ℝ} (p : DeBruijnNewmanHDivisorZeroIndex t) :
    deBruijnNewmanHDivisorZeroConjEquiv t
        (deBruijnNewmanHDivisorZeroConjEquiv t p) = p := by
  change divisorZeroIndexConj
      (deBruijnNewmanH_entireOfOrderAtMost_one t).differentiable
      ⟨0, deBruijnNewmanH_zero_ne_zero t⟩ (deBruijnNewmanH_conj t)
      (divisorZeroIndexConj
        (deBruijnNewmanH_entireOfOrderAtMost_one t).differentiable
        ⟨0, deBruijnNewmanH_zero_ne_zero t⟩ (deBruijnNewmanH_conj t) p) = p
  exact divisorZeroIndexConj_involutive
    (deBruijnNewmanH_entireOfOrderAtMost_one t).differentiable
    ⟨0, deBruijnNewmanH_zero_ne_zero t⟩ (deBruijnNewmanH_conj t) p

/-- The four divisor indices in the negation-conjugation orbit of a selected index. -/
def deBruijnNewmanHDivisorZeroSymmetryOrbit
    {t : ℝ} (p : DeBruijnNewmanHDivisorZeroIndex t) :
    Finset (DeBruijnNewmanHDivisorZeroIndex t) := by
  classical
  exact {p, deBruijnNewmanHDivisorZeroNegEquiv t p,
    deBruijnNewmanHDivisorZeroConjEquiv t p,
    deBruijnNewmanHDivisorZeroNegEquiv t
      (deBruijnNewmanHDivisorZeroConjEquiv t p)}

theorem deBruijnNewmanHDivisorZeroSymmetryOrbit_card_eq_four_of_contact
    {t x Y : ℝ} (p : DeBruijnNewmanHDivisorZeroIndex t)
    (hx : 0 < x) (hY : 0 < Y)
    (hp : deBruijnNewmanHDivisorZeroValue p = (x : ℂ) + (Y : ℂ) * I) :
    (deBruijnNewmanHDivisorZeroSymmetryOrbit p).card = 4 := by
  classical
  let n := deBruijnNewmanHDivisorZeroNegEquiv t
  let c := deBruijnNewmanHDivisorZeroConjEquiv t
  have hpn : p ≠ n p := by
    intro h
    have hv := congrArg (fun q ↦ (deBruijnNewmanHDivisorZeroValue q).im) h
    simp only [n, deBruijnNewmanHDivisorZeroNegEquiv_value, hp, add_im, ofReal_im,
      mul_im, ofReal_re, I_re, I_im, mul_zero, mul_one, zero_add, neg_im] at hv
    linarith
  have hpc : p ≠ c p := by
    intro h
    have hv := congrArg (fun q ↦ (deBruijnNewmanHDivisorZeroValue q).im) h
    simp only [c, deBruijnNewmanHDivisorZeroConjEquiv_value, hp, add_im, ofReal_im,
      mul_im, ofReal_re, I_re, I_im, mul_zero, mul_one, zero_add, conj_im] at hv
    linarith
  have hpnc : p ≠ n (c p) := by
    intro h
    have hv := congrArg (fun q ↦ (deBruijnNewmanHDivisorZeroValue q).re) h
    simp only [n, c, deBruijnNewmanHDivisorZeroNegEquiv_value,
      deBruijnNewmanHDivisorZeroConjEquiv_value, hp, neg_re, conj_re, add_re,
      ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero] at hv
    linarith
  have hnc : n p ≠ c p := by
    intro h
    have hv := congrArg (fun q ↦ (deBruijnNewmanHDivisorZeroValue q).re) h
    simp only [n, c, deBruijnNewmanHDivisorZeroNegEquiv_value,
      deBruijnNewmanHDivisorZeroConjEquiv_value, hp, neg_re, conj_re, add_re,
      ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero] at hv
    linarith
  have hnnc : n p ≠ n (c p) := by
    intro h
    exact hpc ((deBruijnNewmanHDivisorZeroNegEquiv t).injective h)
  have hcnc : c p ≠ n (c p) := by
    intro h
    have hv := congrArg (fun q ↦ (deBruijnNewmanHDivisorZeroValue q).re) h
    simp only [n, c, deBruijnNewmanHDivisorZeroNegEquiv_value,
      deBruijnNewmanHDivisorZeroConjEquiv_value, hp, neg_re, conj_re, add_re,
      ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero] at hv
    linarith
  apply Finset.card_eq_four.mpr
  exact ⟨p, n p, c p, n (c p), hpn, hpc, hpnc, hnc, hnnc, hcnc, by
    rfl⟩

/-- Sum of a term over the four-index orbit generated by two equivalences. -/
def fourEquivOrbitTerm {Z : Type*} (f : Z → ℂ) (e₁ e₂ : Z ≃ Z) (p : Z) : ℂ :=
  (f p + f (e₁ p)) + f (e₂ p) + f (e₁ (e₂ p))

theorem summable_fourEquivOrbitTerm
    {Z : Type*} (f : Z → ℂ) (hf : Summable f) (e₁ e₂ : Z ≃ Z) :
    Summable (fourEquivOrbitTerm f e₁ e₂) := by
  have h₁ : Summable (fun p : Z ↦ f (e₁ p)) := e₁.summable_iff.mpr hf
  have h₂ : Summable (fun p : Z ↦ f (e₂ p)) := e₂.summable_iff.mpr hf
  have h₁₂ : Summable (fun p : Z ↦ f (e₁ (e₂ p))) :=
    (e₂.trans e₁).summable_iff.mpr hf
  change Summable (fun p : Z ↦ (f p + f (e₁ p)) + f (e₂ p) + f (e₁ (e₂ p)))
  exact ((hf.add h₁).add h₂).add h₁₂

/-- An absolutely convergent sum equals one quarter of the sum of its translates by two
index equivalences. This is the reindexing gate for the fourfold zero orbit. -/
theorem tsum_eq_quarter_tsum_equiv_orbit
    {Z : Type*} (f : Z → ℂ) (hf : Summable f) (e₁ e₂ : Z ≃ Z) :
    ∑' p : Z, f p =
      (1 / 4 : ℂ) * ∑' p : Z, fourEquivOrbitTerm f e₁ e₂ p := by
  have h₁ : Summable (fun p : Z ↦ f (e₁ p)) := e₁.summable_iff.mpr hf
  have h₂ : Summable (fun p : Z ↦ f (e₂ p)) := e₂.summable_iff.mpr hf
  have h₁₂ : Summable (fun p : Z ↦ f (e₁ (e₂ p))) :=
    (e₂.trans e₁).summable_iff.mpr hf
  have h₁₂Tsum : (∑' p : Z, f (e₁ (e₂ p))) = ∑' p : Z, f p := by
    simpa only [Equiv.trans_apply] using (e₂.trans e₁).tsum_eq f
  have horbitTsum :
      (∑' p : Z, fourEquivOrbitTerm f e₁ e₂ p) =
        ((∑' p : Z, f p) + ∑' p : Z, f (e₁ p)) +
          (∑' p : Z, f (e₂ p)) + ∑' p : Z, f (e₁ (e₂ p)) := by
    simp only [fourEquivOrbitTerm]
    rw [((hf.add h₁).add h₂).tsum_add h₁₂, (hf.add h₁).tsum_add h₂,
      hf.tsum_add h₁]
  rw [horbitTsum]
  rw [e₁.tsum_eq f, e₂.tsum_eq f, h₁₂Tsum]
  ring

/-- The regularized force summand at a selected source-family zero. -/
def deBruijnNewmanPolymathForceTerm (t : ℝ) (r : ℂ)
    (p : DeBruijnNewmanHDivisorZeroIndex t) : ℂ :=
  if deBruijnNewmanHDivisorZeroValue p = r then 0
  else 1 / (r - deBruijnNewmanHDivisorZeroValue p) +
    1 / deBruijnNewmanHDivisorZeroValue p

theorem summable_deBruijnNewmanPolymathForceTerm (t : ℝ) (r : ℂ) :
    Summable (deBruijnNewmanPolymathForceTerm t r) := by
  exact summable_deBruijnNewman_regularizedZeroForceTerm t r

/-- The sum of a force term over its negation-conjugation divisor orbit. -/
def deBruijnNewmanPolymathForceOrbitTerm (t : ℝ) (r : ℂ)
    (p : DeBruijnNewmanHDivisorZeroIndex t) : ℂ :=
  fourEquivOrbitTerm (deBruijnNewmanPolymathForceTerm t r)
    (deBruijnNewmanHDivisorZeroNegEquiv t)
    (deBruijnNewmanHDivisorZeroConjEquiv t) p

theorem deBruijnNewmanPolymathForceOrbitTerm_negEquiv
    {t : ℝ} {r : ℂ} (p : DeBruijnNewmanHDivisorZeroIndex t) :
    deBruijnNewmanPolymathForceOrbitTerm t r
        (deBruijnNewmanHDivisorZeroNegEquiv t p) =
      deBruijnNewmanPolymathForceOrbitTerm t r p := by
  let n := deBruijnNewmanHDivisorZeroNegEquiv t
  let c := deBruijnNewmanHDivisorZeroConjEquiv t
  let f := deBruijnNewmanPolymathForceTerm t r
  have hn : ∀ q, n (n q) = q := by
    intro q
    change divisorZeroIndexNeg
        (deBruijnNewmanH_entireOfOrderAtMost_one t).differentiable
        ⟨0, deBruijnNewmanH_zero_ne_zero t⟩ (deBruijnNewmanH_neg t)
        (divisorZeroIndexNeg
          (deBruijnNewmanH_entireOfOrderAtMost_one t).differentiable
          ⟨0, deBruijnNewmanH_zero_ne_zero t⟩ (deBruijnNewmanH_neg t) q) = q
    exact divisorZeroIndexNeg_involutive
      (deBruijnNewmanH_entireOfOrderAtMost_one t).differentiable
      ⟨0, deBruijnNewmanH_zero_ne_zero t⟩ (deBruijnNewmanH_neg t) q
  have hcomm : ∀ q, n (c q) = c (n q) := by
    intro q
    exact deBruijnNewmanHDivisorZeroNegEquiv_conjEquiv q
  change fourEquivOrbitTerm f n c (n p) = fourEquivOrbitTerm f n c p
  simp only [fourEquivOrbitTerm]
  rw [hn p, ← hcomm p, hn (c p)]
  ring

theorem deBruijnNewmanPolymathForceOrbitTerm_conjEquiv
    {t : ℝ} {r : ℂ} (p : DeBruijnNewmanHDivisorZeroIndex t) :
    deBruijnNewmanPolymathForceOrbitTerm t r
        (deBruijnNewmanHDivisorZeroConjEquiv t p) =
      deBruijnNewmanPolymathForceOrbitTerm t r p := by
  let n := deBruijnNewmanHDivisorZeroNegEquiv t
  let c := deBruijnNewmanHDivisorZeroConjEquiv t
  let f := deBruijnNewmanPolymathForceTerm t r
  have hc : ∀ q, c (c q) = q := by
    intro q
    change divisorZeroIndexConj
        (deBruijnNewmanH_entireOfOrderAtMost_one t).differentiable
        ⟨0, deBruijnNewmanH_zero_ne_zero t⟩ (deBruijnNewmanH_conj t)
        (divisorZeroIndexConj
          (deBruijnNewmanH_entireOfOrderAtMost_one t).differentiable
          ⟨0, deBruijnNewmanH_zero_ne_zero t⟩ (deBruijnNewmanH_conj t) q) = q
    exact divisorZeroIndexConj_involutive
      (deBruijnNewmanH_entireOfOrderAtMost_one t).differentiable
      ⟨0, deBruijnNewmanH_zero_ne_zero t⟩ (deBruijnNewmanH_conj t) q
  change fourEquivOrbitTerm f n c (c p) = fourEquivOrbitTerm f n c p
  simp only [fourEquivOrbitTerm]
  rw [hc p]
  ring

theorem summable_deBruijnNewmanPolymathForceOrbitTerm (t : ℝ) (r : ℂ) :
    Summable (deBruijnNewmanPolymathForceOrbitTerm t r) := by
  exact summable_fourEquivOrbitTerm _
    (summable_deBruijnNewmanPolymathForceTerm t r) _ _

/-- The regularized force rewritten as an absolutely convergent fourfold divisor-orbit sum. -/
theorem deBruijnNewmanRegularizedZeroForce_eq_quarter_orbit_tsum (t : ℝ) (r : ℂ) :
    deBruijnNewmanRegularizedZeroForce t r =
      1 / r + (1 / 4 : ℂ) *
        ∑' p : DeBruijnNewmanHDivisorZeroIndex t,
          deBruijnNewmanPolymathForceOrbitTerm t r p := by
  rw [deBruijnNewmanRegularizedZeroForce_eq_divisor_tsum]
  congr 1
  exact tsum_eq_quarter_tsum_equiv_orbit _
    (summable_deBruijnNewmanPolymathForceTerm t r) _ _

/-- Away from the selected fourfold orbit, regularization cancels pointwise under negation. -/
theorem deBruijnNewmanPolymathForceOrbitTerm_eq_four_reciprocals
    {t : ℝ} {r : ℂ} (p : DeBruijnNewmanHDivisorZeroIndex t)
    (h₀ : deBruijnNewmanHDivisorZeroValue p ≠ r)
    (hneg : -deBruijnNewmanHDivisorZeroValue p ≠ r)
    (hconj : conj (deBruijnNewmanHDivisorZeroValue p) ≠ r)
    (hnegConj : -conj (deBruijnNewmanHDivisorZeroValue p) ≠ r) :
    deBruijnNewmanPolymathForceOrbitTerm t r p =
      1 / (r - deBruijnNewmanHDivisorZeroValue p) +
      1 / (r + deBruijnNewmanHDivisorZeroValue p) +
      1 / (r - conj (deBruijnNewmanHDivisorZeroValue p)) +
      1 / (r + conj (deBruijnNewmanHDivisorZeroValue p)) := by
  simp only [deBruijnNewmanPolymathForceOrbitTerm, fourEquivOrbitTerm,
    deBruijnNewmanPolymathForceTerm, deBruijnNewmanHDivisorZeroNegEquiv_value,
    deBruijnNewmanHDivisorZeroConjEquiv_value]
  rw [if_neg h₀, if_neg hneg, if_neg hconj, if_neg hnegConj]
  ring

theorem one_div_sub_cartesian_im
    (x Y u v : ℝ) :
    (1 / (((x : ℂ) + (Y : ℂ) * I) - ((u : ℂ) + (v : ℂ) * I))).im =
      -(Y - v) / ((x - u) ^ 2 + (Y - v) ^ 2) := by
  simp only [one_div, inv_im, sub_im, add_im, mul_im, ofReal_re, ofReal_im,
    I_re, I_im, zero_mul, mul_one, zero_add, normSq_apply, sub_re, add_re,
    mul_re, sub_zero]
  ring

theorem polymathConjugatePairKernel_nonneg_of_below
    {d Y v : ℝ} (hv : |v| ≤ Y) :
    0 ≤ (Y - v) / (d ^ 2 + (Y - v) ^ 2) +
      (Y + v) / (d ^ 2 + (Y + v) ^ 2) := by
  have hvLower : -Y ≤ v := by linarith [neg_le_of_abs_le hv]
  have hvUpper : v ≤ Y := le_trans (le_abs_self v) hv
  exact add_nonneg
    (div_nonneg (by linarith) (add_nonneg (sq_nonneg d) (sq_nonneg (Y - v))))
    (div_nonneg (by linarith) (add_nonneg (sq_nonneg d) (sq_nonneg (Y + v))))

theorem polymathConjugatePairKernel_nonneg_of_above
    {d Y v : ℝ} (hY : 0 < Y) (hv : Y < v)
    (hgeom : v ^ 2 ≤ d ^ 2 + Y ^ 2) :
    0 ≤ (Y - v) / (d ^ 2 + (Y - v) ^ 2) +
      (Y + v) / (d ^ 2 + (Y + v) ^ 2) := by
  have hDminus : 0 < d ^ 2 + (Y - v) ^ 2 := by
    have hsq : 0 < (Y - v) ^ 2 := sq_pos_of_ne_zero (by linarith)
    nlinarith [sq_nonneg d]
  have hDplus : 0 < d ^ 2 + (Y + v) ^ 2 := by
    have hsq : 0 < (Y + v) ^ 2 := sq_pos_of_ne_zero (by linarith)
    nlinarith [sq_nonneg d]
  rw [div_add_div (Y - v) (Y + v) hDminus.ne' hDplus.ne']
  apply div_nonneg
  · have hcore : 0 ≤ 2 * Y * (d ^ 2 + Y ^ 2 - v ^ 2) := by positivity
    nlinarith [hcore]
  · exact mul_nonneg hDminus.le hDplus.le

theorem polymathConjugatePairKernel_nonneg
    {d Y v : ℝ} (hY : 0 < Y)
    (hgeom : v ^ 2 ≤ d ^ 2 + Y ^ 2) :
    0 ≤ (Y - v) / (d ^ 2 + (Y - v) ^ 2) +
      (Y + v) / (d ^ 2 + (Y + v) ^ 2) := by
  by_cases hv : |v| ≤ Y
  · exact polymathConjugatePairKernel_nonneg_of_below hv
  · have hYabs : Y < |v| := lt_of_not_ge hv
    rcases abs_cases v with ⟨habs, _⟩ | ⟨habs, _⟩
    · rw [habs] at hYabs
      exact polymathConjugatePairKernel_nonneg_of_above hY hYabs hgeom
    · have hneg : Y < -v := by simpa only [habs] using hYabs
      have hnegGeom : (-v) ^ 2 ≤ d ^ 2 + Y ^ 2 := by simpa using hgeom
      have h := polymathConjugatePairKernel_nonneg_of_above hY hneg hnegGeom
      simpa only [sub_eq_add_neg, neg_neg, add_comm] using h

theorem polymathConjugateReciprocalPair_im_nonpos
    {x Y u v : ℝ} (hY : 0 < Y)
    (hgeom : v ^ 2 ≤ (x - u) ^ 2 + Y ^ 2) :
    (1 / (((x : ℂ) + (Y : ℂ) * I) - ((u : ℂ) + (v : ℂ) * I)) +
      1 / (((x : ℂ) + (Y : ℂ) * I) - conj ((u : ℂ) + (v : ℂ) * I))).im ≤ 0 := by
  have hfirst := one_div_sub_cartesian_im x Y u v
  have hsecond := one_div_sub_cartesian_im x Y u (-v)
  have hkernel := polymathConjugatePairKernel_nonneg hY hgeom
  have hconjPoint :
      ((u : ℂ) + (-v : ℂ) * I) = conj ((u : ℂ) + (v : ℂ) * I) := by
    apply Complex.ext <;> simp
  simp only [ofReal_neg] at hsecond
  rw [hconjPoint] at hsecond
  simp only [sub_neg_eq_add] at hsecond
  rw [add_im, hfirst, hsecond]
  have hnonpos := neg_nonpos.mpr hkernel
  convert hnonpos using 1
  all_goals ring

theorem polymathFourfoldReciprocalOrbit_im_nonpos
    {x Y u v : ℝ} (hY : 0 < Y)
    (hleft : v ^ 2 ≤ (x - u) ^ 2 + Y ^ 2)
    (hright : v ^ 2 ≤ (x + u) ^ 2 + Y ^ 2) :
    (1 / (((x : ℂ) + (Y : ℂ) * I) - ((u : ℂ) + (v : ℂ) * I)) +
      1 / (((x : ℂ) + (Y : ℂ) * I) + ((u : ℂ) + (v : ℂ) * I)) +
      1 / (((x : ℂ) + (Y : ℂ) * I) - conj ((u : ℂ) + (v : ℂ) * I)) +
      1 / (((x : ℂ) + (Y : ℂ) * I) + conj ((u : ℂ) + (v : ℂ) * I))).im ≤ 0 := by
  have hpairLeft := polymathConjugateReciprocalPair_im_nonpos hY hleft
  have hpairRight := polymathConjugateReciprocalPair_im_nonpos
    (x := x) (Y := Y) (u := -u) (v := -v) hY (by simpa [sq] using hright)
  have hnegPoint :
      ((-u : ℂ) + (-v : ℂ) * I) = -((u : ℂ) + (v : ℂ) * I) := by
    apply Complex.ext <;> simp
  simp only [ofReal_neg] at hpairRight
  rw [hnegPoint] at hpairRight
  simp only [map_neg, sub_neg_eq_add] at hpairRight
  have himEq :
      (1 / (((x : ℂ) + (Y : ℂ) * I) - ((u : ℂ) + (v : ℂ) * I)) +
        1 / (((x : ℂ) + (Y : ℂ) * I) + ((u : ℂ) + (v : ℂ) * I)) +
        1 / (((x : ℂ) + (Y : ℂ) * I) - conj ((u : ℂ) + (v : ℂ) * I)) +
        1 / (((x : ℂ) + (Y : ℂ) * I) + conj ((u : ℂ) + (v : ℂ) * I))).im =
      (1 / (((x : ℂ) + (Y : ℂ) * I) - ((u : ℂ) + (v : ℂ) * I)) +
        1 / (((x : ℂ) + (Y : ℂ) * I) - conj ((u : ℂ) + (v : ℂ) * I))).im +
      (1 / (((x : ℂ) + (Y : ℂ) * I) + ((u : ℂ) + (v : ℂ) * I)) +
        1 / (((x : ℂ) + (Y : ℂ) * I) + conj ((u : ℂ) + (v : ℂ) * I))).im := by
    simp only [add_im]
    ring
  rw [himEq]
  linarith

/-- A non-contact divisor orbit has nonpositive vertical force once the two source geometric
inequalities hold. -/
theorem deBruijnNewmanPolymathForceOrbitTerm_im_nonpos_of_geometry
    {t x Y : ℝ} (p : DeBruijnNewmanHDivisorZeroIndex t) (hY : 0 < Y)
    (h₀ : deBruijnNewmanHDivisorZeroValue p ≠ (x : ℂ) + (Y : ℂ) * I)
    (hneg : -deBruijnNewmanHDivisorZeroValue p ≠ (x : ℂ) + (Y : ℂ) * I)
    (hconj : conj (deBruijnNewmanHDivisorZeroValue p) ≠ (x : ℂ) + (Y : ℂ) * I)
    (hnegConj :
      -conj (deBruijnNewmanHDivisorZeroValue p) ≠ (x : ℂ) + (Y : ℂ) * I)
    (hleft : (deBruijnNewmanHDivisorZeroValue p).im ^ 2 ≤
      (x - (deBruijnNewmanHDivisorZeroValue p).re) ^ 2 + Y ^ 2)
    (hright : (deBruijnNewmanHDivisorZeroValue p).im ^ 2 ≤
      (x + (deBruijnNewmanHDivisorZeroValue p).re) ^ 2 + Y ^ 2) :
    (deBruijnNewmanPolymathForceOrbitTerm t ((x : ℂ) + (Y : ℂ) * I) p).im ≤ 0 := by
  rw [deBruijnNewmanPolymathForceOrbitTerm_eq_four_reciprocals
    p h₀ hneg hconj hnegConj]
  have h := polymathFourfoldReciprocalOrbit_im_nonpos hY hleft hright
  simpa only [re_add_im] using h

/-- Escaping the horizontal barrier supplies both geometric square inequalities used by the
fourfold force orbit. -/
theorem polymathHorizontalEscape_sq_geometries
    {x X Y u v : ℝ} (hx0 : 0 ≤ x) (hxX : x ≤ X)
    (hY0 : 0 ≤ Y) (hY1 : Y ≤ 1) (hvStrip : v ^ 2 ≤ 1)
    (hescape : X + Real.sqrt (1 - Y ^ 2) ≤ |u|) :
    v ^ 2 ≤ (x - u) ^ 2 + Y ^ 2 ∧
      v ^ 2 ≤ (x + u) ^ 2 + Y ^ 2 := by
  have hrad : 0 ≤ 1 - Y ^ 2 := by nlinarith
  have hsqrtSq : (Real.sqrt (1 - Y ^ 2)) ^ 2 = 1 - Y ^ 2 :=
    Real.sq_sqrt hrad
  have hsqrt0 : 0 ≤ Real.sqrt (1 - Y ^ 2) := Real.sqrt_nonneg _
  rcases abs_cases u with ⟨huAbs, _hu0⟩ | ⟨huAbs, _hu0⟩
  · have hu : X + Real.sqrt (1 - Y ^ 2) ≤ u := by simpa only [huAbs] using hescape
    have hminus : Real.sqrt (1 - Y ^ 2) ≤ u - x := by linarith
    have hplus : Real.sqrt (1 - Y ^ 2) ≤ x + u := by linarith
    have hminusSq : 1 - Y ^ 2 ≤ (x - u) ^ 2 := by
      nlinarith [sq_nonneg (u - x - Real.sqrt (1 - Y ^ 2))]
    have hplusSq : 1 - Y ^ 2 ≤ (x + u) ^ 2 := by
      nlinarith [sq_nonneg (x + u - Real.sqrt (1 - Y ^ 2))]
    constructor <;> nlinarith
  · have hu : X + Real.sqrt (1 - Y ^ 2) ≤ -u := by simpa only [huAbs] using hescape
    have hminus : Real.sqrt (1 - Y ^ 2) ≤ x - u := by linarith
    have hplus : Real.sqrt (1 - Y ^ 2) ≤ -(x + u) := by linarith
    have hminusSq : 1 - Y ^ 2 ≤ (x - u) ^ 2 := by
      nlinarith [sq_nonneg (x - u - Real.sqrt (1 - Y ^ 2))]
    have hplusSq : 1 - Y ^ 2 ≤ (x + u) ^ 2 := by
      nlinarith [sq_nonneg (-(x + u) - Real.sqrt (1 - Y ^ 2))]
    constructor <;> nlinarith

/-- Strip control below the canopy and horizontal escape above it together make every non-contact
fourfold orbit vertically nonpositive. -/
theorem deBruijnNewmanPolymathForceOrbitTerm_im_nonpos_of_escape
    {t x X Y : ℝ} (p : DeBruijnNewmanHDivisorZeroIndex t)
    (hx0 : 0 ≤ x) (hxX : x ≤ X) (hY : 0 < Y) (hY1 : Y ≤ 1)
    (hstrip : (deBruijnNewmanHDivisorZeroValue p).im ^ 2 ≤ 1)
    (hescape : Y < |(deBruijnNewmanHDivisorZeroValue p).im| →
      X + Real.sqrt (1 - Y ^ 2) ≤
        |(deBruijnNewmanHDivisorZeroValue p).re|)
    (h₀ : deBruijnNewmanHDivisorZeroValue p ≠ (x : ℂ) + (Y : ℂ) * I)
    (hneg : -deBruijnNewmanHDivisorZeroValue p ≠ (x : ℂ) + (Y : ℂ) * I)
    (hconj : conj (deBruijnNewmanHDivisorZeroValue p) ≠ (x : ℂ) + (Y : ℂ) * I)
    (hnegConj :
      -conj (deBruijnNewmanHDivisorZeroValue p) ≠ (x : ℂ) + (Y : ℂ) * I) :
    (deBruijnNewmanPolymathForceOrbitTerm t ((x : ℂ) + (Y : ℂ) * I) p).im ≤ 0 := by
  have hgeometry :
      (deBruijnNewmanHDivisorZeroValue p).im ^ 2 ≤
          (x - (deBruijnNewmanHDivisorZeroValue p).re) ^ 2 + Y ^ 2 ∧
        (deBruijnNewmanHDivisorZeroValue p).im ^ 2 ≤
          (x + (deBruijnNewmanHDivisorZeroValue p).re) ^ 2 + Y ^ 2 := by
    by_cases him : |(deBruijnNewmanHDivisorZeroValue p).im| ≤ Y
    · have himLower : -Y ≤ (deBruijnNewmanHDivisorZeroValue p).im :=
        neg_le_of_abs_le him
      have himUpper : (deBruijnNewmanHDivisorZeroValue p).im ≤ Y :=
        le_trans (le_abs_self _) him
      constructor <;> nlinarith [sq_nonneg
        (x - (deBruijnNewmanHDivisorZeroValue p).re),
        sq_nonneg (x + (deBruijnNewmanHDivisorZeroValue p).re)]
    · exact polymathHorizontalEscape_sq_geometries hx0 hxX hY.le hY1 hstrip
        (hescape (lt_of_not_ge him))
  exact deBruijnNewmanPolymathForceOrbitTerm_im_nonpos_of_geometry
    p hY h₀ hneg hconj hnegConj hgeometry.1 hgeometry.2

/-- A divisor index at the selected upper-right contact has the exact fourfold orbit sum from the
three other symmetry-related zeros. -/
theorem deBruijnNewmanPolymathForceOrbitTerm_eq_of_value_eq_contact
    {t x Y : ℝ} (p : DeBruijnNewmanHDivisorZeroIndex t)
    (hx : 0 < x) (hY : 0 < Y)
    (hp : deBruijnNewmanHDivisorZeroValue p = (x : ℂ) + (Y : ℂ) * I) :
    deBruijnNewmanPolymathForceOrbitTerm t ((x : ℂ) + (Y : ℂ) * I) p =
      -(1 / (2 * ((x : ℂ) + (Y : ℂ) * I))) +
        1 / (((x : ℂ) + (Y : ℂ) * I) - conj ((x : ℂ) + (Y : ℂ) * I)) +
        1 / (((x : ℂ) + (Y : ℂ) * I) + conj ((x : ℂ) + (Y : ℂ) * I)) := by
  let r : ℂ := (x : ℂ) + (Y : ℂ) * I
  have hr0 : r ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp only [r, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero,
      mul_one, zero_add, zero_im] at him
    linarith
  have hneg : -r ≠ r := by
    intro h
    have him := congrArg Complex.im h
    simp only [r, neg_im, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im,
      mul_zero, mul_one, zero_add] at him
    linarith
  have hconj : conj r ≠ r := by
    intro h
    have him := congrArg Complex.im h
    simp only [r, conj_im, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im,
      mul_zero, mul_one, zero_add] at him
    linarith
  have hnegConj : -conj r ≠ r := by
    intro h
    have hre := congrArg Complex.re h
    simp only [r, neg_re, conj_re, add_re, ofReal_re, mul_re, ofReal_im, I_re,
      I_im, mul_zero, zero_mul, sub_zero] at hre
    linarith
  simp only [deBruijnNewmanPolymathForceOrbitTerm, fourEquivOrbitTerm,
    deBruijnNewmanPolymathForceTerm, deBruijnNewmanHDivisorZeroNegEquiv_value,
    deBruijnNewmanHDivisorZeroConjEquiv_value]
  rw [hp]
  change (if r = r then 0 else _) + (if -r = r then 0 else _) +
      (if conj r = r then 0 else _) + (if -conj r = r then 0 else _) = _
  rw [if_pos rfl, if_neg hneg, if_neg hconj, if_neg hnegConj]
  change 0 + (1 / (r - -r) + 1 / -r) +
      (1 / (r - conj r) + 1 / conj r) +
      (1 / (r - -conj r) + 1 / (-conj r)) =
    -(1 / (2 * r)) + 1 / (r - conj r) + 1 / (r + conj r)
  simp only [sub_neg_eq_add, zero_add, one_div, inv_neg, ← two_mul]
  have hcancel : (2 * r)⁻¹ - r⁻¹ = -(2 * r)⁻¹ := by
    field_simp [hr0]
    ring
  have hcancel' : (2 * r)⁻¹ + -r⁻¹ = -(2 * r)⁻¹ := by
    simpa only [sub_eq_add_neg] using hcancel
  rw [hcancel']
  ring

theorem sum_deBruijnNewmanPolymathForceOrbitTerm_symmetryOrbit_eq_four_mul
    {t x Y : ℝ} (p : DeBruijnNewmanHDivisorZeroIndex t)
    (hx : 0 < x) (hY : 0 < Y)
    (hp : deBruijnNewmanHDivisorZeroValue p = (x : ℂ) + (Y : ℂ) * I) :
    ∑ q ∈ deBruijnNewmanHDivisorZeroSymmetryOrbit p,
        deBruijnNewmanPolymathForceOrbitTerm t ((x : ℂ) + (Y : ℂ) * I) q =
      4 * deBruijnNewmanPolymathForceOrbitTerm t ((x : ℂ) + (Y : ℂ) * I) p := by
  classical
  let n := deBruijnNewmanHDivisorZeroNegEquiv t
  let c := deBruijnNewmanHDivisorZeroConjEquiv t
  let s := deBruijnNewmanHDivisorZeroSymmetryOrbit p
  let f := deBruijnNewmanPolymathForceOrbitTerm t ((x : ℂ) + (Y : ℂ) * I)
  have hcard : s.card = 4 := by
    simpa only [s] using
      deBruijnNewmanHDivisorZeroSymmetryOrbit_card_eq_four_of_contact p hx hY hp
  have hconst : ∀ q ∈ s, f q = f p := by
    intro q hq
    have hcases : q = p ∨ q = n p ∨ q = c p ∨ q = n (c p) := by
      simpa only [s, n, c, deBruijnNewmanHDivisorZeroSymmetryOrbit,
        Finset.mem_insert, Finset.mem_singleton] using hq
    rcases hcases with h | h | h | h
    · exact congrArg f h
    · rw [h]
      exact deBruijnNewmanPolymathForceOrbitTerm_negEquiv p
    · rw [h]
      exact deBruijnNewmanPolymathForceOrbitTerm_conjEquiv p
    · rw [h]
      exact (deBruijnNewmanPolymathForceOrbitTerm_negEquiv (c p)).trans
        (deBruijnNewmanPolymathForceOrbitTerm_conjEquiv p)
  change ∑ q ∈ s, f q = 4 * f p
  calc
    ∑ q ∈ s, f q = ∑ _q ∈ s, f p := by
      exact Finset.sum_congr rfl fun q hq ↦ hconst q hq
    _ = 4 * f p := by simp [hcard]

theorem deBruijnNewmanPolymathForceOrbitTerm_im_eq_of_value_eq_contact
    {t x Y : ℝ} (p : DeBruijnNewmanHDivisorZeroIndex t)
    (hx : 0 < x) (hY : 0 < Y)
    (hp : deBruijnNewmanHDivisorZeroValue p = (x : ℂ) + (Y : ℂ) * I) :
    (deBruijnNewmanPolymathForceOrbitTerm t ((x : ℂ) + (Y : ℂ) * I) p).im =
      Y / (2 * (x ^ 2 + Y ^ 2)) - 1 / (2 * Y) := by
  let r : ℂ := (x : ℂ) + (Y : ℂ) * I
  have hr0 : r ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp only [r, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero,
      mul_one, zero_add, zero_im] at him
    linarith
  have hinv : (1 / r).im = -Y / (x ^ 2 + Y ^ 2) := by
    simpa only [r, sub_zero, ofReal_zero, zero_mul, add_zero] using
      one_div_sub_cartesian_im x Y 0 0
  have htwo : 1 / (2 * r) = (1 / 2 : ℂ) * (1 / r) := by
    field_simp [hr0]
  have hfirst : (-(1 / (2 * r))).im = Y / (2 * (x ^ 2 + Y ^ 2)) := by
    rw [htwo, neg_im, mul_im, hinv]
    norm_num
    have hden : x ^ 2 + Y ^ 2 ≠ 0 := by positivity
    field_simp [hden]
  have hconjPoint :
      ((x : ℂ) + (-Y : ℂ) * I) = conj r := by
    apply Complex.ext <;> simp [r]
  have hsecondRaw := one_div_sub_cartesian_im x Y x (-Y)
  simp only [ofReal_neg] at hsecondRaw
  rw [hconjPoint] at hsecondRaw
  have hsecond : (1 / (r - conj r)).im = -1 / (2 * Y) := by
    rw [hsecondRaw]
    field_simp [hY.ne']
    ring
  have hrealSum : r + conj r = (2 * x : ℝ) := by
    apply Complex.ext
    · simp [r]
      ring
    · simp [r]
  have hthird : (1 / (r + conj r)).im = 0 := by
    rw [hrealSum]
    simp
  rw [deBruijnNewmanPolymathForceOrbitTerm_eq_of_value_eq_contact p hx hY hp]
  change (-(1 / (2 * r)) + 1 / (r - conj r) + 1 / (r + conj r)).im = _
  rw [add_im, add_im, hfirst, hsecond, hthird]
  ring

/-- The Polymath geometry gives the strict vertical force inequality at any simple upper-right
contact. The horizontal-escape premise is the exact first-contact consequence used separately
below. -/
theorem deBruijnNewmanRegularizedZeroForce_im_lt_of_simple_contact_escape
    {t x X Y : ℝ} (ht0 : 0 ≤ t) (hthalf : t ≤ (1 : ℝ) / 2)
    (hx : 0 < x) (hxX : x ≤ X) (hY : 0 < Y) (hY1 : Y ≤ 1)
    (hzero : deBruijnNewmanH t ((x : ℂ) + (Y : ℂ) * I) = 0)
    (hsimple : deriv (deBruijnNewmanH t) ((x : ℂ) + (Y : ℂ) * I) ≠ 0)
    (hescape : ∀ p : DeBruijnNewmanHDivisorZeroIndex t,
      Y < |(deBruijnNewmanHDivisorZeroValue p).im| →
        X + Real.sqrt (1 - Y ^ 2) ≤
          |(deBruijnNewmanHDivisorZeroValue p).re|) :
    (2 * deBruijnNewmanRegularizedZeroForce t
      ((x : ℂ) + (Y : ℂ) * I)).im < -1 / Y := by
  classical
  let r : ℂ := (x : ℂ) + (Y : ℂ) * I
  let Z := DeBruijnNewmanHDivisorZeroIndex t
  let n := deBruijnNewmanHDivisorZeroNegEquiv t
  let c := deBruijnNewmanHDivisorZeroConjEquiv t
  let orbitTerm : Z → ℂ := deBruijnNewmanPolymathForceOrbitTerm t r
  let fiber := Complex.Hadamard.divisorZeroIndex₀_fiberFinset
    (f := deBruijnNewmanH t) r
  have hfiberCard : fiber.card = 1 := by
    simpa only [fiber, r] using
      deBruijnNewman_simpleZero_fiber_card_eq_one hzero hsimple
  obtain ⟨p0, hfiber⟩ := Finset.card_eq_one.mp hfiberCard
  have hp0mem : p0 ∈ fiber := by simp [hfiber]
  have hp0val : deBruijnNewmanHDivisorZeroValue p0 = r := by
    apply (Complex.Hadamard.mem_divisorZeroIndex₀_fiberFinset
      (deBruijnNewmanH t) r p0).mp
    exact hp0mem
  have hvalUnique : ∀ q : Z, deBruijnNewmanHDivisorZeroValue q = r → q = p0 := by
    intro q hq
    have hqmem : q ∈ fiber := by
      apply (Complex.Hadamard.mem_divisorZeroIndex₀_fiberFinset
        (deBruijnNewmanH t) r q).mpr
      exact hq
    rw [hfiber] at hqmem
    simpa using hqmem
  let s := deBruijnNewmanHDivisorZeroSymmetryOrbit p0
  have hp0val' : deBruijnNewmanHDivisorZeroValue p0 =
      (x : ℂ) + (Y : ℂ) * I := by simpa only [r] using hp0val
  have hsumOrbit : Summable orbitTerm := by
    simpa only [orbitTerm, r] using
      summable_deBruijnNewmanPolymathForceOrbitTerm t r
  have hsumIm : Summable (fun q : Z ↦ (orbitTerm q).im) :=
    Complex.imCLM.summable hsumOrbit
  have hcomplement :
      ∑' q : (sᶜ : Set Z), (orbitTerm q.1).im ≤ 0 := by
    apply tsum_nonpos
    intro q
    have hqnotSet : q.1 ∉ (s : Set Z) := q.2
    have hqnot : q.1 ∉ s := hqnotSet
    have h₀ : deBruijnNewmanHDivisorZeroValue q.1 ≠ r := by
      intro h
      apply hqnot
      rw [hvalUnique q.1 h]
      simp [s, deBruijnNewmanHDivisorZeroSymmetryOrbit]
    have hneg : -deBruijnNewmanHDivisorZeroValue q.1 ≠ r := by
      intro h
      have hnval : deBruijnNewmanHDivisorZeroValue (n q.1) = r := by
        simpa only [n, deBruijnNewmanHDivisorZeroNegEquiv_value] using h
      have hnEq := hvalUnique (n q.1) hnval
      have hqEq : q.1 = n p0 := by
        have := congrArg n hnEq
        simpa only [n, deBruijnNewmanHDivisorZeroNegEquiv_apply_apply] using this
      apply hqnot
      rw [hqEq]
      simp [s, n, deBruijnNewmanHDivisorZeroSymmetryOrbit]
    have hconj : conj (deBruijnNewmanHDivisorZeroValue q.1) ≠ r := by
      intro h
      have hcval : deBruijnNewmanHDivisorZeroValue (c q.1) = r := by
        simpa only [c, deBruijnNewmanHDivisorZeroConjEquiv_value] using h
      have hcEq := hvalUnique (c q.1) hcval
      have hqEq : q.1 = c p0 := by
        have := congrArg c hcEq
        simpa only [c, deBruijnNewmanHDivisorZeroConjEquiv_apply_apply] using this
      apply hqnot
      rw [hqEq]
      simp [s, c, deBruijnNewmanHDivisorZeroSymmetryOrbit]
    have hnegConj : -conj (deBruijnNewmanHDivisorZeroValue q.1) ≠ r := by
      intro h
      have hncval : deBruijnNewmanHDivisorZeroValue (n (c q.1)) = r := by
        simpa only [n, c, deBruijnNewmanHDivisorZeroNegEquiv_value,
          deBruijnNewmanHDivisorZeroConjEquiv_value] using h
      have hncEq := hvalUnique (n (c q.1)) hncval
      have hcEq : c q.1 = n p0 := by
        have := congrArg n hncEq
        simpa only [n, deBruijnNewmanHDivisorZeroNegEquiv_apply_apply] using this
      have hqEq : q.1 = n (c p0) := by
        have hqc : q.1 = c (n p0) := by
          have := congrArg c hcEq
          simpa only [c, deBruijnNewmanHDivisorZeroConjEquiv_apply_apply] using this
        calc
          q.1 = c (n p0) := hqc
          _ = n (c p0) := by
            simpa only [n, c] using
              (deBruijnNewmanHDivisorZeroNegEquiv_conjEquiv p0).symm
      apply hqnot
      rw [hqEq]
      simp [s, n, c, deBruijnNewmanHDivisorZeroSymmetryOrbit]
    have hvalueZero := deBruijnNewmanH_divisorZeroIndex₀_val_eq_zero t q.1
    have hstripBase := deBruijnNewmanH_zero_im_sq_le_one_sub_two_mul
      ht0 hthalf hvalueZero
    have hstrip : (deBruijnNewmanHDivisorZeroValue q.1).im ^ 2 ≤ 1 := by
      linarith
    exact deBruijnNewmanPolymathForceOrbitTerm_im_nonpos_of_escape
      q.1 hx.le hxX hY hY1 hstrip (hescape q.1) h₀ hneg hconj hnegConj
  have hfiniteIm :
      ∑ q ∈ s, (orbitTerm q).im = 4 * (orbitTerm p0).im := by
    have hsum := sum_deBruijnNewmanPolymathForceOrbitTerm_symmetryOrbit_eq_four_mul
      p0 hx hY hp0val'
    have him := congrArg Complex.im hsum
    norm_num at him
    simpa only [s, orbitTerm, r, map_sum] using him
  have horbitImLe : (∑' q : Z, (orbitTerm q).im) ≤ 4 * (orbitTerm p0).im := by
    calc
      (∑' q : Z, (orbitTerm q).im) =
          (∑ q ∈ s, (orbitTerm q).im) +
            ∑' q : (sᶜ : Set Z), (orbitTerm q.1).im :=
        hsumIm.sum_add_tsum_compl.symm
      _ ≤ 4 * (orbitTerm p0).im := by rw [hfiniteIm]; linarith
  have hp0OrbitIm :=
    deBruijnNewmanPolymathForceOrbitTerm_im_eq_of_value_eq_contact p0 hx hY hp0val'
  have hforceEq := deBruijnNewmanRegularizedZeroForce_eq_quarter_orbit_tsum t r
  have hforceIm :
      (deBruijnNewmanRegularizedZeroForce t r).im =
        -Y / (x ^ 2 + Y ^ 2) +
          (1 / 4) * ∑' q : Z, (orbitTerm q).im := by
    have htsumIm :
        (∑' q : Z, orbitTerm q).im = ∑' q : Z, (orbitTerm q).im :=
      Complex.im_tsum hsumOrbit
    rw [hforceEq, add_im, mul_im, htsumIm]
    simp only [r, orbitTerm, one_div, inv_im, normSq_apply, add_re, ofReal_re,
      mul_re, ofReal_im, I_re, I_im, mul_zero, sub_zero, add_im,
      mul_im, mul_one, zero_add]
    norm_num
    ring
  have hden : 0 < x ^ 2 + Y ^ 2 := by positivity
  rw [mul_im, hforceIm]
  norm_num
  rw [hp0OrbitIm] at horbitImLe
  have hstrict : 0 < Y / (x ^ 2 + Y ^ 2) := div_pos hY hden
  have horbitImLe' :
      (∑' q : Z, (orbitTerm q).im) ≤
        2 * (Y / (x ^ 2 + Y ^ 2)) - 2 * (1 / Y) := by
    calc
      (∑' q : Z, (orbitTerm q).im) ≤
          4 * (Y / (2 * (x ^ 2 + Y ^ 2)) - 1 / (2 * Y)) := horbitImLe
      _ = 2 * (Y / (x ^ 2 + Y ^ 2)) - 2 * (1 / Y) := by
        field_simp [hden.ne', hY.ne']
        ring
  have hforceLe :
      2 * (-Y / (x ^ 2 + Y ^ 2) +
        1 / 4 * ∑' q : Z, (orbitTerm q).im) ≤
          -Y / (x ^ 2 + Y ^ 2) - 1 / Y := by
    calc
      2 * (-Y / (x ^ 2 + Y ^ 2) +
          1 / 4 * ∑' q : Z, (orbitTerm q).im) =
          -2 * (Y / (x ^ 2 + Y ^ 2)) +
            (1 / 2) * ∑' q : Z, (orbitTerm q).im := by ring
      _ ≤ -2 * (Y / (x ^ 2 + Y ^ 2)) +
          (1 / 2) * (2 * (Y / (x ^ 2 + Y ^ 2)) - 2 * (1 / Y)) := by
        gcongr
      _ = -Y / (x ^ 2 + Y ^ 2) - 1 / Y := by ring
  have hnegative : -Y / (x ^ 2 + Y ^ 2) < 0 :=
    div_neg_of_neg_of_pos (neg_lt_zero.mpr hY) hden
  have htarget : -Y / (x ^ 2 + Y ^ 2) - 1 / Y < -1 / Y := by
    calc
      -Y / (x ^ 2 + Y ^ 2) - 1 / Y < 0 - 1 / Y :=
        sub_lt_sub_right hnegative _
      _ = -1 / Y := by ring
  exact lt_of_le_of_lt hforceLe htarget

/-- Compact spacetime witnesses to failure of the moving zero-free region. -/
def deBruijnNewmanPolymathBadWitnesses (t0 X y0 : ℝ) :
    Set ((ℝ × ℝ) × ℝ) :=
  Icc (((0 : ℝ), (0 : ℝ)), (0 : ℝ)) ((t0, X), 1) ∩
    {p | deBruijnNewmanPolymathBoundaryHeight t0 y0 p.1.1 ≤ p.2} ∩
    {p | deBruijnNewmanH p.1.1 ((p.1.2 : ℂ) + (p.2 : ℂ) * I) = 0}

/-- Times at which the compact moving region contains a zero. -/
def deBruijnNewmanPolymathBadTimes (t0 X y0 : ℝ) : Set ℝ :=
  (fun p : (ℝ × ℝ) × ℝ ↦ p.1.1) ''
    deBruijnNewmanPolymathBadWitnesses t0 X y0

theorem isClosed_deBruijnNewmanPolymathBadWitnesses (t0 X y0 : ℝ) :
    IsClosed (deBruijnNewmanPolymathBadWitnesses t0 X y0) := by
  have hheight : Continuous
      (fun p : (ℝ × ℝ) × ℝ ↦ deBruijnNewmanPolymathBoundaryHeight t0 y0 p.1.1) := by
    unfold deBruijnNewmanPolymathBoundaryHeight
    fun_prop
  have hy : Continuous (fun p : (ℝ × ℝ) × ℝ ↦ p.2) := by fun_prop
  have hpoint : Continuous (fun p : (ℝ × ℝ) × ℝ ↦
      (p.1.1, (p.1.2 : ℂ) + (p.2 : ℂ) * I)) := by
    fun_prop
  have hzero : Continuous (fun p : (ℝ × ℝ) × ℝ ↦
      deBruijnNewmanH p.1.1 ((p.1.2 : ℂ) + (p.2 : ℂ) * I)) :=
    continuous_deBruijnNewmanH_joint.comp hpoint
  unfold deBruijnNewmanPolymathBadWitnesses
  exact isClosed_Icc.inter (isClosed_le hheight hy) |>.inter
    (isClosed_eq hzero continuous_const)

theorem isCompact_deBruijnNewmanPolymathBadWitnesses (t0 X y0 : ℝ) :
    IsCompact (deBruijnNewmanPolymathBadWitnesses t0 X y0) := by
  exact isCompact_Icc.of_isClosed_subset
    (isClosed_deBruijnNewmanPolymathBadWitnesses t0 X y0)
    (fun _ hp ↦ hp.1.1)

theorem isCompact_deBruijnNewmanPolymathBadTimes (t0 X y0 : ℝ) :
    IsCompact (deBruijnNewmanPolymathBadTimes t0 X y0) := by
  exact (isCompact_deBruijnNewmanPolymathBadWitnesses t0 X y0).image
    (by fun_prop)

/-- If a bad spacetime witness exists, then there is an earliest bad time. -/
theorem exists_deBruijnNewmanPolymath_firstBadTime
    {t0 X y0 : ℝ}
    (hbad : (deBruijnNewmanPolymathBadWitnesses t0 X y0).Nonempty) :
    ∃ t1 ∈ deBruijnNewmanPolymathBadTimes t0 X y0,
      ∀ t ∈ deBruijnNewmanPolymathBadTimes t0 X y0, t1 ≤ t := by
  have htimes : (deBruijnNewmanPolymathBadTimes t0 X y0).Nonempty := by
    rcases hbad with ⟨p, hp⟩
    exact ⟨p.1.1, ⟨p, hp, rfl⟩⟩
  obtain ⟨t1, ht1, hmin⟩ :=
    (isCompact_deBruijnNewmanPolymathBadTimes t0 X y0).exists_isMinOn
      htimes continuous_id.continuousOn
  exact ⟨t1, ht1, hmin⟩

theorem mem_deBruijnNewmanPolymathBadWitnesses_iff
    {t0 X y0 : ℝ} {p : (ℝ × ℝ) × ℝ} :
    p ∈ deBruijnNewmanPolymathBadWitnesses t0 X y0 ↔
      0 ≤ p.1.1 ∧ p.1.1 ≤ t0 ∧
      0 ≤ p.1.2 ∧ p.1.2 ≤ X ∧
      0 ≤ p.2 ∧ p.2 ≤ 1 ∧
      deBruijnNewmanPolymathBoundaryHeight t0 y0 p.1.1 ≤ p.2 ∧
      deBruijnNewmanH p.1.1 ((p.1.2 : ℂ) + (p.2 : ℂ) * I) = 0 := by
  simp only [deBruijnNewmanPolymathBadWitnesses, mem_inter_iff, mem_Icc,
    mem_setOf_eq]
  constructor
  · rintro ⟨⟨⟨hlow, hupp⟩, hheight⟩, hzero⟩
    exact ⟨hlow.1.1, hupp.1.1, hlow.1.2, hupp.1.2, hlow.2, hupp.2,
      hheight, hzero⟩
  · rintro ⟨ht0, htt0, hx0, hxX, hy0, hy1, hheight, hzero⟩
    exact ⟨⟨⟨⟨⟨ht0, hx0⟩, hy0⟩, ⟨⟨htt0, hxX⟩, hy1⟩⟩, hheight⟩, hzero⟩

/-- The initial certificate excludes time zero from the compact bad-time set. -/
theorem deBruijnNewmanPolymathBadTime_pos_of_initial
    {t0 X y0 t : ℝ}
    (hinit : deBruijnNewmanPolymathInitialRegionZeroFree t0 X y0)
    (ht : t ∈ deBruijnNewmanPolymathBadTimes t0 X y0) :
    0 < t := by
  rcases ht with ⟨p, hp, rfl⟩
  rw [mem_deBruijnNewmanPolymathBadWitnesses_iff] at hp
  rcases hp with ⟨ht0, _htt0, hx0, hxX, _hy0, hy1, hheight, hzero⟩
  have htNe : p.1.1 ≠ 0 := by
    intro htZero
    have hheight0 : Real.sqrt (y0 ^ 2 + 2 * t0) ≤ p.2 := by
      simpa [deBruijnNewmanPolymathBoundaryHeight, htZero] using hheight
    exact hinit p.1.2 p.2 hx0 hxX hheight0 hy1 (by simpa only [htZero] using hzero)
  exact lt_of_le_of_ne ht0 (Ne.symm htNe)

/-- A bad witness cannot lie on either vertical side of the Polymath rectangle. -/
theorem deBruijnNewmanPolymathBadWitness_re_mem_Ioo
    {t0 X y0 : ℝ} (hthalf : t0 ≤ (1 : ℝ) / 2)
    (haxis : ∀ t y : ℝ, deBruijnNewmanH t ((y : ℂ) * I) ≠ 0)
    (hbarrier : deBruijnNewmanPolymathBarrierRegionZeroFree t0 X y0)
    {p : (ℝ × ℝ) × ℝ}
    (hp : p ∈ deBruijnNewmanPolymathBadWitnesses t0 X y0) :
    p.1.2 ∈ Ioo 0 X := by
  rw [mem_deBruijnNewmanPolymathBadWitnesses_iff] at hp
  rcases hp with ⟨ht0, htt0, hx0, hxX, _hy0, _hy1, hheight, hzero⟩
  have hxNeZero : p.1.2 ≠ 0 := by
    intro hxZero
    have hno := haxis p.1.1 p.2
    apply hno
    simpa only [hxZero, Complex.ofReal_zero, zero_add] using hzero
  have hxNeX : p.1.2 ≠ X := by
    intro hxEq
    have htHalf : p.1.1 ≤ (1 : ℝ) / 2 := htt0.trans hthalf
    have hstrip := deBruijnNewmanH_zero_im_sq_le_one_sub_two_mul ht0 htHalf hzero
    have him : (((p.1.2 : ℂ) + (p.2 : ℂ) * I).im) = p.2 := by simp
    rw [him] at hstrip
    have hrad : 0 ≤ 1 - 2 * p.1.1 := by linarith
    have hyTop : p.2 ≤ Real.sqrt (1 - 2 * p.1.1) := by
      nlinarith [Real.sq_sqrt hrad, Real.sqrt_nonneg (1 - 2 * p.1.1)]
    have hno := hbarrier p.1.1 p.1.2 p.2 ht0 htt0
      (show X ≤ p.1.2 by rw [hxEq])
      (show p.1.2 ≤ X + Real.sqrt (1 - y0 ^ 2) by
        rw [hxEq]
        exact le_add_of_nonneg_right (Real.sqrt_nonneg _))
      hheight hyTop
    exact hno hzero
  exact ⟨lt_of_le_of_ne hx0 (Ne.symm hxNeZero),
    lt_of_le_of_ne hxX hxNeX⟩

/-- At the earliest bad time, every bad witness lies on the moving lower boundary.
The proof uses compactness and multiplicity-free zero persistence, so it applies before the
simple/repeated split. -/
theorem deBruijnNewmanPolymath_firstBadWitness_im_eq_boundary
    {t0 X y0 t1 x y : ℝ} (hthalf : t0 ≤ (1 : ℝ) / 2)
    (hinit : deBruijnNewmanPolymathInitialRegionZeroFree t0 X y0)
    (haxis : ∀ t y : ℝ, deBruijnNewmanH t ((y : ℂ) * I) ≠ 0)
    (hbarrier : deBruijnNewmanPolymathBarrierRegionZeroFree t0 X y0)
    (hmin : ∀ t ∈ deBruijnNewmanPolymathBadTimes t0 X y0, t1 ≤ t)
    (hp : ((t1, x), y) ∈ deBruijnNewmanPolymathBadWitnesses t0 X y0) :
    y = deBruijnNewmanPolymathBoundaryHeight t0 y0 t1 := by
  have ht1Bad : t1 ∈ deBruijnNewmanPolymathBadTimes t0 X y0 :=
    ⟨((t1, x), y), hp, rfl⟩
  have ht1Pos : 0 < t1 :=
    deBruijnNewmanPolymathBadTime_pos_of_initial hinit ht1Bad
  rcases mem_deBruijnNewmanPolymathBadWitnesses_iff.mp hp with
    ⟨ht10, ht1t0, _hx0, _hxX, hy0, _hy1, hheight, hzero⟩
  have hxInterior : x ∈ Ioo 0 X :=
    deBruijnNewmanPolymathBadWitness_re_mem_Ioo hthalf haxis hbarrier hp
  apply le_antisymm
  · by_contra hyNot
    have hYlt : deBruijnNewmanPolymathBoundaryHeight t0 y0 t1 < y :=
      lt_of_not_ge hyNot
    have ht1Half : t1 ≤ (1 : ℝ) / 2 := ht1t0.trans hthalf
    have hstrip := deBruijnNewmanH_zero_im_sq_le_one_sub_two_mul
      ht10 ht1Half hzero
    have him : (((x : ℂ) + (y : ℂ) * I).im) = y := by simp
    rw [him] at hstrip
    have hyNonneg : 0 ≤ y := hy0
    have hyOne : y < 1 := by
      nlinarith [sq_nonneg (y - 1)]
    let c : ℝ := (deBruijnNewmanPolymathBoundaryHeight t0 y0 t1 + y) / 2
    have hYc : deBruijnNewmanPolymathBoundaryHeight t0 y0 t1 < c := by
      dsimp only [c]
      linarith
    have hcy : c < y := by
      dsimp only [c]
      linarith
    let U : Set ℂ := {z | 0 < z.re ∧ z.re < X ∧ c < z.im ∧ z.im < 1}
    have hUOpen : IsOpen U := by
      simpa only [U, setOf_and] using
        (isOpen_lt continuous_const Complex.continuous_re).inter
          ((isOpen_lt Complex.continuous_re continuous_const).inter
            ((isOpen_lt continuous_const Complex.continuous_im).inter
              (isOpen_lt Complex.continuous_im continuous_const)))
    let z0 : ℂ := (x : ℂ) + (y : ℂ) * I
    have hz0U : z0 ∈ U := by
      simpa [z0, U] using ⟨hxInterior.1, hxInterior.2, hcy, hyOne⟩
    obtain ⟨R, hR, hboundary, hballU⟩ :=
      exists_deBruijnNewmanH_isolating_closedBall_subset
        hzero (hUOpen.mem_nhds hz0U)
    have hpersist := eventually_exists_deBruijnNewmanH_zero_mem_closedBall
      hR hzero hboundary
    have hYcont : ContinuousAt
        (deBruijnNewmanPolymathBoundaryHeight t0 y0) t1 := by
      unfold deBruijnNewmanPolymathBoundaryHeight
      fun_prop
    have hYevent : ∀ᶠ t in 𝓝 t1,
        deBruijnNewmanPolymathBoundaryHeight t0 y0 t < c :=
      hYcont.eventually (Iio_mem_nhds hYc)
    have hevent : ∀ᶠ t in 𝓝 t1,
        0 < t ∧ deBruijnNewmanPolymathBoundaryHeight t0 y0 t < c ∧
          ∃ z ∈ Metric.closedBall z0 R, deBruijnNewmanH t z = 0 := by
      filter_upwards [Ioi_mem_nhds ht1Pos, hYevent, hpersist] with t ht hY hz
      exact ⟨ht, hY, hz⟩
    obtain ⟨t, htt1, ht, hYt, z, hzBall, hzZero⟩ := hevent.exists_lt
    have hzU := hballU hzBall
    have hzPoint : (z.re : ℂ) + (z.im : ℂ) * I = z := by
      apply Complex.ext <;> simp
    have htLe : t ≤ t0 := (le_of_lt htt1).trans ht1t0
    have hcNonneg : 0 ≤ c := by
      dsimp only [c]
      have hYnonneg : 0 ≤ deBruijnNewmanPolymathBoundaryHeight t0 y0 t1 := by
        exact Real.sqrt_nonneg _
      linarith
    have htBadWitness : ((t, z.re), z.im) ∈
        deBruijnNewmanPolymathBadWitnesses t0 X y0 := by
      rw [mem_deBruijnNewmanPolymathBadWitnesses_iff]
      exact ⟨ht.le, htLe, hzU.1.le, hzU.2.1.le,
        hcNonneg.trans (le_of_lt hzU.2.2.1), hzU.2.2.2.le,
        (hYt.trans hzU.2.2.1).le, by simpa only [hzPoint] using hzZero⟩
    have htBad : t ∈ deBruijnNewmanPolymathBadTimes t0 X y0 :=
      ⟨((t, z.re), z.im), htBadWitness, rfl⟩
    exact (not_lt_of_ge (hmin t htBad)) htt1
  · exact hheight

private theorem cos_mul_I_mul_ofReal (y u : ℝ) :
    Complex.cos (((y : ℂ) * I) * (u : ℂ)) = (Real.cosh (y * u) : ℂ) := by
  rw [show ((y : ℂ) * I) * (u : ℂ) = ((y * u : ℝ) : ℂ) * I by push_cast; ring,
    Complex.cos_mul_I, ← Complex.ofReal_cosh]

private theorem integrableOn_deBruijnNewmanImaginaryAxisIntegrand (t y : ℝ) :
    IntegrableOn
      (fun u : ℝ ↦
        Real.exp (t * u ^ 2) * deBruijnNewmanPhi u * Real.cosh (y * u))
      (Ioi 0) := by
  have hre := (integrableOn_dbnHeatCosIntegrand t ((y : ℂ) * I)).re
  apply hre.congr
  filter_upwards with u
  rw [cos_mul_I_mul_ofReal, ← Complex.ofReal_mul]
  exact RCLike.ofReal_re _

/-- The source heat family is strictly positive on the entire imaginary axis. -/
theorem deBruijnNewmanH_mul_I_re_pos (t y : ℝ) :
    0 < (deBruijnNewmanH t ((y : ℂ) * I)).re := by
  let f : ℝ → ℝ := fun u ↦
    Real.exp (t * u ^ 2) * deBruijnNewmanPhi u * Real.cosh (y * u)
  have hfInt : Integrable f (volume.restrict (Ioi 0)) := by
    change IntegrableOn f (Ioi 0)
    exact integrableOn_deBruijnNewmanImaginaryAxisIntegrand t y
  have hfNonneg : 0 ≤ᵐ[volume.restrict (Ioi 0)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (mul_pos
      (mul_pos (Real.exp_pos _) (deBruijnNewmanPhi_pos hu.le))
      (Real.cosh_pos _)).le
  have hsupport : 0 < (volume.restrict (Ioi 0)) (Function.support f) := by
    have hsubset : Ioo (0 : ℝ) 1 ⊆ Function.support f := by
      intro u hu
      exact (mul_pos
        (mul_pos (Real.exp_pos _) (deBruijnNewmanPhi_pos hu.1.le))
        (Real.cosh_pos _)).ne'
    have hmeasure : 0 < (volume.restrict (Ioi 0)) (Ioo (0 : ℝ) 1) := by
      rw [Measure.restrict_apply measurableSet_Ioo]
      simp only [Ioo_inter_Ioi, max_eq_left (by norm_num : (0 : ℝ) ≤ 0),
        Real.volume_Ioo, sub_zero, ENNReal.ofReal_one]
      norm_num
    exact hmeasure.trans_le (measure_mono hsubset)
  have hfPos : 0 < ∫ u, f u ∂volume.restrict (Ioi 0) :=
    (integral_pos_iff_support_of_nonneg_ae hfNonneg hfInt).2 hsupport
  have hH : deBruijnNewmanH t ((y : ℂ) * I) =
      ((∫ u, f u ∂volume.restrict (Ioi 0) : ℝ) : ℂ) := by
    rw [deBruijnNewmanH, ← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards with u
    rw [cos_mul_I_mul_ofReal]
    simp only [f]
    push_cast
    rfl
  rw [hH]
  simpa using hfPos

/-- There are no source heat-family zeros on the imaginary axis at any heat time. -/
theorem deBruijnNewmanH_mul_I_ne_zero (t y : ℝ) :
    deBruijnNewmanH t ((y : ℂ) * I) ≠ 0 := by
  intro hzero
  have hpos := deBruijnNewmanH_mul_I_re_pos t y
  rw [hzero, Complex.zero_re] at hpos
  exact lt_irrefl 0 hpos

/-- The time-zero region certificate remains valid after deleting its redundant upper boundary. -/
theorem deBruijnNewmanPolymathInitialRegionZeroFree.above
    {t0 X y0 : ℝ}
    (hinit : deBruijnNewmanPolymathInitialRegionZeroFree t0 X y0)
    {x y : ℝ} (hx0 : 0 ≤ x) (hxX : x ≤ X)
    (hy : Real.sqrt (y0 ^ 2 + 2 * t0) ≤ y) :
    deBruijnNewmanH 0 ((x : ℂ) + (y : ℂ) * I) ≠ 0 := by
  by_cases hy1 : y ≤ 1
  · exact hinit x y hx0 hxX hy hy1
  intro hzero
  have hstrip := deBruijnNewmanH_zero_im_mem_Ioo hzero
  have him : (((x : ℂ) + (y : ℂ) * I).im) = y := by simp
  rw [him] at hstrip
  exact (not_lt_of_ge (lt_of_not_ge hy1).le) hstrip.2

/-- The terminal region certificate remains valid after deleting its strip-implied upper bound. -/
theorem deBruijnNewmanPolymathFinalRegionZeroFree.above
    {t0 X y0 : ℝ} (ht0 : 0 ≤ t0) (hthalf : t0 ≤ (1 : ℝ) / 2)
    (hfinal : deBruijnNewmanPolymathFinalRegionZeroFree t0 X y0)
    {x y : ℝ} (hx : X + Real.sqrt (1 - y0 ^ 2) ≤ x) (hy : y0 ≤ y)
    (hy0 : 0 ≤ y0) :
    deBruijnNewmanH t0 ((x : ℂ) + (y : ℂ) * I) ≠ 0 := by
  by_cases hyTop : y ≤ Real.sqrt (1 - 2 * t0)
  · exact hfinal x y hx hy hyTop
  intro hzero
  have hstrip := deBruijnNewmanH_zero_im_sq_le_one_sub_two_mul ht0 hthalf hzero
  have hrad : 0 ≤ 1 - 2 * t0 := by linarith
  have hyPos : 0 ≤ y := hy0.trans hy
  have hsqrtLt : Real.sqrt (1 - 2 * t0) < y := lt_of_not_ge hyTop
  have hySq : 1 - 2 * t0 < y ^ 2 := by
    nlinarith [Real.sq_sqrt hrad, Real.sqrt_nonneg (1 - 2 * t0)]
  have him : (((x : ℂ) + (y : ℂ) * I).im) = y := by simp
  rw [him] at hstrip
  exact (not_lt_of_ge hstrip) hySq

/-- The spacetime barrier certificate remains valid after deleting its strip-implied upper bound. -/
theorem deBruijnNewmanPolymathBarrierRegionZeroFree.above
    {t0 X y0 : ℝ}
    (hbarrier : deBruijnNewmanPolymathBarrierRegionZeroFree t0 X y0)
    {t x y : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ t0) (hthalf : t ≤ (1 : ℝ) / 2)
    (hxX : X ≤ x) (hx : x ≤ X + Real.sqrt (1 - y0 ^ 2))
    (hy : Real.sqrt (y0 ^ 2 + 2 * (t0 - t)) ≤ y) :
    deBruijnNewmanH t ((x : ℂ) + (y : ℂ) * I) ≠ 0 := by
  by_cases hyTop : y ≤ Real.sqrt (1 - 2 * t)
  · exact hbarrier t x y ht0 ht hxX hx hy hyTop
  intro hzero
  have hstrip := deBruijnNewmanH_zero_im_sq_le_one_sub_two_mul ht0 hthalf hzero
  have hrad : 0 ≤ 1 - 2 * t := by linarith
  have hyNonneg : 0 ≤ y := (Real.sqrt_nonneg _).trans hy
  have hsqrtLt : Real.sqrt (1 - 2 * t) < y := lt_of_not_ge hyTop
  have hySq : 1 - 2 * t < y ^ 2 := by
    nlinarith [Real.sq_sqrt hrad, Real.sqrt_nonneg (1 - 2 * t)]
  have him : (((x : ℂ) + (y : ℂ) * I).im) = y := by simp
  rw [him] at hstrip
  exact (not_lt_of_ge hstrip) hySq

/-- At a first contact, every divisor zero strictly above the contact height has escaped beyond
the horizontal buffer. -/
theorem deBruijnNewmanPolymath_firstBadWitness_horizontal_escape
    {t0 X y0 t1 x y : ℝ} (hthalf : t0 ≤ (1 : ℝ) / 2)
    (hinit : deBruijnNewmanPolymathInitialRegionZeroFree t0 X y0)
    (haxis : ∀ t y : ℝ, deBruijnNewmanH t ((y : ℂ) * I) ≠ 0)
    (hbarrier : deBruijnNewmanPolymathBarrierRegionZeroFree t0 X y0)
    (hmin : ∀ t ∈ deBruijnNewmanPolymathBadTimes t0 X y0, t1 ≤ t)
    (hp : ((t1, x), y) ∈ deBruijnNewmanPolymathBadWitnesses t0 X y0)
    (p : DeBruijnNewmanHDivisorZeroIndex t1)
    (hpAbove : y < |(deBruijnNewmanHDivisorZeroValue p).im|) :
    X + Real.sqrt (1 - y ^ 2) ≤
      |(deBruijnNewmanHDivisorZeroValue p).re| := by
  rcases mem_deBruijnNewmanPolymathBadWitnesses_iff.mp hp with
    ⟨ht10, ht1t0, _hx0, _hxX, _hy0, _hy1, _hheight, _hzero⟩
  have hcontact := deBruijnNewmanPolymath_firstBadWitness_im_eq_boundary
    hthalf hinit haxis hbarrier hmin hp
  let u : ℝ := |(deBruijnNewmanHDivisorZeroValue p).re|
  let v : ℝ := |(deBruijnNewmanHDivisorZeroValue p).im|
  obtain ⟨q, hqval⟩ :=
    exists_deBruijnNewmanHDivisorZeroIndex_value_eq_abs_cartesian p
  have hqzero := deBruijnNewmanH_divisorZeroIndex₀_val_eq_zero t1 q
  have hzeroAbs : deBruijnNewmanH t1 ((u : ℂ) + (v : ℂ) * I) = 0 := by
    rw [← hqval]
    exact hqzero
  have hu0 : 0 ≤ u := by simp [u]
  have hv0 : 0 ≤ v := by simp [v]
  have hstrip := deBruijnNewmanH_zero_im_sq_le_one_sub_two_mul
    ht10 (ht1t0.trans hthalf) hzeroAbs
  have hvSq : v ^ 2 ≤ 1 := by
    have him : (((u : ℂ) + (v : ℂ) * I).im) = v := by simp
    rw [him] at hstrip
    linarith
  have hv1 : v ≤ 1 := by nlinarith
  have hheight : deBruijnNewmanPolymathBoundaryHeight t0 y0 t1 ≤ v := by
    rw [← hcontact]
    simpa only [v] using hpAbove.le
  have hXu : X < u := by
    by_contra hnot
    have huX : u ≤ X := le_of_not_gt hnot
    have hpAbs : ((t1, u), v) ∈ deBruijnNewmanPolymathBadWitnesses t0 X y0 := by
      rw [mem_deBruijnNewmanPolymathBadWitnesses_iff]
      exact ⟨ht10, ht1t0, hu0, huX, hv0, hv1, hheight, hzeroAbs⟩
    have hvBoundary := deBruijnNewmanPolymath_firstBadWitness_im_eq_boundary
      hthalf hinit haxis hbarrier hmin hpAbs
    have hvEq : v = y := hvBoundary.trans hcontact.symm
    exact (ne_of_gt hpAbove) (by simpa only [v] using hvEq)
  have hbuffer : X + Real.sqrt (1 - y0 ^ 2) < u := by
    by_contra hnot
    have huUpper : u ≤ X + Real.sqrt (1 - y0 ^ 2) := le_of_not_gt hnot
    exact (hbarrier.above ht10 ht1t0 (ht1t0.trans hthalf)
      hXu.le huUpper hheight) hzeroAbs
  have hrad : 0 ≤ y0 ^ 2 + 2 * (t0 - t1) := by
    nlinarith [sq_nonneg y0]
  have hySq : y ^ 2 = y0 ^ 2 + 2 * (t0 - t1) := by
    rw [hcontact, deBruijnNewmanPolymathBoundaryHeight]
    exact Real.sq_sqrt hrad
  have hwidth : Real.sqrt (1 - y ^ 2) ≤ Real.sqrt (1 - y0 ^ 2) := by
    apply Real.sqrt_le_sqrt
    rw [hySq]
    linarith
  calc
    X + Real.sqrt (1 - y ^ 2) ≤ X + Real.sqrt (1 - y0 ^ 2) := by
      linarith
    _ ≤ u := hbuffer.le

section

private abbrev PolymathHasDerivAt (f : ℝ → ℝ) (f' x : ℝ) : Prop :=
  @HasDerivAt ℝ _ ℝ _ RCLike.toInnerProductSpaceReal.toModule _ _ f f' x

theorem hasDerivAt_deBruijnNewmanPolymathBoundaryHeight
    {t0 y0 t : ℝ}
    (hpos : 0 < deBruijnNewmanPolymathBoundaryHeight t0 y0 t) :
    PolymathHasDerivAt (deBruijnNewmanPolymathBoundaryHeight t0 y0)
      (-1 / deBruijnNewmanPolymathBoundaryHeight t0 y0 t) t := by
  unfold deBruijnNewmanPolymathBoundaryHeight at hpos ⊢
  let q : ℝ → ℝ := fun s ↦ y0 ^ 2 + 2 * (t0 - s)
  have hq : PolymathHasDerivAt q (-2) t := by
    dsimp only [q]
    have hsub : PolymathHasDerivAt (fun s : ℝ ↦ t0 - s) (-1) t := by
      have hraw := (hasDerivAt_const (x := t) (c := t0)).sub (hasDerivAt_id t)
      have hraw' := hraw.congr_deriv (by ring : (0 : ℝ) - 1 = -1)
      apply hraw'.congr_of_eventuallyEq
      exact Filter.Eventually.of_forall (fun s ↦ by simp)
    have hmul : PolymathHasDerivAt (fun s : ℝ ↦ 2 * (t0 - s)) (-2) t := by
      simpa only [mul_neg, mul_one] using hsub.const_mul 2
    have hraw := (hasDerivAt_const (x := t) (c := y0 ^ 2)).add hmul
    have hraw' := hraw.congr_deriv (by ring : (0 : ℝ) + -2 = -2)
    apply hraw'.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun s ↦ by simp)
  have hqPos : 0 < q t := by
    apply Real.sqrt_pos.1
    simpa only [q, deBruijnNewmanPolymathBoundaryHeight] using hpos
  have hsqrt := hq.sqrt hqPos.ne'
  have hsqrtPos : 0 < Real.sqrt (q t) := Real.sqrt_pos.2 hqPos
  have hderiv : -2 / (2 * Real.sqrt (q t)) = -1 / Real.sqrt (q t) := by
    field_simp [hsqrtPos.ne']
  simpa only [q] using hsqrt.congr_deriv hderiv

private theorem eventually_lt_on_left_of_hasDerivAt_lt
    {f g : ℝ → ℝ} {t f' g' : ℝ}
    (hf : PolymathHasDerivAt f f' t) (hg : PolymathHasDerivAt g g' t)
    (hderiv : f' < g') (hvalue : f t = g t) :
    ∀ᶠ s in 𝓝 t, s < t → g s < f s := by
  have hq : PolymathHasDerivAt (f - g) (f' - g') t := hf.sub hg
  have hslopeWithin : ∀ᶠ s in 𝓝[≠] t, slope (f - g) t s < 0 :=
    hq.tendsto_slope.eventually (Iio_mem_nhds (sub_neg.mpr hderiv))
  have hslope : ∀ᶠ s in 𝓝 t, s ≠ t → slope (f - g) t s < 0 :=
    eventually_nhdsWithin_iff.mp hslopeWithin
  filter_upwards [hslope] with s hs
  intro hst
  have hslopeNeg := hs hst.ne
  rw [slope_def_field] at hslopeNeg
  have hnum : 0 < (f - g) s - (f - g) t := by
    have hmul := (div_lt_iff_of_neg (sub_neg.mpr hst)).mp hslopeNeg
    simpa only [zero_mul] using hmul
  simp only [Pi.sub_apply] at hnum
  rw [hvalue] at hnum
  linarith

/-- The simple-contact branch reduces exactly to the strict imaginary force inequality from
Polymath Proposition 3.3. If that inequality holds, minimality of the bad time is contradicted. -/
theorem deBruijnNewmanPolymath_firstBadWitness_not_simple_of_force_lt
    {t0 X y0 t1 x y : ℝ} (hy0 : 0 < y0) (ht1Pos : 0 < t1)
    (hthalf : t0 ≤ (1 : ℝ) / 2)
    (hmin : ∀ t ∈ deBruijnNewmanPolymathBadTimes t0 X y0, t1 ≤ t)
    (hp : ((t1, x), y) ∈ deBruijnNewmanPolymathBadWitnesses t0 X y0)
    (hxInterior : x ∈ Ioo 0 X)
    (hcontact : y = deBruijnNewmanPolymathBoundaryHeight t0 y0 t1)
    (hforce :
      (2 * deBruijnNewmanRegularizedZeroForce t1 ((x : ℂ) + (y : ℂ) * I)).im <
        -1 / deBruijnNewmanPolymathBoundaryHeight t0 y0 t1) :
    deriv (deBruijnNewmanH t1) ((x : ℂ) + (y : ℂ) * I) = 0 := by
  rw [mem_deBruijnNewmanPolymathBadWitnesses_iff] at hp
  rcases hp with ⟨ht10, ht1t0, _hx0, _hxX, _hyNonneg, hy1, _hheight, hzero⟩
  by_contra hsimple
  let z0 : ℂ := (x : ℂ) + (y : ℂ) * I
  obtain ⟨z, hzAnchor, hzTend, hzDeriv, hzZero, _hzUnique⟩ :=
    exists_deBruijnNewman_localComplexSimpleZeroPath hzero hsimple
  have hYPos : 0 < deBruijnNewmanPolymathBoundaryHeight t0 y0 t1 := by
    have hrad : 0 < y0 ^ 2 + 2 * (t0 - t1) := by
      nlinarith [sq_pos_of_pos hy0]
    simpa only [deBruijnNewmanPolymathBoundaryHeight] using Real.sqrt_pos.2 hrad
  have hYDeriv := hasDerivAt_deBruijnNewmanPolymathBoundaryHeight hYPos
  have hzImDeriv : PolymathHasDerivAt (fun t ↦ (z t).im)
      (2 * deBruijnNewmanRegularizedZeroForce t1 z0).im t1 := by
    have hcomp := Complex.imCLM.hasFDerivAt.comp t1 hzDeriv.hasFDerivAt
    simpa [Function.comp_def, Complex.imCLM_apply, ContinuousLinearMap.comp_apply,
      smul_eq_mul, z0] using hcomp.hasDerivAt
  have hzImAnchor : (z t1).im =
      deBruijnNewmanPolymathBoundaryHeight t0 y0 t1 := by
    rw [hzAnchor]
    simp [hcontact]
  have habove : ∀ᶠ t in 𝓝 t1, t < t1 →
      deBruijnNewmanPolymathBoundaryHeight t0 y0 t < (z t).im :=
    eventually_lt_on_left_of_hasDerivAt_lt hzImDeriv hYDeriv hforce hzImAnchor
  let U : Set ℂ := {w | 0 < w.re ∧ w.re < X ∧ w.im < 1}
  have hUOpen : IsOpen U := by
    simpa only [U, setOf_and] using
      (isOpen_lt continuous_const Complex.continuous_re).inter
        ((isOpen_lt Complex.continuous_re continuous_const).inter
          (isOpen_lt Complex.continuous_im continuous_const))
  have hyOne : y < 1 := by
    have hstrip := deBruijnNewmanH_zero_im_sq_le_one_sub_two_mul
      ht10 (ht1t0.trans hthalf) hzero
    have him : (((x : ℂ) + (y : ℂ) * I).im) = y := by simp
    rw [him] at hstrip
    have hyPos : 0 < y := by rw [hcontact]; exact hYPos
    nlinarith [sq_nonneg (y - 1)]
  have hz0U : z0 ∈ U := by
    simpa [z0, U] using ⟨hxInterior.1, hxInterior.2, hyOne⟩
  have hzEventuallyU : ∀ᶠ t in 𝓝 t1, z t ∈ U :=
    hzTend.eventually (hUOpen.mem_nhds hz0U)
  have hevent : ∀ᶠ t in 𝓝 t1,
      0 < t ∧ z t ∈ U ∧ deBruijnNewmanH t (z t) = 0 ∧
        (t < t1 → deBruijnNewmanPolymathBoundaryHeight t0 y0 t < (z t).im) := by
    filter_upwards [Ioi_mem_nhds ht1Pos, hzEventuallyU,
      hzZero, habove] with t ht hzU hzeroT haboveT
    exact ⟨ht, hzU, hzeroT, haboveT⟩
  obtain ⟨t, htt1, ht, hzU, hzeroT, haboveT⟩ := hevent.exists_lt
  have htLe : t ≤ t0 := (le_of_lt htt1).trans ht1t0
  have hzPoint : ((z t).re : ℂ) + ((z t).im : ℂ) * I = z t := by
    apply Complex.ext <;> simp
  have htWitness : ((t, (z t).re), (z t).im) ∈
      deBruijnNewmanPolymathBadWitnesses t0 X y0 := by
    rw [mem_deBruijnNewmanPolymathBadWitnesses_iff]
    have haboveT' := haboveT htt1
    exact ⟨ht.le, htLe, hzU.1.le, hzU.2.1.le,
      (Real.sqrt_nonneg _).trans haboveT'.le, hzU.2.2.le, haboveT'.le,
      by simpa only [hzPoint] using hzeroT⟩
  have htBad : t ∈ deBruijnNewmanPolymathBadTimes t0 X y0 :=
    ⟨((t, (z t).re), (z t).im), htWitness, rfl⟩
  exact (not_lt_of_ge (hmin t htBad)) htt1

/-- The three Polymath region certificates imply the strict force inequality at a simple first
contact. -/
theorem deBruijnNewmanPolymath_firstBadWitness_force_lt_of_simple_contact
    {t0 X y0 t1 x y : ℝ} (hy0 : 0 < y0)
    (hthalf : t0 ≤ (1 : ℝ) / 2)
    (hinit : deBruijnNewmanPolymathInitialRegionZeroFree t0 X y0)
    (haxis : ∀ t y : ℝ, deBruijnNewmanH t ((y : ℂ) * I) ≠ 0)
    (hbarrier : deBruijnNewmanPolymathBarrierRegionZeroFree t0 X y0)
    (hmin : ∀ t ∈ deBruijnNewmanPolymathBadTimes t0 X y0, t1 ≤ t)
    (hp : ((t1, x), y) ∈ deBruijnNewmanPolymathBadWitnesses t0 X y0)
    (hsimple : deriv (deBruijnNewmanH t1) ((x : ℂ) + (y : ℂ) * I) ≠ 0) :
    (2 * deBruijnNewmanRegularizedZeroForce t1
      ((x : ℂ) + (y : ℂ) * I)).im < -1 / y := by
  rcases mem_deBruijnNewmanPolymathBadWitnesses_iff.mp hp with
    ⟨ht10, ht1t0, _hx0, _hxX, _hyNonneg, hy1, _hheight, hzero⟩
  have hxInterior :=
    deBruijnNewmanPolymathBadWitness_re_mem_Ioo hthalf haxis hbarrier hp
  have hcontact := deBruijnNewmanPolymath_firstBadWitness_im_eq_boundary
    hthalf hinit haxis hbarrier hmin hp
  have hrad : 0 < y0 ^ 2 + 2 * (t0 - t1) := by
    nlinarith [sq_pos_of_pos hy0]
  have hboundaryPos :
      0 < deBruijnNewmanPolymathBoundaryHeight t0 y0 t1 := by
    simpa only [deBruijnNewmanPolymathBoundaryHeight] using Real.sqrt_pos.2 hrad
  have hyPos : 0 < y := by rw [hcontact]; exact hboundaryPos
  apply deBruijnNewmanRegularizedZeroForce_im_lt_of_simple_contact_escape
    ht10 (ht1t0.trans hthalf) hxInterior.1 hxInterior.2.le hyPos hy1 hzero hsimple
  intro p hpAbove
  exact deBruijnNewmanPolymath_firstBadWitness_horizontal_escape
    hthalf hinit haxis hbarrier hmin hp p hpAbove

/-- A first contact satisfying the three Polymath region certificates cannot be simple. -/
theorem deBruijnNewmanPolymath_firstBadWitness_not_simple
    {t0 X y0 t1 x y : ℝ} (hy0 : 0 < y0)
    (hthalf : t0 ≤ (1 : ℝ) / 2)
    (hinit : deBruijnNewmanPolymathInitialRegionZeroFree t0 X y0)
    (haxis : ∀ t y : ℝ, deBruijnNewmanH t ((y : ℂ) * I) ≠ 0)
    (hbarrier : deBruijnNewmanPolymathBarrierRegionZeroFree t0 X y0)
    (hmin : ∀ t ∈ deBruijnNewmanPolymathBadTimes t0 X y0, t1 ≤ t)
    (hp : ((t1, x), y) ∈ deBruijnNewmanPolymathBadWitnesses t0 X y0) :
    deriv (deBruijnNewmanH t1) ((x : ℂ) + (y : ℂ) * I) = 0 := by
  have ht1Bad : t1 ∈ deBruijnNewmanPolymathBadTimes t0 X y0 :=
    ⟨((t1, x), y), hp, rfl⟩
  have ht1Pos := deBruijnNewmanPolymathBadTime_pos_of_initial hinit ht1Bad
  have hxInterior :=
    deBruijnNewmanPolymathBadWitness_re_mem_Ioo hthalf haxis hbarrier hp
  have hcontact := deBruijnNewmanPolymath_firstBadWitness_im_eq_boundary
    hthalf hinit haxis hbarrier hmin hp
  by_contra hsimple
  have hforce := deBruijnNewmanPolymath_firstBadWitness_force_lt_of_simple_contact
    hy0 hthalf hinit haxis hbarrier hmin hp hsimple
  have hforceBoundary :
      (2 * deBruijnNewmanRegularizedZeroForce t1
        ((x : ℂ) + (y : ℂ) * I)).im <
          -1 / deBruijnNewmanPolymathBoundaryHeight t0 y0 t1 := by
    simpa only [hcontact] using hforce
  exact hsimple (deBruijnNewmanPolymath_firstBadWitness_not_simple_of_force_lt
    hy0 ht1Pos hthalf hmin hp hxInterior hcontact hforceBoundary)

/-- The weak consequence of backward Hermite splitting needed at a repeated first contact. The
square-root displacement from the source theorem dominates every fixed linear speed. -/
def deBruijnNewmanHasBackwardUpperLinearEscape (t : ℝ) (z : ℂ) : Prop :=
  ∀ C : ℝ, 0 < C → ∀ U ∈ 𝓝 z,
    ∀ᶠ s in 𝓝[<] t,
      ∃ w ∈ U, deBruijnNewmanH s w = 0 ∧ z.im + C * (t - s) < w.im

/-- A first-contact zero cannot have the backward upper-escape property supplied by repeated-zero
Hermite splitting. This closes the full topological consumer of the repeated branch. -/
theorem deBruijnNewmanPolymath_firstBadWitness_not_backwardUpperLinearEscape
    {t0 X y0 t1 x y : ℝ} (hy0 : 0 < y0) (ht1Pos : 0 < t1)
    (hthalf : t0 ≤ (1 : ℝ) / 2)
    (hmin : ∀ t ∈ deBruijnNewmanPolymathBadTimes t0 X y0, t1 ≤ t)
    (hp : ((t1, x), y) ∈ deBruijnNewmanPolymathBadWitnesses t0 X y0)
    (hxInterior : x ∈ Ioo 0 X)
    (hcontact : y = deBruijnNewmanPolymathBoundaryHeight t0 y0 t1) :
    ¬deBruijnNewmanHasBackwardUpperLinearEscape t1 ((x : ℂ) + (y : ℂ) * I) := by
  rw [mem_deBruijnNewmanPolymathBadWitnesses_iff] at hp
  rcases hp with ⟨ht10, ht1t0, _hx0, _hxX, _hyNonneg, _hy1, _hheight, hzero⟩
  intro hescape
  let z0 : ℂ := (x : ℂ) + (y : ℂ) * I
  have hYPos : 0 < deBruijnNewmanPolymathBoundaryHeight t0 y0 t1 := by
    have hrad : 0 < y0 ^ 2 + 2 * (t0 - t1) := by
      nlinarith [sq_pos_of_pos hy0]
    simpa only [deBruijnNewmanPolymathBoundaryHeight] using Real.sqrt_pos.2 hrad
  let C : ℝ := 2 / deBruijnNewmanPolymathBoundaryHeight t0 y0 t1
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  let line : ℝ → ℝ := fun s ↦ y + C * (t1 - s)
  have hsub : PolymathHasDerivAt (fun s : ℝ ↦ t1 - s) (-1) t1 := by
    have hraw := (hasDerivAt_const (x := t1) (c := t1)).sub (hasDerivAt_id t1)
    have hraw' := hraw.congr_deriv (by ring : (0 : ℝ) - 1 = -1)
    apply hraw'.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun s ↦ by simp)
  have hscaled : PolymathHasDerivAt (fun s : ℝ ↦ C * (t1 - s)) (-C) t1 := by
    simpa only [mul_neg, mul_one] using hsub.const_mul C
  have hline : PolymathHasDerivAt line (-C) t1 := by
    have hraw := (hasDerivAt_const (x := t1) (c := y)).add hscaled
    have hraw' := hraw.congr_deriv (by ring : (0 : ℝ) + -C = -C)
    apply hraw'.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun s ↦ by simp [line])
  have hYDeriv := hasDerivAt_deBruijnNewmanPolymathBoundaryHeight hYPos
  have hderiv : -C <
      -1 / deBruijnNewmanPolymathBoundaryHeight t0 y0 t1 := by
    dsimp only [C]
    have hInv : 0 < 1 / deBruijnNewmanPolymathBoundaryHeight t0 y0 t1 := by positivity
    rw [show 2 / deBruijnNewmanPolymathBoundaryHeight t0 y0 t1 =
      2 * (1 / deBruijnNewmanPolymathBoundaryHeight t0 y0 t1) by ring]
    rw [show -1 / deBruijnNewmanPolymathBoundaryHeight t0 y0 t1 =
      -(1 / deBruijnNewmanPolymathBoundaryHeight t0 y0 t1) by ring]
    linarith
  have hlineValue : line t1 = deBruijnNewmanPolymathBoundaryHeight t0 y0 t1 := by
    simp only [line, sub_self, mul_zero, add_zero, hcontact]
  have hlineAbove : ∀ᶠ s in 𝓝 t1, s < t1 →
      deBruijnNewmanPolymathBoundaryHeight t0 y0 s < line s :=
    eventually_lt_on_left_of_hasDerivAt_lt hline hYDeriv hderiv hlineValue
  have hyOne : y < 1 := by
    have hstrip := deBruijnNewmanH_zero_im_sq_le_one_sub_two_mul
      ht10 (ht1t0.trans hthalf) hzero
    have him : (((x : ℂ) + (y : ℂ) * I).im) = y := by simp
    rw [him] at hstrip
    have hyPos : 0 < y := by rw [hcontact]; exact hYPos
    nlinarith [sq_nonneg (y - 1)]
  let U : Set ℂ := {w | 0 < w.re ∧ w.re < X ∧ w.im < 1}
  have hUOpen : IsOpen U := by
    simpa only [U, setOf_and] using
      (isOpen_lt continuous_const Complex.continuous_re).inter
        ((isOpen_lt Complex.continuous_re continuous_const).inter
          (isOpen_lt Complex.continuous_im continuous_const))
  have hz0U : z0 ∈ U := by
    simpa [z0, U] using ⟨hxInterior.1, hxInterior.2, hyOne⟩
  have hsplit := hescape C hC U (hUOpen.mem_nhds hz0U)
  have hlineRaw : ∀ᶠ s in 𝓝[<] t1, s < t1 →
      deBruijnNewmanPolymathBoundaryHeight t0 y0 s < line s :=
    hlineAbove.filter_mono inf_le_left
  have hlineWithin : ∀ᶠ s in 𝓝[<] t1,
      deBruijnNewmanPolymathBoundaryHeight t0 y0 s < line s := by
    filter_upwards [hlineRaw, eventually_mem_nhdsWithin] with
      s hs hst
    exact hs hst
  have hposN : ∀ᶠ s in 𝓝 t1, 0 < s := Ioi_mem_nhds ht1Pos
  have hposWithin : ∀ᶠ s in 𝓝[<] t1, 0 < s :=
    hposN.filter_mono inf_le_left
  have hevent : ∀ᶠ s in 𝓝[<] t1,
      s < t1 ∧ 0 < s ∧
        deBruijnNewmanPolymathBoundaryHeight t0 y0 s < line s ∧
        ∃ w ∈ U, deBruijnNewmanH s w = 0 ∧ z0.im + C * (t1 - s) < w.im := by
    filter_upwards [eventually_mem_nhdsWithin, hposWithin, hlineWithin, hsplit] with
      s hst hs hlineS hsplitS
    exact ⟨hst, hs, hlineS, hsplitS⟩
  obtain ⟨s, hst1, hsPos, hlineS, w, hwU, hwZero, hwEscape⟩ := hevent.exists
  have hlineEq : line s = z0.im + C * (t1 - s) := by
    simp [line, z0]
  have hYw : deBruijnNewmanPolymathBoundaryHeight t0 y0 s < w.im := by
    rw [hlineEq] at hlineS
    exact hlineS.trans hwEscape
  have hsLe : s ≤ t0 := (le_of_lt hst1).trans ht1t0
  have hwPoint : (w.re : ℂ) + (w.im : ℂ) * I = w := by
    apply Complex.ext <;> simp
  have hsWitness : ((s, w.re), w.im) ∈
      deBruijnNewmanPolymathBadWitnesses t0 X y0 := by
    rw [mem_deBruijnNewmanPolymathBadWitnesses_iff]
    exact ⟨hsPos.le, hsLe, hwU.1.le, hwU.2.1.le,
      (Real.sqrt_nonneg _).trans hYw.le, hwU.2.2.le, hYw.le,
      by simpa only [hwPoint] using hwZero⟩
  have hsBad : s ∈ deBruijnNewmanPolymathBadTimes t0 X y0 :=
    ⟨((s, w.re), w.im), hsWitness, rfl⟩
  exact (not_lt_of_ge (hmin s hsBad)) hst1

/-- The exact obstruction pair remaining at a first contact after the force inequality is supplied:
the contact is repeated, but minimality forbids the backward escape predicted by Hermite
splitting. -/
theorem deBruijnNewmanPolymath_firstBadWitness_repeated_obstruction_of_force_lt
    {t0 X y0 t1 x y : ℝ} (hy0 : 0 < y0) (hthalf : t0 ≤ (1 : ℝ) / 2)
    (hinit : deBruijnNewmanPolymathInitialRegionZeroFree t0 X y0)
    (haxis : ∀ t y : ℝ, deBruijnNewmanH t ((y : ℂ) * I) ≠ 0)
    (hbarrier : deBruijnNewmanPolymathBarrierRegionZeroFree t0 X y0)
    (hmin : ∀ t ∈ deBruijnNewmanPolymathBadTimes t0 X y0, t1 ≤ t)
    (hp : ((t1, x), y) ∈ deBruijnNewmanPolymathBadWitnesses t0 X y0)
    (hforce :
      (2 * deBruijnNewmanRegularizedZeroForce t1 ((x : ℂ) + (y : ℂ) * I)).im <
        -1 / deBruijnNewmanPolymathBoundaryHeight t0 y0 t1) :
    deriv (deBruijnNewmanH t1) ((x : ℂ) + (y : ℂ) * I) = 0 ∧
      ¬deBruijnNewmanHasBackwardUpperLinearEscape t1 ((x : ℂ) + (y : ℂ) * I) := by
  have ht1Bad : t1 ∈ deBruijnNewmanPolymathBadTimes t0 X y0 :=
    ⟨((t1, x), y), hp, rfl⟩
  have ht1Pos := deBruijnNewmanPolymathBadTime_pos_of_initial hinit ht1Bad
  have hxInterior :=
    deBruijnNewmanPolymathBadWitness_re_mem_Ioo hthalf haxis hbarrier hp
  have hcontact := deBruijnNewmanPolymath_firstBadWitness_im_eq_boundary
    hthalf hinit haxis hbarrier hmin hp
  exact ⟨deBruijnNewmanPolymath_firstBadWitness_not_simple_of_force_lt
      hy0 ht1Pos hthalf hmin hp hxInterior hcontact hforce,
    deBruijnNewmanPolymath_firstBadWitness_not_backwardUpperLinearEscape
      hy0 ht1Pos hthalf hmin hp hxInterior hcontact⟩

end

/-- A strict time-`t` canopy feeds directly into the compiled arbitrary-base strip theorem. -/
theorem deBruijnNewmanAllZerosReal_add_half_sq_of_im_abs_lt
    {t y : ℝ} (hy : 0 < y)
    (hcanopy : ∀ z : ℂ, deBruijnNewmanH t z = 0 → |z.im| < y) :
    deBruijnNewmanAllZerosReal (t + y ^ 2 / 2) := by
  apply deBruijnNewmanAllZerosReal_add_half_sq hy.le
  intro z hz
  rcases abs_lt.mp (hcanopy z hz) with ⟨hlower, hupper⟩
  have hprod : 0 < (y - z.im) * (y + z.im) :=
    mul_pos (sub_pos.mpr hupper) (by linarith)
  nlinarith

/-- Exact arithmetic for the second row of Polymath Table 1. -/
theorem deBruijnNewmanAllZerosReal_one_fifth_of_polymath_table_endpoint
    (hall : deBruijnNewmanAllZerosReal
      ((93 : ℝ) / 500 + ((16733 : ℝ) / 100000) ^ 2 / 2)) :
    deBruijnNewmanAllZerosReal ((1 : ℝ) / 5) := by
  apply deBruijnNewmanAllZerosReal_mono (t :=
    (93 : ℝ) / 500 + ((16733 : ℝ) / 100000) ^ 2 / 2) (tau := (1 : ℝ) / 5)
  · norm_num
  · exact hall

end

end LeanLab.Riemann
