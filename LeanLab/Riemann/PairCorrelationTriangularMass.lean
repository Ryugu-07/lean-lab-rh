import LeanLab.Riemann.PairCorrelationHorizontalMultiplicity

set_option linter.style.header false

/-!
# Triangular pair mass and horizontal multiplicity

This module formalizes the finite ordered-pair identity behind the
Gallagher--Mueller short-interval method. It contains no pair-correlation asymptotic.
-/

open Complex MeasureTheory Set
open scoped BigOperators

namespace LeanLab.Riemann

noncomputable section

section FinitePopulation

variable {ι : Type*} [Fintype ι]

/-- Directed ordinate gap from the first index to the second. -/
def pairCorrelationGap (gamma : ι → ℝ) (i j : ι) : ℝ :=
  gamma j - gamma i

/-- Ordered pairs with a strictly positive directed gap at most `u`. -/
def positiveGapPairCount (gamma : ι → ℝ) (u : ℝ) : ℕ :=
  ∑ i, ∑ j, if 0 < pairCorrelationGap gamma i j ∧
      pairCorrelationGap gamma i j ≤ u then 1 else 0

/-- Ordered pairs on the same horizontal line. -/
def equalOrdinatePairCount (gamma : ι → ℝ) : ℕ :=
  ∑ i, ∑ j, if pairCorrelationGap gamma i j = 0 then 1 else 0

/-- Source triangular mass, extended by zero outside `|gap| ≤ U`. -/
def triangularPairMass (gamma : ι → ℝ) (U : ℝ) : ℝ :=
  ∑ i, ∑ j, max 0 (U - |pairCorrelationGap gamma i j|)

/-- Contribution from strictly positive directed gaps. -/
def positiveGapMass (gamma : ι → ℝ) (U : ℝ) : ℝ :=
  ∑ i, ∑ j, if 0 < pairCorrelationGap gamma i j then
    max 0 (U - pairCorrelationGap gamma i j) else 0

/-- The max-extension is exactly the source sum filtered by `|gap| <= U`. -/
theorem triangularPairMass_eq_filtered
    (gamma : ι → ℝ) (U : ℝ) :
    triangularPairMass gamma U =
      Finset.univ.sum fun i =>
        (Finset.univ.filter
          fun j => |pairCorrelationGap gamma i j| ≤ U).sum fun j =>
            U - |pairCorrelationGap gamma i j| := by
  unfold triangularPairMass
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _hj
  by_cases hgap : |pairCorrelationGap gamma i j| ≤ U
  · rw [if_pos hgap, max_eq_right (sub_nonneg.mpr hgap)]
  · rw [if_neg hgap, max_eq_left (sub_nonpos.mpr (le_of_not_ge hgap))]

private theorem intervalIntegrable_step_ge (d U : ℝ) :
    IntervalIntegrable (fun u : ℝ => if d ≤ u then (1 : ℝ) else 0)
      volume 0 U := by
  have hconst :
      @IntegrableOn ℝ ℝ Real.measurableSpace _ _ (fun _u : ℝ => (1 : ℝ))
        (uIcc 0 U) volume :=
    (intervalIntegrable_iff').mp (intervalIntegrable_const (μ := volume))
  have hind := hconst.indicator (t := Ici d) measurableSet_Ici
  rw [intervalIntegrable_iff']
  convert hind using 1
  funext u
  by_cases hdu : d ≤ u <;> simp [Set.indicator, hdu]

private theorem integral_step_ge_eq
    {d U : ℝ} (hd : 0 < d) (hdU : d ≤ U) :
    (∫ u : ℝ in 0..U, if d ≤ u then (1 : ℝ) else 0) = U - d := by
  rw [intervalIntegral.integral_of_le (hd.le.trans hdU)]
  have hfun :
      (fun u : ℝ => if d ≤ u then (1 : ℝ) else 0) =
        (Ici d).indicator (fun _ => (1 : ℝ)) := by
    funext u
    simp only [Set.indicator, Set.mem_Ici]
  rw [hfun, MeasureTheory.integral_indicator measurableSet_Ici,
    MeasureTheory.setIntegral_const]
  have hinter : Ici d ∩ Ioc 0 U = Icc d U := by
    ext u
    simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_Icc]
    constructor
    · rintro ⟨hdu, _hu0, huU⟩
      exact ⟨hdu, huU⟩
    · rintro ⟨hdu, huU⟩
      exact ⟨hdu, hd.trans_le hdu, huU⟩
  simp [Measure.real, Measure.restrict_apply measurableSet_Ici, hinter,
    Real.volume_Icc, hdU]

private theorem integral_step_ge_eq_zero_of_not_le
    {d U : ℝ} (hU : 0 ≤ U) (hdU : ¬d ≤ U) :
    (∫ u : ℝ in 0..U, if d ≤ u then (1 : ℝ) else 0) = 0 := by
  calc
    (∫ u : ℝ in 0..U, if d ≤ u then (1 : ℝ) else 0) =
        ∫ _u : ℝ in 0..U, 0 := by
      apply intervalIntegral.integral_congr
      intro u hu
      have hu' : u ∈ Icc 0 U := by
        simpa [uIcc_of_le hU] using hu
      have hnot : ¬d ≤ u :=
        not_le.mpr (lt_of_le_of_lt hu'.2 (lt_of_not_ge hdU))
      simp [hnot]
    _ = 0 := by simp

private theorem integral_positiveGapStep_eq
    {d U : ℝ} (hU : 0 ≤ U) :
    (∫ u : ℝ in 0..U, if 0 < d ∧ d ≤ u then (1 : ℝ) else 0) =
      if 0 < d then max 0 (U - d) else 0 := by
  by_cases hd : 0 < d
  · simp only [hd, true_and, ↓reduceIte]
    by_cases hdU : d ≤ U
    · rw [integral_step_ge_eq hd hdU, max_eq_right (sub_nonneg.mpr hdU)]
    · rw [integral_step_ge_eq_zero_of_not_le hU hdU,
        max_eq_left (sub_nonpos.mpr (lt_of_not_ge hdU).le)]
  · simp [hd]

private theorem intervalIntegrable_positiveGapStep (d U : ℝ) :
    IntervalIntegrable
      (fun u : ℝ => if 0 < d ∧ d ≤ u then (1 : ℝ) else 0)
      volume 0 U := by
  by_cases hd : 0 < d
  · simpa only [hd, true_and] using intervalIntegrable_step_ge d U
  · simp [hd]

/-- Integrating the positive directed-gap count recovers the positive triangular mass. -/
theorem integral_positiveGapPairCount_eq_positiveGapMass
    (gamma : ι → ℝ) {U : ℝ} (hU : 0 ≤ U) :
    (∫ u : ℝ in 0..U, (positiveGapPairCount gamma u : ℝ)) =
      positiveGapMass gamma U := by
  calc
    (∫ u : ℝ in 0..U, (positiveGapPairCount gamma u : ℝ)) =
        ∫ u : ℝ in 0..U, ∑ i, ∑ j,
          if 0 < pairCorrelationGap gamma i j ∧
              pairCorrelationGap gamma i j ≤ u then (1 : ℝ) else 0 := by
      congr 1
      funext u
      simp [positiveGapPairCount]
    _ = ∑ i, ∫ u : ℝ in 0..U, ∑ j,
          if 0 < pairCorrelationGap gamma i j ∧
              pairCorrelationGap gamma i j ≤ u then (1 : ℝ) else 0 := by
      rw [intervalIntegral.integral_finsetSum]
      intro i _hi
      have heq :
          (fun u : ℝ => ∑ j,
            if 0 < pairCorrelationGap gamma i j ∧
                pairCorrelationGap gamma i j ≤ u then (1 : ℝ) else 0) =
            ∑ j, fun u : ℝ =>
              if 0 < pairCorrelationGap gamma i j ∧
                  pairCorrelationGap gamma i j ≤ u then (1 : ℝ) else 0 := by
        funext u
        exact (Finset.sum_apply u Finset.univ
          (fun (j : ι) (u : ℝ) =>
            if 0 < pairCorrelationGap gamma i j ∧
                pairCorrelationGap gamma i j ≤ u then (1 : ℝ) else 0)).symm
      rw [heq]
      exact IntervalIntegrable.sum Finset.univ fun j _hj =>
        intervalIntegrable_positiveGapStep (pairCorrelationGap gamma i j) U
    _ = ∑ i, ∑ j, ∫ u : ℝ in 0..U,
          if 0 < pairCorrelationGap gamma i j ∧
              pairCorrelationGap gamma i j ≤ u then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [intervalIntegral.integral_finsetSum]
      intro j _hj
      exact intervalIntegrable_positiveGapStep (pairCorrelationGap gamma i j) U
    _ = positiveGapMass gamma U := by
      simp_rw [integral_positiveGapStep_eq hU]
      rfl

private theorem triangularGap_decomposition {d U : ℝ} (hU : 0 ≤ U) :
    max 0 (U - |d|) =
      (if d = 0 then U else 0) +
      (if 0 < d then max 0 (U - d) else 0) +
      (if 0 < -d then max 0 (U - (-d)) else 0) := by
  rcases lt_trichotomy d 0 with hd | rfl | hd
  · have hnd : ¬0 < d := not_lt.mpr hd.le
    have hneg : 0 < -d := neg_pos.mpr hd
    simp [hd.ne, hnd, hneg, abs_of_neg hd]
  · simp [max_eq_right hU]
  · have hdz : d ≠ 0 := hd.ne'
    have hnneg : ¬0 < -d := not_lt.mpr (neg_nonpos.mpr hd.le)
    simp [hdz, hd, hnneg, abs_of_pos hd]

private theorem equalGapMass_eq
    (gamma : ι → ℝ) (U : ℝ) :
    (∑ i, ∑ j, if pairCorrelationGap gamma i j = 0 then U else 0) =
      U * (equalOrdinatePairCount gamma : ℝ) := by
  calc
    (∑ i, ∑ j, if pairCorrelationGap gamma i j = 0 then U else 0) =
        ∑ i, ∑ j, U *
          (if pairCorrelationGap gamma i j = 0 then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      by_cases hgap : pairCorrelationGap gamma i j = 0 <;> simp [hgap]
    _ = ∑ i, U * ∑ j,
          (if pairCorrelationGap gamma i j = 0 then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact (Finset.mul_sum Finset.univ
        (fun j => if pairCorrelationGap gamma i j = 0 then (1 : ℝ) else 0) U).symm
    _ = U * ∑ i, ∑ j,
          (if pairCorrelationGap gamma i j = 0 then (1 : ℝ) else 0) := by
      exact (Finset.mul_sum Finset.univ
        (fun i => ∑ j,
          if pairCorrelationGap gamma i j = 0 then (1 : ℝ) else 0) U).symm
    _ = U * (equalOrdinatePairCount gamma : ℝ) := by
      congr 1
      simp [equalOrdinatePairCount]

private theorem negatedPositiveGapMass_eq
    (gamma : ι → ℝ) (U : ℝ) :
    (∑ i, ∑ j, if 0 < -pairCorrelationGap gamma i j then
        max 0 (U - (-pairCorrelationGap gamma i j)) else 0) =
      positiveGapMass gamma U := by
  unfold positiveGapMass
  calc
    (∑ i, ∑ j, if 0 < -pairCorrelationGap gamma i j then
        max 0 (U - (-pairCorrelationGap gamma i j)) else 0) =
        ∑ i, ∑ j, if 0 < pairCorrelationGap gamma j i then
          max 0 (U - pairCorrelationGap gamma j i) else 0 := by
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      have hgap :
          -pairCorrelationGap gamma i j = pairCorrelationGap gamma j i := by
        simp [pairCorrelationGap]
      rw [hgap]
    _ = ∑ i, ∑ j, if 0 < pairCorrelationGap gamma i j then
          max 0 (U - pairCorrelationGap gamma i j) else 0 := by
      rw [Finset.sum_comm]

/-- The finite Gallagher--Mueller triangular-mass decomposition. -/
theorem triangularPairMass_eq_equal_add_two_positive
    (gamma : ι → ℝ) {U : ℝ} (hU : 0 ≤ U) :
    triangularPairMass gamma U =
      U * (equalOrdinatePairCount gamma : ℝ) + 2 * positiveGapMass gamma U := by
  unfold triangularPairMass
  simp_rw [triangularGap_decomposition hU, Finset.sum_add_distrib]
  rw [equalGapMass_eq gamma U, negatedPositiveGapMass_eq gamma U]
  change U * (equalOrdinatePairCount gamma : ℝ) +
      positiveGapMass gamma U + positiveGapMass gamma U =
    U * (equalOrdinatePairCount gamma : ℝ) + 2 * positiveGapMass gamma U
  ring

/-- Source identity: full triangular mass is horizontal mass plus the integrated
strictly positive short-gap count. -/
theorem triangularPairMass_eq_equal_add_integral
    (gamma : ι → ℝ) {U : ℝ} (hU : 0 ≤ U) :
    triangularPairMass gamma U =
      U * (equalOrdinatePairCount gamma : ℝ) +
        2 * (∫ u : ℝ in 0..U, (positiveGapPairCount gamma u : ℝ)) := by
  rw [integral_positiveGapPairCount_eq_positiveGapMass gamma hU]
  exact triangularPairMass_eq_equal_add_two_positive gamma hU

/-- Equal ordinate gaps of a complex population are exactly its horizontal ordered pairs. -/
theorem equalOrdinatePairCount_im_eq_horizontalPairCount
    (z : ι → ℂ) :
    equalOrdinatePairCount (fun i => (z i).im) = horizontalPairCount z := by
  simp [equalOrdinatePairCount, pairCorrelationGap, horizontalPairCount,
    horizontalMultiplicity, sub_eq_zero]

/-- Complex-population form of the source identity, exposing horizontal multiplicity. -/
theorem triangularPairMass_im_eq_horizontal_add_integral
    (z : ι → ℂ) {U : ℝ} (hU : 0 ≤ U) :
    triangularPairMass (fun i => (z i).im) U =
      U * (horizontalPairCount z : ℝ) +
        2 * (∫ u : ℝ in 0..U,
          (positiveGapPairCount (fun i => (z i).im) u : ℝ)) := by
  rw [← equalOrdinatePairCount_im_eq_horizontalPairCount z]
  exact triangularPairMass_eq_equal_add_integral (fun i => (z i).im) hU

end FinitePopulation

section ActualZetaZeros

/-- Positive-height zeta-zero ordinates, with analytic multiplicity copies retained. -/
def pccPositiveZetaOrdinate (T : ℝ) :
    PccPositiveZetaZeroIndex T → ℝ :=
  fun p => (pccPositiveZetaZeroValue T p).im

/-- Positive short-gap count for the actual multiplicity-expanded zeta cutoff. -/
def pccPositiveZetaGapPairCount (T u : ℝ) : ℕ :=
  positiveGapPairCount (pccPositiveZetaOrdinate T) u

/-- Triangular pair mass for the actual multiplicity-expanded zeta cutoff. -/
def pccPositiveZetaTriangularPairMass (T U : ℝ) : ℝ :=
  triangularPairMass (pccPositiveZetaOrdinate T) U

/-- Actual-zeta specialization of the Gallagher--Mueller source identity. -/
theorem pccPositiveZeta_triangularPairMass_eq
    (T : ℝ) {U : ℝ} (hU : 0 ≤ U) :
    pccPositiveZetaTriangularPairMass T U =
      U * (pccPositiveZetaHorizontalPairCount T : ℝ) +
        2 * (∫ u : ℝ in 0..U, (pccPositiveZetaGapPairCount T u : ℝ)) := by
  exact triangularPairMass_im_eq_horizontal_add_integral
    (pccPositiveZetaZeroValue T) hU

end ActualZetaZeros

/-- Aggregate finite and actual-zeta certificate fixed by the campaign preregistration. -/
structure PairCorrelationTriangularMassCertificate : Prop where
  filtered :
    ∀ {ι : Type} [Fintype ι] (gamma : ι → ℝ) (U : ℝ),
      triangularPairMass gamma U =
        Finset.univ.sum fun i =>
          (Finset.univ.filter
            fun j => |pairCorrelationGap gamma i j| ≤ U).sum fun j =>
              U - |pairCorrelationGap gamma i j|
  signPartition :
    ∀ {ι : Type} [Fintype ι] (gamma : ι → ℝ)
        {U : ℝ}, 0 ≤ U →
      triangularPairMass gamma U =
        U * (equalOrdinatePairCount gamma : ℝ) + 2 * positiveGapMass gamma U
  layerCake :
    ∀ {ι : Type} [Fintype ι] (gamma : ι → ℝ)
        {U : ℝ}, 0 ≤ U →
      (∫ u : ℝ in 0..U, (positiveGapPairCount gamma u : ℝ)) =
        positiveGapMass gamma U
  finiteSource :
    ∀ {ι : Type} [Fintype ι] (gamma : ι → ℝ)
        {U : ℝ}, 0 ≤ U →
      triangularPairMass gamma U =
        U * (equalOrdinatePairCount gamma : ℝ) +
          2 * (∫ u : ℝ in 0..U, (positiveGapPairCount gamma u : ℝ))
  horizontalBridge :
    ∀ {ι : Type} [Fintype ι] (z : ι → ℂ),
      equalOrdinatePairCount (fun i => (z i).im) = horizontalPairCount z
  actualZeta :
    ∀ (T : ℝ) {U : ℝ}, 0 ≤ U →
      pccPositiveZetaTriangularPairMass T U =
        U * (pccPositiveZetaHorizontalPairCount T : ℝ) +
          2 * (∫ u : ℝ in 0..U, (pccPositiveZetaGapPairCount T u : ℝ))

/-- Complete no-assumption endpoint for the triangular pair-mass campaign. -/
theorem pairCorrelationTriangularMass_endpoint :
    PairCorrelationTriangularMassCertificate where
  filtered := triangularPairMass_eq_filtered
  signPartition := triangularPairMass_eq_equal_add_two_positive
  layerCake := integral_positiveGapPairCount_eq_positiveGapMass
  finiteSource := triangularPairMass_eq_equal_add_integral
  horizontalBridge := equalOrdinatePairCount_im_eq_horizontalPairCount
  actualZeta := pccPositiveZeta_triangularPairMass_eq

end

end LeanLab.Riemann
