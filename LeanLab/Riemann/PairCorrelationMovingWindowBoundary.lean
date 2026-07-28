import LeanLab.Riemann.PairCorrelationTriangularMass

set_option linter.style.header false

/-!
# Exact moving-window boundary in the pair-correlation second moment

This module retains the literal overlap measure at the upper endpoint of the moving window.
The published `O(L^2)` replacement remains valid asymptotically, but its future-point block is
not a termwise triangular-mass identity.
-/

open MeasureTheory Set
open scoped BigOperators

namespace LeanLab.Riemann

noncomputable section

section PairKernel

/-- Indicator that two ordinates are simultaneously visible in the source window `(t,t+U]`. -/
def shortWindowPairIndicator (U x y t : ℝ) : ℝ :=
  if (t < x ∧ x ≤ t + U) ∧ (t < y ∧ y ≤ t + U) then 1 else 0

/-- Exact length of the overlap of the two source windows with the integration interval. -/
def pairWindowOverlap (T U x y : ℝ) : ℝ :=
  max (min T (min x y) - max 0 (max x y - U)) 0

private theorem shortWindowPairIndicator_eq_indicator (U x y : ℝ) :
    shortWindowPairIndicator U x y =
      (Ico (max x y - U) (min x y)).indicator (fun _t : ℝ => (1 : ℝ)) := by
  funext t
  simp only [shortWindowPairIndicator, Set.indicator, mem_Ico]
  by_cases hsource : (t < x ∧ x ≤ t + U) ∧ (t < y ∧ y ≤ t + U)
  · rw [if_pos hsource]
    have hlower : max x y - U ≤ t := by
      rcases hsource with ⟨⟨_htx, hxt⟩, ⟨_hty, hyt⟩⟩
      rcases le_total x y with hxy | hyx
      · rw [max_eq_right hxy]
        linarith
      · rw [max_eq_left hyx]
        linarith
    have hupper : t < min x y := lt_min hsource.1.1 hsource.2.1
    simp [hlower, hupper]
  · rw [if_neg hsource]
    have hnot : ¬(max x y - U ≤ t ∧ t < min x y) := by
      intro h
      have htx : t < x := h.2.trans_le (min_le_left x y)
      have hty : t < y := h.2.trans_le (min_le_right x y)
      have hxt : x ≤ t + U := by
        have hxmax : x ≤ max x y := le_max_left x y
        linarith
      have hyt : y ≤ t + U := by
        have hymax : y ≤ max x y := le_max_right x y
        linarith
      exact hsource ⟨⟨htx, hxt⟩, ⟨hty, hyt⟩⟩
    rw [if_neg hnot]

private theorem intervalIntegrable_shortWindowPairIndicator
    (T U x y : ℝ) :
    IntervalIntegrable (shortWindowPairIndicator U x y) volume 0 T := by
  rw [shortWindowPairIndicator_eq_indicator]
  have hconst :
      @IntegrableOn ℝ ℝ Real.measurableSpace _ _ (fun _t : ℝ => (1 : ℝ))
        (uIcc 0 T) volume :=
    (intervalIntegrable_iff').mp (intervalIntegrable_const (μ := volume))
  rw [intervalIntegrable_iff']
  exact hconst.indicator measurableSet_Ico

/-- A single ordered pair contributes its literal truncated overlap length. -/
theorem integral_shortWindowPairIndicator_eq_pairWindowOverlap
    {T U x y : ℝ} (hT : 0 ≤ T) :
    (∫ t : ℝ in 0..T, shortWindowPairIndicator U x y t) =
      pairWindowOverlap T U x y := by
  rw [intervalIntegral.integral_of_le hT, ← integral_Ico_eq_integral_Ioc,
    shortWindowPairIndicator_eq_indicator,
    setIntegral_indicator measurableSet_Ico, Ico_inter_Ico,
    MeasureTheory.setIntegral_const]
  simp [Real.volume_real_Ico, pairWindowOverlap]

theorem pairWindowOverlap_nonneg (T U x y : ℝ) :
    0 ≤ pairWindowOverlap T U x y := by
  simp [pairWindowOverlap]

theorem pairWindowOverlap_comm (T U x y : ℝ) :
    pairWindowOverlap T U x y = pairWindowOverlap T U y x := by
  simp [pairWindowOverlap, min_comm, max_comm]

theorem pairWindowOverlap_le
    {T U x y : ℝ} (hU : 0 ≤ U) :
    pairWindowOverlap T U x y ≤ U := by
  unfold pairWindowOverlap
  apply max_le
  · have hupper : min T (min x y) ≤ min x y := min_le_right _ _
    have hlower : max x y - U ≤ max 0 (max x y - U) := le_max_right _ _
    have hminmax : min x y ≤ max x y := min_le_max
    linarith
  · exact hU

/-- Away from the lower endpoint, an interior pair has the usual full triangular weight. -/
theorem pairWindowOverlap_eq_triangular_of_interior
    {T U x y : ℝ} (hxLower : U ≤ x) (hyLower : U ≤ y)
    (hxUpper : x ≤ T) (hyUpper : y ≤ T) :
    pairWindowOverlap T U x y = max (U - |y - x|) 0 := by
  rcases le_total x y with hxy | hyx
  · have hmax : max x y = y := max_eq_right hxy
    have hmin : min x y = x := min_eq_left hxy
    have hTmin : min T (min x y) = x := by simp [hmin, hxUpper]
    have hzero : max 0 (max x y - U) = y - U := by
      rw [hmax, max_eq_right]
      linarith
    rw [pairWindowOverlap, hTmin, hzero, abs_of_nonneg (sub_nonneg.mpr hxy)]
    congr 1
    ring
  · have hmax : max x y = x := max_eq_left hyx
    have hmin : min x y = y := min_eq_right hyx
    have hTmin : min T (min x y) = y := by simp [hmin, hyUpper]
    have hzero : max 0 (max x y - U) = x - U := by
      rw [hmax, max_eq_right]
      linarith
    rw [pairWindowOverlap, hTmin, hzero, abs_of_nonpos (sub_nonpos.mpr hyx)]
    congr 1
    ring

/-- A future endpoint point has no literal overlap with `[0,T]`. -/
theorem pairWindowOverlap_futureEndpoint
    {T U : ℝ} (hT : 0 ≤ T) (hU : 0 ≤ U) :
    pairWindowOverlap T U (T + U) (T + U) = 0 := by
  have hTU : T ≤ T + U := by linarith
  have hsub : T + U - U = T := by ring
  simp [pairWindowOverlap, hTU, hsub, max_eq_right hT]

/-- The same future endpoint point would receive full self-weight from the untruncated kernel. -/
theorem futureEndpoint_triangularSelfWeight
    {T U : ℝ} (hU : 0 ≤ U) :
    max (U - |(T + U) - (T + U)|) 0 = U := by
  simp [max_eq_left hU]

/-- The future block cannot be replaced termwise by full triangular weights. -/
theorem futureEndpoint_overlap_ne_triangular
    {T U : ℝ} (hT : 0 ≤ T) (hU : 0 < U) :
    pairWindowOverlap T U (T + U) (T + U) ≠
      max (U - |(T + U) - (T + U)|) 0 := by
  rw [pairWindowOverlap_futureEndpoint hT hU.le,
    futureEndpoint_triangularSelfWeight hU.le]
  exact hU.ne'.symm

end PairKernel

section FinitePopulation

variable {ι : Type*} [Fintype ι]

/-- Number of multiplicity copies visible in `(t,t+U]`. -/
def shortWindowCount (gamma : ι → ℝ) (U t : ℝ) : ℕ :=
  ∑ i, if t < gamma i ∧ gamma i ≤ t + U then 1 else 0

/-- Source second moment of the moving zero count. -/
def shortWindowSecondMoment (gamma : ι → ℝ) (T U : ℝ) : ℝ :=
  ∫ t : ℝ in 0..T, (shortWindowCount gamma U t : ℝ) ^ 2

/-- Interior triangular mass, using only copies whose ordinates are at most `T`. -/
def interiorTriangularPairMass (gamma : ι → ℝ) (T U : ℝ) : ℝ :=
  ∑ i, ∑ j, if gamma i ≤ T ∧ gamma j ≤ T then
    max (U - |gamma j - gamma i|) 0 else 0

/-- Literal overlap left after removing the interior-interior block. -/
def topBoundaryRemainder (gamma : ι → ℝ) (T U : ℝ) : ℝ :=
  ∑ i, ∑ j, if gamma i ≤ T ∧ gamma j ≤ T then 0
    else pairWindowOverlap T U (gamma i) (gamma j)

/-- Number of copies in the only band capable of contributing to the upper remainder. -/
def topBoundaryIndexCount (gamma : ι → ℝ) (T U : ℝ) : ℕ :=
  (Finset.univ.filter fun i => T - U < gamma i ∧ gamma i ≤ T + U).card

private theorem shortWindowCount_cast_eq_sum (gamma : ι → ℝ) (U t : ℝ) :
    (shortWindowCount gamma U t : ℝ) =
      ∑ i, if t < gamma i ∧ gamma i ≤ t + U then (1 : ℝ) else 0 := by
  simp [shortWindowCount]

private theorem shortWindowCount_sq_eq_pair_sum (gamma : ι → ℝ) (U t : ℝ) :
    (shortWindowCount gamma U t : ℝ) ^ 2 =
      ∑ i, ∑ j, shortWindowPairIndicator U (gamma i) (gamma j) t := by
  rw [shortWindowCount_cast_eq_sum, pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  by_cases hi : t < gamma i ∧ gamma i ≤ t + U
  · by_cases hj : t < gamma j ∧ gamma j ≤ t + U
    · simp [hi, hj, shortWindowPairIndicator]
    · simp [hi, hj, shortWindowPairIndicator]
  · by_cases hj : t < gamma j ∧ gamma j ≤ t + U
    · simp [hi, hj, shortWindowPairIndicator]
    · simp [hi, hj, shortWindowPairIndicator]

/-- Exact ordered-pair expansion of the moving-window square integral. -/
theorem shortWindowSecondMoment_eq_pairOverlapSum
    (gamma : ι → ℝ) {T U : ℝ} (hT : 0 ≤ T) :
    shortWindowSecondMoment gamma T U =
      ∑ i, ∑ j, pairWindowOverlap T U (gamma i) (gamma j) := by
  rw [shortWindowSecondMoment]
  simp_rw [shortWindowCount_sq_eq_pair_sum]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _hi
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _hj
      exact integral_shortWindowPairIndicator_eq_pairWindowOverlap hT
    · intro j _hj
      exact intervalIntegrable_shortWindowPairIndicator T U (gamma i) (gamma j)
  · intro i _hi
    have heq :
        (fun t : ℝ => ∑ j, shortWindowPairIndicator U (gamma i) (gamma j) t) =
          ∑ j, fun t : ℝ => shortWindowPairIndicator U (gamma i) (gamma j) t := by
      funext t
      exact (Finset.sum_apply t Finset.univ
        (fun (j : ι) (t : ℝ) =>
          shortWindowPairIndicator U (gamma i) (gamma j) t)).symm
    rw [heq]
    exact IntervalIntegrable.sum Finset.univ fun j _hj =>
      intervalIntegrable_shortWindowPairIndicator T U (gamma i) (gamma j)

/-- Exact split into the source interior triangular mass and a literal top remainder. -/
theorem shortWindowSecondMoment_eq_interior_add_topBoundary
    (gamma : ι → ℝ) {T U : ℝ} (hT : 0 ≤ T)
    (hlower : ∀ i, U ≤ gamma i) :
    shortWindowSecondMoment gamma T U =
      interiorTriangularPairMass gamma T U +
        topBoundaryRemainder gamma T U := by
  rw [shortWindowSecondMoment_eq_pairOverlapSum gamma hT,
    interiorTriangularPairMass, topBoundaryRemainder, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  by_cases hinterior : gamma i ≤ T ∧ gamma j ≤ T
  · rw [if_pos hinterior, if_pos hinterior, add_zero]
    exact pairWindowOverlap_eq_triangular_of_interior
      (hlower i) (hlower j) hinterior.1 hinterior.2
  · simp [hinterior]

theorem topBoundaryRemainder_nonneg
    (gamma : ι → ℝ) (T U : ℝ) :
    0 ≤ topBoundaryRemainder gamma T U := by
  unfold topBoundaryRemainder
  apply Finset.sum_nonneg
  intro i _hi
  apply Finset.sum_nonneg
  intro j _hj
  by_cases hinterior : gamma i ≤ T ∧ gamma j ≤ T
  · simp [hinterior]
  · simp [hinterior, pairWindowOverlap_nonneg]

/-- Retaining the exact boundary sign gives a loss-free one-sided source inequality. -/
theorem interiorTriangularPairMass_le_shortWindowSecondMoment
    (gamma : ι → ℝ) {T U : ℝ} (hT : 0 ≤ T)
    (hlower : ∀ i, U ≤ gamma i) :
    interiorTriangularPairMass gamma T U ≤
      shortWindowSecondMoment gamma T U := by
  rw [shortWindowSecondMoment_eq_interior_add_topBoundary gamma hT hlower]
  exact le_add_of_nonneg_right (topBoundaryRemainder_nonneg gamma T U)

private theorem pairWindowOverlap_eq_zero_of_above_band
    {T U x y : ℝ} (hx : T + U < x) :
    pairWindowOverlap T U x y = 0 := by
  unfold pairWindowOverlap
  rw [max_eq_right]
  have hupper : min T (min x y) ≤ T := min_le_left _ _
  have hlower : x - U ≤ max 0 (max x y - U) := by
    exact (sub_le_sub_right (le_max_left x y) U).trans (le_max_right _ _)
  linarith

private theorem pairWindowOverlap_eq_zero_of_below_band_of_other_future
    {T U x y : ℝ} (hx : x ≤ T - U) (hy : T < y) :
    pairWindowOverlap T U x y = 0 := by
  unfold pairWindowOverlap
  rw [max_eq_right]
  have hupper : min T (min x y) ≤ x :=
    (min_le_right T (min x y)).trans (min_le_left x y)
  have hlower : y - U ≤ max 0 (max x y - U) := by
    exact (sub_le_sub_right (le_max_right x y) U).trans (le_max_right _ _)
  linarith

omit [Fintype ι] in
private theorem topBoundaryContribution_eq_zero_of_not_mem_band_left
    {gamma : ι → ℝ} {T U : ℝ} {i j : ι}
    (hU : 0 ≤ U)
    (hi : ¬(T - U < gamma i ∧ gamma i ≤ T + U)) :
    (if gamma i ≤ T ∧ gamma j ≤ T then 0
      else pairWindowOverlap T U (gamma i) (gamma j)) = 0 := by
  by_cases hinterior : gamma i ≤ T ∧ gamma j ≤ T
  · simp [hinterior]
  · rw [if_neg hinterior]
    by_cases hiLow : gamma i ≤ T - U
    · have hiT : gamma i ≤ T := hiLow.trans (sub_le_self T hU)
      have hjFuture : T < gamma j := by
        by_contra hj
        exact hinterior ⟨hiT, le_of_not_gt hj⟩
      exact pairWindowOverlap_eq_zero_of_below_band_of_other_future hiLow hjFuture
    · have hiHigh : T + U < gamma i := by
        apply lt_of_not_ge
        intro hiUpper
        exact hi ⟨lt_of_not_ge hiLow, hiUpper⟩
      exact pairWindowOverlap_eq_zero_of_above_band hiHigh

omit [Fintype ι] in
private theorem topBoundaryContribution_eq_zero_of_not_mem_band_right
    {gamma : ι → ℝ} {T U : ℝ} {i j : ι}
    (hU : 0 ≤ U)
    (hj : ¬(T - U < gamma j ∧ gamma j ≤ T + U)) :
    (if gamma i ≤ T ∧ gamma j ≤ T then 0
      else pairWindowOverlap T U (gamma i) (gamma j)) = 0 := by
  have hleft := topBoundaryContribution_eq_zero_of_not_mem_band_left
    (gamma := gamma) (T := T) (U := U) (i := j) (j := i) hU hj
  simpa [and_comm, pairWindowOverlap_comm] using hleft

omit [Fintype ι] in
private theorem topBoundaryContribution_le_bandIndicator
    {gamma : ι → ℝ} {T U : ℝ} (hU : 0 ≤ U) (i j : ι) :
    (if gamma i ≤ T ∧ gamma j ≤ T then 0
      else pairWindowOverlap T U (gamma i) (gamma j)) ≤
      U * (if (T - U < gamma i ∧ gamma i ≤ T + U) ∧
          (T - U < gamma j ∧ gamma j ≤ T + U) then (1 : ℝ) else 0) := by
  by_cases hi : T - U < gamma i ∧ gamma i ≤ T + U
  · by_cases hj : T - U < gamma j ∧ gamma j ≤ T + U
    · simp only [hi, hj, and_self, ↓reduceIte, mul_one]
      by_cases hinterior : gamma i ≤ T ∧ gamma j ≤ T
      · simp [hinterior, hU]
      · simp only [hinterior, ↓reduceIte]
        exact pairWindowOverlap_le hU
    · rw [topBoundaryContribution_eq_zero_of_not_mem_band_right hU hj]
      simp [hj]
  · rw [topBoundaryContribution_eq_zero_of_not_mem_band_left hU hi]
    simp [hi]

private theorem boundaryBandPairSum_eq_count_sq
    (gamma : ι → ℝ) (T U : ℝ) :
    (∑ i, ∑ j, if (T - U < gamma i ∧ gamma i ≤ T + U) ∧
        (T - U < gamma j ∧ gamma j ≤ T + U) then (1 : ℝ) else 0) =
      (topBoundaryIndexCount gamma T U : ℝ) ^ 2 := by
  let band : Finset ι :=
    Finset.univ.filter fun i => T - U < gamma i ∧ gamma i ≤ T + U
  have hsum :
      (∑ i, if T - U < gamma i ∧ gamma i ≤ T + U then (1 : ℝ) else 0) =
        band.card := by
    simp [band]
  calc
    (∑ i, ∑ j, if (T - U < gamma i ∧ gamma i ≤ T + U) ∧
        (T - U < gamma j ∧ gamma j ≤ T + U) then (1 : ℝ) else 0) =
        (∑ i, if T - U < gamma i ∧ gamma i ≤ T + U then (1 : ℝ) else 0) *
          (∑ j, if T - U < gamma j ∧ gamma j ≤ T + U then (1 : ℝ) else 0) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      by_cases hi : T - U < gamma i ∧ gamma i ≤ T + U <;>
        by_cases hj : T - U < gamma j ∧ gamma j ≤ T + U <;>
          simp [hi, hj]
    _ = (band.card : ℝ) ^ 2 := by rw [hsum, pow_two]
    _ = (topBoundaryIndexCount gamma T U : ℝ) ^ 2 := by
      rfl

/-- The exact remainder is supported only by the local moving-height boundary population. -/
theorem topBoundaryRemainder_le
    (gamma : ι → ℝ) {T U : ℝ} (hU : 0 ≤ U) :
    topBoundaryRemainder gamma T U ≤
      U * (topBoundaryIndexCount gamma T U : ℝ) ^ 2 := by
  unfold topBoundaryRemainder
  calc
    (∑ i, ∑ j, if gamma i ≤ T ∧ gamma j ≤ T then 0
        else pairWindowOverlap T U (gamma i) (gamma j)) ≤
        ∑ i, ∑ j, U * (if
          (T - U < gamma i ∧ gamma i ≤ T + U) ∧
          (T - U < gamma j ∧ gamma j ≤ T + U) then (1 : ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro i _hi
      apply Finset.sum_le_sum
      intro j _hj
      exact topBoundaryContribution_le_bandIndicator hU i j
    _ = U * ∑ i, ∑ j, if
          (T - U < gamma i ∧ gamma i ≤ T + U) ∧
          (T - U < gamma j ∧ gamma j ≤ T + U) then (1 : ℝ) else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.mul_sum]
    _ = U * (topBoundaryIndexCount gamma T U : ℝ) ^ 2 := by
      rw [boundaryBandPairSum_eq_count_sq]

end FinitePopulation

section ActualZetaZeros

/-- Actual multiplicity-expanded ordinates up to the source's enlarged cutoff `T+U`. -/
def pccMovingWindowOrdinate (T U : ℝ) :
    PccPositiveZetaZeroIndex (T + U) → ℝ :=
  pccPositiveZetaOrdinate (T + U)

def pccMovingWindowSecondMoment (T U : ℝ) : ℝ :=
  shortWindowSecondMoment (pccMovingWindowOrdinate T U) T U

def pccMovingWindowInteriorMass (T U : ℝ) : ℝ :=
  interiorTriangularPairMass (pccMovingWindowOrdinate T U) T U

def pccMovingWindowTopBoundaryRemainder (T U : ℝ) : ℝ :=
  topBoundaryRemainder (pccMovingWindowOrdinate T U) T U

def pccMovingWindowBoundaryCount (T U : ℝ) : ℕ :=
  topBoundaryIndexCount (pccMovingWindowOrdinate T U) T U

/-- Actual-zeta exact boundary decomposition, with the unavailable first-zero bound explicit. -/
theorem pccMovingWindowSecondMoment_eq_interior_add_boundary
    {T U : ℝ} (hT : 0 ≤ T)
    (hlower : ∀ p : PccPositiveZetaZeroIndex (T + U),
      U ≤ pccMovingWindowOrdinate T U p) :
    pccMovingWindowSecondMoment T U =
      pccMovingWindowInteriorMass T U +
        pccMovingWindowTopBoundaryRemainder T U := by
  exact shortWindowSecondMoment_eq_interior_add_topBoundary
    (pccMovingWindowOrdinate T U) hT hlower

theorem pccMovingWindowInteriorMass_le_secondMoment
    {T U : ℝ} (hT : 0 ≤ T)
    (hlower : ∀ p : PccPositiveZetaZeroIndex (T + U),
      U ≤ pccMovingWindowOrdinate T U p) :
    pccMovingWindowInteriorMass T U ≤
      pccMovingWindowSecondMoment T U := by
  exact interiorTriangularPairMass_le_shortWindowSecondMoment
    (pccMovingWindowOrdinate T U) hT hlower

theorem pccMovingWindowTopBoundaryRemainder_le
    {T U : ℝ} (hU : 0 ≤ U) :
    pccMovingWindowTopBoundaryRemainder T U ≤
      U * (pccMovingWindowBoundaryCount T U : ℝ) ^ 2 := by
  exact topBoundaryRemainder_le (pccMovingWindowOrdinate T U) hU

end ActualZetaZeros

/-- Aggregate exact-boundary certificate fixed by the campaign preregistration. -/
structure PairCorrelationMovingWindowBoundaryCertificate : Prop where
  pairIntegral :
    ∀ {T U x y : ℝ}, 0 ≤ T →
      (∫ t : ℝ in 0..T, shortWindowPairIndicator U x y t) =
        pairWindowOverlap T U x y
  pairExpansion :
    ∀ {ι : Type} [Fintype ι] (gamma : ι → ℝ) {T U : ℝ}, 0 ≤ T →
      shortWindowSecondMoment gamma T U =
        ∑ i, ∑ j, pairWindowOverlap T U (gamma i) (gamma j)
  exactSplit :
    ∀ {ι : Type} [Fintype ι] (gamma : ι → ℝ) {T U : ℝ}, 0 ≤ T →
      (∀ i, U ≤ gamma i) →
      shortWindowSecondMoment gamma T U =
        interiorTriangularPairMass gamma T U + topBoundaryRemainder gamma T U
  boundaryNonneg :
    ∀ {ι : Type} [Fintype ι] (gamma : ι → ℝ) (T U : ℝ),
      0 ≤ topBoundaryRemainder gamma T U
  boundaryBound :
    ∀ {ι : Type} [Fintype ι] (gamma : ι → ℝ) {T U : ℝ}, 0 ≤ U →
      topBoundaryRemainder gamma T U ≤
        U * (topBoundaryIndexCount gamma T U : ℝ) ^ 2
  endpointMismatch :
    ∀ {T U : ℝ}, 0 ≤ T → 0 < U →
      pairWindowOverlap T U (T + U) (T + U) ≠
        max (U - |(T + U) - (T + U)|) 0
  actualZeta :
    ∀ {T U : ℝ}, 0 ≤ T →
      (∀ p : PccPositiveZetaZeroIndex (T + U),
        U ≤ pccMovingWindowOrdinate T U p) →
      pccMovingWindowSecondMoment T U =
        pccMovingWindowInteriorMass T U +
          pccMovingWindowTopBoundaryRemainder T U

theorem pairCorrelationMovingWindowBoundary_endpoint :
    PairCorrelationMovingWindowBoundaryCertificate where
  pairIntegral := integral_shortWindowPairIndicator_eq_pairWindowOverlap
  pairExpansion := shortWindowSecondMoment_eq_pairOverlapSum
  exactSplit := shortWindowSecondMoment_eq_interior_add_topBoundary
  boundaryNonneg := topBoundaryRemainder_nonneg
  boundaryBound := topBoundaryRemainder_le
  endpointMismatch := futureEndpoint_overlap_ne_triangular
  actualZeta := pccMovingWindowSecondMoment_eq_interior_add_boundary

end

end LeanLab.Riemann
