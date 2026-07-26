import LeanLab.Riemann.WeilFiniteDictionaryAdmissibility
import LeanLab.Riemann.WeilCompactLaplaceArithmeticFormula
import LeanLab.Riemann.WeilSymmetricGaussianFamily
import LeanLab.Riemann.WeilArchimedeanTailDensity
import Mathlib.Analysis.Complex.JensenFormula

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The finite Guinand--Weil dictionary explicit formula

This module attacks the weak-regularity boundary in the finite Guinand--Weil dictionary. The first
step replaces the coarse reciprocal-square zero count by a Jensen bound derived from the already
compiled order-one estimate for `riemannXi`, then selects zero-free contour heights in intervals
whose length grows with the contour scale.
-/

open Complex Filter Function MeasureTheory Set Topology
open scoped BigOperators FourierTransform Interval Topology

namespace LeanLab.Riemann

noncomputable section

/-- The multiplicity-bearing xi-zero count in a closed norm ball is exactly the divisor sum in
that ball. -/
theorem riemannXiZeroNormFinset_card_eq_finsum_divisor (R : ℝ) :
    ((riemannXiZeroNormFinset R).card : ℤ) =
      ∑ᶠ z : ℂ, MeromorphicOn.divisor riemannXi (Metric.closedBall 0 R) z := by
  classical
  let s : Finset RiemannXiDivisorZeroIndex := riemannXiZeroNormFinset R
  let t : Finset ℂ := s.image riemannXiDivisorZeroValue
  have hanalytic :
      AnalyticOnNhd ℂ riemannXi (Metric.closedBall (0 : ℂ) R) :=
    analyticOnNhd_riemannXi.mono (by simp)
  have hsupport :
      Function.support
          (MeromorphicOn.divisor riemannXi (Metric.closedBall 0 R)) ⊆
        (t : Set ℂ) := by
    intro z hz
    have hzball :
        z ∈ Metric.closedBall (0 : ℂ) R :=
      (MeromorphicOn.divisor riemannXi (Metric.closedBall 0 R)).supportWithinDomain hz
    have hdivEq :
        MeromorphicOn.divisor riemannXi (Metric.closedBall 0 R) z =
          riemannXiZeroDivisor z := by
      rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hanalytic hzball,
        riemannXiZeroDivisor,
        MeromorphicOn.AnalyticOnNhd.divisor_apply analyticOnNhd_riemannXi
          (Set.mem_univ z)]
    have hzZero : IsNontrivialZero z := by
      have hz' : z ∈ Function.support riemannXiZeroDivisor := by
        rw [Function.mem_support, ← hdivEq]
        exact hz
      simpa only [support_riemannXiZeroDivisor, Set.mem_setOf_eq] using hz'
    obtain ⟨p, hp⟩ :=
      (exists_riemannXiDivisorZeroIndex_val_iff z).mpr hzZero
    rw [Finset.mem_coe, Finset.mem_image]
    refine ⟨p, ?_, hp⟩
    rw [mem_riemannXiZeroNormFinset_iff]
    change ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ≤ R
    rw [hp]
    simpa [Metric.mem_closedBall] using hzball
  have hfiber :
      ∀ z ∈ t,
        ((s.filter (fun p => riemannXiDivisorZeroValue p = z)).card : ℤ) =
          MeromorphicOn.divisor riemannXi (Metric.closedBall 0 R) z := by
    intro z hz
    obtain ⟨p, hp, hpz⟩ := Finset.mem_image.mp hz
    have hzR : ‖z‖ ≤ R := by
      rw [← hpz]
      exact (mem_riemannXiZeroNormFinset_iff R p).mp hp
    have hz0 : z ≠ 0 := by
      rw [← hpz]
      exact Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p
    have hfilter :
        s.filter (fun q => riemannXiDivisorZeroValue q = z) =
          Complex.Hadamard.divisorZeroIndex₀_fiberFinset riemannXi z := by
      ext q
      rw [Finset.mem_filter,
        Complex.Hadamard.mem_divisorZeroIndex₀_fiberFinset]
      constructor
      · exact And.right
      · intro hq
        refine ⟨?_, hq⟩
        rw [mem_riemannXiZeroNormFinset_iff]
        change ‖Complex.Hadamard.divisorZeroIndex₀_val q‖ ≤ R
        rw [hq]
        exact hzR
    have hdivEq :
        MeromorphicOn.divisor riemannXi (Metric.closedBall 0 R) z =
          riemannXiZeroDivisor z := by
      have hzball : z ∈ Metric.closedBall (0 : ℂ) R := by
        simpa [Metric.mem_closedBall] using hzR
      rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hanalytic hzball,
        riemannXiZeroDivisor,
        MeromorphicOn.AnalyticOnNhd.divisor_apply analyticOnNhd_riemannXi
          (Set.mem_univ z)]
    rw [hfilter,
      Complex.Hadamard.divisorZeroIndex₀_fiberFinset_card_eq_analyticOrderNatAt
        differentiable_riemannXi hz0,
      hdivEq, riemannXiZeroDivisor_apply]
    rfl
  calc
    ((riemannXiZeroNormFinset R).card : ℤ) = (s.card : ℤ) := by rfl
    _ = ∑ z ∈ t,
        ((s.filter (fun p => riemannXiDivisorZeroValue p = z)).card : ℤ) := by
      exact_mod_cast
        (Finset.card_eq_sum_card_image riemannXiDivisorZeroValue s)
    _ = ∑ z ∈ t,
        MeromorphicOn.divisor riemannXi (Metric.closedBall 0 R) z := by
      exact Finset.sum_congr rfl hfiber
    _ = ∑ᶠ z : ℂ,
        MeromorphicOn.divisor riemannXi (Metric.closedBall 0 R) z := by
      symm
      exact finsum_eq_sum_of_support_subset _ hsupport

/-- Jensen's inequality and the order-one growth of xi give a fixed subquadratic,
multiplicity-bearing zero count. -/
theorem exists_riemannXiZeroNormFinset_card_le_rpow_five_fourths :
    ∃ K : ℝ, 0 < K ∧ ∀ R : ℝ, 1 ≤ R →
      ((riemannXiZeroNormFinset R).card : ℝ) ≤
        K * R ^ ((5 : ℝ) / 4) := by
  obtain ⟨C, hC, hgrowth⟩ :=
    riemannXi_entireOfOrderAtMost_one.2 (1 / 8 : ℝ) (by norm_num)
  let K : ℝ :=
    (C * (3 : ℝ) ^ ((9 : ℝ) / 8) + Real.log 2) / Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  refine ⟨K, hK, ?_⟩
  intro R hR
  let M : ℝ := Real.exp (C * (1 + 2 * R) ^ ((9 : ℝ) / 8))
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hM : 1 ≤ M := by
    dsimp only [M]
    exact Real.one_le_exp
      (mul_nonneg hC.le
        (Real.rpow_nonneg (by positivity : 0 ≤ 1 + 2 * R) _))
  have hbound :
      ∀ z ∈ Metric.sphere (0 : ℂ) |2 * R|, ‖riemannXi z‖ ≤ M := by
    intro z hz
    have hnorm : ‖z‖ = 2 * R := by
      rw [Metric.mem_sphere, dist_zero_right] at hz
      simpa [abs_of_pos hRpos] using hz
    have hzGrowth := hgrowth z
    norm_num at hzGrowth
    simpa only [M, hnorm] using hzGrowth
  have hjensen :=
    AnalyticOnNhd.sum_divisor_le
      (c := (0 : ℂ)) (r := R) (R := 2 * R) (M := M)
      (by simpa [abs_of_pos hRpos] using hRpos)
      (by
        rw [abs_of_pos hRpos, abs_of_pos (mul_pos (by norm_num) hRpos)]
        linarith)
      hM
      (analyticOnNhd_riemannXi.mono (by simp))
      riemannXi_zero_ne_zero
      hbound
  rw [abs_of_pos hRpos] at hjensen
  have hcardEq :=
    riemannXiZeroNormFinset_card_eq_finsum_divisor R
  have hcardJensen :
      ((riemannXiZeroNormFinset R).card : ℝ) ≤
        Real.log (M / ‖riemannXi 0‖) / Real.log ((2 * R) / R) := by
    calc
      ((riemannXiZeroNormFinset R).card : ℝ) =
          (((∑ᶠ z : ℂ,
            MeromorphicOn.divisor riemannXi (Metric.closedBall 0 R) z) : ℤ) : ℝ) := by
        exact_mod_cast hcardEq
      _ ≤ Real.log (M / ‖riemannXi 0‖) / Real.log ((2 * R) / R) :=
        hjensen
  have hlogM :
      Real.log (M / ‖riemannXi 0‖) =
        C * (1 + 2 * R) ^ ((9 : ℝ) / 8) + Real.log 2 := by
    rw [riemannXi_zero]
    norm_num [norm_def]
    dsimp only [M]
    have hlogHalf : Real.log (1 / 2) = -Real.log 2 := by
      rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub]
    rw [Real.log_div (Real.exp_ne_zero _) (by norm_num),
      Real.log_exp, hlogHalf]
    ring
  have hden : Real.log ((2 * R) / R) = Real.log 2 := by
    field_simp [hRpos.ne']
  have hbase : 1 + 2 * R ≤ 3 * R := by linarith
  have hrpowBase :
      (1 + 2 * R) ^ ((9 : ℝ) / 8) ≤
        (3 * R) ^ ((9 : ℝ) / 8) :=
    Real.rpow_le_rpow (by positivity) hbase (by norm_num)
  have hrpowMul :
      (3 * R) ^ ((9 : ℝ) / 8) =
        (3 : ℝ) ^ ((9 : ℝ) / 8) * R ^ ((9 : ℝ) / 8) := by
    rw [Real.mul_rpow (by norm_num) hRpos.le]
  have hrpowExponent :
      R ^ ((9 : ℝ) / 8) ≤ R ^ ((5 : ℝ) / 4) :=
    Real.rpow_le_rpow_of_exponent_le hR (by norm_num)
  have hrpowOne : 1 ≤ R ^ ((5 : ℝ) / 4) :=
    Real.one_le_rpow hR (by norm_num)
  rw [hlogM, hden] at hcardJensen
  calc
    ((riemannXiZeroNormFinset R).card : ℝ) ≤
        (C * (1 + 2 * R) ^ ((9 : ℝ) / 8) + Real.log 2) /
          Real.log 2 := hcardJensen
    _ ≤ (C * ((3 : ℝ) ^ ((9 : ℝ) / 8) * R ^ ((5 : ℝ) / 4)) +
          Real.log 2 * R ^ ((5 : ℝ) / 4)) / Real.log 2 := by
      apply div_le_div_of_nonneg_right _ hlog2.le
      gcongr
      · calc
          (1 + 2 * R) ^ ((9 : ℝ) / 8) ≤
              (3 * R) ^ ((9 : ℝ) / 8) := hrpowBase
          _ = (3 : ℝ) ^ ((9 : ℝ) / 8) * R ^ ((9 : ℝ) / 8) := hrpowMul
          _ ≤ (3 : ℝ) ^ ((9 : ℝ) / 8) * R ^ ((5 : ℝ) / 4) := by
            gcongr
      · nlinarith
    _ = K * R ^ ((5 : ℝ) / 4) := by
      dsimp only [K]
      field_simp [hlog2.ne']

/-- An interval of positive length contains a point quantitatively separated from every member of
a prescribed finite set. -/
theorem exists_mem_Ioo_add_forall_finset_abs_sub_ge
    (s : Finset ℝ) (R L : ℝ) (hL : 0 < L) :
    ∃ T ∈ Ioo R (R + L),
      ∀ y ∈ s, L / (4 * ((s.card : ℝ) + 1)) ≤ |T - y| := by
  classical
  let delta : ℝ := L / (4 * ((s.card : ℝ) + 1))
  let bad : Set ℝ := ⋃ y ∈ s, Ioo (y - delta) (y + delta)
  have hdelta : 0 < delta := by
    dsimp only [delta]
    positivity
  have hbadMeasure : volume.real bad ≤ (s.card : ℝ) * (2 * delta) := by
    calc
      volume.real bad ≤ ∑ y ∈ s, volume.real (Ioo (y - delta) (y + delta)) := by
        dsimp only [bad]
        exact measureReal_biUnion_finset_le s _
      _ = ∑ _y ∈ s, 2 * delta := by
        apply Finset.sum_congr rfl
        intro y _hy
        rw [Real.volume_real_Ioo_of_le (by linarith [hdelta.le])]
        ring
      _ = (s.card : ℝ) * (2 * delta) := by simp
  have hbadLt : volume.real bad < L := by
    apply lt_of_le_of_lt hbadMeasure
    dsimp only [delta]
    have hcard : 0 ≤ (s.card : ℝ) := Nat.cast_nonneg _
    have hden : 0 < 4 * ((s.card : ℝ) + 1) := by positivity
    rw [div_eq_mul_inv]
    calc
      (s.card : ℝ) * (2 * (L * (4 * ((s.card : ℝ) + 1))⁻¹)) =
          L * ((2 * (s.card : ℝ)) / (4 * ((s.card : ℝ) + 1))) := by
        rw [div_eq_mul_inv]
        ring
      _ < L * 1 := by
        gcongr
        rw [div_lt_one hden]
        nlinarith
      _ = L := mul_one L
  by_contra hnone
  push Not at hnone
  have hsubset : Ioo R (R + L) ⊆ bad := by
    intro T hT
    obtain ⟨y, hy, hdist⟩ := hnone T hT
    have hdist' : |T - y| < delta := by
      simpa only [delta] using hdist
    rw [abs_lt] at hdist'
    dsimp only [bad]
    simp only [Set.mem_iUnion]
    refine ⟨y, ?_⟩
    refine ⟨hy, ?_⟩
    constructor <;> linarith
  have hbadFinite : volume bad < (⊤ : ENNReal) := by
    dsimp only [bad]
    apply measure_biUnion_lt_top s.finite_toSet
    intro y _hy
    simp only [Real.volume_Ioo, ENNReal.ofReal_lt_top]
  have hmono : volume.real (Ioo R (R + L)) ≤ volume.real bad :=
    measureReal_mono hsubset hbadFinite.ne
  rw [Real.volume_real_Ioo_of_le (by linarith)] at hmono
  linarith

/-- A positive scale for the long-height construction. For `1 < c` it is definitionally
controlled by the pre-existing Gaussian scale. -/
def dictionaryXiHeightScale (c : ℝ) (n : ℕ) : ℝ :=
  max 1 (gaussianXiHeightScale c n)

theorem dictionaryXiHeightScale_pos (c : ℝ) (n : ℕ) :
    0 < dictionaryXiHeightScale c n := by
  unfold dictionaryXiHeightScale
  exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem dictionaryXiHeightScale_eq_gaussian
    {c : ℝ} (hc : 1 < c) (n : ℕ) :
    dictionaryXiHeightScale c n = gaussianXiHeightScale c n := by
  rw [dictionaryXiHeightScale, max_eq_right]
  unfold gaussianXiHeightScale
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

theorem tendsto_dictionaryXiHeightScale (c : ℝ) :
    Tendsto (dictionaryXiHeightScale c) atTop atTop := by
  apply tendsto_atTop_mono' atTop
    (Filter.Eventually.of_forall fun n =>
      le_max_right (1 : ℝ) (gaussianXiHeightScale c n))
    (tendsto_gaussianXiHeightScale c)

/-- Xi zeros close enough to affect the long selected top edge. -/
noncomputable def dictionaryXiNearZeroFinset (c : ℝ) (n : ℕ) :
    Finset RiemannXiDivisorZeroIndex :=
  riemannXiZeroNormFinset (6 * dictionaryXiHeightScale c n)

/-- Absolute ordinates represented by the nearby multiplicity-bearing zeros. -/
noncomputable def dictionaryXiNearAbsImFinset (c : ℝ) (n : ℕ) : Finset ℝ :=
  (dictionaryXiNearZeroFinset c n).image
    (fun p => |(riemannXiDivisorZeroValue p).im|)

/-- A canonical zero-avoiding height in `(R,2R)`, where `R` is the campaign scale. -/
noncomputable def dictionaryXiSelectedHeight (c : ℝ) (n : ℕ) : ℝ :=
  Classical.choose
    (exists_mem_Ioo_add_forall_finset_abs_sub_ge
      (dictionaryXiNearAbsImFinset c n)
      (dictionaryXiHeightScale c n) (dictionaryXiHeightScale c n)
      (dictionaryXiHeightScale_pos c n))

theorem dictionaryXiSelectedHeight_spec (c : ℝ) (n : ℕ) :
    dictionaryXiSelectedHeight c n ∈
        Ioo (dictionaryXiHeightScale c n) (2 * dictionaryXiHeightScale c n) ∧
      ∀ y ∈ dictionaryXiNearAbsImFinset c n,
        dictionaryXiHeightScale c n /
            (4 * (((dictionaryXiNearAbsImFinset c n).card : ℝ) + 1)) ≤
          |dictionaryXiSelectedHeight c n - y| := by
  have h := Classical.choose_spec
    (exists_mem_Ioo_add_forall_finset_abs_sub_ge
      (dictionaryXiNearAbsImFinset c n)
      (dictionaryXiHeightScale c n) (dictionaryXiHeightScale c n)
      (dictionaryXiHeightScale_pos c n))
  simpa only [dictionaryXiSelectedHeight, two_mul] using h

theorem tendsto_dictionaryXiSelectedHeight
    (c : ℝ) :
    Tendsto (dictionaryXiSelectedHeight c) atTop atTop := by
  apply tendsto_atTop_mono' atTop
    (Filter.Eventually.of_forall fun n =>
      (dictionaryXiSelectedHeight_spec c n).1.1.le)
    (tendsto_dictionaryXiHeightScale c)

/-- Every long selected symmetric rectangle has a genuinely zero-free boundary. -/
theorem dictionaryXiSelectedHeight_zeroFreeBoundary
    {c : ℝ} (hc : 1 < c) (n : ℕ) (p : RiemannXiDivisorZeroIndex) :
    ¬riemannXiZeroOnRectangleBoundary
      (1 - c) c (-dictionaryXiSelectedHeight c n)
        (dictionaryXiSelectedHeight c n) p := by
  let rho : ℂ := riemannXiDivisorZeroValue p
  let R : ℝ := dictionaryXiHeightScale c n
  let T : ℝ := dictionaryXiSelectedHeight c n
  have hrho : IsNontrivialZero rho :=
    riemannXiDivisorZeroIndex_val_isNontrivialZero p
  have hreflect : IsNontrivialZero (1 - rho) := by
    rw [isNontrivialZero_iff_riemannXi_eq_zero, riemannXi_one_sub]
    exact (isNontrivialZero_iff_riemannXi_eq_zero rho).mp hrho
  have hre0 : 0 < rho.re := by
    have hreflectRe := nontrivial_zero_re_lt_one hreflect
    simp only [sub_re, one_re] at hreflectRe
    linarith
  have hre1 : rho.re < 1 := nontrivial_zero_re_lt_one hrho
  have hRpos : 0 < R := dictionaryXiHeightScale_pos c n
  have hRtwo : 2 < R := by
    dsimp only [R]
    rw [dictionaryXiHeightScale_eq_gaussian hc]
    unfold gaussianXiHeightScale
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hTmem : T ∈ Ioo R (2 * R) :=
    dictionaryXiSelectedHeight_spec c n |>.1
  have hTpos : 0 < T := lt_trans hRpos hTmem.1
  have hnear_of_abs_im_eq
      (him : |rho.im| = T) : p ∈ dictionaryXiNearZeroFinset c n := by
    rw [dictionaryXiNearZeroFinset, mem_riemannXiZeroNormFinset_iff]
    apply le_of_lt
    calc
      ‖rho‖ ≤ |rho.re| + |rho.im| :=
        Complex.norm_le_abs_re_add_abs_im rho
      _ = rho.re + T := by rw [abs_of_pos hre0, him]
      _ < 1 + 2 * R := by linarith [hTmem.2]
      _ < 6 * R := by linarith
  have hsep_of_abs_im_eq (him : |rho.im| = T) : False := by
    have hpNear := hnear_of_abs_im_eq him
    have himMem : |rho.im| ∈ dictionaryXiNearAbsImFinset c n := by
      rw [dictionaryXiNearAbsImFinset]
      exact Finset.mem_image.mpr ⟨p, hpNear, rfl⟩
    have hsep :=
      (dictionaryXiSelectedHeight_spec c n).2 |rho.im| himMem
    have hdeltaPos :
        0 < R /
          (4 * (((dictionaryXiNearAbsImFinset c n).card : ℝ) + 1)) := by
      positivity
    rw [him, sub_self, abs_zero] at hsep
    linarith
  intro hboundary
  rcases hboundary with hbottom | htop | hleft | hright
  · apply hsep_of_abs_im_eq
    rw [hbottom.1, abs_neg, abs_of_pos hTpos]
  · apply hsep_of_abs_im_eq
    rw [htop.1, abs_of_pos hTpos]
  · linarith [hleft.1]
  · linarith [hright.1]

/-- The long selected top edge is separated from the ordinate of every nearby zero. -/
theorem dictionaryXiSelectedHeight_sep_im_of_mem_near
    (c : ℝ) (n : ℕ) (p : RiemannXiDivisorZeroIndex)
    (hp : p ∈ dictionaryXiNearZeroFinset c n) :
    dictionaryXiHeightScale c n /
        (4 * (((dictionaryXiNearAbsImFinset c n).card : ℝ) + 1)) ≤
      |dictionaryXiSelectedHeight c n -
        (riemannXiDivisorZeroValue p).im| := by
  have himMem : |(riemannXiDivisorZeroValue p).im| ∈
      dictionaryXiNearAbsImFinset c n := by
    rw [dictionaryXiNearAbsImFinset]
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
  have hsep := (dictionaryXiSelectedHeight_spec c n).2
    |(riemannXiDivisorZeroValue p).im| himMem
  have hTpos : 0 < dictionaryXiSelectedHeight c n :=
    lt_trans (dictionaryXiHeightScale_pos c n)
      (dictionaryXiSelectedHeight_spec c n).1.1
  exact hsep.trans (by
    simpa only [abs_of_pos hTpos] using
      abs_abs_sub_abs_le_abs_sub
        (dictionaryXiSelectedHeight c n) (riemannXiDivisorZeroValue p).im)

/-- Points of the long selected top edge have norm below three times the campaign scale. -/
theorem norm_dictionaryXiSelectedTopEdge_lt
    {c : ℝ} (hc : 1 < c) (n : ℕ) {x : ℝ} (hx : x ∈ [[1 - c, c]]) :
    ‖(x : ℂ) + dictionaryXiSelectedHeight c n * I‖ <
      3 * dictionaryXiHeightScale c n := by
  have hlr : 1 - c ≤ c := by linarith
  rw [uIcc_of_le hlr] at hx
  have habsx : |x| ≤ c := by
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2]
  have hT := (dictionaryXiSelectedHeight_spec c n).1.2
  have hRgtc : c < dictionaryXiHeightScale c n := by
    rw [dictionaryXiHeightScale_eq_gaussian hc]
    unfold gaussianXiHeightScale
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hnorm := Complex.norm_le_abs_re_add_abs_im
    ((x : ℂ) + dictionaryXiSelectedHeight c n * I)
  have hre :
      (((x : ℂ) + dictionaryXiSelectedHeight c n * I).re) = x := by
    simp
  have him :
      (((x : ℂ) + dictionaryXiSelectedHeight c n * I).im) =
        dictionaryXiSelectedHeight c n := by
    simp
  rw [hre, him, abs_of_pos
    (lt_trans (dictionaryXiHeightScale_pos c n)
      (dictionaryXiSelectedHeight_spec c n).1.1)] at hnorm
  calc
    ‖(x : ℂ) + dictionaryXiSelectedHeight c n * I‖ ≤
        |x| + dictionaryXiSelectedHeight c n := hnorm
    _ ≤ c + dictionaryXiSelectedHeight c n := by gcongr
    _ < dictionaryXiHeightScale c n +
        2 * dictionaryXiHeightScale c n := by linarith
    _ = 3 * dictionaryXiHeightScale c n := by ring

/-- Hadamard factorization bounds xi's logarithmic derivative on the long selected top edge by
one finite near-zero contribution and one reciprocal-square far-zero contribution. -/
theorem exists_norm_logDeriv_dictionaryXiSelectedTopEdge_le
    {c : ℝ} (hc : 1 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ x ∈ [[1 - c, c]],
      ‖logDeriv riemannXi
          ((x : ℂ) + dictionaryXiSelectedHeight c n * I)‖ ≤
        C + ((dictionaryXiNearZeroFinset c n).card : ℝ) *
            ((dictionaryXiHeightScale c n /
                (4 * (((dictionaryXiNearAbsImFinset c n).card : ℝ) + 1)))⁻¹ +
              (riemannXiReciprocalSquareMass + 1)) +
          6 * dictionaryXiHeightScale c n *
            riemannXiReciprocalSquareMass := by
  obtain ⟨P, hPdegree, hPfac⟩ := exists_riemannXi_hadamard_factorization
  refine ⟨‖P.derivative.coeff 0‖, norm_nonneg _, ?_⟩
  intro n x hx
  let R : ℝ := dictionaryXiHeightScale c n
  let T : ℝ := dictionaryXiSelectedHeight c n
  let z : ℂ := (x : ℂ) + T * I
  let near : Finset RiemannXiDivisorZeroIndex :=
    dictionaryXiNearZeroFinset c n
  let delta : ℝ :=
    R / (4 * (((dictionaryXiNearAbsImFinset c n).card : ℝ) + 1))
  let u : RiemannXiDivisorZeroIndex → ℝ := fun p =>
    ‖riemannXiDivisorZeroValue p‖⁻¹ ^ (2 : ℕ)
  have hRpos : 0 < R := dictionaryXiHeightScale_pos c n
  have hTpos : 0 < T :=
    lt_trans hRpos (dictionaryXiSelectedHeight_spec c n).1.1
  have hdelta : 0 < delta := by
    dsimp only [delta]
    positivity
  have hlr : 1 - c < c := by linarith
  have hbt : -T < T := by linarith
  obtain ⟨_hbottomMap, htopMap, _hrightMap, _hleftMap⟩ :=
    mapsTo_riemannXiNonzeroSet_rectangle_edges hlr hbt
      (dictionaryXiSelectedHeight_zeroFreeBoundary hc n)
  have hznonzero : z ∈ riemannXiNonzeroSet := by
    apply htopMap
    simpa only [z, T] using hx
  have hsum : Summable (fun p : RiemannXiDivisorZeroIndex =>
      riemannXiLogDerivZeroTerm p z) :=
    summable_riemannXiLogDerivZeroTerm_of_mem_nonzeroSet hznonzero
  have hu : Summable u :=
    summable_riemannXiDivisorZeroIndex_norm_inv_sq
  have hnearTerm : ∀ p ∈ near,
      ‖riemannXiLogDerivZeroTerm p z‖ ≤
        delta⁻¹ + (riemannXiReciprocalSquareMass + 1) := by
    intro p hp
    have hsepRaw :=
      dictionaryXiSelectedHeight_sep_im_of_mem_near c n p (by
        simpa only [near] using hp)
    have hzim : z.im = T := by simp [z]
    have hsep :
        delta ≤ |z.im - (riemannXiDivisorZeroValue p).im| := by
      simpa only [delta, hzim, T, R] using hsepRaw
    exact
      (norm_riemannXiLogDerivZeroTerm_le_of_im_separated p hdelta hsep).trans
        (by
          gcongr
          exact riemannXiDivisorZeroValue_norm_inv_le_mass_add_one p)
  have hnearSum :
      ∑ p ∈ near, ‖riemannXiLogDerivZeroTerm p z‖ ≤
        (near.card : ℝ) *
          (delta⁻¹ + (riemannXiReciprocalSquareMass + 1)) := by
    calc
      ∑ p ∈ near, ‖riemannXiLogDerivZeroTerm p z‖ ≤
          ∑ _p ∈ near,
            (delta⁻¹ + (riemannXiReciprocalSquareMass + 1)) := by
        exact Finset.sum_le_sum hnearTerm
      _ = (near.card : ℝ) *
          (delta⁻¹ + (riemannXiReciprocalSquareMass + 1)) := by
        simp
        ring
  have hfarTerm : ∀ q : (nearᶜ : Set RiemannXiDivisorZeroIndex),
      ‖riemannXiLogDerivZeroTerm q.1 z‖ ≤ (6 * R) * u q.1 := by
    intro q
    have hqNot : q.1 ∉ near := by
      intro hq
      exact q.2 hq
    have hqNorm : 6 * R < ‖riemannXiDivisorZeroValue q.1‖ := by
      apply lt_of_not_ge
      intro hle
      apply hqNot
      simpa only [near, dictionaryXiNearZeroFinset,
        mem_riemannXiZeroNormFinset_iff, R] using hle
    have hzNorm : ‖z‖ < 3 * R := by
      simpa only [z, T, R] using
        norm_dictionaryXiSelectedTopEdge_lt hc n hx
    have hfar : 2 * ‖z‖ < ‖riemannXiDivisorZeroValue q.1‖ := by
      nlinarith
    calc
      ‖riemannXiLogDerivZeroTerm q.1 z‖ ≤
          (2 * ‖z‖) * u q.1 :=
        norm_riemannXiLogDerivZeroTerm_le_of_two_norm_lt q.1 hfar
      _ ≤ (6 * R) * u q.1 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith
  have hfarMajorant :
      Summable (fun q : (nearᶜ : Set RiemannXiDivisorZeroIndex) =>
        (6 * R) * u q.1) :=
    (hu.subtype _).mul_left (6 * R)
  have hfarSum :
      ∑' q : (nearᶜ : Set RiemannXiDivisorZeroIndex),
          ‖riemannXiLogDerivZeroTerm q.1 z‖ ≤
        6 * R * riemannXiReciprocalSquareMass := by
    calc
      ∑' q : (nearᶜ : Set RiemannXiDivisorZeroIndex),
          ‖riemannXiLogDerivZeroTerm q.1 z‖ ≤
          ∑' q : (nearᶜ : Set RiemannXiDivisorZeroIndex),
            (6 * R) * u q.1 :=
        (hsum.norm.subtype _).tsum_le_tsum hfarTerm hfarMajorant
      _ = (6 * R) *
          ∑' q : (nearᶜ : Set RiemannXiDivisorZeroIndex), u q.1 := by
        rw [tsum_mul_left]
      _ ≤ (6 * R) *
          ∑' p : RiemannXiDivisorZeroIndex, u p := by
        gcongr
        exact Summable.tsum_subtype_le u _ (fun _p => by positivity) hu
      _ = 6 * R * riemannXiReciprocalSquareMass := by
        dsimp only [u, riemannXiReciprocalSquareMass]
  have hzeroSum :
      ‖∑' p : RiemannXiDivisorZeroIndex,
          riemannXiLogDerivZeroTerm p z‖ ≤
        (near.card : ℝ) *
            (delta⁻¹ + (riemannXiReciprocalSquareMass + 1)) +
          6 * R * riemannXiReciprocalSquareMass := by
    calc
      ‖∑' p : RiemannXiDivisorZeroIndex,
          riemannXiLogDerivZeroTerm p z‖ ≤
          ∑' p : RiemannXiDivisorZeroIndex,
            ‖riemannXiLogDerivZeroTerm p z‖ :=
        norm_tsum_le_tsum_norm hsum.norm
      _ = (∑ p ∈ near, ‖riemannXiLogDerivZeroTerm p z‖) +
          ∑' q : (nearᶜ : Set RiemannXiDivisorZeroIndex),
            ‖riemannXiLogDerivZeroTerm q.1 z‖ :=
        hsum.norm.sum_add_tsum_compl.symm
      _ ≤ (near.card : ℝ) *
            (delta⁻¹ + (riemannXiReciprocalSquareMass + 1)) +
          6 * R * riemannXiReciprocalSquareMass :=
        add_le_add hnearSum hfarSum
  have hlog :=
    riemannXi_logDeriv_eq_polynomial_derivative_add_tsum hPfac hznonzero
  rw [hlog, eval_derivative_eq_coeff_zero_of_degree_le_one hPdegree]
  calc
    ‖↑(P.derivative.coeff 0) +
        ∑' p : RiemannXiDivisorZeroIndex,
          riemannXiLogDerivZeroTerm p z‖ ≤
      ‖P.derivative.coeff 0‖ +
        ‖∑' p : RiemannXiDivisorZeroIndex,
          riemannXiLogDerivZeroTerm p z‖ :=
      norm_add_le _ _
    _ ≤ ‖P.derivative.coeff 0‖ +
        ((near.card : ℝ) *
            (delta⁻¹ + (riemannXiReciprocalSquareMass + 1)) +
          6 * R * riemannXiReciprocalSquareMass) := by
      gcongr
    _ = ‖P.derivative.coeff 0‖ +
        ((dictionaryXiNearZeroFinset c n).card : ℝ) *
            ((dictionaryXiHeightScale c n /
                (4 * (((dictionaryXiNearAbsImFinset c n).card : ℝ) + 1)))⁻¹ +
              (riemannXiReciprocalSquareMass + 1)) +
          6 * dictionaryXiHeightScale c n *
            riemannXiReciprocalSquareMass := by
      dsimp only [near, delta, R]
      ring

/-- The long selected-height logarithmic derivative has a power strictly below the
inverse-square decay threshold of the finite dictionary test. -/
theorem exists_norm_logDeriv_dictionaryXiSelectedTopEdge_le_rpow_seven_fourths
    {c : ℝ} (hc : 1 < c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, ∀ x ∈ [[1 - c, c]],
      ‖logDeriv riemannXi
          ((x : ℂ) + dictionaryXiSelectedHeight c n * I)‖ ≤
        K * dictionaryXiHeightScale c n ^ ((7 : ℝ) / 4) := by
  obtain ⟨C, hC, hraw⟩ :=
    exists_norm_logDeriv_dictionaryXiSelectedTopEdge_le hc
  obtain ⟨Kzero, hKzero, hcount⟩ :=
    exists_riemannXiZeroNormFinset_card_le_rpow_five_fourths
  let M : ℝ := riemannXiReciprocalSquareMass
  let B : ℝ := Kzero * (6 : ℝ) ^ ((5 : ℝ) / 4)
  let K : ℝ :=
    C + 4 * B * (B + 1) + B * (M + 1) + 6 * M
  have hM : 0 ≤ M := riemannXiReciprocalSquareMass_nonneg
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  refine ⟨K, hK, ?_⟩
  intro n x hx
  let R : ℝ := dictionaryXiHeightScale c n
  let N : ℝ := ((dictionaryXiNearZeroFinset c n).card : ℝ)
  let A : ℝ := ((dictionaryXiNearAbsImFinset c n).card : ℝ)
  let q : ℝ := R ^ ((5 : ℝ) / 4)
  let Q : ℝ := R ^ ((7 : ℝ) / 4)
  have hRpos : 0 < R := dictionaryXiHeightScale_pos c n
  have hRone : 1 ≤ R := by
    dsimp only [R, dictionaryXiHeightScale]
    exact le_max_left _ _
  have hNnonneg : 0 ≤ N := by
    dsimp only [N]
    positivity
  have hAnonneg : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hqnonneg : 0 ≤ q := by
    dsimp only [q]
    positivity
  have hQnonneg : 0 ≤ Q := by
    dsimp only [Q]
    positivity
  have hqOne : 1 ≤ q := by
    dsimp only [q]
    exact Real.one_le_rpow hRone (by norm_num)
  have hQOne : 1 ≤ Q := by
    dsimp only [Q]
    exact Real.one_le_rpow hRone (by norm_num)
  have h6Rone : 1 ≤ 6 * R := by nlinarith
  have hNraw := hcount (6 * R) h6Rone
  have hN :
      N ≤ B * q := by
    calc
      N ≤ Kzero * (6 * R) ^ ((5 : ℝ) / 4) := by
        simpa only [N, dictionaryXiNearZeroFinset, R] using hNraw
      _ = B * q := by
        dsimp only [B, q]
        rw [Real.mul_rpow (by norm_num) hRpos.le]
        ring
  have hA : A ≤ N := by
    have himage := Finset.card_image_le
      (s := dictionaryXiNearZeroFinset c n)
      (f := fun p => |(riemannXiDivisorZeroValue p).im|)
    dsimp only [A, N, dictionaryXiNearAbsImFinset]
    exact_mod_cast himage
  have hNplus : N + 1 ≤ (B + 1) * q := by
    calc
      N + 1 ≤ B * q + q := add_le_add hN hqOne
      _ = (B + 1) * q := by ring
  have hdeltaInv :
      (R / (4 * (A + 1)))⁻¹ = 4 * (A + 1) / R := by
    have hden : 4 * (A + 1) ≠ 0 := by positivity
    field_simp [hRpos.ne', hden]
  have hqSquareDiv :
      q * q / R = R ^ ((3 : ℝ) / 2) := by
    dsimp only [q]
    rw [← Real.rpow_add hRpos]
    have hexp :
        (5 : ℝ) / 4 + 5 / 4 = (3 : ℝ) / 2 + 1 := by
      norm_num
    rw [hexp, Real.rpow_add hRpos, Real.rpow_one]
    field_simp [hRpos.ne']
  have hpow_three_halves :
      R ^ ((3 : ℝ) / 2) ≤ Q := by
    dsimp only [Q]
    exact Real.rpow_le_rpow_of_exponent_le hRone (by norm_num)
  have hpow_five_fourths :
      q ≤ Q := by
    dsimp only [q, Q]
    exact Real.rpow_le_rpow_of_exponent_le hRone (by norm_num)
  have hpow_one :
      R ≤ Q := by
    rw [← Real.rpow_one R]
    dsimp only [Q]
    exact Real.rpow_le_rpow_of_exponent_le hRone (by norm_num)
  have hnearSep :
      N * (4 * (A + 1) / R) ≤
        (4 * B * (B + 1)) * Q := by
    calc
      N * (4 * (A + 1) / R) =
          4 * (N * (A + 1)) / R := by ring
      _ ≤ 4 * ((B * q) * ((B + 1) * q)) / R := by
        gcongr
        nlinarith [hA, hNplus]
      _ = (4 * B * (B + 1)) * (q * q / R) := by ring
      _ = (4 * B * (B + 1)) * R ^ ((3 : ℝ) / 2) := by
        rw [hqSquareDiv]
      _ ≤ (4 * B * (B + 1)) * Q := by
        gcongr
  have hnearMass :
      N * (M + 1) ≤ (B * (M + 1)) * Q := by
    calc
      N * (M + 1) ≤ (B * q) * (M + 1) := by
        gcongr
      _ = (B * (M + 1)) * q := by ring
      _ ≤ (B * (M + 1)) * Q := by
        gcongr
  have hfar :
      6 * R * M ≤ (6 * M) * Q := by
    calc
      6 * R * M = (6 * M) * R := by ring
      _ ≤ (6 * M) * Q := by
        gcongr
  have hconstant : C ≤ C * Q := by
    nlinarith [mul_nonneg hC (sub_nonneg.mpr hQOne)]
  have hraw' := hraw n x hx
  change
    ‖logDeriv riemannXi
        ((x : ℂ) + dictionaryXiSelectedHeight c n * I)‖ ≤
      C + N * ((R / (4 * (A + 1)))⁻¹ + (M + 1)) +
        6 * R * M at hraw'
  rw [hdeltaInv] at hraw'
  calc
    ‖logDeriv riemannXi
        ((x : ℂ) + dictionaryXiSelectedHeight c n * I)‖ ≤
        C + N * (4 * (A + 1) / R + (M + 1)) +
          6 * R * M := hraw'
    _ = C + (N * (4 * (A + 1) / R) + N * (M + 1)) +
          6 * R * M := by ring
    _ ≤ C * Q +
          ((4 * B * (B + 1)) * Q + (B * (M + 1)) * Q) +
          (6 * M) * Q := by
      gcongr
    _ = K * dictionaryXiHeightScale c n ^ ((7 : ℝ) / 4) := by
      dsimp only [K, Q, R]
      ring

/-- The top horizontal integral at the long zero-free dictionary heights. -/
noncomputable def dictionaryXiTopHorizontalIntegralFor
    (F : ℂ → ℂ) (c : ℝ) (n : ℕ) : ℂ :=
  ∫ x : ℝ in 1 - c..c,
    F ((x : ℂ) + dictionaryXiSelectedHeight c n * I) *
      logDeriv riemannXi
        ((x : ℂ) + dictionaryXiSelectedHeight c n * I)

/-- The right vertical integral at the long zero-free dictionary heights. -/
noncomputable def dictionaryXiRightVerticalIntegralFor
    (F : ℂ → ℂ) (c : ℝ) (n : ℕ) : ℂ :=
  ∫ y : ℝ in
    -dictionaryXiSelectedHeight c n..dictionaryXiSelectedHeight c n,
      F ((c : ℂ) + y * I) *
        logDeriv riemannXi ((c : ℂ) + y * I)

/-- The finite multiplicity-bearing zero sum in a long selected symmetric rectangle. -/
noncomputable def dictionaryXiRectangleZeroFinsumFor
    (F : ℂ → ℂ) (c : ℝ) (n : ℕ) : ℂ :=
  ∑ᶠ p : RiemannXiDivisorZeroIndex,
    if riemannXiZeroStrictlyInsideRectangle
        (1 - c) c (-dictionaryXiSelectedHeight c n)
          (dictionaryXiSelectedHeight c n) p then
      F (riemannXiDivisorZeroValue p)
    else 0

/-- The literal finite dictionary test has inverse-square decay on every long selected top edge
after the exact source-to-xi coordinate conversion. -/
theorem norm_symmetrizedDictionaryWeight_selectedTopEdge_le
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) {c : ℝ} (hc : 1 < c)
    (n : ℕ) {x : ℝ} (hx : x ∈ [[1 - c, c]]) :
    ‖symmetrizedCompactLaplaceWeight
        (weilFiniteDictionaryPhysicalDensity C N u)
        ((x : ℂ) + dictionaryXiSelectedHeight c n * I)‖ ≤
      weilFiniteDictionaryStripDecayConstant C N u (c - 1 / 2) *
        (dictionaryXiHeightScale c n)⁻¹ ^ (2 : ℕ) := by
  have hlr : 1 - c ≤ c := by linarith
  rw [uIcc_of_le hlr] at hx
  let s : ℂ := (x : ℂ) + dictionaryXiSelectedHeight c n * I
  let z : ℂ := (s - 1 / 2) / I
  have hA : 0 ≤ c - 1 / 2 := by linarith
  have hzIm : |z.im| ≤ c - 1 / 2 := by
    dsimp only [z]
    rw [weilFiniteDictionaryZeroCoordinate_im]
    dsimp only [s]
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero]
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2]
  have hstrip :=
    norm_weilFiniteDictionaryTest_le_stripDecay hC N u hA hzIm
  have hzRe : z.re = dictionaryXiSelectedHeight c n := by
    dsimp only [z]
    rw [weilFiniteDictionaryZeroCoordinate_re]
    dsimp only [s]
    simp
  have hTpos : 0 < dictionaryXiSelectedHeight c n :=
    lt_trans (dictionaryXiHeightScale_pos c n)
      (dictionaryXiSelectedHeight_spec c n).1.1
  have hinv :
      (1 + |z.re|)⁻¹ ≤ (dictionaryXiHeightScale c n)⁻¹ := by
    rw [hzRe, abs_of_pos hTpos]
    simpa only [one_div] using one_div_le_one_div_of_le
      (dictionaryXiHeightScale_pos c n)
      (by
        have hT :=
          (dictionaryXiSelectedHeight_spec c n).1.1
        linarith)
  rw [symmetrizedCompactLaplaceWeight_weilFiniteDictionaryPhysicalDensity hC,
    ← weilFiniteDictionaryTest_zeroCoordinate hC]
  exact hstrip.trans
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (inv_nonneg.mpr (by positivity)) hinv 2)
      (weilFiniteDictionaryStripDecayConstant_nonneg
        hC N u hA))

/-- The weak-regularity finite dictionary test makes the long selected top-horizontal xi integral
vanish. This is the analytic obstruction that the old unit-height `O(R^4)` estimate could not
cross. -/
theorem tendsto_dictionaryXiTopHorizontalIntegral
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) {c : ℝ} (hc : 1 < c) :
    Tendsto
      (dictionaryXiTopHorizontalIntegralFor
        (symmetrizedCompactLaplaceWeight
          (weilFiniteDictionaryPhysicalDensity C N u)) c)
      atTop (𝓝 0) := by
  obtain ⟨K, hK, hlog⟩ :=
    exists_norm_logDeriv_dictionaryXiSelectedTopEdge_le_rpow_seven_fourths hc
  let D : ℝ :=
    weilFiniteDictionaryStripDecayConstant C N u (c - 1 / 2)
  let B : ℝ := D * K * |c - (1 - c)|
  have hD : 0 ≤ D := by
    dsimp only [D]
    exact weilFiniteDictionaryStripDecayConstant_nonneg
      hC N u (by linarith)
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity
  have hbound :
      ∀ n : ℕ,
        ‖dictionaryXiTopHorizontalIntegralFor
            (symmetrizedCompactLaplaceWeight
              (weilFiniteDictionaryPhysicalDensity C N u)) c n‖ ≤
          B * (dictionaryXiHeightScale c n) ^ (-((1 : ℝ) / 4)) := by
    intro n
    let R : ℝ := dictionaryXiHeightScale c n
    have hRpos : 0 < R := dictionaryXiHeightScale_pos c n
    have hinvPow :
        R⁻¹ ^ (2 : ℕ) = R ^ (-(2 : ℝ)) := by
      rw [Real.rpow_neg hRpos.le, Real.rpow_two]
      exact inv_pow R 2
    have hpower :
        (R⁻¹ ^ (2 : ℕ)) * R ^ ((7 : ℝ) / 4) =
          R ^ (-((1 : ℝ) / 4)) := by
      rw [hinvPow, ← Real.rpow_add hRpos]
      congr 1
      norm_num
    have hpoint : ∀ x ∈ Ι (1 - c) c,
        ‖symmetrizedCompactLaplaceWeight
              (weilFiniteDictionaryPhysicalDensity C N u)
              ((x : ℂ) + dictionaryXiSelectedHeight c n * I) *
            logDeriv riemannXi
              ((x : ℂ) + dictionaryXiSelectedHeight c n * I)‖ ≤
          (D * R⁻¹ ^ (2 : ℕ)) *
            (K * R ^ ((7 : ℝ) / 4)) := by
      intro x hx
      rw [norm_mul]
      apply mul_le_mul
      · simpa only [D, R] using
          norm_symmetrizedDictionaryWeight_selectedTopEdge_le
            hC N u hc n (Set.uIoc_subset_uIcc hx)
      · simpa only [R] using
          hlog n x (Set.uIoc_subset_uIcc hx)
      · positivity
      · positivity
    have hintegral :=
      intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    rw [dictionaryXiTopHorizontalIntegralFor]
    calc
      ‖∫ x : ℝ in 1 - c..c,
          symmetrizedCompactLaplaceWeight
              (weilFiniteDictionaryPhysicalDensity C N u)
              ((x : ℂ) + dictionaryXiSelectedHeight c n * I) *
            logDeriv riemannXi
              ((x : ℂ) + dictionaryXiSelectedHeight c n * I)‖ ≤
          ((D * R⁻¹ ^ (2 : ℕ)) *
            (K * R ^ ((7 : ℝ) / 4))) * |c - (1 - c)| :=
        hintegral
      _ = B * R ^ (-((1 : ℝ) / 4)) := by
        rw [← hpower]
        dsimp only [B]
        ring
  have hdecay :
      Tendsto
        (fun n : ℕ =>
          (dictionaryXiHeightScale c n) ^ (-((1 : ℝ) / 4)))
        atTop (𝓝 0) := by
    change Tendsto
      ((fun R : ℝ => R ^ (-((1 : ℝ) / 4))) ∘
        dictionaryXiHeightScale c) atTop (𝓝 0)
    exact
      (tendsto_rpow_neg_atTop (by norm_num : 0 < (1 : ℝ) / 4)).comp
        (tendsto_dictionaryXiHeightScale c)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n => norm_nonneg _
  · exact Filter.Eventually.of_forall fun n => hbound n
  · simpa using hdecay.const_mul B

/-- Reflection identifies the long selected bottom horizontal integral with the negative top
integral. -/
theorem dictionaryXiBottomHorizontalIntegral_eq_neg_top
    {F : ℂ → ℂ} (hsym : ∀ z : ℂ, F (1 - z) = F z)
    (c : ℝ) (n : ℕ) :
    (∫ x : ℝ in 1 - c..c,
      F ((x : ℂ) - dictionaryXiSelectedHeight c n * I) *
        logDeriv riemannXi
          ((x : ℂ) - dictionaryXiSelectedHeight c n * I)) =
      -dictionaryXiTopHorizontalIntegralFor F c n := by
  let T : ℝ := dictionaryXiSelectedHeight c n
  let f : ℝ → ℂ := fun x =>
    F ((x : ℂ) + T * I) * logDeriv riemannXi ((x : ℂ) + T * I)
  have hpoint : ∀ x : ℝ,
      F ((x : ℂ) - T * I) * logDeriv riemannXi ((x : ℂ) - T * I) =
        -f (1 - x) := by
    intro x
    have href :=
      selectedXiWeightedLogDeriv_one_sub hsym ((x : ℂ) - T * I)
    have harg :
        (1 : ℂ) - ((x : ℂ) - T * I) =
          ((1 - x : ℝ) : ℂ) + T * I := by
      push_cast
      ring
    rw [harg] at href
    simpa only [f, neg_neg] using (congrArg Neg.neg href).symm
  calc
    (∫ x : ℝ in 1 - c..c,
      F ((x : ℂ) - T * I) * logDeriv riemannXi ((x : ℂ) - T * I)) =
        ∫ x : ℝ in 1 - c..c, -f (1 - x) := by
      apply intervalIntegral.integral_congr
      intro x _hx
      exact hpoint x
    _ = -(∫ x : ℝ in 1 - c..c, f (1 - x)) := by
      rw [intervalIntegral.integral_neg]
    _ = -(∫ x : ℝ in 1 - c..c, f x) := by
      rw [intervalIntegral.integral_comp_sub_left f 1]
      congr 2
      all_goals ring
    _ = -dictionaryXiTopHorizontalIntegralFor F c n := by
      rfl

/-- Reflection and ordinate reversal identify the long selected left vertical integral with the
negative right integral. -/
theorem dictionaryXiLeftVerticalIntegral_eq_neg_right
    {F : ℂ → ℂ} (hsym : ∀ z : ℂ, F (1 - z) = F z)
    (c : ℝ) (n : ℕ) :
    (∫ y : ℝ in
      -dictionaryXiSelectedHeight c n..dictionaryXiSelectedHeight c n,
      F (((1 - c : ℝ) : ℂ) + y * I) *
        logDeriv riemannXi (((1 - c : ℝ) : ℂ) + y * I)) =
      -dictionaryXiRightVerticalIntegralFor F c n := by
  let T : ℝ := dictionaryXiSelectedHeight c n
  let f : ℝ → ℂ := fun y =>
    F ((c : ℂ) + y * I) * logDeriv riemannXi ((c : ℂ) + y * I)
  have hpoint : ∀ y : ℝ,
      F (((1 - c : ℝ) : ℂ) + y * I) *
          logDeriv riemannXi (((1 - c : ℝ) : ℂ) + y * I) =
        -f (-y) := by
    intro y
    have href :=
      selectedXiWeightedLogDeriv_one_sub hsym ((c : ℂ) - y * I)
    have harg :
        (1 : ℂ) - ((c : ℂ) - y * I) =
          ((1 - c : ℝ) : ℂ) + y * I := by
      push_cast
      ring
    rw [harg] at href
    simpa only [f, Complex.ofReal_neg, neg_mul, sub_eq_add_neg, neg_neg]
      using href
  calc
    (∫ y : ℝ in -T..T,
      F (((1 - c : ℝ) : ℂ) + y * I) *
        logDeriv riemannXi (((1 - c : ℝ) : ℂ) + y * I)) =
        ∫ y : ℝ in -T..T, -f (-y) := by
      apply intervalIntegral.integral_congr
      intro y _hy
      exact hpoint y
    _ = -(∫ y : ℝ in -T..T, f (-y)) := by
      rw [intervalIntegral.integral_neg]
    _ = -(∫ y : ℝ in -T..T, f y) := by
      simpa only [zero_sub, neg_neg] using congrArg Neg.neg
        (intervalIntegral.integral_comp_sub_left
          (a := -T) (b := T) f 0)
    _ = -dictionaryXiRightVerticalIntegralFor F c n := by
      rfl

/-- Reflection reduces the long selected rectangle boundary to one top and one right edge. -/
theorem dictionaryXiRectangleBoundary_eq_top_right
    {F : ℂ → ℂ} (hsym : ∀ z : ℂ, F (1 - z) = F z)
    (c : ℝ) (n : ℕ) :
    rectangleBoundaryIntegral (fun z => F z * logDeriv riemannXi z)
        (1 - c) c (-dictionaryXiSelectedHeight c n)
          (dictionaryXiSelectedHeight c n) =
      -2 * dictionaryXiTopHorizontalIntegralFor F c n +
        2 * I * dictionaryXiRightVerticalIntegralFor F c n := by
  let T : ℝ := dictionaryXiSelectedHeight c n
  rw [rectangleBoundaryIntegral]
  simp only [Complex.ofReal_neg]
  rw [show (∫ x : ℝ in 1 - c..c,
      F ((x : ℂ) + (-T) * I) *
        logDeriv riemannXi ((x : ℂ) + (-T) * I)) =
      -dictionaryXiTopHorizontalIntegralFor F c n by
        simpa only [T, neg_mul, sub_eq_add_neg] using
          dictionaryXiBottomHorizontalIntegral_eq_neg_top hsym c n]
  rw [show (∫ x : ℝ in 1 - c..c,
      F ((x : ℂ) + T * I) * logDeriv riemannXi ((x : ℂ) + T * I)) =
      dictionaryXiTopHorizontalIntegralFor F c n by rfl]
  rw [show (∫ y : ℝ in -T..T,
      F ((c : ℂ) + y * I) * logDeriv riemannXi ((c : ℂ) + y * I)) =
      dictionaryXiRightVerticalIntegralFor F c n by rfl]
  rw [show (∫ y : ℝ in -T..T,
      F (((1 - c : ℝ) : ℂ) + y * I) *
        logDeriv riemannXi (((1 - c : ℝ) : ℂ) + y * I)) =
      -dictionaryXiRightVerticalIntegralFor F c n by
        exact dictionaryXiLeftVerticalIntegral_eq_neg_right hsym c n]
  ring

/-- The finite weighted argument principle solved for the long selected right edge. -/
theorem dictionaryXiRightVerticalIntegral_eq_top_add_zeroFinsum
    {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hsym : ∀ z : ℂ, F (1 - z) = F z)
    {c : ℝ} (hc : 1 < c) (n : ℕ) :
    dictionaryXiRightVerticalIntegralFor F c n =
      -I * dictionaryXiTopHorizontalIntegralFor F c n +
        (Real.pi : ℂ) * dictionaryXiRectangleZeroFinsumFor F c n := by
  let T : ℝ := dictionaryXiSelectedHeight c n
  have hTpos : 0 < T :=
    lt_trans (dictionaryXiHeightScale_pos c n)
      (dictionaryXiSelectedHeight_spec c n).1.1
  have hres :=
    rectangleBoundaryIntegral_weighted_logDeriv_riemannXi_eq_finsum hF
      (show 1 - c < c by linarith)
      (show -T < T by linarith)
      (dictionaryXiSelectedHeight_zeroFreeBoundary hc n)
  rw [dictionaryXiRectangleBoundary_eq_top_right hsym] at hres
  change
    -2 * dictionaryXiTopHorizontalIntegralFor F c n +
        2 * I * dictionaryXiRightVerticalIntegralFor F c n =
      2 * (Real.pi : ℂ) * I *
        dictionaryXiRectangleZeroFinsumFor F c n at hres
  have hres' :
      2 * I * dictionaryXiRightVerticalIntegralFor F c n =
        2 * dictionaryXiTopHorizontalIntegralFor F c n +
          2 * (Real.pi : ℂ) * I *
            dictionaryXiRectangleZeroFinsumFor F c n := by
    linear_combination hres
  apply mul_left_cancel₀ (show (2 : ℂ) * I ≠ 0 by simp)
  calc
    ((2 : ℂ) * I) * dictionaryXiRightVerticalIntegralFor F c n =
        2 * I * dictionaryXiRightVerticalIntegralFor F c n := by
      ring
    _ = 2 * dictionaryXiTopHorizontalIntegralFor F c n +
          2 * (Real.pi : ℂ) * I *
            dictionaryXiRectangleZeroFinsumFor F c n := hres'
    _ = ((2 : ℂ) * I) *
        (-I * dictionaryXiTopHorizontalIntegralFor F c n +
          (Real.pi : ℂ) * dictionaryXiRectangleZeroFinsumFor F c n) := by
      calc
        2 * dictionaryXiTopHorizontalIntegralFor F c n +
            2 * (Real.pi : ℂ) * I *
              dictionaryXiRectangleZeroFinsumFor F c n =
          2 * (-(I * I)) * dictionaryXiTopHorizontalIntegralFor F c n +
            2 * (Real.pi : ℂ) * I *
              dictionaryXiRectangleZeroFinsumFor F c n := by
            rw [Complex.I_mul_I]
            ring
        _ = ((2 : ℂ) * I) *
            (-I * dictionaryXiTopHorizontalIntegralFor F c n +
              (Real.pi : ℂ) *
                dictionaryXiRectangleZeroFinsumFor F c n) := by
          ring

/-- Expanding the long symmetric rectangles recovers every absolutely summable xi-zero
weight. -/
theorem tendsto_dictionaryXiRectangleZeroFinsumFor
    {F : ℂ → ℂ}
    (hFsum : Summable (fun p : RiemannXiDivisorZeroIndex =>
      F (riemannXiDivisorZeroValue p)))
    {c : ℝ} (hc : 1 < c) :
    Tendsto (dictionaryXiRectangleZeroFinsumFor F c) atTop
      (𝓝 (∑' p : RiemannXiDivisorZeroIndex,
        F (riemannXiDivisorZeroValue p))) := by
  classical
  let f : ℕ → RiemannXiDivisorZeroIndex → ℂ := fun n p =>
    if riemannXiZeroStrictlyInsideRectangle (1 - c) c
        (-dictionaryXiSelectedHeight c n)
          (dictionaryXiSelectedHeight c n) p then
      F (riemannXiDivisorZeroValue p)
    else 0
  let g : RiemannXiDivisorZeroIndex → ℂ :=
    fun p => F (riemannXiDivisorZeroValue p)
  have hpoint : ∀ p : RiemannXiDivisorZeroIndex,
      Tendsto (fun n => f n p) atTop (𝓝 (g p)) := by
    intro p
    let rho : ℂ := riemannXiDivisorZeroValue p
    have hrho : IsNontrivialZero rho :=
      riemannXiDivisorZeroIndex_val_isNontrivialZero p
    have hreflect : IsNontrivialZero (1 - rho) := by
      rw [isNontrivialZero_iff_riemannXi_eq_zero, riemannXi_one_sub]
      exact (isNontrivialZero_iff_riemannXi_eq_zero rho).mp hrho
    have hre0 : 0 < rho.re := by
      have hreflectRe := nontrivial_zero_re_lt_one hreflect
      simp only [sub_re, one_re] at hreflectRe
      linarith
    have hre1 : rho.re < 1 := nontrivial_zero_re_lt_one hrho
    have hheight :
        ∀ᶠ n : ℕ in atTop, |rho.im| < dictionaryXiSelectedHeight c n :=
      (tendsto_dictionaryXiSelectedHeight c).eventually
        (eventually_gt_atTop |rho.im|)
    apply tendsto_const_nhds.congr'
    filter_upwards [hheight] with n hn
    have hinside :
        riemannXiZeroStrictlyInsideRectangle (1 - c) c
          (-dictionaryXiSelectedHeight c n)
            (dictionaryXiSelectedHeight c n) p := by
      unfold riemannXiZeroStrictlyInsideRectangle
      dsimp only [rho] at hre0 hre1 hn ⊢
      rw [abs_lt] at hn
      constructor
      · linarith
      · constructor
        · linarith
        · constructor <;> linarith
    simp only [f, g, if_pos hinside]
  have hbound :
      ∀ᶠ n : ℕ in atTop, ∀ p : RiemannXiDivisorZeroIndex,
        ‖f n p‖ ≤ ‖g p‖ := by
    filter_upwards [] with n
    intro p
    by_cases hinside :
        riemannXiZeroStrictlyInsideRectangle (1 - c) c
          (-dictionaryXiSelectedHeight c n)
            (dictionaryXiSelectedHeight c n) p
    · simp only [f, g, if_pos hinside]
      exact le_rfl
    · simp only [f, g, if_neg hinside, norm_zero, norm_nonneg]
  have hlim :=
    tendsto_tsum_of_dominated_convergence hFsum.norm hpoint hbound
  have heq :
      (fun n => ∑' p : RiemannXiDivisorZeroIndex, f n p) =
        dictionaryXiRectangleZeroFinsumFor F c := by
    funext n
    change (∑' p : RiemannXiDivisorZeroIndex, f n p) =
      ∑ᶠ p : RiemannXiDivisorZeroIndex, f n p
    rw [tsum_eq_finsum]
    exact hasFiniteSupport_selectedXiRectangleZeroCutoff F
      (1 - c) c (-dictionaryXiSelectedHeight c n)
        (dictionaryXiSelectedHeight c n)
  rw [← heq]
  exact hlim

/-- Long selected-height endpoint for any analytic reflection-symmetric summable weight whose top
edge vanishes. -/
theorem tendsto_dictionaryXiRightVerticalIntegralFor
    {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hsym : ∀ z : ℂ, F (1 - z) = F z)
    (hFsum : Summable (fun p : RiemannXiDivisorZeroIndex =>
      F (riemannXiDivisorZeroValue p)))
    {c : ℝ} (hc : 1 < c)
    (htop : Tendsto (dictionaryXiTopHorizontalIntegralFor F c)
      atTop (𝓝 0)) :
    Tendsto (dictionaryXiRightVerticalIntegralFor F c) atTop
      (𝓝 ((Real.pi : ℂ) *
        ∑' p : RiemannXiDivisorZeroIndex,
          F (riemannXiDivisorZeroValue p))) := by
  have htop' := htop.const_mul (-I)
  have hzero :=
    (tendsto_dictionaryXiRectangleZeroFinsumFor hFsum hc).const_mul
      (Real.pi : ℂ)
  have hcombined := htop'.add hzero
  simpa only [mul_zero, zero_add] using hcombined.congr'
    (Filter.Eventually.of_forall fun n =>
      (dictionaryXiRightVerticalIntegral_eq_top_add_zeroFinsum
        hF hsym hc n).symm)

/-- The long right vertical integral for the finite dictionary converges to its absolutely
convergent multiplicity-bearing xi-zero sum. -/
theorem tendsto_dictionaryXiRightVerticalIntegral
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) {c : ℝ} (hc : 1 < c) :
    Tendsto
      (dictionaryXiRightVerticalIntegralFor
        (symmetrizedCompactLaplaceWeight
          (weilFiniteDictionaryPhysicalDensity C N u)) c)
      atTop
      (𝓝 ((Real.pi : ℂ) *
        ∑' p : RiemannXiDivisorZeroIndex,
          symmetrizedCompactLaplaceWeight
            (weilFiniteDictionaryPhysicalDensity C N u)
            (riemannXiDivisorZeroValue p))) := by
  apply tendsto_dictionaryXiRightVerticalIntegralFor
    (differentiable_symmetrizedCompactLaplaceWeight
      (continuous_weilFiniteDictionaryPhysicalDensity hC N u)
      (hasCompactSupport_weilFiniteDictionaryPhysicalDensity hC N u))
    (symmetrizedCompactLaplaceWeight_one_sub _)
    (summable_symmetrizedCompactLaplaceWeight_weilFiniteDictionary hC N u)
    hc
  exact tendsto_dictionaryXiTopHorizontalIntegral hC N u hc

/-- The finite dictionary weight is integrable on every vertical line under its source-level
inverse-square strip decay. -/
theorem integrable_symmetrizedDictionaryWeight_vertical
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) (c : ℝ) :
    Integrable (fun y : ℝ =>
      symmetrizedCompactLaplaceWeight
        (weilFiniteDictionaryPhysicalDensity C N u)
        ((c : ℂ) + y * I)) := by
  let A : ℝ := |1 / 2 - c|
  let D : ℝ := weilFiniteDictionaryStripDecayConstant C N u A
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hD : 0 ≤ D := by
    dsimp only [D]
    exact weilFiniteDictionaryStripDecayConstant_nonneg hC N u hA
  have hmajorant :
      Integrable (fun y : ℝ => D * (1 + |y|) ^ (-(2 : ℝ))) := by
    have hbase :
        Integrable (fun y : ℝ => (1 + ‖y‖) ^ (-(2 : ℝ))) :=
      integrable_one_add_norm (E := ℝ) (r := (2 : ℝ)) (by norm_num)
    simpa only [Real.norm_eq_abs] using hbase.const_mul D
  have hcontinuous : Continuous (fun y : ℝ =>
      symmetrizedCompactLaplaceWeight
        (weilFiniteDictionaryPhysicalDensity C N u)
        ((c : ℂ) + y * I)) :=
    (differentiable_symmetrizedCompactLaplaceWeight
      (continuous_weilFiniteDictionaryPhysicalDensity hC N u)
      (hasCompactSupport_weilFiniteDictionaryPhysicalDensity hC N u)).continuous.comp
        (by fun_prop)
  refine MeasureTheory.Integrable.mono' hmajorant
    hcontinuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  let s : ℂ := (c : ℂ) + y * I
  let z : ℂ := (s - 1 / 2) / I
  have hzIm : |z.im| ≤ A := by
    dsimp only [z]
    rw [weilFiniteDictionaryZeroCoordinate_im]
    dsimp only [s, A]
    simp
  have hstrip :=
    norm_weilFiniteDictionaryTest_le_stripDecay hC N u hA hzIm
  have hzRe : z.re = y := by
    dsimp only [z]
    rw [weilFiniteDictionaryZeroCoordinate_re]
    dsimp only [s]
    simp
  have hpow :
      (1 + |y|)⁻¹ ^ (2 : ℕ) =
        (1 + |y|) ^ (-(2 : ℝ)) := by
    rw [Real.rpow_neg (by positivity), Real.rpow_two]
    exact inv_pow (1 + |y|) 2
  rw [symmetrizedCompactLaplaceWeight_weilFiniteDictionaryPhysicalDensity hC,
    ← weilFiniteDictionaryTest_zeroCoordinate hC]
  simpa only [D, hzRe, hpow] using hstrip

/-- The source-level strip estimate, exposed pointwise on a vertical line. -/
theorem norm_symmetrizedDictionaryWeight_vertical_le
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) (c y : ℝ) :
    ‖symmetrizedCompactLaplaceWeight
        (weilFiniteDictionaryPhysicalDensity C N u)
        ((c : ℂ) + y * I)‖ ≤
      weilFiniteDictionaryStripDecayConstant C N u |1 / 2 - c| *
        (1 + |y|) ^ (-(2 : ℝ)) := by
  let A : ℝ := |1 / 2 - c|
  let s : ℂ := (c : ℂ) + y * I
  let z : ℂ := (s - 1 / 2) / I
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hzIm : |z.im| ≤ A := by
    dsimp only [z]
    rw [weilFiniteDictionaryZeroCoordinate_im]
    dsimp only [s, A]
    simp
  have hstrip :=
    norm_weilFiniteDictionaryTest_le_stripDecay hC N u hA hzIm
  have hzRe : z.re = y := by
    dsimp only [z]
    rw [weilFiniteDictionaryZeroCoordinate_re]
    dsimp only [s]
    simp
  have hpow :
      (1 + |y|)⁻¹ ^ (2 : ℕ) =
        (1 + |y|) ^ (-(2 : ℝ)) := by
    rw [Real.rpow_neg (by positivity), Real.rpow_two]
    exact inv_pow (1 + |y|) 2
  rw [symmetrizedCompactLaplaceWeight_weilFiniteDictionaryPhysicalDensity hC,
    ← weilFiniteDictionaryTest_zeroCoordinate hC]
  simpa only [A, hzRe, hpow] using hstrip

/-- Fourier inversion needs only continuity, compact support, and integrability of the Fourier
transform; the old six-derivative hypothesis was one sufficient route to the last condition. -/
theorem integral_fourier_compactLaplaceDensity_mul_exp_of_integrable
    {f : ℝ → ℂ} (hf : Continuous f) (hfsupp : HasCompactSupport f)
    (c : ℝ) (hfourier : Integrable (𝓕 (compactLaplaceFourierDensity f c)))
    (t : ℝ) :
    (∫ w : ℝ,
      𝓕 (compactLaplaceFourierDensity f c) w *
        Complex.exp (((2 * Real.pi * w * t : ℝ) : ℂ) * I)) =
      compactLaplaceFourierDensity f c t := by
  have hcont : Continuous (compactLaplaceFourierDensity f c) := by
    unfold compactLaplaceFourierDensity
    exact ((continuous_const.mul Complex.continuous_ofReal).cexp).mul hf
  have hint : Integrable (compactLaplaceFourierDensity f c) :=
    hcont.integrable_of_hasCompactSupport
      (hasCompactSupport_compactLaplaceFourierDensity hfsupp c)
  have hinv :=
    hint.fourierInv_fourier_eq hfourier hcont.continuousAt (v := t)
  rw [Real.fourierInv_eq'] at hinv
  simp only [RCLike.inner_apply, conj_trivial, ofReal_mul, smul_eq_mul] at hinv
  rw [← hinv]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with w
  rw [mul_comm]
  congr 2
  push_cast
  ring

/-- The exponentially weighted finite dictionary density has an integrable Fourier transform on
every vertical line. -/
theorem integrable_fourier_compactLaplaceDensity_dictionary
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) (c : ℝ) :
    Integrable
      (𝓕 (compactLaplaceFourierDensity
        (weilFiniteDictionaryPhysicalDensity C N u) c)) := by
  let f : ℝ → ℂ := weilFiniteDictionaryPhysicalDensity C N u
  have hvertical : Integrable (fun y : ℝ =>
      compactLaplaceTransform f ((c : ℂ) + y * I)) := by
    have h :=
      integrable_symmetrizedDictionaryWeight_vertical hC N u c
    apply h.congr
    filter_upwards [] with y
    exact
      symmetrizedCompactLaplaceWeight_weilFiniteDictionaryPhysicalDensity
        hC N u ((c : ℂ) + y * I)
  let a : ℝ := -2 * Real.pi
  have ha : a ≠ 0 :=
    mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hscaled :=
    hvertical.comp_mul_left' ha
  apply hscaled.congr
  filter_upwards [] with w
  rw [compactLaplaceTransform_vertical_eq_fourier]
  apply congrArg (𝓕 (compactLaplaceFourierDensity f c))
  dsimp only [a]
  field_simp [Real.pi_ne_zero]

/-- Weak-regularity inverse Fourier evaluation for the first finite-dictionary Laplace branch. -/
theorem integral_dictionaryCompactLaplaceTransform_vertical_mul_exp_neg
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) (c t : ℝ) :
    (∫ y : ℝ,
      compactLaplaceTransform
          (weilFiniteDictionaryPhysicalDensity C N u)
          ((c : ℂ) + y * I) *
        Complex.exp (-((y * t : ℝ) : ℂ) * I)) =
      ((2 * Real.pi : ℝ) : ℂ) *
        compactLaplaceFourierDensity
          (weilFiniteDictionaryPhysicalDensity C N u) c t := by
  let f : ℝ → ℂ := weilFiniteDictionaryPhysicalDensity C N u
  let K : ℝ → ℂ := fun w =>
    𝓕 (compactLaplaceFourierDensity f c) w *
      Complex.exp (((2 * Real.pi * w * t : ℝ) : ℂ) * I)
  let a : ℝ := -(2 * Real.pi)⁻¹
  have hscale := Measure.integral_comp_mul_left K a
  have haInv : |a⁻¹| = 2 * Real.pi := by
    dsimp only [a]
    rw [inv_neg, inv_inv, abs_neg, abs_of_pos]
    positivity
  have hK :
      (∫ w : ℝ, K w) = compactLaplaceFourierDensity f c t := by
    simpa only [K] using
      integral_fourier_compactLaplaceDensity_mul_exp_of_integrable
        (continuous_weilFiniteDictionaryPhysicalDensity hC N u)
        (hasCompactSupport_weilFiniteDictionaryPhysicalDensity hC N u)
        c (integrable_fourier_compactLaplaceDensity_dictionary hC N u c) t
  calc
    (∫ y : ℝ,
      compactLaplaceTransform f ((c : ℂ) + y * I) *
        Complex.exp (-((y * t : ℝ) : ℂ) * I)) =
        ∫ y : ℝ, K (a * y) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with y
      rw [compactLaplaceTransform_vertical_eq_fourier]
      dsimp only [K, a]
      congr 2
      · field_simp [Real.pi_ne_zero]
      · congr 1
        push_cast
        field_simp [Real.pi_ne_zero]
    _ = |a⁻¹| • ∫ w : ℝ, K w := hscale
    _ = ((2 * Real.pi : ℝ) : ℂ) *
        compactLaplaceFourierDensity f c t := by
      rw [haInv, hK]
      simp only [Complex.real_smul]

/-- The reflected finite-dictionary Laplace branch evaluates at the opposite physical point. -/
theorem integral_dictionaryCompactLaplaceTransform_reflected_vertical_mul_exp_neg
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) (c t : ℝ) :
    (∫ y : ℝ,
      compactLaplaceTransform
          (weilFiniteDictionaryPhysicalDensity C N u)
          (1 - ((c : ℂ) + y * I)) *
        Complex.exp (-((y * t : ℝ) : ℂ) * I)) =
      ((2 * Real.pi : ℝ) : ℂ) *
        compactLaplaceFourierDensity
          (weilFiniteDictionaryPhysicalDensity C N u) (1 - c) (-t) := by
  let f : ℝ → ℂ := weilFiniteDictionaryPhysicalDensity C N u
  let H : ℝ → ℂ := fun v =>
    compactLaplaceTransform f (((1 - c : ℝ) : ℂ) + v * I) *
      Complex.exp (-((v * (-t) : ℝ) : ℂ) * I)
  have hneg := Measure.integral_comp_mul_left H (-1)
  have hneg' : (∫ y : ℝ, H (-y)) = ∫ v : ℝ, H v := by
    simpa only [neg_mul, one_mul, inv_neg, inv_one, abs_neg, abs_one, one_smul]
      using hneg
  calc
    (∫ y : ℝ,
      compactLaplaceTransform f (1 - ((c : ℂ) + y * I)) *
        Complex.exp (-((y * t : ℝ) : ℂ) * I)) =
        ∫ y : ℝ, H (-y) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with y
      dsimp only [H]
      congr 2
      · push_cast
        ring
      · congr 1
        push_cast
        ring
    _ = ∫ v : ℝ, H v := hneg'
    _ = ((2 * Real.pi : ℝ) : ℂ) *
        compactLaplaceFourierDensity f (1 - c) (-t) := by
      simpa only [H] using
        integral_dictionaryCompactLaplaceTransform_vertical_mul_exp_neg
          hC N u (1 - c) (-t)

/-- The first finite-dictionary Laplace branch remains integrable after multiplication by a
unit-modulus Fourier phase. -/
theorem integrable_dictionaryCompactLaplaceTransform_vertical_mul_exp_neg
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) (c t : ℝ) :
    Integrable (fun y : ℝ =>
      compactLaplaceTransform
          (weilFiniteDictionaryPhysicalDensity C N u)
          ((c : ℂ) + y * I) *
        Complex.exp (-((y * t : ℝ) : ℂ) * I)) := by
  have hvertical : Integrable (fun y : ℝ =>
      compactLaplaceTransform
          (weilFiniteDictionaryPhysicalDensity C N u)
          ((c : ℂ) + y * I)) := by
    have h :=
      integrable_symmetrizedDictionaryWeight_vertical hC N u c
    apply h.congr
    filter_upwards [] with y
    exact
      symmetrizedCompactLaplaceWeight_weilFiniteDictionaryPhysicalDensity
        hC N u ((c : ℂ) + y * I)
  have hphaseMeasurable : AEStronglyMeasurable (fun y : ℝ =>
      Complex.exp (-((y * t : ℝ) : ℂ) * I)) :=
    (by fun_prop : Continuous (fun y : ℝ =>
      Complex.exp (-((y * t : ℝ) : ℂ) * I))).aestronglyMeasurable
  have hphaseBound :
      ∀ᶠ y : ℝ in ae volume,
        ‖Complex.exp (-((y * t : ℝ) : ℂ) * I)‖ ≤ 1 := by
    filter_upwards [] with y
    rw [Complex.norm_exp]
    norm_num [mul_re]
  have hproduct := hvertical.bdd_mul hphaseMeasurable hphaseBound
  apply hproduct.congr
  filter_upwards [] with y
  ring

/-- The reflected finite-dictionary branch has the same phase-preserving integrability. -/
theorem integrable_dictionaryCompactLaplaceTransform_reflected_vertical_mul_exp_neg
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) (c t : ℝ) :
    Integrable (fun y : ℝ =>
      compactLaplaceTransform
          (weilFiniteDictionaryPhysicalDensity C N u)
          (1 - ((c : ℂ) + y * I)) *
        Complex.exp (-((y * t : ℝ) : ℂ) * I)) := by
  let H : ℝ → ℂ := fun v =>
    compactLaplaceTransform
        (weilFiniteDictionaryPhysicalDensity C N u)
        (((1 - c : ℝ) : ℂ) + v * I) *
      Complex.exp (-((v * (-t) : ℝ) : ℂ) * I)
  have hH : Integrable H := by
    simpa only [H] using
      integrable_dictionaryCompactLaplaceTransform_vertical_mul_exp_neg
        hC N u (1 - c) (-t)
  have hHneg : Integrable (fun y : ℝ => H (-1 * y)) :=
    hH.comp_mul_left' (by norm_num)
  apply hHneg.congr
  filter_upwards [] with y
  dsimp only [H]
  congr 2
  · push_cast
    ring
  · congr 1
    push_cast
    ring

open scoped LSeries.notation in
/-- Every individual finite-dictionary von-Mangoldt line term is integrable. -/
theorem integrable_compactSymmetrizedXiPrimeLineTerm_dictionary
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) (c : ℝ) (n : ℕ) :
    Integrable
      (compactSymmetrizedXiPrimeLineTerm
        (weilFiniteDictionaryPhysicalDensity C N u) c n) := by
  by_cases hn : n = 0
  · subst n
    have hzero :
        compactSymmetrizedXiPrimeLineTerm
            (weilFiniteDictionaryPhysicalDensity C N u) c 0 = 0 := by
      funext y
      simp [compactSymmetrizedXiPrimeLineTerm, LSeries.term_zero]
    rw [hzero]
    exact MeasureTheory.integrable_zero ℝ ℂ volume
  let D : ℂ := (ArithmeticFunction.vonMangoldt n : ℂ) *
    Complex.exp ((-(c * Real.log n) : ℝ) : ℂ) / 2
  let A : ℝ → ℂ := fun y =>
    compactLaplaceTransform
        (weilFiniteDictionaryPhysicalDensity C N u)
        ((c : ℂ) + y * I) *
      Complex.exp (-((y * Real.log n : ℝ) : ℂ) * I)
  let B : ℝ → ℂ := fun y =>
    compactLaplaceTransform
        (weilFiniteDictionaryPhysicalDensity C N u)
        (1 - ((c : ℂ) + y * I)) *
      Complex.exp (-((y * Real.log n : ℝ) : ℂ) * I)
  have hA : Integrable A := by
    simpa only [A] using
      integrable_dictionaryCompactLaplaceTransform_vertical_mul_exp_neg
        hC N u c (Real.log n)
  have hB : Integrable B := by
    simpa only [B] using
      integrable_dictionaryCompactLaplaceTransform_reflected_vertical_mul_exp_neg
        hC N u c (Real.log n)
  have hDAB : Integrable (fun y => D * (A y + B y)) :=
    (hA.add hB).const_mul D
  apply hDAB.congr
  filter_upwards [] with y
  rw [compactSymmetrizedXiPrimeLineTerm_vertical hn]

open scoped LSeries.notation in
/-- One finite-dictionary prime term evaluates to its exact two-branch physical weight under the
weak Fourier inversion hypotheses. -/
theorem integral_compactSymmetrizedXiPrimeLineTerm_dictionary
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) (c : ℝ) (n : ℕ) :
    (∫ y : ℝ,
      compactSymmetrizedXiPrimeLineTerm
        (weilFiniteDictionaryPhysicalDensity C N u) c n y) =
      compactSymmetrizedVonMangoldtWeight
        (weilFiniteDictionaryPhysicalDensity C N u) n := by
  by_cases hn : n = 0
  · subst n
    simp [compactSymmetrizedXiPrimeLineTerm,
      compactSymmetrizedVonMangoldtWeight, LSeries.term_zero]
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  let D : ℂ := (ArithmeticFunction.vonMangoldt n : ℂ) *
    Complex.exp ((-(c * Real.log n) : ℝ) : ℂ) / 2
  let A : ℝ → ℂ := fun y =>
    compactLaplaceTransform
        (weilFiniteDictionaryPhysicalDensity C N u)
        ((c : ℂ) + y * I) *
      Complex.exp (-((y * Real.log n : ℝ) : ℂ) * I)
  let B : ℝ → ℂ := fun y =>
    compactLaplaceTransform
        (weilFiniteDictionaryPhysicalDensity C N u)
        (1 - ((c : ℂ) + y * I)) *
      Complex.exp (-((y * Real.log n : ℝ) : ℂ) * I)
  have hA : Integrable A := by
    simpa only [A] using
      integrable_dictionaryCompactLaplaceTransform_vertical_mul_exp_neg
        hC N u c (Real.log n)
  have hB : Integrable B := by
    simpa only [B] using
      integrable_dictionaryCompactLaplaceTransform_reflected_vertical_mul_exp_neg
        hC N u c (Real.log n)
  have hfirst :
      Complex.exp ((-(c * Real.log n) : ℝ) : ℂ) *
          Complex.exp ((c : ℂ) * (Real.log n : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 2
    push_cast
    ring
  have hsecond :
      Complex.exp ((-(c * Real.log n) : ℝ) : ℂ) *
          Complex.exp
            (((1 - c : ℝ) : ℂ) * ((-Real.log n : ℝ) : ℂ)) =
        (n : ℂ)⁻¹ := by
    rw [← Complex.exp_add]
    have harg :
        ((-(c * Real.log n) : ℝ) : ℂ) +
            ((1 - c : ℝ) : ℂ) * ((-Real.log n : ℝ) : ℂ) =
          ((-Real.log n : ℝ) : ℂ) := by
      push_cast
      ring
    rw [harg, ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log hnpos]
    exact Complex.ofReal_inv (n : ℝ)
  have hterm :
      compactSymmetrizedXiPrimeLineTerm
          (weilFiniteDictionaryPhysicalDensity C N u) c n =
        fun y => D * (A y + B y) := by
    funext y
    rw [compactSymmetrizedXiPrimeLineTerm_vertical hn]
  rw [hterm, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_add hA hB]
  rw [show (∫ y : ℝ, A y) =
      ((2 * Real.pi : ℝ) : ℂ) *
        compactLaplaceFourierDensity
          (weilFiniteDictionaryPhysicalDensity C N u) c
          (Real.log n) by
    simpa only [A] using
      integral_dictionaryCompactLaplaceTransform_vertical_mul_exp_neg
        hC N u c (Real.log n)]
  rw [show (∫ y : ℝ, B y) =
      ((2 * Real.pi : ℝ) : ℂ) *
        compactLaplaceFourierDensity
          (weilFiniteDictionaryPhysicalDensity C N u) (1 - c)
          (-Real.log n) by
    simpa only [B] using
      integral_dictionaryCompactLaplaceTransform_reflected_vertical_mul_exp_neg
        hC N u c (Real.log n)]
  unfold D compactLaplaceFourierDensity compactSymmetrizedVonMangoldtWeight
  calc
    ((ArithmeticFunction.vonMangoldt n : ℂ) *
          Complex.exp ((-(c * Real.log n) : ℝ) : ℂ) / 2) *
        (((2 * Real.pi : ℝ) : ℂ) *
            (Complex.exp ((c : ℂ) * (Real.log n : ℂ)) *
              weilFiniteDictionaryPhysicalDensity C N u (Real.log n)) +
          ((2 * Real.pi : ℝ) : ℂ) *
            (Complex.exp
                (((1 - c : ℝ) : ℂ) * ((-Real.log n : ℝ) : ℂ)) *
              weilFiniteDictionaryPhysicalDensity C N u (-Real.log n))) =
        (Real.pi : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) *
          ((Complex.exp ((-(c * Real.log n) : ℝ) : ℂ) *
              Complex.exp ((c : ℂ) * (Real.log n : ℂ))) *
                weilFiniteDictionaryPhysicalDensity C N u (Real.log n) +
            (Complex.exp ((-(c * Real.log n) : ℝ) : ℂ) *
              Complex.exp
                (((1 - c : ℝ) : ℂ) * ((-Real.log n : ℝ) : ℂ))) *
                weilFiniteDictionaryPhysicalDensity C N u (-Real.log n)) := by
      push_cast
      ring
    _ = (Real.pi : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) *
        (weilFiniteDictionaryPhysicalDensity C N u (Real.log n) +
          weilFiniteDictionaryPhysicalDensity C N u (-Real.log n) /
            (n : ℂ)) := by
      rw [hfirst, hsecond]
      simp only [one_mul, div_eq_mul_inv]
      ring

open scoped LSeries.notation in
/-- Absolute series/integral interchange identifies the whole dictionary prime line with the
finite physical von-Mangoldt sum. -/
theorem hasSum_integral_compactSymmetrizedXiPrimeLineTerm_dictionary
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) {c : ℝ} (hc : 1 < c) :
    HasSum
      (compactSymmetrizedVonMangoldtWeight
        (weilFiniteDictionaryPhysicalDensity C N u))
      (∫ y : ℝ, ∑' n : ℕ,
        compactSymmetrizedXiPrimeLineTerm
          (weilFiniteDictionaryPhysicalDensity C N u) c n y) := by
  refine
    (MeasureTheory.hasSum_integral_of_summable_integral_norm
      (fun n : ℕ =>
        integrable_compactSymmetrizedXiPrimeLineTerm_dictionary
          hC N u c n)
      (summable_integral_norm_compactSymmetrizedXiPrimeLineTerm hc)).congr_fun
        ?_
  intro n
  exact
    (integral_compactSymmetrizedXiPrimeLineTerm_dictionary
      hC N u c n).symm

open scoped LSeries.notation in
/-- The finite dictionary prime line integral equals the physical von-Mangoldt `tsum`. -/
theorem tsum_compactSymmetrizedVonMangoldtWeight_dictionary_eq_integral
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) {c : ℝ} (hc : 1 < c) :
    (∑' n : ℕ,
      compactSymmetrizedVonMangoldtWeight
        (weilFiniteDictionaryPhysicalDensity C N u) n) =
      ∫ y : ℝ,
        symmetrizedCompactLaplaceWeight
            (weilFiniteDictionaryPhysicalDensity C N u)
            ((c : ℂ) + y * I) *
          L ↗ArithmeticFunction.vonMangoldt ((c : ℂ) + y * I) := by
  calc
    (∑' n : ℕ,
      compactSymmetrizedVonMangoldtWeight
        (weilFiniteDictionaryPhysicalDensity C N u) n) =
        ∫ y : ℝ, ∑' n : ℕ,
          compactSymmetrizedXiPrimeLineTerm
            (weilFiniteDictionaryPhysicalDensity C N u) c n y :=
      (hasSum_integral_compactSymmetrizedXiPrimeLineTerm_dictionary
        hC N u hc).tsum_eq
    _ = _ := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall
        (tsum_compactSymmetrizedXiPrimeLineTerm
          (weilFiniteDictionaryPhysicalDensity C N u) c)

open scoped LSeries.notation in
/-- The complete finite-dictionary prime-line integrand is integrable under inverse-square
vertical decay. -/
theorem integrable_symmetrizedDictionaryWeight_mul_vonMangoldtLSeries
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) {c : ℝ} (hc : 1 < c) :
    Integrable (fun y : ℝ =>
      symmetrizedCompactLaplaceWeight
          (weilFiniteDictionaryPhysicalDensity C N u)
          ((c : ℂ) + y * I) *
        L ↗ArithmeticFunction.vonMangoldt ((c : ℂ) + y * I)) := by
  let f : ℝ → ℂ := weilFiniteDictionaryPhysicalDensity C N u
  let S : ℝ := ∑' n : ℕ,
    ‖LSeries.term
      (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
      (c : ℂ) n‖
  have hterms : ∀ n : ℕ,
      AEStronglyMeasurable (compactSymmetrizedXiPrimeLineTerm f c n) :=
    fun n =>
      (integrable_compactSymmetrizedXiPrimeLineTerm_dictionary
        hC N u c n).aestronglyMeasurable
  have hsumMeasurable : AEStronglyMeasurable
      (fun y : ℝ => ∑' n : ℕ,
        compactSymmetrizedXiPrimeLineTerm f c n y) :=
    MeasureTheory.AEStronglyMeasurable.tsum hterms
  have hpoint (y : ℝ) :
      ‖∑' n : ℕ, compactSymmetrizedXiPrimeLineTerm f c n y‖ ≤
        S * ‖symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I)‖ := by
    have hsum :
        Summable (fun n : ℕ =>
          compactSymmetrizedXiPrimeLineTerm f c n y) := by
      unfold compactSymmetrizedXiPrimeLineTerm
      exact Summable.mul_left _
        (ArithmeticFunction.LSeriesSummable_vonMangoldt
          (by simpa using hc))
    calc
      ‖∑' n : ℕ, compactSymmetrizedXiPrimeLineTerm f c n y‖ ≤
          ∑' n : ℕ, ‖compactSymmetrizedXiPrimeLineTerm f c n y‖ :=
        norm_tsum_le_tsum_norm hsum.norm
      _ = ∑' n : ℕ,
          ‖symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I)‖ *
            ‖LSeries.term
              (fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℂ))
              (c : ℂ) n‖ := by
        congr 1
        funext n
        rw [norm_compactSymmetrizedXiPrimeLineTerm]
      _ = ‖symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I)‖ * S :=
        tsum_mul_left
      _ = S *
          ‖symmetrizedCompactLaplaceWeight f ((c : ℂ) + y * I)‖ := by
        ring
  have hsumInt : Integrable
      (fun y : ℝ => ∑' n : ℕ,
        compactSymmetrizedXiPrimeLineTerm f c n y) := by
    refine MeasureTheory.Integrable.mono'
      ((integrable_symmetrizedDictionaryWeight_vertical hC N u c).norm.const_mul S)
      hsumMeasurable (Filter.Eventually.of_forall hpoint)
  apply hsumInt.congr
  exact Filter.Eventually.of_forall
    (tsum_compactSymmetrizedXiPrimeLineTerm f c)

/-- Every integrable function is recovered along the long dictionary selected symmetric
heights. -/
theorem tendsto_dictionaryXiSymmetricIntervalIntegral
    {c : ℝ} {f : ℝ → ℂ} (hf : Integrable f) :
    Tendsto
      (fun n : ℕ => ∫ y : ℝ in
        -dictionaryXiSelectedHeight c n..dictionaryXiSelectedHeight c n,
          f y)
      atTop (𝓝 (∫ y : ℝ, f y)) := by
  have hlim := intervalIntegral_tendsto_integral hf
    (tendsto_neg_atTop_atBot.comp
      (tendsto_dictionaryXiSelectedHeight c))
    (tendsto_dictionaryXiSelectedHeight c)
  simpa only [Function.comp_apply] using hlim

open scoped LSeries.notation in
/-- The truncated finite-dictionary prime integrals converge to the finite physical
von-Mangoldt sum. -/
theorem tendsto_dictionaryXiPrimeIntegral
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) {c : ℝ} (hc : 1 < c) :
    Tendsto
      (fun n : ℕ => ∫ y : ℝ in
        -dictionaryXiSelectedHeight c n..dictionaryXiSelectedHeight c n,
          symmetrizedCompactLaplaceWeight
              (weilFiniteDictionaryPhysicalDensity C N u)
              ((c : ℂ) + y * I) *
            L ↗ArithmeticFunction.vonMangoldt ((c : ℂ) + y * I))
      atTop
      (𝓝 (∑' n : ℕ,
        compactSymmetrizedVonMangoldtWeight
          (weilFiniteDictionaryPhysicalDensity C N u) n)) := by
  rw [tsum_compactSymmetrizedVonMangoldtWeight_dictionary_eq_integral
    hC N u hc]
  exact tendsto_dictionaryXiSymmetricIntervalIntegral
    (integrable_symmetrizedDictionaryWeight_mul_vonMangoldtLSeries
      hC N u hc)

/-- The elementary pole pair is integrable against the inverse-square finite dictionary
weight. -/
theorem integrable_dictionaryXiPolePair
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) {c : ℝ} (hc : 1 < c) :
    Integrable (fun y : ℝ =>
      selectedXiPolePairIntegrandFor
        (symmetrizedCompactLaplaceWeight
          (weilFiniteDictionaryPhysicalDensity C N u))
        ((c : ℂ) + y * I)) := by
  let F : ℂ → ℂ :=
    symmetrizedCompactLaplaceWeight
      (weilFiniteDictionaryPhysicalDensity C N u)
  have hweight : Integrable (fun y : ℝ => F ((c : ℂ) + y * I)) :=
    integrable_symmetrizedDictionaryWeight_vertical hC N u c
  have hweightContinuous : Continuous (fun y : ℝ =>
      F ((c : ℂ) + y * I)) :=
    (differentiable_symmetrizedCompactLaplaceWeight
      (continuous_weilFiniteDictionaryPhysicalDensity hC N u)
      (hasCompactSupport_weilFiniteDictionaryPhysicalDensity hC N u)).continuous.comp
        (by fun_prop)
  have hcontinuous : Continuous (fun y : ℝ =>
      selectedXiPolePairIntegrandFor F ((c : ℂ) + y * I)) := by
    unfold selectedXiPolePairIntegrandFor
    apply Continuous.add
    · apply Continuous.div hweightContinuous (by fun_prop)
      intro y hzero
      have hre := congrArg Complex.re hzero
      simp at hre
      linarith
    · apply Continuous.div hweightContinuous (by fun_prop)
      intro y hzero
      have hre := congrArg Complex.re hzero
      simp at hre
      linarith
  refine MeasureTheory.Integrable.mono'
    (hweight.norm.const_mul (c⁻¹ + (c - 1)⁻¹))
    hcontinuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  unfold selectedXiPolePairIntegrandFor
  simp only [sub_zero, div_eq_mul_inv]
  calc
    ‖F ((c : ℂ) + y * I) * ((c : ℂ) + y * I)⁻¹ +
        F ((c : ℂ) + y * I) * ((c : ℂ) + y * I - 1)⁻¹‖ ≤
      ‖F ((c : ℂ) + y * I)‖ * ‖((c : ℂ) + y * I)⁻¹‖ +
        ‖F ((c : ℂ) + y * I)‖ *
          ‖((c : ℂ) + y * I - 1)⁻¹‖ := by
      simpa only [norm_mul] using norm_add_le
        (F ((c : ℂ) + y * I) * ((c : ℂ) + y * I)⁻¹)
        (F ((c : ℂ) + y * I) * ((c : ℂ) + y * I - 1)⁻¹)
    _ ≤ ‖F ((c : ℂ) + y * I)‖ * c⁻¹ +
        ‖F ((c : ℂ) + y * I)‖ * (c - 1)⁻¹ := by
      gcongr
      · simpa using
          norm_inv_vertical_sub_real_le (rho := 0) (y := y) (by linarith)
      · simpa using
          norm_inv_vertical_sub_real_le (rho := 1) (y := y) (by linarith)
    _ = (c⁻¹ + (c - 1)⁻¹) * ‖F ((c : ℂ) + y * I)‖ := by
      ring

/-- The dictionary weight has inverse-square decay on the original selected heights as well; this
is used only to reuse the already compiled two-pole residue contour. -/
theorem norm_symmetrizedDictionaryWeight_gaussianSelectedTopEdge_le
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) {c : ℝ} (hc : 1 < c)
    (n : ℕ) {x : ℝ} (hx : x ∈ [[1 - c, c]]) :
    ‖symmetrizedCompactLaplaceWeight
        (weilFiniteDictionaryPhysicalDensity C N u)
        ((x : ℂ) + gaussianXiSelectedHeight c n * I)‖ ≤
      weilFiniteDictionaryStripDecayConstant C N u (c - 1 / 2) *
        (gaussianXiHeightScale c n)⁻¹ ^ (2 : ℕ) := by
  have hlr : 1 - c ≤ c := by linarith
  rw [uIcc_of_le hlr] at hx
  let s : ℂ := (x : ℂ) + gaussianXiSelectedHeight c n * I
  let z : ℂ := (s - 1 / 2) / I
  have hA : 0 ≤ c - 1 / 2 := by linarith
  have hzIm : |z.im| ≤ c - 1 / 2 := by
    dsimp only [z]
    rw [weilFiniteDictionaryZeroCoordinate_im]
    dsimp only [s]
    simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero]
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2]
  have hstrip :=
    norm_weilFiniteDictionaryTest_le_stripDecay hC N u hA hzIm
  have hzRe : z.re = gaussianXiSelectedHeight c n := by
    dsimp only [z]
    rw [weilFiniteDictionaryZeroCoordinate_re]
    dsimp only [s]
    simp
  have hTpos : 0 < gaussianXiSelectedHeight c n :=
    lt_trans (gaussianXiHeightScale_pos hc n)
      (gaussianXiSelectedHeight_spec c n).1.1
  have hinv :
      (1 + |z.re|)⁻¹ ≤ (gaussianXiHeightScale c n)⁻¹ := by
    rw [hzRe, abs_of_pos hTpos]
    simpa only [one_div] using one_div_le_one_div_of_le
      (gaussianXiHeightScale_pos hc n)
      (by
        have hT := (gaussianXiSelectedHeight_spec c n).1.1
        linarith)
  rw [symmetrizedCompactLaplaceWeight_weilFiniteDictionaryPhysicalDensity hC,
    ← weilFiniteDictionaryTest_zeroCoordinate hC]
  exact hstrip.trans
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (inv_nonneg.mpr (by positivity)) hinv 2)
      (weilFiniteDictionaryStripDecayConstant_nonneg hC N u hA))

/-- The original selected pole top integral vanishes for the finite dictionary under its
inverse-square decay. -/
theorem tendsto_selectedDictionaryXiPoleTopHorizontalIntegral
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) {c : ℝ} (hc : 1 < c) :
    Tendsto
      (selectedXiPoleTopHorizontalIntegralFor
        (symmetrizedCompactLaplaceWeight
          (weilFiniteDictionaryPhysicalDensity C N u)) c)
      atTop (𝓝 0) := by
  let D : ℝ :=
    weilFiniteDictionaryStripDecayConstant C N u (c - 1 / 2)
  let B : ℝ := 2 * D * |c - (1 - c)|
  have hD : 0 ≤ D := by
    dsimp only [D]
    exact weilFiniteDictionaryStripDecayConstant_nonneg
      hC N u (by linarith)
  have hbound :
      ∀ n : ℕ,
        ‖selectedXiPoleTopHorizontalIntegralFor
            (symmetrizedCompactLaplaceWeight
              (weilFiniteDictionaryPhysicalDensity C N u)) c n‖ ≤
          B * (gaussianXiHeightScale c n)⁻¹ ^ (2 : ℕ) := by
    intro n
    let R : ℝ := gaussianXiHeightScale c n
    let T : ℝ := gaussianXiSelectedHeight c n
    have hTone : 1 ≤ T := by
      have hRtwo : 2 < R := by
        dsimp only [R, gaussianXiHeightScale]
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      have hRT := (gaussianXiSelectedHeight_spec c n).1.1
      linarith
    have hpoint : ∀ x ∈ Ι (1 - c) c,
        ‖selectedXiPolePairIntegrandFor
          (symmetrizedCompactLaplaceWeight
            (weilFiniteDictionaryPhysicalDensity C N u))
          ((x : ℂ) + T * I)‖ ≤
          2 * (D * R⁻¹ ^ (2 : ℕ)) := by
      intro x hx
      calc
        ‖selectedXiPolePairIntegrandFor
          (symmetrizedCompactLaplaceWeight
            (weilFiniteDictionaryPhysicalDensity C N u))
          ((x : ℂ) + T * I)‖ ≤
            2 * ‖symmetrizedCompactLaplaceWeight
              (weilFiniteDictionaryPhysicalDensity C N u)
              ((x : ℂ) + T * I)‖ :=
          norm_selectedXiPolePairIntegrandFor_horizontal_le hTone
        _ ≤ 2 * (D * R⁻¹ ^ (2 : ℕ)) := by
          gcongr
          simpa only [D, R, T] using
            norm_symmetrizedDictionaryWeight_gaussianSelectedTopEdge_le
              hC N u hc n (Set.uIoc_subset_uIcc hx)
    have hintegral :=
      intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    rw [selectedXiPoleTopHorizontalIntegralFor]
    calc
      ‖∫ x : ℝ in 1 - c..c,
        selectedXiPolePairIntegrandFor
          (symmetrizedCompactLaplaceWeight
            (weilFiniteDictionaryPhysicalDensity C N u))
          ((x : ℂ) + T * I)‖ ≤
          (2 * (D * R⁻¹ ^ (2 : ℕ))) * |c - (1 - c)| :=
        hintegral
      _ = B * (gaussianXiHeightScale c n)⁻¹ ^ (2 : ℕ) := by
        dsimp only [B, R]
        ring
  have hinv :
      Tendsto (fun n : ℕ => (gaussianXiHeightScale c n)⁻¹)
        atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_gaussianXiHeightScale c)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n => norm_nonneg _
  · exact Filter.Eventually.of_forall fun n => hbound n
  · simpa using (hinv.pow 2).const_mul B

/-- The full dictionary pole-pair integral is exactly the two elementary residues. -/
theorem integral_dictionaryXiPolePair_eq
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) {c : ℝ} (hc : 1 < c) :
    (∫ y : ℝ,
      selectedXiPolePairIntegrandFor
        (symmetrizedCompactLaplaceWeight
          (weilFiniteDictionaryPhysicalDensity C N u))
        ((c : ℂ) + y * I)) =
      2 * (Real.pi : ℂ) *
        symmetrizedCompactLaplaceWeight
          (weilFiniteDictionaryPhysicalDensity C N u) 1 := by
  let F : ℂ → ℂ :=
    symmetrizedCompactLaplaceWeight
      (weilFiniteDictionaryPhysicalDensity C N u)
  have htop :=
    (tendsto_selectedDictionaryXiPoleTopHorizontalIntegral
      hC N u hc).const_mul (-I)
  have hconst : Tendsto
      (fun _ : ℕ => (Real.pi : ℂ) * (F 0 + F 1)) atTop
      (𝓝 ((Real.pi : ℂ) * (F 0 + F 1))) :=
    tendsto_const_nhds
  have hright :=
    (htop.add hconst).congr'
      (Filter.Eventually.of_forall fun n =>
        (selectedXiPoleRightVerticalIntegral_eq_top_add_residues
          (differentiable_symmetrizedCompactLaplaceWeight
            (continuous_weilFiniteDictionaryPhysicalDensity hC N u)
            (hasCompactSupport_weilFiniteDictionaryPhysicalDensity hC N u))
          (symmetrizedCompactLaplaceWeight_one_sub _)
          hc n).symm)
  have hfull := tendsto_selectedGaussianXiSymmetricIntervalIntegral
    (c := c) (integrable_dictionaryXiPolePair hC N u hc)
  have hzeroOne : F 0 = F 1 := by
    convert
      symmetrizedCompactLaplaceWeight_one_sub
        (weilFiniteDictionaryPhysicalDensity C N u) 1 using 1
    norm_num [F]
  have hright' :
      Tendsto
        (selectedXiPoleRightVerticalIntegralFor F c) atTop
        (𝓝 (2 * (Real.pi : ℂ) * F 1)) := by
    simpa only [mul_zero, zero_add, hzeroOne, two_mul, add_mul, mul_add]
      using hright
  exact tendsto_nhds_unique hfull hright'

/-- The new long-height pole truncations converge to the same two-residue value. -/
theorem tendsto_dictionaryXiPoleIntegral
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) {c : ℝ} (hc : 1 < c) :
    Tendsto
      (fun n : ℕ => ∫ y : ℝ in
        -dictionaryXiSelectedHeight c n..dictionaryXiSelectedHeight c n,
          selectedXiPolePairIntegrandFor
            (symmetrizedCompactLaplaceWeight
              (weilFiniteDictionaryPhysicalDensity C N u))
            ((c : ℂ) + y * I))
      atTop
      (𝓝 (2 * (Real.pi : ℂ) *
        symmetrizedCompactLaplaceWeight
          (weilFiniteDictionaryPhysicalDensity C N u) 1)) := by
  rw [← integral_dictionaryXiPolePair_eq hC N u hc]
  exact tendsto_dictionaryXiSymmetricIntervalIntegral
    (integrable_dictionaryXiPolePair hC N u hc)

/-- Inverse-square dictionary decay absorbs the logarithmic growth of the real-place factor,
without the six-derivative hypothesis used by the generic compact formula. -/
theorem integrable_dictionaryXiArchimedean_of_pos
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) {c : ℝ} (hc : 0 < c) :
    Integrable (fun y : ℝ =>
      symmetrizedCompactLaplaceWeight
          (weilFiniteDictionaryPhysicalDensity C N u)
          ((c : ℂ) + y * I) *
        logDeriv Gammaℝ ((c : ℂ) + y * I)) := by
  let D : ℝ :=
    weilFiniteDictionaryStripDecayConstant C N u |1 / 2 - c|
  have hD : 0 ≤ D := by
    dsimp only [D]
    exact weilFiniteDictionaryStripDecayConstant_nonneg hC N u (abs_nonneg _)
  have hc0 : 0 < c := hc
  obtain ⟨K, hK, hdigamma⟩ :=
    exists_norm_digamma_div_two_le_log (a := c) (b := c) hc0
  let E : ℝ := |Real.log Real.pi| + 2 * K
  have hE : 0 ≤ E := by
    dsimp only [E]
    positivity
  have hlog (y : ℝ) :
      Real.log (|y| + 2) ≤ 4 * Real.sqrt (1 + |y|) := by
    have hx0 : 0 ≤ |y| + 2 := by positivity
    have hraw :=
      Real.log_le_rpow_div hx0 (show (0 : ℝ) < 1 / 2 by norm_num)
    have hsqrt :
        Real.sqrt (|y| + 2) ≤ 2 * Real.sqrt (1 + |y|) := by
      calc
        Real.sqrt (|y| + 2) ≤ Real.sqrt (4 * (1 + |y|)) :=
          Real.sqrt_le_sqrt (by nlinarith [abs_nonneg y])
        _ = Real.sqrt 4 * Real.sqrt (1 + |y|) := by
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
        _ = 2 * Real.sqrt (1 + |y|) := by norm_num
    rw [← Real.sqrt_eq_rpow] at hraw
    calc
      Real.log (|y| + 2) ≤ Real.sqrt (|y| + 2) / (1 / 2) := hraw
      _ = 2 * Real.sqrt (|y| + 2) := by ring
      _ ≤ 4 * Real.sqrt (1 + |y|) := by linarith
  have hdigamma' (y : ℝ) :
      ‖digamma (((c : ℂ) + y * I) / 2)‖ ≤
        4 * K * Real.sqrt (1 + |y|) := by
    calc
      ‖digamma (((c : ℂ) + y * I) / 2)‖ ≤
          K * Real.log (|y| + 2) := by
        simpa using hdigamma ((c : ℂ) + y * I) (by simp) (by simp)
      _ ≤ K * (4 * Real.sqrt (1 + |y|)) :=
        mul_le_mul_of_nonneg_left (hlog y) hK.le
      _ = 4 * K * Real.sqrt (1 + |y|) := by ring
  have hlogGamma (y : ℝ) :
      ‖-(Real.log Real.pi : ℂ) / 2 +
          digamma (((c : ℂ) + y * I) / 2) / 2‖ ≤
        E * Real.sqrt (1 + |y|) := by
    have hsqrtOne : 1 ≤ Real.sqrt (1 + |y|) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.one_le_rpow (by linarith [abs_nonneg y]) (by norm_num)
    calc
      ‖-(Real.log Real.pi : ℂ) / 2 +
          digamma (((c : ℂ) + y * I) / 2) / 2‖ ≤
          ‖-(Real.log Real.pi : ℂ) / 2‖ +
            ‖digamma (((c : ℂ) + y * I) / 2) / 2‖ := norm_add_le _ _
      _ = |Real.log Real.pi| / 2 +
          ‖digamma (((c : ℂ) + y * I) / 2)‖ / 2 := by
        simp [Real.norm_eq_abs]
      _ ≤ |Real.log Real.pi| * Real.sqrt (1 + |y|) +
          (4 * K * Real.sqrt (1 + |y|)) / 2 := by
        gcongr
        · nlinarith [abs_nonneg (Real.log Real.pi)]
        · exact hdigamma' y
      _ = E * Real.sqrt (1 + |y|) := by
        dsimp only [E]
        ring
  have hmajorant :
      Integrable (fun y : ℝ =>
        (D * E) * (1 + |y|) ^ (-(3 / 2 : ℝ))) := by
    have hbase :
        Integrable (fun y : ℝ =>
          (1 + ‖y‖) ^ (-(3 / 2 : ℝ))) :=
      integrable_one_add_norm (E := ℝ) (r := (3 / 2 : ℝ)) (by norm_num)
    simpa only [Real.norm_eq_abs] using hbase.const_mul (D * E)
  have hdigammaContinuous : Continuous (fun y : ℝ =>
      digamma (((c : ℂ) + y * I) / 2)) := by
    rw [continuous_iff_continuousAt]
    intro y
    exact (continuousAt_digamma_of_re_pos (by norm_num [div_re]; linarith)).comp
      (by fun_prop)
  have hweightContinuous : Continuous (fun y : ℝ =>
      symmetrizedCompactLaplaceWeight
        (weilFiniteDictionaryPhysicalDensity C N u)
        ((c : ℂ) + y * I)) :=
    (differentiable_symmetrizedCompactLaplaceWeight
      (continuous_weilFiniteDictionaryPhysicalDensity hC N u)
      (hasCompactSupport_weilFiniteDictionaryPhysicalDensity hC N u)).continuous.comp
        (by fun_prop)
  have hrewritten :
      (fun y : ℝ =>
        symmetrizedCompactLaplaceWeight
            (weilFiniteDictionaryPhysicalDensity C N u)
            ((c : ℂ) + y * I) *
          logDeriv Gammaℝ ((c : ℂ) + y * I)) =
      (fun y : ℝ =>
        symmetrizedCompactLaplaceWeight
            (weilFiniteDictionaryPhysicalDensity C N u)
            ((c : ℂ) + y * I) *
          (-(Real.log Real.pi : ℂ) / 2 +
            digamma (((c : ℂ) + y * I) / 2) / 2)) := by
    funext y
    rw [logDeriv_GammaR_eq_digamma (by
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
        mul_one, sub_self, add_zero]
      exact hc0)]
  rw [hrewritten]
  refine MeasureTheory.Integrable.mono' hmajorant
    (hweightContinuous.mul
      (continuous_const.add (hdigammaContinuous.div_const (2 : ℂ)))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  have hweight :=
    norm_symmetrizedDictionaryWeight_vertical_le hC N u c y
  have ht : 0 < 1 + |y| := by positivity
  rw [norm_mul]
  calc
    ‖symmetrizedCompactLaplaceWeight
        (weilFiniteDictionaryPhysicalDensity C N u)
        ((c : ℂ) + y * I)‖ *
        ‖-(Real.log Real.pi : ℂ) / 2 +
          digamma (((c : ℂ) + y * I) / 2) / 2‖ ≤
      (D * (1 + |y|) ^ (-(2 : ℝ))) *
        (E * Real.sqrt (1 + |y|)) := by
      exact mul_le_mul hweight (hlogGamma y) (norm_nonneg _) (by positivity)
    _ = (D * E) *
        ((1 + |y|) ^ (-(2 : ℝ)) * (1 + |y|) ^ (1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow]
      ring
    _ = (D * E) * (1 + |y|) ^ (-(3 / 2 : ℝ)) := by
      rw [← Real.rpow_add ht]
      norm_num

/-- Right-half-plane wrapper used by the arithmetic decomposition. -/
theorem integrable_dictionaryXiArchimedean
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) {c : ℝ} (hc : 1 < c) :
    Integrable (fun y : ℝ =>
      symmetrizedCompactLaplaceWeight
          (weilFiniteDictionaryPhysicalDensity C N u)
          ((c : ℂ) + y * I) *
        logDeriv Gammaℝ ((c : ℂ) + y * I)) :=
  integrable_dictionaryXiArchimedean_of_pos hC N u
    (lt_trans zero_lt_one hc)

/-- The long-height Archimedean truncations converge to the complete real-place integral. -/
theorem tendsto_dictionaryXiArchimedeanIntegral
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) {c : ℝ} (hc : 1 < c) :
    Tendsto
      (fun n : ℕ => ∫ y : ℝ in
        -dictionaryXiSelectedHeight c n..dictionaryXiSelectedHeight c n,
          symmetrizedCompactLaplaceWeight
              (weilFiniteDictionaryPhysicalDensity C N u)
              ((c : ℂ) + y * I) *
            logDeriv Gammaℝ ((c : ℂ) + y * I))
      atTop
      (𝓝 (compactSymmetrizedXiArchimedeanIntegral
        (weilFiniteDictionaryPhysicalDensity C N u) c)) := by
  simpa only [compactSymmetrizedXiArchimedeanIntegral] using
    tendsto_dictionaryXiSymmetricIntervalIntegral
      (integrable_dictionaryXiArchimedean hC N u hc)

open scoped LSeries.notation in
/-- On each long selected right edge, the xi logarithmic derivative splits into the pole,
real-place, and von-Mangoldt truncations. -/
theorem dictionaryXiRightVerticalIntegral_eq_arithmetic_truncations
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) {c : ℝ} (hc : 1 < c) (n : ℕ) :
    dictionaryXiRightVerticalIntegralFor
        (symmetrizedCompactLaplaceWeight
          (weilFiniteDictionaryPhysicalDensity C N u)) c n =
      (∫ y : ℝ in
        -dictionaryXiSelectedHeight c n..dictionaryXiSelectedHeight c n,
          selectedXiPolePairIntegrandFor
            (symmetrizedCompactLaplaceWeight
              (weilFiniteDictionaryPhysicalDensity C N u))
            ((c : ℂ) + y * I)) +
      (∫ y : ℝ in
        -dictionaryXiSelectedHeight c n..dictionaryXiSelectedHeight c n,
          symmetrizedCompactLaplaceWeight
              (weilFiniteDictionaryPhysicalDensity C N u)
              ((c : ℂ) + y * I) *
            logDeriv Gammaℝ ((c : ℂ) + y * I)) -
      (∫ y : ℝ in
        -dictionaryXiSelectedHeight c n..dictionaryXiSelectedHeight c n,
          symmetrizedCompactLaplaceWeight
              (weilFiniteDictionaryPhysicalDensity C N u)
              ((c : ℂ) + y * I) *
            L ↗ArithmeticFunction.vonMangoldt ((c : ℂ) + y * I)) := by
  let f : ℝ → ℂ := weilFiniteDictionaryPhysicalDensity C N u
  let F : ℂ → ℂ := symmetrizedCompactLaplaceWeight f
  let T : ℝ := dictionaryXiSelectedHeight c n
  have hpole : IntervalIntegrable (fun y : ℝ =>
      selectedXiPolePairIntegrandFor F ((c : ℂ) + y * I))
      volume (-T) T :=
    (integrable_dictionaryXiPolePair hC N u hc).intervalIntegrable
  have harch : IntervalIntegrable (fun y : ℝ =>
      F ((c : ℂ) + y * I) *
        logDeriv Gammaℝ ((c : ℂ) + y * I))
      volume (-T) T :=
    (integrable_dictionaryXiArchimedean hC N u hc).intervalIntegrable
  have hprime : IntervalIntegrable (fun y : ℝ =>
      F ((c : ℂ) + y * I) *
        L ↗ArithmeticFunction.vonMangoldt ((c : ℂ) + y * I))
      volume (-T) T :=
    (integrable_symmetrizedDictionaryWeight_mul_vonMangoldtLSeries
      hC N u hc).intervalIntegrable
  have hpoint (y : ℝ) :
      F ((c : ℂ) + y * I) *
          logDeriv riemannXi ((c : ℂ) + y * I) =
        selectedXiPolePairIntegrandFor F ((c : ℂ) + y * I) +
          F ((c : ℂ) + y * I) *
            logDeriv Gammaℝ ((c : ℂ) + y * I) -
          F ((c : ℂ) + y * I) *
            L ↗ArithmeticFunction.vonMangoldt ((c : ℂ) + y * I) := by
    rw [logDeriv_riemannXi_eq_poles_archimedean_sub_vonMangoldt
      (by simpa using hc)]
    unfold selectedXiPolePairIntegrandFor
    simp only [sub_zero, div_eq_mul_inv]
    ring
  rw [dictionaryXiRightVerticalIntegralFor]
  change
    (∫ y : ℝ in -T..T,
      F ((c : ℂ) + y * I) *
        logDeriv riemannXi ((c : ℂ) + y * I)) = _
  calc
    (∫ y : ℝ in -T..T,
      F ((c : ℂ) + y * I) *
        logDeriv riemannXi ((c : ℂ) + y * I)) =
      ∫ y : ℝ in -T..T,
        selectedXiPolePairIntegrandFor F ((c : ℂ) + y * I) +
          F ((c : ℂ) + y * I) *
            logDeriv Gammaℝ ((c : ℂ) + y * I) -
          F ((c : ℂ) + y * I) *
            L ↗ArithmeticFunction.vonMangoldt ((c : ℂ) + y * I) := by
      apply intervalIntegral.integral_congr
      intro y _hy
      exact hpoint y
    _ = (∫ y : ℝ in -T..T,
          selectedXiPolePairIntegrandFor F ((c : ℂ) + y * I)) +
        (∫ y : ℝ in -T..T,
          F ((c : ℂ) + y * I) *
            logDeriv Gammaℝ ((c : ℂ) + y * I)) -
        (∫ y : ℝ in -T..T,
          F ((c : ℂ) + y * I) *
            L ↗ArithmeticFunction.vonMangoldt ((c : ℂ) + y * I)) := by
      rw [intervalIntegral.integral_sub (hpole.add harch) hprime,
        intervalIntegral.integral_add hpole harch]

/-- The mandatory weak-regularity arithmetic explicit formula for the finite dictionary. -/
theorem symmetrizedFiniteDictionaryXi_arithmetic_explicit_formula
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) {c : ℝ} (hc : 1 < c) :
    (Real.pi : ℂ) *
        ∑' p : RiemannXiDivisorZeroIndex,
          symmetrizedCompactLaplaceWeight
            (weilFiniteDictionaryPhysicalDensity C N u)
            (riemannXiDivisorZeroValue p) =
      2 * (Real.pi : ℂ) *
          symmetrizedCompactLaplaceWeight
            (weilFiniteDictionaryPhysicalDensity C N u) 1 +
        compactSymmetrizedXiArchimedeanIntegral
          (weilFiniteDictionaryPhysicalDensity C N u) c -
        ∑' n : ℕ, compactSymmetrizedVonMangoldtWeight
          (weilFiniteDictionaryPhysicalDensity C N u) n := by
  have hpole := tendsto_dictionaryXiPoleIntegral hC N u hc
  have harch := tendsto_dictionaryXiArchimedeanIntegral hC N u hc
  have hprime := tendsto_dictionaryXiPrimeIntegral hC N u hc
  have harithmetic := (hpole.add harch).sub hprime
  have hright : Tendsto
      (dictionaryXiRightVerticalIntegralFor
        (symmetrizedCompactLaplaceWeight
          (weilFiniteDictionaryPhysicalDensity C N u)) c)
      atTop
      (𝓝 (2 * (Real.pi : ℂ) *
          symmetrizedCompactLaplaceWeight
            (weilFiniteDictionaryPhysicalDensity C N u) 1 +
        compactSymmetrizedXiArchimedeanIntegral
          (weilFiniteDictionaryPhysicalDensity C N u) c -
        ∑' n : ℕ, compactSymmetrizedVonMangoldtWeight
          (weilFiniteDictionaryPhysicalDensity C N u) n)) := by
    apply harithmetic.congr'
    exact Filter.Eventually.of_forall fun n =>
      (dictionaryXiRightVerticalIntegral_eq_arithmetic_truncations
        hC N u hc n).symm
  exact tendsto_nhds_unique
    (tendsto_dictionaryXiRightVerticalIntegral hC N u hc) hright

/-- Literal source-coordinate form of the finite-dictionary zero side. -/
theorem weilFiniteDictionaryTest_arithmetic_explicit_formula
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) {c : ℝ} (hc : 1 < c) :
    (Real.pi : ℂ) *
        ∑' p : RiemannXiDivisorZeroIndex,
          weilFiniteDictionaryTest C N u
            ((riemannXiDivisorZeroValue p - 1 / 2) / I) =
      2 * (Real.pi : ℂ) *
          symmetrizedCompactLaplaceWeight
            (weilFiniteDictionaryPhysicalDensity C N u) 1 +
        compactSymmetrizedXiArchimedeanIntegral
          (weilFiniteDictionaryPhysicalDensity C N u) c -
        ∑' n : ℕ, compactSymmetrizedVonMangoldtWeight
          (weilFiniteDictionaryPhysicalDensity C N u) n := by
  have hzero :
      (fun p : RiemannXiDivisorZeroIndex =>
        weilFiniteDictionaryTest C N u
          ((riemannXiDivisorZeroValue p - 1 / 2) / I)) =
      (fun p : RiemannXiDivisorZeroIndex =>
        symmetrizedCompactLaplaceWeight
          (weilFiniteDictionaryPhysicalDensity C N u)
          (riemannXiDivisorZeroValue p)) := by
    funext p
    exact weilFiniteDictionaryTest_xiDivisorZero hC N u p
  rw [hzero]
  exact symmetrizedFiniteDictionaryXi_arithmetic_explicit_formula hC N u hc

/-- The project pole evaluation is the source value at `i/2`; the sign is supplied by the
compiled evenness of the finite dictionary test. -/
theorem symmetrizedDictionaryWeight_one_eq_test_I_div_two
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) :
    symmetrizedCompactLaplaceWeight
        (weilFiniteDictionaryPhysicalDensity C N u) 1 =
      weilFiniteDictionaryTest C N u (I / 2) := by
  rw [symmetrizedCompactLaplaceWeight_weilFiniteDictionaryPhysicalDensity hC,
    ← weilFiniteDictionaryTest_zeroCoordinate hC]
  have hcoord : (((1 : ℂ) - 1 / 2) / I) = -(I / 2) := by
    field_simp [Complex.I_ne_zero]
    norm_num [pow_two, Complex.I_mul_I]
  rw [hcoord, weilFiniteDictionaryTest_neg]

/-- One project finite-place weight is exactly the source `Lambda(q)/sqrt(q)` Fourier atom. -/
theorem compactSymmetrizedVonMangoldtWeight_dictionary_eq_fourierWeight
    {C : ℕ} (_hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) {q : ℕ} (hq : 0 < q) :
    compactSymmetrizedVonMangoldtWeight
        (weilFiniteDictionaryPhysicalDensity C N u) q =
      (ArithmeticFunction.vonMangoldt q : ℂ) /
          (Real.sqrt q : ℂ) *
        weilFiniteDictionaryFourierWeight C N u
          (Real.log q / (2 * Real.pi)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hhalf :
      Real.exp (-(Real.log (q : ℝ) / 2)) =
        (Real.sqrt q)⁻¹ := by
    rw [Real.exp_neg]
    congr 1
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hqR]
    ring_nf
  have hhalfPos :
      Real.exp (Real.log (q : ℝ) / 2) =
        Real.sqrt q := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hqR]
    congr 1
    ring
  have hsqrtSq : Real.sqrt q * Real.sqrt q = q := by
    nlinarith [Real.sq_sqrt hqR.le]
  have hsqrtSqC : (Real.sqrt q : ℂ) ^ 2 = (q : ℂ) := by
    calc
      (Real.sqrt q : ℂ) ^ 2 =
          ((Real.sqrt q * Real.sqrt q : ℝ) : ℂ) := by
        push_cast
        ring
      _ = (q : ℂ) := by
        rw [hsqrtSq]
        norm_num
  rw [compactSymmetrizedVonMangoldtWeight]
  simp only [weilFiniteDictionaryPhysicalDensity,
    weilFiniteDictionaryLogWeight]
  rw [show -(Real.log (q : ℝ)) / 2 = -(Real.log q / 2) by ring,
    ← Complex.ofReal_exp, hhalf]
  rw [show -(-(Real.log (q : ℝ) / 2)) = Real.log q / 2 by ring,
    ← Complex.ofReal_exp, hhalfPos]
  rw [show -Real.log (q : ℝ) / (2 * Real.pi) =
      -(Real.log q / (2 * Real.pi)) by ring,
    weilFiniteDictionaryFourierWeight_neg]
  push_cast
  field_simp [Real.pi_ne_zero, (Real.sqrt_pos.2 hqR).ne', hq.ne']
  rw [hsqrtSqC]
  ring

/-- The exact source bandwidth kills every project finite-place atom beyond the integer cutoff. -/
theorem compactSymmetrizedVonMangoldtWeight_dictionary_eq_zero_of_cutoff_lt
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) {q : ℕ} (hqC : C < q) :
    compactSymmetrizedVonMangoldtWeight
        (weilFiniteDictionaryPhysicalDensity C N u) q = 0 := by
  have hq : 0 < q := lt_trans (by omega : 0 < C) hqC
  rw [compactSymmetrizedVonMangoldtWeight_dictionary_eq_fourierWeight
    hC N u hq]
  have hCpos : (0 : ℝ) < C := by positivity
  have hqpos : (0 : ℝ) < q := by positivity
  have hlog :
      Real.log (C : ℝ) < Real.log (q : ℝ) :=
    Real.strictMonoOn_log hCpos hqpos (by exact_mod_cast hqC)
  have hden : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hcoordNonneg :
      0 ≤ Real.log (q : ℝ) / (2 * Real.pi) := by
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega)))
      hden.le
  have hout :
      weilFiniteDictionaryBandwidth C <
        |Real.log (q : ℝ) / (2 * Real.pi)| := by
    rw [abs_of_nonneg hcoordNonneg, weilFiniteDictionaryBandwidth]
    exact div_lt_div_of_pos_right hlog hden
  rw [weilFiniteDictionaryFourierWeight_eq_zero_of_bandwidth_lt hout]
  simp

/-- The project finite-place `tsum` is the source's exact finite sum over `2 <= q <= C`. -/
theorem tsum_compactSymmetrizedVonMangoldtWeight_dictionary_eq_source_sum
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) :
    (∑' q : ℕ,
      compactSymmetrizedVonMangoldtWeight
        (weilFiniteDictionaryPhysicalDensity C N u) q) =
      ∑ q ∈ Finset.Icc 2 C,
        (ArithmeticFunction.vonMangoldt q : ℂ) /
            (Real.sqrt q : ℂ) *
          weilFiniteDictionaryFourierWeight C N u
            (Real.log q / (2 * Real.pi)) := by
  rw [tsum_eq_sum (s := Finset.Icc 2 C)]
  · apply Finset.sum_congr rfl
    intro q hq
    have hq2 := (Finset.mem_Icc.mp hq).1
    exact compactSymmetrizedVonMangoldtWeight_dictionary_eq_fourierWeight
      hC N u (by omega)
  · intro q hq
    simp only [Finset.mem_Icc, not_and_or, not_le] at hq
    rcases hq with hq | hq
    · interval_cases q <;>
        simp [compactSymmetrizedVonMangoldtWeight]
    · exact compactSymmetrizedVonMangoldtWeight_dictionary_eq_zero_of_cutoff_lt
        hC N u hq

/-- The complete project finite-place side is `-pi` times the existing source prime quadratic. -/
theorem tsum_compactSymmetrizedVonMangoldtWeight_dictionary_eq_neg_pi_mul_primeQuadratic
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) :
    (∑' q : ℕ,
      compactSymmetrizedVonMangoldtWeight
        (weilFiniteDictionaryPhysicalDensity C N u) q) =
      -(Real.pi : ℂ) *
        ((dotProduct u (Matrix.mulVec
          (weilFinitePrimeSourceMatrix C N) u) : ℝ) : ℂ) := by
  rw [tsum_compactSymmetrizedVonMangoldtWeight_dictionary_eq_source_sum
    hC N u,
    weilFinitePrimeSourceMatrix_quadratic_eq_fourierWeight hC u]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [weilPrimeAtomCoefficient]
  push_cast
  have hq2 := (Finset.mem_Icc.mp hq).1
  have hsqrt : (Real.sqrt q : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (by positivity : (0 : ℝ) < q)).ne'
  field_simp [Real.pi_ne_zero, hsqrt]

/-- Digamma respects complex conjugation, including at the conventionally totalized poles. -/
theorem digamma_conj_eq (z : ℂ) :
    digamma ((starRingEnd ℂ) z) = (starRingEnd ℂ) (digamma z) := by
  have hGammaConj :
      ((starRingEnd ℂ) ∘ Gamma ∘ (starRingEnd ℂ)) = Gamma := by
    funext w
    change star (Gamma (star w)) = Gamma w
    simpa using (Complex.Gamma_conj ((starRingEnd ℂ) w)).symm
  have hderiv :=
    congrFun (deriv_conj_conj_eq_self Gamma hGammaConj)
      ((starRingEnd ℂ) z)
  have hderiv' :
      deriv Gamma ((starRingEnd ℂ) z) =
        (starRingEnd ℂ) (deriv Gamma z) := by
    simpa using hderiv.symm
  rw [digamma_def, logDeriv_apply, logDeriv_apply, Gamma_conj, hderiv']
  simp only [map_div₀]

/-- Digamma is complex differentiable throughout the open right half-plane. -/
theorem differentiableAt_digamma_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ digamma z := by
  let U : Set ℂ := {w | 0 < w.re}
  have hU : IsOpen U := by
    dsimp only [U]
    exact Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
  have hGammaDiff : DifferentiableOn ℂ Gamma U := by
    intro w hw
    exact (differentiableAt_Gamma w (fun m hm => by
      have hre := congrArg Complex.re hm
      simp only [Complex.neg_re, Complex.natCast_re] at hre
      change 0 < w.re at hw
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith)).differentiableWithinAt
  have hGammaAnalytic : AnalyticOnNhd ℂ Gamma U :=
    (Complex.analyticOnNhd_iff_differentiableOn hU).2 hGammaDiff
  have hzU : z ∈ U := hz
  have hGammaNe : Gamma z ≠ 0 :=
    Gamma_ne_zero_of_re_pos hz
  have hlog : AnalyticAt ℂ (deriv Gamma / Gamma) z :=
    (hGammaAnalytic.deriv z hzU).div (hGammaAnalytic z hzU) hGammaNe
  rw [digamma_def]
  change DifferentiableAt ℂ (deriv Gamma / Gamma) z
  exact hlog.differentiableAt

/-- The holomorphic real-place integrand used to move between positive vertical lines. -/
noncomputable def dictionaryXiArchimedeanHolomorphicIntegrand
    (C N : ℕ) (u : Fin (2 * N + 1) → ℝ) (z : ℂ) : ℂ :=
  symmetrizedCompactLaplaceWeight
      (weilFiniteDictionaryPhysicalDensity C N u) z *
    (-(Real.log Real.pi : ℂ) / 2 + digamma (z / 2) / 2)

theorem differentiableAt_dictionaryXiArchimedeanHolomorphicIntegrand
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ
      (dictionaryXiArchimedeanHolomorphicIntegrand C N u) z := by
  have hweight :=
    (differentiable_symmetrizedCompactLaplaceWeight
      (continuous_weilFiniteDictionaryPhysicalDensity hC N u)
      (hasCompactSupport_weilFiniteDictionaryPhysicalDensity hC N u)) z
  have hdigamma :
      DifferentiableAt ℂ (fun w : ℂ => digamma (w / 2)) z :=
    (differentiableAt_digamma_of_re_pos
      (by norm_num [div_re]; linarith)).comp z
        (differentiableAt_id.div_const (2 : ℂ))
  unfold dictionaryXiArchimedeanHolomorphicIntegrand
  exact hweight.mul
    ((differentiableAt_const
      (c := -(Real.log Real.pi : ℂ) / 2)).add
        (hdigamma.div_const (2 : ℂ)))

theorem dictionaryXiArchimedeanHolomorphicIntegrand_eq
    {C N : ℕ} (u : Fin (2 * N + 1) → ℝ)
    {z : ℂ} (hz : 0 < z.re) :
    dictionaryXiArchimedeanHolomorphicIntegrand C N u z =
      symmetrizedCompactLaplaceWeight
          (weilFiniteDictionaryPhysicalDensity C N u) z *
        logDeriv Gammaℝ z := by
  rw [dictionaryXiArchimedeanHolomorphicIntegrand,
    logDeriv_GammaR_eq_digamma hz]

/-- Both horizontal sides of the Gamma line-shift rectangle vanish at the long selected heights. -/
theorem tendsto_dictionaryXiArchimedeanHorizontalIntegrals
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) {c : ℝ} (hc : 1 < c) :
    Tendsto
        (fun n : ℕ => ∫ x : ℝ in 1 / 2..c,
          dictionaryXiArchimedeanHolomorphicIntegrand C N u
            ((x : ℂ) + dictionaryXiSelectedHeight c n * I))
        atTop (𝓝 0) ∧
      Tendsto
        (fun n : ℕ => ∫ x : ℝ in 1 / 2..c,
          dictionaryXiArchimedeanHolomorphicIntegrand C N u
            ((x : ℂ) + (-dictionaryXiSelectedHeight c n) * I))
        atTop (𝓝 0) := by
  obtain ⟨K, hK, hdigamma⟩ :=
    exists_norm_digamma_div_two_le_log
      (a := (1 / 2 : ℝ)) (b := c) (by norm_num)
  let D : ℝ :=
    weilFiniteDictionaryStripDecayConstant C N u (c - 1 / 2)
  let E : ℝ := |Real.log Real.pi| + 2 * K
  let B : ℝ := D * E * |c - 1 / 2|
  have hD : 0 ≤ D := by
    dsimp only [D]
    exact weilFiniteDictionaryStripDecayConstant_nonneg hC N u (by linarith)
  have hE : 0 ≤ E := by
    dsimp only [E]
    positivity
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity
  have hpoint :
      ∀ (n : ℕ) {x τ : ℝ}, x ∈ Ι (1 / 2 : ℝ) c →
        |τ| = dictionaryXiSelectedHeight c n →
        ‖dictionaryXiArchimedeanHolomorphicIntegrand C N u
            ((x : ℂ) + τ * I)‖ ≤
          D * E *
            dictionaryXiHeightScale c n ^ (-(3 / 2 : ℝ)) := by
    intro n x τ hx hτ
    let R : ℝ := dictionaryXiHeightScale c n
    let T : ℝ := dictionaryXiSelectedHeight c n
    let s : ℂ := (x : ℂ) + τ * I
    let z : ℂ := (s - 1 / 2) / I
    have hRpos : 0 < R := dictionaryXiHeightScale_pos c n
    have hRone : 1 ≤ R := by
      dsimp only [R, dictionaryXiHeightScale]
      exact le_max_left _ _
    have hTlo : R < T := (dictionaryXiSelectedHeight_spec c n).1.1
    have hThi : T < 2 * R := (dictionaryXiSelectedHeight_spec c n).1.2
    have hTpos : 0 < T := hRpos.trans hTlo
    have hxclosed : x ∈ Set.Icc (1 / 2 : ℝ) c := by
      have hu := Set.uIoc_subset_uIcc hx
      rw [Set.uIcc_of_le (by linarith : (1 / 2 : ℝ) ≤ c)] at hu
      exact hu
    have hA : 0 ≤ c - 1 / 2 := by linarith
    have hzIm : |z.im| ≤ c - 1 / 2 := by
      dsimp only [z]
      rw [weilFiniteDictionaryZeroCoordinate_im]
      dsimp only [s]
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero]
      rw [abs_le]
      constructor <;> linarith [hxclosed.1, hxclosed.2]
    have hstrip :=
      norm_weilFiniteDictionaryTest_le_stripDecay hC N u hA hzIm
    have hzRe : z.re = τ := by
      dsimp only [z]
      rw [weilFiniteDictionaryZeroCoordinate_re]
      dsimp only [s]
      simp
    have hinv :
        (1 + |z.re|)⁻¹ ≤ R⁻¹ := by
      rw [hzRe, hτ]
      simpa only [one_div] using one_div_le_one_div_of_le hRpos
        (by linarith)
    have hweight :
        ‖symmetrizedCompactLaplaceWeight
            (weilFiniteDictionaryPhysicalDensity C N u) s‖ ≤
          D * R ^ (-(2 : ℝ)) := by
      have hpow :
          R⁻¹ ^ (2 : ℕ) = R ^ (-(2 : ℝ)) := by
        rw [Real.rpow_neg hRpos.le, Real.rpow_two]
        exact inv_pow R 2
      rw [symmetrizedCompactLaplaceWeight_weilFiniteDictionaryPhysicalDensity hC,
        ← weilFiniteDictionaryTest_zeroCoordinate hC]
      exact hstrip.trans
        (by
          simpa only [D, hpow] using
            mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (inv_nonneg.mpr (by positivity)) hinv 2)
              hD)
    have hlog :
        Real.log (T + 2) ≤ 4 * Real.sqrt R := by
      have hraw :=
        Real.log_le_rpow_div (show 0 ≤ T + 2 by positivity)
          (show (0 : ℝ) < 1 / 2 by norm_num)
      rw [← Real.sqrt_eq_rpow] at hraw
      have hsqrt :
          Real.sqrt (T + 2) ≤ 2 * Real.sqrt R := by
        calc
          Real.sqrt (T + 2) ≤ Real.sqrt (4 * R) :=
            Real.sqrt_le_sqrt (by linarith)
          _ = Real.sqrt 4 * Real.sqrt R := by
            rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
          _ = 2 * Real.sqrt R := by norm_num
      calc
        Real.log (T + 2) ≤ Real.sqrt (T + 2) / (1 / 2) := hraw
        _ = 2 * Real.sqrt (T + 2) := by ring
        _ ≤ 4 * Real.sqrt R := by linarith
    have hdigamma' :
        ‖digamma (s / 2)‖ ≤ 4 * K * Real.sqrt R := by
      calc
        ‖digamma (s / 2)‖ ≤ K * Real.log (|s.im| + 2) := by
          apply hdigamma s
          · dsimp only [s]
            norm_num
            exact hxclosed.1
          · dsimp only [s]
            norm_num
            exact hxclosed.2
        _ = K * Real.log (T + 2) := by
          have hsIm : s.im = τ := by
            dsimp only [s]
            simp
          rw [hsIm, hτ]
        _ ≤ K * (4 * Real.sqrt R) :=
          mul_le_mul_of_nonneg_left hlog hK.le
        _ = 4 * K * Real.sqrt R := by ring
    have hsqrtOne : 1 ≤ Real.sqrt R := by
      rw [Real.sqrt_eq_rpow]
      exact Real.one_le_rpow hRone (by norm_num)
    have hgamma :
        ‖-(Real.log Real.pi : ℂ) / 2 + digamma (s / 2) / 2‖ ≤
          E * Real.sqrt R := by
      calc
        ‖-(Real.log Real.pi : ℂ) / 2 + digamma (s / 2) / 2‖ ≤
            ‖-(Real.log Real.pi : ℂ) / 2‖ +
              ‖digamma (s / 2) / 2‖ := norm_add_le _ _
        _ = |Real.log Real.pi| / 2 + ‖digamma (s / 2)‖ / 2 := by
          simp [Real.norm_eq_abs]
        _ ≤ |Real.log Real.pi| * Real.sqrt R +
            (4 * K * Real.sqrt R) / 2 := by
          gcongr
          · nlinarith [abs_nonneg (Real.log Real.pi)]
        _ = E * Real.sqrt R := by
          dsimp only [E]
          ring
    rw [dictionaryXiArchimedeanHolomorphicIntegrand, norm_mul]
    calc
      ‖symmetrizedCompactLaplaceWeight
          (weilFiniteDictionaryPhysicalDensity C N u) s‖ *
          ‖-(Real.log Real.pi : ℂ) / 2 + digamma (s / 2) / 2‖ ≤
        (D * R ^ (-(2 : ℝ))) * (E * Real.sqrt R) := by
          exact mul_le_mul hweight hgamma (norm_nonneg _) (by positivity)
      _ = D * E *
          (R ^ (-(2 : ℝ)) * R ^ (1 / 2 : ℝ)) := by
        rw [Real.sqrt_eq_rpow]
        ring
      _ = D * E * R ^ (-(3 / 2 : ℝ)) := by
        rw [← Real.rpow_add hRpos]
        norm_num
  have hboundTop :
      ∀ n : ℕ,
        ‖∫ x : ℝ in 1 / 2..c,
          dictionaryXiArchimedeanHolomorphicIntegrand C N u
            ((x : ℂ) + dictionaryXiSelectedHeight c n * I)‖ ≤
          B * dictionaryXiHeightScale c n ^ (-(3 / 2 : ℝ)) := by
    intro n
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
      (fun x hx => hpoint n hx
        (abs_of_pos (lt_trans (dictionaryXiHeightScale_pos c n)
          (dictionaryXiSelectedHeight_spec c n).1.1)))
    exact hnorm.trans_eq (by
      dsimp only [B]
      ring)
  have hboundBottom :
      ∀ n : ℕ,
        ‖∫ x : ℝ in 1 / 2..c,
          dictionaryXiArchimedeanHolomorphicIntegrand C N u
            ((x : ℂ) + (-dictionaryXiSelectedHeight c n) * I)‖ ≤
          B * dictionaryXiHeightScale c n ^ (-(3 / 2 : ℝ)) := by
    intro n
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
      (fun x hx => hpoint n hx (by
        rw [abs_neg, abs_of_pos]
        exact lt_trans (dictionaryXiHeightScale_pos c n)
          (dictionaryXiSelectedHeight_spec c n).1.1))
    have hnorm' :
        ‖∫ x : ℝ in 1 / 2..c,
          dictionaryXiArchimedeanHolomorphicIntegrand C N u
            ((x : ℂ) +
              ((-dictionaryXiSelectedHeight c n : ℝ) : ℂ) * I)‖ ≤
          B * dictionaryXiHeightScale c n ^ (-(3 / 2 : ℝ)) := by
      exact hnorm.trans_eq (by
        dsimp only [B]
        ring)
    convert hnorm' using 1
    simp
  have hdecay :
      Tendsto
        (fun n : ℕ =>
          dictionaryXiHeightScale c n ^ (-(3 / 2 : ℝ)))
        atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 2)).comp
      (tendsto_dictionaryXiHeightScale c)
  constructor
  · apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun n => norm_nonneg _
    · exact Filter.Eventually.of_forall hboundTop
    · simpa using hdecay.const_mul B
  · apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun n => norm_nonneg _
    · exact Filter.Eventually.of_forall hboundBottom
    · simpa using hdecay.const_mul B

/-- Finite-rectangle Cauchy shift from the middle line to the Euler-product line. -/
theorem dictionaryXiArchimedeanVerticalIntegral_eq_middle_add_horizontals
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) {c : ℝ} (hc : 1 < c) (n : ℕ) :
    (∫ y : ℝ in
      -dictionaryXiSelectedHeight c n..dictionaryXiSelectedHeight c n,
        dictionaryXiArchimedeanHolomorphicIntegrand C N u
          ((c : ℂ) + y * I)) =
      (∫ y : ℝ in
        -dictionaryXiSelectedHeight c n..dictionaryXiSelectedHeight c n,
          dictionaryXiArchimedeanHolomorphicIntegrand C N u
            ((1 / 2 : ℂ) + y * I)) +
        I * ((∫ x : ℝ in 1 / 2..c,
          dictionaryXiArchimedeanHolomorphicIntegrand C N u
            ((x : ℂ) + (-dictionaryXiSelectedHeight c n) * I)) -
          (∫ x : ℝ in 1 / 2..c,
            dictionaryXiArchimedeanHolomorphicIntegrand C N u
              ((x : ℂ) + dictionaryXiSelectedHeight c n * I))) := by
  let T : ℝ := dictionaryXiSelectedHeight c n
  have hrect :
      DifferentiableOn ℂ
        (dictionaryXiArchimedeanHolomorphicIntegrand C N u)
        ([[(1 / 2 : ℝ), c]] ×ℂ [[-T, T]]) := by
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    have hzre : (1 / 2 : ℝ) ≤ z.re := by
      rw [Set.uIcc_of_le (by linarith : (1 / 2 : ℝ) ≤ c)] at hz
      exact hz.1.1
    exact
      (differentiableAt_dictionaryXiArchimedeanHolomorphicIntegrand
        hC N u (by linarith)).differentiableWithinAt
  have hboundary :=
    rectangleBoundaryIntegral_eq_zero_of_differentiableOn hrect
  rw [rectangleBoundaryIntegral] at hboundary
  simp only [Complex.ofReal_neg] at hboundary ⊢
  norm_num at hboundary ⊢
  apply mul_left_cancel₀ Complex.I_ne_zero
  rw [mul_add]
  simp only [← mul_assoc, Complex.I_mul_I, neg_one_mul]
  linear_combination hboundary

/-- The complete Gamma integral is independent of the chosen positive vertical line, specialized
to the middle line and the campaign line `c>1`. -/
theorem integral_dictionaryXiArchimedean_eq_middle
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) {c : ℝ} (hc : 1 < c) :
    (∫ y : ℝ,
      dictionaryXiArchimedeanHolomorphicIntegrand C N u
        ((c : ℂ) + y * I)) =
      ∫ y : ℝ,
        dictionaryXiArchimedeanHolomorphicIntegrand C N u
          ((1 / 2 : ℂ) + y * I) := by
  have hrightInt : Integrable (fun y : ℝ =>
      dictionaryXiArchimedeanHolomorphicIntegrand C N u
        ((c : ℂ) + y * I)) := by
    apply (integrable_dictionaryXiArchimedean hC N u hc).congr
    exact Filter.Eventually.of_forall fun y =>
      (dictionaryXiArchimedeanHolomorphicIntegrand_eq
        (C := C) (N := N) u (by norm_num; linarith)).symm
  have hmiddleInt : Integrable (fun y : ℝ =>
      dictionaryXiArchimedeanHolomorphicIntegrand C N u
        ((1 / 2 : ℂ) + y * I)) := by
    have hbase : Integrable (fun y : ℝ =>
        symmetrizedCompactLaplaceWeight
            (weilFiniteDictionaryPhysicalDensity C N u)
            ((1 / 2 : ℂ) + y * I) *
          logDeriv Gammaℝ ((1 / 2 : ℂ) + y * I)) := by
      convert
        integrable_dictionaryXiArchimedean_of_pos hC N u
          (show (0 : ℝ) < 1 / 2 by norm_num) using 1
      norm_num
    apply hbase.congr
    exact Filter.Eventually.of_forall fun y =>
      (dictionaryXiArchimedeanHolomorphicIntegrand_eq
        (C := C) (N := N) u (by norm_num)).symm
  have hright :=
    tendsto_dictionaryXiSymmetricIntervalIntegral
      (c := c) hrightInt
  have hmiddle :=
    tendsto_dictionaryXiSymmetricIntervalIntegral
      (c := c) hmiddleInt
  obtain ⟨htop, hbottom⟩ :=
    tendsto_dictionaryXiArchimedeanHorizontalIntegrals hC N u hc
  have hhorizontal := (hbottom.sub htop).const_mul I
  have hshift := hmiddle.add hhorizontal
  have hshift' :
      Tendsto
        (fun n : ℕ => ∫ y : ℝ in
          -dictionaryXiSelectedHeight c n..dictionaryXiSelectedHeight c n,
            dictionaryXiArchimedeanHolomorphicIntegrand C N u
              ((c : ℂ) + y * I))
        atTop
        (𝓝 (∫ y : ℝ,
          dictionaryXiArchimedeanHolomorphicIntegrand C N u
            ((1 / 2 : ℂ) + y * I))) := by
    simpa only [sub_zero, mul_zero, add_zero] using hshift.congr'
      (Filter.Eventually.of_forall fun n =>
        (dictionaryXiArchimedeanVerticalIntegral_eq_middle_add_horizontals
          hC N u hc n).symm)
  exact tendsto_nhds_unique hright hshift'

/-- On the critical middle line, the project Laplace coordinate is the literal source variable. -/
theorem symmetrizedDictionaryWeight_half_add_mul_I
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) (y : ℝ) :
    symmetrizedCompactLaplaceWeight
        (weilFiniteDictionaryPhysicalDensity C N u)
        ((1 / 2 : ℂ) + y * I) =
      weilFiniteDictionaryTest C N u y := by
  rw [symmetrizedCompactLaplaceWeight_weilFiniteDictionaryPhysicalDensity hC,
    ← weilFiniteDictionaryTest_zeroCoordinate hC]
  congr 2
  field_simp [Complex.I_ne_zero]
  ring

/-- Averaging the two middle-line Gamma integrands removes the odd imaginary digamma part and
leaves exactly one half of the source density `h_+(r) g(r)`. -/
theorem dictionaryXiArchimedean_middle_pair
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) (y : ℝ) :
    (symmetrizedCompactLaplaceWeight
          (weilFiniteDictionaryPhysicalDensity C N u)
          ((1 / 2 : ℂ) + y * I) *
        logDeriv Gammaℝ ((1 / 2 : ℂ) + y * I) +
      symmetrizedCompactLaplaceWeight
          (weilFiniteDictionaryPhysicalDensity C N u)
          ((1 / 2 : ℂ) + (-y) * I) *
        logDeriv Gammaℝ ((1 / 2 : ℂ) + (-y) * I)) / 2 =
      (1 / 2 : ℂ) * (weilArchimedeanDensity y : ℂ) *
        weilFiniteDictionaryTest C N u y := by
  have hpos (t : ℝ) : 0 < (((1 / 2 : ℂ) + t * I).re) := by
    simp
  have hlogPos :
      logDeriv Gammaℝ ((1 / 2 : ℂ) + y * I) =
        -(Real.log Real.pi : ℂ) / 2 +
          digamma (((1 / 2 : ℂ) + y * I) / 2) / 2 :=
    logDeriv_GammaR_eq_digamma (hpos y)
  have hlogNeg :
      logDeriv Gammaℝ ((1 / 2 : ℂ) + (-y) * I) =
        -(Real.log Real.pi : ℂ) / 2 +
          digamma (((1 / 2 : ℂ) + (-y) * I) / 2) / 2 :=
    logDeriv_GammaR_eq_digamma (by simp)
  have hweightPos :=
    symmetrizedDictionaryWeight_half_add_mul_I hC N u y
  have hweightNeg :
      symmetrizedCompactLaplaceWeight
          (weilFiniteDictionaryPhysicalDensity C N u)
          ((1 / 2 : ℂ) + (-y) * I) =
        weilFiniteDictionaryTest C N u y := by
    calc
      symmetrizedCompactLaplaceWeight
          (weilFiniteDictionaryPhysicalDensity C N u)
          ((1 / 2 : ℂ) + (-y) * I) =
        symmetrizedCompactLaplaceWeight
          (weilFiniteDictionaryPhysicalDensity C N u)
          ((1 / 2 : ℂ) + ((-y : ℝ) : ℂ) * I) := by
            push_cast
            rfl
      _ = weilFiniteDictionaryTest C N u (-y) :=
        by simpa using
          symmetrizedDictionaryWeight_half_add_mul_I hC N u (-y)
      _ = weilFiniteDictionaryTest C N u y :=
        weilFiniteDictionaryTest_neg C N u y
  rw [hlogPos, hlogNeg, hweightPos, hweightNeg]
  have harg :
      (((1 / 2 : ℂ) + (-y) * I) / 2) =
        (starRingEnd ℂ) (((1 / 2 : ℂ) + y * I) / 2) := by
    simp only [map_div₀, map_add, map_mul, map_one, map_ofNat,
      Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [harg, digamma_conj_eq]
  have hmiddle :
      (((1 / 2 : ℂ) + y * I) / 2) =
        (1 / 4 : ℂ) + (y / 2 : ℂ) * I := by
    ring
  rw [hmiddle, weilArchimedeanDensity]
  push_cast
  rw [Complex.re_eq_add_conj]
  ring

/-- The literal source real-place integral for the finite dictionary. -/
noncomputable def weilFiniteDictionarySourceArchimedeanIntegral
    (C N : ℕ) (u : Fin (2 * N + 1) → ℝ) : ℂ :=
  ∫ y : ℝ, (weilArchimedeanDensity y : ℂ) *
    weilFiniteDictionaryTest C N u y

/-- The project Gamma integral on the middle line is exactly half the literal source
`h_+(r) g(r)` integral. -/
theorem integral_dictionaryXiArchimedean_middle_eq_source
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) :
    (∫ y : ℝ,
      symmetrizedCompactLaplaceWeight
          (weilFiniteDictionaryPhysicalDensity C N u)
          ((1 / 2 : ℂ) + y * I) *
        logDeriv Gammaℝ ((1 / 2 : ℂ) + y * I)) =
      (1 / 2 : ℂ) *
        weilFiniteDictionarySourceArchimedeanIntegral C N u := by
  let H : ℝ → ℂ := fun y =>
    symmetrizedCompactLaplaceWeight
        (weilFiniteDictionaryPhysicalDensity C N u)
        ((1 / 2 : ℂ) + y * I) *
      logDeriv Gammaℝ ((1 / 2 : ℂ) + y * I)
  have hH : Integrable H := by
    convert
      integrable_dictionaryXiArchimedean_of_pos hC N u
        (show (0 : ℝ) < 1 / 2 by norm_num) using 1
    norm_num [H]
  have hHneg : Integrable (fun y : ℝ => H (-y)) := hH.comp_neg
  calc
    (∫ y : ℝ, H y) =
        ((∫ y : ℝ, H y) + (∫ y : ℝ, H (-y))) / 2 := by
      rw [integral_neg_eq_self]
      ring
    _ = ∫ y : ℝ, (H y + H (-y)) / 2 := by
      rw [MeasureTheory.integral_div, MeasureTheory.integral_add hH hHneg]
    _ = ∫ y : ℝ,
        (1 / 2 : ℂ) * (weilArchimedeanDensity y : ℂ) *
          weilFiniteDictionaryTest C N u y := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        dsimp only [H]
        convert dictionaryXiArchimedean_middle_pair hC N u y using 1
        simp
    _ = (1 / 2 : ℂ) *
        weilFiniteDictionarySourceArchimedeanIntegral C N u := by
      rw [weilFiniteDictionarySourceArchimedeanIntegral]
      have hfun :
          (fun y : ℝ =>
            (1 / 2 : ℂ) * (weilArchimedeanDensity y : ℂ) *
              weilFiniteDictionaryTest C N u y) =
          (fun y : ℝ => (1 / 2 : ℂ) *
            ((weilArchimedeanDensity y : ℂ) *
              weilFiniteDictionaryTest C N u y)) := by
        funext y
        ring
      rw [hfun, MeasureTheory.integral_const_mul]

/-- The project real-place term is exactly one half of the literal source
`integral h_+(r) g_u(r) dr`, independently of the contour line `c>1`. -/
theorem compactSymmetrizedXiArchimedeanIntegral_dictionary_eq_source
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) {c : ℝ} (hc : 1 < c) :
    compactSymmetrizedXiArchimedeanIntegral
        (weilFiniteDictionaryPhysicalDensity C N u) c =
      (1 / 2 : ℂ) *
        weilFiniteDictionarySourceArchimedeanIntegral C N u := by
  rw [compactSymmetrizedXiArchimedeanIntegral]
  calc
    (∫ y : ℝ,
      symmetrizedCompactLaplaceWeight
          (weilFiniteDictionaryPhysicalDensity C N u)
          ((c : ℂ) + y * I) *
        logDeriv Gammaℝ ((c : ℂ) + y * I)) =
      ∫ y : ℝ,
        dictionaryXiArchimedeanHolomorphicIntegrand C N u
          ((c : ℂ) + y * I) := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall fun y =>
        (dictionaryXiArchimedeanHolomorphicIntegrand_eq
          (C := C) (N := N) u (by norm_num; linarith)).symm
    _ = ∫ y : ℝ,
        dictionaryXiArchimedeanHolomorphicIntegrand C N u
          ((1 / 2 : ℂ) + y * I) :=
      integral_dictionaryXiArchimedean_eq_middle hC N u hc
    _ = ∫ y : ℝ,
      symmetrizedCompactLaplaceWeight
          (weilFiniteDictionaryPhysicalDensity C N u)
          ((1 / 2 : ℂ) + y * I) *
        logDeriv Gammaℝ ((1 / 2 : ℂ) + y * I) := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall fun y =>
        dictionaryXiArchimedeanHolomorphicIntegrand_eq
          (C := C) (N := N) u (by norm_num)
    _ = (1 / 2 : ℂ) *
        weilFiniteDictionarySourceArchimedeanIntegral C N u :=
      integral_dictionaryXiArchimedean_middle_eq_source hC N u

/-- Source-coordinate Guinand--Weil formula with the exact finite prime cutoff, the even pole
evaluation, and the literal Archimedean density. -/
theorem weilFiniteDictionary_source_arithmetic_explicit_formula
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) {c : ℝ} (hc : 1 < c) :
    (∑' p : RiemannXiDivisorZeroIndex,
      weilFiniteDictionaryTest C N u
        ((riemannXiDivisorZeroValue p - 1 / 2) / I)) =
      -(1 / (Real.pi : ℂ)) *
          (∑ q ∈ Finset.Icc 2 C,
            (ArithmeticFunction.vonMangoldt q : ℂ) /
                (Real.sqrt q : ℂ) *
              weilFiniteDictionaryFourierWeight C N u
                (Real.log q / (2 * Real.pi))) +
        2 * weilFiniteDictionaryTest C N u (I / 2) +
        (1 / (2 * Real.pi : ℂ)) *
          weilFiniteDictionarySourceArchimedeanIntegral C N u := by
  have hformula :=
    weilFiniteDictionaryTest_arithmetic_explicit_formula hC N u hc
  rw [symmetrizedDictionaryWeight_one_eq_test_I_div_two hC,
    compactSymmetrizedXiArchimedeanIntegral_dictionary_eq_source hC N u hc,
    tsum_compactSymmetrizedVonMangoldtWeight_dictionary_eq_source_sum hC]
    at hformula
  apply mul_left_cancel₀ (show (Real.pi : ℂ) ≠ 0 by
    exact ofReal_ne_zero.mpr Real.pi_ne_zero)
  rw [hformula]
  field_simp [Real.pi_ne_zero]
  ring

/-- Matrix/source assembly: the finite prime sum is the existing prime-source quadratic, while
the pole and complete Archimedean pieces retain their literal source evaluations. -/
theorem weilFiniteDictionary_primeMatrix_archimedean_zeroSum
    {C : ℕ} (hC : 2 ≤ C) (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ) {c : ℝ} (hc : 1 < c) :
    (∑' p : RiemannXiDivisorZeroIndex,
      weilFiniteDictionaryTest C N u
        ((riemannXiDivisorZeroValue p - 1 / 2) / I)) =
      ((dotProduct u (Matrix.mulVec
        (weilFinitePrimeSourceMatrix C N) u) : ℝ) : ℂ) +
        2 * weilFiniteDictionaryTest C N u (I / 2) +
        (1 / (2 * Real.pi : ℂ)) *
          weilFiniteDictionarySourceArchimedeanIntegral C N u := by
  have hsource :=
    weilFiniteDictionary_source_arithmetic_explicit_formula hC N u hc
  have hprime :=
    tsum_compactSymmetrizedVonMangoldtWeight_dictionary_eq_neg_pi_mul_primeQuadratic
      hC N u
  rw [tsum_compactSymmetrizedVonMangoldtWeight_dictionary_eq_source_sum
    hC N u] at hprime
  have hpi : (Real.pi : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [hsource, hprime]
  field_simp [hpi]

end

end LeanLab.Riemann
