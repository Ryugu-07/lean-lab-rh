import LeanLab.Riemann.DeBruijnNewmanThirdLi
import LeanLab.Riemann.DeBruijnNewmanUpperHalf
import LeanLab.Riemann.LiReverseCriterion

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The all-index Li criterion for the de Bruijn-Newman heat family

This module aligns the derivative-defined Li coefficients of the source-normalized heat family
with its zero geometry.  The campaign endpoint is the complete nonnegative-time equivalence; finite
coefficient consequences are not endpoints here.
-/

open Complex Filter Function Metric Polynomial Set Topology
open scoped BigOperators ComplexConjugate Topology

namespace LeanLab.Riemann

noncomputable section

/-- Finite entire order is preserved when the input is multiplied by a complex constant. -/
theorem entireOfOrderAtMost_comp_const_mul
    {rho : Real} {F : Complex -> Complex}
    (hF : Complex.Hadamard.EntireOfOrderAtMost rho F) (hrho : 0 <= rho)
    (a : Complex) :
    Complex.Hadamard.EntireOfOrderAtMost rho (fun z : Complex => F (a * z)) := by
  refine ⟨hF.differentiable.comp ((differentiable_const a).mul differentiable_id), ?_⟩
  intro epsilon hepsilon
  obtain ⟨C, hC, hbound⟩ := hF.exists_bound hepsilon
  let A : Real := max 1 ‖a‖
  let C' : Real := C * A ^ (rho + epsilon)
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_left 1 ‖a‖)
  have hexponent : 0 <= rho + epsilon := by linarith
  refine ⟨C', mul_pos hC (Real.rpow_pos_of_pos hApos _), ?_⟩
  intro z
  have hbase : 1 + ‖a * z‖ <= A * (1 + ‖z‖) := by
    rw [norm_mul]
    have ha : ‖a‖ <= A := le_max_right 1 ‖a‖
    have hAone : 1 <= A := le_max_left 1 ‖a‖
    nlinarith [norm_nonneg z, mul_le_mul_of_nonneg_right ha (norm_nonneg z)]
  have hpow :
      (1 + ‖a * z‖) ^ (rho + epsilon) <=
        (A * (1 + ‖z‖)) ^ (rho + epsilon) :=
    Real.rpow_le_rpow (by positivity) hbase hexponent
  calc
    ‖F (a * z)‖ <= Real.exp (C * (1 + ‖a * z‖) ^ (rho + epsilon)) := hbound _
    _ <= Real.exp (C' * (1 + ‖z‖) ^ (rho + epsilon)) := by
      apply Real.exp_le_exp.mpr
      calc
        C * (1 + ‖a * z‖) ^ (rho + epsilon) <=
            C * (A * (1 + ‖z‖)) ^ (rho + epsilon) := by gcongr
        _ = C' * (1 + ‖z‖) ^ (rho + epsilon) := by
          rw [Real.mul_rpow hApos.le (by positivity : 0 <= 1 + ‖z‖)]
          ring

/-- Finite entire order is preserved when the output is multiplied by a complex constant. -/
theorem entireOfOrderAtMost_const_mul
    {rho : Real} {F : Complex -> Complex}
    (hF : Complex.Hadamard.EntireOfOrderAtMost rho F) (hrho : 0 <= rho)
    (a : Complex) :
    Complex.Hadamard.EntireOfOrderAtMost rho (fun z : Complex => a * F z) := by
  refine ⟨(differentiable_const a).mul hF.differentiable, ?_⟩
  intro epsilon hepsilon
  obtain ⟨C, hC, hbound⟩ := hF.exists_bound hepsilon
  let A : Real := max 1 ‖a‖
  let C' : Real := C + Real.log A
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_left 1 ‖a‖)
  have hlogA : 0 <= Real.log A := Real.log_nonneg (le_max_left 1 ‖a‖)
  have hexponent : 0 <= rho + epsilon := by linarith
  refine ⟨C', add_pos_of_pos_of_nonneg hC hlogA, ?_⟩
  intro z
  let xGrowth : Real := (1 + ‖z‖) ^ (rho + epsilon)
  have hxGrowth : 1 <= xGrowth := by
    exact Real.one_le_rpow (by linarith [norm_nonneg z]) hexponent
  have hFz : ‖F z‖ <= Real.exp (C * xGrowth) := by
    simpa only [xGrowth] using (hbound z)
  change ‖a * F z‖ <= Real.exp (C' * xGrowth)
  calc
    ‖a * F z‖ = ‖a‖ * ‖F z‖ := norm_mul _ _
    _ <= A * ‖F z‖ := by
      exact mul_le_mul_of_nonneg_right (le_max_right 1 ‖a‖) (norm_nonneg _)
    _ <= A * Real.exp (C * xGrowth) := by
      exact mul_le_mul_of_nonneg_left hFz (le_trans (by norm_num) (le_max_left 1 ‖a‖))
    _ = Real.exp (Real.log A) * Real.exp (C * xGrowth) := by
      rw [Real.exp_log hApos]
    _ = Real.exp (Real.log A + C * xGrowth) := (Real.exp_add _ _).symm
    _ <= Real.exp (C' * xGrowth) := by
      apply Real.exp_le_exp.mpr
      dsimp only [C']
      nlinarith

/-- Every heat-Xi function is entire of order at most one. -/
theorem deBruijnNewmanHeatXi_entireOfOrderAtMost_one (t : Real) :
    Complex.Hadamard.EntireOfOrderAtMost (1 : Real) (deBruijnNewmanHeatXi t) := by
  have htranslated :=
    (deBruijnNewmanH_entireOfOrderAtMost_one t).comp_add_const
      (by norm_num : (0 : Real) <= 1) Complex.I
  have hscaled := entireOfOrderAtMost_comp_const_mul htranslated
    (by norm_num : (0 : Real) <= 1) (-Complex.I * 2)
  have hcoordinate :
      (fun s : Complex =>
        deBruijnNewmanH t ((-Complex.I * 2) * s + Complex.I)) =
      fun s : Complex => deBruijnNewmanH t (-Complex.I * (2 * s - 1)) := by
    funext s
    congr 1
    ring
  rw [hcoordinate] at hscaled
  change Complex.Hadamard.EntireOfOrderAtMost (1 : Real)
    (fun s : Complex => 8 * deBruijnNewmanH t (-Complex.I * (2 * s - 1)))
  exact entireOfOrderAtMost_const_mul hscaled
    (by norm_num : (0 : Real) <= 1) (8 : Complex)

/-- The heat-Xi function does not vanish at the reflected base point `0`. -/
theorem deBruijnNewmanHeatXi_zero_ne_zero (t : Real) :
    deBruijnNewmanHeatXi t 0 ≠ 0 := by
  have h := deBruijnNewmanHeatXi_one_ne_zero t
  rw [← deBruijnNewmanHeatXi_one_sub t 0]
  simpa using h

/-- The multiplicity-bearing nonzero heat-Xi divisor. -/
abbrev DeBruijnNewmanHeatXiDivisorZeroIndex (t : Real) :=
  Complex.Hadamard.divisorZeroIndex₀ (deBruijnNewmanHeatXi t) (Set.univ : Set Complex)

/-- The value represented by a multiplicity-bearing heat-Xi divisor index. -/
abbrev deBruijnNewmanHeatXiDivisorZeroValue
    {t : Real} (p : DeBruijnNewmanHeatXiDivisorZeroIndex t) : Complex :=
  Complex.Hadamard.divisorZeroIndex₀_val p

/-- Squared reciprocal norms of the nonzero heat-Xi zeros are summable at every real time. -/
theorem summable_deBruijnNewmanHeatXiDivisorZeroIndex_norm_inv_sq (t : Real) :
    Summable (fun p : DeBruijnNewmanHeatXiDivisorZeroIndex t =>
      ‖deBruijnNewmanHeatXiDivisorZeroValue p‖⁻¹ ^ (2 : Nat)) := by
  have hnot : ∃ s : Complex, deBruijnNewmanHeatXi t s ≠ 0 :=
    ⟨1, deBruijnNewmanHeatXi_one_ne_zero t⟩
  simpa using
    (deBruijnNewmanHeatXi_entireOfOrderAtMost_one t).summable_norm_inv_pow_divisorZeroIndex₀
        (by norm_num : (0 : Real) <= 1) hnot

/-- Genus-one Hadamard factorization of heat-Xi, with no origin monomial. -/
theorem exists_deBruijnNewmanHeatXi_hadamard_factorization (t : Real) :
    ∃ P : Polynomial Complex, P.degree <= 1 ∧ ∀ s : Complex,
      deBruijnNewmanHeatXi t s = Complex.exp (Polynomial.eval s P) *
        Complex.Hadamard.divisorCanonicalProduct 1 (deBruijnNewmanHeatXi t)
          (Set.univ : Set Complex) s := by
  have hnot : ∃ s : Complex, deBruijnNewmanHeatXi t s ≠ 0 :=
    ⟨0, deBruijnNewmanHeatXi_zero_ne_zero t⟩
  obtain ⟨P, hdegree, hfactor⟩ :=
    Complex.Hadamard.hadamard_factorization_of_order
      (by norm_num : (0 : Real) <= 1) hnot
      (deBruijnNewmanHeatXi_entireOfOrderAtMost_one t)
  have horder0 : analyticOrderNatAt (deBruijnNewmanHeatXi t) 0 = 0 := by
    by_contra horder
    exact deBruijnNewmanHeatXi_zero_ne_zero t
      (apply_eq_zero_of_analyticOrderNatAt_ne_zero horder)
  refine ⟨P, ?_, ?_⟩
  · simpa using hdegree
  · intro s
    simpa [horder0] using hfactor s

/-- The heat-Xi family is compatible with complex conjugation. -/
@[simp]
theorem deBruijnNewmanHeatXi_conj (t : Real) (s : Complex) :
    deBruijnNewmanHeatXi t (conj s) = conj (deBruijnNewmanHeatXi t s) := by
  rw [deBruijnNewmanHeatXi, deBruijnNewmanHeatXi]
  have hcoordinate :
      -Complex.I * (2 * conj s - 1) =
        -conj (-Complex.I * (2 * s - 1)) := by
    apply Complex.ext <;> simp
  rw [hcoordinate, deBruijnNewmanH_neg, deBruijnNewmanH_conj]
  simp only [map_mul, map_ofNat]

/-- Reflection preserves the analytic multiplicity of every heat-Xi zero. -/
theorem analyticOrderAt_deBruijnNewmanHeatXi_one_sub (t : Real) (s : Complex) :
    analyticOrderAt (deBruijnNewmanHeatXi t) (1 - s) =
      analyticOrderAt (deBruijnNewmanHeatXi t) s := by
  let reflect : Complex -> Complex := fun z => 1 - z
  have hreflectAnalytic : AnalyticAt Complex reflect s := by fun_prop
  have hreflectDeriv : deriv reflect s ≠ 0 := by
    simp [reflect, deriv_const_sub_id]
  have hcomp :
      analyticOrderAt (deBruijnNewmanHeatXi t ∘ reflect) s =
        analyticOrderAt (deBruijnNewmanHeatXi t) (reflect s) :=
    analyticOrderAt_comp_of_deriv_ne_zero hreflectAnalytic hreflectDeriv
  have hfunctional :
      analyticOrderAt (deBruijnNewmanHeatXi t ∘ reflect) s =
        analyticOrderAt (deBruijnNewmanHeatXi t) s := by
    apply analyticOrderAt_congr
    exact Filter.Eventually.of_forall fun z => by
      simpa [reflect, Function.comp_def] using deBruijnNewmanHeatXi_one_sub t z
  calc
    analyticOrderAt (deBruijnNewmanHeatXi t) (1 - s) =
        analyticOrderAt (deBruijnNewmanHeatXi t ∘ reflect) s := by
      simpa only [reflect] using hcomp.symm
    _ = analyticOrderAt (deBruijnNewmanHeatXi t) s := hfunctional

/-- Every nonzero heat-Xi divisor index represents a zero of heat-Xi. -/
theorem deBruijnNewmanHeatXiDivisorZeroIndex_val_eq_zero
    {t : Real} (p : DeBruijnNewmanHeatXiDivisorZeroIndex t) :
    deBruijnNewmanHeatXi t (deBruijnNewmanHeatXiDivisorZeroValue p) = 0 := by
  have hsupport :=
    Complex.Hadamard.divisorZeroIndex₀_val_mem_divisor_support
      (f := deBruijnNewmanHeatXi t) (U := (Set.univ : Set Complex)) p
  have hdivisor : MeromorphicOn.divisor (deBruijnNewmanHeatXi t) Set.univ
      (deBruijnNewmanHeatXiDivisorZeroValue p) ≠ 0 := by
    simpa only [Function.mem_support] using hsupport
  have horder : analyticOrderNatAt (deBruijnNewmanHeatXi t)
      (deBruijnNewmanHeatXiDivisorZeroValue p) ≠ 0 := by
    intro hzero
    apply hdivisor
    rw [Complex.Hadamard.divisor_univ_eq_analyticOrderNatAt_int
      (deBruijnNewmanHeatXi_entireOfOrderAtMost_one t).differentiable]
    simp [hzero]
  exact apply_eq_zero_of_analyticOrderNatAt_ne_zero horder

theorem one_sub_deBruijnNewmanHeatXiDivisorZeroValue_ne_zero
    {t : Real} (p : DeBruijnNewmanHeatXiDivisorZeroIndex t) :
    1 - deBruijnNewmanHeatXiDivisorZeroValue p ≠ 0 := by
  intro hzero
  have hp1 : deBruijnNewmanHeatXiDivisorZeroValue p = 1 :=
    (sub_eq_zero.mp hzero).symm
  have hpZero := deBruijnNewmanHeatXiDivisorZeroIndex_val_eq_zero p
  rw [hp1] at hpZero
  exact deBruijnNewmanHeatXi_one_ne_zero t hpZero

private theorem deBruijnNewmanHeatXiDivisorZeroIndex_reflect_card
    {t : Real} (p : DeBruijnNewmanHeatXiDivisorZeroIndex t) :
    Int.toNat (MeromorphicOn.divisor (deBruijnNewmanHeatXi t) (Set.univ : Set Complex)
        (1 - deBruijnNewmanHeatXiDivisorZeroValue p)) =
      Int.toNat (MeromorphicOn.divisor (deBruijnNewmanHeatXi t) (Set.univ : Set Complex)
        (deBruijnNewmanHeatXiDivisorZeroValue p)) := by
  rw [Complex.Hadamard.divisor_univ_eq_analyticOrderNatAt_int
      (deBruijnNewmanHeatXi_entireOfOrderAtMost_one t).differentiable,
    Complex.Hadamard.divisor_univ_eq_analyticOrderNatAt_int
      (deBruijnNewmanHeatXi_entireOfOrderAtMost_one t).differentiable]
  simp only [Int.toNat_natCast]
  unfold analyticOrderNatAt
  rw [analyticOrderAt_deBruijnNewmanHeatXi_one_sub]

/-- Reflection of a multiplicity-bearing heat-Xi divisor index. -/
def deBruijnNewmanHeatXiDivisorZeroReflect
    {t : Real} (p : DeBruijnNewmanHeatXiDivisorZeroIndex t) :
    DeBruijnNewmanHeatXiDivisorZeroIndex t :=
  ⟨⟨1 - deBruijnNewmanHeatXiDivisorZeroValue p,
      Fin.cast (deBruijnNewmanHeatXiDivisorZeroIndex_reflect_card p).symm p.1.2⟩,
    one_sub_deBruijnNewmanHeatXiDivisorZeroValue_ne_zero p⟩

@[simp]
theorem deBruijnNewmanHeatXiDivisorZeroValue_reflect
    {t : Real} (p : DeBruijnNewmanHeatXiDivisorZeroIndex t) :
    deBruijnNewmanHeatXiDivisorZeroValue
        (deBruijnNewmanHeatXiDivisorZeroReflect p) =
      1 - deBruijnNewmanHeatXiDivisorZeroValue p :=
  rfl

theorem deBruijnNewmanHeatXiDivisorZeroReflect_involutive (t : Real) :
    Function.Involutive
      (deBruijnNewmanHeatXiDivisorZeroReflect (t := t)) := by
  intro p
  apply Subtype.ext
  have hvalue : 1 - (1 - deBruijnNewmanHeatXiDivisorZeroValue p) =
      deBruijnNewmanHeatXiDivisorZeroValue p := by ring
  apply Sigma.ext hvalue
  refine (Fin.heq_ext_iff ?_).2 ?_
  · simp only [deBruijnNewmanHeatXiDivisorZeroValue_reflect, hvalue]
  · simp [deBruijnNewmanHeatXiDivisorZeroReflect]

/-- The divisor-index permutation induced by `rho |-> 1-rho`. -/
def deBruijnNewmanHeatXiDivisorZeroReflectEquiv (t : Real) :
    DeBruijnNewmanHeatXiDivisorZeroIndex t ≃
      DeBruijnNewmanHeatXiDivisorZeroIndex t :=
  (deBruijnNewmanHeatXiDivisorZeroReflect_involutive t).toPerm

@[simp]
theorem deBruijnNewmanHeatXiDivisorZeroReflectEquiv_apply
    {t : Real} (p : DeBruijnNewmanHeatXiDivisorZeroIndex t) :
    deBruijnNewmanHeatXiDivisorZeroReflectEquiv t p =
      deBruijnNewmanHeatXiDivisorZeroReflect p :=
  rfl

/-- A reflection-paired raw Li term for an arbitrary multiplicity-bearing zero family. -/
def pairedLiZeroTerm {index : Type*} (value : index -> Complex)
    (n : Nat) (p : index) : Complex :=
  (liRawZeroTerm (n + 1) (value p) +
      liRawZeroTerm (n + 1) (1 - value p)) / 2

theorem pairedLiZeroTerm_eq_normSq_of_re_eq_half
    {index : Type*} {value : index -> Complex}
    (n : Nat) (p : index) (hzero : value p ≠ 0) (hone : value p ≠ 1)
    (hline : (value p).re = 1 / 2) :
    pairedLiZeroTerm value n p =
      (Complex.normSq (liRawZeroTerm (n + 1) (value p)) : Complex) / 2 := by
  have hreflect : 1 - value p = conj (value p) := by
    apply Complex.ext
    · simp [hline]
      ring
    · simp
  unfold pairedLiZeroTerm
  rw [liRawZeroTerm_add_reflect_eq_mul (n + 1) hzero hone, hreflect,
    liRawZeroTerm_conj, Complex.mul_conj]

/-- The forward half of the abstract Li criterion once the paired zero formula is available. -/
theorem forall_coefficient_re_nonneg_of_pairedLiZeroFormula
    {index : Type*} {value : index -> Complex} {coefficient : Nat -> Complex}
    (hzero : ∀ p, value p ≠ 0) (hone : ∀ p, value p ≠ 1)
    (hsum : ∀ n, Summable (pairedLiZeroTerm value n))
    (hformula : ∀ n, coefficient n = ∑' p, pairedLiZeroTerm value n p)
    (hline : ∀ p, (value p).re = 1 / 2) :
    ∀ n, 0 <= (coefficient n).re := by
  intro n
  have hnormSum : Summable (fun p =>
      (Complex.normSq (liRawZeroTerm (n + 1) (value p)) : Complex) / 2) := by
    apply (hsum n).congr
    intro p
    exact pairedLiZeroTerm_eq_normSq_of_re_eq_half n p (hzero p) (hone p) (hline p)
  rw [hformula n]
  rw [Complex.re_tsum (hsum n)]
  apply tsum_nonneg
  intro p
  rw [pairedLiZeroTerm_eq_normSq_of_re_eq_half n p (hzero p) (hone p) (hline p)]
  simpa using div_nonneg
    (Complex.normSq_nonneg (liRawZeroTerm (n + 1) (value p)))
    (by norm_num : (0 : Real) <= 2)

/-- Reflection-invariant size of the reciprocal Li transforms in one abstract zero orbit. -/
def pairedLiOrbitRadius {index : Type*} (value : index -> Complex) (p : index) : Real :=
  max ‖liZeroTransform (value p)‖ ‖(liZeroTransform (value p))⁻¹‖

theorem pairedLiOrbitRadius_reflect
    {index : Type*} {value : index -> Complex} (reflect : index ≃ index)
    (hreflect : ∀ p, value (reflect p) = 1 - value p)
    (hzero : ∀ p, value p ≠ 0) (hone : ∀ p, value p ≠ 1) (p : index) :
    pairedLiOrbitRadius value (reflect p) = pairedLiOrbitRadius value p := by
  have hqzero := liZeroTransform_ne_zero (hzero p) (hone p)
  simp only [pairedLiOrbitRadius, hreflect,
    liZeroTransform_one_sub (hzero p) (hone p), inv_inv]
  rw [max_comm]

theorem one_le_pairedLiOrbitRadius
    {index : Type*} {value : index -> Complex}
    (hzero : ∀ p, value p ≠ 0) (hone : ∀ p, value p ≠ 1) (p : index) :
    1 <= pairedLiOrbitRadius value p := by
  have hqzero := liZeroTransform_ne_zero (hzero p) (hone p)
  by_cases hq : 1 <= ‖liZeroTransform (value p)‖
  · exact hq.trans (le_max_left _ _)
  · have hqpos : 0 < ‖liZeroTransform (value p)‖ := norm_pos_iff.mpr hqzero
    have hinv : 1 < ‖(liZeroTransform (value p))⁻¹‖ := by
      rw [norm_inv]
      exact (one_lt_inv₀ hqpos).2 (lt_of_not_ge hq)
    exact hinv.le.trans (le_max_right _ _)

theorem one_lt_pairedLiOrbitRadius_of_re_ne_half
    {index : Type*} {value : index -> Complex}
    (hzero : ∀ p, value p ≠ 0) (hone : ∀ p, value p ≠ 1)
    (p : index) (hoff : (value p).re ≠ 1 / 2) :
    1 < pairedLiOrbitRadius value p := by
  rcases lt_or_gt_of_ne hoff with hleft | hright
  · exact ((one_lt_norm_liZeroTransform_iff (hzero p)).2 hleft).trans_le
      (le_max_left _ _)
  · have hreflectLine : (1 - value p).re < 1 / 2 := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have hlarge := (one_lt_norm_liZeroTransform_iff
      (sub_ne_zero.mpr (hone p).symm)).2 hreflectLine
    rw [liZeroTransform_one_sub (hzero p) (hone p)] at hlarge
    exact hlarge.trans_le (le_max_right _ _)

theorem eventually_pairedLiOrbitRadius_lt
    {index : Type*} {value : index -> Complex} (reflect : index ≃ index)
    (hreflect : ∀ p, value (reflect p) = 1 - value p)
    (hzero : ∀ p, value p ≠ 0) (hone : ∀ p, value p ≠ 1)
    (hfinite : ∀ B : Real, ({p | ‖value p‖ <= B} : Set index).Finite)
    {c : Real} (hc : 1 < c) :
    ∀ᶠ p : index in Filter.cofinite, pairedLiOrbitRadius value p < c := by
  let B : Real := 1 / (c - 1)
  have hlarge : ∀ᶠ p : index in Filter.cofinite, B < ‖value p‖ := by
    filter_upwards [(hfinite B).eventually_cofinite_notMem] with p hp
    exact lt_of_not_ge (by simpa using hp)
  have hlargeReflect : ∀ᶠ p : index in Filter.cofinite, B < ‖1 - value p‖ := by
    have h := reflect.injective.tendsto_cofinite.eventually hlarge
    simpa only [hreflect] using h
  filter_upwards [hlarge, hlargeReflect] with p hp hpReflect
  have hleft : ‖liZeroTransform (value p)‖ < c :=
    norm_liZeroTransform_lt_of_one_div_sub_one_lt_norm hc hp
  have hright : ‖(liZeroTransform (value p))⁻¹‖ < c := by
    rw [← liZeroTransform_one_sub (hzero p) (hone p)]
    exact norm_liZeroTransform_lt_of_one_div_sub_one_lt_norm hc hpReflect
  exact max_lt hleft hright

theorem finite_pairedLiOrbitRadius_superlevel
    {index : Type*} {value : index -> Complex} (reflect : index ≃ index)
    (hreflect : ∀ p, value (reflect p) = 1 - value p)
    (hzero : ∀ p, value p ≠ 0) (hone : ∀ p, value p ≠ 1)
    (hfinite : ∀ B : Real, ({p | ‖value p‖ <= B} : Set index).Finite)
    {c : Real} (hc : 1 < c) :
    ({p | c <= pairedLiOrbitRadius value p} : Set index).Finite := by
  simpa only [not_lt] using
    (Filter.eventually_cofinite.mp
      (eventually_pairedLiOrbitRadius_lt reflect hreflect hzero hone hfinite hc))

/-- A summable reciprocal-square weight for both values in an abstract reflection orbit. -/
def pairedLiReciprocalSqWeight {index : Type*} (value : index -> Complex)
    (p : index) : Real :=
  ‖value p‖⁻¹ ^ (2 : Nat) + ‖1 - value p‖⁻¹ ^ (2 : Nat)

theorem summable_pairedLiReciprocalSqWeight
    {index : Type*} {value : index -> Complex} (reflect : index ≃ index)
    (hreflect : ∀ p, value (reflect p) = 1 - value p)
    (hsum : Summable (fun p => ‖value p‖⁻¹ ^ (2 : Nat))) :
    Summable (pairedLiReciprocalSqWeight value) := by
  have hreflectSum : Summable (fun p => ‖value (reflect p)‖⁻¹ ^ (2 : Nat)) :=
    hsum.comp_injective reflect.injective
  exact hsum.add (by
    simpa only [hreflect] using hreflectSum)

theorem pairedLiReciprocalSqWeight_nonneg
    {index : Type*} {value : index -> Complex} (p : index) :
    0 <= pairedLiReciprocalSqWeight value p :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem norm_pairedLiZeroTerm_le
    {index : Type*} {value : index -> Complex}
    (hzero : ∀ p, value p ≠ 0) (hone : ∀ p, value p ≠ 1)
    (n : Nat) (p : index) :
    ‖pairedLiZeroTerm value n p‖ <=
      ((n + 1 : Nat) : Real) ^ (2 : Nat) * pairedLiOrbitRadius value p ^ (n + 1) *
        pairedLiReciprocalSqWeight value p := by
  let m : Nat := n + 1
  let rho : Complex := value p
  let q : Complex := liZeroTransform rho
  let r : Real := pairedLiOrbitRadius value p
  have hm : 0 < m := by simp [m]
  have hrhoZero : rho ≠ 0 := hzero p
  have hrhoOne : rho ≠ 1 := hone p
  have hqzero : q ≠ 0 := liZeroTransform_ne_zero hrhoZero hrhoOne
  have hr : 1 <= r := one_le_pairedLiOrbitRadius hzero hone p
  have hqLeft : ‖q‖ <= r := le_max_left _ _
  have hqRight : ‖q⁻¹‖ <= r := le_max_right _ _
  have hreflect : liZeroTransform (1 - rho) = q⁻¹ :=
    liZeroTransform_one_sub hrhoZero hrhoOne
  have hproduct :
      liRawZeroTerm m rho + liRawZeroTerm m (1 - rho) =
        liRawZeroTerm m rho * liRawZeroTerm m (1 - rho) :=
    liRawZeroTerm_add_reflect_eq_mul m hrhoZero hrhoOne
  have hweight :
      ‖1 / rho‖ ^ (2 : Nat) + ‖1 / (1 - rho)‖ ^ (2 : Nat) =
        pairedLiReciprocalSqWeight value p := by
    simp [pairedLiReciprocalSqWeight, rho, one_div]
  have hab (a b : Real) (ha : 0 <= a) (hb : 0 <= b) :
      a * b <= a ^ (2 : Nat) + b ^ (2 : Nat) := by
    nlinarith [sq_nonneg (a - b)]
  by_cases hq : ‖q‖ <= 1
  · have hleft := norm_liRawZeroTerm_le m hm rho 1 le_rfl hq
    have hright := norm_liRawZeroTerm_le m hm (1 - rho) r hr (by
      rw [hreflect]
      exact hqRight)
    have hrpow : r ^ (m - 1) <= r ^ m :=
      pow_le_pow_right₀ hr (Nat.sub_le m 1)
    have hmul := mul_le_mul hleft hright (norm_nonneg _) (by positivity)
    have hab' := hab ‖1 / rho‖ ‖1 / (1 - rho)‖ (norm_nonneg _) (norm_nonneg _)
    calc
      ‖pairedLiZeroTerm value n p‖ =
          (‖liRawZeroTerm m rho‖ * ‖liRawZeroTerm m (1 - rho)‖) / 2 := by
        rw [pairedLiZeroTerm, show n + 1 = m by rfl, hproduct,
          norm_div, norm_mul, norm_ofNat]
      _ <= ‖liRawZeroTerm m rho‖ * ‖liRawZeroTerm m (1 - rho)‖ := by
        exact div_le_self (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
      _ <= ((m : Real) * 1 ^ (m - 1) * ‖1 / rho‖) *
          ((m : Real) * r ^ (m - 1) * ‖1 / (1 - rho)‖) := hmul
      _ = (m : Real) ^ (2 : Nat) * r ^ (m - 1) *
          (‖1 / rho‖ * ‖1 / (1 - rho)‖) := by ring
      _ <= (m : Real) ^ (2 : Nat) * r ^ m *
          (‖1 / rho‖ * ‖1 / (1 - rho)‖) := by gcongr
      _ <= (m : Real) ^ (2 : Nat) * r ^ m *
          (‖1 / rho‖ ^ (2 : Nat) + ‖1 / (1 - rho)‖ ^ (2 : Nat)) := by gcongr
      _ = ((n + 1 : Nat) : Real) ^ (2 : Nat) *
          pairedLiOrbitRadius value p ^ (n + 1) *
            pairedLiReciprocalSqWeight value p := by rw [hweight]
  · have hqOne : ‖q⁻¹‖ <= 1 := by
      rw [norm_inv]
      exact (inv_le_one₀ (norm_pos_iff.mpr hqzero)).2 (le_of_not_ge hq)
    have hleft := norm_liRawZeroTerm_le m hm rho r hr hqLeft
    have hright := norm_liRawZeroTerm_le m hm (1 - rho) 1 le_rfl (by
      rw [hreflect]
      exact hqOne)
    have hrpow : r ^ (m - 1) <= r ^ m :=
      pow_le_pow_right₀ hr (Nat.sub_le m 1)
    have hmul := mul_le_mul hleft hright (norm_nonneg _) (by positivity)
    have hab' := hab ‖1 / rho‖ ‖1 / (1 - rho)‖ (norm_nonneg _) (norm_nonneg _)
    calc
      ‖pairedLiZeroTerm value n p‖ =
          (‖liRawZeroTerm m rho‖ * ‖liRawZeroTerm m (1 - rho)‖) / 2 := by
        rw [pairedLiZeroTerm, show n + 1 = m by rfl, hproduct,
          norm_div, norm_mul, norm_ofNat]
      _ <= ‖liRawZeroTerm m rho‖ * ‖liRawZeroTerm m (1 - rho)‖ := by
        exact div_le_self (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
      _ <= ((m : Real) * r ^ (m - 1) * ‖1 / rho‖) *
          ((m : Real) * 1 ^ (m - 1) * ‖1 / (1 - rho)‖) := hmul
      _ = (m : Real) ^ (2 : Nat) * r ^ (m - 1) *
          (‖1 / rho‖ * ‖1 / (1 - rho)‖) := by ring
      _ <= (m : Real) ^ (2 : Nat) * r ^ m *
          (‖1 / rho‖ * ‖1 / (1 - rho)‖) := by gcongr
      _ <= (m : Real) ^ (2 : Nat) * r ^ m *
          (‖1 / rho‖ ^ (2 : Nat) + ‖1 / (1 - rho)‖ ^ (2 : Nat)) := by gcongr
      _ = ((n + 1 : Nat) : Real) ^ (2 : Nat) *
          pairedLiOrbitRadius value p ^ (n + 1) *
            pairedLiReciprocalSqWeight value p := by rw [hweight]

theorem norm_tsum_indicator_compl_pairedLiZeroTerm_le
    {index : Type*} {value : index -> Complex}
    (hzero : ∀ p, value p ≠ 0) (hone : ∀ p, value p ≠ 1)
    (htermSum : ∀ n, Summable (pairedLiZeroTerm value n))
    (hweightSum : Summable (pairedLiReciprocalSqWeight value))
    (n : Nat) (s : Set index) (c : Real) (hc : 0 <= c)
    (hs : ∀ p, p ∉ s -> pairedLiOrbitRadius value p <= c) :
    ‖∑' p, sᶜ.indicator (pairedLiZeroTerm value n) p‖ <=
      ((n + 1 : Nat) : Real) ^ (2 : Nat) * c ^ (n + 1) *
        ∑' p, pairedLiReciprocalSqWeight value p := by
  let scale : Real := ((n + 1 : Nat) : Real) ^ (2 : Nat) * c ^ (n + 1)
  have hterm : Summable (sᶜ.indicator (pairedLiZeroTerm value n)) :=
    (htermSum n).indicator _
  have hmajor : Summable (fun p => scale * pairedLiReciprocalSqWeight value p) :=
    hweightSum.mul_left scale
  have hpoint (p : index) :
      ‖sᶜ.indicator (pairedLiZeroTerm value n) p‖ <=
        scale * pairedLiReciprocalSqWeight value p := by
    by_cases hp : p ∈ s
    · rw [Set.indicator_of_notMem (by simpa using hp)]
      simpa [scale] using mul_nonneg
        (mul_nonneg (sq_nonneg (((n + 1 : Nat) : Real))) (pow_nonneg hc (n + 1)))
        (pairedLiReciprocalSqWeight_nonneg (value := value) p)
    · rw [Set.indicator_of_mem (by simpa using hp)]
      calc
        ‖pairedLiZeroTerm value n p‖ <=
            ((n + 1 : Nat) : Real) ^ (2 : Nat) *
              pairedLiOrbitRadius value p ^ (n + 1) *
                pairedLiReciprocalSqWeight value p :=
          norm_pairedLiZeroTerm_le hzero hone n p
        _ <= ((n + 1 : Nat) : Real) ^ (2 : Nat) * c ^ (n + 1) *
              pairedLiReciprocalSqWeight value p := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀
                (zero_le_one.trans (one_le_pairedLiOrbitRadius hzero hone p)) (hs p hp) _)
              (sq_nonneg (((n + 1 : Nat) : Real))))
            (pairedLiReciprocalSqWeight_nonneg (value := value) p)
        _ = scale * pairedLiReciprocalSqWeight value p := rfl
  calc
    ‖∑' p, sᶜ.indicator (pairedLiZeroTerm value n) p‖ <=
        ∑' p, ‖sᶜ.indicator (pairedLiZeroTerm value n) p‖ :=
      norm_tsum_le_tsum_norm hterm.norm
    _ <= ∑' p, scale * pairedLiReciprocalSqWeight value p :=
      hterm.norm.tsum_le_tsum hpoint hmajor
    _ = scale * ∑' p, pairedLiReciprocalSqWeight value p := tsum_mul_left
    _ = ((n + 1 : Nat) : Real) ^ (2 : Nat) * c ^ (n + 1) *
          ∑' p, pairedLiReciprocalSqWeight value p := rfl

/-- The member of a reciprocal transform pair whose norm is at least one. -/
def pairedLiDominantTransform {index : Type*} (value : index -> Complex)
    (p : index) : Complex :=
  let q := liZeroTransform (value p)
  if ‖q‖ <= 1 then q⁻¹ else q

theorem pairedLiDominantTransform_ne_zero
    {index : Type*} {value : index -> Complex}
    (hzero : ∀ p, value p ≠ 0) (hone : ∀ p, value p ≠ 1) (p : index) :
    pairedLiDominantTransform value p ≠ 0 := by
  have hqzero := liZeroTransform_ne_zero (hzero p) (hone p)
  simp only [pairedLiDominantTransform]
  split <;> simp [hqzero]

theorem norm_pairedLiDominantTransform
    {index : Type*} {value : index -> Complex}
    (hzero : ∀ p, value p ≠ 0) (hone : ∀ p, value p ≠ 1) (p : index) :
    ‖pairedLiDominantTransform value p‖ = pairedLiOrbitRadius value p := by
  let q := liZeroTransform (value p)
  have hqzero : q ≠ 0 := liZeroTransform_ne_zero (hzero p) (hone p)
  have hqpos : 0 < ‖q‖ := norm_pos_iff.mpr hqzero
  by_cases hq : ‖q‖ <= 1
  · have honeInv : 1 <= ‖q⁻¹‖ := by
      rw [norm_inv]
      exact (one_le_inv₀ hqpos).2 hq
    have hle : ‖q‖ <= ‖q⁻¹‖ := hq.trans honeInv
    have hq' : ‖liZeroTransform (value p)‖ <= 1 := by simpa only [q] using hq
    rw [pairedLiDominantTransform, if_pos hq', pairedLiOrbitRadius,
      max_eq_right (by simpa only [q] using hle)]
  · have hone : 1 < ‖q‖ := lt_of_not_ge hq
    have hinv : ‖q⁻¹‖ < 1 := by
      rw [norm_inv]
      exact (inv_lt_one₀ hqpos).2 hone
    have hle : ‖q⁻¹‖ <= ‖q‖ := hinv.le.trans hone.le
    have hq' : ¬‖liZeroTransform (value p)‖ <= 1 := by simpa only [q] using hq
    rw [pairedLiDominantTransform, if_neg hq', pairedLiOrbitRadius,
      max_eq_left (by simpa only [q] using hle)]

theorem pairedLiZeroTerm_eq_dominant
    {index : Type*} {value : index -> Complex}
    (hzero : ∀ p, value p ≠ 0) (hone : ∀ p, value p ≠ 1)
    (n : Nat) (p : index) :
    pairedLiZeroTerm value n p =
      1 - (pairedLiDominantTransform value p ^ (n + 1) +
        (pairedLiDominantTransform value p)⁻¹ ^ (n + 1)) / 2 := by
  let rho := value p
  let q := liZeroTransform rho
  have hqzero : q ≠ 0 := liZeroTransform_ne_zero (hzero p) (hone p)
  have hreflect : liZeroTransform (1 - rho) = q⁻¹ :=
    liZeroTransform_one_sub (hzero p) (hone p)
  change ((1 - q ^ (n + 1)) +
      (1 - liZeroTransform (1 - rho) ^ (n + 1))) / 2 = _
  rw [hreflect]
  change ((1 - q ^ (n + 1)) + (1 - q⁻¹ ^ (n + 1))) / 2 =
    1 - ((if ‖q‖ <= 1 then q⁻¹ else q) ^ (n + 1) +
      (if ‖q‖ <= 1 then q⁻¹ else q)⁻¹ ^ (n + 1)) / 2
  by_cases hq : ‖q‖ <= 1
  · simp only [if_pos hq, inv_inv]
    ring
  · simp only [if_neg hq]
    ring

/-- The unit phase of the dominant abstract Li transform. -/
def pairedLiDominantPhase
    {index : Type*} {value : index -> Complex}
    (hzero : ∀ p, value p ≠ 0) (hone : ∀ p, value p ≠ 1) (p : index) : Circle :=
  ⟨pairedLiDominantTransform value p / (pairedLiOrbitRadius value p : Complex), by
    have hr : 0 < pairedLiOrbitRadius value p :=
      zero_lt_one.trans_le (one_le_pairedLiOrbitRadius hzero hone p)
    have hnorm : ‖pairedLiDominantTransform value p /
        (pairedLiOrbitRadius value p : Complex)‖ = 1 := by
      rw [norm_div, norm_pairedLiDominantTransform hzero hone]
      simp [abs_of_pos hr, hr.ne']
    simpa [Submonoid.unitSphere] using mem_sphere_zero_iff_norm.mpr hnorm⟩

@[simp]
theorem coe_pairedLiDominantPhase
    {index : Type*} {value : index -> Complex}
    (hzero : ∀ p, value p ≠ 0) (hone : ∀ p, value p ≠ 1) (p : index) :
    (pairedLiDominantPhase hzero hone p : Complex) =
      pairedLiDominantTransform value p / (pairedLiOrbitRadius value p : Complex) :=
  rfl

theorem three_quarters_mul_pairedLiOrbitRadius_pow_lt_dominant_pow_re
    {index : Type*} {value : index -> Complex}
    (hzero : ∀ p, value p ≠ 0) (hone : ∀ p, value p ≠ 1)
    (p : index) (m : Nat)
    (hphase : dist (pairedLiDominantPhase hzero hone p ^ m) 1 < 1 / 4) :
    3 / 4 * pairedLiOrbitRadius value p ^ m <
      (pairedLiDominantTransform value p ^ m).re := by
  let d := pairedLiDominantTransform value p
  let r := pairedLiOrbitRadius value p
  let u := pairedLiDominantPhase hzero hone p
  have hr : 0 < r := zero_lt_one.trans_le (one_le_pairedLiOrbitRadius hzero hone p)
  have hdist : ‖((u ^ m : Circle) : Complex) - 1‖ < 1 / 4 := by
    have hphase' : dist (u ^ m) 1 < 1 / 4 := by simpa only [u] using hphase
    change dist (((u ^ m : Circle) : Complex)) ((1 : Circle) : Complex) < 1 / 4 at hphase'
    simpa only [Circle.coe_one, Complex.dist_eq] using hphase'
  have hrePhase : 3 / 4 < (((u ^ m : Circle) : Complex)).re := by
    have habs := Complex.abs_re_le_norm ((((u ^ m : Circle) : Complex)) - 1)
    have hlt := habs.trans_lt hdist
    simp only [Complex.sub_re, Complex.one_re] at hlt
    linarith [(abs_lt.mp hlt).1]
  have hrecover : pairedLiDominantTransform value p =
      (pairedLiOrbitRadius value p : Complex) *
        (pairedLiDominantPhase hzero hone p : Complex) := by
    rw [coe_pairedLiDominantPhase]
    have hrComplex : (pairedLiOrbitRadius value p : Complex) ≠ 0 := by
      exact_mod_cast (zero_lt_one.trans_le
        (one_le_pairedLiOrbitRadius hzero hone p)).ne'
    field_simp [hrComplex]
  have hmul := mul_lt_mul_of_pos_left hrePhase (pow_pos hr m)
  have hpowRe : (pairedLiDominantTransform value p ^ m).re =
      pairedLiOrbitRadius value p ^ m *
        (((pairedLiDominantPhase hzero hone p ^ m : Circle) : Complex)).re := by
    rw [hrecover, mul_pow, ← Complex.ofReal_pow, ← Circle.coe_pow, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [hpowRe]
  simpa only [r, u, mul_comm] using hmul

theorem pairedLiZeroTerm_re_le_of_phase_close
    {index : Type*} {value : index -> Complex}
    (hzero : ∀ p, value p ≠ 0) (hone : ∀ p, value p ≠ 1)
    (n : Nat) (p : index)
    (hphase : dist (pairedLiDominantPhase hzero hone p ^ (n + 1)) 1 < 1 / 4) :
    (pairedLiZeroTerm value n p).re <=
      3 / 2 - 3 / 8 * pairedLiOrbitRadius value p ^ (n + 1) := by
  let d := pairedLiDominantTransform value p
  let r := pairedLiOrbitRadius value p
  let m := n + 1
  have hr : 1 <= r := one_le_pairedLiOrbitRadius hzero hone p
  have hrpos : 0 < r := zero_lt_one.trans_le hr
  have hdre : 3 / 4 * r ^ m < (d ^ m).re :=
    three_quarters_mul_pairedLiOrbitRadius_pow_lt_dominant_pow_re
      hzero hone p m hphase
  have hnormInv : ‖d⁻¹ ^ m‖ <= 1 := by
    rw [norm_pow, norm_inv, norm_pairedLiDominantTransform hzero hone]
    exact pow_le_one₀ (inv_nonneg.mpr hrpos.le) ((inv_le_one₀ hrpos).2 hr)
  have hinvRe : -1 <= (d⁻¹ ^ m).re := by
    have habs := Complex.abs_re_le_norm (d⁻¹ ^ m)
    have hneg := neg_abs_le (d⁻¹ ^ m).re
    linarith
  have hre : (pairedLiZeroTerm value n p).re =
      1 - ((d ^ m).re + (d⁻¹ ^ m).re) / 2 := by
    rw [pairedLiZeroTerm_eq_dominant hzero hone]
    norm_num [d, m]
  rw [hre]
  linarith

theorem sum_toFinset_add_tsum_indicator_compl_eq_tsum_generic
    {index : Type*} {f : index -> Complex} (hf : Summable f)
    {s : Set index} (hs : s.Finite) :
    (∑ p ∈ hs.toFinset, f p) + ∑' p, sᶜ.indicator f p = ∑' p, f p := by
  rw [sum_eq_tsum_indicator]
  simp only [hs.coe_toFinset]
  rw [← (hf.indicator s).tsum_add (hf.indicator sᶜ)]
  apply tsum_congr
  intro p
  by_cases hp : p ∈ s <;> simp [hp]

/-- An off-line member of an abstract reflected zero divisor forces a negative Li coefficient. -/
theorem exists_coefficient_re_neg_of_value_re_ne_half
    {index : Type*} {value : index -> Complex} {coefficient : Nat -> Complex}
    (reflect : index ≃ index) (hreflect : ∀ p, value (reflect p) = 1 - value p)
    (hzero : ∀ p, value p ≠ 0) (hone : ∀ p, value p ≠ 1)
    (hfinite : ∀ B : Real, ({p | ‖value p‖ <= B} : Set index).Finite)
    (hweightBase : Summable (fun p => ‖value p‖⁻¹ ^ (2 : Nat)))
    (htermSum : ∀ n, Summable (pairedLiZeroTerm value n))
    (hformula : ∀ n, coefficient n = ∑' p, pairedLiZeroTerm value n p)
    (p0 : index) (hoff : (value p0).re ≠ 1 / 2) :
    ∃ n : Nat, (coefficient n).re < 0 := by
  classical
  let radius : Real := pairedLiOrbitRadius value p0
  let c : Real := (1 + radius) / 2
  let weight : Real := ∑' p, pairedLiReciprocalSqWeight value p
  have hradius : 1 < radius :=
    one_lt_pairedLiOrbitRadius_of_re_ne_half hzero hone p0 hoff
  have hcOne : 1 < c := by dsimp only [c]; linarith
  have hcpos : 0 < c := zero_lt_one.trans hcOne
  have hcRadius : c < radius := by dsimp only [c]; linarith
  let mainSet : Set index := {p | c <= pairedLiOrbitRadius value p}
  have hmainFinite : mainSet.Finite := by
    simpa only [mainSet] using
      finite_pairedLiOrbitRadius_superlevel reflect hreflect hzero hone hfinite hcOne
  letI : Fintype mainSet := hmainFinite.fintype
  have hp0Main : p0 ∈ mainSet := by
    change c <= radius
    exact hcRadius.le
  have hradiusPow : ∀ᶠ m : Nat in atTop, 8 <= radius ^ m :=
    (tendsto_pow_atTop_atTop_of_one_lt hradius).eventually_ge_atTop 8
  have hcPow : ∀ᶠ m : Nat in atTop, 4 <= c ^ m :=
    (tendsto_pow_atTop_atTop_of_one_lt hcOne).eventually_ge_atTop 4
  have htail : ∀ᶠ m : Nat in atTop,
      (m : Real) ^ (2 : Nat) * c ^ m * weight < 3 / 16 * radius ^ m :=
    eventually_sq_mul_pow_mul_lt_three_sixteenths_mul_pow
      c radius weight hcpos hcRadius
  obtain ⟨cutoff, hcutoff⟩ := eventually_atTop.1 (hradiusPow.and (hcPow.and htail))
  let phase : mainSet -> Circle := fun p => pairedLiDominantPhase hzero hone p.1
  obtain ⟨m, hmCutoff, _hmEven, hphase⟩ :=
    exists_even_gt_forall_circle_pow_dist_one_lt phase cutoff
      (by norm_num : (0 : Real) < 1 / 4)
  have hmLarge := hcutoff m hmCutoff.le
  have hmpos : 0 < m := lt_of_le_of_lt (Nat.zero_le cutoff) hmCutoff
  let n : Nat := m - 1
  have hn : n + 1 = m :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hmpos))
  have hphaseAt (p : index) (hp : p ∈ mainSet) :
      dist (pairedLiDominantPhase hzero hone p ^ (n + 1)) 1 < 1 / 4 := by
    rw [hn]
    exact hphase ⟨p, hp⟩
  have htermNonpos (p : index) (hp : p ∈ mainSet) :
      (pairedLiZeroTerm value n p).re <= 0 := by
    have hbound := pairedLiZeroTerm_re_le_of_phase_close
      hzero hone n p (hphaseAt p hp)
    rw [hn] at hbound
    have hcp : c <= pairedLiOrbitRadius value p := hp
    have hpow : c ^ m <= pairedLiOrbitRadius value p ^ m :=
      pow_le_pow_left₀ hcpos.le hcp m
    nlinarith [hmLarge.2.1]
  have hp0Term :
      (pairedLiZeroTerm value n p0).re <= -(3 / 16 * radius ^ m) := by
    have hbound := pairedLiZeroTerm_re_le_of_phase_close
      hzero hone n p0 (hphaseAt p0 hp0Main)
    rw [hn] at hbound
    nlinarith [hmLarge.1]
  let mainFinset : Finset index := hmainFinite.toFinset
  have hp0Finset : p0 ∈ mainFinset := by
    simpa only [mainFinset, hmainFinite.mem_toFinset] using hp0Main
  have herase :
      ∑ p ∈ mainFinset.erase p0, (pairedLiZeroTerm value n p).re <= 0 := by
    apply Finset.sum_nonpos
    intro p hp
    apply htermNonpos p
    have hpFinset : p ∈ mainFinset := (Finset.mem_erase.mp hp).2
    simpa only [mainFinset, hmainFinite.mem_toFinset] using hpFinset
  have hfiniteReal :
      ∑ p ∈ mainFinset, (pairedLiZeroTerm value n p).re <=
        -(3 / 16 * radius ^ m) := by
    rw [← Finset.sum_erase_add mainFinset
      (fun p => (pairedLiZeroTerm value n p).re) hp0Finset]
    exact add_le_of_nonpos_of_le herase hp0Term
  have hfiniteComplex :
      (∑ p ∈ mainFinset, pairedLiZeroTerm value n p).re <=
        -(3 / 16 * radius ^ m) := by
    simpa only [Complex.re_sum] using hfiniteReal
  let tail : Complex := ∑' p, mainSetᶜ.indicator (pairedLiZeroTerm value n) p
  have houtside : ∀ p, p ∉ mainSet -> pairedLiOrbitRadius value p <= c := by
    intro p hp
    exact (lt_of_not_ge hp).le
  have hweightSum :=
    summable_pairedLiReciprocalSqWeight reflect hreflect hweightBase
  have htailNormLe : ‖tail‖ <= (m : Real) ^ (2 : Nat) * c ^ m * weight := by
    have h := norm_tsum_indicator_compl_pairedLiZeroTerm_le
      hzero hone htermSum hweightSum n mainSet c hcpos.le houtside
    rw [hn] at h
    exact h
  have htailNorm : ‖tail‖ < 3 / 16 * radius ^ m :=
    htailNormLe.trans_lt hmLarge.2.2
  have hdecomp :
      (∑ p ∈ mainFinset, pairedLiZeroTerm value n p) + tail =
        ∑' p, pairedLiZeroTerm value n p := by
    simpa only [mainFinset, tail] using
      sum_toFinset_add_tsum_indicator_compl_eq_tsum_generic
        (htermSum n) hmainFinite
  have htotal : (∑' p, pairedLiZeroTerm value n p).re < 0 := by
    rw [← hdecomp, Complex.add_re]
    have htailRe := Complex.re_le_norm tail
    nlinarith
  refine ⟨n, ?_⟩
  rw [hformula n]
  exact htotal

/-- Abstract Bombieri-Lagarias criterion for a reflected multiplicity-bearing zero divisor. -/
theorem all_values_on_line_iff_forall_coefficient_re_nonneg
    {index : Type*} {value : index -> Complex} {coefficient : Nat -> Complex}
    (reflect : index ≃ index) (hreflect : ∀ p, value (reflect p) = 1 - value p)
    (hzero : ∀ p, value p ≠ 0) (hone : ∀ p, value p ≠ 1)
    (hfinite : ∀ B : Real, ({p | ‖value p‖ <= B} : Set index).Finite)
    (hweightBase : Summable (fun p => ‖value p‖⁻¹ ^ (2 : Nat)))
    (htermSum : ∀ n, Summable (pairedLiZeroTerm value n))
    (hformula : ∀ n, coefficient n = ∑' p, pairedLiZeroTerm value n p) :
    (∀ p, (value p).re = 1 / 2) <->
      ∀ n, 0 <= (coefficient n).re := by
  constructor
  · exact forall_coefficient_re_nonneg_of_pairedLiZeroFormula
      hzero hone htermSum hformula
  · intro hcoeff p
    by_contra hoff
    obtain ⟨n, hn⟩ := exists_coefficient_re_neg_of_value_re_ne_half
      reflect hreflect hzero hone hfinite hweightBase htermSum hformula p hoff
    exact (not_lt_of_ge (hcoeff n)) hn

/-- The nonzero multiplicity-bearing divisor index of an arbitrary entire function. -/
abbrev EntireLiDivisorZeroIndex (F : Complex -> Complex) :=
  Complex.Hadamard.divisorZeroIndex₀ F (Set.univ : Set Complex)

abbrev entireLiDivisorZeroValue
    {F : Complex -> Complex} (p : EntireLiDivisorZeroIndex F) : Complex :=
  Complex.Hadamard.divisorZeroIndex₀_val p

def entireLiLogDerivZeroTerm
    {F : Complex -> Complex} (p : EntireLiDivisorZeroIndex F) (z : Complex) : Complex :=
  1 / (z - entireLiDivisorZeroValue p) + 1 / entireLiDivisorZeroValue p

def entireLiLogDerivZeroDerivativeTerm
    {F : Complex -> Complex} (k : Nat) (p : EntireLiDivisorZeroIndex F)
    (z : Complex) : Complex :=
  (-1 : Complex) ^ k * (k.factorial : Complex) /
      (z - entireLiDivisorZeroValue p) ^ (k + 1) +
    if k = 0 then 1 / entireLiDivisorZeroValue p else 0

def entireLiNonzeroSet (F : Complex -> Complex) : Set Complex :=
  {z | F z ≠ 0}

theorem entireLiDivisorZeroValue_eq_zero
    {F : Complex -> Complex} (hF : Differentiable Complex F)
    (p : EntireLiDivisorZeroIndex F) : F (entireLiDivisorZeroValue p) = 0 := by
  have hsupport :=
    Complex.Hadamard.divisorZeroIndex₀_val_mem_divisor_support
      (f := F) (U := (Set.univ : Set Complex)) p
  have hdivisor : MeromorphicOn.divisor F Set.univ (entireLiDivisorZeroValue p) ≠ 0 := by
    simpa only [Function.mem_support] using hsupport
  have horder : analyticOrderNatAt F (entireLiDivisorZeroValue p) ≠ 0 := by
    intro hzero
    apply hdivisor
    rw [Complex.Hadamard.divisor_univ_eq_analyticOrderNatAt_int hF]
    simp [hzero]
  exact apply_eq_zero_of_analyticOrderNatAt_ne_zero horder

theorem ne_entireLiDivisorZeroValue_of_mem_nonzeroSet
    {F : Complex -> Complex} (hF : Differentiable Complex F)
    {z : Complex} (hz : z ∈ entireLiNonzeroSet F) (p : EntireLiDivisorZeroIndex F) :
    z ≠ entireLiDivisorZeroValue p := by
  intro hzp
  apply hz
  rw [hzp]
  exact entireLiDivisorZeroValue_eq_zero hF p

theorem iteratedDeriv_entireLiLogDerivZeroTerm
    {F : Complex -> Complex} (k : Nat) (p : EntireLiDivisorZeroIndex F) {z : Complex}
    (hz : z ≠ entireLiDivisorZeroValue p) :
    iteratedDeriv k (entireLiLogDerivZeroTerm p) z =
      entireLiLogDerivZeroDerivativeTerm k p z := by
  rcases k with _ | k
  · simp [entireLiLogDerivZeroTerm, entireLiLogDerivZeroDerivativeTerm]
  · have hinv : ContDiffAt Complex (k + 1)
        (fun w : Complex => 1 / (w - entireLiDivisorZeroValue p)) z := by
      have hsub : ContDiffAt Complex (k + 1)
          (fun w : Complex => w - entireLiDivisorZeroValue p) z := by fun_prop
      simpa only [one_div] using hsub.inv (sub_ne_zero.mpr hz)
    have hconst : ContDiffAt Complex (k + 1)
        (fun _ : Complex => 1 / entireLiDivisorZeroValue p) z := by fun_prop
    rw [show entireLiLogDerivZeroTerm p =
        (fun w : Complex => 1 / (w - entireLiDivisorZeroValue p)) +
          fun _ : Complex => 1 / entireLiDivisorZeroValue p by
      funext w
      rfl]
    rw [iteratedDeriv_add hinv hconst]
    have hfirst :
        iteratedDeriv (k + 1)
            (fun w : Complex => 1 / (w - entireLiDivisorZeroValue p)) z =
          (-1 : Complex) ^ (k + 1) * ((k + 1).factorial : Complex) *
            (z - entireLiDivisorZeroValue p) ^ (-1 - (k + 1 : Nat) : Int) := by
      rw [iteratedDeriv_eq_iterate]
      simpa only [one_div, one_mul, mul_one, one_pow] using
        congrFun (iter_deriv_inv_linear_sub (k + 1) (1 : Complex)
          (entireLiDivisorZeroValue p)) z
    have hkzero : k + 1 ≠ 0 := by omega
    have hconstDeriv :
        iteratedDeriv (k + 1) (fun _ : Complex => 1 / entireLiDivisorZeroValue p) z = 0 := by
      rw [iteratedDeriv_const, if_neg hkzero]
    rw [hfirst, hconstDeriv, add_zero]
    rw [entireLiLogDerivZeroDerivativeTerm, if_neg hkzero, add_zero]
    rw [show (-1 : Int) - ((k + 1 : Nat) : Int) = -(((k + 1) + 1 : Nat) : Int) by omega]
    rw [zpow_neg_coe_of_pos (z - entireLiDivisorZeroValue p) (by omega)]
    rw [div_eq_mul_inv]

theorem isOpen_entireLiNonzeroSet
    {F : Complex -> Complex} (hF : Differentiable Complex F) :
    IsOpen (entireLiNonzeroSet F) :=
  isOpen_ne_fun hF.continuous continuous_const

theorem summable_entireLiLogDerivZeroTerm_of_mem_nonzeroSet
    {F : Complex -> Complex}
    (hF : Differentiable Complex F)
    (hsum : Summable (fun p : EntireLiDivisorZeroIndex F =>
      ‖entireLiDivisorZeroValue p‖⁻¹ ^ (2 : Nat)))
    {z : Complex} (hz : z ∈ entireLiNonzeroSet F) :
    Summable (fun p : EntireLiDivisorZeroIndex F => entireLiLogDerivZeroTerm p z) := by
  apply Complex.Hadamard.summable_logDerivTerms_divisorZeroIndex₀_of_summable_inv_sq hsum
  intro p hzp
  exact ne_entireLiDivisorZeroValue_of_mem_nonzeroSet hF hz p hzp

theorem summableLocallyUniformlyOn_entireLiLogDerivZeroDerivativeTerm
    {F : Complex -> Complex}
    (hF : Differentiable Complex F)
    (hsum : Summable (fun p : EntireLiDivisorZeroIndex F =>
      ‖entireLiDivisorZeroValue p‖⁻¹ ^ (2 : Nat)))
    (k : Nat) (hk : 1 <= k) :
    SummableLocallyUniformlyOn
      (fun p : EntireLiDivisorZeroIndex F => entireLiLogDerivZeroDerivativeTerm k p)
      (entireLiNonzeroSet F) := by
  apply SummableLocallyUniformlyOn.of_locally_bounded_eventually
    (isOpen_entireLiNonzeroSet hF)
  intro compact hcompactSubset hcompact
  obtain ⟨radius0, hradius0⟩ := isBounded_iff_forall_norm_le.1 hcompact.isBounded
  let radius : Real := max radius0 1
  have hradiusPos : 0 < radius :=
    lt_of_lt_of_le (by norm_num : (0 : Real) < 1) (le_max_right _ _)
  have hnormCompact : ∀ z ∈ compact, ‖z‖ <= radius := fun z hz =>
    le_trans (hradius0 z hz) (le_max_left _ _)
  let major : EntireLiDivisorZeroIndex F -> Real := fun p =>
    ((k.factorial : Real) * 2 ^ (k + 1)) *
      (‖entireLiDivisorZeroValue p‖⁻¹ ^ (2 : Nat))
  have hmajor : Summable major :=
    hsum.mul_left ((k.factorial : Real) * 2 ^ (k + 1))
  refine ⟨major, hmajor, ?_⟩
  let bound : Real := max (2 * radius) 1
  have hlarge : ∀ᶠ p : EntireLiDivisorZeroIndex F in Filter.cofinite,
      bound < ‖entireLiDivisorZeroValue p‖ := by
    have hfinite :
        ({p : EntireLiDivisorZeroIndex F |
          ‖entireLiDivisorZeroValue p‖ <= bound} : Set _).Finite := by
      have hball : Metric.closedBall (0 : Complex) bound <= (Set.univ : Set Complex) := by simp
      exact Complex.Hadamard.divisorZeroIndex₀_norm_le_finite
        (f := F) (U := (Set.univ : Set Complex)) bound hball
    filter_upwards [hfinite.eventually_cofinite_notMem] with p hp
    exact lt_of_not_ge (by simpa using hp)
  filter_upwards [hlarge] with p hp z hzCompact
  let root : Complex := entireLiDivisorZeroValue p
  have hrootZero : root ≠ 0 := Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p
  have hzrootZero : z - root ≠ 0 := sub_ne_zero.mpr
    (ne_entireLiDivisorZeroValue_of_mem_nonzeroSet hF (hcompactSubset hzCompact) p)
  have hrootRadius : 2 * radius < ‖root‖ := lt_of_le_of_lt (le_max_left _ _) hp
  have hrootOne : 1 < ‖root‖ := lt_of_le_of_lt (le_max_right _ _) hp
  have htriangle : ‖root‖ <= ‖z‖ + ‖z - root‖ := by
    have hraw : ‖root‖ <= ‖z‖ + ‖root - z‖ := by
      have h := norm_add_le z (root - z)
      simpa [root, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
    simpa [norm_sub_rev] using hraw
  have hzrootLower : ‖root‖ / 2 <= ‖z - root‖ := by
    nlinarith [htriangle, hnormCompact z hzCompact, hrootRadius]
  have hinv : ‖z - root‖⁻¹ <= 2 * ‖root‖⁻¹ := by
    have hrootNormPos : 0 < ‖root‖ := norm_pos_iff.mpr hrootZero
    have hzrootNormPos : 0 < ‖z - root‖ := norm_pos_iff.mpr hzrootZero
    have hraw : ‖z - root‖⁻¹ <= (‖root‖ / 2)⁻¹ := by
      simpa only [one_div] using
        one_div_le_one_div_of_le (by positivity : 0 < ‖root‖ / 2) hzrootLower
    have hhalfInv : (‖root‖ / 2)⁻¹ = 2 * ‖root‖⁻¹ := by
      field_simp [hrootNormPos.ne']
    simpa only [hhalfInv] using hraw
  have hpow : ‖z - root‖⁻¹ ^ (k + 1) <= (2 * ‖root‖⁻¹) ^ (k + 1) :=
    pow_le_pow_left₀ (inv_nonneg.2 (norm_nonneg _)) hinv (k + 1)
  have hrootInvOne : ‖root‖⁻¹ <= 1 := inv_le_one_of_one_le₀ hrootOne.le
  have hrootInvPow : ‖root‖⁻¹ ^ (k + 1) <= ‖root‖⁻¹ ^ (2 : Nat) :=
    pow_le_pow_of_le_one (inv_nonneg.2 (norm_nonneg _)) hrootInvOne (by omega)
  have hnorm : ‖entireLiLogDerivZeroDerivativeTerm k p z‖ =
      (k.factorial : Real) * ‖z - root‖⁻¹ ^ (k + 1) := by
    rw [entireLiLogDerivZeroDerivativeTerm, if_neg (by omega : k ≠ 0), add_zero]
    simp [root, norm_pow, div_eq_mul_inv, inv_pow]
  rw [hnorm]
  calc
    (k.factorial : Real) * ‖z - root‖⁻¹ ^ (k + 1) <=
        (k.factorial : Real) * (2 * ‖root‖⁻¹) ^ (k + 1) := by gcongr
    _ = ((k.factorial : Real) * 2 ^ (k + 1)) * ‖root‖⁻¹ ^ (k + 1) := by
      rw [mul_pow]
      ring
    _ <= ((k.factorial : Real) * 2 ^ (k + 1)) * ‖root‖⁻¹ ^ (2 : Nat) := by gcongr
    _ = major p := by simp [major, root]

theorem summableLocallyUniformlyOn_iteratedDerivWithin_entireLiLogDerivZeroTerm
    {F : Complex -> Complex}
    (hF : Differentiable Complex F)
    (hsum : Summable (fun p : EntireLiDivisorZeroIndex F =>
      ‖entireLiDivisorZeroValue p‖⁻¹ ^ (2 : Nat)))
    (k : Nat) (hk : 1 <= k) :
    SummableLocallyUniformlyOn
      (fun p : EntireLiDivisorZeroIndex F =>
        iteratedDerivWithin k (entireLiLogDerivZeroTerm p) (entireLiNonzeroSet F))
      (entireLiNonzeroSet F) := by
  apply SummableLocallyUniformlyOn_congr
    (fun p z hz => ?_)
    (summableLocallyUniformlyOn_entireLiLogDerivZeroDerivativeTerm hF hsum k hk)
  rw [iteratedDerivWithin_of_isOpen (isOpen_entireLiNonzeroSet hF) hz]
  exact (iteratedDeriv_entireLiLogDerivZeroTerm k p
    (ne_entireLiDivisorZeroValue_of_mem_nonzeroSet hF hz p)).symm

theorem differentiableAt_iteratedDerivWithin_entireLiLogDerivZeroTerm
    {F : Complex -> Complex} (hF : Differentiable Complex F)
    (p : EntireLiDivisorZeroIndex F) (k : Nat) {z : Complex}
    (hz : z ∈ entireLiNonzeroSet F) :
    DifferentiableAt Complex
      (iteratedDerivWithin k (entireLiLogDerivZeroTerm p) (entireLiNonzeroSet F)) z := by
  have heq :
      iteratedDerivWithin k (entireLiLogDerivZeroTerm p) (entireLiNonzeroSet F) =ᶠ[𝓝 z]
        entireLiLogDerivZeroDerivativeTerm k p := by
    filter_upwards [(isOpen_entireLiNonzeroSet hF).mem_nhds hz] with w hw
    rw [iteratedDerivWithin_of_isOpen (isOpen_entireLiNonzeroSet hF) hw]
    exact iteratedDeriv_entireLiLogDerivZeroTerm k p
      (ne_entireLiDivisorZeroValue_of_mem_nonzeroSet hF hw p)
  rw [heq.differentiableAt_iff]
  have hden : z - entireLiDivisorZeroValue p ≠ 0 := sub_ne_zero.mpr
    (ne_entireLiDivisorZeroValue_of_mem_nonzeroSet hF hz p)
  unfold entireLiLogDerivZeroDerivativeTerm
  have hmain : DifferentiableAt Complex
      (fun w : Complex => (-1 : Complex) ^ k * (k.factorial : Complex) /
        (w - entireLiDivisorZeroValue p) ^ (k + 1)) z := by
    apply DifferentiableAt.div
    · fun_prop
    · fun_prop
    · exact pow_ne_zero _ hden
  split_ifs <;> exact hmain.add (by fun_prop)

theorem iteratedDeriv_tsum_entireLiLogDerivZeroTerm
    {F : Complex -> Complex}
    (hF : Differentiable Complex F)
    (hsum : Summable (fun p : EntireLiDivisorZeroIndex F =>
      ‖entireLiDivisorZeroValue p‖⁻¹ ^ (2 : Nat)))
    (hone : F 1 ≠ 0) (k : Nat) :
    iteratedDeriv k
        (fun z : Complex => ∑' p : EntireLiDivisorZeroIndex F,
          entireLiLogDerivZeroTerm p z) 1 =
      ∑' p : EntireLiDivisorZeroIndex F,
        entireLiLogDerivZeroDerivativeTerm k p 1 := by
  have honeMem : (1 : Complex) ∈ entireLiNonzeroSet F := hone
  have hwithin := iteratedDerivWithin_tsum
    (f := fun p : EntireLiDivisorZeroIndex F => entireLiLogDerivZeroTerm p)
    k (isOpen_entireLiNonzeroSet hF) honeMem
    (fun z hz => summable_entireLiLogDerivZeroTerm_of_mem_nonzeroSet hF hsum hz)
    (fun j hj1 _hjk =>
      summableLocallyUniformlyOn_iteratedDerivWithin_entireLiLogDerivZeroTerm
        hF hsum j hj1)
    (fun p j z _hjk hz =>
      differentiableAt_iteratedDerivWithin_entireLiLogDerivZeroTerm hF p j hz)
  rw [iteratedDerivWithin_of_isOpen (isOpen_entireLiNonzeroSet hF) honeMem] at hwithin
  calc
    iteratedDeriv k
        (fun z : Complex => ∑' p : EntireLiDivisorZeroIndex F,
          entireLiLogDerivZeroTerm p z) 1 =
        ∑' p : EntireLiDivisorZeroIndex F,
          iteratedDerivWithin k (entireLiLogDerivZeroTerm p)
            (entireLiNonzeroSet F) 1 := hwithin
    _ = ∑' p : EntireLiDivisorZeroIndex F,
          entireLiLogDerivZeroDerivativeTerm k p 1 := by
      apply tsum_congr
      intro p
      rw [iteratedDerivWithin_of_isOpen (isOpen_entireLiNonzeroSet hF) honeMem]
      exact iteratedDeriv_entireLiLogDerivZeroTerm k p
        (ne_entireLiDivisorZeroValue_of_mem_nonzeroSet hF honeMem p)

theorem summable_entireLiLogDerivZeroDerivativeTerm_one
    {F : Complex -> Complex}
    (hF : Differentiable Complex F)
    (hsum : Summable (fun p : EntireLiDivisorZeroIndex F =>
      ‖entireLiDivisorZeroValue p‖⁻¹ ^ (2 : Nat)))
    (hone : F 1 ≠ 0) (k : Nat) :
    Summable (fun p : EntireLiDivisorZeroIndex F =>
      entireLiLogDerivZeroDerivativeTerm k p 1) := by
  by_cases hk : k = 0
  · subst k
    simpa [entireLiLogDerivZeroTerm, entireLiLogDerivZeroDerivativeTerm] using
      summable_entireLiLogDerivZeroTerm_of_mem_nonzeroSet hF hsum
        (show (1 : Complex) ∈ entireLiNonzeroSet F from hone)
  · exact (summableLocallyUniformlyOn_entireLiLogDerivZeroDerivativeTerm
      hF hsum k (Nat.one_le_iff_ne_zero.mpr hk)).summable
        (show (1 : Complex) ∈ entireLiNonzeroSet F from hone)

theorem entireLi_logDeriv_eq_polynomial_derivative_add_tsum
    {F : Complex -> Complex} {P : Polynomial Complex}
    (hF : Differentiable Complex F)
    (hsum : Summable (fun p : EntireLiDivisorZeroIndex F =>
      ‖entireLiDivisorZeroValue p‖⁻¹ ^ (2 : Nat)))
    (hfactor : ∀ w : Complex, F w = Complex.exp (Polynomial.eval w P) *
      Complex.Hadamard.divisorCanonicalProduct 1 F (Set.univ : Set Complex) w)
    {z : Complex} (hz : z ∈ entireLiNonzeroSet F) :
    logDeriv F z = Polynomial.eval z P.derivative +
      ∑' p : EntireLiDivisorZeroIndex F, entireLiLogDerivZeroTerm p z := by
  let product : Complex -> Complex :=
    Complex.Hadamard.divisorCanonicalProduct 1 F (Set.univ : Set Complex)
  have hfun : F = fun w => Complex.exp (Polynomial.eval w P) * product w := by
    funext w
    simpa only [product] using hfactor w
  have haway : ∀ p : EntireLiDivisorZeroIndex F,
      z ≠ entireLiDivisorZeroValue p := fun p =>
    ne_entireLiDivisorZeroValue_of_mem_nonzeroSet hF hz p
  have hdiffExp : DifferentiableAt Complex
      (fun w : Complex => Complex.exp (Polynomial.eval w P)) z :=
    ((Complex.hasDerivAt_exp (Polynomial.eval z P)).comp z (P.hasDerivAt z)).differentiableAt
  have hproductNe :
      Complex.Hadamard.divisorCanonicalProduct 1 F (Set.univ : Set Complex) z ≠ 0 :=
    Complex.Hadamard.divisorCanonicalProduct_ne_zero_of_forall_ne 1 F hsum haway
  calc
    logDeriv F z = logDeriv
        (fun w => Complex.exp (Polynomial.eval w P) * product w) z := by rw [hfun]
    _ = logDeriv (fun w => Complex.exp (Polynomial.eval w P)) z +
        logDeriv product z := by
      exact logDeriv_mul z (Complex.exp_ne_zero _)
        (by simpa only [product] using hproductNe) hdiffExp
        (by
          simpa only [product] using
            Complex.Hadamard.differentiableAt_divisorCanonicalProduct_univ 1 F hsum z)
    _ = Polynomial.eval z P.derivative +
        ∑' p : EntireLiDivisorZeroIndex F, entireLiLogDerivZeroTerm p z := by
      rw [Polynomial.logDeriv_exp_eval]
      rw [show logDeriv product z =
          ∑' p : EntireLiDivisorZeroIndex F, entireLiLogDerivZeroTerm p z from by
        simpa only [product, entireLiLogDerivZeroTerm] using
          Complex.Hadamard.logDeriv_divisorCanonicalProduct_one_eq_tsum_of_forall_ne
            hsum haway]

theorem iteratedDeriv_logDeriv_eq_entireLi_hadamard_zero_formula
    {F : Complex -> Complex} {P : Polynomial Complex}
    (hF : Differentiable Complex F)
    (hsum : Summable (fun p : EntireLiDivisorZeroIndex F =>
      ‖entireLiDivisorZeroValue p‖⁻¹ ^ (2 : Nat)))
    (hone : F 1 ≠ 0)
    (hfactor : ∀ w : Complex, F w = Complex.exp (Polynomial.eval w P) *
      Complex.Hadamard.divisorCanonicalProduct 1 F (Set.univ : Set Complex) w)
    (k : Nat) :
    iteratedDeriv k (logDeriv F) 1 =
      iteratedDeriv k (fun z : Complex => Polynomial.eval z P.derivative) 1 +
        ∑' p : EntireLiDivisorZeroIndex F,
          entireLiLogDerivZeroDerivativeTerm k p 1 := by
  let polynomialPart : Complex -> Complex := fun z => Polynomial.eval z P.derivative
  let zeroPart : Complex -> Complex := fun z =>
    ∑' p : EntireLiDivisorZeroIndex F, entireLiLogDerivZeroTerm p z
  have honeMem : (1 : Complex) ∈ entireLiNonzeroSet F := hone
  have heq : logDeriv F =ᶠ[𝓝 (1 : Complex)]
      fun z => polynomialPart z + zeroPart z := by
    filter_upwards [(isOpen_entireLiNonzeroSet hF).mem_nhds honeMem] with z hz
    exact entireLi_logDeriv_eq_polynomial_derivative_add_tsum hF hsum hfactor hz
  have hzeroEq : zeroPart =ᶠ[𝓝 (1 : Complex)] fun z => logDeriv F z - polynomialPart z := by
    filter_upwards [heq] with z hz
    rw [hz]
    ring
  have hpolynomial : ContDiffAt Complex k polynomialPart 1 := by
    dsimp only [polynomialPart]
    simpa [Polynomial.aeval_def] using
      (Polynomial.contDiff_aeval (R := Complex) (𝕜 := Complex) P.derivative
        (k : WithTop ℕ∞)).contDiffAt
  have hFanalytic : AnalyticAt Complex F 1 :=
    Complex.analyticAt_iff_eventually_differentiableAt.mpr
      (Filter.Eventually.of_forall fun z => hF z)
  have hlogDeriv : ContDiffAt Complex k (logDeriv F) 1 :=
    (hFanalytic.deriv.div hFanalytic hone).contDiffAt
  have hzeroPart : ContDiffAt Complex k zeroPart 1 :=
    (hlogDeriv.sub hpolynomial).congr_of_eventuallyEq hzeroEq
  rw [heq.iteratedDeriv_eq k]
  change iteratedDeriv k (polynomialPart + zeroPart) 1 = _
  rw [iteratedDeriv_add hpolynomial hzeroPart]
  change iteratedDeriv k (fun z : Complex => Polynomial.eval z P.derivative) 1 +
      iteratedDeriv k zeroPart 1 = _
  rw [show iteratedDeriv k zeroPart 1 =
      ∑' p : EntireLiDivisorZeroIndex F,
        entireLiLogDerivZeroDerivativeTerm k p 1 by
    exact iteratedDeriv_tsum_entireLiLogDerivZeroTerm hF hsum hone k]

/-- The classical `lambda_(n+1)` coefficient of the source-normalized heat-Xi function. -/
def deBruijnNewmanHeatLiCoefficient (t : Real) (n : Nat) : Complex :=
  iteratedDeriv (n + 1)
      (fun s : Complex => s ^ n * log (deBruijnNewmanHeatXi t s)) 1 /
    (Nat.factorial n : Complex)

theorem deBruijnNewmanHeatXi_one_mem_slitPlane (t : Real) :
    deBruijnNewmanHeatXi t 1 ∈ slitPlane := by
  rw [deBruijnNewmanHeatXi_one_eq, Complex.mem_slitPlane_iff]
  left
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  norm_num
  nlinarith [deBruijnNewmanHeatLiMomentA_pos t]

theorem analyticAt_log_deBruijnNewmanHeatXi_one (t : Real) :
    AnalyticAt Complex (fun s => log (deBruijnNewmanHeatXi t s)) 1 := by
  have hanalytic : AnalyticAt Complex (deBruijnNewmanHeatXi t) 1 :=
    Complex.analyticAt_iff_eventually_differentiableAt.mpr
      (Filter.Eventually.of_forall fun s =>
        (deBruijnNewmanHeatXi_entireOfOrderAtMost_one t).differentiable s)
  exact hanalytic.clog (deBruijnNewmanHeatXi_one_mem_slitPlane t)

theorem eventually_deriv_log_deBruijnNewmanHeatXi_eq_logDeriv (t : Real) :
    (fun s : Complex => deriv (fun z : Complex => log (deBruijnNewmanHeatXi t z)) s)
      =ᶠ[𝓝 (1 : Complex)] logDeriv (deBruijnNewmanHeatXi t) := by
  have hcontinuous :=
    ((deBruijnNewmanHeatXi_entireOfOrderAtMost_one t).differentiable 1).continuousAt
  have heventually : ∀ᶠ s in 𝓝 (1 : Complex), deBruijnNewmanHeatXi t s ∈ slitPlane :=
    hcontinuous.preimage_mem_nhds
      (isOpen_slitPlane.mem_nhds (deBruijnNewmanHeatXi_one_mem_slitPlane t))
  filter_upwards [heventually] with s hs
  simpa [Function.comp_def] using
    (Complex.deriv_log_comp_eq_logDeriv (f := deBruijnNewmanHeatXi t) (x := s)
      ((deBruijnNewmanHeatXi_entireOfOrderAtMost_one t).differentiable s) hs)

theorem iteratedDeriv_succ_log_deBruijnNewmanHeatXi_eq_logDeriv
    (t : Real) (k : Nat) :
    iteratedDeriv (k + 1) (fun s : Complex => log (deBruijnNewmanHeatXi t s)) 1 =
      iteratedDeriv k (logDeriv (deBruijnNewmanHeatXi t)) 1 := by
  rw [iteratedDeriv_succ']
  exact (eventually_deriv_log_deBruijnNewmanHeatXi_eq_logDeriv t).iteratedDeriv_eq k

theorem deBruijnNewmanHeatLiCoefficient_eq_finset_sum_iteratedDeriv_logDeriv
    (t : Real) (n : Nat) :
    deBruijnNewmanHeatLiCoefficient t n =
      (∑ i ∈ Finset.range (n + 1),
          ((n + 1).choose i : Complex) * (n.descFactorial i : Complex) *
            iteratedDeriv (n - i) (logDeriv (deBruijnNewmanHeatXi t)) 1) /
        (n.factorial : Complex) := by
  have hpower : ContDiffAt Complex (n + 1) (fun z : Complex => z ^ n) 1 := by fun_prop
  have hlog : ContDiffAt Complex (n + 1)
      (fun z : Complex => log (deBruijnNewmanHeatXi t z)) 1 :=
    (analyticAt_log_deBruijnNewmanHeatXi_one t).contDiffAt
  unfold deBruijnNewmanHeatLiCoefficient
  change iteratedDeriv (n + 1)
      ((fun z : Complex => z ^ n) * fun z => log (deBruijnNewmanHeatXi t z)) 1 /
      (n.factorial : Complex) = _
  rw [iteratedDeriv_mul hpower hlog]
  simp only
  rw [Finset.sum_range_succ]
  simp only [iteratedDeriv_pow, one_pow, mul_one]
  rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega : n < n + 1)]
  simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero]
  apply congrArg (fun x : Complex => x / (n.factorial : Complex))
  apply Finset.sum_congr rfl
  intro i hi
  have hiLe : i <= n := by
    simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hi
  rw [show n + 1 - i = (n - i) + 1 by omega]
  rw [iteratedDeriv_succ_log_deBruijnNewmanHeatXi_eq_logDeriv]

def entireLiZeroContribution
    {F : Complex -> Complex} (n : Nat) (p : EntireLiDivisorZeroIndex F) : Complex :=
  (∑ i ∈ Finset.range (n + 1),
      ((n + 1).choose i : Complex) * (n.descFactorial i : Complex) *
        entireLiLogDerivZeroDerivativeTerm (n - i) p 1) /
    (n.factorial : Complex)

private def normalizedEntireLiReflectedContributionTerm
    (n k : Nat) (rho : Complex) : Complex :=
  ((n + 1).choose (k + 1) : Complex) * (-1 : Complex) ^ k /
      (1 - rho) ^ (k + 1) +
    if k = 0 then (n + 1 : Complex) / rho else 0

private theorem normalizedEntireLiReflectedContributionTerm_from_le
    {F : Complex -> Complex} (hF : Differentiable Complex F) (hone : F 1 ≠ 0)
    (n i : Nat) (hi : i < n + 1)
    (p : EntireLiDivisorZeroIndex F) :
    (((n + 1).choose i : Complex) * (n.descFactorial i : Complex) *
        entireLiLogDerivZeroDerivativeTerm (n - i) p 1) /
      (n.factorial : Complex) =
        normalizedEntireLiReflectedContributionTerm n (n - i)
          (entireLiDivisorZeroValue p) := by
  have hin : i <= n := by omega
  have him : i <= n + 1 := by omega
  have hchoose : (n + 1).choose i = (n + 1).choose (n - i + 1) := by
    calc
      (n + 1).choose i = (n + 1).choose (n + 1 - i) := (Nat.choose_symm him).symm
      _ = (n + 1).choose (n - i + 1) := congrArg ((n + 1).choose ·) (by omega)
  have hfactorial : (n - i).factorial * n.descFactorial i = n.factorial :=
    Nat.factorial_mul_descFactorial hin
  have hfactorialComplex :
      ((n - i).factorial : Complex) * (n.descFactorial i : Complex) =
        (n.factorial : Complex) := by exact_mod_cast hfactorial
  have hnfac : (n.factorial : Complex) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hrhoOne : (1 : Complex) - entireLiDivisorZeroValue p ≠ 0 := by
    intro hzero
    have hp1 : entireLiDivisorZeroValue p = 1 := (sub_eq_zero.mp hzero).symm
    have hpZero := entireLiDivisorZeroValue_eq_zero hF p
    rw [hp1] at hpZero
    exact hone hpZero
  have hrhoZero : entireLiDivisorZeroValue p ≠ 0 :=
    Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p
  by_cases hk : n - i = 0
  · have hiEq : i = n := by omega
    subst i
    simp [normalizedEntireLiReflectedContributionTerm,
      entireLiLogDerivZeroDerivativeTerm]
    field_simp [hnfac, hrhoZero, hrhoOne, Nat.descFactorial_self]
    exact_mod_cast Nat.descFactorial_self n
  · rw [entireLiLogDerivZeroDerivativeTerm, if_neg hk, add_zero]
    rw [normalizedEntireLiReflectedContributionTerm, if_neg hk]
    simp only [add_zero]
    rw [hchoose]
    field_simp [hnfac, hrhoOne]
    calc
      ((n + 1).choose (n - i + 1) : Complex) * (n.descFactorial i : Complex) *
          ((n - i).factorial : Complex) =
        ((n + 1).choose (n - i + 1) : Complex) *
          (((n - i).factorial : Complex) * (n.descFactorial i : Complex)) := by ring
      _ = ((n + 1).choose (n - i + 1) : Complex) * (n.factorial : Complex) := by
        rw [hfactorialComplex]

theorem entireLiZeroContribution_eq_reflected_raw
    {F : Complex -> Complex} (hF : Differentiable Complex F) (hone : F 1 ≠ 0)
    (n : Nat) (p : EntireLiDivisorZeroIndex F) :
    entireLiZeroContribution n p =
      liRawZeroTerm (n + 1) (1 - entireLiDivisorZeroValue p) +
        (n + 1 : Complex) / entireLiDivisorZeroValue p := by
  rw [entireLiZeroContribution, Finset.sum_div]
  have hreflect :
      (∑ i ∈ Finset.range (n + 1),
          normalizedEntireLiReflectedContributionTerm n (n - i)
            (entireLiDivisorZeroValue p)) =
        ∑ i ∈ Finset.range (n + 1),
          (((n + 1).choose i : Complex) * (n.descFactorial i : Complex) *
            entireLiLogDerivZeroDerivativeTerm (n - i) p 1) /
              (n.factorial : Complex) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact (normalizedEntireLiReflectedContributionTerm_from_le
      hF hone n i (Finset.mem_range.mp hi) p).symm
  rw [← hreflect]
  have hsumReflect := Finset.sum_range_reflect
    (fun k => normalizedEntireLiReflectedContributionTerm n k
      (entireLiDivisorZeroValue p)) (n + 1)
  rw [show (∑ i ∈ Finset.range (n + 1),
      normalizedEntireLiReflectedContributionTerm n (n - i)
        (entireLiDivisorZeroValue p)) =
      ∑ i ∈ Finset.range (n + 1),
        normalizedEntireLiReflectedContributionTerm n i
          (entireLiDivisorZeroValue p) by
    simpa only [Nat.add_sub_cancel_right] using hsumReflect]
  unfold normalizedEntireLiReflectedContributionTerm
  rw [Finset.sum_add_distrib]
  have hlinear :
      (∑ k ∈ Finset.range (n + 1),
        if k = 0 then (n + 1 : Complex) / entireLiDivisorZeroValue p else 0) =
          (n + 1 : Complex) / entireLiDivisorZeroValue p := by simp
  rw [hlinear]
  rw [show (∑ k ∈ Finset.range (n + 1),
      ((n + 1).choose (k + 1) : Complex) * (-1 : Complex) ^ k /
        (1 - entireLiDivisorZeroValue p) ^ (k + 1)) =
      liRawZeroTerm (n + 1) (1 - entireLiDivisorZeroValue p) by
    rw [liRawZeroTerm]
    have hx : 1 / (1 - entireLiDivisorZeroValue p) =
        (1 - entireLiDivisorZeroValue p)⁻¹ := one_div _
    rw [show 1 - 1 / (1 - entireLiDivisorZeroValue p) =
        1 - (1 - entireLiDivisorZeroValue p)⁻¹ by rw [hx]]
    rw [← sum_choose_neg_one_mul_pow_succ n
      ((1 - entireLiDivisorZeroValue p)⁻¹)]
    apply Finset.sum_congr rfl
    intro k hk
    rw [div_eq_mul_inv, inv_pow]]

private theorem summable_finset_sum_of_summable_entireLi
    {alpha : Type*} (s : Finset Nat) (f : Nat -> alpha -> Complex)
    (hf : ∀ i ∈ s, Summable (f i)) :
    Summable (fun a => ∑ i ∈ s, f i a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hs : Summable (fun a => ∑ j ∈ s, f j a) :=
        ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      have hiSum : Summable (f i) := hf i (Finset.mem_insert_self i s)
      simpa [Finset.sum_insert hi] using hiSum.add hs

theorem summable_entireLiZeroContribution
    {F : Complex -> Complex} (hF : Differentiable Complex F)
    (hsum : Summable (fun p : EntireLiDivisorZeroIndex F =>
      ‖entireLiDivisorZeroValue p‖⁻¹ ^ (2 : Nat)))
    (hone : F 1 ≠ 0) (n : Nat) :
    Summable (entireLiZeroContribution (F := F) n) := by
  unfold entireLiZeroContribution
  apply Summable.div_const
  apply summable_finset_sum_of_summable_entireLi
  intro i hi
  exact (summable_entireLiLogDerivZeroDerivativeTerm_one hF hsum hone (n - i)).mul_left
    (((n + 1).choose i : Complex) * (n.descFactorial i : Complex))

def entireLiReciprocalPair
    {F : Complex -> Complex} (p : EntireLiDivisorZeroIndex F) : Complex :=
  1 / (1 - entireLiDivisorZeroValue p) + 1 / entireLiDivisorZeroValue p

theorem summable_entireLiReciprocalPair
    {F : Complex -> Complex} (hF : Differentiable Complex F)
    (hsum : Summable (fun p : EntireLiDivisorZeroIndex F =>
      ‖entireLiDivisorZeroValue p‖⁻¹ ^ (2 : Nat)))
    (hone : F 1 ≠ 0) :
    Summable (entireLiReciprocalPair (F := F)) := by
  change Summable (fun p : EntireLiDivisorZeroIndex F =>
    1 / (1 - entireLiDivisorZeroValue p) + 1 / entireLiDivisorZeroValue p)
  simpa [entireLiLogDerivZeroDerivativeTerm, one_div] using
    summable_entireLiLogDerivZeroDerivativeTerm_one hF hsum hone 0

theorem entireLiZeroContribution_reflect_average
    {F : Complex -> Complex} (hF : Differentiable Complex F)
    (hone : F 1 ≠ 0) (reflect : EntireLiDivisorZeroIndex F ≃ EntireLiDivisorZeroIndex F)
    (hreflect : ∀ p, entireLiDivisorZeroValue (reflect p) =
      1 - entireLiDivisorZeroValue p)
    (n : Nat) (p : EntireLiDivisorZeroIndex F) :
    (entireLiZeroContribution n p + entireLiZeroContribution n (reflect p)) / 2 =
      pairedLiZeroTerm (fun q : EntireLiDivisorZeroIndex F =>
        entireLiDivisorZeroValue q) n p +
      ((n + 1 : Complex) / 2) * entireLiReciprocalPair p := by
  rw [entireLiZeroContribution_eq_reflected_raw hF hone,
    entireLiZeroContribution_eq_reflected_raw hF hone]
  simp only [hreflect]
  unfold pairedLiZeroTerm entireLiReciprocalPair
  rw [show 1 - (1 - entireLiDivisorZeroValue p) =
      entireLiDivisorZeroValue p by ring]
  ring

theorem summable_pairedLiZeroTerm_of_entireLiFormula
    {F : Complex -> Complex} (hF : Differentiable Complex F)
    (hsum : Summable (fun p : EntireLiDivisorZeroIndex F =>
      ‖entireLiDivisorZeroValue p‖⁻¹ ^ (2 : Nat)))
    (hone : F 1 ≠ 0) (reflect : EntireLiDivisorZeroIndex F ≃ EntireLiDivisorZeroIndex F)
    (hreflect : ∀ p, entireLiDivisorZeroValue (reflect p) =
      1 - entireLiDivisorZeroValue p) (n : Nat) :
    Summable (pairedLiZeroTerm
      (fun p : EntireLiDivisorZeroIndex F => entireLiDivisorZeroValue p) n) := by
  let contribution : EntireLiDivisorZeroIndex F -> Complex := entireLiZeroContribution n
  have hcontribution : Summable contribution := summable_entireLiZeroContribution hF hsum hone n
  have hreflectSum : Summable (fun p => contribution (reflect p)) :=
    hcontribution.comp_injective reflect.injective
  have havg : Summable (fun p => (contribution p + contribution (reflect p)) / 2) :=
    (hcontribution.add hreflectSum).div_const 2
  have hpair : Summable (fun p =>
      ((n + 1 : Complex) / 2) * entireLiReciprocalPair p) :=
    (summable_entireLiReciprocalPair hF hsum hone).mul_left ((n + 1 : Complex) / 2)
  apply (havg.sub hpair).congr
  intro p
  rw [entireLiZeroContribution_reflect_average hF hone reflect hreflect]
  ring

theorem tsum_entireLiZeroContribution_eq_reflect_average
    {F : Complex -> Complex} (hF : Differentiable Complex F)
    (hsum : Summable (fun p : EntireLiDivisorZeroIndex F =>
      ‖entireLiDivisorZeroValue p‖⁻¹ ^ (2 : Nat)))
    (hone : F 1 ≠ 0) (reflect : EntireLiDivisorZeroIndex F ≃ EntireLiDivisorZeroIndex F)
    (n : Nat) :
    (∑' p : EntireLiDivisorZeroIndex F, entireLiZeroContribution n p) =
      ∑' p : EntireLiDivisorZeroIndex F,
        (entireLiZeroContribution n p + entireLiZeroContribution n (reflect p)) / 2 := by
  have hcontribution := summable_entireLiZeroContribution hF hsum hone n
  have hreflectSum : Summable (fun p => entireLiZeroContribution n (reflect p)) :=
    hcontribution.comp_injective reflect.injective
  rw [tsum_div_const]
  rw [hcontribution.tsum_add hreflectSum]
  rw [reflect.tsum_eq]
  ring

def entireLiPolynomialContribution (n : Nat) (P : Polynomial Complex) : Complex :=
  (∑ i ∈ Finset.range (n + 1),
      ((n + 1).choose i : Complex) * (n.descFactorial i : Complex) *
        iteratedDeriv (n - i) (fun z : Complex => Polynomial.eval z P.derivative) 1) /
    (n.factorial : Complex)

theorem entireLiPolynomialContribution_eq
    {P : Polynomial Complex} (hdegree : P.degree <= 1) (n : Nat) :
    entireLiPolynomialContribution n P =
      (n + 1 : Complex) * Polynomial.eval 1 P.derivative := by
  rw [entireLiPolynomialContribution,
    polynomial_derivative_eq_C_eval_one_of_degree_le_one hdegree]
  simp only [Polynomial.eval_C]
  rw [Finset.sum_eq_single n]
  · simp only [Nat.choose_succ_self_right, Nat.cast_add, Nat.cast_one,
      Nat.descFactorial_self, tsub_self, iteratedDeriv_zero]
    have hnfac : (n.factorial : Complex) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    apply (div_eq_iff hnfac).2
    ring
  · intro i hi hin
    have hiLe : i <= n := by simpa using Finset.mem_range.mp hi
    have hsub : n - i ≠ 0 := by omega
    simp [iteratedDeriv_const, hsub]
  · simp

theorem deBruijnNewmanHeatLiCoefficient_eq_polynomial_add_tsum_zeroContribution
    {t : Real} {P : Polynomial Complex}
    (hfactor : ∀ z : Complex, deBruijnNewmanHeatXi t z =
      Complex.exp (Polynomial.eval z P) *
        Complex.Hadamard.divisorCanonicalProduct 1 (deBruijnNewmanHeatXi t)
          (Set.univ : Set Complex) z)
    (n : Nat) :
    deBruijnNewmanHeatLiCoefficient t n =
      entireLiPolynomialContribution n P +
        ∑' p : DeBruijnNewmanHeatXiDivisorZeroIndex t,
          entireLiZeroContribution n p := by
  rw [deBruijnNewmanHeatLiCoefficient_eq_finset_sum_iteratedDeriv_logDeriv]
  simp_rw [iteratedDeriv_logDeriv_eq_entireLi_hadamard_zero_formula
    (deBruijnNewmanHeatXi_entireOfOrderAtMost_one t).differentiable
    (summable_deBruijnNewmanHeatXiDivisorZeroIndex_norm_inv_sq t)
    (deBruijnNewmanHeatXi_one_ne_zero t) hfactor]
  unfold entireLiPolynomialContribution entireLiZeroContribution
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, add_div]
  congr 1
  rw [tsum_div_const]
  rw [Summable.tsum_finsetSum]
  · congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [tsum_mul_left]
  · intro i hi
    exact (summable_entireLiLogDerivZeroDerivativeTerm_one
      (deBruijnNewmanHeatXi_entireOfOrderAtMost_one t).differentiable
      (summable_deBruijnNewmanHeatXiDivisorZeroIndex_norm_inv_sq t)
      (deBruijnNewmanHeatXi_one_ne_zero t) (n - i)).mul_left
        (((n + 1).choose i : Complex) * (n.descFactorial i : Complex))

theorem deriv_deBruijnNewmanHeatXi_zero_eq_neg_one (t : Real) :
    deriv (deBruijnNewmanHeatXi t) 0 = -deriv (deBruijnNewmanHeatXi t) 1 := by
  have hcomp : HasDerivAt (fun z : Complex => deBruijnNewmanHeatXi t (1 - z))
      (-deriv (deBruijnNewmanHeatXi t) 1) 0 := by
    apply HasDerivAt.comp_const_sub (1 : Complex) 0
    simpa using
      ((deBruijnNewmanHeatXi_entireOfOrderAtMost_one t).differentiable 1).hasDerivAt
  have heq : (fun z : Complex => deBruijnNewmanHeatXi t (1 - z)) =
      deBruijnNewmanHeatXi t := by
    funext z
    exact deBruijnNewmanHeatXi_one_sub t z
  rw [heq] at hcomp
  exact hcomp.deriv

theorem logDeriv_deBruijnNewmanHeatXi_zero_eq_neg_one (t : Real) :
    logDeriv (deBruijnNewmanHeatXi t) 0 =
      -logDeriv (deBruijnNewmanHeatXi t) 1 := by
  unfold logDeriv
  change deriv (deBruijnNewmanHeatXi t) 0 / deBruijnNewmanHeatXi t 0 =
    -(deriv (deBruijnNewmanHeatXi t) 1 / deBruijnNewmanHeatXi t 1)
  rw [deriv_deBruijnNewmanHeatXi_zero_eq_neg_one]
  have hvalue : deBruijnNewmanHeatXi t 0 = deBruijnNewmanHeatXi t 1 := by
    simpa using (deBruijnNewmanHeatXi_one_sub t 0).symm
  rw [hvalue]
  ring

theorem deBruijnNewmanHeatXi_hadamard_polynomial_add_half_reciprocal_tsum_eq_zero
    {t : Real} {P : Polynomial Complex} (hdegree : P.degree <= 1)
    (hfactor : ∀ z : Complex, deBruijnNewmanHeatXi t z =
      Complex.exp (Polynomial.eval z P) *
        Complex.Hadamard.divisorCanonicalProduct 1 (deBruijnNewmanHeatXi t)
          (Set.univ : Set Complex) z) :
    Polynomial.eval 1 P.derivative +
        (∑' p : DeBruijnNewmanHeatXiDivisorZeroIndex t,
          entireLiReciprocalPair p) / 2 = 0 := by
  let F := deBruijnNewmanHeatXi t
  have hF := (deBruijnNewmanHeatXi_entireOfOrderAtMost_one t).differentiable
  have hsum := summable_deBruijnNewmanHeatXiDivisorZeroIndex_norm_inv_sq t
  have hzero := entireLi_logDeriv_eq_polynomial_derivative_add_tsum
    hF hsum hfactor (show (0 : Complex) ∈ entireLiNonzeroSet F from
      deBruijnNewmanHeatXi_zero_ne_zero t)
  have hone := entireLi_logDeriv_eq_polynomial_derivative_add_tsum
    hF hsum hfactor (show (1 : Complex) ∈ entireLiNonzeroSet F from
      deBruijnNewmanHeatXi_one_ne_zero t)
  have hzeroTerm : ∀ p : DeBruijnNewmanHeatXiDivisorZeroIndex t,
      entireLiLogDerivZeroTerm p 0 = 0 := by
    intro p
    unfold entireLiLogDerivZeroTerm
    have hpzero := Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p
    field_simp [hpzero]
    ring
  have hzeroSum :
      (∑' p : DeBruijnNewmanHeatXiDivisorZeroIndex t,
        entireLiLogDerivZeroTerm p 0) = 0 := by
    rw [show (fun p : DeBruijnNewmanHeatXiDivisorZeroIndex t =>
        entireLiLogDerivZeroTerm p 0) = fun _ => 0 by
      funext p
      exact hzeroTerm p]
    simp
  rw [hzeroSum] at hzero
  simp only [add_zero] at hzero
  have hP := polynomial_derivative_eq_C_eval_one_of_degree_le_one hdegree
  have hPconstant : Polynomial.eval 0 P.derivative = Polynomial.eval 1 P.derivative := by
    rw [hP]
    simp
  change logDeriv (deBruijnNewmanHeatXi t) 1 = Polynomial.eval 1 P.derivative +
    ∑' p : DeBruijnNewmanHeatXiDivisorZeroIndex t, entireLiReciprocalPair p at hone
  rw [logDeriv_deBruijnNewmanHeatXi_zero_eq_neg_one, hone, hPconstant] at hzero
  have htwice : 2 * Polynomial.eval 1 P.derivative +
      (∑' p : DeBruijnNewmanHeatXiDivisorZeroIndex t,
        entireLiReciprocalPair p) = 0 := by
    calc
      2 * Polynomial.eval 1 P.derivative +
          (∑' p : DeBruijnNewmanHeatXiDivisorZeroIndex t,
            entireLiReciprocalPair p) =
        -(-(Polynomial.eval 1 P.derivative +
          ∑' p : DeBruijnNewmanHeatXiDivisorZeroIndex t,
            entireLiReciprocalPair p) - Polynomial.eval 1 P.derivative) := by ring
      _ = 0 := by rw [hzero]; ring
  calc
    Polynomial.eval 1 P.derivative +
        (∑' p : DeBruijnNewmanHeatXiDivisorZeroIndex t,
          entireLiReciprocalPair p) / 2 =
      (2 * Polynomial.eval 1 P.derivative +
        ∑' p : DeBruijnNewmanHeatXiDivisorZeroIndex t,
          entireLiReciprocalPair p) / 2 := by ring
    _ = 0 := by rw [htwice]; norm_num

theorem tsum_entireLi_reflect_average_eq_paired_add_reciprocal
    {F : Complex -> Complex} (hF : Differentiable Complex F)
    (hsum : Summable (fun p : EntireLiDivisorZeroIndex F =>
      ‖entireLiDivisorZeroValue p‖⁻¹ ^ (2 : Nat)))
    (hone : F 1 ≠ 0) (reflect : EntireLiDivisorZeroIndex F ≃ EntireLiDivisorZeroIndex F)
    (hreflect : ∀ p, entireLiDivisorZeroValue (reflect p) =
      1 - entireLiDivisorZeroValue p) (n : Nat) :
    (∑' p : EntireLiDivisorZeroIndex F,
        (entireLiZeroContribution n p + entireLiZeroContribution n (reflect p)) / 2) =
      (∑' p : EntireLiDivisorZeroIndex F,
        pairedLiZeroTerm (fun q : EntireLiDivisorZeroIndex F =>
          entireLiDivisorZeroValue q) n p) +
      ((n + 1 : Complex) / 2) *
        ∑' p : EntireLiDivisorZeroIndex F, entireLiReciprocalPair p := by
  rw [show (fun p : EntireLiDivisorZeroIndex F =>
      (entireLiZeroContribution n p + entireLiZeroContribution n (reflect p)) / 2) =
      fun p => pairedLiZeroTerm (fun q : EntireLiDivisorZeroIndex F =>
          entireLiDivisorZeroValue q) n p +
        ((n + 1 : Complex) / 2) * entireLiReciprocalPair p by
    funext p
    exact entireLiZeroContribution_reflect_average hF hone reflect hreflect n p]
  rw [(summable_pairedLiZeroTerm_of_entireLiFormula hF hsum hone reflect hreflect n).tsum_add
    ((summable_entireLiReciprocalPair hF hsum hone).mul_left ((n + 1 : Complex) / 2))]
  rw [tsum_mul_left]

/-- Exact paired zero formula for every heat-family Li coefficient and every real heat time. -/
theorem deBruijnNewmanHeatLiCoefficient_eq_tsum_pairedLiZeroTerm
    (t : Real) (n : Nat) :
    deBruijnNewmanHeatLiCoefficient t n =
      ∑' p : DeBruijnNewmanHeatXiDivisorZeroIndex t,
        pairedLiZeroTerm (fun q : DeBruijnNewmanHeatXiDivisorZeroIndex t =>
          deBruijnNewmanHeatXiDivisorZeroValue q) n p := by
  obtain ⟨P, hdegree, hfactor⟩ :=
    exists_deBruijnNewmanHeatXi_hadamard_factorization t
  let reflect := deBruijnNewmanHeatXiDivisorZeroReflectEquiv t
  have hreflect : ∀ p : DeBruijnNewmanHeatXiDivisorZeroIndex t,
      deBruijnNewmanHeatXiDivisorZeroValue (reflect p) =
        1 - deBruijnNewmanHeatXiDivisorZeroValue p := by
    intro p
    exact deBruijnNewmanHeatXiDivisorZeroValue_reflect p
  rw [deBruijnNewmanHeatLiCoefficient_eq_polynomial_add_tsum_zeroContribution hfactor]
  rw [entireLiPolynomialContribution_eq hdegree]
  rw [tsum_entireLiZeroContribution_eq_reflect_average
    (deBruijnNewmanHeatXi_entireOfOrderAtMost_one t).differentiable
    (summable_deBruijnNewmanHeatXiDivisorZeroIndex_norm_inv_sq t)
    (deBruijnNewmanHeatXi_one_ne_zero t) reflect]
  rw [tsum_entireLi_reflect_average_eq_paired_add_reciprocal
    (deBruijnNewmanHeatXi_entireOfOrderAtMost_one t).differentiable
    (summable_deBruijnNewmanHeatXiDivisorZeroIndex_norm_inv_sq t)
    (deBruijnNewmanHeatXi_one_ne_zero t) reflect hreflect]
  have hcancel :=
    deBruijnNewmanHeatXi_hadamard_polynomial_add_half_reciprocal_tsum_eq_zero
      hdegree hfactor
  calc
    (n + 1 : Complex) * Polynomial.eval 1 P.derivative +
        ((∑' p : DeBruijnNewmanHeatXiDivisorZeroIndex t,
          pairedLiZeroTerm (fun q : DeBruijnNewmanHeatXiDivisorZeroIndex t =>
            deBruijnNewmanHeatXiDivisorZeroValue q) n p) +
          ((n + 1 : Complex) / 2) *
            ∑' p : DeBruijnNewmanHeatXiDivisorZeroIndex t,
              entireLiReciprocalPair p) =
      (∑' p : DeBruijnNewmanHeatXiDivisorZeroIndex t,
        pairedLiZeroTerm (fun q : DeBruijnNewmanHeatXiDivisorZeroIndex t =>
          deBruijnNewmanHeatXiDivisorZeroValue q) n p) +
        (n + 1 : Complex) *
          (Polynomial.eval 1 P.derivative +
            (∑' p : DeBruijnNewmanHeatXiDivisorZeroIndex t,
              entireLiReciprocalPair p) / 2) := by ring
    _ = ∑' p : DeBruijnNewmanHeatXiDivisorZeroIndex t,
        pairedLiZeroTerm (fun q : DeBruijnNewmanHeatXiDivisorZeroIndex t =>
          deBruijnNewmanHeatXiDivisorZeroValue q) n p := by
      rw [hcancel]
      ring

/-- At time zero the heat-family definition is exactly the existing project Li definition. -/
theorem deBruijnNewmanHeatLiCoefficient_zero_eq (n : Nat) :
    deBruijnNewmanHeatLiCoefficient 0 n = liCoefficientCandidate n := by
  unfold deBruijnNewmanHeatLiCoefficient liCoefficientCandidate
  congr 2
  funext s
  rw [deBruijnNewmanHeatXi_zero_eq_riemannXi]

/-- In the Xi coordinate, real source zeros are exactly critical-line zeros. -/
theorem deBruijnNewmanAllZerosReal_iff_heatXi_zeros_on_line (t : Real) :
    deBruijnNewmanAllZerosReal t ↔
      ∀ s : Complex, deBruijnNewmanHeatXi t s = 0 → s.re = 1 / 2 := by
  constructor
  · intro hall s hs
    have hH : deBruijnNewmanH t (deBruijnNewmanZeroCoordinate s) = 0 := by
      rw [deBruijnNewmanHeatXi] at hs
      simpa only [deBruijnNewmanZeroCoordinate] using
        (mul_eq_zero.mp hs).resolve_left (by norm_num)
    exact (deBruijnNewmanZeroCoordinate_im_eq_zero_iff s).mp (hall _ hH)
  · intro hline z hz
    have hheat : deBruijnNewmanHeatXi t ((1 + Complex.I * z) / 2) = 0 := by
      rw [deBruijnNewmanHeatXi]
      have hcoordinate :
          -Complex.I * (2 * ((1 + Complex.I * z) / 2) - 1) = z := by
        apply Complex.ext <;> simp <;> ring
      rw [hcoordinate, hz, mul_zero]
    exact (deBruijnNewmanSourceCoordinate_re_eq_half_iff z).mp (hline _ hheat)

theorem analyticOnNhd_deBruijnNewmanHeatXi (t : Real) :
    AnalyticOnNhd Complex (deBruijnNewmanHeatXi t) Set.univ :=
  analyticOnNhd_univ_iff_differentiable.mpr
    (deBruijnNewmanHeatXi_entireOfOrderAtMost_one t).differentiable

theorem analyticOrderAt_deBruijnNewmanHeatXi_ne_top (t : Real) (s : Complex) :
    analyticOrderAt (deBruijnNewmanHeatXi t) s ≠ ⊤ := by
  intro htop
  have hlocal : deBruijnNewmanHeatXi t =ᶠ[𝓝 s] (0 : Complex -> Complex) := by
    filter_upwards [analyticOrderAt_eq_top.mp htop] with z hz
    simpa using hz
  have hglobal : deBruijnNewmanHeatXi t = (0 : Complex -> Complex) :=
    (analyticOnNhd_deBruijnNewmanHeatXi t).eq_of_eventuallyEq analyticOnNhd_const hlocal
  have hone := congrFun hglobal 1
  exact deBruijnNewmanHeatXi_one_ne_zero t (by simpa using hone)

theorem exists_deBruijnNewmanHeatXiDivisorZeroIndex_of_eq_zero
    {t : Real} {s : Complex} (hs : deBruijnNewmanHeatXi t s = 0) :
    ∃ p : DeBruijnNewmanHeatXiDivisorZeroIndex t,
      deBruijnNewmanHeatXiDivisorZeroValue p = s := by
  have hanalytic : AnalyticAt Complex (deBruijnNewmanHeatXi t) s :=
    Complex.analyticAt_iff_eventually_differentiableAt.mpr
      (Filter.Eventually.of_forall fun z =>
        (deBruijnNewmanHeatXi_entireOfOrderAtMost_one t).differentiable z)
  have horderNe : analyticOrderAt (deBruijnNewmanHeatXi t) s ≠ 0 :=
    hanalytic.analyticOrderAt_ne_zero.mpr hs
  have hmult : 0 < analyticOrderNatAt (deBruijnNewmanHeatXi t) s := by
    apply Nat.pos_of_ne_zero
    intro hzero
    apply horderNe
    rw [← Nat.cast_analyticOrderNatAt
      (analyticOrderAt_deBruijnNewmanHeatXi_ne_top t s), hzero]
    simp
  have hfiber :
      0 < Int.toNat (MeromorphicOn.divisor (deBruijnNewmanHeatXi t) Set.univ s) := by
    rw [Complex.Hadamard.divisor_univ_eq_analyticOrderNatAt_int
      (deBruijnNewmanHeatXi_entireOfOrderAtMost_one t).differentiable]
    simpa using hmult
  have hsZero : s ≠ 0 := by
    intro hs0
    subst s
    exact deBruijnNewmanHeatXi_zero_ne_zero t hs
  let q : Complex.Hadamard.divisorZeroIndex
      (deBruijnNewmanHeatXi t) (Set.univ : Set Complex) :=
    ⟨s, ⟨0, hfiber⟩⟩
  exact ⟨⟨q, hsZero⟩, rfl⟩

theorem heatXi_zeros_on_line_iff_divisorZeroValues_on_line (t : Real) :
    (∀ s : Complex, deBruijnNewmanHeatXi t s = 0 -> s.re = 1 / 2) <->
      ∀ p : DeBruijnNewmanHeatXiDivisorZeroIndex t,
        (deBruijnNewmanHeatXiDivisorZeroValue p).re = 1 / 2 := by
  constructor
  · intro hall p
    exact hall _ (deBruijnNewmanHeatXiDivisorZeroIndex_val_eq_zero p)
  · intro hdivisor s hs
    obtain ⟨p, hp⟩ := exists_deBruijnNewmanHeatXiDivisorZeroIndex_of_eq_zero hs
    simpa only [hp] using hdivisor p

/-- Complete all-index heat-family Li criterion, valid at every real heat time. -/
theorem deBruijnNewmanAllZerosReal_iff_forall_heatLiCoefficient_re_nonneg
    (t : Real) :
    deBruijnNewmanAllZerosReal t <->
      ∀ n : Nat, 0 <= (deBruijnNewmanHeatLiCoefficient t n).re := by
  rw [deBruijnNewmanAllZerosReal_iff_heatXi_zeros_on_line,
    heatXi_zeros_on_line_iff_divisorZeroValues_on_line]
  let value : DeBruijnNewmanHeatXiDivisorZeroIndex t -> Complex :=
    fun p => deBruijnNewmanHeatXiDivisorZeroValue p
  let reflect := deBruijnNewmanHeatXiDivisorZeroReflectEquiv t
  apply all_values_on_line_iff_forall_coefficient_re_nonneg reflect
  · intro p
    exact deBruijnNewmanHeatXiDivisorZeroValue_reflect p
  · intro p
    exact Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p
  · intro p
    exact (sub_ne_zero.mp
      (one_sub_deBruijnNewmanHeatXiDivisorZeroValue_ne_zero p)).symm
  · intro bound
    exact Complex.Hadamard.divisorZeroIndex₀_norm_le_finite
      (f := deBruijnNewmanHeatXi t) (U := (Set.univ : Set Complex)) bound (by simp)
  · exact summable_deBruijnNewmanHeatXiDivisorZeroIndex_norm_inv_sq t
  · intro n
    exact summable_pairedLiZeroTerm_of_entireLiFormula
      (deBruijnNewmanHeatXi_entireOfOrderAtMost_one t).differentiable
      (summable_deBruijnNewmanHeatXiDivisorZeroIndex_norm_inv_sq t)
      (deBruijnNewmanHeatXi_one_ne_zero t) reflect
      (fun p => deBruijnNewmanHeatXiDivisorZeroValue_reflect p) n
  · exact deBruijnNewmanHeatLiCoefficient_eq_tsum_pairedLiZeroTerm t

theorem riemannHypothesis_iff_forall_deBruijnNewmanHeatLiCoefficient_zero_re_nonneg :
    RiemannHypothesis <->
      ∀ n : Nat, 0 <= (deBruijnNewmanHeatLiCoefficient 0 n).re := by
  rw [riemannHypothesis_iff_forall_liCoefficientCandidate_re_nonneg]
  constructor <;> intro h n
  · simpa only [deBruijnNewmanHeatLiCoefficient_zero_eq] using h n
  · simpa only [deBruijnNewmanHeatLiCoefficient_zero_eq] using h n

/-- Aggregate witness for the complete all-index endpoint and time-zero definition alignment. -/
theorem deBruijnNewmanHeat_allIndexLi_endpoint :
    (∀ n, deBruijnNewmanHeatLiCoefficient 0 n = liCoefficientCandidate n) ∧
    (∀ t : Real, 0 <= t ->
      (deBruijnNewmanAllZerosReal t <->
        ∀ n, 0 <= (deBruijnNewmanHeatLiCoefficient t n).re)) := by
  exact ⟨deBruijnNewmanHeatLiCoefficient_zero_eq,
    fun t _ht => deBruijnNewmanAllZerosReal_iff_forall_heatLiCoefficient_re_nonneg t⟩

end

end LeanLab.Riemann
