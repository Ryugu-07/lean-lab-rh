import LeanLab.Riemann.DeBruijnNewmanUpperHalf
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorQuotientRemovable

set_option linter.style.header false

/-!
# Zero dynamics for the de Bruijn-Newman heat family

This module begins the direct H6-E proof attempt by identifying the logarithmic force exerted by
the multiplicity-bearing Hadamard divisor at a simple zero. The zero fiber is removed before the
infinite sum is evaluated, so the resulting genus-one sum is absolutely convergent.
-/

open Complex Filter Function Set Topology
open scoped BigOperators Topology

namespace LeanLab.Riemann

noncomputable section

private def regularizedDivisorForceTerm
    {F : ℂ → ℂ} (r : ℂ)
    (p : Complex.Hadamard.divisorZeroIndex₀ F (Set.univ : Set ℂ)) : ℂ :=
  if Complex.Hadamard.divisorZeroIndex₀_val p = r then 0
  else 1 / (r - Complex.Hadamard.divisorZeroIndex₀_val p) +
    1 / Complex.Hadamard.divisorZeroIndex₀_val p

private theorem summable_regularizedDivisorForceTerm
    {F : ℂ → ℂ}
    (hsum : Summable
      (fun p : Complex.Hadamard.divisorZeroIndex₀ F (Set.univ : Set ℂ) ↦
        ‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹ ^ (2 : ℕ)))
    (r : ℂ) :
    Summable (regularizedDivisorForceTerm (F := F) r) := by
  let R : ℝ := max ‖r‖ 1
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  have hrle : ‖r‖ ≤ R := le_max_left _ _
  let u : Complex.Hadamard.divisorZeroIndex₀ F (Set.univ : Set ℂ) → ℝ :=
    fun p ↦ (2 * R) * (‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹ ^ (2 : ℕ))
  have hu : Summable u := hsum.mul_left (2 * R)
  refine hu.of_norm_bounded_eventually ?_
  have hbig :
      ∀ᶠ p : Complex.Hadamard.divisorZeroIndex₀ F (Set.univ : Set ℂ) in Filter.cofinite,
        (2 * R : ℝ) < ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ := by
    have hfinite :
        ({p : Complex.Hadamard.divisorZeroIndex₀ F (Set.univ : Set ℂ) |
          ‖Complex.Hadamard.divisorZeroIndex₀_val p‖ ≤ 2 * R} : Set _).Finite := by
      have hball : Metric.closedBall (0 : ℂ) (2 * R) ⊆ (Set.univ : Set ℂ) := by simp
      exact Complex.Hadamard.divisorZeroIndex₀_norm_le_finite
        (f := F) (U := (Set.univ : Set ℂ)) (B := 2 * R) hball
    filter_upwards [hfinite.eventually_cofinite_notMem] with p hp
    exact lt_of_not_ge (by simpa using hp)
  filter_upwards [hbig] with p hp
  let a : ℂ := Complex.Hadamard.divisorZeroIndex₀_val p
  have ha0 : a ≠ 0 := Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p
  have hra : r ≠ a := by
    intro hra
    have hnormeq : ‖r‖ = ‖a‖ := congrArg norm hra
    nlinarith
  have hra0 : r - a ≠ 0 := sub_ne_zero.mpr hra
  have hterm : 1 / (r - a) + 1 / a = r / (a * (r - a)) := by
    field_simp [ha0, hra0]
    ring
  have htriangle : ‖a‖ ≤ ‖r‖ + ‖r - a‖ := by
    calc
      ‖a‖ = ‖r + (a - r)‖ := by congr 1; ring
      _ ≤ ‖r‖ + ‖a - r‖ := norm_add_le _ _
      _ = ‖r‖ + ‖r - a‖ := by rw [norm_sub_rev]
  have hlower : ‖a‖ / 2 ≤ ‖r - a‖ := by
    nlinarith
  have hnorm : ‖1 / (r - a) + 1 / a‖ ≤
      (2 * R) * (‖a‖⁻¹ ^ (2 : ℕ)) := by
    rw [hterm, norm_div, norm_mul]
    have hanorm : 0 < ‖a‖ := norm_pos_iff.mpr ha0
    have hranorm : 0 < ‖r - a‖ := norm_pos_iff.mpr hra0
    rw [div_eq_mul_inv]
    calc
      ‖r‖ * (‖a‖ * ‖r - a‖)⁻¹ = ‖r‖ * ‖a‖⁻¹ * ‖r - a‖⁻¹ := by
        field_simp [hanorm.ne', hranorm.ne']
      _ ≤ R * ‖a‖⁻¹ * ‖r - a‖⁻¹ := by gcongr
      _ ≤ R * ‖a‖⁻¹ * (2 * ‖a‖⁻¹) := by
        gcongr
        have hhalf : 0 < ‖a‖ / 2 := by positivity
        have hinv : ‖r - a‖⁻¹ ≤ (‖a‖ / 2)⁻¹ := by
          simpa [one_div] using one_div_le_one_div_of_le hhalf hlower
        have hhalfInv : (‖a‖ / 2)⁻¹ = 2 * ‖a‖⁻¹ := by
          field_simp [hanorm.ne']
        simpa [hhalfInv] using hinv
      _ = (2 * R) * (‖a‖⁻¹ ^ (2 : ℕ)) := by ring
  have har : a ≠ r := Ne.symm hra
  simpa [regularizedDivisorForceTerm, har, u, a] using hnorm

private theorem logDeriv_divisorComplementCanonicalProduct_one_eq_tsum
    {F : ℂ → ℂ}
    (hsum : Summable
      (fun p : Complex.Hadamard.divisorZeroIndex₀ F (Set.univ : Set ℂ) ↦
        ‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹ ^ (2 : ℕ)))
    (r : ℂ) :
    logDeriv (Complex.Hadamard.divisorComplementCanonicalProduct 1 F r) r =
      ∑' p : Complex.Hadamard.divisorZeroIndex₀ F (Set.univ : Set ℂ),
        regularizedDivisorForceTerm r p := by
  let Phi : Complex.Hadamard.divisorZeroIndex₀ F (Set.univ : Set ℂ) → ℂ → ℂ :=
    fun p z ↦ Complex.Hadamard.divisorComplementFactor 1 F r p z
  have hfactor_ne : ∀ p, Phi p r ≠ 0 := by
    intro p
    by_cases hp : p ∈ Complex.Hadamard.divisorZeroIndex₀_fiberFinset (f := F) r
    · simp [Phi, Complex.Hadamard.divisorComplementFactor_eq_one_of_mem, hp]
    · rw [show Phi p r = Complex.weierstrassFactor 1
          (r / Complex.Hadamard.divisorZeroIndex₀_val p) by
        simp [Phi, Complex.Hadamard.divisorComplementFactor_eq_weierstrassFactor_of_not_mem, hp]]
      refine Complex.weierstrassFactor_ne_zero_of_ne_one 1 ?_
      intro heq
      have hval : r = Complex.Hadamard.divisorZeroIndex₀_val p :=
        (div_eq_one_iff_eq (Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p)).mp heq
      exact hp (by simpa [Complex.Hadamard.mem_divisorZeroIndex₀_fiberFinset] using hval.symm)
  have hdiff : ∀ p, DifferentiableOn ℂ (Phi p) (Set.univ : Set ℂ) := by
    intro p
    by_cases hp : p ∈ Complex.Hadamard.divisorZeroIndex₀_fiberFinset (f := F) r
    · have hfun : Phi p = fun _ : ℂ ↦ (1 : ℂ) := by
        funext z
        simp [Phi, Complex.Hadamard.divisorComplementFactor_eq_one_of_mem, hp]
      rw [hfun]
      fun_prop
    · have hfun : Phi p = fun z : ℂ ↦ Complex.weierstrassFactor 1
          (z / Complex.Hadamard.divisorZeroIndex₀_val p) := by
        funext z
        simp [Phi, Complex.Hadamard.divisorComplementFactor_eq_weierstrassFactor_of_not_mem, hp]
      rw [hfun]
      exact ((Complex.differentiable_weierstrassFactor 1).comp
        (differentiable_id.div_const _)).differentiableOn
  have hlogTerm : ∀ p, logDeriv (Phi p) r = regularizedDivisorForceTerm r p := by
    intro p
    by_cases hp : Complex.Hadamard.divisorZeroIndex₀_val p = r
    · have hmem : p ∈ Complex.Hadamard.divisorZeroIndex₀_fiberFinset (f := F) r := by
        simpa [Complex.Hadamard.mem_divisorZeroIndex₀_fiberFinset] using hp
      have hfun : Phi p = fun _ : ℂ ↦ (1 : ℂ) := by
        funext z
        simp [Phi, Complex.Hadamard.divisorComplementFactor_eq_one_of_mem, hmem]
      simp [hfun, regularizedDivisorForceTerm, hp]
    · have hnotmem : p ∉ Complex.Hadamard.divisorZeroIndex₀_fiberFinset (f := F) r := by
        simpa [Complex.Hadamard.mem_divisorZeroIndex₀_fiberFinset] using hp
      have hfun : Phi p = fun z : ℂ ↦ Complex.weierstrassFactor 1
          (z / Complex.Hadamard.divisorZeroIndex₀_val p) := by
        funext z
        simp [Phi, Complex.Hadamard.divisorComplementFactor_eq_weierstrassFactor_of_not_mem,
          hnotmem]
      rw [hfun]
      simpa [regularizedDivisorForceTerm, hp] using
        (Complex.logDeriv_weierstrassFactor_one_div
          (Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p) (Ne.symm hp))
  have hlogSummable : Summable (fun p ↦ logDeriv (Phi p) r) := by
    exact (summable_regularizedDivisorForceTerm hsum r).congr (fun p ↦ (hlogTerm p).symm)
  have hmultipliable : MultipliableLocallyUniformlyOn Phi (Set.univ : Set ℂ) := by
    simpa [Phi, Complex.Hadamard.divisorComplementCanonicalProduct] using
      (Complex.Hadamard.hasProdLocallyUniformlyOn_divisorComplementCanonicalProduct_univ
        1 F r hsum).multipliableLocallyUniformlyOn
  have hproduct_ne : (∏' p, Phi p r) ≠ 0 := by
    simpa [Phi, Complex.Hadamard.divisorComplementCanonicalProduct] using
      (Complex.Hadamard.divisorComplementCanonicalProduct_ne_zero_at
        (m := 1) (f := F) (z₀ := r) hsum)
  have hlog : logDeriv (∏' p, Phi p ·) r = ∑' p, logDeriv (Phi p) r :=
    logDeriv_tprod_eq_tsum (s := (Set.univ : Set ℂ)) isOpen_univ (by simp)
      hfactor_ne hdiff hlogSummable hmultipliable hproduct_ne
  change logDeriv (fun z ↦ ∏' p, Complex.Hadamard.divisorComplementFactor 1 F r p z) r = _
  calc
    logDeriv (fun z ↦ ∏' p, Complex.Hadamard.divisorComplementFactor 1 F r p z) r =
        ∑' p, logDeriv (Phi p) r := hlog
    _ = ∑' p, regularizedDivisorForceTerm r p := tsum_congr hlogTerm

private theorem divisorCanonicalProduct_eq_fiber_mul_complement
    (m : ℕ) (F : ℂ → ℂ)
    (hsum : Summable
      (fun p : Complex.Hadamard.divisorZeroIndex₀ F (Set.univ : Set ℂ) ↦
        ‖Complex.Hadamard.divisorZeroIndex₀_val p‖⁻¹ ^ (m + 1)))
    (r z : ℂ) :
    Complex.Hadamard.divisorCanonicalProduct m F (Set.univ : Set ℂ) z =
      Complex.Hadamard.divisorPartialProduct m F
          (Complex.Hadamard.divisorZeroIndex₀_fiberFinset (f := F) r) z *
        Complex.Hadamard.divisorComplementCanonicalProduct m F r z := by
  have hfull : Tendsto
      (fun s : Finset (Complex.Hadamard.divisorZeroIndex₀ F (Set.univ : Set ℂ)) ↦
        Complex.Hadamard.divisorPartialProduct m F s z)
      Filter.atTop
      (𝓝 (Complex.Hadamard.divisorCanonicalProduct m F (Set.univ : Set ℂ) z)) := by
    exact (Complex.Hadamard.tendstoLocallyUniformlyOn_divisorPartialProduct_univ
      m F hsum).tendsto_at (by simp)
  have hcomplement : Tendsto
      (fun s : Finset (Complex.Hadamard.divisorZeroIndex₀ F (Set.univ : Set ℂ)) ↦
        Complex.Hadamard.divisorComplementPartialProduct m F r s z)
      Filter.atTop
      (𝓝 (Complex.Hadamard.divisorComplementCanonicalProduct m F r z)) := by
    exact (Complex.Hadamard.tendstoLocallyUniformlyOn_divisorComplementPartialProduct_univ
      m F r hsum).tendsto_at (by simp)
  let fiberValue : ℂ := Complex.Hadamard.divisorPartialProduct m F
    (Complex.Hadamard.divisorZeroIndex₀_fiberFinset (f := F) r) z
  have hconst : Tendsto
      (fun _ : Finset (Complex.Hadamard.divisorZeroIndex₀ F (Set.univ : Set ℂ)) ↦ fiberValue)
      Filter.atTop (𝓝 fiberValue) := tendsto_const_nhds
  have hright := hconst.mul hcomplement
  have heq := Complex.Hadamard.eventually_eq_fiber_mul_divisorComplementPartialProduct
    m F r
  have hright' : Tendsto
      (fun s : Finset (Complex.Hadamard.divisorZeroIndex₀ F (Set.univ : Set ℂ)) ↦
        Complex.Hadamard.divisorPartialProduct m F
            (Complex.Hadamard.divisorZeroIndex₀_fiberFinset (f := F) r) z *
          Complex.Hadamard.divisorComplementPartialProduct m F r s z)
      Filter.atTop
      (𝓝 (Complex.Hadamard.divisorPartialProduct m F
          (Complex.Hadamard.divisorZeroIndex₀_fiberFinset (f := F) r) z *
        Complex.Hadamard.divisorComplementCanonicalProduct m F r z)) := by
    simpa [fiberValue] using hright
  exact tendsto_nhds_unique hfull (hright'.congr' (heq.mono fun s hs ↦ (hs z).symm))

/-- The absolutely convergent genus-one force at a possible zero of `H_t`. The complete fiber
over `r` is removed, and the regularized contribution of a simple removed factor is `1 / r`. -/
def deBruijnNewmanRegularizedZeroForce (t : ℝ) (r : ℂ) : ℂ :=
  1 / r +
    ∑' p : Complex.Hadamard.divisorZeroIndex₀
        (deBruijnNewmanH t) (Set.univ : Set ℂ),
      regularizedDivisorForceTerm r p

theorem summable_deBruijnNewman_regularizedZeroForceTerm (t : ℝ) (r : ℂ) :
    Summable
      (fun p : Complex.Hadamard.divisorZeroIndex₀
          (deBruijnNewmanH t) (Set.univ : Set ℂ) ↦
        if Complex.Hadamard.divisorZeroIndex₀_val p = r then 0
        else 1 / (r - Complex.Hadamard.divisorZeroIndex₀_val p) +
          1 / Complex.Hadamard.divisorZeroIndex₀_val p) := by
  change Summable (regularizedDivisorForceTerm (F := deBruijnNewmanH t) r)
  exact summable_regularizedDivisorForceTerm
    (summable_deBruijnNewmanH_divisorZeroIndex_norm_inv_sq t) r

private theorem deBruijnNewman_simpleZero_fiber_card_eq_one
    {t : ℝ} {r : ℂ} (hr : deBruijnNewmanH t r = 0)
    (hsimple : deriv (deBruijnNewmanH t) r ≠ 0) :
    (Complex.Hadamard.divisorZeroIndex₀_fiberFinset
      (f := deBruijnNewmanH t) r).card = 1 := by
  have hr0 : r ≠ 0 := by
    intro hr0
    subst r
    exact deBruijnNewmanH_zero_ne_zero t hr
  rw [Complex.Hadamard.divisorZeroIndex₀_fiberFinset_card_eq_analyticOrderNatAt
    (differentiable_deBruijnNewmanH t) hr0]
  have horder : analyticOrderAt (deBruijnNewmanH t) r = 1 :=
    (differentiable_deBruijnNewmanH t).analyticAt r
      |>.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hr hsimple
  simp [analyticOrderNatAt, horder]

private theorem deBruijnNewman_simpleZero_fiberPartialProduct_eq
    {t : ℝ} {r : ℂ} (hcard :
      (Complex.Hadamard.divisorZeroIndex₀_fiberFinset
        (f := deBruijnNewmanH t) r).card = 1)
    (z : ℂ) :
    Complex.Hadamard.divisorPartialProduct 1 (deBruijnNewmanH t)
        (Complex.Hadamard.divisorZeroIndex₀_fiberFinset
          (f := deBruijnNewmanH t) r) z =
      Complex.weierstrassFactor 1 (z / r) := by
  classical
  let fiber := Complex.Hadamard.divisorZeroIndex₀_fiberFinset
    (f := deBruijnNewmanH t) r
  calc
    Complex.Hadamard.divisorPartialProduct 1 (deBruijnNewmanH t) fiber z =
        ∏ p ∈ fiber, Complex.weierstrassFactor 1
          (z / Complex.Hadamard.divisorZeroIndex₀_val p) := by
      rfl
    _ = ∏ _p ∈ fiber, Complex.weierstrassFactor 1 (z / r) := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [(Complex.Hadamard.mem_divisorZeroIndex₀_fiberFinset
        (deBruijnNewmanH t) r p).mp hp]
    _ = Complex.weierstrassFactor 1 (z / r) := by
      rw [Finset.prod_const, hcard]
      simp

private def deBruijnNewmanSimpleZeroQuotient
    (t : ℝ) (r b : ℂ) (z : ℂ) : ℂ :=
  Complex.exp b * (-Complex.exp (z / r) / r) *
    Complex.Hadamard.divisorComplementCanonicalProduct 1 (deBruijnNewmanH t) r z

private theorem differentiable_deBruijnNewmanSimpleZeroQuotient
    (t : ℝ) (r b : ℂ) :
    Differentiable ℂ (deBruijnNewmanSimpleZeroQuotient t r b) := by
  have hexp : Differentiable ℂ (fun z : ℂ ↦ -Complex.exp (z / r) / r) := by
    fun_prop
  have hcomplement : Differentiable ℂ
      (Complex.Hadamard.divisorComplementCanonicalProduct 1 (deBruijnNewmanH t) r) := by
    rw [← differentiableOn_univ]
    exact Complex.Hadamard.differentiableOn_divisorComplementCanonicalProduct_univ
      1 (deBruijnNewmanH t) r
      (summable_deBruijnNewmanH_divisorZeroIndex_norm_inv_sq t)
  change Differentiable ℂ (fun z : ℂ ↦
    (Complex.exp b * (-Complex.exp (z / r) / r)) *
      Complex.Hadamard.divisorComplementCanonicalProduct 1 (deBruijnNewmanH t) r z)
  exact ((differentiable_const (c := Complex.exp b)).mul hexp).mul hcomplement

private theorem logDeriv_neg_exp_div_const {r : ℂ} (hr0 : r ≠ 0) :
    logDeriv (fun z : ℂ ↦ -Complex.exp (z / r) / r) r = 1 / r := by
  rw [logDeriv_apply]
  have hinner : HasDerivAt (· / r) (1 / r) r := by
    simpa using (hasDerivAt_id r).div_const r
  have hexp : HasDerivAt (fun z : ℂ ↦ Complex.exp (z / r))
      (Complex.exp (r / r) * (1 / r)) r :=
    hinner.cexp
  have hderiv : HasDerivAt (fun z : ℂ ↦ -Complex.exp (z / r) / r)
      (-(Complex.exp (r / r) * (1 / r)) / r) r := by
    simpa using hexp.neg.div_const r
  rw [hderiv.deriv]
  field_simp [hr0, Complex.exp_ne_zero (r / r)]

private theorem second_deriv_at_of_eq_sub_mul
    {F q : ℂ → ℂ} {r : ℂ}
    (hfactor : ∀ z : ℂ, F z = (z - r) * q z)
    (hq : Differentiable ℂ q) :
    deriv F r = q r ∧ deriv (deriv F) r = 2 * deriv q r := by
  have hfun : F = fun z : ℂ ↦ (z - r) * q z := funext hfactor
  have hderiv : deriv F = fun z : ℂ ↦ q z + (z - r) * deriv q z := by
    funext z
    rw [hfun]
    change deriv ((fun w : ℂ ↦ w - r) * q) z = _
    simpa using (((hasDerivAt_id z).sub_const r).mul (hq z).hasDerivAt).deriv
  have hqderiv : Differentiable ℂ (deriv q) := by
    rw [← differentiableOn_univ]
    exact hq.differentiableOn.deriv isOpen_univ
  constructor
  · rw [hderiv]
    simp
  · rw [hderiv]
    change deriv (q + (fun z : ℂ ↦ z - r) * deriv q) r = _
    have hsecond := (hq r).hasDerivAt.add
      (((hasDerivAt_id r).sub_const r).mul (hqderiv r).hasDerivAt)
    simpa [two_mul] using hsecond.deriv

private theorem exists_deBruijnNewman_simpleZero_factorization
    {t : ℝ} {r : ℂ} (hr : deBruijnNewmanH t r = 0)
    (hsimple : deriv (deBruijnNewmanH t) r ≠ 0) :
    ∃ b : ℂ, ∀ z : ℂ,
      deBruijnNewmanH t z =
        (z - r) * deBruijnNewmanSimpleZeroQuotient t r b z := by
  have hr0 : r ≠ 0 := by
    intro hr0
    subst r
    exact deBruijnNewmanH_zero_ne_zero t hr
  obtain ⟨b, hfactor⟩ := exists_deBruijnNewmanH_constant_hadamard_factorization t
  have hcard := deBruijnNewman_simpleZero_fiber_card_eq_one hr hsimple
  refine ⟨b, fun z ↦ ?_⟩
  have hsplit := divisorCanonicalProduct_eq_fiber_mul_complement
    1 (deBruijnNewmanH t)
    (summable_deBruijnNewmanH_divisorZeroIndex_norm_inv_sq t) r z
  rw [deBruijnNewman_simpleZero_fiberPartialProduct_eq hcard] at hsplit
  rw [hfactor z, hsplit]
  have hweierstrass : Complex.weierstrassFactor 1 (z / r) =
      (1 - z / r) * Complex.exp (z / r) := by
    simp [Complex.weierstrassFactor_def, Complex.partialLogSum_eq_sum]
  rw [hweierstrass]
  simp only [deBruijnNewmanSimpleZeroQuotient]
  have honeSub : 1 - z / r = -(z - r) / r := by
    field_simp [hr0]
    ring
  rw [honeSub]
  ring

private theorem logDeriv_deBruijnNewmanSimpleZeroQuotient_eq_force
    {t : ℝ} {r b : ℂ} (hr0 : r ≠ 0) :
    logDeriv (deBruijnNewmanSimpleZeroQuotient t r b) r =
      deBruijnNewmanRegularizedZeroForce t r := by
  let A : ℂ → ℂ := fun z ↦ -Complex.exp (z / r) / r
  let C : ℂ → ℂ :=
    Complex.Hadamard.divisorComplementCanonicalProduct 1 (deBruijnNewmanH t) r
  let B : ℂ → ℂ := fun z ↦ Complex.exp b * A z
  have hA_diff : Differentiable ℂ A := by
    dsimp only [A]
    fun_prop
  have hC_diff : Differentiable ℂ C := by
    rw [← differentiableOn_univ]
    exact Complex.Hadamard.differentiableOn_divisorComplementCanonicalProduct_univ
      1 (deBruijnNewmanH t) r
      (summable_deBruijnNewmanH_divisorZeroIndex_norm_inv_sq t)
  have hB_diff : Differentiable ℂ B := by
    exact (differentiable_const (c := Complex.exp b)).mul hA_diff
  have hA_ne : A r ≠ 0 := by
    dsimp only [A]
    exact div_ne_zero (neg_ne_zero.mpr (Complex.exp_ne_zero _)) hr0
  have hC_ne : C r ≠ 0 := by
    exact Complex.Hadamard.divisorComplementCanonicalProduct_ne_zero_at
      (m := 1) (f := deBruijnNewmanH t) (z₀ := r)
      (summable_deBruijnNewmanH_divisorZeroIndex_norm_inv_sq t)
  have hB_ne : B r ≠ 0 := mul_ne_zero (Complex.exp_ne_zero b) hA_ne
  have hA_log : logDeriv A r = 1 / r := by
    simpa [A] using logDeriv_neg_exp_div_const hr0
  have hB_log : logDeriv B r = 1 / r := by
    have hmul := logDeriv_mul r (Complex.exp_ne_zero b) hA_ne
      (differentiable_const (c := Complex.exp b) r) (hA_diff r)
    calc
      logDeriv B r = logDeriv (fun _ : ℂ ↦ Complex.exp b) r + logDeriv A r := by
        simpa [B] using hmul
      _ = 1 / r := by
        rw [hA_log]
        simp [logDeriv_apply]
  have hC_log : logDeriv C r =
      ∑' p : Complex.Hadamard.divisorZeroIndex₀
          (deBruijnNewmanH t) (Set.univ : Set ℂ),
        regularizedDivisorForceTerm r p := by
    exact logDeriv_divisorComplementCanonicalProduct_one_eq_tsum
      (summable_deBruijnNewmanH_divisorZeroIndex_norm_inv_sq t) r
  have hmul := logDeriv_mul r hB_ne hC_ne (hB_diff r) (hC_diff r)
  have hfun : deBruijnNewmanSimpleZeroQuotient t r b = fun z ↦ B z * C z := by
    funext z
    rfl
  rw [hfun]
  calc
    logDeriv (fun z ↦ B z * C z) r = logDeriv B r + logDeriv C r := by
      simpa using hmul
    _ = deBruijnNewmanRegularizedZeroForce t r := by
      rw [hB_log, hC_log]
      rfl

/-- At a simple zero, the regularized Hadamard force is exactly half the spatial logarithmic
derivative after the zero factor is removed. This is the divisor-indexed form of the force in the
de Bruijn-Newman zero dynamics equation. -/
theorem deBruijnNewmanH_second_deriv_div_two_deriv_eq_regularizedZeroForce
    {t : ℝ} {r : ℂ}
    (hr : deBruijnNewmanH t r = 0)
    (hsimple : deriv (deBruijnNewmanH t) r ≠ 0) :
    deriv (deriv (deBruijnNewmanH t)) r /
        (2 * deriv (deBruijnNewmanH t) r) =
      deBruijnNewmanRegularizedZeroForce t r := by
  have hr0 : r ≠ 0 := by
    intro hr0
    subst r
    exact deBruijnNewmanH_zero_ne_zero t hr
  obtain ⟨b, hfactor⟩ := exists_deBruijnNewman_simpleZero_factorization hr hsimple
  let q := deBruijnNewmanSimpleZeroQuotient t r b
  have hqdiff : Differentiable ℂ q :=
    differentiable_deBruijnNewmanSimpleZeroQuotient t r b
  have hderivs :
      deriv (deBruijnNewmanH t) r = q r ∧
        deriv (deriv (deBruijnNewmanH t)) r = 2 * deriv q r := by
    simpa [q] using second_deriv_at_of_eq_sub_mul hfactor hqdiff
  have hqne : q r ≠ 0 := by
    rw [← hderivs.1]
    exact hsimple
  have hratio : deriv (deriv (deBruijnNewmanH t)) r /
      (2 * deriv (deBruijnNewmanH t) r) = logDeriv q r := by
    rw [hderivs.1, hderivs.2, logDeriv_apply]
    field_simp [hqne]
  rw [hratio]
  exact logDeriv_deBruijnNewmanSimpleZeroQuotient_eq_force hr0

private def deBruijnNewmanTimePartialFDeriv (t : ℝ) (z : ℂ) : ℝ →L[ℝ] ℂ :=
  ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (deBruijnNewmanHSecondMoment t z)

private def deBruijnNewmanSpatialPartialFDeriv (t : ℝ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  deriv (deBruijnNewmanH t) z • (1 : ℂ →L[ℝ] ℂ)

private theorem hasStrictFDerivAt_deBruijnNewmanH_joint (p : ℝ × ℂ) :
    HasStrictFDerivAt (fun q : ℝ × ℂ ↦ deBruijnNewmanH q.1 q.2)
      ((deBruijnNewmanTimePartialFDeriv p.1 p.2).coprod
        (deBruijnNewmanSpatialPartialFDeriv p.1 p.2)) p := by
  apply hasStrictFDerivAt_uncurry_coprod
    (f := deBruijnNewmanH)
    (f₁ := deBruijnNewmanTimePartialFDeriv)
    (f₂ := deBruijnNewmanSpatialPartialFDeriv)
  · filter_upwards with q
    exact (hasDerivAt_deBruijnNewmanH_time q.1 q.2).hasFDerivAt
  · filter_upwards with q
    change HasFDerivAt (deBruijnNewmanH q.1)
      (deBruijnNewmanSpatialPartialFDeriv q.1 q.2) q.2
    simpa only [deBruijnNewmanSpatialPartialFDeriv, deriv_deBruijnNewmanH] using
      (hasDerivAt_deBruijnNewmanH_spatial q.1 q.2).complexToReal_fderiv
  · exact (ContinuousLinearMap.smulRightL ℝ ℝ ℂ 1).continuous.continuousAt.comp
      (continuousAt_deBruijnNewmanHSecondMoment_joint p)
  · have hmoment := continuousAt_deBruijnNewmanHSpatialFirstMoment_joint p
    have hderiv : ContinuousAt
        (fun q : ℝ × ℂ ↦ deriv (deBruijnNewmanH q.1) q.2) p := by
      simpa only [deriv_deBruijnNewmanH] using hmoment
    exact hderiv.smul continuousAt_const

/-- Chain rule for the source heat family along a complex-valued real path. The joint strict
Fréchet derivative is derived from the two source integral moments, so the path itself only needs
to be differentiable at the time under consideration. -/
theorem hasDerivAt_deBruijnNewmanH_along
    {x : ℝ → ℂ} {t : ℝ} {v : ℂ} (hx : HasDerivAt x v t) :
    HasDerivAt (fun tau : ℝ ↦ deBruijnNewmanH tau (x tau))
      (deBruijnNewmanHSecondMoment t (x t) + deriv (deBruijnNewmanH t) (x t) * v) t := by
  have hpath := (hasFDerivAt_id t).prodMk hx.hasFDerivAt
  have hcomp := (hasStrictFDerivAt_deBruijnNewmanH_joint (t, x t)).hasFDerivAt.comp t hpath
  simpa [Function.comp_def, deBruijnNewmanTimePartialFDeriv,
    deBruijnNewmanSpatialPartialFDeriv, ContinuousLinearMap.coprod_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, one_apply_eq_self, smul_eq_mul] using hcomp.hasDerivAt

/-- Every differentiable path of simple zeros obeys the divisor-regularized de Bruijn-Newman
velocity law. The sign uses the source convention `∂ₜ H = -∂²_z H`. -/
theorem deBruijnNewman_simpleZeroPath_velocity
    {x : ℝ → ℂ} {t : ℝ} {v : ℂ}
    (hx : HasDerivAt x v t)
    (hzero : ∀ tau : ℝ, deBruijnNewmanH tau (x tau) = 0)
    (hsimple : deriv (deBruijnNewmanH t) (x t) ≠ 0) :
    v = 2 * deBruijnNewmanRegularizedZeroForce t (x t) := by
  have hchain := (hasDerivAt_deBruijnNewmanH_along hx).unique
    (show HasDerivAt (fun tau : ℝ ↦ deBruijnNewmanH tau (x tau)) 0 t by
      simpa only [hzero] using hasDerivAt_const (x := t) (c := (0 : ℂ)))
  have hmoment : deBruijnNewmanHSecondMoment t (x t) =
      -deriv (deriv (deBruijnNewmanH t)) (x t) := by
    rw [deriv_deriv_deBruijnNewmanH]
    ring
  rw [hmoment] at hchain
  have hvelocity : v = deriv (deriv (deBruijnNewmanH t)) (x t) /
      deriv (deBruijnNewmanH t) (x t) := by
    apply (eq_div_iff hsimple).2
    calc
      v * deriv (deBruijnNewmanH t) (x t) =
          deriv (deBruijnNewmanH t) (x t) * v := mul_comm _ _
      _ = deriv (deriv (deBruijnNewmanH t)) (x t) := by
        linear_combination hchain
  rw [hvelocity]
  calc
    deriv (deriv (deBruijnNewmanH t)) (x t) /
          deriv (deBruijnNewmanH t) (x t) =
        2 * (deriv (deriv (deBruijnNewmanH t)) (x t) /
          (2 * deriv (deBruijnNewmanH t) (x t))) := by
            field_simp [hsimple]
    _ = 2 * deBruijnNewmanRegularizedZeroForce t (x t) := by
      rw [deBruijnNewmanH_second_deriv_div_two_deriv_eq_regularizedZeroForce
        (hzero t) hsimple]

end

end LeanLab.Riemann
