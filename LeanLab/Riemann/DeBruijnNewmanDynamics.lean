import LeanLab.Riemann.DeBruijnNewmanUpperHalf
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorQuotientRemovable
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain

set_option linter.style.header false

/-!
# Zero dynamics for the de Bruijn-Newman heat family

This module begins the direct H6-E proof attempt by identifying the logarithmic force exerted by
the multiplicity-bearing Hadamard divisor at a simple zero. The zero fiber is removed before the
infinite sum is evaluated, so the resulting genus-one sum is absolutely convergent.
-/

open Complex Filter Function Set Topology
open scoped BigOperators ComplexConjugate Topology

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

private def deBruijnNewmanZeroPairForceTerm (t : ℝ) (r s : ℂ)
    (p : Complex.Hadamard.divisorZeroIndex₀
      (deBruijnNewmanH t) (Set.univ : Set ℂ)) : ℂ :=
  if Complex.Hadamard.divisorZeroIndex₀_val p = r ∨
      Complex.Hadamard.divisorZeroIndex₀_val p = s then 0
  else 1 / (s - Complex.Hadamard.divisorZeroIndex₀_val p) -
    1 / (r - Complex.Hadamard.divisorZeroIndex₀_val p)

/-- The absolutely convergent force difference after removing the complete fibers over a selected
zero pair. -/
def deBruijnNewmanZeroPairForceRemainder (t : ℝ) (r s : ℂ) : ℂ :=
  ∑' p : Complex.Hadamard.divisorZeroIndex₀
      (deBruijnNewmanH t) (Set.univ : Set ℂ),
    deBruijnNewmanZeroPairForceTerm t r s p

theorem summable_deBruijnNewman_zeroPairForceTerm (t : ℝ) (r s : ℂ) :
    Summable (deBruijnNewmanZeroPairForceTerm t r s) := by
  let Ar : Complex.Hadamard.divisorZeroIndex₀
      (deBruijnNewmanH t) (Set.univ : Set ℂ) → ℂ :=
    regularizedDivisorForceTerm r
  let As : Complex.Hadamard.divisorZeroIndex₀
      (deBruijnNewmanH t) (Set.univ : Set ℂ) → ℂ :=
    regularizedDivisorForceTerm s
  have hbase : Summable (fun p ↦ As p - Ar p) :=
    (summable_regularizedDivisorForceTerm
      (summable_deBruijnNewmanH_divisorZeroIndex_norm_inv_sq t) s).sub
      (summable_regularizedDivisorForceTerm
        (summable_deBruijnNewmanH_divisorZeroIndex_norm_inv_sq t) r)
  have hfinite : ({p : Complex.Hadamard.divisorZeroIndex₀
      (deBruijnNewmanH t) (Set.univ : Set ℂ) |
      Complex.Hadamard.divisorZeroIndex₀_val p = r ∨
        Complex.Hadamard.divisorZeroIndex₀_val p = s} : Set _).Finite := by
    let fiberR := Complex.Hadamard.divisorZeroIndex₀_fiberFinset
      (f := deBruijnNewmanH t) r
    let fiberS := Complex.Hadamard.divisorZeroIndex₀_fiberFinset
      (f := deBruijnNewmanH t) s
    have heq : ({p : Complex.Hadamard.divisorZeroIndex₀
        (deBruijnNewmanH t) (Set.univ : Set ℂ) |
        Complex.Hadamard.divisorZeroIndex₀_val p = r ∨
          Complex.Hadamard.divisorZeroIndex₀_val p = s} : Set _) =
        (fiberR : Set _) ∪ (fiberS : Set _) := by
      ext p
      simp [fiberR, fiberS, Complex.Hadamard.mem_divisorZeroIndex₀_fiberFinset]
    rw [heq]
    exact (Finset.finite_toSet fiberR).union (Finset.finite_toSet fiberS)
  refine hbase.congr_cofinite ?_
  filter_upwards [hfinite.eventually_cofinite_notMem] with p hp
  have hp' : ¬(Complex.Hadamard.divisorZeroIndex₀_val p = r ∨
      Complex.Hadamard.divisorZeroIndex₀_val p = s) := by
    simpa only [Set.mem_setOf_eq] using hp
  simp only [deBruijnNewmanZeroPairForceTerm, hp', ↓reduceIte, As, Ar,
    regularizedDivisorForceTerm]
  rw [if_neg (fun h ↦ hp' (Or.inr h)), if_neg (fun h ↦ hp' (Or.inl h))]
  ring

/-- Every value represented by the multiplicity-bearing Hadamard divisor index is an actual zero
of the source heat family. -/
theorem deBruijnNewmanH_divisorZeroIndex₀_val_eq_zero (t : ℝ)
    (p : Complex.Hadamard.divisorZeroIndex₀
      (deBruijnNewmanH t) (Set.univ : Set ℂ)) :
    deBruijnNewmanH t (Complex.Hadamard.divisorZeroIndex₀_val p) = 0 := by
  obtain ⟨b, hfactor⟩ := exists_deBruijnNewmanH_constant_hadamard_factorization t
  rw [hfactor]
  rw [Complex.Hadamard.divisorCanonicalProduct_eq_zero_at_index 1 (deBruijnNewmanH t)
    (summable_deBruijnNewmanH_divisorZeroIndex_norm_inv_sq t) p]
  simp

/-- Two real zeros are adjacent when they are strictly ordered and no real zero lies strictly
between them. Simplicity is separate because the sign of the pair remainder does not need it. -/
def deBruijnNewmanAdjacentRealZeros (t r s : ℝ) : Prop :=
  r < s ∧
    deBruijnNewmanH t (r : ℂ) = 0 ∧
    deBruijnNewmanH t (s : ℂ) = 0 ∧
    ∀ u : ℝ, deBruijnNewmanH t (u : ℂ) = 0 → ¬(r < u ∧ u < s)

private theorem one_div_sub_sub_one_div_sub_nonpos_of_outside
    {r s u : ℝ} (hrs : r < s) (hur : u ≠ r) (hus : u ≠ s)
    (hout : u ≤ r ∨ s ≤ u) :
    1 / (s - u) - 1 / (r - u) ≤ 0 := by
  have hsu : s - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hus)
  have hru : r - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hur)
  have hid : 1 / (s - u) - 1 / (r - u) =
      (r - s) / ((s - u) * (r - u)) := by
    field_simp [hsu, hru]
    ring
  rw [hid]
  apply div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hrs.le)
  rcases hout with hu | hu
  · exact mul_nonneg (sub_nonneg.mpr (hu.trans hrs.le)) (sub_nonneg.mpr hu)
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hu)
      (sub_nonpos.mpr (hrs.le.trans hu))

/-- A real zero strictly between the selected endpoints contributes positively to the pair force.
This is the exact adversarial witness showing that adjacency is necessary for the sign theorem. -/
theorem realPairForceContribution_re_pos_of_between
    {r u s : ℝ} (hru : r < u) (hus : u < s) :
    0 < (1 / ((s : ℂ) - (u : ℂ)) - 1 / ((r : ℂ) - (u : ℂ))).re := by
  norm_cast
  have hleft : 0 < 1 / (s - u) := one_div_pos.mpr (sub_pos.mpr hus)
  have hright : 1 / (r - u) < 0 := one_div_neg.mpr (sub_neg.mpr hru)
  linarith

private theorem deBruijnNewmanZeroPairForceTerm_re_nonpos_of_adjacent
    {t r s : ℝ} (hall : deBruijnNewmanAllZerosReal t)
    (hadj : deBruijnNewmanAdjacentRealZeros t r s)
    (p : Complex.Hadamard.divisorZeroIndex₀
      (deBruijnNewmanH t) (Set.univ : Set ℂ)) :
    (deBruijnNewmanZeroPairForceTerm t (r : ℂ) (s : ℂ) p).re ≤ 0 := by
  let a : ℂ := Complex.Hadamard.divisorZeroIndex₀_val p
  by_cases har : a = (r : ℂ)
  · simp [deBruijnNewmanZeroPairForceTerm, a, har]
  by_cases has : a = (s : ℂ)
  · simp [deBruijnNewmanZeroPairForceTerm, a, has]
  have haZero : deBruijnNewmanH t a = 0 := by
    simpa only [a] using deBruijnNewmanH_divisorZeroIndex₀_val_eq_zero t p
  have haReal : a.im = 0 := hall a haZero
  let u : ℝ := a.re
  have hau : a = (u : ℂ) := by
    apply Complex.ext
    · simp [u]
    · simpa [u] using haReal
  have hur : u ≠ r := by
    intro h
    apply har
    simp [hau, h]
  have hus : u ≠ s := by
    intro h
    apply has
    simp [hau, h]
  have huZero : deBruijnNewmanH t (u : ℂ) = 0 := by
    simpa only [hau] using haZero
  have hout : u ≤ r ∨ s ≤ u := by
    by_cases hur' : u ≤ r
    · exact Or.inl hur'
    · right
      by_contra hsu'
      exact hadj.2.2.2 u huZero ⟨lt_of_not_ge hur', lt_of_not_ge hsu'⟩
  rw [deBruijnNewmanZeroPairForceTerm, if_neg]
  · change (1 / ((s : ℂ) - a) - 1 / ((r : ℂ) - a)).re ≤ 0
    rw [hau]
    norm_cast
    exact one_div_sub_sub_one_div_sub_nonpos_of_outside hadj.1 hur hus hout
  · simpa only [a] using not_or_intro har has

/-- At an all-real time, every remaining zero outside an adjacent pair contributes nonpositively
to the real pair force. Hence the complete absolutely convergent pair remainder is nonpositive. -/
theorem deBruijnNewmanZeroPairForceRemainder_re_nonpos
    {t r s : ℝ} (hall : deBruijnNewmanAllZerosReal t)
    (hadj : deBruijnNewmanAdjacentRealZeros t r s) :
    (deBruijnNewmanZeroPairForceRemainder t (r : ℂ) (s : ℂ)).re ≤ 0 := by
  rw [deBruijnNewmanZeroPairForceRemainder,
    Complex.re_tsum (summable_deBruijnNewman_zeroPairForceTerm t (r : ℂ) (s : ℂ))]
  exact tsum_nonpos fun p ↦
    deBruijnNewmanZeroPairForceTerm_re_nonpos_of_adjacent hall hadj p

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

/-- For two distinct simple zeros, their mutual interaction contributes exactly `2 / (s-r)` to
the regularized force difference. The remaining infinite sum omits both complete zero fibers and
is absolutely convergent. -/
theorem deBruijnNewmanRegularizedZeroForce_sub_eq_two_div_add_pairRemainder
    {t : ℝ} {r s : ℂ} (hrs : r ≠ s)
    (hr : deBruijnNewmanH t r = 0)
    (hs : deBruijnNewmanH t s = 0)
    (hrSimple : deriv (deBruijnNewmanH t) r ≠ 0)
    (hsSimple : deriv (deBruijnNewmanH t) s ≠ 0) :
    deBruijnNewmanRegularizedZeroForce t s -
        deBruijnNewmanRegularizedZeroForce t r =
      2 / (s - r) + deBruijnNewmanZeroPairForceRemainder t r s := by
  classical
  let Z := Complex.Hadamard.divisorZeroIndex₀
    (deBruijnNewmanH t) (Set.univ : Set ℂ)
  let fiberR := Complex.Hadamard.divisorZeroIndex₀_fiberFinset
    (f := deBruijnNewmanH t) r
  let fiberS := Complex.Hadamard.divisorZeroIndex₀_fiberFinset
    (f := deBruijnNewmanH t) s
  have hcardR : fiberR.card = 1 := by
    simpa only [fiberR] using deBruijnNewman_simpleZero_fiber_card_eq_one hr hrSimple
  have hcardS : fiberS.card = 1 := by
    simpa only [fiberS] using deBruijnNewman_simpleZero_fiber_card_eq_one hs hsSimple
  obtain ⟨pR, hpR⟩ := Finset.card_eq_one.mp hcardR
  obtain ⟨pS, hpS⟩ := Finset.card_eq_one.mp hcardS
  have hvalR : Complex.Hadamard.divisorZeroIndex₀_val pR = r := by
    apply (Complex.Hadamard.mem_divisorZeroIndex₀_fiberFinset
      (deBruijnNewmanH t) r pR).mp
    change pR ∈ fiberR
    rw [hpR]
    simp
  have hvalS : Complex.Hadamard.divisorZeroIndex₀_val pS = s := by
    apply (Complex.Hadamard.mem_divisorZeroIndex₀_fiberFinset
      (deBruijnNewmanH t) s pS).mp
    change pS ∈ fiberS
    rw [hpS]
    simp
  have hpSR : pS ≠ pR := by
    intro heq
    apply hrs
    calc
      r = Complex.Hadamard.divisorZeroIndex₀_val pR := hvalR.symm
      _ = Complex.Hadamard.divisorZeroIndex₀_val pS := by simp [heq]
      _ = s := hvalS
  have hEqR (p : Z) :
      Complex.Hadamard.divisorZeroIndex₀_val p = r ↔ p = pR := by
    constructor
    · intro hp
      have hmem : p ∈ fiberR := by
        exact (Complex.Hadamard.mem_divisorZeroIndex₀_fiberFinset
          (deBruijnNewmanH t) r p).mpr hp
      rw [hpR] at hmem
      simpa using hmem
    · rintro rfl
      exact hvalR
  have hEqS (p : Z) :
      Complex.Hadamard.divisorZeroIndex₀_val p = s ↔ p = pS := by
    constructor
    · intro hp
      have hmem : p ∈ fiberS := by
        exact (Complex.Hadamard.mem_divisorZeroIndex₀_fiberFinset
          (deBruijnNewmanH t) s p).mpr hp
      rw [hpS] at hmem
      simpa using hmem
    · rintro rfl
      exact hvalS
  let Ar : Z → ℂ := regularizedDivisorForceTerm r
  let As : Z → ℂ := regularizedDivisorForceTerm s
  let B : Z → ℂ := fun p ↦ As p - Ar p
  have hAr : Summable Ar := summable_regularizedDivisorForceTerm
    (summable_deBruijnNewmanH_divisorZeroIndex_norm_inv_sq t) r
  have hAs : Summable As := summable_regularizedDivisorForceTerm
    (summable_deBruijnNewmanH_divisorZeroIndex_norm_inv_sq t) s
  have hB : Summable B := by
    simpa only [B] using hAs.sub hAr
  have hdropR : Summable (fun p : Z ↦ if p = pR then 0 else B p) := by
    refine hB.congr_cofinite ?_
    filter_upwards [(Set.finite_singleton pR).eventually_cofinite_notMem] with p hp
    have hpne : p ≠ pR := by
      change p ≠ pR at hp
      exact hp
    simp [hpne]
  have htail (p : Z) :
      (if p = pS then 0 else if p = pR then 0 else B p) =
        deBruijnNewmanZeroPairForceTerm t r s p := by
    by_cases hpr : p = pR
    · subst p
      simp [hvalR, hrs, deBruijnNewmanZeroPairForceTerm]
    by_cases hps : p = pS
    · subst p
      simp [hvalS, deBruijnNewmanZeroPairForceTerm]
    have hvalNeR : Complex.Hadamard.divisorZeroIndex₀_val p ≠ r :=
      fun h ↦ hpr ((hEqR p).mp h)
    have hvalNeS : Complex.Hadamard.divisorZeroIndex₀_val p ≠ s :=
      fun h ↦ hps ((hEqS p).mp h)
    simp [hpr, hps, B, As, Ar, regularizedDivisorForceTerm,
      deBruijnNewmanZeroPairForceTerm, hvalNeR, hvalNeS]
  have hsplit :
      ∑' p : Z, B p = B pR + B pS +
        ∑' p : Z, deBruijnNewmanZeroPairForceTerm t r s p := by
    calc
      ∑' p : Z, B p = B pR + ∑' p : Z, if p = pR then 0 else B p :=
        hB.tsum_eq_add_tsum_ite pR
      _ = B pR + ((if pS = pR then 0 else B pS) +
          ∑' p : Z, if p = pS then 0 else if p = pR then 0 else B p) := by
        rw [hdropR.tsum_eq_add_tsum_ite pS]
      _ = B pR + B pS +
          ∑' p : Z, deBruijnNewmanZeroPairForceTerm t r s p := by
        rw [if_neg hpSR, tsum_congr htail]
        ring
  have hBpR : B pR = 1 / (s - r) + 1 / r := by
    simp [B, As, Ar, regularizedDivisorForceTerm, hvalR, hrs]
  have hBpS : B pS = -(1 / (r - s) + 1 / s) := by
    simp [B, As, Ar, regularizedDivisorForceTerm, hvalS, Ne.symm hrs]
  have hneg : 1 / (r - s) = -(1 / (s - r)) := by
    rw [show r - s = -(s - r) by ring]
    simp only [one_div, inv_neg]
  change (1 / s + ∑' p : Z, As p) - (1 / r + ∑' p : Z, Ar p) =
    2 / (s - r) + ∑' p : Z, deBruijnNewmanZeroPairForceTerm t r s p
  calc
    (1 / s + ∑' p : Z, As p) - (1 / r + ∑' p : Z, Ar p) =
        1 / s - 1 / r + ((∑' p : Z, As p) - ∑' p : Z, Ar p) := by ring
    _ = 1 / s - 1 / r + ∑' p : Z, B p := by
      rw [hAs.tsum_sub hAr]
    _ = 2 / (s - r) +
        ∑' p : Z, deBruijnNewmanZeroPairForceTerm t r s p := by
      rw [hsplit, hBpR, hBpS, hneg]
      ring

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

/-- Every path that is differentiable at `t` and is locally a path of simple zeros obeys the
divisor-regularized de Bruijn-Newman velocity law. The sign uses the source convention
`∂ₜ H = -∂²_z H`. -/
theorem deBruijnNewman_simpleZeroPath_velocity_of_eventually
    {x : ℝ → ℂ} {t : ℝ} {v : ℂ}
    (hx : HasDerivAt x v t)
    (hzero : ∀ᶠ tau in 𝓝 t, deBruijnNewmanH tau (x tau) = 0)
    (hsimple : deriv (deBruijnNewmanH t) (x t) ≠ 0) :
    v = 2 * deBruijnNewmanRegularizedZeroForce t (x t) := by
  have hchain := (hasDerivAt_deBruijnNewmanH_along hx).unique
    (show HasDerivAt (fun tau : ℝ ↦ deBruijnNewmanH tau (x tau)) 0 t by
      apply (hasDerivAt_const (x := t) (c := (0 : ℂ))).congr_of_eventuallyEq
      exact hzero.mono fun tau hz ↦ hz)
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
        hzero.self_of_nhds hsimple]

/-- Global-path specialization of the local simple-zero velocity law. -/
theorem deBruijnNewman_simpleZeroPath_velocity
    {x : ℝ → ℂ} {t : ℝ} {v : ℂ}
    (hx : HasDerivAt x v t)
    (hzero : ∀ tau : ℝ, deBruijnNewmanH tau (x tau) = 0)
    (hsimple : deriv (deBruijnNewmanH t) (x t) ≠ 0) :
    v = 2 * deBruijnNewmanRegularizedZeroForce t (x t) :=
  deBruijnNewman_simpleZeroPath_velocity_of_eventually hx
    (Filter.Eventually.of_forall hzero) hsimple

private theorem isInvertible_deBruijnNewmanSpatialPartialFDeriv
    {t : ℝ} {r : ℂ} (hsimple : deriv (deBruijnNewmanH t) r ≠ 0) :
    (deBruijnNewmanSpatialPartialFDeriv t r).IsInvertible := by
  let e : ℂ ≃L[ℝ] ℂ :=
    ContinuousLinearEquiv.smulLeft (Units.mk0 (deriv (deBruijnNewmanH t) r) hsimple)
  refine ⟨e, ?_⟩
  ext z
  simp [e, deBruijnNewmanSpatialPartialFDeriv]

/-- A simple real zero extends to a locally unique differentiable real zero trajectory. The
trajectory is produced by the real implicit-function theorem on `ℝ × ℂ`; conjugation symmetry and
local uniqueness force its nearby values back onto the real axis. -/
theorem exists_deBruijnNewman_localRealSimpleZeroPath
    {t r : ℝ}
    (hr : deBruijnNewmanH t (r : ℂ) = 0)
    (hsimple : deriv (deBruijnNewmanH t) (r : ℂ) ≠ 0) :
    ∃ x : ℝ → ℂ,
      x t = (r : ℂ) ∧
      Tendsto x (𝓝 t) (𝓝 (r : ℂ)) ∧
      HasDerivAt x (2 * deBruijnNewmanRegularizedZeroForce t (r : ℂ)) t ∧
      (∀ᶠ tau in 𝓝 t,
        deBruijnNewmanH tau (x tau) = 0 ∧ (x tau).im = 0) ∧
      (∀ᶠ p : ℝ × ℂ in 𝓝 (t, (r : ℂ)),
        deBruijnNewmanH p.1 p.2 = 0 ↔ x p.1 = p.2) := by
  let D : ℝ × ℂ →L[ℝ] ℂ :=
    (deBruijnNewmanTimePartialFDeriv t (r : ℂ)).coprod
      (deBruijnNewmanSpatialPartialFDeriv t (r : ℂ))
  have hD : HasStrictFDerivAt (fun p : ℝ × ℂ ↦ deBruijnNewmanH p.1 p.2)
      D (t, (r : ℂ)) := by
    simpa only [D] using hasStrictFDerivAt_deBruijnNewmanH_joint (t, (r : ℂ))
  have hinv : (D ∘L ContinuousLinearMap.inr ℝ ℝ ℂ).IsInvertible := by
    simpa only [D, ContinuousLinearMap.coprod_comp_inr] using
      isInvertible_deBruijnNewmanSpatialPartialFDeriv hsimple
  let x : ℝ → ℂ := hD.implicitFunctionOfProdDomain hinv
  have huniq : ∀ᶠ p : ℝ × ℂ in 𝓝 (t, (r : ℂ)),
      deBruijnNewmanH p.1 p.2 = deBruijnNewmanH t (r : ℂ) ↔ x p.1 = p.2 := by
    simpa only [x] using hD.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinv
  have hanchor : x t = (r : ℂ) := (huniq.self_of_nhds).mp rfl
  have htend : Tendsto x (𝓝 t) (𝓝 (r : ℂ)) := by
    simpa only [x] using hD.tendsto_implicitFunctionOfProdDomain hinv
  have hzero : ∀ᶠ tau in 𝓝 t, deBruijnNewmanH tau (x tau) = 0 := by
    have h := hD.eventually_apply_implicitFunctionOfProdDomain hinv
    simpa only [x, hr] using h
  have hxRaw := (hD.hasStrictFDerivAt_implicitFunctionOfProdDomain hinv).hasFDerivAt.hasDerivAt
  have hsimplex : deriv (deBruijnNewmanH t) (x t) ≠ 0 := by
    simpa only [hanchor] using hsimple
  have hvelocity := deBruijnNewman_simpleZeroPath_velocity_of_eventually
    hxRaw hzero hsimplex
  change _ = 2 * deBruijnNewmanRegularizedZeroForce t (x t) at hvelocity
  rw [hanchor] at hvelocity
  have hxderiv :
      HasDerivAt x (2 * deBruijnNewmanRegularizedZeroForce t (r : ℂ)) t :=
    hxRaw.congr_deriv hvelocity
  have hconjTend : Tendsto (fun tau : ℝ ↦ conj (x tau)) (𝓝 t) (𝓝 (r : ℂ)) := by
    change Tendsto (conj ∘ x) (𝓝 t) (𝓝 (r : ℂ))
    simpa only [conj_ofReal] using Complex.continuous_conj.continuousAt.tendsto.comp htend
  have hpairConj : Tendsto (fun tau : ℝ ↦ (tau, conj (x tau)))
      (𝓝 t) (𝓝 (t, (r : ℂ))) :=
    tendsto_id.prodMk_nhds hconjTend
  have huniqConj : ∀ᶠ tau in 𝓝 t,
      deBruijnNewmanH tau (conj (x tau)) = deBruijnNewmanH t (r : ℂ) ↔
        x tau = conj (x tau) :=
    hpairConj.eventually huniq
  have hreal : ∀ᶠ tau in 𝓝 t, (x tau).im = 0 := by
    filter_upwards [hzero, huniqConj] with tau hzeroTau huniqTau
    have hconjZero : deBruijnNewmanH tau (conj (x tau)) = 0 := by
      rw [deBruijnNewmanH_conj, hzeroTau, map_zero]
    exact Complex.conj_eq_iff_im.mp (huniqTau.mp (by simpa only [hr] using hconjZero)).symm
  refine ⟨x, hanchor, htend, hxderiv, ?_, ?_⟩
  · filter_upwards [hzero, hreal] with tau hzeroTau hrealTau
    exact ⟨hzeroTau, hrealTau⟩
  · simpa only [hr] using huniq

/-- Two distinct simple real zeros extend to locally ordered real zero trajectories. This is the
local no-collision interface: any loss of order must occur only after leaving the common
simple-zero neighbourhood. -/
theorem exists_deBruijnNewman_orderedLocalRealSimpleZeroPaths
    {t r s : ℝ} (hrs : r < s)
    (hr : deBruijnNewmanH t (r : ℂ) = 0)
    (hs : deBruijnNewmanH t (s : ℂ) = 0)
    (hrSimple : deriv (deBruijnNewmanH t) (r : ℂ) ≠ 0)
    (hsSimple : deriv (deBruijnNewmanH t) (s : ℂ) ≠ 0) :
    ∃ x y : ℝ → ℂ,
      x t = (r : ℂ) ∧ y t = (s : ℂ) ∧
      HasDerivAt x (2 * deBruijnNewmanRegularizedZeroForce t (r : ℂ)) t ∧
      HasDerivAt y (2 * deBruijnNewmanRegularizedZeroForce t (s : ℂ)) t ∧
      (∀ᶠ tau in 𝓝 t,
        deBruijnNewmanH tau (x tau) = 0 ∧
        (x tau).im = 0 ∧
        deBruijnNewmanH tau (y tau) = 0 ∧
        (y tau).im = 0 ∧
        (x tau).re < (y tau).re) := by
  obtain ⟨x, hxAnchor, hxTend, hxDeriv, hxZeroReal, _⟩ :=
    exists_deBruijnNewman_localRealSimpleZeroPath hr hrSimple
  obtain ⟨y, hyAnchor, hyTend, hyDeriv, hyZeroReal, _⟩ :=
    exists_deBruijnNewman_localRealSimpleZeroPath hs hsSimple
  have hxReTend : Tendsto (fun tau : ℝ ↦ (x tau).re) (𝓝 t) (𝓝 r) := by
    change Tendsto (Complex.re ∘ x) (𝓝 t) (𝓝 r)
    simpa only [ofReal_re] using (Complex.continuous_re.tendsto (r : ℂ)).comp hxTend
  have hyReTend : Tendsto (fun tau : ℝ ↦ (y tau).re) (𝓝 t) (𝓝 s) := by
    change Tendsto (Complex.re ∘ y) (𝓝 t) (𝓝 s)
    simpa only [ofReal_re] using (Complex.continuous_re.tendsto (s : ℂ)).comp hyTend
  have hordered : ∀ᶠ tau in 𝓝 t, (x tau).re < (y tau).re :=
    hxReTend.eventually_lt hyReTend hrs
  refine ⟨x, y, hxAnchor, hyAnchor, hxDeriv, hyDeriv, ?_⟩
  filter_upwards [hxZeroReal, hyZeroReal, hordered] with tau hxTau hyTau hxyTau
  exact ⟨hxTau.1, hxTau.2, hyTau.1, hyTau.2, hxyTau⟩

/-- The complex gap between two locally differentiable simple-zero paths has derivative twice the
difference of their regularized divisor forces. -/
theorem hasDerivAt_deBruijnNewman_simpleZeroPath_gap
    {x y : ℝ → ℂ} {t : ℝ} {vx vy : ℂ}
    (hx : HasDerivAt x vx t) (hy : HasDerivAt y vy t)
    (hxZero : ∀ᶠ tau in 𝓝 t, deBruijnNewmanH tau (x tau) = 0)
    (hyZero : ∀ᶠ tau in 𝓝 t, deBruijnNewmanH tau (y tau) = 0)
    (hxSimple : deriv (deBruijnNewmanH t) (x t) ≠ 0)
    (hySimple : deriv (deBruijnNewmanH t) (y t) ≠ 0) :
    HasDerivAt (fun tau : ℝ ↦ y tau - x tau)
      (2 * (deBruijnNewmanRegularizedZeroForce t (y t) -
        deBruijnNewmanRegularizedZeroForce t (x t))) t := by
  have hvxEq := deBruijnNewman_simpleZeroPath_velocity_of_eventually
    hx hxZero hxSimple
  have hvyEq := deBruijnNewman_simpleZeroPath_velocity_of_eventually
    hy hyZero hySimple
  exact (hy.sub hx).congr_deriv (by rw [hvxEq, hvyEq]; ring)

/-- Real-part form of the exact simple-zero gap velocity. -/
theorem hasDerivAt_deBruijnNewman_simpleZeroPath_realGap
    {x y : ℝ → ℂ} {t : ℝ} {vx vy : ℂ}
    (hx : HasDerivAt x vx t) (hy : HasDerivAt y vy t)
    (hxZero : ∀ᶠ tau in 𝓝 t, deBruijnNewmanH tau (x tau) = 0)
    (hyZero : ∀ᶠ tau in 𝓝 t, deBruijnNewmanH tau (y tau) = 0)
    (hxSimple : deriv (deBruijnNewmanH t) (x t) ≠ 0)
    (hySimple : deriv (deBruijnNewmanH t) (y t) ≠ 0) :
    HasDerivAt (fun tau : ℝ ↦ (y tau).re - (x tau).re)
      (2 * (deBruijnNewmanRegularizedZeroForce t (y t) -
        deBruijnNewmanRegularizedZeroForce t (x t)).re) t := by
  have hgap := hasDerivAt_deBruijnNewman_simpleZeroPath_gap
    hx hy hxZero hyZero hxSimple hySimple
  have hcomp := Complex.reCLM.hasFDerivAt.comp t hgap.hasFDerivAt
  simpa [Function.comp_def, Complex.reCLM_apply, ContinuousLinearMap.comp_apply,
    smul_eq_mul] using hcomp.hasDerivAt

/-- Exact squared-gap evolution for two simple-zero paths. Any global collision exclusion must
control the real part of the force difference in this identity uniformly over the relevant zero
pairs and heights. -/
theorem hasDerivAt_deBruijnNewman_simpleZeroPath_realGapSq
    {x y : ℝ → ℂ} {t : ℝ} {vx vy : ℂ}
    (hx : HasDerivAt x vx t) (hy : HasDerivAt y vy t)
    (hxZero : ∀ᶠ tau in 𝓝 t, deBruijnNewmanH tau (x tau) = 0)
    (hyZero : ∀ᶠ tau in 𝓝 t, deBruijnNewmanH tau (y tau) = 0)
    (hxSimple : deriv (deBruijnNewmanH t) (x t) ≠ 0)
    (hySimple : deriv (deBruijnNewmanH t) (y t) ≠ 0) :
    HasDerivAt (fun tau : ℝ ↦ ((y tau).re - (x tau).re) ^ 2)
      (4 * ((y t).re - (x t).re) *
        (deBruijnNewmanRegularizedZeroForce t (y t) -
          deBruijnNewmanRegularizedZeroForce t (x t)).re) t := by
  have hgap := hasDerivAt_deBruijnNewman_simpleZeroPath_realGap
    hx hy hxZero hyZero hxSimple hySimple
  exact (hgap.pow 2).congr_deriv (by ring)

/-- Squared-gap evolution with the mutual pair interaction extracted. The positive constant `8`
is exact; all possible collision-producing behavior is confined to the absolutely convergent
force remainder over the other zero fibers. -/
theorem hasDerivAt_deBruijnNewman_simpleZeroPath_realGapSq_pairRemainder
    {x y : ℝ → ℂ} {t r s : ℝ} {vx vy : ℂ} (hrs : r < s)
    (hxAnchor : x t = (r : ℂ)) (hyAnchor : y t = (s : ℂ))
    (hx : HasDerivAt x vx t) (hy : HasDerivAt y vy t)
    (hxZero : ∀ᶠ tau in nhds t, deBruijnNewmanH tau (x tau) = 0)
    (hyZero : ∀ᶠ tau in nhds t, deBruijnNewmanH tau (y tau) = 0)
    (hxSimple : deriv (deBruijnNewmanH t) (x t) ≠ 0)
    (hySimple : deriv (deBruijnNewmanH t) (y t) ≠ 0) :
    HasDerivAt (fun tau : ℝ ↦ ((y tau).re - (x tau).re) ^ 2)
      (8 + 4 * (s - r) *
        (deBruijnNewmanZeroPairForceRemainder t (r : ℂ) (s : ℂ)).re) t := by
  have hgap := hasDerivAt_deBruijnNewman_simpleZeroPath_realGapSq
    hx hy hxZero hyZero hxSimple hySimple
  have hrsC : (r : ℂ) ≠ (s : ℂ) := by
    exact_mod_cast hrs.ne
  have hrZero : deBruijnNewmanH t (r : ℂ) = 0 := by
    simpa only [hxAnchor] using hxZero.self_of_nhds
  have hsZero : deBruijnNewmanH t (s : ℂ) = 0 := by
    simpa only [hyAnchor] using hyZero.self_of_nhds
  have hrSimple : deriv (deBruijnNewmanH t) (r : ℂ) ≠ 0 := by
    simpa only [hxAnchor] using hxSimple
  have hsSimple : deriv (deBruijnNewmanH t) (s : ℂ) ≠ 0 := by
    simpa only [hyAnchor] using hySimple
  have hforce := deBruijnNewmanRegularizedZeroForce_sub_eq_two_div_add_pairRemainder
    hrsC hrZero hsZero hrSimple hsSimple
  have hmutualRe : (2 / ((s : ℂ) - (r : ℂ))).re = 2 / (s - r) := by
    norm_cast
  apply hgap.congr_deriv
  rw [hxAnchor, hyAnchor, hforce]
  simp only [ofReal_re, add_re, hmutualRe]
  field_simp [sub_ne_zero.mpr hrs.ne']
  ring

/-- At an all-real time, an adjacent simple-zero pair has squared-gap velocity at most `8`. The
derivative identity and its inequality certificate are returned together so the bound cannot be
detached from the exact pair-removed dynamics. -/
theorem hasDerivAt_deBruijnNewman_adjacentSimpleZeroPath_realGapSq_and_deriv_le_eight
    {x y : ℝ → ℂ} {t r s : ℝ} {vx vy : ℂ}
    (hall : deBruijnNewmanAllZerosReal t)
    (hadj : deBruijnNewmanAdjacentRealZeros t r s)
    (hxAnchor : x t = (r : ℂ)) (hyAnchor : y t = (s : ℂ))
    (hx : HasDerivAt x vx t) (hy : HasDerivAt y vy t)
    (hxZero : ∀ᶠ tau in nhds t, deBruijnNewmanH tau (x tau) = 0)
    (hyZero : ∀ᶠ tau in nhds t, deBruijnNewmanH tau (y tau) = 0)
    (hxSimple : deriv (deBruijnNewmanH t) (x t) ≠ 0)
    (hySimple : deriv (deBruijnNewmanH t) (y t) ≠ 0) :
    HasDerivAt (fun tau : ℝ ↦ ((y tau).re - (x tau).re) ^ 2)
        (8 + 4 * (s - r) *
          (deBruijnNewmanZeroPairForceRemainder t (r : ℂ) (s : ℂ)).re) t ∧
      8 + 4 * (s - r) *
          (deBruijnNewmanZeroPairForceRemainder t (r : ℂ) (s : ℂ)).re ≤ 8 := by
  refine ⟨hasDerivAt_deBruijnNewman_simpleZeroPath_realGapSq_pairRemainder hadj.1
    hxAnchor hyAnchor hx hy hxZero hyZero hxSimple hySimple, ?_⟩
  have hrem := deBruijnNewmanZeroPairForceRemainder_re_nonpos hall hadj
  have hcoeff : 0 ≤ 4 * (s - r) := mul_nonneg (by norm_num) (sub_nonneg.mpr hadj.1.le)
  have hprod : 4 * (s - r) *
      (deBruijnNewmanZeroPairForceRemainder t (r : ℂ) (s : ℂ)).re ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hcoeff hrem
  linarith

private theorem sub_le_eight_mul_sub_of_hasDerivAt_le_eight
    {q d : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hq : ∀ u ∈ Set.Icc a b, HasDerivAt q (d u) u)
    (hd : ∀ u ∈ Set.Icc a b, d u ≤ 8) :
    q b - q a ≤ 8 * (b - a) := by
  let g : ℝ → ℝ := (fun u ↦ 8 * u) - q
  have hg (u : ℝ) (hu : u ∈ Set.Icc a b) :
      HasDerivAt g (8 - d u) u := by
    simpa [g, Function.id_def] using
      ((hasDerivAt_id u).const_mul (8 : ℝ)).sub (hq u hu)
  have hgContinuous : ContinuousOn g (Set.Icc a b) := by
    intro u hu
    exact (hg u hu).continuousAt.continuousWithinAt
  have hgMono : MonotoneOn g (Set.Icc a b) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) hgContinuous
    · intro u hu
      exact (hg u (interior_subset hu)).hasDerivWithinAt
    · intro u hu
      exact sub_nonneg.mpr (hd u (interior_subset hu))
  have hmono := hgMono (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab) hab
  change 8 * a - q a ≤ 8 * b - q b at hmono
  linarith

/-- Integrating the adjacent-pair velocity bound backward over an interval of all-real, adjacent,
simple zero paths gives the exact terminal-gap lower bound. Its useful time scale is the terminal
squared gap divided by `8`; no height-uniform lower gap is asserted. -/
theorem deBruijnNewman_adjacentSimpleZeroPath_realGapSq_lower_bound
    {x y : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hall : ∀ t ∈ Set.Icc a b, deBruijnNewmanAllZerosReal t)
    (hadj : ∀ t ∈ Set.Icc a b,
      deBruijnNewmanAdjacentRealZeros t (x t).re (y t).re)
    (hxZero : ∀ t : ℝ, deBruijnNewmanH t (x t) = 0)
    (hyZero : ∀ t : ℝ, deBruijnNewmanH t (y t) = 0)
    (hxDiff : ∀ t ∈ Set.Icc a b, ∃ v : ℂ, HasDerivAt x v t)
    (hyDiff : ∀ t ∈ Set.Icc a b, ∃ v : ℂ, HasDerivAt y v t)
    (hxSimple : ∀ t ∈ Set.Icc a b, deriv (deBruijnNewmanH t) (x t) ≠ 0)
    (hySimple : ∀ t ∈ Set.Icc a b, deriv (deBruijnNewmanH t) (y t) ≠ 0) :
    ((y b).re - (x b).re) ^ 2 - 8 * (b - a) ≤
      ((y a).re - (x a).re) ^ 2 := by
  let q : ℝ → ℝ := fun t ↦ ((y t).re - (x t).re) ^ 2
  let d : ℝ → ℝ := fun t ↦
    8 + 4 * ((y t).re - (x t).re) *
      (deBruijnNewmanZeroPairForceRemainder t ((x t).re : ℂ) ((y t).re : ℂ)).re
  have hqd (t : ℝ) (ht : t ∈ Set.Icc a b) :
      HasDerivAt q (d t) t ∧ d t ≤ 8 := by
    obtain ⟨vx, hx⟩ := hxDiff t ht
    obtain ⟨vy, hy⟩ := hyDiff t ht
    have hxAnchor : x t = ((x t).re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using hall t ht (x t) (hxZero t)
    have hyAnchor : y t = ((y t).re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using hall t ht (y t) (hyZero t)
    simpa only [q, d] using
      (hasDerivAt_deBruijnNewman_adjacentSimpleZeroPath_realGapSq_and_deriv_le_eight
        (hall t ht) (hadj t ht) hxAnchor hyAnchor hx hy
        (Filter.Eventually.of_forall hxZero) (Filter.Eventually.of_forall hyZero)
        (hxSimple t ht) (hySimple t ht))
  have hbound : q b - q a ≤ 8 * (b - a) :=
    sub_le_eight_mul_sub_of_hasDerivAt_le_eight hab
      (fun t ht ↦ (hqd t ht).1) (fun t ht ↦ (hqd t ht).2)
  dsimp only [q] at hbound
  linarith

end

end LeanLab.Riemann
