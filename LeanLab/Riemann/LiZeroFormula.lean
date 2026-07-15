import LeanLab.Riemann.LiHadamard
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# All-index Li coefficients and the compensated xi zero sum

This module justifies iterated differentiation of the genus-one logarithmic-derivative zero sum
near `s = 1` and combines it with the derivative definition of the project Li candidates.
-/

open Complex Filter Function Metric Polynomial Set Topology
open scoped BigOperators Topology

namespace LeanLab.Riemann

noncomputable section

/-- The multiplicity-bearing nonzero xi divisor index used in the Hadamard product. -/
abbrev RiemannXiDivisorZeroIndex :=
  Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ)

/-- The value of a multiplicity-bearing nonzero xi divisor index. -/
abbrev riemannXiDivisorZeroValue (p : RiemannXiDivisorZeroIndex) : ℂ :=
  Complex.Hadamard.divisorZeroIndex₀_val p

/-- One genus-one logarithmic-derivative term attached to a nonzero xi zero. -/
def riemannXiLogDerivZeroTerm (p : RiemannXiDivisorZeroIndex) (z : ℂ) : ℂ :=
  1 / (z - riemannXiDivisorZeroValue p) + 1 / riemannXiDivisorZeroValue p

/-- The explicit `k`-th derivative of a compensated xi zero term at a variable point. -/
def riemannXiLogDerivZeroDerivativeTerm
    (k : ℕ) (p : RiemannXiDivisorZeroIndex) (z : ℂ) : ℂ :=
  (-1 : ℂ) ^ k * (k.factorial : ℂ) /
      (z - riemannXiDivisorZeroValue p) ^ (k + 1) +
    if k = 0 then 1 / riemannXiDivisorZeroValue p else 0

/-- The xi nonzero set is the open set on which its logarithmic derivative is analytic. -/
def riemannXiNonzeroSet : Set ℂ := {z : ℂ | riemannXi z ≠ 0}

theorem isOpen_riemannXiNonzeroSet : IsOpen riemannXiNonzeroSet := by
  exact isOpen_ne_fun differentiable_riemannXi.continuous continuous_const

theorem one_mem_riemannXiNonzeroSet : (1 : ℂ) ∈ riemannXiNonzeroSet :=
  riemannXi_one_ne_zero

theorem ne_riemannXiDivisorZeroValue_of_mem_nonzeroSet
    {z : ℂ} (hz : z ∈ riemannXiNonzeroSet) (p : RiemannXiDivisorZeroIndex) :
    z ≠ riemannXiDivisorZeroValue p := by
  intro hzp
  apply hz
  rw [hzp]
  exact riemannXi_eq_zero_of_isNontrivialZero
    (riemannXiDivisorZeroIndex_val_isNontrivialZero p)

/-- Every iterated derivative of one compensated zero term has the expected rational form. -/
theorem iteratedDeriv_riemannXiLogDerivZeroTerm
    (k : ℕ) (p : RiemannXiDivisorZeroIndex) {z : ℂ}
    (hz : z ≠ riemannXiDivisorZeroValue p) :
    iteratedDeriv k (riemannXiLogDerivZeroTerm p) z =
      riemannXiLogDerivZeroDerivativeTerm k p z := by
  rcases k with _ | k
  · simp [riemannXiLogDerivZeroTerm, riemannXiLogDerivZeroDerivativeTerm]
  · have hinv : ContDiffAt ℂ (k + 1)
        (fun w : ℂ => 1 / (w - riemannXiDivisorZeroValue p)) z := by
      have hsub : ContDiffAt ℂ (k + 1)
          (fun w : ℂ => w - riemannXiDivisorZeroValue p) z := by
        fun_prop
      simpa only [one_div] using hsub.inv (sub_ne_zero.mpr hz)
    have hconst : ContDiffAt ℂ (k + 1)
        (fun _ : ℂ => 1 / riemannXiDivisorZeroValue p) z := by
      fun_prop
    rw [show riemannXiLogDerivZeroTerm p =
        (fun w : ℂ => 1 / (w - riemannXiDivisorZeroValue p)) +
          fun _ : ℂ => 1 / riemannXiDivisorZeroValue p by
      funext w
      rfl]
    rw [iteratedDeriv_add hinv hconst]
    have hfirst :
        iteratedDeriv (k + 1)
            (fun w : ℂ => 1 / (w - riemannXiDivisorZeroValue p)) z =
          (-1 : ℂ) ^ (k + 1) * ((k + 1).factorial : ℂ) *
            (z - riemannXiDivisorZeroValue p) ^ (-1 - (k + 1 : ℕ) : ℤ) := by
      rw [iteratedDeriv_eq_iterate]
      simpa only [one_div, one_mul, mul_one, one_pow] using
        congrFun (iter_deriv_inv_linear_sub (k + 1) (1 : ℂ)
          (riemannXiDivisorZeroValue p)) z
    have hk0 : k + 1 ≠ 0 := by omega
    have hconstDeriv :
        iteratedDeriv (k + 1) (fun _ : ℂ => 1 / riemannXiDivisorZeroValue p) z = 0 := by
      rw [iteratedDeriv_const, if_neg hk0]
    rw [hfirst, hconstDeriv, add_zero]
    rw [riemannXiLogDerivZeroDerivativeTerm, if_neg hk0, add_zero]
    rw [show (-1 : ℤ) - ((k + 1 : ℕ) : ℤ) = -(((k + 1) + 1 : ℕ) : ℤ) by omega]
    rw [zpow_neg_coe_of_pos (z - riemannXiDivisorZeroValue p) (by omega)]
    rw [div_eq_mul_inv]

/-- Near `1`, every positive derivative of the chosen logarithm is the preceding derivative of
the logarithmic derivative. -/
theorem iteratedDeriv_succ_log_riemannXi_eq_logDeriv (k : ℕ) :
    iteratedDeriv (k + 1) (fun z : ℂ => log (riemannXi z)) 1 =
      iteratedDeriv k (logDeriv riemannXi) 1 := by
  rw [iteratedDeriv_succ']
  exact eventually_deriv_log_riemannXi_eq_logDeriv.iteratedDeriv_eq k

theorem summable_riemannXiLogDerivZeroTerm_of_mem_nonzeroSet
    {z : ℂ} (hz : z ∈ riemannXiNonzeroSet) :
    Summable (fun p : RiemannXiDivisorZeroIndex => riemannXiLogDerivZeroTerm p z) := by
  apply summable_riemannXi_logDerivTerms_of_not_isNontrivialZero
  intro hzero
  exact hz (riemannXi_eq_zero_of_isNontrivialZero hzero)

/-- On the xi nonzero set, every positive-order differentiated zero series is locally uniformly
summable. The far-zero majorant is a constant multiple of `|rho|^(-2)`. -/
theorem summableLocallyUniformlyOn_riemannXiLogDerivZeroDerivativeTerm
    (k : ℕ) (hk : 1 ≤ k) :
    SummableLocallyUniformlyOn
      (fun p : RiemannXiDivisorZeroIndex =>
        riemannXiLogDerivZeroDerivativeTerm k p)
      riemannXiNonzeroSet := by
  apply SummableLocallyUniformlyOn.of_locally_bounded_eventually
    isOpen_riemannXiNonzeroSet
  intro K hKU hK
  rcases (isBounded_iff_forall_norm_le.1 hK.isBounded) with ⟨R0, hR0⟩
  let R : ℝ := max R0 1
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  have hnormK : ∀ z ∈ K, ‖z‖ ≤ R := fun z hzK =>
    le_trans (hR0 z hzK) (le_max_left _ _)
  let u : RiemannXiDivisorZeroIndex → ℝ := fun p =>
    ((k.factorial : ℝ) * 2 ^ (k + 1)) *
      (‖riemannXiDivisorZeroValue p‖⁻¹ ^ (2 : ℕ))
  have hu : Summable u :=
    summable_riemannXiDivisorZeroIndex_norm_inv_sq.mul_left
      ((k.factorial : ℝ) * 2 ^ (k + 1))
  refine ⟨u, hu, ?_⟩
  let B : ℝ := max (2 * R) 1
  have h_big :
      ∀ᶠ p : RiemannXiDivisorZeroIndex in Filter.cofinite,
        B < ‖riemannXiDivisorZeroValue p‖ := by
    have hfin :
        ({p : RiemannXiDivisorZeroIndex |
          ‖riemannXiDivisorZeroValue p‖ ≤ B} : Set _).Finite := by
      have hball : Metric.closedBall (0 : ℂ) B ⊆ (Set.univ : Set ℂ) := by simp
      exact Complex.Hadamard.divisorZeroIndex₀_norm_le_finite
        (f := riemannXi) (U := (Set.univ : Set ℂ)) B hball
    filter_upwards [hfin.eventually_cofinite_notMem] with p hp
    have hnot : ¬‖riemannXiDivisorZeroValue p‖ ≤ B := by simpa using hp
    exact lt_of_not_ge hnot
  filter_upwards [h_big] with p hp z hzK
  let a : ℂ := riemannXiDivisorZeroValue p
  have ha0 : a ≠ 0 := Complex.Hadamard.divisorZeroIndex₀_val_ne_zero p
  have hza0 : z - a ≠ 0 := sub_ne_zero.mpr
    (ne_riemannXiDivisorZeroValue_of_mem_nonzeroSet (hKU hzK) p)
  have hpR : 2 * R < ‖a‖ := lt_of_le_of_lt (le_max_left _ _) hp
  have hp1 : 1 < ‖a‖ := lt_of_le_of_lt (le_max_right _ _) hp
  have htri : ‖a‖ ≤ ‖z‖ + ‖z - a‖ := by
    have hraw : ‖a‖ ≤ ‖z‖ + ‖a - z‖ := by
      have h := norm_add_le z (a - z)
      simpa [a, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
    simpa [norm_sub_rev] using hraw
  have hza_lower : ‖a‖ / 2 ≤ ‖z - a‖ := by
    nlinarith [htri, hnormK z hzK, hpR]
  have hinv : ‖z - a‖⁻¹ ≤ 2 * ‖a‖⁻¹ := by
    have ha_norm_pos : 0 < ‖a‖ := norm_pos_iff.mpr ha0
    have hza_norm_pos : 0 < ‖z - a‖ := norm_pos_iff.mpr hza0
    have hraw : ‖z - a‖⁻¹ ≤ (‖a‖ / 2)⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le (by positivity : 0 < ‖a‖ / 2) hza_lower
    have hhalf_inv : (‖a‖ / 2)⁻¹ = 2 * ‖a‖⁻¹ := by
      field_simp [ha_norm_pos.ne']
    simpa [hhalf_inv] using hraw
  have hpow : ‖z - a‖⁻¹ ^ (k + 1) ≤ (2 * ‖a‖⁻¹) ^ (k + 1) :=
    pow_le_pow_left₀ (inv_nonneg.2 (norm_nonneg _)) hinv (k + 1)
  have hainv_le_one : ‖a‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp1.le
  have hainv_pow : ‖a‖⁻¹ ^ (k + 1) ≤ ‖a‖⁻¹ ^ (2 : ℕ) :=
    pow_le_pow_of_le_one (inv_nonneg.2 (norm_nonneg _)) hainv_le_one (by omega)
  have hnorm :
      ‖riemannXiLogDerivZeroDerivativeTerm k p z‖ =
        (k.factorial : ℝ) * ‖z - a‖⁻¹ ^ (k + 1) := by
    rw [riemannXiLogDerivZeroDerivativeTerm, if_neg (by omega : k ≠ 0), add_zero]
    simp [a, norm_pow, div_eq_mul_inv, inv_pow]
  rw [hnorm]
  calc
    (k.factorial : ℝ) * ‖z - a‖⁻¹ ^ (k + 1)
        ≤ (k.factorial : ℝ) * (2 * ‖a‖⁻¹) ^ (k + 1) := by gcongr
    _ = ((k.factorial : ℝ) * 2 ^ (k + 1)) * ‖a‖⁻¹ ^ (k + 1) := by
      rw [mul_pow]
      ring
    _ ≤ ((k.factorial : ℝ) * 2 ^ (k + 1)) * ‖a‖⁻¹ ^ (2 : ℕ) := by gcongr
    _ = u p := by simp [u, a]

theorem summableLocallyUniformlyOn_iteratedDerivWithin_riemannXiLogDerivZeroTerm
    (k : ℕ) (hk : 1 ≤ k) :
    SummableLocallyUniformlyOn
      (fun p : RiemannXiDivisorZeroIndex =>
        iteratedDerivWithin k (riemannXiLogDerivZeroTerm p) riemannXiNonzeroSet)
      riemannXiNonzeroSet := by
  apply SummableLocallyUniformlyOn_congr
    (fun p z hz => ?_)
    (summableLocallyUniformlyOn_riemannXiLogDerivZeroDerivativeTerm k hk)
  rw [iteratedDerivWithin_of_isOpen isOpen_riemannXiNonzeroSet hz]
  exact (iteratedDeriv_riemannXiLogDerivZeroTerm k p
    (ne_riemannXiDivisorZeroValue_of_mem_nonzeroSet hz p)).symm

theorem differentiableAt_iteratedDerivWithin_riemannXiLogDerivZeroTerm
    (p : RiemannXiDivisorZeroIndex) (k : ℕ) {z : ℂ}
    (hz : z ∈ riemannXiNonzeroSet) :
    DifferentiableAt ℂ
      (iteratedDerivWithin k (riemannXiLogDerivZeroTerm p) riemannXiNonzeroSet) z := by
  have heq :
      (iteratedDerivWithin k (riemannXiLogDerivZeroTerm p) riemannXiNonzeroSet)
        =ᶠ[𝓝 z] riemannXiLogDerivZeroDerivativeTerm k p := by
    filter_upwards [isOpen_riemannXiNonzeroSet.mem_nhds hz] with w hw
    rw [iteratedDerivWithin_of_isOpen isOpen_riemannXiNonzeroSet hw]
    exact iteratedDeriv_riemannXiLogDerivZeroTerm k p
      (ne_riemannXiDivisorZeroValue_of_mem_nonzeroSet hw p)
  rw [heq.differentiableAt_iff]
  have hden : z - riemannXiDivisorZeroValue p ≠ 0 := sub_ne_zero.mpr
    (ne_riemannXiDivisorZeroValue_of_mem_nonzeroSet hz p)
  unfold riemannXiLogDerivZeroDerivativeTerm
  have hmain : DifferentiableAt ℂ
      (fun w : ℂ => (-1 : ℂ) ^ k * (k.factorial : ℂ) /
        (w - riemannXiDivisorZeroValue p) ^ (k + 1)) z := by
    apply DifferentiableAt.div
    · fun_prop
    · fun_prop
    · exact pow_ne_zero _ hden
  split_ifs <;> exact hmain.add (by fun_prop)

/-- All iterated derivatives of the compensated zero sum may be computed term by term at `1`. -/
theorem iteratedDeriv_tsum_riemannXiLogDerivZeroTerm (k : ℕ) :
    iteratedDeriv k
        (fun z : ℂ => ∑' p : RiemannXiDivisorZeroIndex,
          riemannXiLogDerivZeroTerm p z) 1 =
      ∑' p : RiemannXiDivisorZeroIndex,
        riemannXiLogDerivZeroDerivativeTerm k p 1 := by
  have hwithin := iteratedDerivWithin_tsum
    (f := fun p : RiemannXiDivisorZeroIndex => riemannXiLogDerivZeroTerm p)
    k isOpen_riemannXiNonzeroSet one_mem_riemannXiNonzeroSet
    (fun z hz => summable_riemannXiLogDerivZeroTerm_of_mem_nonzeroSet hz)
    (fun j hj1 hjk =>
      summableLocallyUniformlyOn_iteratedDerivWithin_riemannXiLogDerivZeroTerm j hj1)
    (fun p j z hjk hz =>
      differentiableAt_iteratedDerivWithin_riemannXiLogDerivZeroTerm p j hz)
  rw [iteratedDerivWithin_of_isOpen isOpen_riemannXiNonzeroSet
    one_mem_riemannXiNonzeroSet] at hwithin
  calc
    iteratedDeriv k
        (fun z : ℂ => ∑' p : RiemannXiDivisorZeroIndex,
          riemannXiLogDerivZeroTerm p z) 1 =
        ∑' p : RiemannXiDivisorZeroIndex,
          iteratedDerivWithin k (riemannXiLogDerivZeroTerm p)
            riemannXiNonzeroSet 1 := hwithin
    _ = ∑' p : RiemannXiDivisorZeroIndex,
          riemannXiLogDerivZeroDerivativeTerm k p 1 := by
      apply tsum_congr
      intro p
      rw [iteratedDerivWithin_of_isOpen isOpen_riemannXiNonzeroSet
        one_mem_riemannXiNonzeroSet]
      exact iteratedDeriv_riemannXiLogDerivZeroTerm k p
        (ne_riemannXiDivisorZeroValue_of_mem_nonzeroSet one_mem_riemannXiNonzeroSet p)

theorem summable_riemannXiLogDerivZeroDerivativeTerm_one (k : ℕ) :
    Summable (fun p : RiemannXiDivisorZeroIndex =>
      riemannXiLogDerivZeroDerivativeTerm k p 1) := by
  by_cases hk : k = 0
  · subst k
    simpa [riemannXiLogDerivZeroTerm, riemannXiLogDerivZeroDerivativeTerm] using
      summable_riemannXiLogDerivZeroTerm_of_mem_nonzeroSet one_mem_riemannXiNonzeroSet
  · exact (summableLocallyUniformlyOn_riemannXiLogDerivZeroDerivativeTerm k
      (Nat.one_le_iff_ne_zero.mpr hk)).summable one_mem_riemannXiNonzeroSet

/-- A fixed project Hadamard factorization gives the logarithmic-derivative identity at every
point of the xi nonzero set. -/
theorem riemannXi_logDeriv_eq_polynomial_derivative_add_tsum
    {P : Polynomial ℂ}
    (hfac : ∀ w : ℂ, riemannXi w = Complex.exp (Polynomial.eval w P) *
      Complex.Hadamard.divisorCanonicalProduct 1 riemannXi (Set.univ : Set ℂ) w)
    {z : ℂ} (hz : z ∈ riemannXiNonzeroSet) :
    logDeriv riemannXi z = Polynomial.eval z P.derivative +
      ∑' p : RiemannXiDivisorZeroIndex, riemannXiLogDerivZeroTerm p z := by
  have haway : ∀ p : RiemannXiDivisorZeroIndex,
      z ≠ riemannXiDivisorZeroValue p := fun p =>
    ne_riemannXiDivisorZeroValue_of_mem_nonzeroSet hz p
  change ∀ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      z ≠ Complex.Hadamard.divisorZeroIndex₀_val p at haway
  rw [riemannXi_eq_complex_riemannXi] at haway hfac
  change logDeriv riemannXi z = Polynomial.eval z P.derivative +
    ∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      (1 / (z - Complex.Hadamard.divisorZeroIndex₀_val p) +
        1 / Complex.Hadamard.divisorZeroIndex₀_val p)
  rw [riemannXi_eq_complex_riemannXi]
  exact _root_.logDeriv_riemannXi_eq_polynomial_derivative_add_tsum hfac haway

theorem analyticAt_logDeriv_riemannXi_one :
    AnalyticAt ℂ (logDeriv riemannXi) 1 := by
  unfold logDeriv
  exact (analyticAt_riemannXi 1).deriv.div
    (analyticAt_riemannXi 1) riemannXi_one_ne_zero

/-- For one fixed Hadamard polynomial, every iterated derivative of xi's logarithmic derivative
is the polynomial contribution plus the explicitly differentiated compensated zero sum. -/
theorem iteratedDeriv_logDeriv_riemannXi_eq_hadamard_zero_formula
    {P : Polynomial ℂ}
    (hfac : ∀ w : ℂ, riemannXi w = Complex.exp (Polynomial.eval w P) *
      Complex.Hadamard.divisorCanonicalProduct 1 riemannXi (Set.univ : Set ℂ) w)
    (k : ℕ) :
    iteratedDeriv k (logDeriv riemannXi) 1 =
      iteratedDeriv k (fun z : ℂ => Polynomial.eval z P.derivative) 1 +
        ∑' p : RiemannXiDivisorZeroIndex,
          riemannXiLogDerivZeroDerivativeTerm k p 1 := by
  let Q : ℂ → ℂ := fun z : ℂ => Polynomial.eval z P.derivative
  let S : ℂ → ℂ := fun z : ℂ =>
    ∑' p : RiemannXiDivisorZeroIndex, riemannXiLogDerivZeroTerm p z
  have heq : logDeriv riemannXi =ᶠ[𝓝 (1 : ℂ)] fun z => Q z + S z := by
    filter_upwards [isOpen_riemannXiNonzeroSet.mem_nhds one_mem_riemannXiNonzeroSet] with z hz
    exact riemannXi_logDeriv_eq_polynomial_derivative_add_tsum hfac hz
  have hSeq : S =ᶠ[𝓝 (1 : ℂ)] fun z => logDeriv riemannXi z - Q z := by
    filter_upwards [heq] with z hz
    rw [hz]
    ring
  have hQ : ContDiffAt ℂ k Q 1 := by
    dsimp only [Q]
    simpa [Polynomial.aeval_def] using
      (Polynomial.contDiff_aeval (R := ℂ) (𝕜 := ℂ) P.derivative
        (k : WithTop ℕ∞)).contDiffAt
  have hlog : ContDiffAt ℂ k (logDeriv riemannXi) 1 :=
    analyticAt_logDeriv_riemannXi_one.contDiffAt
  have hS : ContDiffAt ℂ k S 1 :=
    (hlog.sub hQ).congr_of_eventuallyEq hSeq
  rw [heq.iteratedDeriv_eq k]
  change iteratedDeriv k (Q + S) 1 = _
  rw [iteratedDeriv_add hQ hS]
  change iteratedDeriv k (fun z : ℂ => Polynomial.eval z P.derivative) 1 +
      iteratedDeriv k S 1 = _
  rw [show iteratedDeriv k S 1 =
      ∑' p : RiemannXiDivisorZeroIndex,
        riemannXiLogDerivZeroDerivativeTerm k p 1 by
    exact iteratedDeriv_tsum_riemannXiLogDerivZeroTerm k]

theorem exists_riemannXi_hadamard_iterated_logDeriv_zero_formula :
    ∃ P : Polynomial ℂ, P.degree ≤ 1 ∧
      (∀ z : ℂ, riemannXi z = Complex.exp (Polynomial.eval z P) *
        Complex.Hadamard.divisorCanonicalProduct 1 riemannXi (Set.univ : Set ℂ) z) ∧
      ∀ k : ℕ, iteratedDeriv k (logDeriv riemannXi) 1 =
        iteratedDeriv k (fun z : ℂ => Polynomial.eval z P.derivative) 1 +
          ∑' p : RiemannXiDivisorZeroIndex,
            riemannXiLogDerivZeroDerivativeTerm k p 1 := by
  obtain ⟨P, hdegree, hfac⟩ := exists_riemannXi_hadamard_factorization
  exact ⟨P, hdegree, hfac,
    iteratedDeriv_logDeriv_riemannXi_eq_hadamard_zero_formula hfac⟩

/-- The derivative definition of every project Li candidate is a finite linear combination of
iterated derivatives of `logDeriv riemannXi`. -/
theorem liCoefficientCandidate_eq_finset_sum_iteratedDeriv_logDeriv (n : ℕ) :
    liCoefficientCandidate n =
      (∑ i ∈ Finset.range (n + 1),
          ((n + 1).choose i : ℂ) * (n.descFactorial i : ℂ) *
            iteratedDeriv (n - i) (logDeriv riemannXi) 1) /
        (n.factorial : ℂ) := by
  have hpow : ContDiffAt ℂ (n + 1) (fun z : ℂ => z ^ n) 1 := by
    fun_prop
  have hlog : ContDiffAt ℂ (n + 1) (fun z : ℂ => log (riemannXi z)) 1 :=
    analyticAt_log_riemannXi_one.contDiffAt
  unfold liCoefficientCandidate
  change iteratedDeriv (n + 1)
      ((fun z : ℂ => z ^ n) * fun z : ℂ => log (riemannXi z)) 1 /
      (n.factorial : ℂ) = _
  rw [iteratedDeriv_mul hpow hlog]
  simp only
  rw [Finset.sum_range_succ]
  simp only [iteratedDeriv_pow, one_pow, mul_one]
  rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega : n < n + 1)]
  simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero]
  apply congrArg (fun x : ℂ => x / (n.factorial : ℂ))
  apply Finset.sum_congr rfl
  intro i hi
  have hi_le : i ≤ n := by
    simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hi
  rw [show n + 1 - i = (n - i) + 1 by omega]
  rw [iteratedDeriv_succ_log_riemannXi_eq_logDeriv]

/-- One fixed genus-one Hadamard polynomial gives an exact compensated zero formula for every
derivative-defined project Li coefficient. -/
theorem exists_liCoefficientCandidate_eq_hadamard_zero_formula :
    ∃ P : Polynomial ℂ, P.degree ≤ 1 ∧
      (∀ z : ℂ, riemannXi z = Complex.exp (Polynomial.eval z P) *
        Complex.Hadamard.divisorCanonicalProduct 1 riemannXi (Set.univ : Set ℂ) z) ∧
      ∀ n : ℕ, liCoefficientCandidate n =
        (∑ i ∈ Finset.range (n + 1),
            ((n + 1).choose i : ℂ) * (n.descFactorial i : ℂ) *
              (iteratedDeriv (n - i)
                  (fun z : ℂ => Polynomial.eval z P.derivative) 1 +
                ∑' p : RiemannXiDivisorZeroIndex,
                  riemannXiLogDerivZeroDerivativeTerm (n - i) p 1)) /
          (n.factorial : ℂ) := by
  obtain ⟨P, hdegree, hfac, hderiv⟩ :=
    exists_riemannXi_hadamard_iterated_logDeriv_zero_formula
  refine ⟨P, hdegree, hfac, fun n => ?_⟩
  rw [liCoefficientCandidate_eq_finset_sum_iteratedDeriv_logDeriv]
  apply congrArg (fun x : ℂ => x / (n.factorial : ℂ))
  apply Finset.sum_congr rfl
  intro i hi
  rw [hderiv (n - i)]

end

end LeanLab.Riemann
